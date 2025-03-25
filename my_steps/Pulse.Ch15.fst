module Pulse.Ch15

open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module L = Pulse.Lib.SpinLock
module GR = Pulse.Lib.GhostReference
module R = Pulse.Lib.Reference

// # Parallel Increment

// Parallel Blocks

```pulse
fn par (#pf #pg #qf #qg:_)
       (f: unit -> stt unit pf (fun _ -> qf))
       (g: unit -> stt unit pg (fun _ -> qg))
requires pf ** pg
ensures qf ** qg
{
  parallel 
  requires pf and pg
  ensures qf and qg
  { f () }
  { g () };
  ()
}
```

```pulse // I copied the incr code from one of previous chapters
fn incr (r:ref int)
requires pts_to r 'v
ensures pts_to r ('v + 1)
{
    let v = !r;
    r := v + 1;
}
```


```pulse
fn par_incr (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y ('j + 1)
{
   par (fun _ -> incr x)
       (fun _ -> incr y)
}
```

[@@expect_failure]
```pulse
fn attempt0 (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
  par (fun _ -> incr) (fun _ -> incr);
}
```

```pulse
fn attempt (x:ref int)
requires pts_to x 'i
ensures emp
{
  let l = L.new_lock (exists* v. pts_to x v);
  fn incr ()
  requires emp
  ensures emp
  {
    L.acquire l;
    let v = !x;
    x := v + 1;
    L.release l
  };
  par incr incr
}
```

// A First Take, with Locks

let contributions (left right: GR.ref int) (i v:int)=
  exists* (vl vr:int).
    GR.pts_to left #one_half vl **
    GR.pts_to right #one_half vr **
    pure (v == i + vl + vr)

let lock_inv (x:ref int) (init:int) (left right:GR.ref int) =
  exists* v. 
    pts_to x v **
    contributions left right init v
    
```pulse
fn incr_left (x:ref int)
             (#left:GR.ref int)
             (#right:GR.ref int)
             (#i:erased int)
             (lock:L.lock (lock_inv x i left right))
requires GR.pts_to left #one_half 'vl
ensures  GR.pts_to left #one_half ('vl + 1)
{
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  let v = !x;
  x := v + 1;
  GR.gather left;
  GR.write left ('vl + 1);
  GR.share left;
  fold (contributions left right i (v + 1));
  fold lock_inv;
  L.release lock
}
```

```pulse
fn incr_right (x:ref int)
              (#left:GR.ref int)
              (#right:GR.ref int)
              (#i:erased int)
              (lock:L.lock (lock_inv x i left right))
requires GR.pts_to right #one_half 'vl
ensures  GR.pts_to right #one_half ('vl + 1)
{
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  let v = !x;
  x := v + 1;
  GR.gather right;
  GR.write right ('vl + 1);
  GR.share right;
  fold (contributions left right i (v + 1));
  fold (lock_inv x i left right);
  L.release lock
}
```

```pulse
fn add2 (x:ref int)
requires pts_to x 'i
ensures  pts_to x ('i + 2)
{
  let left = GR.alloc 0;
  let right = GR.alloc 0;
  GR.share left;
  GR.share right;
  fold (contributions left right 'i 'i);
  fold (lock_inv x 'i left right);
  let lock = L.new_lock (lock_inv x 'i left right);
  par (fun _ -> incr_left x lock)
      (fun _ -> incr_right x lock);
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  GR.gather left;
  GR.gather right;
  GR.free left;
  GR.free right;
}
```

// Modularity with higher-order ghost code

```pulse
fn incr_m (x: ref int)
        (#refine #aspec: int -> vprop)
        (l:L.lock (exists* v. pts_to x v ** refine v))
        (ghost_steps: 
          (v:int -> vq:int -> stt_ghost unit emp_inames 
               (refine v ** aspec vq ** pts_to x (v + 1))
               (fun _ -> refine (v + 1) ** aspec (vq + 1) ** pts_to x (v + 1))))
requires aspec 'i
ensures aspec ('i + 1)
 {
    L.acquire l;
    with _v. _;
    let vx = !x;
    rewrite each _v as vx;
    x := vx + 1;
    ghost_steps vx 'i;
    L.release l;
}
```

// I skipped the rest of the chapter till I learn more on separation logic 