module PulseTutorialExercises.Basics
open Pulse.Lib.Pervasives

let fstar_five : int = 5

```pulse
fn five ()
requires emp  // this is a trivial proposition, fun s -> True
returns n:int
ensures pure (n == 5)  // heap-independent predicate fun s -> (n == 5)
{ 
  fstar_five
}
```

```pulse
fn incr (r:ref int) (#n:erased int) // since n is purely specificational, it is erased
  requires pts_to r n
  ensures pts_to r (n + 1)
{
    let x = !r;
    r := x + 1
}
```

```pulse
fn incr_frame (x y: ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y 'j
{
  incr x
}
```

```pulse
fn incr_frame_any (x: ref int) (f: vprop)
requires pts_to x 'i ** f
ensures pts_to x ('i + 1) ** f
{
  incr x
}
```

```pulse
fn read (r:ref int) p (n:erased int) // any permission is ok for reading
requires pts_to r #p n
returns x:int
ensures pts_to r #p n ** pure (x == n)
{
    !r
}
```

```pulse
fn write (r:ref int) (n:erased int) // write requires full permission
  requires pts_to r #full_perm n
  ensures pts_to r #full_perm n
{
    let y = !r;
    r := y
}
```

[@@ expect_failure] // fails
```pulse
fn write (r:ref int) p (n:erased int)
  requires pts_to r #p n
  ensures pts_to r #p n
{
    let y = !r;
    r := y
}
```

```pulse
fn incr2 (r1 r2:ref int)
  requires pts_to r1 'n1 ** pts_to r2 'n2
  ensures pts_to r1 ('n1 + 1) ** pts_to r2 ('n2 + 1)
{
    // pts_to r1 ‘n1 ** pts_to r2 ‘n2
    incr r1;

    // pts_to r1 (‘n1 + 1) ** pts_to r2 ‘n2
    incr r2;

    // pts_to r1 (‘n1 + 1) ** pts_to r2 (‘n2 + 1)
}
```

```pulse
fn incr_stack ()
  requires emp
  returns x:int
  ensures pure (x == 1)
{
    let mut i = 0;
    incr i;
    !i  // explicit dereference, no need to free i, automatically reclaimed when the function returns
}
```

module Box = Pulse.Lib.Box
```pulse
fn incr_heap ()
  requires emp
  returns x:int
  ensures pure (x == 1)
{
    let r = Box.alloc 0;
    Box.to_ref_pts_to r;  // explicit coercions from Box to ref, we plan to automate these coercions in the prover
    incr (Box.box_to_ref r);
    Box.to_box_pts_to r;
    let x = Box.(!r);
    Box.free r;  // need to free explicitly
    x
}
```

//Exercise 1: Fill in the spec and implementation of swap
```pulse
fn swap #a (r1 r2:ref a)
requires emp
ensures emp
{
    admit()
}
```
