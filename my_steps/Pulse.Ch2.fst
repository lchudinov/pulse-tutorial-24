module Pulse.Ch2

open Pulse.Lib.Pervasives
open FStar.Mul

// # Mutable References

// ## ref t: Stack or Heap References


```pulse
fn swap #a (r0 r1: ref a)
requires pts_to r0 'v0 ** pts_to r1 'v1
ensures pts_to r0 'v1 ** pts_to r1 'v0
{
  let v0 = !r0;
  let v1 = !r1;
  r0 := v1;
  r1 := v0;
}
```

// ## Reading a reference
```pulse
fn value_of (#a:Type) (r:ref a)
requires pts_to r 'v
returns v:a
ensures pts_to r 'v ** pure (v == 'v)
{
  !r;
}
```

```pulse
fn value_of_explicit (#a:Type) (r:ref a) (#w:erased a)
requires pts_to r w
returns v:a
ensures pts_to r w ** pure (v == reveal w)
{
  !r;
}
```

// ## Erased values are for specification and proof only

// ```pulse
// fn value_of_explicit_fail (#a:Type) (r:ref a) (#w:erased a)
// requires pts_to r w
// returns v:a
// ensures pts_to r w ** pure (v == reveal w)
// {
//     reveal w // error: Expected a Total computation, but got Ghost
// }
// ```

// ## Writing through a reference

```pulse
fn assign (#a:Type) (r:ref a) (v:a)
requires pts_to r 'v
ensures pts_to r v
{
  r := v;
}
```

// ## Dereferencing is explicit

```pulse
fn add (r:ref int) (n:int)
requires pts_to r 'v
ensures pts_to r ('v + n)
{
  let v = !r;
  r := v + n;
}
```

```pulse
fn quadruple (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
  let v1 = !r;
  add r v1;
  // show_proof_state;
  let v2 = !r;
  add r v2;
}
```

// ## Stateful commands are explicitly sequenced

[@expect_failure]
```pulse
fn quad_fail (r:ref int)
requires pts_to r 'v
ensures pts_to r (4 * 'v)
{
  add r (!r);
  add r (!r);
}
```
// - Expected type "int"; but "!r" has type
//   "stt int
//        (pts_to r (reveal (*?u93*) _))
//        (fun x -> pts_to r x ** pure (reveal (*?u93*) _ == x))"

// ## Fractional Permissions

// open PulseCore.FractionalPermission

```pulse
fn assign_full_perm (#a:Type) (r:ref a) (v:a)
requires pts_to r #full_perm 'v
ensures pts_to r #full_perm v
{
  r := v;
}
```

```pulse
fn value_of_perm #a #p (r:ref a)
requires pts_to r #p 'v
returns v:a
ensures pts_to r #p 'v ** pure (v == 'v)
{
  !r;
}
```

#push-options "--print_implicits"
[@expect_failure] // If we try to write to a reference without holding full permission on it, Pulse rejects the program, as shown below
```pulse
fn assign_perm #a #p (r:ref a) (v:a) (#w: erased a)
requires pts_to r #p w
ensures pts_to r #p w
{
  r := v;
}
```
#pop-options

```pulse
fn share_ref #a #p (r:ref a)
requires pts_to r #p 'v
ensures pts_to r #(half_perm p) 'v ** pts_to r #(half_perm p) 'v
{
  share r;
}
```


```pulse
fn gather_ref #a #p (r:ref a)
requires 
  pts_to r #(half_perm p) 'v0 **
  pts_to r #(half_perm p) 'v1
ensures pts_to r #p 'v0 ** pure ('v0 == 'v1)
{
  gather r;
}
```

// # Stack references

// let mut creates a new stack ref

```pulse // I copied the incr code from the previous chapter
fn incr (r:ref int)
requires pts_to r 'v
ensures pts_to r ('v + 1)
{
    let v = !r;
    r := v + 1;
}
```

```pulse
fn one()
requires emp
returns v:int
ensures pure (v == 1)
{
                 // .          |- emp
  let mut i = 0; // i: ref int |- pts_to i 0
  incr i;        // i: ref int |- pts_to i (0 + 1)
  !i             // .          |- v:int. emp ** pure (v == 1)
}
```

// ## Stack references are scoped and implicitly reclaimed

[@expect_failure]
```pulse
fn refs_are_scoped ()
requires emp
returns s:ref int
ensures pts_to s 0
{
    let mut s = 0;
    s
  // - Cannot prove:
  //     pts_to s 0
  // - In the context:
  //     emp
}
```

// # Heap references

module Box = Pulse.Lib.Box

```pulse
fn new_heap_ref (#a: Type) (v: a)
requires emp
returns r:Box.box a
ensures Box.pts_to r v
{
  Box.alloc v
}
```

```pulse
fn last_value_off #a (r:Box.box a)
requires Box.pts_to r 'v
returns v:a
ensures pure (v == 'v)
{
  open Box;
  let v = !r;
  free r;
  v
}
```

```pulse
fn incr_box (r:Box.box int)
requires Box.pts_to r 'v
ensures Box.pts_to r ('v + 1)
{
  Box.to_ref_pts_to r;     // Box.pts_to (box_to_ref r) 'v
  incr (Box.box_to_ref r); // pts_to (box_to_ref r) ('v + 1)
  Box.to_box_pts_to r      // Box.pts_to r ('v + 1)
}
```
