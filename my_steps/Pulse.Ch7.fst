module Pulse.Ch7

open Pulse.Lib.Pervasives
open FStar.Mul
open Pulse.Lib.Array
module SZ = FStar.SizeT

// # Mutable Arrays

// # array t

```pulse
fn read_i
  (#[@@@ Rust_generics_bound ["Copy"]] t:Type)
  (arr:array t)
  (#p:perm)
  (#s:erased (Seq.seq t))
  (i:SZ.t { SZ.v i < Seq.length s})
  requires pts_to arr #p s
  returns x:t
  ensures pts_to arr #p s ** pure (x == Seq.index s (SZ.v i))
{
  arr.(i)
}
```

```pulse
fn write_i (#t:Type) (arr:array t) (#s:erased (Seq.seq t)) (x:t) (i:SZ.t { SZ.v i < Seq.length s })
  requires pts_to arr s
  ensures pts_to arr (Seq.upd s (SZ.v i) x)
{
  arr.(i) <- x
}
```

// # Compare

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
open FStar.SizeT

```pulse
fn compare
  (#[@@@ Rust_generics_bound ["PartialEq"; "Copy"]] t:eqtype)
  #p1 #p2
  (a1 a2:A.array t)
  (l:SZ.t)
  requires (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  returns res:bool
  ensures (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (res <==> Seq.equal 's1 's2)
  )
{
  let mut i = 0sz;
  while (
    let vi = !i;
    if (vi <^ l) {
      let v1 = a1.(vi);
      let v2 = a2.(vi);
      (v1 = v2)
    } else {
      false
    }
  )
  invariant b.
  exists* vi. ( 
    R.pts_to i vi **
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l && Seq.index 's1 (SZ.v vi) = Seq.index 's2 (SZ.v vi))) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index 's1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i; 
    i := vi +^ 1sz
  };
  let vi = !i;
  let res = vi = l;
  res
}
```

// # Copy

```pulse
fn copy
  (#[@@@ Rust_generics_bounds ["Copy"]] t:Type0)
  (a1 a2:A.array t)
  (l:SZ.t)
  (#p2:perm)
  requires (
    A.pts_to a1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  ensures (
    (exists* s1. A.pts_to a1 s1 ** pure (Seq.equal s1 's2)) **
    A.pts_to a2 #p2 's2
  )
{
  let mut i = 0sz;
  while (
    let vi = !i;
    (vi <^ l)
  )
  invariant b.
  exists* vi s1. ( 
    R.pts_to i vi **
    A.pts_to a1 s1 **
    A.pts_to a2 #p2 's2 **
    pure (
      Seq.length s1 == Seq.length 's2 /\
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l)) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index s1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i;
    let v = a2.(vi);
    a1.(vi) <- v;
    i := vi +^ 1sz
  }
}
```

// # Stack allocated arrays

```pulse
fn compare_stack_arrays ()
  requires emp
  ensures emp
{
  // |- emp
  let mut a1 = [| 0; 2sz |];
  // a1:array int |- pts_to a1 (Seq.create 0 (SZ.v 2))
  let mut a2 = [| 0; 2sz |];
  // a1 a2:array int |- pts_to a1 (Seq.create 0 (SZ.v 2)) ** pts_to a2 (Seq.create 0 (SZ.v 2))
  let b = compare a1 a2 2sz;
  assert (pure b)
}
```

// # Heap allocated arrays

module V = Pulse.Lib.Vec

```pulse 
fn heap_arrays ()
  requires emp
  returns a:V.vec int
  ensures V.pts_to a (Seq.create 2 0)
{
  let a1 = V.alloc 0 2sz;
  let a2 = V.alloc 0 2sz;
  V.free a1;
  a2  // returning vec is ok
}
```