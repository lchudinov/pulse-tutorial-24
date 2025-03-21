module Pulse.Ch9

open Pulse.Lib.Pervasives
open FStar.Mul
open Pulse.Lib.Array
open Pulse.Lib.Box

// Higher Order Functions

// Pulse Computation Types

```pulse
fn apply (#a:Type0)
         (#b:a -> Type0)
         (#pre:a -> vprop)
         (#post:(x:a -> b x -> vprop))
         (f: (x:a -> stt (b x) (pre x) (fun y -> post x y)))
         (x:a)
requires pre x
returns y:b x
ensures post x y
{
  f x
}
```

// # Counters

noeq
type ctr = {
    inv: int -> vprop;
    next: i:erased int -> stt int (inv i) (fun y -> inv (i + 1) ** pure (y == reveal i));
    destroy: i:erased int -> stt unit (inv i) (fun _ -> emp)
}

```pulse
fn new_counter ()
requires emp
returns c:ctr
ensures c.inv 0
{
    let x = alloc 0;
    fn next (i:erased int)
    requires pts_to x i 
    returns j:int
    ensures pts_to x (i + 1) ** pure (j == reveal i)
    {
        let j = !x;
        x := j + 1;
        j
    };
    fn destroy (i:erased int)
    requires pts_to x i
    ensures emp
    {
       free x
    };
    let c = { inv = pts_to x; next; destroy };
    rewrite (pts_to x 0) as (c.inv 0);
    c
}
```

let next c = c.next
let destroy c = c.destroy

```pulse
fn test_counter ()
requires emp
ensures emp
{
    let c = new_counter ();
    let x = next c _; //FIXME: Should be able to write c.next
    assert pure (x == 0);
    let x = next c _;
    assert pure (x == 1);
    destroy c _;
}
```