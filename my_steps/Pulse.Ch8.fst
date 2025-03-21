module Pulse.Ch8

open Pulse.Lib.Pervasives
open FStar.Mul
open Pulse.Lib.Array

// # Ghost Computations

// # Ghost Functions

[@@expect_failure]
```pulse
fn incr_erased_non_ghost (x:erased int)
requires emp
returns y:int
ensures emp ** pure (y == x + 1)
{
  let x = reveal x; // Error: Cannot bind ghost expression reveal x with ST computation
  (x + 1)
}
```

```pulse
ghost
fn incr_erased (x:erased int)
requires emp
returns y:int
ensures emp ** pure (y == x + 1)
{
  let x = reveal x;
  (x + 1)
}
```

[@@expect_failure]
```pulse
fn use_incr_erased (x:erased int)
requires emp
returns y:int
ensures emp ** pure (y == x + 1)
{
  incr_erased x; // Error:  Expected a term with a non-informative (e.g., erased) type; got int
}
```

```pulse
fn use_incr_erased (x:erased int)
requires emp
returns y:erased int
ensures emp ** pure (y == x + 1)
{
  ghost
  fn wrap (x:erased int)
  requires emp
  returns y:erased int
  ensures emp ** pure (y == x + 1)
  {
    let y = incr_erased x;
    hide y
  };
  wrap x
}
```

```pulse
fn use_incr_erased_alt (x:erased int)
requires emp
returns y:erased int
ensures emp ** pure (y == x + 1)
{ 
  call_ghost incr_erased x;
}
```

```pulse
ghost
fn add_erased (x y:erased int)
requires emp
returns z:int
ensures emp ** pure (z == x + y)
{
  let x = reveal x;
  let y = reveal y;
  (x + y)
}
```

```pulse
fn use_add_erased (x y:erased int)
requires emp
returns z:erased int
ensures emp ** pure (z == x + y)
{
  call_ghost (add_erased x) y
}
```

```pulse
ghost
fn add_erased_erased (x y:erased int)
requires emp
returns z:erased int
ensures emp ** pure (z == x + y)
{
  let x = reveal x;
  let y = reveal y;
  hide (x + y)
}
```

// # Some Primitive Ghost Functions

// I not intend to finish this chapter
