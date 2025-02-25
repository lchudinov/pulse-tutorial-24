module Pulse.Ch3

open Pulse.Lib.Pervasives


// # Existential Quantification

```pulse
fn assign #a (x:ref a) (v:a)
requires
  exists* w. pts_to x w
ensures
  pts_to x v
{
  x := v
}
```

[@expect_failure]
```pulse
fn incr #a (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  pts_to x (w0 + 1) // w0 is not in scope here for postcondition
{
  let w = !x;
  x := w + 1
}
```

```pulse
fn make_even (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  let v = !x;
  x := v + v;
}
```

// # Manipulating existentials

```pulse
fn make_even_explicit (x:ref int)
requires
  exists* w0. pts_to x w0
ensures
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
{
  with w0. assert (pts_to x w0);
  let v = !x;
  x := v + v;
  introduce
  exists* w1. pts_to x w1 ** pure (w1 % 2 == 0)
  with (v + v);
}
```

// ## Eliminating existentials



