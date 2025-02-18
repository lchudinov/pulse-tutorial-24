module Pulse.Ch2

open Pulse.Lib.Pervasives

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

