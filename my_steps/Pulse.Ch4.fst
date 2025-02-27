module Pulse.Ch4

open Pulse.Lib.Pervasives
open FStar.Mul

// # User-defined Predicates

// pts_to_diag r v is a vprop - a refrerence to a pair whose components are equal
let pts_to_diag #a (r:ref (a & a)) (v:a)
  : vprop
  = pts_to r (v, v)

```pulse
fn double (r: ref(int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold (pts_to_diag r 'v);
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  fold (pts_to_diag r v2);
}
```

```pulse
fn double_alt (r: ref(int & int))
requires pts_to_diag r 'v
ensures pts_to_diag r (2 * 'v)
{
  unfold pts_to_diag;
  let v = !r;
  let v2 = fst v + snd v;
  r := (v2, v2);
  fold pts_to_diag r;
}
```

// # Mutable Points

noeq
type point = {
  x:ref int;
  y:ref int;
}

let is_point (p:point) (xy: int & int) =
  pts_to p.x (fst xy) **
  pts_to p.y (snd xy)


```pulse
fn move (p: point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold(is_point p (x + dx, y + dy));
}
```

```pulse
ghost
fn fold_is_point (p:point)
requires pts_to p.x 'x ** pts_to p.y 'y
ensures is_point p (reveal 'x, reveal 'y)
{
  fold (is_point p (reveal 'x, reveal 'y))
}
```

```pulse
fn move_alt (p: point) (dx:int) (dy:int)
requires is_point p 'xy
ensures is_point p (fst 'xy + dx, snd 'xy + dy)
{
  unfold is_point;
  let x = !p.x;
  let y = !p.y;
  p.x := x + dx;
  p.y := y + dy;
  fold_is_point p;
}
```

// # Rewriting

```pulse
fn create_and_move ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    //pts_to x 0 ** pts_to y 0
    with _v. rewrite pts_to x _v as pts_to p.x _v;
    with _v. rewrite pts_to y _v as pts_to p.y _v;
    //pts_to p.x 0 ** pts_to p.y 0
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    //pts_to p.x (fst (1, 1)) ** pts_to p.y (snd (1, 1))
    with _v. rewrite pts_to p.x _v as pts_to x _v;
    with _v. rewrite pts_to p.y _v as pts_to y _v;
    //pts_to x (fst (1, 1)) ** pts_to y (snd (1, 1))
}
```

```pulse
fn create_and_move_alt ()
requires emp
ensures emp
{
    let mut x = 0;
    let mut y = 0;
    let p = { x; y };
    rewrite each x as p.x, y as p.y;
    fold_is_point p;
    move p 1 1;
    assert (is_point p (1, 1));
    unfold is_point;
    rewrite each p.x as x, p.y as y;
}
```