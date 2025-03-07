module Pulse.Ch6

open Pulse.Lib.Pervasives
open FStar.Mul

// # Loops & Recursion

// # Countdown

```pulse
fn count_down (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
  let mut keep_going = true;
  while (!keep_going)
  invariant b.
    exists* v.
      pts_to keep_going b ** 
      pts_to x v **
      pure (b == false ==> v == 0)
  {
    let n = !x;
    if (n = 0) {
      keep_going := false;
    } else {
      x := n - 1;
    }
  }
}
```

```pulse
fn count_down2 (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        } 
        else
        {
            x := n - 1;
            true
        }
    )
    invariant b. 
      exists* v.
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}
```

// # Partial correctness

```pulse
fn count_down_loopy (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        }
        else
        {
            x := n + 1;
            true
        }
    )
    invariant b. 
      exists* v.
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}
```

// # Multiply by repeated addition

```pulse
fn multiply_by_repeated_addition(x y: nat)
  requires emp
  returns z:nat
  ensures pure (z == x * y)
{
  let mut ctr : nat = 0;    
  let mut acc : nat = 0;
  while (
    let c = !ctr;
    (c < x)
  )
  invariant b.
  exists* c a.
    pts_to ctr c **
    pts_to acc a **
    pure (c <= x /\ a == (c * y) /\ b == (c < x))
  {
    let a = !acc;
    acc := a + y;
    let c = !ctr;
    ctr := c + 1;
  };
  !acc
}
```

// # Summing the first N numbers

let rec sum (n:nat)
  : nat
  = if n = 0 then 0 else n + sum (n - 1)
  
#push-options "--z3rlimit 20"
noextract
let rec sum_lemma (n:nat)
  : Lemma (sum n == n * (n + 1) / 2)
= if n = 0 then ()
  else sum_lemma (n - 1)
#pop-options

#push-options "--z3cliopt 'smt.arith.nl=false'"
noextract
```pulse
fn issum (n:nat)
requires emp
returns z:nat
ensures pure ((n * (n + 1) / 2) == z)
{
  let mut acc : nat = 0;
  let mut ctr : nat = 0;
  while (
    let c = !ctr;
    (c < n)
  )
  invariant b.
  exists* c a.
    pts_to ctr c **
    pts_to acc a **
    pure (
      c <= n /\
      a == sum c /\
      b == (c < n)
    )
  {
    let a = !acc;
    let c = !ctr;
    ctr := c + 1;
    acc := a + c + 1;
  };
  sum_lemma n;
  !acc;
}
```

// # Recursion

let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)
  
```pulse
fn rec fib_rec (n:pos) (out:ref (nat & nat))
requires 
  pts_to out 'v
ensures
  exists* v.
    pts_to out v **
    pure (
      fst v == fib (n - 1) /\
      snd v == fib n
    )
{
  if ((n = 1)) {
    out := ((1 <: nat), (1 <: nat));
  } else {
    fib_rec (n - 1) out;
    let v = !out;
    out := (snd v, fst v + snd v);
  }
}
```

```pulse
fn fib_loop (k:pos)
  requires emp
  returns r:nat
  ensures pure (r == fib k)
{
  let mut i : nat = 1;
  let mut j : nat = 1;
  let mut ctr : nat = 1;
  while (
    let c = !ctr;
    (c < k)
  )
  invariant b . 
    exists* vi vj vctr. 
        pts_to i vi **
        pts_to j vj **
        pts_to ctr vctr **
        pure (
            1 <= vctr /\
            vctr <= k /\
            vi == fib (vctr - 1) /\
            vj == fib vctr /\
            b == (vctr < k)
        )
  {
      let vi = !i;
      let vj = !j;
      let c = !ctr;
      ctr := c + 1;
      i := vj;
      j := vi + vj;
  };
  !j
}
```