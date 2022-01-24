/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import section02reals.sheet3 -- import the definition of `tendsto` from a previous sheet

-- you can maybe do this one now
theorem tendsto_neg {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  intros ε εpos,
  specialize ha ε εpos, cases ha with B pf,
  use B, intros n hn, ring_nf,
  specialize pf n hn,
  have lem1 : | - a n + t | = | - (a n - t) |,
  { ring_nf, },
  have lem2 : | - a n + t| = |a n - t|,
  { rw lem1, exact abs_neg (a n - t),  },
  rw lem2, exact pf,
end

/-
`tendsto_add` is quite a challenge. In a few weeks' time I'll
show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsto_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n + b n) (t + u) :=
begin
  intros ε εpos,
  specialize ha (ε/2) (half_pos εpos),
  specialize hb (ε/2) (half_pos εpos),
  cases ha with B1 pf1,
  cases hb with B2 pf2,
  use (max B1 B2), intros n hn,
  have bnd1 : B1 ≤ n,
  { exact trans (le_max_left B1 B2) hn },
  have bnd2 : B2 ≤ n,
  { exact trans (le_max_right B1 B2) hn },
  specialize pf1 n bnd1,
  specialize pf2 n bnd2,
  ring_nf,
  have lem1 : |a n - t| + |b n - u| < ε / 2 + | b n - u|,
  { linarith, },
  have lem2 : ε / 2 + | b n - u| < ε,
  { linarith, },
  refine trans _ lem2,
  refine gt_of_gt_of_ge lem1 _,
  have tri_ineq : | a n - t + (b n - u) | ≤ |a n - t | + |b n - u |,
  { exact abs_add (a n - t) (b n - u)},
  have lem3 : | a n - t + (b n - u) | = | a n + (b n + (-t - u))|,
  { ring_nf },
  rw <- lem3, exact tri_ineq,
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n - b n) (t - u) :=
begin
  have hbneg : (tendsto (λ n, - b n) (- u)),
  { exact tendsto_neg hb },
  apply tendsto_add ha hbneg,
end
