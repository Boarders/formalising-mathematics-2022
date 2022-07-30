/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intros not_t, apply not_t, triv,
end

example : false → ¬ true :=
begin
  intros f _, exact f,
end

example : ¬ false → true :=
begin
  intros _, triv
end

example : true → ¬ false :=
begin
  intros _ f, exact f,
end

example : false → ¬ P :=
begin
  intros f p, exact f
end

example : P → ¬ P → false :=
begin
  intros p not_p, apply not_p, exact p,
end

example : P → ¬ (¬ P) :=
begin
--  non-constructive proof by constradiction:
--  intros p, by_contra not_p, apply not_p, exact p,
  intros p not_p, apply not_p, exact p
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros p_q not_q p, apply not_q, apply p_q, exact p,
end

example : ¬ ¬ false → false :=
begin
  intros not_not_f, by_contra not_f, apply not_not_f, exact not_f
end

example : ¬ ¬ P → P :=
begin
  intros not_not_p, by_contra not_p, apply not_not_p, exact not_p
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros notq_notp p, by_contra not_q, apply notq_notp,
  {exact not_q},
  {exact p}
end
