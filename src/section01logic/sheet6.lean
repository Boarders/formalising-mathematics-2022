/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intros p, left, assumption,
end

example : Q → P ∨ Q :=
begin
  intros q, right, assumption,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros pq pr qr, cases pq with p q,
  { apply pr, assumption},
  { apply qr, assumption},
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intros pq, cases pq with p q,
  { right, assumption },
  { left, assumption },
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  { intros pqr, cases pqr with pq r,
    { cases pq, {left, assumption }, {right, left, assumption} },
    { right, right, assumption},
  },
  { intros pqr, cases pqr with p qr,
    { left, left, assumption },
    { cases qr, { left, right, assumption }, { right, assumption }, },
  },
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros pr qs p_or_q, cases p_or_q with p q,
  { left, apply pr, assumption },
  { right, apply qs, assumption },
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros pq p_or_r, cases p_or_r with p q,
  { left, apply pq, assumption },
  { right, assumption }
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros pr qs, cases pr with pr rp, cases qs with qs sq, split,
  { intros pq, cases pq, {left, apply pr, assumption}, { right, apply qs, assumption } },
  { intros rs, cases rs, {left, apply rp, assumption}, { right, apply sq, assumption },},
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  { intros not_pq, split,
      { intros p, apply not_pq, left, assumption },
      { intros q, apply not_pq, right, assumption},
  },
  { intros pq, cases pq with not_p not_q, intros p_or_q, cases p_or_q,
    { apply not_p, assumption },
    { apply not_q, assumption },
  },
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  { intros not_pq, by_cases hP : P,
    { right, intros q, apply not_pq, split; assumption, },
    { left, assumption, },
  },
  { intros pq, cases pq with not_p not_q;
    { intros p_and_q, cases p_and_q, try {apply not_p}, try {apply not_q}, try {assumption}, },
  },
end
