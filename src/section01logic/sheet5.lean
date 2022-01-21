/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intros h, rw h,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split; {intros assump; rw assump},
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros pq qr, split;
  { rw pq, rw qr, exact id },
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split; rintros ⟨p, q⟩; split; assumption,
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  { rintros ⟨⟨p, q⟩, r⟩, split; try {split}; assumption, },
  { rintros ⟨p, ⟨q, r⟩⟩, split; try {split}; assumption, },
end

example : P ↔ (P ∧ true) :=
begin
  split; intros p; try {cases p}; try {split}; try {assumption}; try {triv},
end

example : false ↔ (P ∧ false) :=
begin
  split; try {rintros ⟨⟩}; try {rintros ⟨_,⟨⟩⟩}, try {assumption},
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros pq rs, split,
  {  rw pq, rw rs, exact id, },
  {  rw pq, rw rs, exact id, }
end

example : ¬ (P ↔ ¬ P) :=
begin
  intros contra, cases contra with for bac, apply for;
  { by_contra not_p, apply not_p, apply bac, assumption },
end
