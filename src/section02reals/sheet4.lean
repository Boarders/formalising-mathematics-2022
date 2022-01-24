/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

/-

# Figuring out how to use the reals

## The `library_search` tactic

We saw in the previous sheet that we couldn't even prove something
as simple as "if `aₙ → L` then `-aₙ → -L`" because when you write down
the proof carefully, it relies on the fact that `|x - y| = |y - x|`
or, equivalently, that `|(-x)| = |x|`. I say "equivalently" because
`ring` will prove that `-(x - y) = y - x`.

You don't want to be proving stuff like `|x - y| = |y - x|` from first
principles. Someone else has already done all the hard work for you.
All you need to do is to learn how to find out the names of the lemmas.
The `library_search` tactic tells you the names of all these lemmas. 
See where it says "try this" -- click there and Lean will replace
`library_search` with the actual name of the lemma. Once you've done
that, hover over the lemma name to see in what generality it holds.

## The `linarith` tactic

Some of the results below are bare inequalities which are too complex
to be in the library. The library contains "natural" or "standard"
results, but it doesn't contain a random inequality fact just because
it happens to be true -- the library just contains "beautiful" facts.

The `linarith` tactic is a tactic which can solve some equalities and inequalities
in ordered structures like the naturals or reals. Unlike `ring`, `linarith`
does look at hypotheses in the tactic state. For example if you have
hypotheses `h1 : a < b` and `h2 : b ≤ c` then `linarith` would prove
a goal of `⊢ a < c`.

However `linarith` doesn't know about anything other than `=`, `≠`,
`<` and `≤`, so don't expect it to prove any results about `|x|` or
`max A B`.

Experiment with the `library_search` and `linarith` tactics below.
Try and learn something about the naming convention which Lean uses;
see if you can start beginning to guess what various lemmas should be called.

-/

example (x : ℝ) : |(-x)| = |x| :=
begin
  sorry
end

example (x y : ℝ) : |x - y| = |y - x| :=
begin
  sorry
end 

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C :=
begin
  sorry
end

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y :=
begin
  sorry
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 :=
begin
  sorry,
end

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y :=
begin
  sorry,
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 :=
begin
  sorry,
end

example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) :
  a + b + c + d < x + y :=
begin
  sorry
end
/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

/-

# Figuring out how to use the reals

## The `library_search` tactic

We saw in the previous sheet that we couldn't even prove something
as simple as "if `aₙ → L` then `-aₙ → -L`" because when you write down
the proof carefully, it relies on the fact that `|x - y| = |y - x|`
or, equivalently, that `|(-x)| = |x|`. I say "equivalently" because
`ring` will prove that `-(x - y) = y - x`.

You don't want to be proving stuff like `|x - y| = |y - x|` from first
principles. Someone else has already done all the hard work for you.
All you need to do is to learn how to find out the names of the lemmas.
The `library_search` tactic tells you the names of all these lemmas.
See where it says "try this" -- click there and Lean will replace
`library_search` with the actual name of the lemma. Once you've done
that, hover over the lemma name to see in what generality it holds.

## The `linarith` tactic

Some of the results below are bare inequalities which are too complex
to be in the library. The library contains "natural" or "standard"
results, but it doesn't contain a random inequality fact just because
it happens to be true -- the library just contains "beautiful" facts.

The `linarith` tactic is a tactic which can solve some equalities and inequalities
in ordered structures like the naturals or reals. Unlike `ring`, `linarith`
does look at hypotheses in the tactic state. For example if you have
hypotheses `h1 : a < b` and `h2 : b ≤ c` then `linarith` would prove
a goal of `⊢ a < c`.

However `linarith` doesn't know about anything other than `=`, `≠`,
`<` and `≤`, so don't expect it to prove any results about `|x|` or
`max A B`.

Experiment with the `library_search` and `linarith` tactics below.
Try and learn something about the naming convention which Lean uses;
see if you can start beginning to guess what various lemmas should be called.

-/
example (a b : ℝ) : a ≤ max a b :=
begin
  exact le_max_left a b,
end

example (a b c : ℝ) : |a + b| ≤ | a | + | b | :=
begin
  exact abs_add a b,
end

example (a b c : ℝ) (ab : a ≥ b) : b ≤ a :=
begin
  linarith,
end

example (x : ℝ) : |(-x)| = |x| :=
begin
  exact abs_neg x
end

example (x y : ℝ) : |x - y| = |y - x| :=
begin
  exact abs_sub_comm x y,
end

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C :=
begin
  split,
  { intros hP, split,
    { exact le_of_max_le_left hP, },
    { exact le_of_max_le_right hP, }
  },
  { rintro ⟨ac, bc⟩, exact max_le ac bc, },
end

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y :=
begin
  exact abs_lt,
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 :=
begin
   exact half_pos hε,
end

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y :=
begin
  exact add_lt_add h1 h2,
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 :=
begin
  have l1 : ε/2/2 = ε/4,
  { ring, },
  have hε_4 : 0 < ε / 4,
  { rw <- l1, exact half_pos (half_pos hε), },
  have εlem : ε / 4 < ε / 3,
  { linarith, },
  exact trans hε_4 εlem,
end

example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) :
  a + b + c + d < x + y :=
begin
  have h3 : (a + c) + (b + d) < x + y,
  { exact add_lt_add h1 h2 },
  have h4 : a + b + c + d = (a + c) + (b + d),
  { ring },
  rw h4, exact h3
end
