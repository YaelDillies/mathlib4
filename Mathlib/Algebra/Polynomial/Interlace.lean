/-
Copyright (c) 2026 Erik Barkeling, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Barkeling, Yaël Dillies
-/
module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# Interlacing and interleaving polynomials

## References

https://arxiv.org/pdf/1410.6601
-/

public section

namespace List
variable {α : Type*} {r s : α → α → Prop} {l l₁ l₂ : List α} {a b c : α}

@[expose]
def interleave : List α → List α → List α
  | _, [] => []
  | l₁, a :: l₂ => a :: interleave l₂ l₁
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp] lemma interleave_nil (l₁ : List α) : l₁.interleave [] = [] := by rw [interleave]

@[simp]
lemma interleave_cons (l₁ : List α) (a : α) (l₂ : List α) :
    l₁.interleave (a :: l₂) = a :: interleave l₂ l₁ := by rw [interleave]

lemma left_sublist_interleave : ∀ {l₁ l₂ : List α}, l₁.length ≤ l₂.length → l₁ <+ l₁.interleave l₂
  | [], _, _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [interleave_cons]
    exact .cons _ <| .cons_cons _ <| left_sublist_interleave <| by simpa using h

lemma right_sublist_interleave :
  ∀ {l₁ l₂ : List α}, l₂.length ≤ l₁.length + 1 → l₂ <+ l₁.interleave l₂
  | [], [], _ => by simp
  | [], [a], _ => by simp
  | a :: l₁, [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [interleave_cons]
    exact .cons_cons _ <| .cons _ <| right_sublist_interleave <| by simpa using h

variable (r) in
@[mk_iff]
inductive Interleaves : List α → List α → Prop
  | nil_nil : Interleaves [] []
  | nil_singleton (a : α) : Interleaves [] [a]
  | cons_symm ⦃l₁ l₂ : List α⦄ ⦃b : α⦄ (hl : Interleaves l₁ (b :: l₂)) ⦃a : α⦄ (hab : r a b) :
      Interleaves (b :: l₂) (a :: l₁)

attribute [simp] Interleaves.nil_nil Interleaves.nil_singleton

@[simp]
lemma interleaves_nil_cons : Interleaves r [] (a :: l) ↔ l = [] := by rw [interleaves_iff]; simp

@[simp]
lemma not_interleaves_cons_nil : ¬ Interleaves r (a :: l) [] := by rw [interleaves_iff]; simp

@[simp]
lemma interleaves_singleton_singleton : Interleaves r [a] [b] ↔ r b a := by
  rw [interleaves_iff]; simp

@[gcongr]
lemma Interleaves.mono (hrs : ∀ ⦃a b⦄, r a b → s a b) :
    ∀ l₁ l₂ : List α, Interleaves r l₁ l₂ → Interleaves s l₁ l₂
  | _, _, .nil_nil => .nil_nil
  | _, _, .nil_singleton a => .nil_singleton _
  | _, _, .cons_symm hl hab => .cons_symm (hl.mono hrs) <| hrs hab

lemma interleaves_iff_length_isChain :
    ∀ {l₁ l₂ : List α},
    Interleaves r l₁ l₂ ↔
      (l₁.length = l₂.length ∨ l₁.length + 1 = l₂.length) ∧ (l₁.interleave l₂).IsChain r
  | [], [] => by simp
  | [], b :: l₂ => by simp
  | a :: l₁, [] => by simp
  | a :: l₁, [b] => by rw [interleaves_iff]; simp
  | a :: l₁, b :: l₂ => by
    rw [interleaves_iff]
    simp only [reduceCtorEq, and_self, cons.injEq, false_and, exists_false, ↓existsAndEq, true_and,
      exists_eq_right_right', false_or, length_cons, Nat.add_right_cancel_iff, interleave_cons,
      isChain_cons_cons]
    rw [interleaves_iff_length_isChain]
    simp [or_comm, eq_comm, and_comm, and_assoc]
termination_by l₁ l₂ => l₁.length + l₂.length

variable [IsTrans α r]

lemma Interleaves.pairwise_left (hl : Interleaves r l₁ l₂) : l₁.Pairwise r := by
  rw [interleaves_iff_length_isChain] at hl
  exact hl.2.pairwise.sublist <| left_sublist_interleave <| by lia

lemma Interleaves.pairwise_right (hl : Interleaves r l₁ l₂) : l₂.Pairwise r := by
  rw [interleaves_iff_length_isChain] at hl
  exact hl.2.pairwise.sublist <| right_sublist_interleave <| by lia

end List

namespace Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R] [IsOrderedRing R]

inductive Interleaves : R[X] → R[X] → Prop
  | zero_zero : Interleaves 0 0
  | zero_of_leadingCoeff_left_pos ⦃P : R[X]⦄ (hP : P.Splits) (hP₀ : 0 < P.leadingCoeff) :
    Interleaves P 0
  | zero_of_leadingCoeff_right_pos ⦃Q : R[X]⦄ (hQ : Q.Splits) (hQ₀ : 0 < Q.leadingCoeff) :
    Interleaves 0 Q
  | of_interleaves_roots
      ⦃P : R[X]⦄ (hP : P.Splits) (hP₀ : 0 < P.leadingCoeff)
      ⦃Q : R[X]⦄ (hQ : Q.Splits) (hQ₀ : 0 < Q.leadingCoeff)
      (hPQ : (P.roots.sort (· ≥ ·)).Interleaves (· ≥ ·) (Q.roots.sort (· ≥ ·))) : Interleaves P Q

inductive StrictInterleaves : R[X] → R[X] → Prop
  | zero_zero : StrictInterleaves 0 0
  | zero_of_leadingCoeff_left_pos ⦃P : R[X]⦄ (hP : P.Splits) (hP₀ : 0 < P.leadingCoeff) :
    StrictInterleaves P 0
  | zero_of_leadingCoeff_right_pos ⦃Q : R[X]⦄ (hQ : Q.Splits) (hQ₀ : 0 < Q.leadingCoeff) :
    StrictInterleaves 0 Q
  | of_interleaves_roots
      ⦃P : R[X]⦄ (hP : P.Splits) (hP₀ : 0 < P.leadingCoeff)
      ⦃Q : R[X]⦄ (hQ : Q.Splits) (hQ₀ : 0 < Q.leadingCoeff)
      (hPQ : (P.roots.sort (· ≥ ·)).Interleaves (· > ·) (Q.roots.sort (· ≥ ·))) :
    StrictInterleaves P Q

end Polynomial
