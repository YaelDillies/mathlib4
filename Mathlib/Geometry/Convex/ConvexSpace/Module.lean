/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Order
public import Mathlib.Geometry.Convex.Star
public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.NormNum.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Abel

/-!
# Modules are convex spaces

This file shows that every module over ordered coefficients is a convex space.

## Main declarations

* `ConvexSpace.ofModule`: A semimodule space over a semiring is a convex space.
* `convexSpaceSelf`: A semiring is a convex space over itself.
* `IsModuleConvexSpace`: Predicate for a convex space and module structures to be compatible.

We also show that a linearly ordered module is an ordered convex space
(`IsOrderedConvexSpace.ofModule`), by Abel summation.
-/

open scoped Pointwise

public noncomputable section

namespace Convexity
variable {F R M N I : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

section AddCommMonoid
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [SetLike F M]
  [AddSubmonoidClass F M] [SMulMemClass F R M] {f g : M → N}

/-- Any semimodule over an ordered semiring is a convex space.

This is not an instance because it creates a diamond with structural instances such as
`ConvexSpace R X → ConvexSpace R Y → ConvexSpace R (X × Y)` because
`(∑ i, f i).fst = ∑ i, (f i).fst` isn't defeq, ultimately because `Finset.sum` isn't a field of
`AddCommMonoid` but derived from them through recursion. -/
@[expose, implicit_reducible]
def ConvexSpace.ofModule : ConvexSpace R M where
  sConvexComb w := w.weights.sum fun m r ↦ r • m
  sConvexComb_single := by simp
  assoc := by
    simp [Finsupp.sum_mapDomain_index, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      mul_smul, Finsupp.smul_sum]

instance convexSpaceSelf : ConvexSpace R R := .ofModule

variable (R M) [ConvexSpace R M] in
/-- Typeclass for a convex space structure on a module to be given by weighted sums. -/
class IsModuleConvexSpace : Prop where
  sConvexComb_eq_sum (w : StdSimplex R M) : w.sConvexComb = w.weights.sum fun m r ↦ r • m

export IsModuleConvexSpace (sConvexComb_eq_sum)
attribute [simp] sConvexComb_eq_sum

@[deprecated (since := "2026-04-03")]
alias _root_.convexCombination_eq_sum := sConvexComb_eq_sum

attribute [local instance] ConvexSpace.ofModule in
instance IsModuleConvexSpace.ofModule : IsModuleConvexSpace R M where
  sConvexComb_eq_sum _ := rfl

@[deprecated "Implied by `IsModuleConvexSpace.ofModule`" (since := "2026-07-02")]
lemma isModuleConvexSpace_self : IsModuleConvexSpace R R := inferInstance

section IsModuleConvexSpace
variable [ConvexSpace R M] [IsModuleConvexSpace R M] [ConvexSpace R N] [IsModuleConvexSpace R N]
  {x y : M} {s t : Set M} {a b : R}

/-- `iConvexComb` in a module can be expressed as a sum. -/
@[simp]
lemma iConvexComb_eq_sum (w : StdSimplex R I) (f : I → M) :
    w.iConvexComb f = w.weights.sum fun i r ↦ r • f i := by
  simp [iConvexComb, sConvexComb_eq_sum, Finsupp.sum_mapDomain_index, add_smul]

lemma StdSimplex.affineMapMk_apply_eq_sum_of_fintype
    [Fintype I] (f : I → M) (w : StdSimplex R I) :
    StdSimplex.affineMapMk (R := R) f w = ∑ (i : I), w.weights i • f i := by
  rw [affineMapMk_apply, iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]

lemma StdSimplex.coe_affineMapMk_of_fintype [Fintype I] (f : I → M) :
    ⇑(StdSimplex.affineMapMk (R := R) f) =
      fun w ↦ ∑ (i : I), w.weights i • f i := by
  ext
  rw [StdSimplex.affineMapMk_apply_eq_sum_of_fintype]

/-- `convexCombPair` in a module can be expressed as a sum. -/
@[simp]
lemma convexCombPair_eq_sum (a b : R) (ha hb hab) (x y : M) :
    convexCombPair a b ha hb hab x y = a • x + b • y := by
  classical simp [convexCombPair, sConvexComb_eq_sum, Finsupp.sum_add_index, add_smul]

lemma IsAffineMap.map_sum_weights (hf : IsAffineMap R f) (w : StdSimplex R I) (g : I → M) :
    f (w.weights.sum fun i r ↦ r • g i) = w.weights.sum fun i r ↦ r • f (g i) := by
  simpa using hf.map_iConvexComb w g

lemma IsAffineMap.map_smul_add_smul (hf : IsAffineMap R f) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (x y : M) : f (a • x + b • y) = a • f x + b • f y := by
  simpa using hf.map_convexCombPair ha hb hab x y

@[simp] lemma isConvexSet_coe (S : F) : IsConvexSet R (S : Set M) := by
  refine .of_sConvexComb_mem fun w hw ↦ ?_
  rw [sConvexComb_eq_sum]
  exact AddSubmonoidClass.finsuppSum_mem _ _ _ fun m hm ↦ SMulMemClass.smul_mem _ <| hw <| by simpa

instance (S : F) : ConvexSpace R S := .subtype _ <| isConvexSet_coe _

@[simp]
lemma subtypeVal_submodule_sConvexComb (S : F) (w : StdSimplex R S) :
    (w.sConvexComb : M) = w.iConvexComb (↑) := rfl

lemma subtypeVal_submodule_iConvexComb (S : F) (w : StdSimplex R I) (f : I → S) :
    (↑(w.iConvexComb f) : M) = w.iConvexComb (fun i ↦ (f i).val) := subtypeVal_iConvexComb ..

lemma subtypeVal_submodule_convexCombPair (S : F) (a b : R) (ha hb hab) (x y : S) :
    (↑(convexCombPair a b ha hb hab x y) : M) = convexCombPair a b ha hb hab x.val y.val :=
  subtypeVal_convexCombPair ..

instance (S : F) : IsModuleConvexSpace R S where sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]

instance : IsModuleConvexSpace R (M × N) where
  sConvexComb_eq_sum w := by ext <;> simp [Finsupp.sum, Prod.fst_sum, Prod.snd_sum]

instance {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, ConvexSpace R (M i)] [∀ i, IsModuleConvexSpace R (M i)] :
    IsModuleConvexSpace R (∀ i, M i) where
  sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]

instance {ι : Type*} : IsModuleConvexSpace R (ι →₀ M) where
  sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]

@[to_fun (attr := fun_prop)]
lemma IsAffineMap.add (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (f + g) where
  map_sConvexComb w := by
    simp [hf.map_sum_weights, hg.map_sum_weights, Finsupp.sum_mapDomain_index, add_smul]

lemma IsStarConvexSet.add (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R y t) :
    IsStarConvexSet R (x + y) (s + t) := by
  rw [← Set.add_image_prod]; exact (hs.prod ht).image (by fun_prop)

end IsModuleConvexSpace

variable (R I) in
lemma StdSimplex.isAffineMap_weights : IsAffineMap R (weights (R := R) (M := I)) where
  map_sConvexComb s := by simp [sConvexComb_eq_sum, Finsupp.sum_mapDomain_index, add_smul]

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [ConvexSpace R M] [IsModuleConvexSpace R M] [ConvexSpace R N] [IsModuleConvexSpace R N]
  {x y : M} {s t : Set M} {f g : M → N}

@[to_fun (attr := fun_prop)]
lemma IsAffineMap.neg (hf : IsAffineMap R f) : IsAffineMap R (-f) where
  map_sConvexComb w := by simp [hf.map_sum_weights, Finsupp.sum_mapDomain_index, add_smul]

@[to_fun (attr := fun_prop)]
lemma IsAffineMap.sub (hf : IsAffineMap R f) (hg : IsAffineMap R g) : IsAffineMap R (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma IsStarConvexSet.neg (hs : IsStarConvexSet R x s) : IsStarConvexSet R (-x) (-s) := by
  rw [← Set.image_neg_eq_neg]; exact hs.image (by fun_prop)

lemma IsStarConvexSet.sub (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R y t) :
    IsStarConvexSet R (x - y) (s - t) := by
  rw [← Set.sub_image_prod]; exact (hs.prod ht).image (by fun_prop)

end AddCommGroup

section OrderedModule
variable [AddCommGroup M] [Module R M]

omit [PartialOrder R] [IsStrictOrderedRing R] in
open Finset in
/-- **Abel summation**: a weighted sum `∑ k < n, c k • y k` is determined by the tail sums of `c`
and the increments of `y`. -/
private lemma sum_smul_eq_sum_tail_smul_sub (n : ℕ) (c : ℕ → R) (y : ℕ → M) :
    ∑ k ∈ range n, c k • y k =
      (∑ k ∈ range n, c k) • y 0 +
        ∑ i ∈ range n, (∑ k ∈ Ico (i + 1) n, c k) • (y (i + 1) - y i) := by
  have step (k : ℕ) : c k • y k = c k • y 0 + ∑ i ∈ range k, c k • (y (i + 1) - y i) := by
    rw [← Finset.smul_sum, sum_range_sub, smul_sub]
    abel
  rw [sum_congr rfl fun k _ ↦ step k, sum_add_distrib, ← Finset.sum_smul]
  congr 1
  rw [sum_comm' (t' := range n) (s' := fun i ↦ Ico (i + 1) n) (by intro k i; simp; omega)]
  exact sum_congr rfl fun i _ ↦ Finset.sum_smul.symm

variable [LinearOrder M] [IsOrderedAddMonoid M] [SMulPosMono R M]

omit [IsStrictOrderedRing R] in
open Finset in
/-- If the tail sums of `a` are dominated by those of `b` and the two have the same total, then
`∑ a k • y k ≤ ∑ b k • y k` for any monotone `y`. This is Abel summation plus the fact that the
increments of `y` are nonnegative. -/
private lemma sum_smul_le_sum_smul {n : ℕ} {a b : ℕ → R} {y : ℕ → M} (hy : Monotone y)
    (hab : ∑ k ∈ range n, a k = ∑ k ∈ range n, b k)
    (h : ∀ i, ∑ k ∈ Ico i n, a k ≤ ∑ k ∈ Ico i n, b k) :
    ∑ k ∈ range n, a k • y k ≤ ∑ k ∈ range n, b k • y k := by
  rw [sum_smul_eq_sum_tail_smul_sub n a y, sum_smul_eq_sum_tail_smul_sub n b y, hab]
  gcongr with i hi
  · exact sub_nonneg.2 (hy i.le_succ)
  · exact h (i + 1)

variable [ConvexSpace R M] [IsModuleConvexSpace R M]

open Finset in
/-- A linearly ordered module is an ordered convex space: replacing the points of a convex
combination by larger ones, or moving weight from smaller points to larger ones, can only increase
the combination.

The proof is by Abel summation over the union of the two supports, enumerated in increasing
order. -/
instance (priority := low) IsOrderedConvexSpace.ofModule : IsOrderedConvexSpace R M where
  monotone_sConvexComb w₁ w₂ hw := by
    -- Enumerate the union `S` of the two supports in increasing order as `y 0 < … < y (n - 1)`.
    set S := w₁.weights.support ∪ w₂.weights.support with hSdef
    have hS₁ : w₁.weights.support ⊆ S := subset_union_left
    have hS₂ : w₂.weights.support ⊆ S := subset_union_right
    obtain ⟨n, hn⟩ : ∃ n, S.card = n := ⟨_, rfl⟩
    have hpos : 0 < n := hn ▸ card_pos.2 (w₁.support_weights_nonempty.mono hS₁)
    set e := S.orderEmbOfFin hn with he
    obtain ⟨y, hyk, hy⟩ : ∃ y : ℕ → M, (∀ k, ∀ hk : k < n, y k = e ⟨k, hk⟩) ∧ Monotone y :=
      ⟨fun k ↦ e ⟨min k (n - 1), by omega⟩,
        fun k hk ↦ by
          have hmin : min k (n - 1) = k := by omega
          simp only [hmin],
        fun k l hkl ↦ e.monotone (by simp only [Fin.mk_le_mk]; omega)⟩
    have hinj : ∀ k ∈ range n, ∀ l ∈ range n, y k = y l → k = l := by
      simp only [mem_range]
      intro k hk l hl hkl
      rw [hyk k hk, hyk l hl] at hkl
      simpa using e.injective hkl
    have hle : ∀ i < n, ∀ k < n, (y i ≤ y k ↔ i ≤ k) := fun i hi k hk ↦ by
      rw [hyk i hi, hyk k hk, e.le_iff_le, Fin.mk_le_mk]
    have himg : (range n).image y = S := by
      rw [← Finset.image_orderEmbOfFin_univ S hn, ← he]
      ext x
      simp only [mem_image, mem_range, Finset.mem_univ, true_and]
      exact ⟨fun ⟨k, hk, hkx⟩ ↦ ⟨⟨k, hk⟩, by rwa [← hyk k hk]⟩,
        fun ⟨i, hix⟩ ↦ ⟨i, i.2, by rwa [hyk i i.2]⟩⟩
    -- Sums over `S` are sums over `range n`.
    have hsumM (f : M → M) : ∑ x ∈ S, f x = ∑ k ∈ range n, f (y k) := by
      rw [← himg, Finset.sum_image hinj]
    have hsumR (f : M → R) : ∑ x ∈ S, f x = ∑ k ∈ range n, f (y k) := by
      rw [← himg, Finset.sum_image hinj]
    have hcomb (w : StdSimplex R M) (hwS : w.weights.support ⊆ S) :
        w.sConvexComb = ∑ k ∈ range n, w.weights (y k) • y k := by
      rw [sConvexComb_eq_sum w, Finsupp.sum, Finset.sum_subset hwS, hsumM]
      intro x _ hx
      rw [Finsupp.notMem_support_iff.1 hx, zero_smul]
    have htotal (w : StdSimplex R M) (hwS : w.weights.support ⊆ S) :
        ∑ k ∈ range n, w.weights (y k) = 1 := by
      have hw := w.total
      rw [Finsupp.sum] at hw
      rw [← hsumR, ← Finset.sum_subset hwS fun x _ hx ↦ Finsupp.notMem_support_iff.1 hx, hw]
    have hupper (w : StdSimplex R M) (hwS : w.weights.support ⊆ S) (i : ℕ) (hi : i < n) :
        w.upperMass (y i) = ∑ k ∈ Ico i n, w.weights (y k) := by
      have hfilter : (range n).filter (fun k ↦ y i ≤ y k) = Ico i n := by
        ext k
        simp only [mem_filter, mem_range, mem_Ico]
        exact ⟨fun h ↦ ⟨(hle i hi k h.1).1 h.2, h.1⟩, fun h ↦ ⟨h.2, (hle i hi k h.2).2 h.1⟩⟩
      rw [StdSimplex.upperMass_eq_sum,
        Finset.sum_subset (Finset.filter_subset_filter _ hwS) (fun x hx hx' ↦ by
          by_contra h
          exact hx' (Finset.mem_filter.2
            ⟨Finsupp.mem_support_iff.2 h, (Finset.mem_filter.1 hx).2⟩)),
        ← himg, Finset.filter_image, hfilter,
        Finset.sum_image fun k hk l hl ↦ hinj k (mem_range.2 (mem_Ico.1 hk).2) l
          (mem_range.2 (mem_Ico.1 hl).2)]
    rw [hcomb w₁ hS₁, hcomb w₂ hS₂]
    refine sum_smul_le_sum_smul hy ((htotal w₁ hS₁).trans (htotal w₂ hS₂).symm) fun i ↦ ?_
    rcases lt_or_ge i n with hi | hi
    · rw [← hupper w₁ hS₁ i hi, ← hupper w₂ hS₂ i hi]
      exact StdSimplex.le_def.1 hw _
    · rw [Finset.Ico_eq_empty (by omega)]
      simp

end OrderedModule
end Convexity
