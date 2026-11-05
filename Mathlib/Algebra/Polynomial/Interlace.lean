/-
Copyright (c) 2026 Erik Barkeling, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Barkeling, Yaël Dillies
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.List.Interleave

/-!
# Interlacing and interleaving polynomials

## References

https://arxiv.org/pdf/1410.6601
-/

public section

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
