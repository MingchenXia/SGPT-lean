import SGPT.Foundations.Analysis.Pending.DiagonalTangentialReduction

set_option autoImplicit false

/-!
# The normal decomposition of `A - π^*B` for an arbitrary `ℂ`-linear projection

`DiagonalTangentialReduction.sub_compDiagProj_eq` decomposes `A - B ∘ π` for the FIXED linear
projection `π(u, u') = (u, u)` of a product chart onto the diagonal.  For the graph of a
holomorphic map `f` the projection becomes point dependent: at a chart point `ζ = (z, w)` it is the
derivative `π_ζ(ξ, η) = (ξ, DF(z) ξ)` of `(z, w) ↦ (z, F(z))`.  This module states the decomposition
for an arbitrary `ℂ`-linear `π` with a normal decomposition `ξ - π ξ = ∑ₐ ℓₐ(ξ) Nₐ`
(`sub_comp_eq`):

`A - B ∘ π = ∑ₐ ∑_c A(Nₐ, h_c) Π₁₁(ℓₐ ∧ s_c) + ∑_{c,d} ((A - B)(πE_c, πE_d)/2) Π₁₁(s_c ∧ s_d)`,

`h_c = πE_c + (E_c - πE_c)/2`, for `(1,1)`-forms `A`, `B`.  The proof is the one of the diagonal case
(`twoForm_sub_comp`, `twoForm_eq_sum`), which never used the particular `π`.

Step G2 of the graph support plan,
requested by TN-CLASSICAL (earlier discussion the statement under discussion) for the graph route of the `(P)` step of
Boucksom 4.8.
-/

noncomputable section

open Set

namespace SGPT.Foundations.Analysis.Pending.GraphTangentialAlgebra

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents ClosedProductCurrents CurrentTraceMeasure
  CurrentRestriction SlotTestForms CarriedCurrentTests TopDegreeDensity NormalDirectionVanishing
  DiagonalTangentialReduction

variable {N : ℕ}

/-- The vectors `πE_c + (E_c - πE_c)/2`. -/
def halfVecOf (π : ComplexModel N →L[ℂ] ComplexModel N) (c : Fin (2 * N)) : ComplexModel N :=
  π (topBasis N c) + (1 / 2 : ℝ) • (topBasis N c - π (topBasis N c))

theorem halfVecOf_sum (π : ComplexModel N →L[ℂ] ComplexModel N) (ζ : ComplexModel N) :
    π ζ + (1 / 2 : ℝ) • (ζ - π ζ) = ∑ c, coordFun c ζ • halfVecOf π c := by
  have hlin : ∀ v : ComplexModel N, π v + (1 / 2 : ℝ) • (v - π v) =
      (π.restrictScalars ℝ + (1 / 2 : ℝ) •
        (ContinuousLinearMap.id ℝ (ComplexModel N) - π.restrictScalars ℝ)) v :=
    fun v => rfl
  rw [hlin]
  conv_lhs => rw [← sum_coordFun_smul ζ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ← hlin]
  rfl

/-- **The decomposition of `A - π^*B`** for a `ℂ`-linear `π` with `ξ - πξ = ∑ₐ ℓₐ(ξ) Nₐ`: a sum of
`(1,1)`-parts of `ℓₐ ∧ s_c` (normal) and of `s_c ∧ s_d` with coefficients `(A - B)(πE_c, πE_d)/2`. -/
theorem sub_comp_eq (π : ComplexModel N →L[ℂ] ComplexModel N) {ι : Type*} [Fintype ι]
    (ℓ : ι → ComplexModel N →L[ℝ] ℝ) (Nv : ι → ComplexModel N)
    (hν : ∀ ξ, ξ - π ξ = ∑ a, ℓ a ξ • Nv a) (A B : RealForm N 2) (hA : IsOneOne A)
    (hB : IsOneOne B) :
    A - B.compContinuousLinearMap (π.restrictScalars ℝ) =
      (∑ a, ∑ c, A ![Nv a, halfVecOf π c] • pi11 (pairForm (ℓ a) (coordFun c))) +
        ∑ c, ∑ d, ((A - B) ![π (topBasis N c), π (topBasis N d)] / 2) •
          pi11 (pairForm (coordFun c) (coordFun d)) := by
  set π' : ComplexModel N →L[ℝ] ComplexModel N := π.restrictScalars ℝ with hπ'
  have hπ : ∀ v, π' (Complex.I • v) = Complex.I • π' v := fun v => π.map_smul _ v
  have hlhs : IsOneOne (A - B.compContinuousLinearMap π') := by
    have hBπ := isOneOne_compContinuousLinearMap hB π' hπ
    intro u v
    simp only [ContinuousAlternatingMap.sub_apply]
    rw [hA u v, hBπ u v]
  have key : A - B.compContinuousLinearMap π' =
      (∑ a, ∑ c, A ![Nv a, halfVecOf π c] • pairForm (ℓ a) (coordFun c)) +
        ∑ c, ∑ d, ((A - B) ![π (topBasis N c), π (topBasis N d)] / 2) •
          pairForm (coordFun c) (coordFun d) := by
    ext v
    rw [eq_vec_two v]
    set ξ := v 0
    set η := v 1
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      pairForm_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two]
    have h1 := twoForm_sub_comp A π' ℓ Nv hν ξ η
    have h2 := twoForm_eq_sum ((A - B).compContinuousLinearMap π') ξ η
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two,
      ContinuousAlternatingMap.sub_apply] at h2
    have hexp : ∀ (a : ι) (ζ : ComplexModel N),
        A ![Nv a, π' ζ + (1 / 2 : ℝ) • (ζ - π' ζ)] =
          ∑ c, coordFun c ζ * A ![Nv a, halfVecOf π c] := by
      intro a ζ
      rw [show π' ζ = π ζ from rfl, halfVecOf_sum, ← twoFormBilin_apply, map_sum]
      simp only [map_smul, smul_eq_mul, twoFormBilin_apply]
    simp only [hexp] at h1
    have hfirst : A ![ξ, η] - A ![π' ξ, π' η] =
        ∑ a, ∑ c, A ![Nv a, halfVecOf π c] *
          (ℓ a ξ * coordFun c η - ℓ a η * coordFun c ξ) := by
      rw [h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have hsecond : A ![π' ξ, π' η] - B ![π' ξ, π' η] =
        ∑ c, ∑ d, (A ![π' (topBasis N c), π' (topBasis N d)] -
          B ![π' (topBasis N c), π' (topBasis N d)]) / 2 *
            (coordFun c ξ * coordFun d η - coordFun c η * coordFun d ξ) := h2
    rw [show A ![ξ, η] - B ![π' ξ, π' η] =
      (A ![ξ, η] - A ![π' ξ, π' η]) + (A ![π' ξ, π' η] - B ![π' ξ, π' η]) by ring,
      hfirst, hsecond]
    rfl
  rw [← pi11_eq_self hlhs, key, pi11_add, pi11_sum, pi11_sum]
  simp only [pi11_sum, pi11_smul]

/-- The diagonal case is the instance `π = diagProj n` (consistency check). -/
theorem sub_compDiagProj_eq' {n : ℕ} (A B : RealForm (n + n) 2) (hA : IsOneOne A)
    (hB : IsOneOne B) :
    A - B.compContinuousLinearMap ((diagProj n).restrictScalars ℝ) =
      (∑ a, ∑ c, A ![normalVec a, halfVecOf (diagProj n) c] • pi11 (pairForm (normalRe a) (coordFun c))) +
        ∑ c, ∑ d, ((A - B) ![diagProj n (topBasis (n + n) c), diagProj n (topBasis (n + n) d)] /
          2) • pi11 (pairForm (coordFun c) (coordFun d)) :=
  sub_comp_eq (diagProj n) normalRe normalVec sub_diagProj_eq A B hA hB

end SGPT.Foundations.Analysis.Pending.GraphTangentialAlgebra
