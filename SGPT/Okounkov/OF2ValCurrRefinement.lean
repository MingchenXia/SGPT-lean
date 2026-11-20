import SGPT.Okounkov.OF2AlgebraicCorMatrix
import SGPT.Okounkov.OF2ValCurrPresentation
import SGPT.Okounkov.CurrentFlagCorrection
import SGPT.Okounkov.AnalyticModificationCurrent

/-!
# `rmk:valcurr`: invariance of `ν(T)` under refinement of the model

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`: `ν(T) := ν_{Y•}(π^*T) g` for a
presentation `ν = ν_{Y•} g` on a resolution `π`, "independent of `π`, by passing to a common
resolution and applying `prop:cormatrix`, `prop:cormult`".

Let `X` be an integral smooth projective complex scheme of dimension `n = m + 1`, `π : X' → X(ℂ)`
a modification from a compact connected Kähler manifold with a smooth flag `F•` and `G`
unitriangular with `ν = (ν_{F•} ∘ π^*) G` (a *presentation* of `ν`). For a closed positive
`(1,1)`-current `T = θ + dd^c v` on `X(ℂ)`, the value of the presentation is
`ν_{F•}(π^*T) G` (`modificationPresentationValue`).

* `modificationPresentationValue_lifting` (**refinement invariance**): if `p : X'' → X'` lifts
  `F•` to `W•`, then `ν = (ν_{W•} ∘ (π p)^*) (cor(F•, p)⁻¹ G)` is a presentation on `π ∘ p` with the
  same value `ν(T)`; for surjective `ν`, every presentation of `ν` on `(π ∘ p, W•)` has this matrix
  (`OF2.matrix_eq_of_lexMapValuation_eq`), hence this value.

The proof is the book's: the algebraic `prop:cormatrix` (`OF2.modificationFlagValuation_lifting`)
for the valuations, the current `prop:cormatrix`
(`SGPT.Okounkov.exists_originalCurrentFlagValuation_pullback_correctionMatrix`) and the
composition of pull-backs for the currents.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF2

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open scoped Matrix

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance of2RefTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2RefCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of2RefManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The value `ν_{F•}(π^*T) G` of a presentation on a modification, for `T = θ + dd^c v`. -/
def modificationPresentationValue (F : OriginalFlagGeometry.{0} (m + 1))
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := m + 1) π)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (v : SchemeComplexPoint f → EReal)
    (hv : IsThetaPshPotential θ.val v) : Fin (m + 1) → ℝ :=
  (fun i => (currentFlagValuation F (analyticModificationThetaCurrent hπ θ v hv)
      (analyticModificationThetaCurrent_closed_type_positive hπ θ v hv).1
      (analyticModificationThetaCurrent_closed_type_positive hπ θ v hv).2.1
      (analyticModificationThetaCurrent_closed_type_positive hπ θ v hv).2.2 i : ℝ)) ᵥ*
    (Int.castRingHom ℝ).mapMatrix G

omit [IsIntegral X] in
/-- `currentFlagValuation` only depends on the current. -/
theorem currentFlagValuation_congr_current' (F : OriginalFlagGeometry.{0} (m + 1))
    {T T' : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m))} (h : T = T')
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT : IsFullPositive T)
    (hc' : T'.IsClosed (canonicalBasis (m + 1)))
    (h11' : T'.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT' : IsFullPositive T') :
    currentFlagValuation F T hc h11 hT = currentFlagValuation F T' hc' h11' hT' := by
  subst h
  rfl

omit [IsIntegral X] in
/-- The value only depends on the current `T`, not on its representation `θ + dd^c v`. -/
theorem modificationPresentationValue_eq_of_eq (F : OriginalFlagGeometry.{0} (m + 1))
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := m + 1) π)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    {θ σ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)}
    {v w : SchemeComplexPoint f → EReal}
    (hv : IsThetaPshPotential θ.val v) (hw : IsThetaPshPotential σ.val w)
    (heq : thetaPotentialCurrent θ.val v hv = thetaPotentialCurrent σ.val w hw) :
    modificationPresentationValue f F hπ G θ v hv =
      modificationPresentationValue f F hπ G σ w hw := by
  unfold modificationPresentationValue
  have h := analyticModificationThetaCurrent_eq_of_eq hπ hv hw heq
  rw [currentFlagValuation_congr_current' F h _ _ _
    (analyticModificationThetaCurrent_closed_type_positive hπ σ w hw).1
    (analyticModificationThetaCurrent_closed_type_positive hπ σ w hw).2.1
    (analyticModificationThetaCurrent_closed_type_positive hπ σ w hw).2.2]

/-- **`rmk:valcurr`, refinement invariance.** A presentation `ν = (ν_{F•} ∘ π^*) G` on `π` and a
lifting `p` of `F•` to `W•` give the presentation `ν = (ν_{W•} ∘ (π p)^*) (cor(F•, p)⁻¹ G)` on
`π ∘ p`, with the same value `ν(T)`. -/
theorem modificationPresentationValue_lifting {F W : OriginalFlagGeometry.{0} (m + 1)}
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := m + 1) π)
    {p : W.carrier → F.carrier} (hp : IsFlagLifting F W p)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    {G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG : IsUnitUpperTriangular G)
    (hpres : v = lexMapValuation G hG (modificationFlagValuation f F hπ))
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    v = lexMapValuation ((flagLiftingCorrectionMatrix (m + 1) F W p hp)⁻¹ * G)
        ((isUnitUpperTriangular_flagLiftingCorrectionMatrix (m + 1) F W p hp).inv.mul hG)
        (modificationFlagValuation f W
          (AnalyticModificationComposition.isAnalyticModification_comp hπ hp.1)) ∧
      modificationPresentationValue f W
          (AnalyticModificationComposition.isAnalyticModification_comp hπ hp.1)
          ((flagLiftingCorrectionMatrix (m + 1) F W p hp)⁻¹ * G) θ u hu =
        modificationPresentationValue f F hπ G θ u hu := by
  have hcor := modificationFlagValuation_lifting f hπ hp
  have hC := isUnitUpperTriangular_flagLiftingCorrectionMatrix (m + 1) F W p hp
  set C := flagLiftingCorrectionMatrix (m + 1) F W p hp with hCdef
  set hπp := AnalyticModificationComposition.isAnalyticModification_comp hπ hp.1 with hπpdef
  refine ⟨?_, ?_⟩
  · -- the valuation
    rw [hpres]
    apply AddValuation.ext
    intro r
    rw [lexMapValuation_apply, lexMapValuation_apply, hcor, lexMapValuation_apply,
      lexWithTopHom_mul, lexWithTopHom_congr (show C * (C⁻¹ * G) = G by
        rw [← Matrix.mul_assoc, hC.mul_inv, Matrix.one_mul]) _ hG]
  · -- the current value
    set T' := analyticModificationThetaCurrent hπ θ u hu with hT'def
    obtain ⟨hc', h11', hT'⟩ := analyticModificationThetaCurrent_closed_type_positive hπ θ u hu
    obtain ⟨R, ⟨hcR, h11R, hR, hall, -, hmat⟩, -⟩ :=
      exists_originalCurrentFlagValuation_pullback_correctionMatrix hp T' hc' h11' hT'
    have hu' :=
      AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
        hπ θ hu
    have hRrep : R = thetaPotentialModificationCurrent hp (ClosedRealOneOneForm.pullback hπ.1 θ)
        (u ∘ π) hu' := hall _ _ hu' rfl
    have hcomp : analyticModificationThetaCurrent hπp θ u hu = R := by
      rw [hRrep]
      exact analyticModificationThetaCurrent_comp hπ hp.1 θ u hu
    unfold modificationPresentationValue
    rw [currentFlagValuation_congr_current' W hcomp _ _ _ hcR h11R hR]
    rw [← hmat]
    rw [map_mul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc]
    have hCC : (Int.castRingHom ℝ).mapMatrix C * (Int.castRingHom ℝ).mapMatrix C⁻¹ = 1 := by
      rw [← map_mul, hC.mul_inv, map_one]
    have hcast : (fun i j => (C i j : ℝ)) = (Int.castRingHom ℝ).mapMatrix C := by
      ext i j
      simp
    rw [hcast, hCC, Matrix.one_mul]

end SGPT.Okounkov.OF2
