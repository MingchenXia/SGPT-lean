import SGPT.Okounkov.ThetaCurrentPullbackCompatibility
import SGPT.Okounkov.FlagLiftingComposition
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial
import SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity

set_option autoImplicit false
universe u
noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions Manifold ContDiff

namespace SGPT.Okounkov

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame CanonicalSmoothCurrentDensity
open NaturalThetaPshGeometricCurrent GlobalPositiveCurrentACRestriction
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- The actual smooth current reads only genuine chart-target coefficients.
Its off-target test integrands are zero, not substituted geometric data. -/
theorem smoothGlobalCurrent_eq_of_geometricallyEq
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {k : CurrentDegree n} {a b : SmoothRealForm n M k.val}
    (hab : a.GeometricallyEq b) :
    smoothGlobalCurrent (canonicalBasis n) a =
      smoothGlobalCurrent (canonicalBasis n) b := by
  apply GlobalCurrent.ext
  intro e η
  rw [smoothGlobalCurrent_apply_eq_integral_topDensity,
    smoothGlobalCurrent_apply_eq_integral_topDensity]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ e.val.target
  · rw [hab e hx]
  · have hη : η x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hxs => hx (η.tsupport_subset hxs))
    rw [hη]
    simp only [ConstantFormProducts.wedgeTo_zero_right]

/-- Same-function theta currents retain all their supported data when the
actual smooth backgrounds are geometrically equal. -/
theorem thetaPotentialCurrent_eq_of_geometricallyEq
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ σ : SmoothRealForm (m + 1) M 2} (hθσ : θ.GeometricallyEq σ)
    {v : M → EReal} (hvθ : IsThetaPshPotential θ v)
    (hvσ : IsThetaPshPotential σ v) :
    thetaPotentialCurrent θ v hvθ = thetaPotentialCurrent σ v hvσ := by
  unfold thetaPotentialCurrent
  rw [smoothGlobalCurrent_eq_of_geometricallyEq hθσ]

/-- Genuine geometric form functoriality gives actual whole-current
composition through the literal original flag maps. -/
theorem thetaPotentialModificationCurrent_comp
    {m : ℕ} {F W V : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (v : F.carrier → EReal)
    (hv : IsThetaPshPotential θ.val v) :
    thetaPotentialModificationCurrent (hπ.comp hp) θ v hv =
      thetaPotentialModificationCurrent hp
        (ClosedRealOneOneForm.pullback hπ.1.1 θ) (v ∘ π)
        (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
          hπ.1 θ hv) := by
  apply thetaPotentialCurrent_eq_of_geometricallyEq
  exact SmoothRealForm.pullback_comp_geometricallyEq hπ.1.1 hp.1.1 θ.val

/-- An arbitrary original full current internally supplies both whole
pullbacks and their readbacks for ALL original and intermediate representations.
No representation or desired composition equality is a caller premise. -/
theorem exists_original_current_modification_pullback_comp
    {m : ℕ} {F W V : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p)
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (R : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m)))
      (S : GlobalCurrent (m + 1) V.carrier (degreeTwo (Nat.succ_pos m))),
      (R.IsClosed (canonicalBasis (m + 1)) ∧
        R.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive R) ∧
      (S.IsClosed (canonicalBasis (m + 1)) ∧
        S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive S) ∧
      (∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (v : F.carrier → EReal)
        (hv : IsThetaPshPotential θ.val v), T = thetaPotentialCurrent θ.val v hv →
        R = thetaPotentialModificationCurrent hπ θ v hv ∧
        S = thetaPotentialModificationCurrent (hπ.comp hp) θ v hv) ∧
      ∀ (σ : ClosedRealOneOneForm (m + 1) W.carrier) (w : W.carrier → EReal)
        (hw : IsThetaPshPotential σ.val w), R = thetaPotentialCurrent σ.val w hw →
        S = thetaPotentialModificationCurrent hp σ w hw := by
  obtain ⟨R, hR, _huniqR⟩ :=
    exists_unique_original_current_modification_pullback hπ T hc h11 hT
  obtain ⟨S, hS, _huniqS⟩ :=
    exists_unique_original_current_modification_pullback (hπ.comp hp) T hc h11 hT
  refine ⟨R, S, ⟨hR.1, hR.2.1, hR.2.2.1⟩,
    ⟨hS.1, hS.2.1, hS.2.2.1⟩, ?_, ?_⟩
  · intro θ v hv hread
    exact ⟨hR.2.2.2 θ v hv hread, hS.2.2.2 θ v hv hread⟩
  · intro σ w hw hreadR
    obtain ⟨θ, v, hv, hread, _hchart⟩ :=
      OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
        T hc h11 hT
    let hvπ := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ.1 θ hv
    have hrepR : thetaPotentialCurrent
        (ClosedRealOneOneForm.pullback hπ.1.1 θ).val (v ∘ π) hvπ =
        thetaPotentialCurrent σ.val w hw :=
      (hR.2.2.2 θ v hv hread).symm.trans hreadR
    exact (hS.2.2.2 θ v hv hread).trans
      ((thetaPotentialModificationCurrent_comp hπ hp θ v hv).trans
        (thetaPotentialModificationCurrent_eq_of_thetaPotentialCurrent_eq hp hvπ hw hrepR))

end SGPT.Okounkov
