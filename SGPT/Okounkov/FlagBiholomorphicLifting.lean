import SGPT.Okounkov.FlagBiholomorphicCorrection
import SGPT.Okounkov.PartialBodyBirational
import SGPT.Okounkov.FlagLiftingTail
import SGPT.Okounkov.SourceTestCurveAllDimensions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Okounkov.ToricTransport
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalLifting
open scoped Topology Manifold ContDiff

/-- Actual whole flag images give the literal forward restriction. -/
theorem mapsTo_flag_of_image {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i) (i : Fin (n + 1)) :
    MapsTo e (W.flag i) (F.flag i) := by
  intro x hx
  rw [← he i]
  exact ⟨x, hx, rfl⟩

/-- The inverse restriction is produced from the SAME whole actual flag
images; it is not an additional flag-lifting hypothesis. -/
theorem mapsTo_flag_symm_of_image {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i) (i : Fin (n + 1)) :
    MapsTo e.symm (F.flag i) (W.flag i) := by
  intro x hx
  rw [← he i] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [Homeomorph.symm_apply_apply] using hy

/-- Every actual whole flag image also holds in the genuine inverse direction. -/
theorem image_flag_symm_of_image {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i) (i : Fin (n + 1)) :
    e.symm '' F.flag i = W.flag i := by
  rw [← he i, ← Set.image_comp]
  simp only [Homeomorph.symm_comp_self, Set.image_id]

/-- The genuine component homeomorphism on the SAME original subspace
topologies, constructed from the actual map/inverse and whole flag images. -/
def flagComponentHomeomorph {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i) (i : Fin (n + 1)) :
    W.flag i ≃ₜ F.flag i where
  toFun x := ⟨e x.val, mapsTo_flag_of_image e he i x.property⟩
  invFun x := ⟨e.symm x.val, mapsTo_flag_symm_of_image e he i x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- A genuine whole-flag biholomorphism PRODUCES the existing ORIGINAL
IsFlagLifting in all dimensions. Both component holomorphies are restrictions
in the actual inherited atlases; actual identity transport constructs every
analytic modification, with no supplied trace/valuation/body certificate. -/
theorem isFlagLifting_of_biholomorphic {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    IsFlagLifting F W e := by
  refine ⟨?_, fun i => ⟨mapsTo_flag_of_image e he i, ?_⟩⟩
  · exact isAnalyticModification_biholomorphic_transport (Homeomorph.refl F.carrier) e
      contMDiff_id contMDiff_id hf hg isAnalyticModification_identity
  · let := F.componentCharts i
    let := F.componentComplex i
    let := W.componentCharts i
    let := W.componentComplex i
    let : CompactSpace (F.flag i) := isCompact_iff_compactSpace.mp (F.smooth.level_isCompact i)
    let : CompactSpace (W.flag i) := isCompact_iff_compactSpace.mp (W.smooth.level_isCompact i)
    have hforward := contMDiff_flagComponentMap F W e hf i (mapsTo_flag_of_image e he i)
    have hbackward := contMDiff_flagComponentMap W F e.symm hg i (mapsTo_flag_symm_of_image e he i)
    exact isAnalyticModification_biholomorphic_transport (Homeomorph.refl (F.flag i))
      (flagComponentHomeomorph e he i) contMDiff_id contMDiff_id hforward hbackward
      isAnalyticModification_identity

/-- The ACTUAL full-flag biholomorphism has actual correction matrix1,
derived from genuine liftings in both directions and their actual composition. -/
theorem correctionMatrixReal_biholomorphic {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    correctionMatrixReal (isFlagLifting_of_biholomorphic e he hf hg) = 1 :=
  correctionMatrixReal_eq_one_of_inverse (isFlagLifting_of_biholomorphic e he hf hg)
    (isFlagLifting_of_biholomorphic e.symm (image_flag_symm_of_image e he) hg hf)
    (funext e.apply_symm_apply)

/-- Genuine body transport for arbitrary ORIGINAL theta-PSH potentials
under a produced whole-flag biholomorphism. The SAME actual pulled tensor and
potential are retained; no positivity, QEA/body presentation or matrix premise
is added. Dimension0 is handled by the separate actual ZeroSource dictionary. -/
theorem generalPartialBody_biholomorphic {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e.symm)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    PartialBody.generalPartialBody W (ClosedRealOneOneForm.pullback hf θ) (φ ∘ e) =
      PartialBody.generalPartialBody F θ φ := by
  have h := PartialBody.generalPartialBody_pullback hφ (isFlagLifting_of_biholomorphic e he hf hg)
  rw [correctionMatrixReal_biholomorphic e he hf hg] at h
  simp only [Matrix.vecMul_one] at h
  exact h.trans (Set.image_id _)

/-- Actual strong theta-PSH pullback through the produced ORIGINAL analytic
modification; no separate target-potential certificate is supplied. -/
theorem thetaPsh_biholomorphic_pullback {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hf θ).val (φ ∘ e) :=
  AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    (isFlagLifting_of_biholomorphic e he hf hg).1 θ hφ

/-- The SAME actual original source general bodies are transported in
EVERY dimension, including the genuine0-dimensional source construction. -/
theorem sourceGeneralBody_biholomorphic {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    (e : W.carrier ≃ₜ F.carrier) (he : ∀ i, e '' W.flag i = F.flag i)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    SourceTestCurveAllDimensions.generalBody W (ClosedRealOneOneForm.pullback hf θ)
      ⟨φ ∘ e, thetaPsh_biholomorphic_pullback e he hf hg hφ⟩ =
      SourceTestCurveAllDimensions.generalBody F θ ⟨φ, hφ⟩ := by
  cases n with
  | zero =>
    change ZeroSource.generalBody W (ClosedRealOneOneForm.pullback hf θ) (φ ∘ e)
      (thetaPsh_biholomorphic_pullback e he hf hg hφ) = ZeroSource.generalBody F θ φ hφ
    rw [ZeroSource.generalBody_eq_partial, ZeroSource.generalBody_eq_partial,
      ZeroSource.partialOkounkovBody_eq_univ W (thetaPsh_biholomorphic_pullback e he hf hg hφ),
      ZeroSource.partialOkounkovBody_eq_univ F hφ]
  | succ m => exact generalPartialBody_biholomorphic e he hf hg hφ

end SGPT.Okounkov.ToricTransport
