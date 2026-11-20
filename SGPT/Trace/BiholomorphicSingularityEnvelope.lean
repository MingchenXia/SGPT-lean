import SGPT.PSH.BiholomorphicGeometricQPullback
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Trace
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine biholomorphic maps and preservation of the ACTUAL background
form internally produce strong same-background PSH pullback, including
nondegeneracy and all original poles. -/
theorem isThetaPSH_comp_biholomorphic_preserving_form
    (θ : ClosedRealOneOneForm n M) (e : M ≃ₜ M)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (hθ : (ClosedRealOneOneForm.pullback he θ).val.GeometricallyEq θ.val)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas θ) u) :
    (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas θ) (u ∘ e) := by
  have hun : IsThetaPshPotential θ.val u :=
    (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas θ) u).mp hu
  have hp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    (nativeAnalyticModification_of_biholomorphic e he hei) θ hun
  exact (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas θ) (u ∘ e)).mpr
    ((hθ.thetaPshPotential_iff (u ∘ e)).mp hp)

/-- The ACTUAL source ordinary P-envelope commutes pointwise with a
background-preserving biholomorphism. All competitors, empty families,
original neighbourhood regularization, and original poles are retained. -/
theorem sourceSingularityEnvelope_comp_biholomorphic
    (θ : ClosedRealOneOneForm n M) (e : M ≃ₜ M)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (hθ : (ClosedRealOneOneForm.pullback he θ).val.GeometricallyEq θ.val)
    (hθi : (ClosedRealOneOneForm.pullback hei θ).val.GeometricallyEq θ.val)
    (u : M → EReal) (x : M) :
    sourceSingularityEnvelope (nativeClosedFormToAtlas θ) u (e x) =
      sourceSingularityEnvelope (nativeClosedFormToAtlas θ) (u ∘ e) x := by
  let A := nativeClosedFormToAtlas θ
  let F : M → EReal := fun y => ⨆ v : sourceSingularityCompetitors A u, v.val y
  let G : M → EReal := fun y => ⨆ v : sourceSingularityCompetitors A (u ∘ e), v.val y
  have hsup : F ∘ e = G := by
    funext y
    apply le_antisymm
    · apply iSup_le
      intro v
      have hvP : (ofFixedModel n M).IsThetaPSH A (v.val ∘ e) :=
        isThetaPSH_comp_biholomorphic_preserving_form θ e he hei hθ v.property.1
      have hv0 : v.val ∘ e ≤ 0 := fun z => v.property.2.1 (e z)
      obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp v.property.2.2
      have hvu : SingularityLE (v.val ∘ e) (u ∘ e) :=
        (singularityLE_iff_exists_real _ _).mpr ⟨C, fun z => hC (e z)⟩
      exact le_iSup_of_le (⟨v.val ∘ e, hvP, hv0, hvu⟩ : sourceSingularityCompetitors A (u ∘ e)) le_rfl
    · apply iSup_le
      intro v
      have hvP : (ofFixedModel n M).IsThetaPSH A (v.val ∘ e.symm) :=
        isThetaPSH_comp_biholomorphic_preserving_form θ e.symm hei he hθi v.property.1
      have hv0 : v.val ∘ e.symm ≤ 0 := fun z => v.property.2.1 (e.symm z)
      obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp v.property.2.2
      have hvu : SingularityLE (v.val ∘ e.symm) u :=
        (singularityLE_iff_exists_real _ _).mpr ⟨C, fun z => by
          simpa only [Function.comp_apply, e.apply_symm_apply] using hC (e.symm z)⟩
      have hle := le_iSup (fun w : sourceSingularityCompetitors A u => w.val (e y))
        ⟨v.val ∘ e.symm, hvP, hv0, hvu⟩
      simpa only [Function.comp_apply, e.symm_apply_apply] using hle
  change uscRegularization F (e x) = uscRegularization G x
  rw [← uscRegularization_comp_homeomorph_apply F e x, hsup]

/-- Native readback of the same pointwise original-envelope equivariance. -/
theorem singularityEnvelope_comp_biholomorphic
    (θ : ClosedRealOneOneForm n M) (e : M ≃ₜ M)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (hθ : (ClosedRealOneOneForm.pullback he θ).val.GeometricallyEq θ.val)
    (hθi : (ClosedRealOneOneForm.pullback hei θ).val.GeometricallyEq θ.val)
    (u : M → EReal) (x : M) :
    singularityEnvelope θ.val u (e x) = singularityEnvelope θ.val (u ∘ e) x := by
  simpa only [sourceSingularityEnvelope_eq_native, sourceNativeAtlasForm_roundTrip] using
    sourceSingularityEnvelope_comp_biholomorphic θ e he hei hθ hθi u x

end SGPT.Trace
