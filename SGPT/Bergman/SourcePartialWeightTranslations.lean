import SGPT.Bergman.SourcePartialIEnvelopeComparison
import SGPT.Bergman.SourcePartialEquilibriumEnergy

/-! Finite obstacle translations and uniform control of continuous affine weights. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PartialEnergyDifferentiability

open Set Filter MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeIComparison
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- BOTH actual candidate maps prove exact ordinary obstacle translation,
including arbitrary extended-real weights, empty families and all poles. -/
theorem partialEnvelope_add_obstacle_const
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (w : K → EReal) (c : ℝ) :
    partialEnvelope θ φ K (fun x => w x + (c : EReal)) =
      fun x => partialEnvelope θ φ K w x + (c : EReal) := by
  let A := fun x => ⨆ η : partialCompetitors θ φ K w, η.val x
  have heq : (fun x => ⨆ η : partialCompetitors θ φ K (fun y => w y + (c : EReal)), η.val x) =
      fun x => A x + (c : EReal) := by
    funext x
    apply le_antisymm
    · apply iSup_le
      intro η
      let χ : M → EReal := fun y => η.val y + ((-c : ℝ) : EReal)
      have hχ := sourceThetaPSH_add_const η.property.1 (-c)
      have hχK : partialObstacle (n := n) K w χ := by
        obtain ⟨S, hS, hη⟩ := (partialObstacle_iff_exists_pluripolar _ _ _).mp η.property.2.1
        apply (partialObstacle_iff_exists_pluripolar _ _ _).mpr
        refine ⟨S, hS, fun y hy => ?_⟩
        have h := add_le_add (hη y hy) (le_refl ((-c : ℝ) : EReal))
        simpa only [χ, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] using h
      have hord : SGPT.PSH.SingularityLE χ φ :=
        (show SGPT.PSH.SingularityLE χ η.val from ⟨-c, fun _ _ => le_rfl⟩).trans η.property.2.2
      have hlo : χ x ≤ A x := le_iSup (fun ζ : partialCompetitors θ φ K w => ζ.val x) ⟨χ, hχ, hχK, hord⟩
      have h := add_le_add hlo (le_refl (c : EReal))
      simpa only [χ, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] using h
    · rw [show A x + (c : EReal) = ⨆ η : partialCompetitors θ φ K w, η.val x + (c : EReal) from
        (iSup_add_coe (fun η : partialCompetitors θ φ K w => η.val x) c).symm]
      apply iSup_le
      intro η
      let χ : M → EReal := fun y => η.val y + (c : EReal)
      have hχ := sourceThetaPSH_add_const η.property.1 c
      have hχK : partialObstacle (n := n) K (fun y => w y + (c : EReal)) χ := by
        obtain ⟨S, hS, hη⟩ := (partialObstacle_iff_exists_pluripolar _ _ _).mp η.property.2.1
        exact (partialObstacle_iff_exists_pluripolar _ _ _).mpr
          ⟨S, hS, fun y hy => add_le_add (hη y hy) le_rfl⟩
      have hord : SGPT.PSH.SingularityLE χ φ :=
        (show SGPT.PSH.SingularityLE χ η.val from ⟨c, fun _ _ => le_rfl⟩).trans η.property.2.2
      exact le_iSup (fun ζ : partialCompetitors θ φ K (fun y => w y + (c : EReal)) => ζ.val x)
        ⟨χ, hχ, hχK, hord⟩
  change uscRegularization _ = _
  rw [heq, uscRegularization_add_coe_const]
  rfl

variable [CompactSpace M] [Nonempty M]

/-- Exact ideal obstacle translation is DERIVED from the entire
I/P-at-PI family identity, with no desired output fixedness assumption. -/
theorem partialIEnvelope_add_obstacle_const
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (K : Set M) (w : K → EReal) (c : ℝ) :
    partialIEnvelope θ φ K (fun x => w x + (c : EReal)) =
      fun x => partialIEnvelope θ φ K w x + (c : EReal) := by
  rw [partialIEnvelope_eq_partialEnvelope_iEnvelope hφ,
    partialEnvelope_add_obstacle_const, partialIEnvelope_eq_partialEnvelope_iEnvelope hφ]

/-- The actual original affine continuous weight, retaining the SAME subtype. -/
def affineWeight {K : Set M} (v f : C(K, ℝ)) (t : ℝ) : C(K, ℝ) := v + t • f

/-- Every positive or negative real step is controlled by ONE actual finite
bound manufactured from the original continuous subtype direction. -/
theorem partialI_affineWeight_translate_control
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
    (v f : C(K, ℝ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s t x,
      partialIEnvelope θ φ K (fun y => (affineWeight v f s y : EReal)) x +
          ((-|t - s| * R : ℝ) : EReal) ≤
        partialIEnvelope θ φ K (fun y => (affineWeight v f t y : EReal)) x ∧
      partialIEnvelope θ φ K (fun y => (affineWeight v f t y : EReal)) x ≤
        partialIEnvelope θ φ K (fun y => (affineWeight v f s y : EReal)) x +
          ((|t - s| * R : ℝ) : EReal) := by
  let W : SGPT.Bergman.WeightedSubset.WeightedSubset n M := ⟨K, hKc, hK, f⟩
  obtain ⟨R, hR0, hR⟩ := W.exists_real_abs_bound
  refine ⟨R, hR0, fun s t x => ?_⟩
  have hgap (y : K) : |affineWeight v f t y - affineWeight v f s y| ≤ |t - s| * R := by
    have heq : affineWeight v f t y - affineWeight v f s y = (t - s) * f y := by
      simp only [affineWeight, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [heq, abs_mul]
    exact mul_le_mul_of_nonneg_left (hR y) (abs_nonneg _)
  constructor
  · have hbound : (fun y => (affineWeight v f s y : EReal) + ((-(|t - s| * R) : ℝ) : EReal)) ≤
        fun y => (affineWeight v f t y : EReal) := by
      intro y
      change (affineWeight v f s y : EReal) + ((-(|t - s| * R) : ℝ) : EReal) ≤ (affineWeight v f t y : EReal)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      have h := (abs_le.mp (hgap y)).1
      linarith
    have h := partialIEnvelope_mono_obstacle θ φ K hbound x
    rw [partialIEnvelope_add_obstacle_const hφ] at h
    simpa only [neg_mul] using h
  · have hbound : (fun y => (affineWeight v f t y : EReal)) ≤
        fun y => (affineWeight v f s y : EReal) + ((|t - s| * R : ℝ) : EReal) := by
      intro y
      change (affineWeight v f t y : EReal) ≤ (affineWeight v f s y : EReal) + ((|t - s| * R : ℝ) : EReal)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      have h := (abs_le.mp (hgap y)).2
      linarith
    have h := partialIEnvelope_mono_obstacle θ φ K hbound x
    rwa [partialIEnvelope_add_obstacle_const hφ] at h

end SGPT.Bergman.PartialEnergyDifferentiability
