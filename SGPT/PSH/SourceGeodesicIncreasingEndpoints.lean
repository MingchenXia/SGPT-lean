import SGPT.PSH.SourceRelativeGeodesics
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicIncreasingEndpoints

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {ui₀ ui₁ : I → M → EReal}

/-- The actual original ALL-competitor Perron envelopes commute with
increasing original E1 endpoint nets. BOTH original limit E1 classes are
manufactured from the actual source bounds, not supplied as certificates. -/
theorem sourcePerron_uscSup_of_increasing_endpoints (omega : KahlerBackground n M)
    (h₀ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₀ i) hφ)
    (h₁ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₁ i) hφ)
    (hB₀ : ∃ C : ℝ, ∀ i x, ui₀ i x ≤ (C : EReal))
    (hB₁ : ∃ C : ℝ, ∀ i x, ui₁ i x ≤ (C : EReal))
    (hm₀ : ∀ x, Monotone fun i ↦ ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i ↦ ui₁ i x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SGPT.PSH.uscSup (fun i ↦ sourcePerronGeodesic omega θ (ui₀ i) (ui₁ i) t) =
      sourcePerronGeodesic omega θ (SGPT.PSH.uscSup ui₀) (SGPT.PSH.uscSup ui₁) t := by
  obtain ⟨C₀, hC₀⟩ := hB₀
  obtain ⟨C₁, hC₁⟩ := hB₁
  have hU₀ := sourceRelativeFiniteEnergy_uscSup omega h₀ hC₀
  have hU₁ := sourceRelativeFiniteEnergy_uscSup omega h₁ hC₁
  have hn := SingularModelGeodesicIncreasingEndpoints.uscRegularization_iSup_finiteGeodesic_eq
    omega (fun i ↦ (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (h₀ i))
    (fun i ↦ (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (h₁ i))
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp hU₀)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp hU₁)
    (sourceUscSup_eq_native ui₀).symm (sourceUscSup_eq_native ui₁).symm hm₀ hm₁ ht
  simpa only [sourceUscSup_eq_native, sourcePerronGeodesic_eq_native] using hn

/-- The stronger genuine assigned-CLOSED version retains both actual
endpoint suprema, in addition to every original interior Perron slice. -/
theorem sourcePerronClosedSlice_uscSup_of_increasing_endpoints (omega : KahlerBackground n M)
    (h₀ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₀ i) hφ)
    (h₁ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₁ i) hφ)
    (hB₀ : ∃ C : ℝ, ∀ i x, ui₀ i x ≤ (C : EReal))
    (hB₁ : ∃ C : ℝ, ∀ i x, ui₁ i x ≤ (C : EReal))
    (hm₀ : ∀ x, Monotone fun i ↦ ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i ↦ ui₁ i x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    SGPT.PSH.uscSup (fun i ↦ sourcePerronClosedSlice omega θ (ui₀ i) (ui₁ i) t) =
      sourcePerronClosedSlice omega θ (SGPT.PSH.uscSup ui₀) (SGPT.PSH.uscSup ui₁) t := by
  obtain ⟨C₀, hC₀⟩ := hB₀
  obtain ⟨C₁, hC₁⟩ := hB₁
  have hU₀ := sourceRelativeFiniteEnergy_uscSup omega h₀ hC₀
  have hU₁ := sourceRelativeFiniteEnergy_uscSup omega h₁ hC₁
  have hn := SingularModelGeodesicIncreasingEndpoints.uscRegularization_iSup_closedSubgeodesicSlice_eq
    omega (fun i ↦ (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (h₀ i))
    (fun i ↦ (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (h₁ i))
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp hU₀)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp hU₁)
    (sourceUscSup_eq_native ui₀).symm (sourceUscSup_eq_native ui₁).symm hm₀ hm₁ ht
  simpa only [sourceUscSup_eq_native, sourcePerronClosedSlice_eq_native] using hn

/-- EVERY prescribed original geodesic family has the same actual slice
supremum, using only its original interior equality. Arbitrary directed
nets are retained, without countable cofinality or an off-time premise. -/
theorem sourceGeodesic_uscSup_eq_of_increasing_endpoints (omega : KahlerBackground n M)
    {curve : I → ℝ → M → EReal}
    (hg : ∀ i, SourceIsGeodesicFrom omega θ (curve i) (ui₀ i) (ui₁ i))
    (h₀ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₀ i) hφ)
    (h₁ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₁ i) hφ)
    (hB₀ : ∃ C : ℝ, ∀ i x, ui₀ i x ≤ (C : EReal))
    (hB₁ : ∃ C : ℝ, ∀ i x, ui₁ i x ≤ (C : EReal))
    (hm₀ : ∀ x, Monotone fun i ↦ ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i ↦ ui₁ i x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SGPT.PSH.uscSup (fun i ↦ curve i t) =
      sourcePerronGeodesic omega θ (SGPT.PSH.uscSup ui₀) (SGPT.PSH.uscSup ui₁) t := by
  have heq : (fun i ↦ curve i t) =
      (fun i ↦ sourcePerronGeodesic omega θ (ui₀ i) (ui₁ i) t) :=
    funext fun i ↦ (hg i).2.2.2 t ht
  rw [heq]
  exact sourcePerron_uscSup_of_increasing_endpoints omega h₀ h₁ hB₀ hB₁ hm₀ hm₁ ht

/-- WHOLE original prop:supsgeod for ANY prescribed original geodesics:
the genuine spatial usc supremum is the original geodesic from the two
actual endpoint suprema, on the WHOLE original preceq E1 source domain. -/
theorem sourceGeodesic_uscSup_isGeodesicFrom (omega : KahlerBackground n M)
    {curve : I → ℝ → M → EReal}
    (hg : ∀ i, SourceIsGeodesicFrom omega θ (curve i) (ui₀ i) (ui₁ i))
    (h₀ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₀ i) hφ)
    (h₁ : ∀ i, SourceRelativeFiniteEnergy θ φ (ui₁ i) hφ)
    (hB₀ : ∃ C : ℝ, ∀ i x, ui₀ i x ≤ (C : EReal))
    (hB₁ : ∃ C : ℝ, ∀ i x, ui₁ i x ≤ (C : EReal))
    (hm₀ : ∀ x, Monotone fun i ↦ ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i ↦ ui₁ i x) :
    SourceIsGeodesicFrom omega θ (fun t ↦ SGPT.PSH.uscSup (fun i ↦ curve i t))
      (SGPT.PSH.uscSup ui₀) (SGPT.PSH.uscSup ui₁) := by
  obtain ⟨C₀, hC₀⟩ := hB₀
  obtain ⟨C₁, hC₁⟩ := hB₁
  have hU₀ := sourceRelativeFiniteEnergy_uscSup omega h₀ hC₀
  have hU₁ := sourceRelativeFiniteEnergy_uscSup omega h₁ hC₁
  have hcanonical := sourcePerronGeodesic_isGeodesicFrom omega hU₀.1.choose hU₁.1.choose
  refine ⟨hcanonical.1, hcanonical.2.1, ?_, ?_⟩
  · intro t ht
    change IsThetaPSHOrBot θ (SGPT.PSH.uscSup (fun i ↦ curve i t))
    rw [sourceGeodesic_uscSup_eq_of_increasing_endpoints omega hg h₀ h₁
      ⟨C₀, hC₀⟩ ⟨C₁, hC₁⟩ hm₀ hm₁ ht]
    exact hcanonical.2.2.1 t ht
  · intro t ht
    exact sourceGeodesic_uscSup_eq_of_increasing_endpoints omega hg h₀ h₁
      ⟨C₀, hC₀⟩ ⟨C₁, hC₁⟩ hm₀ hm₁ ht

end SGPT.PSH.VariableComplexAtlas
