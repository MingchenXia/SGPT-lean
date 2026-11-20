import SGPT.PSH.SourcePerronStability
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicAffineCovariance

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Affine covariance of the ENTIRE original all-subgeodesic Perron family,
with every endpoint choice and literal pole retained. -/
theorem sourcePerron_affineCovariance (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u₀ u₁ : M → EReal) (A B t : ℝ) :
    sourcePerronGeodesic omega θ (fun x ↦ u₀ x + (B : EReal))
      (fun x ↦ u₁ x + ((A + B : ℝ) : EReal)) t =
        fun x ↦ sourcePerronGeodesic omega θ u₀ u₁ t x + ((A * t + B : ℝ) : EReal) := by
  simp only [sourcePerronGeodesic_eq_native]
  exact finiteGeodesic_affineCovariance _ u₀ u₁ A B t

/-- The general clause of the entire original affine example, for EVERY
original normalized geodesic and its correctly translated own endpoints. -/
theorem SourceIsGeodesicFrom.affineTranslated {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceIsGeodesicFrom omega θ curve u₀ u₁) (A B : ℝ) :
    SourceIsGeodesicFrom omega θ (affineTranslatedCurve curve A B)
      (fun x ↦ u₀ x + (B : EReal)) (fun x ↦ u₁ x + ((A + B : ℝ) : EReal)) := by
  have h₀ := (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (((isThetaPSH_iff_nativeThetaPotential θ u₀).mp h.1).add_const B)
  have h₁ := (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (((isThetaPSH_iff_nativeThetaPotential θ u₁).mp h.2.1).add_const (A + B))
  have heq : ∀ t ∈ Ioo (0 : ℝ) 1, affineTranslatedCurve curve A B t =
      sourcePerronGeodesic omega θ (fun x ↦ u₀ x + (B : EReal))
        (fun x ↦ u₁ x + ((A + B : ℝ) : EReal)) t := by
    intro t ht
    rw [sourcePerron_affineCovariance]
    funext x
    simp only [affineTranslatedCurve_apply, h.2.2.2 t ht]
  exact ⟨h₀, h₁, fun t ht ↦ (heq t ht) ▸
    sourcePerronGeodesic_isThetaPSHOrBot omega h₀ h₁ ht, heq⟩

/-- The original constant geodesic at an arbitrary genuine source potential. -/
theorem sourceIsGeodesic_const (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    SourceIsGeodesicFrom omega θ (fun _ : ℝ ↦ u) u u :=
  ⟨hu, hu, fun _ _ ↦ Or.inl hu,
    fun _ ht ↦ (sourcePerronGeodesic_const omega hu ht).symm⟩

/-- The displayed original affine geodesic for any theta-PSH base and real slope. -/
theorem sourceIsGeodesic_affine (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (C : ℝ) :
    SourceIsGeodesicFrom omega θ (fun t x ↦ u x + ((t * C : ℝ) : EReal))
      u (fun x ↦ u x + (C : EReal)) := by
  have h := (sourceIsGeodesic_const omega hu).affineTranslated C 0
  change SourceIsGeodesicFrom omega θ (fun t x ↦ u x + ((C * t + 0 : ℝ) : EReal))
    (fun x ↦ u x + ((0 : ℝ) : EReal)) (fun x ↦ u x + ((C + 0 : ℝ) : EReal)) at h
  simpa only [add_zero, EReal.coe_zero, mul_comm] using h

/-- The actual closed constant family, including both original endpoints. -/
theorem sourceGeodesicClosedInterval_const (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    SourceGeodesicClosedInterval omega θ 0 1 (fun _ : ℝ ↦ u) :=
  ⟨zero_le_one, fun _ _ ↦ hu, sourceIsGeodesic_const omega hu⟩

/-- The ENTIRE original general example on [0,1], retaining genuine closed
slices and both endpoint values, for every original geodesic. -/
theorem SourceGeodesicClosedInterval.affineTranslated_unit
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ 0 1 curve) (A B : ℝ) :
    SourceGeodesicClosedInterval omega θ 0 1 (affineTranslatedCurve curve A B) := by
  refine ⟨zero_le_one, ?_, ?_⟩
  · intro t ht
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (((isThetaPSH_iff_nativeThetaPotential θ (curve t)).mp (h.2.1 t ht)).add_const (A * t + B))
  · have hn : SourceIsGeodesicFrom omega θ curve (curve 0) (curve 1) := by
      simpa only [mul_one, mul_zero, add_zero] using h.2.2
    have h₀ : affineTranslatedCurve curve A B 0 = fun x ↦ curve 0 x + (B : EReal) := by
      funext x
      simp only [affineTranslatedCurve_apply, mul_zero, zero_add]
    have h₁ : affineTranslatedCurve curve A B 1 =
        fun x ↦ curve 1 x + ((A + B : ℝ) : EReal) := by
      funext x
      simp only [affineTranslatedCurve_apply, mul_one]
    rw [h₀, h₁]
    simpa only [mul_one, mul_zero, add_zero] using hn.affineTranslated A B

/-- The displayed original example on the entire CLOSED unit interval. -/
theorem sourceGeodesicClosedInterval_affine (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (C : ℝ) :
    SourceGeodesicClosedInterval omega θ 0 1
      (fun t x ↦ u x + ((t * C : ℝ) : EReal)) := by
  have h := (sourceGeodesicClosedInterval_const omega hu).affineTranslated_unit C 0
  have heq : affineTranslatedCurve (fun _ : ℝ ↦ u) C 0 =
      (fun t x ↦ u x + ((t * C : ℝ) : EReal)) := by
    funext t x
    simp only [affineTranslatedCurve_apply, add_zero, mul_comm]
  rw [heq] at h
  exact h

end SGPT.PSH.VariableComplexAtlas
