import SGPT.PSH.SourceRelativeGeodesics
import SGPT.Foundations.Analysis.Pending.FiniteLowerGapGeodesicInfimum

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- The literal printed infimum on EXACTLY the original model nonpole set.
Differences are EReal differences; no value is assigned to a common pole. -/
def sourceRelativeDifferenceInf {X : Type*} (φ u v : X → EReal) : EReal :=
  ⨅ x : {x // φ x ≠ ⊥}, u x.val - v x.val

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual same-type dictionary identifies the whole model nonpole set
with the subtracted potential's nonpole set, preserving every difference. -/
theorem sourceRelativeDifferenceInf_eq_native
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ v : M → EReal}
    (hv : SourceRelativeEInfinity θ φ v) (u : M → EReal) :
    sourceRelativeDifferenceInf φ u v = FiniteLowerGapGeodesicInfimum.differenceInf u v := by
  exact (FiniteLowerGapGeodesicInfimum.differenceInf_eq_iInf_of_sameSingularityType
    ((sourceRelativeEInfinity_iff_native θ φ v).mp hv).2).symm

/-- Actual original same-type comparisons and a genuine finite point
produce BOTH finite gap endpoints before any real readback. -/
theorem sourceRelativeDifferenceInf_finite [Nonempty M]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u₀ u₁ : M → EReal}
    (h₀ : SourceRelativeEInfinity θ φ u₀) (h₁ : SourceRelativeEInfinity θ φ u₁) :
    sourceRelativeDifferenceInf φ u₁ u₀ ≠ ⊤ ∧ sourceRelativeDifferenceInf φ u₁ u₀ ≠ ⊥ := by
  rw [sourceRelativeDifferenceInf_eq_native h₀]
  have hn₀ := (sourceRelativeEInfinity_iff_native θ φ u₀).mp h₀
  have hn₁ := (sourceRelativeEInfinity_iff_native θ φ u₁).mp h₁
  exact FiniteLowerGapGeodesicInfimum.differenceInf_ne_top_ne_bot hn₀.1 hn₁.1
    (hn₀.2.1.trans hn₁.2.2)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The actual original model-domain infimum formula, as a literal EReal
product, for every assigned closed Perron time including zero and one.
The original model reference may be unbounded. -/
theorem sourcePerron_relativeInfimum_closed (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u₀ u₁ : M → EReal}
    (hφ : SourceModelPotential θ φ)
    (h₀ : SourceRelativeEInfinity θ φ u₀) (h₁ : SourceRelativeEInfinity θ φ u₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceRelativeDifferenceInf φ (sourcePerronClosedSlice omega θ u₀ u₁ t) u₀ =
      (t : EReal) * sourceRelativeDifferenceInf φ u₁ u₀ := by
  have hfinite := sourceRelativeDifferenceInf_finite h₀ h₁
  have hn := FiniteLowerGapGeodesicInfimum.relative_iInf_closedFiniteGeodesic hφ.toNative
    ((sourceRelativeEInfinity_iff_native θ φ u₀).mp h₀)
    ((sourceRelativeEInfinity_iff_native θ φ u₁).mp h₁) ht
  have hreal : sourceRelativeDifferenceInf φ (sourcePerronClosedSlice omega θ u₀ u₁ t) u₀ =
      ((t * (sourceRelativeDifferenceInf φ u₁ u₀).toReal : ℝ) : EReal) := by
    simpa only [sourceRelativeDifferenceInf, sourcePerronClosedSlice_eq_native] using hn
  calc
    sourceRelativeDifferenceInf φ (sourcePerronClosedSlice omega θ u₀ u₁ t) u₀ = _ := hreal
    _ = (t : EReal) * sourceRelativeDifferenceInf φ u₁ u₀ := by
      rw [EReal.coe_mul, EReal.coe_toReal hfinite.1 hfinite.2]

/-- The WHOLE original prop:geodinfsublinear for EVERY original normalized
geodesic with its prescribed endpoint values, precisely on the printed
(0,1] time and model nonpole domains. No stronger slice-class is an input. -/
theorem source_relative_geodesic_infimum (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (hgeo : SourceIsGeodesicFrom omega θ curve u₀ u₁)
    (h₀ : SourceRelativeEInfinity θ φ u₀) (h₁ : SourceRelativeEInfinity θ φ u₁)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    sourceRelativeDifferenceInf φ (closedSubgeodesicSlice curve u₀ u₁ t) u₀ =
      (t : EReal) * sourceRelativeDifferenceInf φ u₁ u₀ := by
  have heq : closedSubgeodesicSlice curve u₀ u₁ t = sourcePerronClosedSlice omega θ u₀ u₁ t := by
    by_cases ht1 : t = 1
    · simp only [ht1, sourcePerronClosedSlice, closedSubgeodesicSlice_one]
    have hti : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
    simpa only [sourcePerronClosedSlice, closedSubgeodesicSlice_eq_curve hti] using hgeo.2.2.2 t hti
  rw [heq]
  exact sourcePerron_relativeInfimum_closed omega hφ h₀ h₁ ⟨ht.1.le, ht.2⟩

end SGPT.PSH.VariableComplexAtlas
