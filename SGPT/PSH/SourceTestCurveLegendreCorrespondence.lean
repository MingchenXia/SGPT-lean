import SGPT.PSH.SourceRayLegendreTestCurve

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Equality of the original cutoff and literal sub-cutoff potential
families determines the original test-curve object, without a quotient. -/
theorem SourceTestCurve.ext_of_max_potential (Γ Δ : SourceTestCurve θ)
    (hmax : Γ.max = Δ.max)
    (hpotential : ∀ (τ : ℝ) (hτ : τ < Γ.max) (hτ' : τ < Δ.max),
      Γ.potential ⟨τ, hτ⟩ = Δ.potential ⟨τ, hτ'⟩) : Γ = Δ := by
  rcases Γ with ⟨⟨a, p, hp, ha, hc, hf⟩, hm⟩
  rcases Δ with ⟨⟨b, q, hq, hb, hd, hg⟩, hn⟩
  dsimp at hmax hpotential
  subst b
  have hpq : p = q := by
    funext τ
    exact hpotential τ.1 τ.2 τ.2
  subst q
  rfl

variable [BorelSpace M] [ConnectedSpace M]
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

/-- Exact real cutoff readback of the genuine forward ray. -/
private theorem forwardRay_cutoff (omega : KahlerBackground n M) (Γ : SourceTestCurve θ)
    (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceRayLegendreCutoff omega
      (source_test_curve_legendre_geodesic_whole omega Γ hbased).1 = Γ.max := by
  change (⨆ x, sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨1, by norm_num⟩ x).toReal = Γ.max
  have hs : (⨆ x, sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ⟨1, by norm_num⟩ x) =
      (Γ.max : EReal) := by
    simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
      if_neg (one_ne_zero : (1 : ℝ) ≠ 0), one_mul] using
      Γ.toSourceTestCurvePredata.rawLegendre_globalSup (by norm_num : (0 : ℝ) < 1)
  rw [hs]
  exact EReal.toReal_coe _

/-- The literal inverse of the actual forward ray recovers every original
sub-cutoff function and the exact real cutoff, hence the original object. -/
theorem sourceTestCurveLegendre_left_inverse (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceRayLegendreTestCurve omega
      (source_test_curve_legendre_geodesic_whole omega Γ hbased).1 = Γ := by
  apply SourceTestCurve.ext_of_max_potential _ Γ (forwardRay_cutoff omega Γ hbased)
  intro τ hτ hτ'
  change sourcePositiveRayInverse (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata) τ =
    Γ.potential ⟨τ, hτ'⟩
  funext x
  rw [← sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hτ']
  rw [Γ.toSourceTestCurvePredata.at_eq_iInf_positive_rawLegendre τ x]
  unfold sourcePositiveRayInverse
  apply iInf_congr
  intro t
  have ht : 0 < t.1 := t.2
  simp only [sourceRayExtension_nonneg _ t.1 ht.le, sourceTestCurveLegendreRay,
    sourceTestCurveLegendreWithInitial, if_neg ht.ne']

private theorem originalRay_positive_inversion (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ)
    {t : ℝ} (ht : 0 < t) (x : M) :
    sourceRayExtension ℓ t x =
      ⨆ τ : ℝ, ((t * τ : ℝ) : EReal) + sourcePositiveRayInverse ℓ τ x := by
  have hf (s : ℝ) (hs : 0 < s) : sourceRayExtension ℓ s x < ⊤ := by
    rw [sourceRayExtension_nonneg ℓ s hs.le]
    exact (le_iSup (fun y ↦ ℓ ⟨s, hs.le⟩ y) x).trans_lt
      ((sourceRay_globalSup_finite omega h ⟨s, hs.le⟩).1.lt_top)
  have hi := SGPT.Convex.halfLineConjugate_inversion
    (h.1.isSubgeodesicRay.positiveEpigraph_convex x) hf ht
  rw [← hi]
  simp only [SGPT.Convex.conjugate, SGPT.Convex.scalarPairing, LinearMap.mul_apply',
    sourcePositiveRayInverse_conjugate, sub_eq_add_neg, neg_neg]
  apply iSup_congr
  intro τ
  rw [mul_comm]

/-- The literal inverse's original cutoff extension dominates the actual
cutoff inverse; this one-sided comparison suffices for exact ray recovery. -/
private theorem inverse_le_constructed_extension (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ)
    (τ : ℝ) (x : M) :
    sourcePositiveRayInverse ℓ τ x ≤
      sourceTestCurveAt (sourceRayLegendreTestCurve omega h).toSourceTestCurvePredata τ x := by
  let Γ := sourceRayLegendreTestCurve omega h
  let C := sourceRayLegendreCutoff omega h
  change sourcePositiveRayInverse ℓ τ x ≤ sourceTestCurveAt Γ.toSourceTestCurvePredata τ x
  by_cases hlt : τ < C
  · rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hlt]
    exact le_rfl
  by_cases he : τ = C
  · subst τ
    rw [show C = Γ.max from rfl, sourceTestCurveAt_eq_max]
    apply le_iInf
    intro σ
    exact sourceRayLegendre_inverse_antitone ℓ x σ.2.le
  · have hgt : C < τ := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
    rw [sourceRayLegendre_inverse_bot_above omega h hgt]
    exact bot_le

/-- Exact original ray recovery at all nonnegative times, retaining its
assigned origin. No equality of cutoff extensions is assumed. -/
theorem sourceRayLegendre_right_inverse (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    sourceTestCurveLegendreRay (sourceRayLegendreTestCurve omega h).toSourceTestCurvePredata = ℓ := by
  let Γ := sourceRayLegendreTestCurve omega h
  funext t x
  change sourceTestCurveLegendreWithInitial Γ.toSourceTestCurvePredata
    (sourceTestCurveLimit Γ.toSourceTestCurvePredata) t.1 x = ℓ t x
  by_cases ht : t.1 = 0
  · rw [sourceTestCurveLegendreWithInitial, if_pos ht,
      (source_ray_legendre_test_curve_whole omega h).1]
    have hz : t = ⟨0, by simp⟩ := Subtype.ext ht
    rw [hz, h.2]
  · rw [sourceTestCurveLegendreWithInitial, if_neg ht]
    have hpos : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht)
    have hi := originalRay_positive_inversion omega h hpos x
    rw [← sourceRayExtension_nonneg ℓ t.1 t.2]
    apply le_antisymm
    · rw [Γ.toSourceTestCurvePredata.rawLegendre_eq_iSup_open, hi]
      apply iSup_le
      intro τ
      exact le_iSup (fun σ : ℝ ↦ ((t.1 * σ : ℝ) : EReal) +
        sourcePositiveRayInverse ℓ σ x) τ.1
    · rw [hi]
      apply iSup_le
      intro τ
      exact (add_le_add le_rfl (inverse_le_constructed_extension omega h τ x)).trans
        (le_iSup (fun σ : ℝ ↦ ((t.1 * σ : ℝ) : EReal) +
          sourceTestCurveAt Γ.toSourceTestCurvePredata σ x) τ)

/-- The original based Ross--Witt Nyström correspondence on actual objects.
This is the base bijection only; the energy clauses are separate. -/
def sourceTestCurveLegendreEquiv (omega : KahlerBackground n M)
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) :
    {Γ : SourceTestCurve θ // Γ ∈ SourceTestCurvesBased θ φ hφ} ≃
      {ℓ : SourceRayFamily M // ℓ ∈ sourceGeodesicRays omega θ φ hφ} where
  toFun Γ := ⟨sourceTestCurveLegendreRay Γ.1.toSourceTestCurvePredata,
    (source_test_curve_legendre_geodesic_whole omega Γ.1 Γ.2).1⟩
  invFun ℓ := ⟨sourceRayLegendreTestCurve omega ℓ.2,
    (source_ray_legendre_test_curve_whole omega ℓ.2).1⟩
  left_inv Γ := Subtype.ext (sourceTestCurveLegendre_left_inverse omega Γ.1 Γ.2)
  right_inv ℓ := Subtype.ext (sourceRayLegendre_right_inverse omega ℓ.2)

end SGPT.PSH.VariableComplexAtlas
