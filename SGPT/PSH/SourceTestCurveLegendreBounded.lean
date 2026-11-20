import SGPT.PSH.SourceTestCurveLegendreCorrespondence
import SGPT.PSH.SourceRayLegendreTestCurve
import SGPT.PSH.SourceTestCurveEnergy

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

/-- The SAME original assigned-zero Legendre ray of an actual bounded
based test curve has the SAME relative singularity type at EVERY t≥0.
The reference positive model need not be bounded. -/
theorem source_test_curve_legendre_bounded_forward (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) :
    sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ∈ sourceBoundedRays omega θ φ hφ := by
  have hR := (source_test_curve_legendre_geodesic_whole omega Γ hΓ.1).1
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  obtain ⟨σ, hσ⟩ := hΓ.2.exists
  refine ⟨⟨hR.1, ?_⟩, hR.2⟩
  intro t
  refine ⟨(hR.1.1 t).choose, ?_⟩
  by_cases ht : t.1 = 0
  · have ht0 : t = ⟨0, by simp⟩ := Subtype.ext ht
    rw [ht0, hR.2]
    exact SGPT.PSH.singularityEquiv_refl φ
  · have htpos : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht)
    have hupper := Γ.toSourceTestCurvePredata.rawLegendre_le_limit_add htpos.le
    have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ.1
    rw [hbase] at hupper
    have hlower (x : M) : φ x + ((t.1 * σ.1 : ℝ) : EReal) ≤
        sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t.1 x := by
      rw [Γ.toSourceTestCurvePredata.rawLegendre_eq_iSup_open t.1 x, ← hσ, add_comm]
      exact le_iSup (fun τ : Iio Γ.max ↦ ((t.1 * τ.1 : ℝ) : EReal) + Γ.potential τ x) σ
    change SGPT.PSH.SingularityEquiv
      (sourceTestCurveLegendreWithInitial Γ.toSourceTestCurvePredata
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata) t.1) φ
    rw [sourceTestCurveLegendreWithInitial, if_neg ht]
    refine ⟨⟨t.1 * Γ.max, fun x _ ↦ hupper x⟩, ⟨-(t.1 * σ.1), fun x _ ↦ ?_⟩⟩
    simpa only [sub_eq_add_neg, EReal.coe_neg] using
      (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).mpr (hlower x)

/-- An ACTUAL original bounded ray produces a uniform finite lower slope
from its time-one same-type comparison. All nonnegative times, model poles,
and unbounded positive models are included; no lower-bound certificate. -/
theorem source_bounded_ray_uniform_lower_bound (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceBoundedRays omega θ φ hφ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : Ici (0 : ℝ),
      (fun x ↦ φ x + ((-(K * t.1) : ℝ) : EReal)) ≤ ℓ t := by
  have hR : ℓ ∈ sourceGeodesicRays omega θ φ hφ := ⟨h.1.1, h.2⟩
  obtain ⟨A, hA⟩ := (h.1.2 ⟨1, by norm_num⟩).2.2
  let K : ℝ := max A 0
  have hAK : A ≤ K := le_max_left _ _
  have hK : 0 ≤ K := le_max_right _ _
  have h1 (x : M) : φ x + ((-K : ℝ) : EReal) ≤ ℓ ⟨1, by norm_num⟩ x := by
    apply (EReal.addLECancellable_coe K).add_le_add_iff_right.mp
    calc
      (φ x + ((-K : ℝ) : EReal)) + (K : EReal) = φ x := by
        rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
      _ ≤ ℓ ⟨1, by norm_num⟩ x + (A : EReal) := hA x (mem_univ _)
      _ ≤ ℓ ⟨1, by norm_num⟩ x + (K : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe hAK)
  refine ⟨K, hK, ?_⟩
  intro t x
  by_cases ht0 : t.1 = 0
  · have heq : t = ⟨0, by simp⟩ := Subtype.ext ht0
    rw [heq, h.2]
    simp
  have htpos : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht0)
  by_cases ht1 : t.1 = 1
  · have heq : t = ⟨1, by norm_num⟩ := Subtype.ext ht1
    simpa only [heq, mul_one] using h1 x
  by_cases hsmall : t.1 < 1
  · have hq := sourceSubgeodesic_affine omega hφ.thetaPSH (-K)
    have hmem : (fun s y ↦ φ y + ((s * (-K) : ℝ) : EReal)) ∈
        sourcePerronCompetitors omega θ φ (ℓ ⟨1, by norm_num⟩) :=
      ⟨φ, fun y ↦ φ y + ((-K : ℝ) : EReal), hφ.thetaPSH, hq.2.1,
        le_rfl, h1, hq⟩
    have hle := sourcePerron_competitor_le hmem t.1 x
    have heq := (hR.1.2 0 1 le_rfl (by norm_num)).2.2.2.2.2 t.1 ⟨htpos, hsmall⟩
    simp only [mul_zero, mul_one, add_zero] at heq
    rw [sourceRayExtension_nonneg ℓ 0 le_rfl,
      sourceRayExtension_nonneg ℓ 1 (by norm_num), h.2,
      sourceRayExtension_nonneg ℓ t.1 htpos.le] at heq
    rw [← heq] at hle
    simpa only [mul_neg, mul_comm t.1 K] using hle
  · have hlarge : 1 < t.1 := lt_of_le_of_ne (le_of_not_gt hsmall) (Ne.symm ht1)
    by_cases hx : φ x = ⊥
    · simp [hx]
    have hfinite (s : Ici (0 : ℝ)) : ℓ s x ≠ ⊤ ∧ ℓ s x ≠ ⊥ := by
      refine ⟨((isThetaPSH_iff_nativeThetaPotential θ _).mp (h.1.2 s).1).1.quasiPlurisubharmonic.ne_top x, ?_⟩
      obtain ⟨B, hB⟩ := (h.1.2 s).2.2
      intro hb
      exact hx (le_bot_iff.mp (by simpa [hb] using hB x (mem_univ _)))
    have hp : φ x ≠ ⊤ :=
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hφ.thetaPSH).1.quasiPlurisubharmonic.ne_top x
    have hch := (hR.1.isSubgeodesicRay 0 t.1 le_rfl htpos.le).2.le_closedChord
      (a := 0) (b := 1) (s := 1 / t.1) le_rfl le_rfl zero_lt_one
        ⟨(div_pos zero_lt_one htpos).le, (div_le_one htpos).mpr hlarge.le⟩ x
    have hs : 1 / t.1 ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos zero_lt_one htpos, (div_lt_one htpos).mpr hlarge⟩
    simp only [mul_zero, mul_one, add_zero, zero_add, closedSubgeodesicSlice_zero,
      closedSubgeodesicSlice_one] at hch
    rw [closedSubgeodesicSlice_eq_curve hs] at hch
    have htime : (1 / t.1) * t.1 = 1 := div_mul_cancel₀ _ htpos.ne'
    simp only [htime, sourceRayExtension_nonneg ℓ 0 le_rfl,
      sourceRayExtension_nonneg ℓ 1 (by norm_num),
      sourceRayExtension_nonneg ℓ t.1 htpos.le, h.2] at hch
    rw [← EReal.coe_toReal hp hx,
      ← EReal.coe_toReal (hfinite ⟨1, by norm_num⟩).1 (hfinite ⟨1, by norm_num⟩).2,
      ← EReal.coe_toReal (hfinite t).1 (hfinite t).2,
      SubgeodesicInfimum.eRealChord_coe_coe, EReal.coe_le_coe_iff] at hch
    have hlow := h1 x
    rw [← EReal.coe_toReal hp hx,
      ← EReal.coe_toReal (hfinite ⟨1, by norm_num⟩).1 (hfinite ⟨1, by norm_num⟩).2,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hlow
    change φ x + ((-(K * t.1) : ℝ) : EReal) ≤ ℓ t x
    rw [← EReal.coe_toReal hp hx, ← EReal.coe_toReal (hfinite t).1 (hfinite t).2,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hmul := mul_le_mul_of_nonneg_left hch htpos.le
    have hcancel : t.1 * (1 / t.1) = 1 := by field_simp
    simp only [mul_add, ← mul_assoc, hcancel, one_mul] at hmul
    have hcoeff : t.1 * (1 - 1 / t.1) = t.1 - 1 := by field_simp
    rw [hcoeff] at hmul
    nlinarith

/-- The original bounded ray INTERNALLY produces a real threshold. Below
it every literal inverse dominates the model, and EVERY actual sub-cutoff
inverse equals that SAME model as a function, including all model poles. -/
theorem source_bounded_ray_inverse_eq_model_of_le (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceBoundedRays omega θ φ hφ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ τ : ℝ, τ ≤ -K → φ ≤ sourcePositiveRayInverse ℓ τ) ∧
      (∀ τ : Iio (sourceRayLegendreCutoff omega ⟨h.1.1, h.2⟩),
        τ.1 ≤ -K → sourcePositiveRayInverse ℓ τ.1 = φ) := by
  have hR : ℓ ∈ sourceGeodesicRays omega θ φ hφ := ⟨h.1.1, h.2⟩
  obtain ⟨K, hK, hlow⟩ := source_bounded_ray_uniform_lower_bound omega h
  have hχlow (τ : ℝ) (hτ : τ ≤ -K) : φ ≤ sourcePositiveRayInverse ℓ τ := by
    intro x
    apply le_iInf
    intro t
    have ht : 0 < t.1 := t.2
    rw [sourceRayExtension_nonneg ℓ t.1 ht.le]
    apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr
    exact (add_le_add le_rfl (EReal.coe_le_coe
      (show t.1 * τ ≤ -(K * t.1) by nlinarith))).trans (hlow ⟨t.1, ht.le⟩ x)
  refine ⟨K, hK, hχlow, ?_⟩
  intro τ hτ
  apply le_antisymm
  · intro x
    have hsup : sourcePositiveRayInverse ℓ τ.1 x ≤
        SGPT.PSH.uscSup (fun q : Iio (sourceRayLegendreCutoff omega hR) ↦
          sourcePositiveRayInverse ℓ q.1) x :=
      (le_iSup (fun q : Iio (sourceRayLegendreCutoff omega hR) ↦
        sourcePositiveRayInverse ℓ q.1 x) τ).trans
          (le_uscRegularization (fun y ↦ ⨆ q : Iio (sourceRayLegendreCutoff omega hR),
            sourcePositiveRayInverse ℓ q.1 y) x)
    rwa [sourceRayLegendre_inverse_uscSup_eq_model omega hR] at hsup
  · exact hχlow τ.1 hτ

/-- The produced threshold yields EXACT original atBot eventual equality
on the genuine open cutoff interval, without reparametrizing the family. -/
theorem source_bounded_ray_inverse_eventually_model (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceBoundedRays omega θ φ hφ) :
    SourceTestCurveIsBounded φ (sourceRayLegendreTestCurve omega ⟨h.1.1, h.2⟩) := by
  obtain ⟨K, _, _, heq⟩ := source_bounded_ray_inverse_eq_model_of_le omega h
  let C := sourceRayLegendreCutoff omega ⟨h.1.1, h.2⟩
  let σ : Iio C := ⟨min (-K) (C - 1) - 1, by
    change min (-K) (C - 1) - 1 < C
    linarith [min_le_right (-K) (C - 1)]⟩
  change ∀ᶠ τ : Iio C in atBot, sourcePositiveRayInverse ℓ τ.1 = φ
  filter_upwards [eventually_le_atBot σ] with τ hτ
  apply heq τ
  have hreal : τ.1 ≤ σ.1 := hτ
  change τ.1 ≤ -K
  dsimp [σ] at hreal
  linarith [min_le_left (-K) (C - 1)]

/-- The ACTUAL inverse manufactured from an original bounded ray belongs
to the original bounded based class, with its literal potentials unchanged. -/
theorem source_test_curve_legendre_bounded_reverse (omega : KahlerBackground n M)
    {ℓ : SourceRayFamily M} (h : ℓ ∈ sourceBoundedRays omega θ φ hφ) :
    sourceRayLegendreTestCurve omega ⟨h.1.1, h.2⟩ ∈ SourceBoundedTestCurves θ φ hφ :=
  ⟨(source_ray_legendre_test_curve_whole omega ⟨h.1.1, h.2⟩).1,
    source_bounded_ray_inverse_eventually_model omega h⟩

/-- Both original bounded Legendre MAP RESTRICTIONS, with every original
nonnegative time and arbitrary unbounded positive model retained.
This proves exactly Step 2's well-defined maps, not the energy correspondence. -/
theorem source_test_curve_legendre_bounded_whole (omega : KahlerBackground n M) :
    (∀ (Γ : SourceTestCurve θ), Γ ∈ SourceBoundedTestCurves θ φ hφ →
      sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ∈ sourceBoundedRays omega θ φ hφ) ∧
    (∀ (ℓ : SourceRayFamily M) (h : ℓ ∈ sourceBoundedRays omega θ φ hφ),
      sourceRayLegendreTestCurve omega ⟨h.1.1, h.2⟩ ∈ SourceBoundedTestCurves θ φ hφ) :=
  ⟨fun Γ hΓ ↦ source_test_curve_legendre_bounded_forward omega Γ hΓ,
    fun _ h ↦ source_test_curve_legendre_bounded_reverse omega h⟩

/-- The actual bounded Ross--Witt Nyström equivalence, on the SAME original
bounded subtypes and arbitrary unbounded positive model. This is precisely
the bounded restriction; the finite-energy and energy claims are separate. -/
def sourceTestCurveBoundedLegendreEquiv (omega : KahlerBackground n M)
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) :
    {Γ : SourceTestCurve θ // Γ ∈ SourceBoundedTestCurves θ φ hφ} ≃
      {ℓ : SourceRayFamily M // ℓ ∈ sourceBoundedRays omega θ φ hφ} where
  toFun Γ := ⟨sourceTestCurveLegendreRay Γ.1.toSourceTestCurvePredata,
    source_test_curve_legendre_bounded_forward omega Γ.1 Γ.2⟩
  invFun ℓ := ⟨sourceRayLegendreTestCurve omega ⟨ℓ.2.1.1, ℓ.2.2⟩,
    source_test_curve_legendre_bounded_reverse omega ℓ.2⟩
  left_inv Γ := Subtype.ext (sourceTestCurveLegendre_left_inverse omega Γ.1 Γ.2.1)
  right_inv ℓ := Subtype.ext (sourceRayLegendre_right_inverse omega ⟨ℓ.2.1.1, ℓ.2.2⟩)

end SGPT.PSH.VariableComplexAtlas
