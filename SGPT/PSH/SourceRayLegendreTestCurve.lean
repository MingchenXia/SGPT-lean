import SGPT.PSH.SourceTestCurveLegendreGeodesic
import SGPT.PSH.SourceSubgeodesicLinearBound
import SGPT.PSH.SourceSubgeodesicEndpoints

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
  {φ : M → EReal} {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}

/-- The actual original full-mass ray fields manufacture genuine whole
subgeodesicity, with every closed interval and global L1 endpoint limits. -/
theorem SourceIsRelativeGeodesicRay.isSubgeodesicRay
    {omega : KahlerBackground n M} (h : SourceIsRelativeGeodesicRay omega θ φ hφ ℓ) :
    SourceIsSubgeodesicRay omega θ ℓ := by
  intro a b ha hab
  have hg := h.2 a b ha hab
  have hp := sourcePerron_isSubgeodesicFrom_of_relativeFullMass omega
    (h.1 ⟨a, ha⟩) (h.1 ⟨b, ha.trans hab⟩)
  refine ⟨hab, ?_⟩
  rw [sourceRayExtension_nonneg ℓ a ha, sourceRayExtension_nonneg ℓ b (ha.trans hab)]
  apply hp.congr_Ioo
  intro s hs
  simpa only [sourceRayExtension_nonneg ℓ a ha,
    sourceRayExtension_nonneg ℓ b (ha.trans hab)] using (hg.2.2.2.2.2 s hs).symm

/-- The original real cutoff is read ONLY AFTER the actual time-one
spatial supremum has been proved different from BOTH infinite endpoints. -/
def sourceRayLegendreCutoff (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) : ℝ :=
  let S : {q : EReal // q ≠ ⊤ ∧ q ≠ ⊥} :=
    ⟨⨆ x, ℓ ⟨1, by norm_num⟩ x, sourceRay_globalSup_finite omega h ⟨1, by norm_num⟩⟩
  S.1.toReal

/-- Genuine original ray data produce exact linear spatial suprema,
the SAME model bound and normalized decrease at ALL nonnegative times. -/
theorem sourceRayLegendre_normalized (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    (∀ t : Ici (0 : ℝ), (⨆ x, ℓ t x) = ((t.1 * sourceRayLegendreCutoff omega h : ℝ) : EReal)) ∧
    (∀ t : Ici (0 : ℝ), ℓ t ≤ fun x ↦ φ x + ((t.1 * sourceRayLegendreCutoff omega h : ℝ) : EReal)) ∧
    (∀ x, AntitoneOn
      (fun t : ℝ ↦ sourceRayExtension ℓ t x - ((t * sourceRayLegendreCutoff omega h : ℝ) : EReal))
      (Ici 0)) := by
  refine ⟨fun t ↦ sourceRay_globalSup_eq omega h t,
    fun t ↦ sourceRay_le_model_add_linear omega h t, ?_⟩
  intro x
  apply h.1.isSubgeodesicRay.normalized_antitone_of_linear_upper_bound (sourceRayLegendreCutoff omega h)
  intro t x
  exact (le_iSup (fun x ↦ ℓ t x) x).trans_eq (sourceRay_globalSup_eq omega h t)

private theorem rayCutoffInverse_genuine (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ (sourceRayLegendreCutoff omega h)) ∧
      (⨆ x, sourcePositiveRayInverse ℓ (sourceRayLegendreCutoff omega h) x) = 0 := by
  let C := sourceRayLegendreCutoff omega h
  let v : Ioi (0 : ℝ) → M → EReal := fun t x ↦
    sourceRayExtension ℓ t.1 x - ((t.1 * C : ℝ) : EReal)
  let : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have hv (t : Ioi (0 : ℝ)) : (ofFixedModel n M).IsThetaPSH θ (v t) := by
    have ht : 0 < t.1 := t.2
    have hh := sourceThetaPSH_add_const (h.1.1 ⟨t.1, ht.le⟩).choose (-(t.1 * C))
    simpa only [v, sourceRayExtension_nonneg ℓ t.1 ht.le,
      sub_eq_add_neg, EReal.coe_neg] using hh
  have hsup (t : Ioi (0 : ℝ)) : (⨆ x, v t x) = 0 := by
    have ht : 0 < t.1 := t.2
    simp only [v, sourceRayExtension_nonneg ℓ t.1 ht.le, sub_eq_add_neg, ← EReal.coe_neg]
    rw [iSup_add_coe, sourceRay_globalSup_eq omega h ⟨t.1, ht.le⟩]
    change ((t.1 * C : ℝ) : EReal) + ((-(t.1 * C) : ℝ) : EReal) = 0
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hanti (x : M) : Antitone (fun t ↦ v t x) := by
    intro s t hst
    exact (sourceRayLegendre_normalized omega h).2.2 x
      (show 0 < s.1 from s.2).le (show 0 < t.1 from t.2).le hst
  have hn := SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun t ↦ (isThetaPSH_iff_nativeThetaPotential θ _).mp (hv t)) hanti 0
    (fun t ↦ by simp only [EReal.coe_zero, hsup t, le_refl])
  have htheta : (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ C) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr hn.1
  have hlim : Tendsto (fun t : Ioi (0 : ℝ) ↦ ⨆ x, v t x) atTop
      (𝓝 (⨆ x, sourcePositiveRayInverse ℓ C x)) := hn.2
  have hzero : Tendsto (fun t : Ioi (0 : ℝ) ↦ ⨆ x, v t x) atTop (𝓝 (0 : EReal)) := by
    simpa only [hsup] using
      (tendsto_const_nhds : Tendsto (fun _ : Ioi (0 : ℝ) ↦ (0 : EReal)) atTop (𝓝 0))
  exact ⟨htheta, tendsto_nhds_unique hlim hzero⟩

/-- Genuine cutoff PSH is produced BEFORE ANY cutoff fixed-point argument,
using the original normalized directed family and its actual spatial sup0. -/
theorem sourceRayLegendre_cutoff_thetaPSH (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ (sourceRayLegendreCutoff omega h)) :=
  (rayCutoffInverse_genuine omega h).1

/-- The same actual directed-compact producer also gives exact spatial
supremum zero at the genuine cutoff, without positive cutoff mass. -/
theorem sourceRayLegendre_cutoff_supremum (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    (⨆ x, sourcePositiveRayInverse ℓ (sourceRayLegendreCutoff omega h) x) = 0 :=
  (rayCutoffInverse_genuine omega h).2

omit [ConnectedSpace M] in
private theorem sourceRayInverse_le_linear (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (τ : ℝ)
    {t : ℝ} (ht : 0 < t) (x : M) :
    sourcePositiveRayInverse ℓ τ x ≤ ((t * (sourceRayLegendreCutoff omega h - τ) : ℝ) : EReal) := by
  have hbound : sourceRayExtension ℓ t x ≤ ((t * sourceRayLegendreCutoff omega h : ℝ) : EReal) := by
    rw [sourceRayExtension_nonneg ℓ t ht.le]
    exact (le_iSup (fun x ↦ ℓ ⟨t, ht.le⟩ x) x).trans_eq
      (sourceRay_globalSup_eq omega h ⟨t, ht.le⟩)
  have hh := (iInf_le (fun s : Ioi (0 : ℝ) ↦
    sourceRayExtension ℓ s.1 x - ((s.1 * τ : ℝ) : EReal)) ⟨t, ht⟩).trans
      (EReal.sub_le_sub hbound le_rfl)
  simpa only [sourcePositiveRayInverse, ← EReal.coe_sub, ← mul_sub] using hh

omit [ConnectedSpace M] in
/-- Every original real-parameter inverse is nonpositive, by the actual
nontrivial positive-right limit of its produced finite linear bound. -/
theorem sourceRayLegendre_inverse_nonpositive (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (τ : ℝ) :
    sourcePositiveRayInverse ℓ τ ≤ 0 := by
  intro x
  let C := sourceRayLegendreCutoff omega h
  have hf : Continuous (fun t : ℝ ↦ ((-(t * (C - τ)) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp ((continuous_id.mul continuous_const).neg)
  have hlim : Tendsto (fun t : ℝ ↦ ((-(t * (C - τ)) : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    simpa only [zero_mul, neg_zero, EReal.coe_zero] using
      (hf.tendsto (0 : ℝ)).mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hneg : (0 : EReal) ≤ -sourcePositiveRayInverse ℓ τ x := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [EReal.coe_neg] using EReal.neg_le_neg_iff.mpr
      (sourceRayInverse_le_linear omega h τ ht x)
  exact EReal.neg_nonneg.mp hneg

omit [ConnectedSpace M] in
/-- Strictly above the actual finite inverse cutoff the WHOLE original
positive-time infimum is literally the bottom function. -/
theorem sourceRayLegendre_inverse_bot_above (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ}
    (hτ : sourceRayLegendreCutoff omega h < τ) : sourcePositiveRayInverse ℓ τ = ⊥ := by
  funext x
  apply le_bot_iff.mp
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r _
  let C := sourceRayLegendreCutoff omega h
  let t : ℝ := Max.max 1 ((r - 1) / (C - τ))
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hδ : C - τ < 0 := sub_neg.mpr hτ
  have hmul : t * (C - τ) ≤ r - 1 := by
    have hh := mul_le_mul_of_nonpos_right (le_max_right (1 : ℝ) ((r - 1) / (C - τ))) hδ.le
    simpa only [div_mul_cancel₀ _ hδ.ne] using hh
  exact (sourceRayInverse_le_linear omega h τ ht x).trans
    (EReal.coe_le_coe (by linarith : t * (C - τ) ≤ r))

private theorem positiveInverse_precedes_time_one {X : Type*} (R : SourceRayFamily X)
    (τ : ℝ) : SGPT.PSH.SingularityLE (sourcePositiveRayInverse R τ) (R ⟨1, by norm_num⟩) := by
  refine ⟨-τ, fun y _ ↦ ?_⟩
  have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
    sourceRayExtension R t.1 y - ((t.1 * τ : ℝ) : EReal)) ⟨1, by norm_num⟩
  simpa only [sourcePositiveRayInverse, sourceRayExtension_nonneg R 1 (by norm_num),
    one_mul, sub_eq_add_neg, EReal.coe_neg] using hh

omit [ConnectedSpace M] in
/-- EVERY actual ordinary-envelope competitor is bounded by the SAME
inverse, using the original ray's genuine Perron maximality. This applies
already at the genuine cutoff and assumes no cutoff fixedness or mass. -/
theorem sourceRayLegendre_inverse_fixedPoint_of_thetaPSH (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (τ : ℝ)
    (hχ : (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ)) :
    sourceSingularityEnvelope θ (sourcePositiveRayInverse ℓ τ) = sourcePositiveRayInverse ℓ τ := by
  let χ := sourcePositiveRayInverse ℓ τ
  have hχ0 := sourceRayLegendre_inverse_nonpositive omega h τ
  have hχφ : SGPT.PSH.SingularityLE χ φ :=
    (positiveInverse_precedes_time_one ℓ τ).trans (h.1.1 ⟨1, by norm_num⟩).choose_spec.1
  apply le_antisymm
  · change uscRegularization (fun y ↦ ⨆ w : sourceSingularityCompetitors θ χ, w.1 y) ≤ χ
    apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hχ).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro w
    obtain ⟨K, hK⟩ := w.2.2.2
    let D : ℝ := Max.max K 0
    have hD : 0 ≤ D := le_max_right _ _
    have hwχ (y : M) : w.1 y ≤ χ y + (D : EReal) :=
      (hK y (mem_univ y)).trans (add_le_add le_rfl (EReal.coe_le_coe (le_max_left K 0)))
    have hwφ : w.1 ≤ φ := sourceModel_nonpositive_le hφ
      ⟨w.2.1, w.2.2.2.trans hχφ⟩ w.2.2.1
    have htime (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (T : ℝ) (hT : 0 < T) (y : M) :
        w.1 y - ((D * s : ℝ) : EReal) ≤
          sourceRayExtension ℓ (s * T) y - (((s * T) * τ : ℝ) : EReal) := by
      have hterminal (y : M) : w.1 y + ((T * τ - D : ℝ) : EReal) ≤ ℓ ⟨T, hT.le⟩ y := by
        have hχT : χ y ≤ ℓ ⟨T, hT.le⟩ y - ((T * τ : ℝ) : EReal) := by
          have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
            sourceRayExtension ℓ t.1 y - ((t.1 * τ : ℝ) : EReal)) ⟨T, hT⟩
          simpa only [χ, sourcePositiveRayInverse, sourceRayExtension_nonneg ℓ T hT.le] using hh
        calc
          w.1 y + ((T * τ - D : ℝ) : EReal) ≤
              (χ y + (D : EReal)) + ((T * τ - D : ℝ) : EReal) := add_le_add (hwχ y) le_rfl
          _ = χ y + ((T * τ : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add]
            congr 2
            ring
          _ ≤ ℓ ⟨T, hT.le⟩ y := by
            simpa only [EReal.sub_add_cancel] using
              add_le_add hχT (le_rfl : ((T * τ : ℝ) : EReal) ≤ ((T * τ : ℝ) : EReal))
      have hq := sourceSubgeodesic_affine omega w.2.1 (T * τ - D)
      have hc : (fun s : ℝ ↦ fun y ↦ w.1 y + ((s * (T * τ - D) : ℝ) : EReal)) ∈
          sourcePerronCompetitors omega θ φ (ℓ ⟨T, hT.le⟩) :=
        ⟨w.1, (fun y ↦ w.1 y + ((T * τ - D : ℝ) : EReal)), w.2.1,
          sourceThetaPSH_add_const w.2.1 (T * τ - D), hwφ, hterminal, hq⟩
      have hg := (h.1.2 0 T le_rfl hT.le).2.2.2.2.2 s hs
      simp only [mul_zero, add_zero] at hg
      rw [sourceRayExtension_nonneg ℓ 0 (by norm_num), h.2,
        sourceRayExtension_nonneg ℓ T hT.le] at hg
      have hdom := sourcePerron_competitor_le hc s y
      rw [← hg] at hdom
      apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).mpr
      convert hdom using 1
      simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
      congr 2
      ring
    have hwhole (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (y : M) :
        w.1 y - ((D * s : ℝ) : EReal) ≤ χ y := by
      apply le_iInf
      intro t
      have ht : 0 < t.1 := t.2
      have heq : s * (t.1 / s) = t.1 := by field_simp [hs.1.ne']
      simpa only [heq] using htime s hs (t.1 / s) (div_pos ht hs.1) y
    have hDlim : Tendsto (fun s : ℝ ↦ ((D * s : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
      have hf : Continuous (fun s : ℝ ↦ ((D * s : ℝ) : EReal)) :=
        continuous_coe_real_ereal.comp (continuous_const.mul continuous_id)
      simpa only [mul_zero, EReal.coe_zero] using
        (hf.tendsto (0 : ℝ)).mono_left
          (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hpair : Tendsto (fun s : ℝ ↦ (χ x, ((D * s : ℝ) : EReal)))
        (𝓝[>] (0 : ℝ)) (𝓝 (χ x, (0 : EReal))) := tendsto_const_nhds.prodMk_nhds hDlim
    have hadd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (χ x, (0 : EReal)) :=
      EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
    have hlim : Tendsto (fun s : ℝ ↦ χ x + ((D * s : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 (χ x)) := by
      simpa only [Function.comp_def, add_zero] using hadd.tendsto.comp hpair
    have hneg : -χ x ≤ -w.1 x := by
      apply le_of_tendsto ((continuous_neg : Continuous (fun z : EReal ↦ -z)).tendsto (χ x) |>.comp hlim)
      filter_upwards [sourceRay_endpoint_filters.1] with s hs
      exact EReal.neg_le_neg_iff.mpr ((EReal.sub_le_iff_le_add
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mp (hwhole s hs x))
    exact EReal.neg_le_neg_iff.mp hneg
  · exact le_sourceSingularityEnvelope hχ hχ0 (MoreSingularOn.refl _ univ)

/-- The already produced genuine cutoff fixed point is an ACTUAL lower
barrier for every lower parameter; the existing generic whole-inverse
producer therefore gives all source PSH slices without analytic duplication. -/
theorem sourceRayLegendre_inverse_thetaPSH (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ}
    (hτ : τ ≤ sourceRayLegendreCutoff omega h) :
    (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ) := by
  have hC := sourceRayLegendre_cutoff_thetaPSH omega h
  have hfix := sourceRayLegendre_inverse_fixedPoint_of_thetaPSH omega h
    (sourceRayLegendreCutoff omega h) hC
  apply h.1.isSubgeodesicRay.inverse_thetaPSH_of_lower_fixedPoint hC hfix τ
  intro t ht x
  exact (iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceRayExtension ℓ s.1 x -
    ((s.1 * sourceRayLegendreCutoff omega h : ℝ) : EReal)) ⟨t, ht⟩).trans
      (EReal.sub_le_sub le_rfl (EReal.coe_le_coe (mul_le_mul_of_nonneg_left hτ ht.le)))

/-- Every genuine sub-cutoff inverse is an ordinary fixed point, with
all generic producer hypotheses discharged from the original ray fields. -/
theorem sourceRayLegendre_inverse_fixedPoint (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ}
    (hτ : τ ≤ sourceRayLegendreCutoff omega h) :
    sourceSingularityEnvelope θ (sourcePositiveRayInverse ℓ τ) = sourcePositiveRayInverse ℓ τ :=
  sourceRayLegendre_inverse_fixedPoint_of_thetaPSH omega h τ
    (sourceRayLegendre_inverse_thetaPSH omega h hτ)

/-- Actual finite-positive-time coefficients give original parameter
antitonicity for ANY source ray, retaining all poles and infinities. -/
theorem sourceRayLegendre_inverse_antitone {X : Type*} (R : SourceRayFamily X) (x : X) :
    Antitone (fun τ : ℝ ↦ sourcePositiveRayInverse R τ x) := by
  intro a b hab
  apply iInf_mono
  intro t
  have ht : 0 < t.1 := t.2
  exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe (mul_le_mul_of_nonneg_left hab ht.le))

/-- EXISTING genuine conjugate convexity, restricted to the SAME original
sub-cutoff epigraph, produces precisely the original source concavity. -/
theorem sourceRayLegendre_inverse_concave {X : Type*} (R : SourceRayFamily X)
    (C : ℝ) (x : X) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace C
      (fun τ : Iio C ↦ sourcePositiveRayInverse R τ.1) x) := by
  have hc := SGPT.Convex.isConvex_halfLineConjugate (fun t ↦ sourceRayExtension R t x)
  change Convex ℝ (SGPT.Convex.epigraph _)
  convert (((convex_Iio C).prod (convex_univ : Convex ℝ (univ : Set ℝ))).inter hc) using 1
  ext p
  by_cases hp : p.1 < C
  · simp [sourceTestCurveNegativeTrace, SGPT.Convex.epigraph, hp,
      sourcePositiveRayInverse_conjugate]
  · simp [sourceTestCurveNegativeTrace, SGPT.Convex.epigraph, hp]

private def rayLegendrePredata (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) : SourceTestCurvePredata θ where
  max := sourceRayLegendreCutoff omega h
  potential := fun τ ↦ sourcePositiveRayInverse ℓ τ.1
  thetaPSH := fun τ ↦ sourceRayLegendre_inverse_thetaPSH omega h (le_of_lt τ.2)
  antitone := fun x _ _ hab ↦ sourceRayLegendre_inverse_antitone ℓ x hab
  concave := sourceRayLegendre_inverse_concave ℓ _
  fixedPoint := fun τ ↦ sourceRayLegendre_inverse_fixedPoint omega h (le_of_lt τ.2)

/-- Existing full half-line biconjugation recovers the SAME original ray
at every positive time, including every bottom vertical trace. -/
private theorem rayLegendre_positive_inversion (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {t : ℝ} (ht : 0 < t) (x : M) :
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

private theorem rayLegendreLimit_le_model (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    sourceTestCurveLimit (rayLegendrePredata omega h) ≤ φ := by
  apply uscRegularization_le
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ.thetaPSH).1.quasiPlurisubharmonic.upperSemicontinuous
  intro x
  apply iSup_le
  intro τ
  apply sourceModel_nonpositive_le hφ
    ⟨sourceRayLegendre_inverse_thetaPSH omega h (le_of_lt τ.2), ?_⟩
    (sourceRayLegendre_inverse_nonpositive omega h τ.1) x
  exact (positiveInverse_precedes_time_one ℓ τ.1).trans (h.1.1 ⟨1, by norm_num⟩).choose_spec.1

private theorem rayLegendre_le_limit_add (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {t : ℝ} (ht : 0 < t) (x : M) :
    sourceRayExtension ℓ t x ≤ sourceTestCurveLimit (rayLegendrePredata omega h) x +
      ((t * sourceRayLegendreCutoff omega h : ℝ) : EReal) := by
  let C := sourceRayLegendreCutoff omega h
  let ψ := sourceTestCurveLimit (rayLegendrePredata omega h)
  have hslice (τ : ℝ) (hτ : τ < C) : sourcePositiveRayInverse ℓ τ x ≤ ψ x :=
    (le_iSup (fun q : Iio C ↦ sourcePositiveRayInverse ℓ q.1 x) ⟨τ, hτ⟩).trans
      (le_uscRegularization (fun y ↦ ⨆ q : Iio C, sourcePositiveRayInverse ℓ q.1 y) x)
  rw [rayLegendre_positive_inversion omega h ht x]
  apply iSup_le
  intro τ
  by_cases hτ : C < τ
  · rw [sourceRayLegendre_inverse_bot_above omega h hτ]
    simp
  · have hτC : τ ≤ C := le_of_not_gt hτ
    have hχ : sourcePositiveRayInverse ℓ τ x ≤ ψ x := by
      rcases lt_or_eq_of_le hτC with hlt | heq
      · exact hslice τ hlt
      · rw [heq]
        exact (sourceRayLegendre_inverse_antitone ℓ x (show C - 1 ≤ C by linarith)).trans
          (hslice (C - 1) (by linarith))
    rw [add_comm]
    exact add_le_add hχ (EReal.coe_le_coe (mul_le_mul_of_nonneg_left hτC ht.le))

/-- The original ONE endpoint QE event, actual positive-time inversion and
source PSH comparison identify the literal usc supremum with the model
EVERYWHERE; no new endpoint equality or representative is assumed. -/
private theorem rayLegendreLimit_eq_model (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    sourceTestCurveLimit (rayLegendrePredata omega h) = φ := by
  let ψ := sourceTestCurveLimit (rayLegendrePredata omega h)
  have hψ := (rayLegendrePredata omega h).limit_thetaPSH
  apply le_antisymm (rayLegendreLimit_le_model omega h)
  apply (sourceQuasiEverywhere_le_iff hφ.thetaPSH hψ).mp
  have hu : SourceSubgeodesicFrom omega θ (fun s ↦ sourceRayExtension ℓ s) φ
      (ℓ ⟨1, by norm_num⟩) := by
    have hh := (h.1.isSubgeodesicRay 0 1 le_rfl (by norm_num)).2
    simpa only [mul_one, mul_zero, add_zero,
      sourceRayExtension_nonneg ℓ 0 le_rfl, sourceRayExtension_nonneg ℓ 1 (by norm_num), h.2] using hh
  apply (sourceQuasiEverywhere_iff_native _).mpr
  apply ((sourceQuasiEverywhere_iff_native _).mp
    (sourceSubgeodesicLeftLimit_quasiEverywhere hu)).mono
  intro x hx
  have hL := tendsto_sourceSubgeodesicLeftLimit hu x
  rw [hx] at hL
  have hc : Tendsto (fun s : ℝ ↦ ((s * sourceRayLegendreCutoff omega h : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    have hf : Continuous (fun s : ℝ ↦ ((s * sourceRayLegendreCutoff omega h : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (continuous_id.mul continuous_const)
    simpa only [zero_mul, EReal.coe_zero] using
      (hf.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hadd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (ψ x, (0 : EReal)) :=
    EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
  have hR : Tendsto (fun s : ℝ ↦ ψ x + ((s * sourceRayLegendreCutoff omega h : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (ψ x)) := by
    simpa only [Function.comp_def, add_zero] using
      hadd.tendsto.comp (tendsto_const_nhds.prodMk_nhds hc)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact rayLegendre_le_limit_add omega h hs x

/-- The LITERAL original sub-cutoff usc supremum, at every original point,
is exactly the original positive model with its assigned poles. -/
theorem sourceRayLegendre_inverse_uscSup_eq_model (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    SGPT.PSH.uscSup (fun τ : Iio (sourceRayLegendreCutoff omega h) ↦
      sourcePositiveRayInverse ℓ τ.1) = φ := rayLegendreLimit_eq_model omega h

/-- The genuine ENTIRE original source test curve manufactured from the
original ray, with its ACTUAL positive limit mass produced from the model. -/
def sourceRayLegendreTestCurve (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) : SourceTestCurve θ where
  toSourceTestCurvePredata := rayLegendrePredata omega h
  positiveLimitMass := by
    have heq := rayLegendreLimit_eq_model omega h
    generalize rayLegendrePredata omega h = Γ at heq ⊢
    cases heq
    exact hφ.choose_spec.2

/-- The constructed test curve retains the ACTUAL finite time-one cutoff. -/
theorem sourceRayLegendreTestCurve_max (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    (sourceRayLegendreTestCurve omega h).max = sourceRayLegendreCutoff omega h := rfl

/-- Every original sub-cutoff potential is the LITERAL positive-time infimum. -/
theorem sourceRayLegendreTestCurve_potential (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ)
    (τ : Iio (sourceRayLegendreCutoff omega h)) :
    (sourceRayLegendreTestCurve omega h).potential τ = sourcePositiveRayInverse ℓ τ.1 := rfl

/-- WHOLE original lma:LegendsRtoTC: an actual original based test curve,
with its actual literal inverse potentials and the produced finite cutoff.
All original ray hypotheses are retained without finite-energy restrictions. -/
theorem source_ray_legendre_test_curve_whole (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    sourceRayLegendreTestCurve omega h ∈ SourceTestCurvesBased θ φ hφ ∧
    (sourceRayLegendreTestCurve omega h).max = sourceRayLegendreCutoff omega h ∧
    (∀ τ : Iio (sourceRayLegendreCutoff omega h),
      (sourceRayLegendreTestCurve omega h).potential τ = sourcePositiveRayInverse ℓ τ.1) :=
  ⟨rayLegendreLimit_eq_model omega h, rfl, fun _ ↦ rfl⟩

/-- WHOLE original cor:reltestcursuplinear for the SAME inverse test curve:
actual spatial suprema and normalized pointwise decrease at ALL nonnegative
times, with the original assigned time-zero value included. -/
theorem source_ray_inverse_cutoff_linear_whole (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    (∀ t : Ici (0 : ℝ), (⨆ x, ℓ t x) =
      ((t.1 * (sourceRayLegendreTestCurve omega h).max : ℝ) : EReal)) ∧
    (∀ x, AntitoneOn
      (fun t : ℝ ↦ sourceRayExtension ℓ t x -
        ((t * (sourceRayLegendreTestCurve omega h).max : ℝ) : EReal)) (Ici 0)) :=
  ⟨(sourceRayLegendre_normalized omega h).1, (sourceRayLegendre_normalized omega h).2.2⟩

end SGPT.PSH.VariableComplexAtlas
