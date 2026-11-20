import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayMetricGeometry

set_option autoImplicit false

/-!
# The actual finite radial Darvas metric over a singular model

Xia SGPT PDF0174--0175 Definition 4.3.5 and Theorem 4.3.4. Actual
positive-time ratio monotonicity and the internally produced finite speed
bound give a finite real radial limit. The existing actual extended
rayD1 is identified with that real value. Actual slice metric laws then
give separation and a genuine native metric space on actual based rays.
No bounded reference, normalization, linear-growth or limit certificate
is a hypothesis. Completeness is not asserted by this construction.
-/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayDistance

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeGeodesicRays SingularModelGeodesicRays
  SingularModelGeodesicRayMetricGeometry SingularModelDarvasMetricSpace

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Actual ratio monotonicity and actual finite speed bounds produce a genuine finite real limit of the defining radial distance. -/
theorem exists_tendsto_rayD1 (omega : KahlerBackground n M)
    (L K : ModelFiniteEnergyGeodesicRay θ φ hφ) (h0 : L.rawCurve 0 = K.rawCurve 0) :
    ∃ m : ℝ, 0 ≤ m ∧
      Tendsto (fun t : ℝ => relativeD1 θ φ hφ (L.rawCurve t) (K.rawCurve t) / t)
        atTop (𝓝 m) ∧
      (∀ t : ℝ, 0 < t → relativeD1 θ φ hφ (L.rawCurve t) (K.rawCurve t) / t ≤ m) ∧
      rayD1 θ φ hφ L.rawCurve K.rawCurve = (m : EReal) := by
  let D : ℝ → ℝ := fun t => relativeD1 θ φ hφ (L.rawCurve t) (K.rawCurve t)
  let F : ℝ → ℝ := fun t => if 0 < t then D t / t else 0
  have hF0 (t : ℝ) : 0 ≤ F t := by
    dsimp [F]
    split_ifs with ht
    · exact (relativeD1_rays_div_le_speeds omega L K h0 ht).1
    · exact le_rfl
  have hmono : Monotone F := by
    intro s t hst
    by_cases hs : 0 < s
    · have ht : 0 < t := hs.trans_le hst
      simp only [F, if_pos hs, if_pos ht]
      exact relativeD1_rays_div_mono omega L K h0 hs hst
    · simp only [F, if_neg hs]
      exact hF0 t
  have hspeed0 : 0 ≤ relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) +
      relativeD1 θ φ hφ (K.rawCurve 0) (K.rawCurve 1) :=
    add_nonneg (SingularModelDarvasBasic.relativeD1_nonneg omega
      (L.finiteEnergy_rawCurve 0) (L.finiteEnergy_rawCurve 1))
      (SingularModelDarvasBasic.relativeD1_nonneg omega
        (K.finiteEnergy_rawCurve 0) (K.finiteEnergy_rawCurve 1))
  have hbdd : BddAbove (range F) := by
    refine ⟨relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) +
      relativeD1 θ φ hφ (K.rawCurve 0) (K.rawCurve 1), ?_⟩
    rintro _ ⟨t, rfl⟩
    dsimp [F]
    split_ifs with ht
    · exact (relativeD1_rays_div_le_speeds omega L K h0 ht).2
    · exact hspeed0
  let m : ℝ := ⨆ t, F t
  have hT : Tendsto F atTop (𝓝 m) := tendsto_atTop_ciSup hmono hbdd
  have hev : ∀ᶠ t : ℝ in atTop, F t = D t / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [F, if_pos ht]
  have hT' : Tendsto (fun t => D t / t) atTop (𝓝 m) := hT.congr' hev
  have hle (t : ℝ) (ht : 0 < t) : D t / t ≤ m := by
    have h := le_ciSup hbdd t
    simpa only [F, if_pos ht] using h
  exact ⟨m, (hF0 1).trans (le_ciSup hbdd 1), hT', hle,
    (EReal.tendsto_coe.mpr hT').limUnder_eq⟩

/-- The actual defining radial Darvas distance obeys all metric laws for genuine finite-energy rays with any fixed common actual finite-energy initial slice. -/
theorem rayD1_isMetric (omega : KahlerBackground n M) (p : M → EReal) :
    (∀ L K : ModelFiniteEnergyGeodesicRay θ φ hφ,
      L.rawCurve 0 = p → K.rawCurve 0 = p →
      0 ≤ rayD1 θ φ hφ L.rawCurve K.rawCurve ∧
        rayD1 θ φ hφ L.rawCurve K.rawCurve < ⊤) ∧
    (∀ L : ModelFiniteEnergyGeodesicRay θ φ hφ,
      rayD1 θ φ hφ L.rawCurve L.rawCurve = 0) ∧
    (∀ L K : ModelFiniteEnergyGeodesicRay θ φ hφ,
      rayD1 θ φ hφ L.rawCurve K.rawCurve = rayD1 θ φ hφ K.rawCurve L.rawCurve) ∧
    (∀ L K H : ModelFiniteEnergyGeodesicRay θ φ hφ,
      L.rawCurve 0 = p → K.rawCurve 0 = p → H.rawCurve 0 = p →
      rayD1 θ φ hφ L.rawCurve H.rawCurve ≤
        rayD1 θ φ hφ L.rawCurve K.rawCurve + rayD1 θ φ hφ K.rawCurve H.rawCurve) ∧
    (∀ L K : ModelFiniteEnergyGeodesicRay θ φ hφ,
      L.rawCurve 0 = p → K.rawCurve 0 = p →
      rayD1 θ φ hφ L.rawCurve K.rawCurve = 0 →
      ∀ t : ℝ, 0 ≤ t → L.rawCurve t = K.rawCurve t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro L K hL hK
    obtain ⟨m, hm, _, _, he⟩ := exists_tendsto_rayD1 omega L K (hL.trans hK.symm)
    rw [he]
    exact ⟨EReal.coe_nonneg.mpr hm, EReal.coe_lt_top m⟩
  · intro L
    have hT : Tendsto (fun t : ℝ => ((relativeD1 θ φ hφ
        (L.rawCurve t) (L.rawCurve t) / t : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : EReal)) atTop (𝓝 0)) using 1
      funext t
      rw [relativeD1_self (L.finiteEnergy_rawCurve t).1.plurisubharmonic, zero_div, EReal.coe_zero]
    exact hT.limUnder_eq
  · intro L K
    unfold rayD1
    congr 1
    funext t
    rw [relativeD1_comm]
  · intro L K H hL hK hH
    obtain ⟨a, _, hTa, _, hea⟩ := exists_tendsto_rayD1 omega L H (hL.trans hH.symm)
    obtain ⟨b, _, hTb, _, heb⟩ := exists_tendsto_rayD1 omega L K (hL.trans hK.symm)
    obtain ⟨c, _, hTc, _, hec⟩ := exists_tendsto_rayD1 omega K H (hK.trans hH.symm)
    rw [hea, heb, hec, ← EReal.coe_add, EReal.coe_le_coe_iff]
    refine le_of_tendsto_of_tendsto hTa (hTb.add hTc) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← add_div]
    exact div_le_div_of_nonneg_right (SingularModelDarvasContraction.relativeD1_triangle
      omega (L.finiteEnergy_rawCurve t) (H.finiteEnergy_rawCurve t)
        (K.finiteEnergy_rawCurve t)) ht.le
  · intro L K hL hK hzero t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hL, hK]
    obtain ⟨m, _, _, hle, he⟩ := exists_tendsto_rayD1 omega L K (hL.trans hK.symm)
    rw [he, EReal.coe_eq_zero] at hzero
    have hD := hle t h
    rw [hzero, div_le_iff₀ h, zero_mul] at hD
    exact SingularModelDarvasSeparation.eq_of_relativeD1_eq_zero_of_preceq omega
      (L.finiteEnergy_rawCurve t) (K.finiteEnergy_rawCurve t)
      (le_antisymm hD (SingularModelDarvasBasic.relativeD1_nonneg omega
        (L.finiteEnergy_rawCurve t) (K.finiteEnergy_rawCurve t)))

/-- Actual native rays based at the given genuine finite-energy potential. -/
abbrev BasedModelFiniteEnergyGeodesicRay (θ : ClosedRealOneOneForm n M)
    (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (p : ModelFiniteEnergyPotential θ φ hφ) :=
  {L : ModelFiniteEnergyGeodesicRay θ φ hφ // L.toFun 0 = p}

omit [BorelSpace M] [ConnectedSpace M] in
private theorem initial_eq {p : ModelFiniteEnergyPotential θ φ hφ}
    (L : BasedModelFiniteEnergyGeodesicRay θ φ hφ p) : L.val.rawCurve 0 = p.val := by
  calc
    L.val.rawCurve 0 = (L.val.toFun 0).val := L.val.rawCurve_coe 0
    _ = p.val := congrArg Subtype.val L.property

omit [BorelSpace M] [ConnectedSpace M] in
private theorem ray_ext {L K : ModelFiniteEnergyGeodesicRay θ φ hφ}
    (h : ∀ t : ℝ, 0 ≤ t → L.rawCurve t = K.rawCurve t) : L = K := by
  have hfun : L.toFun = K.toFun := by
    funext t
    apply Subtype.ext
    have ht := h t t.property
    simpa only [L.rawCurve_coe t, K.rawCurve_coe t] using ht
  cases L
  cases K
  cases hfun
  rfl

/-- The actual finite real radial distance defines a genuine native MetricSpace on the actual based E1 rays, with its ordinary distance-generated uniformity and topology. -/
@[instance_reducible]
def basedRayMetricSpace (omega : KahlerBackground n M)
    (p : ModelFiniteEnergyPotential θ φ hφ) :
    MetricSpace (BasedModelFiniteEnergyGeodesicRay θ φ hφ p) where
  dist L K := (rayD1 θ φ hφ L.val.rawCurve K.val.rawCurve).toReal
  dist_self L := by rw [(rayD1_isMetric omega p.val).2.1 L.val, EReal.toReal_zero]
  dist_comm L K := congrArg EReal.toReal ((rayD1_isMetric omega p.val).2.2.1 L.val K.val)
  dist_triangle L K H := by
    obtain ⟨a, _, _, _, hea⟩ := exists_tendsto_rayD1 omega L.val H.val
      ((initial_eq L).trans (initial_eq H).symm)
    obtain ⟨b, _, _, _, heb⟩ := exists_tendsto_rayD1 omega L.val K.val
      ((initial_eq L).trans (initial_eq K).symm)
    obtain ⟨c, _, _, _, hec⟩ := exists_tendsto_rayD1 omega K.val H.val
      ((initial_eq K).trans (initial_eq H).symm)
    have h := (rayD1_isMetric omega p.val).2.2.2.1 L.val K.val H.val
      (initial_eq L) (initial_eq K) (initial_eq H)
    rw [hea, heb, hec, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    simpa only [hea, heb, hec, EReal.toReal_coe] using h
  eq_of_dist_eq_zero {L K} h := by
    obtain ⟨m, _, _, _, he⟩ := exists_tendsto_rayD1 omega L.val K.val
      ((initial_eq L).trans (initial_eq K).symm)
    have hm : m = 0 := by simpa only [he, EReal.toReal_coe] using h
    have hz : rayD1 θ φ hφ L.val.rawCurve K.val.rawCurve = 0 := by
      simpa only [hm, EReal.coe_zero] using he
    apply Subtype.ext
    exact ray_ext ((rayD1_isMetric omega p.val).2.2.2.2 L.val K.val (initial_eq L) (initial_eq K) hz)

/-- Native based-ray distance is transparently the finite real value of the actual defining radial Darvas distance. -/
theorem dist_eq_rayD1_toReal (omega : KahlerBackground n M)
    (p : ModelFiniteEnergyPotential θ φ hφ)
    (L K : BasedModelFiniteEnergyGeodesicRay θ φ hφ p) :
    letI := basedRayMetricSpace omega p
    dist L K = (rayD1 θ φ hφ L.val.rawCurve K.val.rawCurve).toReal := rfl

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayDistance
