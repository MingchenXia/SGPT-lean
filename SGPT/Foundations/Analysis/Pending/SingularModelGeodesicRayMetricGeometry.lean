import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicMetricGeometry
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRays

set_option autoImplicit false

/-!
# Actual distance geometry of singular-model finite-energy rays

Xia SGPT PDF0174 Proposition 4.3.5 and the finite-growth step of PDF0175
Theorem 4.3.4. The genuine ray record supplies only actual E1 slices and
actual completed Perron restriction. Actual segment constant speed gives
radial and full ray speed, and actual endpoint distance convexity gives
two-ray convexity and positive-time ratio monotonicity. The finite ratio
bound is an independent actual constant-speed adaptation of the source.
No bounded model, normalized slices, energy identity, or metric certificate
is a new hypothesis.
-/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayMetricGeometry

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelGeodesicRays SingularModelGeodesicMetricGeometry
  SingularModelGeodesicDarvasConvexity SingularModelDarvasMetricSpace

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

private theorem scaled_speed (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ)
    {b s t : ℝ} (hb : 0 < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    relativeD1 θ φ hφ (L.rawCurve (s * b)) (L.rawCurve (t * b)) =
      |s - t| * relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve b) := by
  let B : ℝ≥0 := ⟨b, hb.le⟩
  have hB : (0 : ℝ≥0) < B := hb
  have h := relativeD1_closedGeodesic_eq_abs_mul omega
    (L.finiteEnergy_rawCurve 0) (L.finiteEnergy_rawCurve b) hs ht
  have hLs := L.rawCurve_segment_eq 0 B hB ⟨s, hs⟩
  have hLt := L.rawCurve_segment_eq 0 B hB ⟨t, ht⟩
  change L.rawCurve ((1 - s) * 0 + s * b) =
    closedSubgeodesicSlice (finiteGeodesic θ.val (L.rawCurve 0) (L.rawCurve b))
      (L.rawCurve 0) (L.rawCurve b) s at hLs
  change L.rawCurve ((1 - t) * 0 + t * b) =
    closedSubgeodesicSlice (finiteGeodesic θ.val (L.rawCurve 0) (L.rawCurve b))
      (L.rawCurve 0) (L.rawCurve b) t at hLt
  simp only [mul_zero, zero_add] at hLs hLt
  rw [← hLs, ← hLt] at h
  simpa only [NNReal.coe_zero, mul_zero, zero_add] using h

/-- The actual completed segment geometry internally forces finite radial Darvas speed, for any genuine E1 initial slice. -/
theorem relativeD1_ray_zero_eq_mul (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ)
    {t : ℝ} (ht : 0 ≤ t) :
    relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve t) =
      t * relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) := by
  let b : ℝ := t + 1
  have hb : 0 < b := by dsimp [b]; linarith
  have hq1 : 1 / b ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hb).mpr (by dsimp [b]; linarith)⟩
  have hqt : t / b ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht hb.le, (div_le_one hb).mpr (by dsimp [b]; linarith)⟩
  have h1 := scaled_speed omega L hb (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hq1
  have h := scaled_speed omega L hb (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hqt
  simp only [zero_mul, zero_sub, abs_neg, abs_of_nonneg hq1.1, div_mul_cancel₀ 1 hb.ne'] at h1
  simp only [zero_mul, zero_sub, abs_neg, abs_of_nonneg hqt.1, div_mul_cancel₀ t hb.ne'] at h
  rw [h, h1]
  ring

/-- Genuine finite Perron restriction and the actual radial speed force exact Darvas speed for every pair of nonnegative ray times. -/
theorem relativeD1_ray_eq_abs_mul (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    relativeD1 θ φ hφ (L.rawCurve s) (L.rawCurve t) =
      |s - t| * relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) := by
  let b : ℝ := 1 + max s t
  have hb : 0 < b := by dsimp [b]; have := le_max_left s t; linarith
  have hsb : s ≤ b := by dsimp [b]; have := le_max_left s t; linarith
  have htb : t ≤ b := by dsimp [b]; have := le_max_right s t; linarith
  have hqs : s / b ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hs hb.le, (div_le_one hb).mpr hsb⟩
  have hqt : t / b ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht hb.le, (div_le_one hb).mpr htb⟩
  have h := scaled_speed omega L hb hqs hqt
  rw [div_mul_cancel₀ s hb.ne', div_mul_cancel₀ t hb.ne',
    relativeD1_ray_zero_eq_mul omega L hb.le, ← sub_div, abs_div, abs_of_pos hb] at h
  rw [h]
  field_simp

private theorem ray_chord (omega : KahlerBackground n M)
    (L K : ModelFiniteEnergyGeodesicRay θ φ hφ)
    {a b q : ℝ} (ha : 0 ≤ a) (hab : a < b) (hq : q ∈ Icc (0 : ℝ) 1) :
    relativeD1 θ φ hφ (L.rawCurve ((1 - q) * a + q * b))
      (K.rawCurve ((1 - q) * a + q * b)) ≤
      (1 - q) * relativeD1 θ φ hφ (L.rawCurve a) (K.rawCurve a) +
      q * relativeD1 θ φ hφ (L.rawCurve b) (K.rawCurve b) := by
  let A : ℝ≥0 := ⟨a, ha⟩
  let B : ℝ≥0 := ⟨b, ha.trans hab.le⟩
  have hAB : A < B := hab
  have h := relativeD1_closedGeodesics_le_endpoint_chord omega
    (L.finiteEnergy_rawCurve a) (L.finiteEnergy_rawCurve b)
    (K.finiteEnergy_rawCurve a) (K.finiteEnergy_rawCurve b) hq
  have hL := L.rawCurve_segment_eq A B hAB ⟨q, hq⟩
  have hK := K.rawCurve_segment_eq A B hAB ⟨q, hq⟩
  change L.rawCurve ((1 - q) * a + q * b) =
    closedSubgeodesicSlice (finiteGeodesic θ.val (L.rawCurve a) (L.rawCurve b))
      (L.rawCurve a) (L.rawCurve b) q at hL
  change K.rawCurve ((1 - q) * a + q * b) =
    closedSubgeodesicSlice (finiteGeodesic θ.val (K.rawCurve a) (K.rawCurve b))
      (K.rawCurve a) (K.rawCurve b) q at hK
  rw [← hL, ← hK] at h
  exact h

/-- The actual distance between two genuine singular-model E1 rays is convex on the complete nonnegative half-line; their initial slices may differ. -/
theorem convexOn_relativeD1_rays (omega : KahlerBackground n M)
    (L K : ModelFiniteEnergyGeodesicRay θ φ hφ) :
    ConvexOn ℝ (Ici 0) (fun t => relativeD1 θ φ hφ (L.rawCurve t) (K.rawCurve t)) := by
  refine ⟨convex_Ici 0, fun x hx y hy p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := ray_chord omega L K hx hxy ⟨hq, by linarith⟩
    rw [show (1 - q) * x + q * y = p * x + q * y by
      rw [show 1 - q = p by linarith], show 1 - q = p by linarith] at h
    exact h
  · subst y
    rw [← add_mul, hpq, one_mul, ← add_mul, hpq, one_mul]
  · have h := ray_chord omega L K hy hxy ⟨hp, by linarith⟩
    rw [show (1 - p) * y + p * x = p * x + q * y by
      rw [show 1 - p = q by linarith]; ring, show 1 - p = q by linarith] at h
    linarith

/-- A common genuine initial slice and actual convexity give monotonicity of the positive-time distance ratio. -/
theorem relativeD1_rays_div_mono (omega : KahlerBackground n M)
    (L K : ModelFiniteEnergyGeodesicRay θ φ hφ) (h0 : L.rawCurve 0 = K.rawCurve 0)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    relativeD1 θ φ hφ (L.rawCurve s) (K.rawCurve s) / s ≤
      relativeD1 θ φ hφ (L.rawCurve t) (K.rawCurve t) / t := by
  have hD0 : relativeD1 θ φ hφ (L.rawCurve 0) (K.rawCurve 0) = 0 := by
    rw [h0]
    exact relativeD1_self (K.finiteEnergy_rawCurve 0).1.plurisubharmonic
  have h := (convexOn_relativeD1_rays omega L K).secant_mono
    (a := 0) (x := s) (y := t) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs.le)
    (mem_Ici.mpr (hs.le.trans hst)) hs.ne' (hs.trans_le hst).ne' hst
  simpa only [hD0, sub_zero] using h

/-- Actual triangle and actual radial speed internally give a nonnegative, finite uniform bound for the positive-time distance ratio. -/
theorem relativeD1_rays_div_le_speeds (omega : KahlerBackground n M)
    (L K : ModelFiniteEnergyGeodesicRay θ φ hφ) (h0 : L.rawCurve 0 = K.rawCurve 0)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ relativeD1 θ φ hφ (L.rawCurve t) (K.rawCurve t) / t ∧
    relativeD1 θ φ hφ (L.rawCurve t) (K.rawCurve t) / t ≤
      relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) +
      relativeD1 θ φ hφ (K.rawCurve 0) (K.rawCurve 1) := by
  have hnonneg := SingularModelDarvasBasic.relativeD1_nonneg omega
    (L.finiteEnergy_rawCurve t) (K.finiteEnergy_rawCurve t)
  have h := SingularModelDarvasContraction.relativeD1_triangle omega
    (L.finiteEnergy_rawCurve t) (K.finiteEnergy_rawCurve t) (L.finiteEnergy_rawCurve 0)
  have hK0 : relativeD1 θ φ hφ (L.rawCurve 0) (K.rawCurve t) =
      t * relativeD1 θ φ hφ (K.rawCurve 0) (K.rawCurve 1) := by
    rw [h0, relativeD1_ray_zero_eq_mul omega K ht.le]
  rw [relativeD1_comm θ φ hφ (L.rawCurve t) (L.rawCurve 0),
    relativeD1_ray_zero_eq_mul omega L ht.le, hK0] at h
  exact ⟨div_nonneg hnonneg ht.le, (div_le_iff₀ ht).mpr (by nlinarith [h])⟩

/-- The actual native E1 ray is Lipschitz with its genuine finite time-one speed; its metric, uniformity and topology are explicitly native Darvas structures. -/
theorem lipschitzWith_native_ray (omega : KahlerBackground n M)
    (L : ModelFiniteEnergyGeodesicRay θ φ hφ) :
    letI := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
        (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
        (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    LipschitzWith ⟨relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1),
      SingularModelDarvasBasic.relativeD1_nonneg omega
        (L.finiteEnergy_rawCurve 0) (L.finiteEnergy_rawCurve 1)⟩ L.toFun := by
  let := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
    (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [SingularModelDarvasMetricSpace.dist_eq_relativeD1]
  change relativeD1 θ φ hφ (L.toFun a).val (L.toFun b).val ≤
    relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) * dist a b
  calc
    relativeD1 θ φ hφ (L.toFun a).val (L.toFun b).val =
        |(a : ℝ) - (b : ℝ)| * relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) := by
      rw [← L.rawCurve_coe a, ← L.rawCurve_coe b]
      exact relativeD1_ray_eq_abs_mul omega L a.property b.property
    _ ≤ relativeD1 θ φ hφ (L.rawCurve 0) (L.rawCurve 1) * dist a b := by
      rw [NNReal.dist_eq, mul_comm]

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayMetricGeometry
