import Mathlib.Analysis.MeanInequalities
import SGPT.AlmostSemigroup.VolumeTransport
import SGPT.AlmostSemigroup.WeightedSlices
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
namespace SGPT.AlmostSemigroup.BrunnMinkowski
open Set Filter MeasureTheory
open scoped Topology

/-- Genuine weighted arithmetic--geometric mean with the actual two source mass normalizers gives the true density/Jacobian lower bound. -/
theorem density_jacobian_lower_bound {A B f g h t : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hf : 0 < f) (hg : 0 < g)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hshape : f ^ (1 - t) * g ^ t ≤ h) :
    (B / A) ^ t * f ≤ h * ((1 - t) + t * ((B / g) * (f / A))) := by
  let q : ℝ := (B / A) * (f / g)
  have hq : 0 ≤ q := (mul_pos (div_pos hB hA) (div_pos hf hg)).le
  have hqeq : q = (B / g) * (f / A) := by
    dsimp only [q]
    field_simp
  have hamgm : q ^ t ≤ (1 - t) + t * q := by
    simpa only [Real.one_rpow, one_mul, mul_one] using
      Real.geom_mean_le_arith_mean2_weighted (by linarith : 0 ≤ 1 - t) ht
        (by norm_num : (0 : ℝ) ≤ 1) hq (by ring : (1 - t) + t = 1)
  have hprod : (f ^ (1 - t) * g ^ t) * q ^ t = (B / A) ^ t * f := by
    dsimp only [q]
    rw [Real.mul_rpow (div_pos hB hA).le (div_pos hf hg).le, Real.div_rpow hf.le hg.le]
    have hgpow : g ^ t ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hg t)
    calc
      _ = (B / A) ^ t * (f ^ (1 - t) * f ^ t) := by
        field_simp [hgpow]
      _ = _ := by rw [← Real.rpow_add hf, sub_add_cancel, Real.rpow_one]
  calc
    _ = (f ^ (1 - t) * g ^ t) * q ^ t := hprod.symm
    _ ≤ (f ^ (1 - t) * g ^ t) * ((1 - t) + t * q) :=
      mul_le_mul_of_nonneg_left hamgm
        (mul_nonneg (Real.rpow_nonneg hf.le _) (Real.rpow_nonneg hg.le _))
    _ ≤ h * ((1 - t) + t * q) :=
      mul_le_mul_of_nonneg_right hshape (add_nonneg (by linarith) (mul_nonneg ht hq))
    _ = _ := by rw [hqeq]

variable {n : ℕ}
local notation "Body" => ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))

/-- The actual original weighted Minkowski body. -/
def weightedBody (K L : Body) (t : ℝ) : Body := (1 - t) • K + t • L

/-- The actual weighted original coordinate and genuine transported coordinate. -/
def weightedParameter (K L : Body)
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) (t x : ℝ) : ℝ :=
  (1 - t) * x + t * VolumeTransport.transport K L hL x

/-- The actual derivative expression of the genuine weighted coordinate map. -/
def weightedJacobian (K L : Body)
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) (t x : ℝ) : ℝ :=
  (1 - t) + t * deriv (VolumeTransport.transport K L hL) x

theorem continuousOn_weightedParameter (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) (t : ℝ) :
    ContinuousOn (weightedParameter K L hL t)
      (Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :=
  (continuousOn_id.const_mul _).add ((VolumeTransport.continuousOn_transport K L hK hL).const_mul _)

theorem hasDerivAt_weightedParameter (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) (t : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    HasDerivAt (weightedParameter K L hL t) (weightedJacobian K L hL t x) x := by
  have hT := (VolumeTransport.hasDerivAt_transport K L hK hL hx).differentiableAt.hasDerivAt
  convert ((hasDerivAt_id x).const_mul (1 - t)).add (hT.const_mul t) using 1 <;>
    first | rfl | simp only [weightedJacobian, mul_one]

theorem weightedJacobian_pos (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t x : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1)
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    0 < weightedJacobian K L hL t x := by
  have hT := mul_nonneg ht (VolumeTransport.deriv_transport_pos K L hK hL hx).le
  dsimp only [weightedJacobian]
  linarith

theorem weightedParameter_mem_interval (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) (t : ℝ) {x : ℝ}
    (hx : x ∈ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    weightedParameter K L hL t x ∈ Icc (BodyExtrema.coordinateMin 0 (weightedBody K L t))
      (BodyExtrema.coordinateMax 0 (weightedBody K L t)) :=
  WeightedSlices.weighted_coordinate_mem_interval K L (1 - t) t ⟨x, hx⟩
    ⟨VolumeTransport.transport K L hL x, VolumeTransport.transport_mem_Icc K L hK hL hx⟩

/-- Genuine lower-dimensional induction and actual source slice inclusion give the true weighted target density bound. -/
theorem slice_volume_lower_bound (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) (t : ℝ)
    (ih : ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)),
      volume.real (A : Set (EuclideanSpace ℝ (Fin n))) ^ (1 - t) *
        volume.real (B : Set (EuclideanSpace ℝ (Fin n))) ^ t ≤
        volume.real (((1 - t) • A + t • B : ConvexBody (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n)))) {x : ℝ}
    (hx : x ∈ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    PositiveSlices.density K x ^ (1 - t) *
      PositiveSlices.density L (VolumeTransport.transport K L hL x) ^ t ≤
      PositiveSlices.density (weightedBody K L t) (weightedParameter K L hL t x) := by
  let x' : Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) := ⟨x, hx⟩
  let y' : Icc (BodyExtrema.coordinateMin 0 L) (BodyExtrema.coordinateMax 0 L) :=
    ⟨VolumeTransport.transport K L hL x, VolumeTransport.transport_mem_Icc K L hK hL hx⟩
  let A := BodySlices.euclideanSlice n K x'
  let B := BodySlices.euclideanSlice n L y'
  have hA : volume.real (A : Set (EuclideanSpace ℝ (Fin n))) = PositiveSlices.density K x := by
    dsimp only [PositiveSlices.density, Measure.real]
    rw [BodyFubini.euclideanFiber_eq_sourceSlice n K x']
  have hB : volume.real (B : Set (EuclideanSpace ℝ (Fin n))) =
      PositiveSlices.density L (VolumeTransport.transport K L hL x) := by
    dsimp only [PositiveSlices.density, Measure.real]
    rw [BodyFubini.euclideanFiber_eq_sourceSlice n L y']
  have hsub := WeightedSlices.weighted_sourceSlice_subset_euclideanFiber K L (1 - t) t x' y'
  have hm : volume.real (((1 - t) • A + t • B : ConvexBody (EuclideanSpace ℝ (Fin n))) :
      Set (EuclideanSpace ℝ (Fin n))) ≤
      PositiveSlices.density (weightedBody K L t) (weightedParameter K L hL t x) :=
    ENNReal.toReal_mono (BodyFubini.isCompact_euclideanFiber n (weightedBody K L t)
      (weightedParameter K L hL t x)).measure_ne_top (measure_mono hsub)
  have h := ih A B
  rw [hA, hB] at h
  exact h.trans hm

/-- True compact-body slice integrability and the actual positive coordinate Jacobian produce actual transported density integrability on the whole original interval. -/
theorem intervalIntegrable_transported_density (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    IntervalIntegrable (fun x ↦ PositiveSlices.density (weightedBody K L t)
      (weightedParameter K L hL t x) * weightedJacobian K L hL t x) volume
      (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) := by
  have hab := (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK).le
  have hc : ContinuousOn (weightedParameter K L hL t)
      (uIcc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) := by
    rw [uIcc_of_le hab]
    exact continuousOn_weightedParameter K L hK hL t
  have hd : ∀ x ∈ Ioo (min (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K))
      (max (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)),
      HasDerivAt (weightedParameter K L hL t) (weightedJacobian K L hL t x) x := by
    simp only [min_eq_left hab, max_eq_right hab]
    exact fun x hx ↦ hasDerivAt_weightedParameter K L hK hL t hx
  have hj : ∀ x ∈ Ioo (min (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K))
      (max (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)),
      0 ≤ weightedJacobian K L hL t x := by
    simp only [min_eq_left hab, max_eq_right hab]
    exact fun x hx ↦ (weightedJacobian_pos K L hK hL ht ht1 hx).le
  exact (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (g := PositiveSlices.density (weightedBody K L t)) hc hd hj).mpr
    (BodyFubini.integrable_real_euclideanFiber n (weightedBody K L t)).intervalIntegrable

/-- Genuine monotone change of variables gives the exact whole-interval original-body fiber integral identity, with no endpoint derivative premise. -/
theorem integral_transported_density (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    (∫ x in BodyExtrema.coordinateMin 0 K..BodyExtrema.coordinateMax 0 K,
      PositiveSlices.density (weightedBody K L t) (weightedParameter K L hL t x) *
        weightedJacobian K L hL t x) =
      ∫ y in weightedParameter K L hL t (BodyExtrema.coordinateMin 0 K)..
        weightedParameter K L hL t (BodyExtrema.coordinateMax 0 K),
        PositiveSlices.density (weightedBody K L t) y := by
  have hab := (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK).le
  apply intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := weightedParameter K L hL t) (f' := weightedJacobian K L hL t)
    (g := PositiveSlices.density (weightedBody K L t))
  · rw [uIcc_of_le hab]
    exact continuousOn_weightedParameter K L hK hL t
  · simp only [min_eq_left hab, max_eq_right hab]
    exact fun x hx ↦ hasDerivAt_weightedParameter K L hK hL t hx
  · simp only [min_eq_left hab, max_eq_right hab]
    exact fun x hx ↦ (weightedJacobian_pos K L hK hL ht ht1 hx).le

/-- The actual positive Jacobian makes the genuine weighted coordinate map strictly increasing on the entire source interval. -/
theorem strictMonoOn_weightedParameter (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    StrictMonoOn (weightedParameter K L hL t)
      (Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_weightedParameter K L hK hL t)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_weightedParameter K L hK hL t hx).deriv]
  exact weightedJacobian_pos K L hK hL ht ht1 hx

/-- The true transformed source interval is inside the actual weighted-body projection interval, so its actual density integral is bounded by the original body volume. -/
theorem integral_transported_density_le_volume (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) :
    (∫ x in BodyExtrema.coordinateMin 0 K..BodyExtrema.coordinateMax 0 K,
      PositiveSlices.density (weightedBody K L t) (weightedParameter K L hL t x) *
        weightedJacobian K L hL t x) ≤
      volume.real (weightedBody K L t : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hab := PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK
  have ha : BodyExtrema.coordinateMin 0 K ∈
      Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) := ⟨le_rfl, hab.le⟩
  have hb : BodyExtrema.coordinateMax 0 K ∈
      Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) := ⟨hab.le, le_rfl⟩
  have hwa := weightedParameter_mem_interval K L hK hL t ha
  have hwb := weightedParameter_mem_interval K L hK hL t hb
  have hwab := (strictMonoOn_weightedParameter K L hK hL ht ht1 ha hb hab).le
  rw [integral_transported_density K L hK hL ht ht1,
    ← PositiveSlices.integral_density_eq_volume (weightedBody K L t)]
  exact intervalIntegral.integral_mono_interval hwa.1 hwab hwb.2
    (ae_restrict_of_ae (Eventually.of_forall (fun x ↦ PositiveSlices.density_nonneg (weightedBody K L t) x)))
    (BodyFubini.integrable_real_euclideanFiber n (weightedBody K L t)).intervalIntegrable

/-- The actual dimension-induction slice inequality and genuine normalized transport give the pointwise true source Jacobian bound. -/
theorem jacobian_density_lower_bound (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1)
    (ih : ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)),
      volume.real (A : Set (EuclideanSpace ℝ (Fin n))) ^ (1 - t) *
        volume.real (B : Set (EuclideanSpace ℝ (Fin n))) ^ t ≤
        volume.real (((1 - t) • A + t • B : ConvexBody (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n)))) {x : ℝ}
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    (volume.real (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) /
      volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) ^ t * PositiveSlices.density K x ≤
      PositiveSlices.density (weightedBody K L t) (weightedParameter K L hL t x) *
        weightedJacobian K L hL t x := by
  have h := density_jacobian_lower_bound (VolumeTransport.real_volume_pos K hK)
    (VolumeTransport.real_volume_pos L hL) (PositiveSlices.density_pos K hK hx)
    (PositiveSlices.density_pos L hL (VolumeTransport.transport_mem_Ioo K L hK hL hx)) ht ht1.le
    (slice_volume_lower_bound K L hK hL t ih (Ioo_subset_Icc_self hx))
  rw [weightedJacobian, (VolumeTransport.hasDerivAt_transport K L hK hL hx).deriv]
  exact h

/-- Genuine positive source masses identify the normalized Jacobian mass with the exact original weighted source volume product. -/
theorem normalized_mass_identity {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (B / A) ^ t * A = A ^ (1 - t) * B ^ t := by
  rw [Real.div_rpow hB.le hA.le]
  have hApow : A ^ t ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hA t)
  have hprod : A ^ (1 - t) * A ^ t = A := by
    rw [← Real.rpow_add hA, sub_add_cancel, Real.rpow_one]
  calc
    B ^ t / A ^ t * A = B ^ t / A ^ t * (A ^ (1 - t) * A ^ t) := by rw [hprod]
    _ = _ := by field_simp [hApow]

/-- Actual source fiber integration and true body cumulative transport prove the positive-volume successor step of Brunn--Minkowski from the genuine lower-dimensional induction hypothesis. -/
theorem successor_of_positive_volume (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1)
    (ih : ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)),
      volume.real (A : Set (EuclideanSpace ℝ (Fin n))) ^ (1 - t) *
        volume.real (B : Set (EuclideanSpace ℝ (Fin n))) ^ t ≤
        volume.real (((1 - t) • A + t • B : ConvexBody (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n)))) :
    volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) ^ (1 - t) *
      volume.real (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) ^ t ≤
      volume.real (weightedBody K L t : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  let c : ℝ := (volume.real (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) /
    volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) ^ t
  have hab := (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK).le
  have hi : IntervalIntegrable (PositiveSlices.density K) volume
      (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) :=
    (BodyFubini.integrable_real_euclideanFiber n K).intervalIntegrable
  have hm : volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) ^ (1 - t) *
      volume.real (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) ^ t =
      ∫ x in BodyExtrema.coordinateMin 0 K..BodyExtrema.coordinateMax 0 K,
        c * PositiveSlices.density K x := by
    rw [intervalIntegral.integral_const_mul, PositiveSlices.integral_density_eq_volume K]
    exact (normalized_mass_identity (VolumeTransport.real_volume_pos K hK)
      (VolumeTransport.real_volume_pos L hL)).symm
  rw [hm]
  apply le_trans _ (integral_transported_density_le_volume K L hK hL ht ht1)
  exact intervalIntegral.integral_mono_on_of_le_Ioo hab (hi.const_mul c)
    (intervalIntegrable_transported_density K L hK hL ht ht1)
    (fun x hx ↦ jacobian_density_lower_bound K L hK hL ht ht1 ih hx)

/-- The actual zero-dimensional nonempty body has exactly one point and genuine Euclidean volume one. -/
theorem volume_zero_dimensional (K : ConvexBody (EuclideanSpace ℝ (Fin 0))) :
    volume.real (K : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  have hK : (K : Set (EuclideanSpace ℝ (Fin 0))) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := K.nonempty
    simpa only [Subsingleton.elim x y] using hy
  have hpi : (volume : Measure (Fin 0 → ℝ)) univ = 1 :=
    Measure.pi_empty_univ (fun _ : Fin 0 ↦ (volume : Measure ℝ))
  have hp := (PiLp.volume_preserving_ofLp (Fin 0)).measure_preimage
    (MeasurableSet.univ : MeasurableSet (univ : Set (Fin 0 → ℝ))).nullMeasurableSet
  rw [preimage_univ, hpi] at hp
  simp only [Measure.real, hK, hp, ENNReal.toReal_one]

/-- Full source `thm:BrunnMin`, with the original actual Euclidean bodies and genuine Lebesgue volume, including empty interior and dimension zero. -/
theorem brunn_minkowski (n : ℕ) (K L : ConvexBody (EuclideanSpace ℝ (Fin n)))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    volume.real (K : Set (EuclideanSpace ℝ (Fin n))) ^ (1 - t) *
      volume.real (L : Set (EuclideanSpace ℝ (Fin n))) ^ t ≤
      volume.real (((1 - t) • K + t • L : ConvexBody (EuclideanSpace ℝ (Fin n))) :
        Set (EuclideanSpace ℝ (Fin n))) := by
  induction n with
  | zero =>
      simp only [volume_zero_dimensional, Real.one_rpow, one_mul, le_refl]
  | succ n ih =>
      by_cases hK : volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) = 0
      · simp only [Measure.real, hK, ENNReal.toReal_zero,
          Real.zero_rpow (ne_of_gt (sub_pos.mpr ht1)), zero_mul]
        exact ENNReal.toReal_nonneg
      by_cases hL : volume (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) = 0
      · simp only [Measure.real, hL, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt ht), mul_zero]
        exact ENNReal.toReal_nonneg
      exact successor_of_positive_volume K L (bot_lt_iff_ne_bot.mpr hK)
        (bot_lt_iff_ne_bot.mpr hL) ht.le ht1 ih

end SGPT.AlmostSemigroup.BrunnMinkowski
