import SGPT.AlmostSemigroup.PositiveSlices
import SGPT.AlmostSemigroup.CumulativeVolume

noncomputable section
namespace SGPT.AlmostSemigroup.VolumeTransport
open Set Filter MeasureTheory
open scoped Topology
variable {n : ℕ}
local notation "Body" => ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))

/-- The actual cumulative integral of the original Euclidean body's genuine slice volumes. -/
def cumulative (K : Body) (x : ℝ) : ℝ :=
  CumulativeVolume.cumulative (PositiveSlices.density K)
    (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) x

/-- The inverse cumulative function produced by the genuine original positive-volume body. -/
def inverse (K : Body) (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) : ℝ → ℝ :=
  CumulativeVolume.inverse (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx)

theorem image_cumulative (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    cumulative K '' Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) = Icc 0 1 :=
  CumulativeVolume.image_cumulative (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx)

theorem cumulative_mem_Icc (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    cumulative K x ∈ Icc (0 : ℝ) 1 := by
  rw [← image_cumulative K hK]
  exact mem_image_of_mem _ hx

theorem cumulative_left (K : Body) : cumulative K (BodyExtrema.coordinateMin 0 K) = 0 :=
  CumulativeVolume.cumulative_left

theorem cumulative_right (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    cumulative K (BodyExtrema.coordinateMax 0 K) = 1 :=
  CumulativeVolume.cumulative_right (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx)

theorem strictMonoOn_cumulative (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    StrictMonoOn (cumulative K) (Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :=
  CumulativeVolume.strictMonoOn_cumulative (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx)

theorem cumulative_mem_Ioo (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    cumulative K x ∈ Ioo (0 : ℝ) 1 := by
  have hm := strictMonoOn_cumulative K hK
  have hab := PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK
  constructor
  · simpa only [cumulative_left] using hm ⟨le_rfl, hab.le⟩ (Ioo_subset_Icc_self hx) hx.1
  · simpa only [cumulative_right K hK] using hm (Ioo_subset_Icc_self hx) ⟨hab.le, le_rfl⟩ hx.2

theorem continuousOn_cumulative (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ContinuousOn (cumulative K) (Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :=
  CumulativeVolume.continuousOn_cumulative (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK).le
    (PositiveSlices.continuousOn_density K)

theorem continuousOn_inverse (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ContinuousOn (inverse K hK) (Icc (0 : ℝ) 1) :=
  CumulativeVolume.continuousOn_inverse (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx)

theorem inverse_mem_Icc (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    inverse K hK y ∈ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) :=
  CumulativeVolume.inverse_mem (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx) hy

theorem inverse_mem_Ioo (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    inverse K hK y ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) :=
  CumulativeVolume.inverse_mem_Ioo (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx) hy

theorem cumulative_inverse (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : cumulative K (inverse K hK y) = y :=
  CumulativeVolume.cumulative_inverse (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx) hy

theorem inverse_cumulative (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    inverse K hK (cumulative K x) = x :=
  CumulativeVolume.inverse_cumulative (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx) hx

/-- The actual source body volume normalizes the genuine original cumulative derivative. -/
theorem hasDerivAt_cumulative (K : Body) {x : ℝ}
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    HasDerivAt (cumulative K)
      (PositiveSlices.density K x / volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) x := by
  have h := CumulativeVolume.hasDerivAt_cumulative (PositiveSlices.continuousOn_density K) hx
  rw [PositiveSlices.integral_density_eq_volume K] at h
  exact h

/-- The produced actual body inverse has its actual source-volume/density derivative. -/
theorem hasDerivAt_inverse (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (inverse K hK)
      (volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) / PositiveSlices.density K (inverse K hK y)) y := by
  have h := CumulativeVolume.hasDerivAt_inverse (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK)
    (PositiveSlices.continuousOn_density K) (fun x _ ↦ PositiveSlices.density_nonneg K x)
    (fun _ hx ↦ PositiveSlices.density_pos K hK hx) hy
  rw [PositiveSlices.integral_density_eq_volume K] at h
  exact h

/-- The actual cumulative transport between the two genuine positive-volume bodies. -/
def transport (K L : Body)
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) (x : ℝ) : ℝ :=
  inverse L hL (cumulative K x)

theorem transport_mem_Icc (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    transport K L hL x ∈ Icc (BodyExtrema.coordinateMin 0 L) (BodyExtrema.coordinateMax 0 L) :=
  inverse_mem_Icc L hL (cumulative_mem_Icc K hK hx)

theorem transport_mem_Ioo (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    transport K L hL x ∈ Ioo (BodyExtrema.coordinateMin 0 L) (BodyExtrema.coordinateMax 0 L) :=
  inverse_mem_Ioo L hL (cumulative_mem_Ioo K hK hx)

theorem continuousOn_transport (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ContinuousOn (transport K L hL)
      (Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :=
  (continuousOn_inverse L hL).comp' (continuousOn_cumulative K hK)
    (fun _ hx ↦ cumulative_mem_Icc K hK hx)

/-- Actual chain-rule derivative of the genuine body transport, with both real normalizers equal to the actual original body volumes. -/
theorem hasDerivAt_transport (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    HasDerivAt (transport K L hL)
      ((volume.real (L : Set (EuclideanSpace ℝ (Fin (n + 1)))) /
        PositiveSlices.density L (transport K L hL x)) *
      (PositiveSlices.density K x /
        volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))) x :=
  (hasDerivAt_inverse L hL (cumulative_mem_Ioo K hK hx)).comp x (hasDerivAt_cumulative K hx)

/-- Actual original cumulative mass is genuinely preserved by the constructed body transport. -/
theorem cumulative_transport (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    cumulative L (transport K L hL x) = cumulative K x :=
  cumulative_inverse L hL (cumulative_mem_Icc K hK hx)

/-- Actual strict cumulative increase proves true strict increase of the constructed transport. -/
theorem strictMonoOn_transport (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    StrictMonoOn (transport K L hL)
      (Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) := by
  intro x hx y hy hxy
  apply ((strictMonoOn_cumulative L hL).lt_iff_lt
    (transport_mem_Icc K L hK hL hx) (transport_mem_Icc K L hK hL hy)).mp
  rw [cumulative_transport K L hK hL hx, cumulative_transport K L hK hL hy]
  exact strictMonoOn_cumulative K hK hx hy hxy

/-- Compactness prevents the actual positive original volume from losing positivity under real conversion. -/
theorem real_volume_pos (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    0 < volume.real (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
  ENNReal.toReal_pos (ne_of_gt hK) K.isCompact.measure_ne_top

/-- Actual positive source volumes and interior slice densities give a strictly positive genuine transport derivative. -/
theorem deriv_transport_pos (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) {x : ℝ}
    (hx : x ∈ Ioo (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    0 < deriv (transport K L hL) x := by
  rw [(hasDerivAt_transport K L hK hL hx).deriv]
  exact mul_pos (div_pos (real_volume_pos L hL)
    (PositiveSlices.density_pos L hL (transport_mem_Ioo K L hK hL hx)))
    (div_pos (PositiveSlices.density_pos K hK hx) (real_volume_pos K hK))

theorem inverse_left (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    inverse K hK 0 = BodyExtrema.coordinateMin 0 K := by
  have h := inverse_cumulative K hK
    ⟨le_rfl, (PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK).le⟩
  simpa only [cumulative_left] using h

theorem inverse_right (K : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    inverse K hK 1 = BodyExtrema.coordinateMax 0 K := by
  have h := inverse_cumulative K hK
    ⟨(PositiveSlices.coordinateMin_lt_coordinateMax_of_volume_pos K hK).le, le_rfl⟩
  simpa only [cumulative_right K hK] using h

theorem transport_left (K L : Body)
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    transport K L hL (BodyExtrema.coordinateMin 0 K) = BodyExtrema.coordinateMin 0 L := by
  simp only [transport, cumulative_left, inverse_left L hL]

theorem transport_right (K L : Body)
    (hK : 0 < volume (K : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hL : 0 < volume (L : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    transport K L hL (BodyExtrema.coordinateMax 0 K) = BodyExtrema.coordinateMax 0 L := by
  simp only [transport, cumulative_right K hK, inverse_right L hL]

end SGPT.AlmostSemigroup.VolumeTransport
