import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStages

set_option autoImplicit false

/-! # Genuine order and restriction of terminal-maximum join stages -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStageOrder

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularBoundedRayJoinStages

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem closedSlice_mono {θ : SmoothRealForm n M 2}
    {u₀ u₁ v₀ v₁ : M → EReal} (h0 : u₀ ≤ v₀) (h1 : u₁ ≤ v₁)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ s ≤
      closedSubgeodesicSlice (finiteGeodesic θ v₀ v₁) v₀ v₁ s := by
  by_cases hzero : s = 0
  · simpa only [hzero, closedSubgeodesicSlice_zero] using h0
  by_cases hone : s = 1
  · simpa only [hone, closedSubgeodesicSlice_one] using h1
  have hI : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hzero), lt_of_le_of_ne hs.2 hone⟩
  simp only [closedSubgeodesicSlice_eq_curve hI]
  exact finiteGeodesic_mono h0 h1 s

variable [MeasurableSpace M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}
  {ℓ ℓ' L : ℝ → M → EReal}

private theorem source_closed_geometry (hL : IsRayFromModel θ φ hφ L)
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) T) :
    L s = closedSubgeodesicSlice (finiteGeodesic θ.val φ (L T)) φ (L T) (s / T) := by
  by_cases hzero : s = 0
  · rw [hzero, zero_div, closedSubgeodesicSlice_zero, hL.2]
  by_cases hend : s = T
  · rw [hend, div_self hT.ne', closedSubgeodesicSlice_one]
  have hI : s / T ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (lt_of_le_of_ne hs.1 (Ne.symm hzero)) hT,
      (div_lt_one hT).mpr (lt_of_le_of_ne hs.2 hend)⟩
  rw [closedSubgeodesicSlice_eq_curve hI]
  have h := hL.1.2 0 T le_rfl hT (s / T) hI
  rw [show (0 : ℝ) + (s / T) * (T - 0) = s by
    rw [sub_zero, zero_add, div_mul_cancel₀ _ hT.ne'], hL.2] at h
  exact h

/-- Actual ray geometry and actual terminal maximum monotonicity put both source slices below the actual finite stage. -/
theorem max_le_joinStage (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) T) :
    (fun x => max (ℓ s x) (ℓ' s x)) ≤ joinStage θ φ ℓ ℓ' T s := by
  have hr : s / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩
  have hleft : ℓ s ≤ joinStage θ φ ℓ ℓ' T s := by
    rw [source_closed_geometry ⟨hℓ.1.1, hℓ.2⟩ hT hs]
    exact closedSlice_mono le_rfl (fun _ => le_max_left _ _) hr
  have hright : ℓ' s ≤ joinStage θ φ ℓ ℓ' T s := by
    rw [source_closed_geometry ⟨hℓ'.1.1, hℓ'.2⟩ hT hs]
    exact closedSlice_mono le_rfl (fun _ => le_max_right _ _) hr
  exact fun x => max_le (hleft x) (hright x)

/-- A genuine source upper ray needs only the natural two terminal inequalities to dominate the actual closed finite stage. -/
theorem joinStage_le_upperRay (hL : IsRayFromModel θ φ hφ L)
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) T)
    (hle : ℓ T ≤ L T) (hle' : ℓ' T ≤ L T) :
    joinStage θ φ ℓ ℓ' T s ≤ L s := by
  rw [source_closed_geometry hL hT hs]
  exact closedSlice_mono le_rfl (fun x => max_le (hle x) (hle' x))
    ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩

variable [BorelSpace M] [ConnectedSpace M]

/-- The larger actual stage has its genuine Perron restriction, produced internally from actual finite-type endpoints, full-mass joint PSH and the proved Perron gluing theorem. -/
theorem finiteGeodesic_joinStage_restriction (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T S s : ℝ} (hT : 0 < T) (hTS : T ≤ S) (hs : s ∈ Ioo (0 : ℝ) T) :
    finiteGeodesic θ.val φ (joinStage θ φ ℓ ℓ' S T) (s / T) =
      joinStage θ φ ℓ ℓ' S s := by
  have hS : 0 < S := hT.trans_le hTS
  have h0 : RelativeEInfinity θ φ φ :=
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h1 : RelativeEInfinity θ φ (fun x => max (ℓ S x) (ℓ' S x)) :=
    relativeEInfinity_max (hℓ.1.2 S hS.le) (hℓ'.1.2 S hS.le)
  have hf0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h0
  have hf1 : RelativeFiniteEnergyPreceq θ φ (fun x => max (ℓ S x) (ℓ' S x)) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h1
  have hb : T / S ≤ 1 := (div_le_one hS).mpr hTS
  have hq : s / S ∈ Ioo (0 : ℝ) (T / S) :=
    ⟨div_pos hs.1 hS, (div_lt_div_iff_of_pos_right hS).mpr hs.2⟩
  have h := SingularModelGeodesicRestriction.finiteGeodesic_closed_interval_restriction_eq
    omega hf0.1 hf1.1 (a := 0) (b := T / S) (t := s / S)
      le_rfl hb (div_pos hT hS) hq
  simp only [sub_zero, closedSubgeodesicSlice_zero] at h
  rw [show (s / S) / (T / S) = s / T by
    field_simp] at h
  have hI : s / S ∈ Ioo (0 : ℝ) 1 := ⟨hq.1, hq.2.trans_le hb⟩
  simpa only [joinStage, closedSubgeodesicSlice_eq_curve hI] using h

/-- The actual fixed-time terminal-maximum stages increase with terminal time by the internally proved larger-stage Perron restriction. -/
theorem joinStage_mono_terminalTime (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T S s : ℝ} (hT : 0 < T) (hTS : T ≤ S) (hs : s ∈ Icc (0 : ℝ) T) :
    joinStage θ φ ℓ ℓ' T s ≤ joinStage θ φ ℓ ℓ' S s := by
  have hS : 0 < S := hT.trans_le hTS
  by_cases hzero : s = 0
  · simp only [hzero, joinStage_zero, le_refl]
  have hmax := max_le_joinStage hℓ hℓ' hS ⟨hT.le, hTS⟩
  by_cases hend : s = T
  · rw [hend, joinStage_terminal θ φ ℓ ℓ' hT]
    exact hmax
  have hI : s ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hzero), lt_of_le_of_ne hs.2 hend⟩
  have hr : s / T ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hI.1 hT, (div_lt_one hT).mpr hI.2⟩
  rw [joinStage, closedSubgeodesicSlice_eq_curve hr,
    ← finiteGeodesic_joinStage_restriction omega hℓ hℓ' hT hTS hI]
  exact finiteGeodesic_mono le_rfl hmax (s / T)

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStageOrder
