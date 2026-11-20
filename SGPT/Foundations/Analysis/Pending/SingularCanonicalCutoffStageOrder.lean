import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffStages

set_option autoImplicit false

/-! # Genuine cutoff-horizon monotonicity and closed stage geometry -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffStageOrder

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativePreceqClasses
  SingularModelNormalizedMixedCutoff SingularCanonicalCutoffStages

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u : M → EReal}

/-- The larger actual stage has its genuine Perron restriction, produced internally from actual finite-type endpoints, full-mass joint PSH and the proved Perron gluing theorem. -/
theorem finiteGeodesic_cutoffStage_restriction (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {T S s : ℝ} (hT : 0 < T) (hTS : T ≤ S) (hs : s ∈ Ioo (0 : ℝ) T) :
    finiteGeodesic θ.val φ (cutoffStage θ φ u S T) (s / T) =
      cutoffStage θ φ u S s := by
  have hS : 0 < S := hT.trans_le hTS
  have h0 : RelativeEInfinity θ φ φ :=
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h1 : RelativeEInfinity θ φ (realCutoff φ u S) :=
    relativeEInfinity_realCutoff hφ.plurisubharmonic hu
      (MoreSingularOn.of_le fun x _ => hup x) S
  have hf0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h0
  have hf1 : RelativeFiniteEnergyPreceq θ φ (realCutoff φ u S) hφ :=
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
  simpa only [cutoffStage, closedSubgeodesicSlice_eq_curve hI] using h

/-- The actual fixed-time cutoff stages increase with their horizon by the internally proved larger-stage Perron restriction. -/
theorem cutoffStage_mono_horizon (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {T S s : ℝ} (hT : 0 < T) (hTS : T ≤ S) (hs : s ∈ Icc (0 : ℝ) T) :
    cutoffStage θ φ u T s ≤ cutoffStage θ φ u S s := by
  have hS : 0 < S := hT.trans_le hTS
  by_cases hzero : s = 0
  · simp only [hzero, cutoffStage_zero, le_refl]
  have hmax := realCutoff_le_cutoffStage hφ.plurisubharmonic hu hup hS ⟨hT.le, hTS⟩
  by_cases hend : s = T
  · rw [hend, cutoffStage_terminal θ φ u hT]
    exact hmax
  have hI : s ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hzero), lt_of_le_of_ne hs.2 hend⟩
  have hr : s / T ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hI.1 hT, (div_lt_one hT).mpr hI.2⟩
  rw [cutoffStage, closedSubgeodesicSlice_eq_curve hr,
    ← finiteGeodesic_cutoffStage_restriction omega hφ hu hup hT hTS hI]
  exact finiteGeodesic_mono le_rfl hmax (s / T)


/-- Actual full-mass Perron gluing internally produces the entire closed finite-interval geometry of each genuine cutoff stage. -/
theorem cutoffStage_closed_geometry (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {T a b r : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hb : b ≤ T) (hab : a < b)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    cutoffStage θ φ u T ((1 - r) * a + r * b) =
      closedSubgeodesicSlice
        (finiteGeodesic θ.val (cutoffStage θ φ u T a) (cutoffStage θ φ u T b))
        (cutoffStage θ φ u T a) (cutoffStage θ φ u T b) r := by
  by_cases hzero : r = 0
  · rw [hzero]
    simp only [sub_zero, one_mul, zero_mul, add_zero, closedSubgeodesicSlice_zero]
  by_cases hone : r = 1
  · rw [hone]
    simp only [sub_self, zero_mul, one_mul, zero_add, closedSubgeodesicSlice_one]
  have hri : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hzero), lt_of_le_of_ne hr.2 hone⟩
  let q : ℝ := (1 - r) * a + r * b
  have hqa : a < q := by
    have hpos := mul_pos hri.1 (sub_pos.mpr hab)
    dsimp only [q]
    nlinarith
  have hqb : q < b := by
    have hpos := mul_pos (sub_pos.mpr hri.2) (sub_pos.mpr hab)
    dsimp only [q]
    nlinarith
  have h0 : RelativeEInfinity θ φ φ :=
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h1 : RelativeEInfinity θ φ (realCutoff φ u T) :=
    relativeEInfinity_realCutoff hφ.plurisubharmonic hu
      (MoreSingularOn.of_le fun x _ => hup x) T
  have hf0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h0
  have hf1 : RelativeFiniteEnergyPreceq θ φ (realCutoff φ u T) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h1
  have habr : a / T < b / T := (div_lt_div_iff_of_pos_right hT).mpr hab
  have hq : q / T ∈ Ioo (a / T) (b / T) :=
    ⟨(div_lt_div_iff_of_pos_right hT).mpr hqa,
      (div_lt_div_iff_of_pos_right hT).mpr hqb⟩
  have h := SingularModelGeodesicRestriction.finiteGeodesic_closed_interval_restriction_eq
    omega hf0.1 hf1.1 (a := a / T) (b := b / T) (t := q / T)
      (div_nonneg ha hT.le) ((div_le_one hT).mpr hb) habr hq
  have hratio : (q / T - a / T) / (b / T - a / T) = r := by
    apply (div_eq_iff (ne_of_gt (sub_pos.mpr habr))).mpr
    dsimp only [q]
    ring
  rw [hratio] at h
  have hI : q / T ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (lt_of_le_of_lt ha hqa) hT, (div_lt_one hT).mpr (hqb.trans_le hb)⟩
  change cutoffStage θ φ u T q = _
  rw [cutoffStage, closedSubgeodesicSlice_eq_curve hI, closedSubgeodesicSlice_eq_curve hri]
  exact h.symm


end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffStageOrder
