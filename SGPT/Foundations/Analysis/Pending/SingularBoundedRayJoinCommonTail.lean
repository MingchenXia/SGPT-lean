import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinSlices

set_option autoImplicit false

/-! # Actual common terminal tails and closed join-stage restriction -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinCommonTail

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularBoundedRayJoinStages
  SingularBoundedRayJoinStageOrder SingularBoundedRayJoinSlices

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ ℓ' : ℝ → M → EReal}

/-- Actual stage monotonicity constructs the common-tail cofinal indices and proves equality of the genuine raw pointwise stage suprema. -/
theorem iSup_joinStage_common_tail_eq (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {s B : ℝ} (hs : 0 ≤ s) (hsB : s ≤ B) :
    (⨆ T : {T : ℝ // s < T}, joinStage θ φ ℓ ℓ' T.val s) =
      ⨆ T : {T : ℝ // B < T}, joinStage θ φ ℓ ℓ' T.val s := by
  apply le_antisymm
  · apply iSup_le
    intro T
    let S : {T : ℝ // B < T} :=
      ⟨max T.val (B + 1), lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
    have hT : 0 < T.val := lt_of_le_of_lt hs T.property
    have hTS : T.val ≤ S.val := le_max_left _ _
    have hst : s ∈ Icc (0 : ℝ) T.val := ⟨hs, T.property.le⟩
    exact (joinStage_mono_terminalTime omega hℓ hℓ' hT hTS hst).trans
      (le_iSup (fun R : {T : ℝ // B < T} => joinStage θ φ ℓ ℓ' R.val s) S)
  · apply iSup_le
    intro T
    exact le_iSup (fun R : {T : ℝ // s < T} => joinStage θ φ ℓ ℓ' R.val s)
      ⟨T.val, lt_of_le_of_lt hsB T.property⟩

/-- The actual defined regularized join slice is exactly the regularized stage supremum on any genuine common terminal tail above its nonnegative time. -/
theorem joinSlice_eq_regularized_common_tail (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {s B : ℝ} (hs : 0 ≤ s) (hsB : s ≤ B) :
    joinSlice θ φ ℓ ℓ' s =
      uscRegularization (⨆ T : {T : ℝ // B < T}, joinStage θ φ ℓ ℓ' T.val s) := by
  unfold joinSlice
  rw [max_eq_left hs]
  exact congrArg (fun f : M → EReal => uscRegularization f)
    (iSup_joinStage_common_tail_eq omega hℓ hℓ' hs hsB)

/-- Actual full-mass Perron gluing internally produces the entire closed finite-interval geometry of each genuine terminal-maximum stage. -/
theorem joinStage_closed_geometry (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T a b r : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hb : b ≤ T) (hab : a < b)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    joinStage θ φ ℓ ℓ' T ((1 - r) * a + r * b) =
      closedSubgeodesicSlice
        (finiteGeodesic θ.val (joinStage θ φ ℓ ℓ' T a) (joinStage θ φ ℓ ℓ' T b))
        (joinStage θ φ ℓ ℓ' T a) (joinStage θ φ ℓ ℓ' T b) r := by
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
  have h1 : RelativeEInfinity θ φ (fun x => max (ℓ T x) (ℓ' T x)) :=
    relativeEInfinity_max (hℓ.1.2 T hT.le) (hℓ'.1.2 T hT.le)
  have hf0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega h0
  have hf1 : RelativeFiniteEnergyPreceq θ φ (fun x => max (ℓ T x) (ℓ' T x)) hφ :=
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
  change joinStage θ φ ℓ ℓ' T q = _
  rw [joinStage, closedSubgeodesicSlice_eq_curve hI, closedSubgeodesicSlice_eq_curve hri]
  exact h.symm

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinCommonTail
