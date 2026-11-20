import SGPT.Trace.TwistedL2MainStatement

/-!
# A measurable unit frame of a Hermitian line bundle

The Hilbert space `H₁ = L²(U, L; w dμ)` of sections of `L` is realized as an ordinary `L²` space
of complex functions on `X`: a section `s` corresponds to its coordinate `⟪ε x, s x⟫` along a
*measurable unit frame* `ε` (`unitFrame`), i.e. `s x = ⟪ε x, s x⟫ • ε x` and `‖s x‖ = |⟪ε x, s x⟫|`.

`ε x` is the normalized frame of the first trivialization, in a fixed countable family of
trivializations covering `X`, whose base set contains `x`.  Its coefficient in any atlas frame is
measurable on the base set (`measurable_indicator_unitCoeff`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-! ### Frame coefficients -/

/-- The trivialization at `y` as an atlas frame. -/
def atlasFrameAt (y : X) : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber y, inferInstance⟩

theorem mem_atlasFrameAt_baseSet (y : X) : y ∈ (atlasFrameAt L y).val.baseSet :=
  FiberBundle.mem_baseSet_trivializationAt' y

variable {L}

/-- Coefficients are linear on the base set. -/
theorem frameCoeff_smul_apply (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) (c : ℂ)
    (y : L.Fiber x) : (e.val ⟨x, c • y⟩).2 = c * (e.val ⟨x, y⟩).2 := by
  have := e.property
  change e.val.linearEquivAt ℂ x hx (c • y) = c * e.val.linearEquivAt ℂ x hx y
  rw [map_smul, smul_eq_mul]

theorem frameCoeff_add_apply (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet)
    (y y' : L.Fiber x) : (e.val ⟨x, y + y'⟩).2 = (e.val ⟨x, y⟩).2 + (e.val ⟨x, y'⟩).2 := by
  have := e.property
  change e.val.linearEquivAt ℂ x hx (y + y') =
    e.val.linearEquivAt ℂ x hx y + e.val.linearEquivAt ℂ x hx y'
  rw [map_add]

theorem frameCoeff_sub_apply (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet)
    (y y' : L.Fiber x) : (e.val ⟨x, y - y'⟩).2 = (e.val ⟨x, y⟩).2 - (e.val ⟨x, y'⟩).2 := by
  have := e.property
  change e.val.linearEquivAt ℂ x hx (y - y') =
    e.val.linearEquivAt ℂ x hx y - e.val.linearEquivAt ℂ x hx y'
  rw [map_sub]

theorem frameCoeff_zero_apply (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    (e.val ⟨x, (0 : L.Fiber x)⟩).2 = 0 := by
  have := e.property
  change e.val.linearEquivAt ℂ x hx 0 = 0
  rw [map_zero]

theorem frameCoeff_symm_one (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    (e.val ⟨x, e.val.symm x 1⟩).2 = 1 := by
  have h := e.val.apply_mk_symm hx (1 : ℂ)
  exact congrArg Prod.snd h

/-- Every vector of a fibre over the base set is its coefficient times the frame. -/
theorem eq_frameCoeff_smul (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) (y : L.Fiber x) :
    y = (e.val ⟨x, y⟩).2 • e.val.symm x 1 := by
  have := e.property
  have h1 : e.val.symm x ((e.val ⟨x, y⟩).2) = y := e.val.symm_apply_apply_mk hx y
  have h2 : ∀ c : ℂ, e.val.symm x c = c • e.val.symm x 1 := by
    intro c
    rw [← e.val.symmL_apply (R := ℂ) hx c, ← e.val.symmL_apply (R := ℂ) hx 1, ← map_smul,
      smul_eq_mul, mul_one]
  conv_lhs => rw [← h1]
  exact h2 _

theorem frame_ne_zero (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    e.val.symm x 1 ≠ 0 := by
  have := e.property
  exact norm_pos_iff.mp (frameNorm_pos L.Fiber e.val hx)

theorem frameNormSq_pos (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    0 < frameNormSq L e x := by
  have := e.property
  exact sq_pos_of_pos (frameNorm_pos L.Fiber e.val hx)

/-- `⟪c • e, c' • e⟫ = conj c · c' · |e|²`. -/
theorem inner_frame_smul (e : AtlasFrame L) (x : X) (c c' : ℂ) :
    ⟪c • e.val.symm x 1, c' • e.val.symm x 1⟫_ℂ = conj c * c' * (frameNormSq L e x : ℂ) := by
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, frameNormSq]
  simp only [Complex.ofReal_pow]
  rw [mul_assoc]
  rfl

/-- `⟪y, y'⟫ = conj y_e · y'_e · |e|²` over the base set. -/
theorem inner_eq_frameCoeff (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet)
    (y y' : L.Fiber x) :
    ⟪y, y'⟫_ℂ = conj (e.val ⟨x, y⟩).2 * (e.val ⟨x, y'⟩).2 * (frameNormSq L e x : ℂ) := by
  conv_lhs => rw [eq_frameCoeff_smul e hx y, eq_frameCoeff_smul e hx y']
  exact inner_frame_smul e x _ _

theorem norm_sq_eq_frameCoeff (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet)
    (y : L.Fiber x) : ‖y‖ ^ 2 = ‖(e.val ⟨x, y⟩).2‖ ^ 2 * frameNormSq L e x := by
  conv_lhs => rw [eq_frameCoeff_smul e hx y]
  rw [norm_smul, mul_pow, frameNormSq]

theorem continuousOn_frameCoeff_frame (e e' : AtlasFrame L) :
    ContinuousOn (fun x => (e.val ⟨x, e'.val.symm x 1⟩).2) (e.val.baseSet ∩ e'.val.baseSet) := by
  have h1 : ContinuousOn (fun x => (⟨x, e'.val.symm x 1⟩ : TotalSpace ℂ L.Fiber))
      e'.val.baseSet :=
    e'.val.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy => ⟨hy, Set.mem_univ _⟩)
  have h2 : ContinuousOn (fun x => e.val (⟨x, e'.val.symm x 1⟩ : TotalSpace ℂ L.Fiber))
      (e.val.baseSet ∩ e'.val.baseSet) := by
    refine e.val.continuousOn.comp (h1.mono inter_subset_right) ?_
    intro x hx
    exact (e.val.coe_mem_source).2 hx.1
  exact continuous_snd.comp_continuousOn h2

/-! ### The unit frame -/

variable (L)

theorem exists_frameSeq (hX : Nonempty X) :
    ∃ f : ℕ → X, ∀ x : X, ∃ k, x ∈ (atlasFrameAt L (f k)).val.baseSet := by
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : X => (atlasFrameAt L y).val.baseSet) (fun y => (atlasFrameAt L y).val.open_baseSet)
  have hcov : ∀ x : X, ∃ y ∈ T, x ∈ (atlasFrameAt L y).val.baseSet := by
    intro x
    have hx : x ∈ ⋃ y, (atlasFrameAt L y).val.baseSet :=
      mem_iUnion.2 ⟨x, mem_atlasFrameAt_baseSet L x⟩
    rw [← hT] at hx
    obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.1 hx
    exact ⟨y, hyT, hy⟩
  obtain ⟨x₀⟩ := hX
  have hTne : T.Nonempty := by
    obtain ⟨y, hy, -⟩ := hcov x₀
    exact ⟨y, hy⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  refine ⟨f, fun x => ?_⟩
  obtain ⟨y, hyT, hy⟩ := hcov x
  rw [hf] at hyT
  obtain ⟨k, rfl⟩ := hyT
  exact ⟨k, hy⟩

/-- A sequence of points whose trivializations cover `X`. -/
def frameSeq (hX : Nonempty X) : ℕ → X := Classical.choose (exists_frameSeq L hX)

theorem frameSeq_spec (hX : Nonempty X) (x : X) :
    ∃ k, x ∈ (atlasFrameAt L (frameSeq L hX k)).val.baseSet :=
  Classical.choose_spec (exists_frameSeq L hX) x

open Classical in
/-- The index of the first trivialization of the sequence containing `x`. -/
def frameIndex (x : X) : ℕ := Nat.find (frameSeq_spec L ⟨x⟩ x)

/-- The trivialization used by the unit frame at `x`. -/
def unitFrameTriv (x : X) : AtlasFrame L := atlasFrameAt L (frameSeq L ⟨x⟩ (frameIndex L x))

theorem mem_unitFrameTriv_baseSet (x : X) : x ∈ (unitFrameTriv L x).val.baseSet := by
  classical
  exact Nat.find_spec (frameSeq_spec L ⟨x⟩ x)

/-- The measurable unit frame `ε x = e(x)/|e(x)|`. -/
def unitFrame (x : X) : L.Fiber x :=
  ((‖(unitFrameTriv L x).val.symm x 1‖⁻¹ : ℝ) : ℂ) • (unitFrameTriv L x).val.symm x 1

theorem norm_unitFrame (x : X) : ‖unitFrame L x‖ = 1 := by
  have hne := frame_ne_zero (unitFrameTriv L x) (mem_unitFrameTriv_baseSet L x)
  rw [unitFrame, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (norm_pos_iff.2 hne)), inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]

theorem unitFrame_ne_zero (x : X) : unitFrame L x ≠ 0 := by
  intro h
  have := norm_unitFrame L x
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- Every vector of the fibre is its `ε`-coordinate times `ε`. -/
theorem eq_inner_unitFrame_smul (x : X) (y : L.Fiber x) :
    y = ⟪unitFrame L x, y⟫_ℂ • unitFrame L x := by
  have hx := mem_unitFrameTriv_baseSet L x
  have hε : ((unitFrameTriv L x).val ⟨x, unitFrame L x⟩).2 ≠ 0 := by
    intro h0
    apply unitFrame_ne_zero L x
    have h1 := eq_frameCoeff_smul (unitFrameTriv L x) hx (unitFrame L x)
    rw [h0, zero_smul] at h1
    exact h1
  have hy : y = (((unitFrameTriv L x).val ⟨x, y⟩).2 /
      ((unitFrameTriv L x).val ⟨x, unitFrame L x⟩).2) • unitFrame L x := by
    have h1 := eq_frameCoeff_smul (unitFrameTriv L x) hx (unitFrame L x)
    have h2 := eq_frameCoeff_smul (unitFrameTriv L x) hx y
    calc y = ((unitFrameTriv L x).val ⟨x, y⟩).2 • (unitFrameTriv L x).val.symm x 1 := h2
      _ = (((unitFrameTriv L x).val ⟨x, y⟩).2 /
          ((unitFrameTriv L x).val ⟨x, unitFrame L x⟩).2) •
          ((((unitFrameTriv L x).val ⟨x, unitFrame L x⟩).2) •
            (unitFrameTriv L x).val.symm x 1) := by
        rw [smul_smul, div_mul_cancel₀ _ hε]
      _ = _ := by rw [← h1]
  have hinner : ⟪unitFrame L x, y⟫_ℂ = ((unitFrameTriv L x).val ⟨x, y⟩).2 /
      ((unitFrameTriv L x).val ⟨x, unitFrame L x⟩).2 := by
    conv_lhs => rw [hy]
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_unitFrame]
    simp
  rw [hinner]
  exact hy

theorem norm_inner_unitFrame (x : X) (y : L.Fiber x) : ‖⟪unitFrame L x, y⟫_ℂ‖ = ‖y‖ := by
  conv_rhs => rw [eq_inner_unitFrame_smul L x y]
  rw [norm_smul, norm_unitFrame, mul_one]

theorem inner_unitFrame_smul (x : X) (c : ℂ) : ⟪unitFrame L x, c • unitFrame L x⟫_ℂ = c := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_unitFrame]
  simp

variable {L}

/-- The coefficient of the unit frame in an atlas frame. -/
def unitCoeff (e : AtlasFrame L) (x : X) : ℂ := (e.val ⟨x, unitFrame L x⟩).2

theorem norm_unitCoeff_mul (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    ‖unitCoeff e x‖ ^ 2 * frameNormSq L e x = 1 := by
  rw [unitCoeff, ← norm_sq_eq_frameCoeff e hx, norm_unitFrame, one_pow]

theorem unitCoeff_ne_zero (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    unitCoeff e x ≠ 0 := by
  intro h
  have := norm_unitCoeff_mul e hx
  rw [h, norm_zero] at this
  simp at this

/-- The `e`-coefficient of `f • ε`. -/
theorem frameCoeff_smul_unitFrame (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) (c : ℂ) :
    (e.val ⟨x, c • unitFrame L x⟩).2 = c * unitCoeff e x :=
  frameCoeff_smul_apply e hx c _

/-- `⟪ε, c • e⟫ = c · conj(ε_e) · |e|²`. -/
theorem inner_unitFrame_frame_smul (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) (c : ℂ) :
    ⟪unitFrame L x, c • e.val.symm x 1⟫_ℂ = c * conj (unitCoeff e x) * (frameNormSq L e x : ℂ) := by
  rw [inner_eq_frameCoeff e hx, frameCoeff_smul_apply e hx, frameCoeff_symm_one e hx, unitCoeff]
  ring

variable [MeasurableSpace X] [BorelSpace X]

open Classical in
theorem measurable_indicator_unitCoeff (e : AtlasFrame L) :
    Measurable (e.val.baseSet.indicator (unitCoeff e)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · intro t _
    have : (e.val.baseSet.indicator (unitCoeff e)) ⁻¹' t = ∅ :=
      Set.eq_empty_of_isEmpty _
    rw [this]
    exact MeasurableSet.empty
  -- the `k`-th normalized frame and its `e`-coefficient
  set E : ℕ → AtlasFrame L := fun k => atlasFrameAt L (frameSeq L hX k) with hE
  set F : ℕ → X → ℂ := fun k => (e.val.baseSet ∩ (E k).val.baseSet).indicator
    (fun x => ((‖(E k).val.symm x 1‖⁻¹ : ℝ) : ℂ) * (e.val ⟨x, (E k).val.symm x 1⟩).2) with hF
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    have hopen : IsOpen (e.val.baseSet ∩ (E k).val.baseSet) :=
      e.val.open_baseSet.inter (E k).val.open_baseSet
    have hcont : ContinuousOn
        (fun x => ((‖(E k).val.symm x 1‖⁻¹ : ℝ) : ℂ) * (e.val ⟨x, (E k).val.symm x 1⟩).2)
        (e.val.baseSet ∩ (E k).val.baseSet) := by
      have hn : ContinuousOn (fun x => ‖(E k).val.symm x 1‖) (E k).val.baseSet :=
        frameNorm_continuousOn L.Fiber (E k).val
      have hn' : ContinuousOn (fun x => ‖(E k).val.symm x 1‖⁻¹)
          (e.val.baseSet ∩ (E k).val.baseSet) :=
        (hn.mono inter_subset_right).inv₀ fun x hx => norm_ne_zero_iff.2 (frame_ne_zero _ hx.2)
      exact (Complex.continuous_ofReal.comp_continuousOn hn').mul
        (continuousOn_frameCoeff_frame e (E k))
    have := hcont.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const
      hopen.measurableSet
    convert this using 1
    ext x
    simp only [hF, Set.indicator, Set.piecewise]
    split_ifs <;> rfl
  have hp : ∀ k, MeasurableSet {x | x ∈ (E k).val.baseSet} :=
    fun k => (E k).val.open_baseSet.measurableSet
  have hm := Measurable.find hFm hp (frameSeq_spec L hX)
  convert hm using 1
  ext x
  by_cases hx : x ∈ e.val.baseSet
  · have hk : x ∈ (E (frameIndex L x)).val.baseSet := mem_unitFrameTriv_baseSet L x
    simp only [Set.indicator_of_mem hx]
    have hfi : Nat.find (frameSeq_spec L hX x) = frameIndex L x := rfl
    rw [hfi, hF]
    simp only [Set.indicator_of_mem (show x ∈ e.val.baseSet ∩ (E (frameIndex L x)).val.baseSet
      from ⟨hx, hk⟩)]
    rw [unitCoeff, unitFrame, frameCoeff_smul_apply e hx]
    rfl
  · rw [Set.indicator_of_notMem hx]
    have hfi : Nat.find (frameSeq_spec L hX x) = frameIndex L x := rfl
    rw [hfi, hF]
    simp only [Set.indicator_of_notMem (show x ∉ e.val.baseSet ∩ _ from fun h => hx h.1)]

end SGPT.Trace.TwistedL2
