import SGPT.Trace.OTMarginFlat
import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import SGPT.Foundations.Analysis.Pending.ChartWeightedL2Transfer

/-!
# Flattening coordinates on the manifold and the normal pole

Blueprint `claude-ot3.tex`, nodes `claude-ot3:transfer`, `claude-ot3:pole-region`.

For a flattening datum `F` of a submanifold `W ⊆ X` (`SubmanifoldChartedSpace.FlatData`) the
coordinates `ζ = Φ ∘ e` identify a neighbourhood of a point of `W` with an open set of `ℂ^n` in
which `W` is the coordinate plane `{w = 0}`.

* `lintegral_finv_image_le`, `lintegral_le_finv_image`: integrals
  against a smooth positive volume `μ` and against Lebesgue measure in the coordinates `ζ` are
  comparable on compact sets.
* `exists_poleRegion`: if `Λ` is a function with `Λ = log |w|² + O(1)` near a point `p ∈ W` in the
  flattening coordinates of `p` (the local form of a normal pole, `IsSubmanifoldPole.localForm`),
  then on a compact neighbourhood `K` of `p`:
  `e^{-cΛ}` is integrable for `c < codim W` (`subcrit`), a holomorphic function vanishing on `W`
  is bounded by `C e^{Λ}` (`lip`), and a holomorphic function with `∫ |g|² e^{-codim(W) Λ} < ∞`
  vanishes on `W` (`crit`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

section FlatCoord

variable (F : FlatData n m X W)

/-- The flattening coordinates `ζ = Φ ∘ e`. -/
def fcoord (x : X) : ComplexModel n := F.flat (F.amb.val x)

/-- The inverse `e⁻¹ ∘ Φ⁻¹` of the flattening coordinates. -/
def finv (z : ComplexModel n) : X := F.amb.val.symm (F.flat.symm z)

theorem finv_fcoord {x : X} (hx : x ∈ F.ambSource) : finv F (fcoord F x) = x := by
  rw [finv, fcoord, F.flat.left_inv hx.2, F.amb.val.left_inv hx.1]

theorem fcoord_finv {z : ComplexModel n} (hz : z ∈ F.flat.target) :
    fcoord F (finv F z) = z := by
  rw [finv, fcoord, F.amb.val.right_inv (F.flat_source_subset (F.flat.map_target hz)),
    F.flat.right_inv hz]

theorem finv_mem {z : ComplexModel n} (hz : z ∈ F.flat.target) :
    finv F z ∈ F.ambSource := by
  have hw := F.flat.map_target hz
  refine ⟨F.amb.val.map_target (F.flat_source_subset hw), ?_⟩
  rw [mem_preimage, finv, F.amb.val.right_inv (F.flat_source_subset hw)]
  exact hw

theorem fcoord_mem {x : X} (hx : x ∈ F.ambSource) : fcoord F x ∈ F.flat.target :=
  F.flat.map_source hx.2

theorem continuousOn_fcoord : ContinuousOn (fcoord F) F.ambSource :=
  F.flat.continuousOn.comp (F.amb.val.continuousOn.mono fun _ hx => hx.1) fun _ hx => hx.2

theorem continuousOn_finv : ContinuousOn (finv F) F.flat.target :=
  F.amb.val.continuousOn_symm.comp F.flat.continuousOn_symm
    fun _ hz => F.flat_source_subset (F.flat.map_target hz)

theorem mem_iff_fcoord {x : X} (hx : x ∈ F.ambSource) :
    x ∈ W ↔ fcoord F x ∈ complexCoordinatePlane n m :=
  F.mem_iff x hx.1 hx.2

theorem finv_image {A : Set (ComplexModel n)} (hA : A ⊆ F.flat.target) :
    finv F '' A = F.ambSource ∩ fcoord F ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨finv_mem F (hA hz), by rw [mem_preimage, fcoord_finv F (hA hz)]; exact hz⟩
  · rintro ⟨hx, hxA⟩
    exact ⟨fcoord F x, hxA, finv_fcoord F hx⟩

/-- `ζ⁻¹` is holomorphic. -/
theorem mdifferentiableAt_finv {z : ComplexModel n} (hz : z ∈ F.flat.target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (finv F) z := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) F.amb.val.symm
      (F.flat.symm z) :=
    mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) F.amb.property
      (F.flat_source_subset (F.flat.map_target hz))
  have h2 : DifferentiableAt ℂ F.flat.symm z :=
    F.differentiableOn_flat_symm.differentiableAt (F.flat.open_target.mem_nhds hz)
  exact h1.comp z h2.mdifferentiableAt

/-- A function holomorphic on an open set of `X` reads holomorphically in the coordinates. -/
theorem differentiableAt_comp_finv {g : X → ℂ} {z : ComplexModel n} (hz : z ∈ F.flat.target)
    (hg : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g (finv F z)) :
    DifferentiableAt ℂ (fun z => g (finv F z)) z := by
  have := hg.comp z (mdifferentiableAt_finv F hz)
  exact mdifferentiableAt_iff_differentiableAt.mp this

/-- The coordinates are holomorphic. -/
theorem mdifferentiableAt_fcoord {x : X} (hx : x ∈ F.ambSource) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fcoord F) x := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) F.amb.val x :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) F.amb.property hx.1
  have h2 : DifferentiableAt ℂ F.flat (F.amb.val x) :=
    F.differentiableOn_flat.differentiableAt (F.flat.open_source.mem_nhds hx.2)
  exact h2.mdifferentiableAt.comp x h1

/-! ### Comparison of measures -/

variable [MeasurableSpace X] [BorelSpace X]

/-- **Upper comparison**: `∫_{ζ⁻¹ K} f dμ ≤ C ∫_K f ∘ ζ⁻¹ dz` on a compact `K` of the target. -/
theorem lintegral_finv_image_le {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ F.flat.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ x in finv F '' K, f x ∂μ ≤ ENNReal.ofReal C * ∫⁻ z in K, f (finv F z) := by
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ F.amb
  set A : Set (ComplexModel n) := F.flat.symm '' K with hA
  have hAc : IsCompact A := hK.image_of_continuousOn (F.flat.continuousOn_symm.mono hKt)
  have hAs : A ⊆ F.flat.source := by
    rintro _ ⟨z, hz, rfl⟩; exact F.flat.map_target (hKt hz)
  have hAt : A ⊆ F.amb.val.target := hAs.trans F.flat_source_subset
  obtain ⟨C₁, hC₁⟩ := hAc.exists_bound_of_continuousOn (hρs.continuousOn.mono hAt)
  have hC1 : ContDiffOn ℝ 1 F.flat.symm F.flat.target :=
    ((contDiffOn_of_differentiableOn_complex F.differentiableOn_flat_symm
      F.flat.open_target).restrict_scalars ℝ).of_le (by simp)
  obtain ⟨C₂, hC₂0, hC₂⟩ := ChartWeightedL2.exists_bound_abs_det_fderiv F.flat.open_target hK hKt hC1
  refine ⟨max C₁ 0 * C₂, by positivity, fun f hf => ?_⟩
  have himage : finv F '' K = F.amb.val.source ∩ F.amb.val ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨F.amb.val.map_target (hAt ⟨z, hz, rfl⟩), ?_⟩
      rw [mem_preimage, finv, F.amb.val.right_inv (hAt ⟨z, hz, rfl⟩)]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨hx, y, hy, hyx⟩
      refine ⟨y, hy, ?_⟩
      rw [finv, hyx, F.amb.val.left_inv hx]
  rw [himage, setLIntegral_source_inter_preimage F.amb hρs.continuousOn hmap hAc hAt hf]
  calc ∫⁻ y in A, ENNReal.ofReal (ρ y) * f (F.amb.val.symm y)
      ≤ ∫⁻ y in A, ENNReal.ofReal (max C₁ 0) * f (F.amb.val.symm y) := by
        refine setLIntegral_mono' hAc.isClosed.measurableSet fun y hy => ?_
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have := hC₁ y hy
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    _ = ENNReal.ofReal (max C₁ 0) * ∫⁻ y in F.flat.symm '' K, f (F.amb.val.symm y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max C₁ 0) * (ENNReal.ofReal C₂ *
          ∫⁻ z in K, f (F.amb.val.symm (F.flat.symm z))) := by
        refine mul_le_mul' le_rfl ?_
        refine ChartWeightedL2.lintegral_image_le_of_abs_det_le volume hK.isClosed.measurableSet
          (f' := fun z => fderiv ℝ F.flat.symm z) (fun z hz => ?_)
          (F.flat.symm.injOn.mono hKt) (fun z hz => hC₂ z hz) (fun y => f (F.amb.val.symm y))
        exact ((hC1.differentiableOn one_ne_zero).differentiableAt
          (F.flat.open_target.mem_nhds (hKt hz))).hasFDerivAt.hasFDerivWithinAt
    _ = ENNReal.ofReal (max C₁ 0 * C₂) * ∫⁻ z in K, f (finv F z) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_max_right _ _)]
        rfl

/-- **Lower comparison**: `∫_K f ∘ ζ⁻¹ dz ≤ C ∫_{ζ⁻¹ K} f dμ` on a compact `K` of the target. -/
theorem lintegral_le_finv_image {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ F.flat.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ z in K, f (finv F z) ≤ ENNReal.ofReal C * ∫⁻ x in finv F '' K, f x ∂μ := by
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ F.amb
  set A : Set (ComplexModel n) := F.flat.symm '' K with hA
  have hAc : IsCompact A := hK.image_of_continuousOn (F.flat.continuousOn_symm.mono hKt)
  have hAs : A ⊆ F.flat.source := by
    rintro _ ⟨z, hz, rfl⟩; exact F.flat.map_target (hKt hz)
  have hAt : A ⊆ F.amb.val.target := hAs.trans F.flat_source_subset
  -- `ρ ≥ c > 0` on `A`
  have hρc : ContinuousOn ρ A := hρs.continuousOn.mono hAt
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · refine ⟨0, le_rfl, fun f _ => ?_⟩
    have : K = ∅ := by
      rw [eq_empty_iff_forall_notMem]; intro z hz
      have : F.flat.symm z ∈ A := ⟨z, hz, rfl⟩
      rw [hAe] at this; exact this
    simp [this]
  obtain ⟨y₀, hy₀A, hmin⟩ := hAc.exists_isMinOn hAne hρc
  have hc : 0 < ρ y₀ := hρpos y₀ (hAt hy₀A)
  have hC1 : ContDiffOn ℝ 1 F.flat F.flat.source :=
    ((contDiffOn_of_differentiableOn_complex F.differentiableOn_flat
      F.flat.open_source).restrict_scalars ℝ).of_le (by simp)
  obtain ⟨C₂, hC₂0, hC₂⟩ := ChartWeightedL2.exists_bound_abs_det_fderiv F.flat.open_source hAc hAs hC1
  refine ⟨C₂ * (ρ y₀)⁻¹, by positivity, fun f hf => ?_⟩
  have himage : finv F '' K = F.amb.val.source ∩ F.amb.val ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨F.amb.val.map_target (hAt ⟨z, hz, rfl⟩), ?_⟩
      rw [mem_preimage, finv, F.amb.val.right_inv (hAt ⟨z, hz, rfl⟩)]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨hx, y, hy, hyx⟩
      refine ⟨y, hy, ?_⟩
      rw [finv, hyx, F.amb.val.left_inv hx]
  have hKimg : F.flat '' A = K := by
    ext z
    constructor
    · rintro ⟨y, ⟨z', hz', rfl⟩, rfl⟩; rw [F.flat.right_inv (hKt hz')]; exact hz'
    · intro hz; exact ⟨F.flat.symm z, ⟨z, hz, rfl⟩, F.flat.right_inv (hKt hz)⟩
  rw [himage, setLIntegral_source_inter_preimage F.amb hρs.continuousOn hmap hAc hAt hf]
  calc ∫⁻ z in K, f (finv F z)
      = ∫⁻ z in F.flat '' A, f (F.amb.val.symm (F.flat.symm z)) := by rw [hKimg]; rfl
    _ ≤ ENNReal.ofReal C₂ * ∫⁻ y in A, f (F.amb.val.symm (F.flat.symm (F.flat y))) :=
        ChartWeightedL2.lintegral_image_le_of_abs_det_le volume hAc.isClosed.measurableSet
          (f' := fun y => fderiv ℝ F.flat y)
          (fun y hy => ((hC1.differentiableOn one_ne_zero).differentiableAt
            (F.flat.open_source.mem_nhds (hAs hy))).hasFDerivAt.hasFDerivWithinAt)
          (F.flat.injOn.mono hAs) (fun y hy => hC₂ y hy) _
    _ = ENNReal.ofReal C₂ * ∫⁻ y in A, f (F.amb.val.symm y) := by
        congr 1
        refine setLIntegral_congr_fun hAc.isClosed.measurableSet fun y hy => ?_
        rw [F.flat.left_inv (hAs hy)]
    _ ≤ ENNReal.ofReal C₂ * ∫⁻ y in A, ENNReal.ofReal (ρ y₀)⁻¹ *
          (ENNReal.ofReal (ρ y) * f (F.amb.val.symm y)) := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' hAc.isClosed.measurableSet fun y hy => ?_)
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
        refine le_mul_of_one_le_left zero_le ?_
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]
        exact hmin hy
    _ = ENNReal.ofReal (C₂ * (ρ y₀)⁻¹) * ∫⁻ y in A, ENNReal.ofReal (ρ y) * f (F.amb.val.symm y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul hC₂0]

end FlatCoord

/-! ### The normal weight -/

theorem volume_coord_eq_zero {n : ℕ} (i : Fin n) :
    volume {z : ComplexModel n | z i = 0} = 0 := by
  set ℓ : ComplexModel n →ₗ[ℝ] ℂ :=
    ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) : ComplexModel n →ₗ[ℂ] ℂ).restrictScalars ℝ
    with hℓ
  have hsub : {z : ComplexModel n | z i = 0} = (LinearMap.ker ℓ : Set _) := by
    ext z; simp [hℓ]
  have hker : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single i (1 : ℂ) : ComplexModel n) ∈ LinearMap.ker ℓ := by
      rw [h]; trivial
    simp [hℓ] at this
  rw [hsub]
  exact Measure.addHaar_submodule volume _ hker

theorem normalWeight_eq_zero_iff {n m : ℕ} (z : ComplexModel n) :
    normalWeight n m z = 0 ↔ z ∈ complexCoordinatePlane n m := by
  rw [normalWeight, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by split_ifs <;> positivity)]
  constructor
  · intro h i hi
    have := h i (Finset.mem_univ _)
    rw [if_pos hi] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · intro h i _
    split_ifs with hi
    · rw [h i hi, norm_zero, zero_pow two_ne_zero]
    · rfl

theorem normalWeight_pos_of_notMem {n m : ℕ} {z : ComplexModel n}
    (hz : z ∉ complexCoordinatePlane n m) : 0 < normalWeight n m z :=
  lt_of_le_of_ne (normalWeight_nonneg n m z) (fun h => hz ((normalWeight_eq_zero_iff z).mp h.symm))

theorem ae_normalWeight_pos {n m : ℕ} (hmn : m < n) :
    ∀ᵐ z : ComplexModel n, 0 < normalWeight n m z := by
  have h0 := volume_coord_eq_zero (⟨n - 1, by omega⟩ : Fin n)
  rw [← compl_mem_ae_iff] at h0
  filter_upwards [h0] with z hz
  refine normalWeight_pos_of_notMem fun hpl => hz ?_
  exact hpl _ (by simp; omega)

/-- `e^{-cL} ≤ e^{cC} |w|^{-2c}` from `L ≥ log |w|² - C`. -/
theorem multiplierWeight_le_of_log {c L C t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    (h : |L - Real.log t| ≤ C) :
    multiplierWeight c (L : EReal) ≤ ENNReal.ofReal (Real.exp (c * C)) * ENNReal.ofReal (t ^ (-c)) := by
  rw [multiplierWeight_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := (abs_le.mp h).1
  nlinarith

/-- `e^{-cL} ≥ e^{-cC} |w|^{-2c}` from `L ≤ log |w|² + C`. -/
theorem le_multiplierWeight_of_log {c L C t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    (h : |L - Real.log t| ≤ C) :
    ENNReal.ofReal (Real.exp (-(c * C))) * ENNReal.ofReal (t ^ (-c)) ≤ multiplierWeight c (L : EReal) := by
  rw [multiplierWeight_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := (abs_le.mp h).2
  nlinarith

/-- `|w|² ≤ e^{C} e^{L}` from `L ≥ log |w|² - C`. -/
theorem le_exp_of_log {L C t : ℝ} (ht : 0 < t) (h : |L - Real.log t| ≤ C) :
    t ≤ Real.exp C * Real.exp L := by
  rw [← Real.exp_add]
  calc t = Real.exp (Real.log t) := (Real.exp_log ht).symm
    _ ≤ Real.exp (C + L) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp h).1])

theorem measurable_indicator_of_continuousOn' {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {V : Set Y} (hV : IsOpen V) {f : Y → ℝ≥0∞}
    (hf : ContinuousOn f V) : Measurable (V.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hf continuousOn_const hV.measurableSet

/-! ### The pole region -/

section PoleRegion

variable [MeasurableSpace X] [BorelSpace X]

/-- **The pole region.**  Let `Λ` be a function with the local form `Λ = log |w|² + O(1)` of a
normal pole near `p ∈ W` in the flattening coordinates `ζ` of `F`, finite off `W`.  Then on
`K = ζ⁻¹(B̄(0, ε))` for small `ε`: `e^{-cΛ}` is integrable for `0 ≤ c < codim W`; a holomorphic
function vanishing on `W` is `O(e^{Λ})`; a holomorphic function with
`∫ |g|² e^{-codim(W) Λ} < ∞` vanishes on `W ∩ ζ⁻¹(B(0, ε))`. -/
theorem exists_poleRegion {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (F : FlatData n m X W) (hmn : m < n) {p : X} (hpF : p ∈ F.ambSource) (hp0 : fcoord F p = 0)
    {Λ : X → EReal} (hΛm : Measurable Λ) (hΛtop : ∀ x, Λ x ≠ ⊤) (hΛbot : ∀ x, Λ x = ⊥ → x ∈ W)
    (hloc : ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ y ∈ U, y ∉ W →
      |(Λ y).toReal - Real.log (normalWeight n m (fcoord F y))| ≤ C) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → closedBall (0 : ComplexModel n) ε ⊆ F.flat.target ∧
      (∀ c : ℝ, 0 ≤ c → c < ((n - m : ℕ) : ℝ) →
        ∫⁻ x in finv F '' closedBall 0 ε, multiplierWeight c (Λ x) ∂μ ≠ ⊤) ∧
      (∀ (g : X → ℂ) (O : Set X), IsOpen O →
        (∀ x ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x) →
        (∀ x ∈ O, x ∈ W → g x = 0) → ∀ K : Set X, IsCompact K →
        K ⊆ O ∩ finv F '' closedBall 0 ε →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ENNReal.ofReal (‖g x‖ ^ 2) ≤ ENNReal.ofReal C * EReal.exp (Λ x)) ∧
      (∀ (g : X → ℂ) (O : Set X), IsOpen O →
        (∀ x ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x) →
        ∀ y ∈ O, y ∈ W → y ∈ finv F '' ball 0 ε →
        ∫⁻ x in O ∩ finv F '' closedBall 0 ε,
          ENNReal.ofReal (‖g x‖ ^ 2) * multiplierWeight ((n - m : ℕ) : ℝ) (Λ x) ∂μ ≠ ⊤ →
        g y = 0) ∧
      (∃ C : ℝ, ∀ c : ℝ, 0 ≤ c → ∀ z ∈ closedBall (0 : ComplexModel n) ε,
        z ∉ complexCoordinatePlane n m →
        multiplierWeight c (Λ (finv F z)) ≤ ENNReal.ofReal (Real.exp (c * C)) *
          ENNReal.ofReal (normalWeight n m z ^ (-c))) := by
  obtain ⟨U, hU, CΛ, hCΛ⟩ := hloc
  have h0t : (0 : ComplexModel n) ∈ F.flat.target := by rw [← hp0]; exact fcoord_mem F hpF
  have hfinv0 : finv F 0 = p := by rw [← hp0, finv_fcoord F hpF]
  have hcont : ContinuousAt (finv F) 0 :=
    (continuousOn_finv F).continuousAt (F.flat.open_target.mem_nhds h0t)
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ F.flat.target ∧ finv F z ∈ U := by
    filter_upwards [F.flat.open_target.mem_nhds h0t, hcont.eventually (by rw [hfinv0]; exact hU)]
      with z h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε₁ / 2, by positivity, fun ε hε0 hεle => ?_⟩
  have hcb : closedBall (0 : ComplexModel n) ε ⊆ ball 0 ε₁ :=
    closedBall_subset_ball (by linarith)
  have hcbt : closedBall (0 : ComplexModel n) ε ⊆ F.flat.target := fun z hz => (hball z (hcb hz)).1
  have hcbc : IsCompact (closedBall (0 : ComplexModel n) ε) := isCompact_closedBall 0 ε
  -- the local form along the coordinates
  have hLF : ∀ z ∈ ball (0 : ComplexModel n) ε₁, z ∉ complexCoordinatePlane n m →
      ∃ L : ℝ, Λ (finv F z) = (L : EReal) ∧ |L - Real.log (normalWeight n m z)| ≤ CΛ := by
    intro z hz hzpl
    have hzt := (hball z hz).1
    have hnW : finv F z ∉ W := by
      rw [mem_iff_fcoord F (finv_mem F hzt), fcoord_finv F hzt]; exact hzpl
    have hne : Λ (finv F z) ≠ ⊥ := fun h => hnW (hΛbot _ h)
    refine ⟨(Λ (finv F z)).toReal, (EReal.coe_toReal (hΛtop _) hne).symm, ?_⟩
    have := hCΛ _ (hball z hz).2 hnW
    rwa [fcoord_finv F hzt] at this
  have hKsub : finv F '' closedBall 0 ε ⊆ F.ambSource := by
    rintro _ ⟨z, hz, rfl⟩; exact finv_mem F (hcbt hz)
  refine ⟨hcbt, ?_, ?_, ?_, CΛ, fun c hc0 z hz hzpl => ?_⟩
  rotate_left
  rotate_left
  rotate_left
  · obtain ⟨L, hL, hLC⟩ := hLF z (hcb hz) hzpl
    rw [hL]
    exact multiplierWeight_le_of_log hc0 (normalWeight_pos_of_notMem hzpl) hLC
  · -- subcritical integrability
    intro c hc0 hc
    obtain ⟨C₀, -, hC₀⟩ := lintegral_finv_image_le F hμ hcbc hcbt
    have hfm : Measurable fun x => multiplierWeight c (Λ x) :=
      (multiplierWeight_antitone hc0).measurable.comp hΛm
    refine ne_top_of_le_ne_top ?_ (hC₀ _ hfm)
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have hbound : ∫⁻ z in closedBall (0 : ComplexModel n) ε, multiplierWeight c (Λ (finv F z)) ≤
        ∫⁻ z in ball (0 : ComplexModel n) ε₁, ENNReal.ofReal (Real.exp (c * CΛ)) *
          ENNReal.ofReal (normalWeight n m z ^ (-c)) := by
      refine (setLIntegral_mono_ae' measurableSet_closedBall ?_).trans (lintegral_mono_set hcb)
      filter_upwards [ae_normalWeight_pos (m := m) hmn] with z hzpos hz
      have hzpl : z ∉ complexCoordinatePlane n m := fun h =>
        (hzpos.ne' ((normalWeight_eq_zero_iff z).mpr h))
      obtain ⟨L, hL, hLC⟩ := hLF z (hcb hz) hzpl
      rw [hL]
      exact multiplierWeight_le_of_log hc0 hzpos hLC
    refine ne_top_of_le_ne_top ?_ hbound
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lintegral_normalWeight_rpow_lt_top hmn hc ε₁).ne
  · -- the Lipschitz bound
    intro g O hO hg hgW K hK hKO
    set O' : Set (ComplexModel n) := ball (0 : ComplexModel n) ε₁ ∩ (finv F) ⁻¹' O with hO'
    have hO'o : IsOpen O' :=
      ((continuousOn_finv F).mono fun z hz => (hball z hz).1).isOpen_inter_preimage isOpen_ball hO
    have hhd : DifferentiableOn ℂ (fun z => g (finv F z)) O' := fun z hz =>
      (differentiableAt_comp_finv F (hball z hz.1).1 (hg _ hz.2)).differentiableWithinAt
    have hh0 : ∀ z ∈ O', z ∈ complexCoordinatePlane n m → g (finv F z) = 0 := by
      intro z hz hpl
      have hzt := (hball z hz.1).1
      refine hgW _ hz.2 ?_
      rw [mem_iff_fcoord F (finv_mem F hzt), fcoord_finv F hzt]; exact hpl
    have hKs : K ⊆ F.ambSource := fun x hx => hKsub (hKO hx).2
    have hK'c : IsCompact (fcoord F '' K) := hK.image_of_continuousOn
      ((continuousOn_fcoord F).mono hKs)
    have hK'O : fcoord F '' K ⊆ O' := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hzx⟩ := (hKO hx).2
      refine ⟨?_, ?_⟩
      · rw [← hzx, fcoord_finv F (hcbt hz)]; exact hcb hz
      · rw [mem_preimage, finv_fcoord F (hKs hx)]; exact (hKO hx).1
    obtain ⟨C₁, hC₁0, hC₁⟩ := exists_sq_le_normalWeight hmn.le hO'o hhd hh0 hK'c hK'O
    refine ⟨C₁ * Real.exp CΛ, by positivity, fun x hx => ?_⟩
    by_cases hxW : x ∈ W
    · rw [hgW x (hKO hx).1 hxW, norm_zero]; simp
    have hxs := hKs hx
    have hzpl : fcoord F x ∉ complexCoordinatePlane n m := by
      rw [← mem_iff_fcoord F hxs]; exact hxW
    have hzb : fcoord F x ∈ ball (0 : ComplexModel n) ε₁ := (hK'O ⟨x, hx, rfl⟩).1
    obtain ⟨L, hL, hLC⟩ := hLF _ hzb hzpl
    rw [finv_fcoord F hxs] at hL
    rw [hL, EReal.exp_coe, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hC₁ _ ⟨x, hx, rfl⟩
    rw [finv_fcoord F hxs] at h1
    have h2 := le_exp_of_log (normalWeight_pos_of_notMem hzpl) hLC
    calc ‖g x‖ ^ 2 ≤ C₁ * normalWeight n m (fcoord F x) := h1
      _ ≤ C₁ * (Real.exp CΛ * Real.exp L) := mul_le_mul_of_nonneg_left h2 hC₁0
      _ = C₁ * Real.exp CΛ * Real.exp L := by ring
  · -- vanishing from the critical exponent
    intro g O hO hg y hyO hyW hyB hint
    obtain ⟨z₀, hz₀, hz₀y⟩ := hyB
    have hz₀t : z₀ ∈ F.flat.target := hcbt (ball_subset_closedBall hz₀)
    have hz₀pl : z₀ ∈ complexCoordinatePlane n m := by
      rw [← fcoord_finv F hz₀t, ← mem_iff_fcoord F (finv_mem F hz₀t), hz₀y]; exact hyW
    set O' : Set (ComplexModel n) := ball (0 : ComplexModel n) ε ∩ (finv F) ⁻¹' O with hO'
    have hO'o : IsOpen O' :=
      ((continuousOn_finv F).mono fun z hz => hcbt (ball_subset_closedBall hz)).isOpen_inter_preimage
        isOpen_ball hO
    have hz₀O' : z₀ ∈ O' := ⟨hz₀, by rw [mem_preimage, hz₀y]; exact hyO⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hO'o z₀ hz₀O'
    set K'' := closedBall z₀ (δ / 2) with hK''
    have hK''sub : K'' ⊆ O' := (closedBall_subset_ball (by linarith)).trans hδsub
    have hK''t : K'' ⊆ F.flat.target := fun z hz =>
      hcbt (ball_subset_closedBall (hK''sub hz).1)
    obtain ⟨C₂, -, hC₂⟩ := lintegral_le_finv_image F hμ (isCompact_closedBall z₀ (δ / 2)) hK''t
    have hgc : ContinuousOn g O := fun x hx => (hg x hx).continuousAt.continuousWithinAt
    set f : X → ℝ≥0∞ := fun x => O.indicator (fun x => ENNReal.ofReal (‖g x‖ ^ 2)) x *
      multiplierWeight ((n - m : ℕ) : ℝ) (Λ x) with hf
    have hfm : Measurable f := by
      refine (measurable_indicator_of_continuousOn' hO
        (ENNReal.continuous_ofReal.comp_continuousOn ((continuous_norm.comp_continuousOn hgc).pow 2))).mul ?_
      exact (multiplierWeight_antitone (Nat.cast_nonneg _)).measurable.comp hΛm
    have himg : finv F '' K'' ⊆ O ∩ finv F '' closedBall 0 ε := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨(hK''sub hz).2, z, ball_subset_closedBall (hK''sub hz).1, rfl⟩
    have hfin : ∫⁻ z in K'', f (finv F z) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) (hC₂ f hfm)
      refine ne_top_of_le_ne_top hint ((lintegral_mono_set himg).trans (le_of_eq ?_))
      refine setLIntegral_congr_fun ((hO.measurableSet).inter ?_) fun x hx => ?_
      · exact (hcbc.image_of_continuousOn ((continuousOn_finv F).mono hcbt)).isClosed.measurableSet
      · rw [hf]; simp only; rw [indicator_of_mem hx.1]
    -- compare with the critical weight in the coordinates
    have hcrit : ∫⁻ z in ball z₀ (δ / 2), ENNReal.ofReal (‖g (finv F z)‖ ^ 2) *
        ENNReal.ofReal (normalWeight n m z ^ (-((n - m : ℕ) : ℝ))) ≠ ⊤ := by
      set r : ℝ := ((n - m : ℕ) : ℝ)
      have hr0 : 0 ≤ r := Nat.cast_nonneg _
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
        (ENNReal.ofReal_ne_top (r := Real.exp (r * CΛ))) hfin) ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (setLIntegral_mono_ae' measurableSet_ball ?_).trans
        (lintegral_mono_set ball_subset_closedBall)
      filter_upwards [ae_normalWeight_pos (m := m) hmn] with z hzpos hz
      have hzpl : z ∉ complexCoordinatePlane n m := fun h =>
        (hzpos.ne' ((normalWeight_eq_zero_iff z).mpr h))
      have hzO' := hδsub (ball_subset_ball (by linarith) hz)
      obtain ⟨L, hL, hLC⟩ := hLF z (ball_subset_ball (by linarith) hzO'.1) hzpl
      have hlow := le_multiplierWeight_of_log hr0 hzpos hLC
      rw [hf]
      simp only
      rw [indicator_of_mem (show finv F z ∈ O from hzO'.2), hL]
      calc ENNReal.ofReal (‖g (finv F z)‖ ^ 2) * ENNReal.ofReal (normalWeight n m z ^ (-r))
          = ENNReal.ofReal (Real.exp (r * CΛ)) * (ENNReal.ofReal (‖g (finv F z)‖ ^ 2) *
              (ENNReal.ofReal (Real.exp (-(r * CΛ))) * ENNReal.ofReal (normalWeight n m z ^ (-r)))) := by
            rw [← mul_assoc (ENNReal.ofReal (Real.exp (r * CΛ))), mul_comm (ENNReal.ofReal _)
              (ENNReal.ofReal (‖g (finv F z)‖ ^ 2)), mul_assoc, ← mul_assoc (ENNReal.ofReal _)
              (ENNReal.ofReal (Real.exp (-(r * CΛ)))), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← Real.exp_add, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (r * CΛ)) * (ENNReal.ofReal (‖g (finv F z)‖ ^ 2) *
              multiplierWeight r (L : EReal)) := by gcongr
    have hzero := eq_zero_of_lintegral_normalWeight hmn isOpen_ball
      (fun z hz => ((differentiableAt_comp_finv F (hK''t (ball_subset_closedBall hz))
        (hg _ (hK''sub (ball_subset_closedBall hz)).2)).continuousAt).continuousWithinAt)
      (mem_ball_self (by linarith)) hz₀pl hcrit
    rwa [hz₀y] at hzero

end PoleRegion

end SGPT.Trace.OTMargin
