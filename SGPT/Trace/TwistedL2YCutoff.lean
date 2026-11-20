import SGPT.Trace.TwistedL2YProj
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Cut-offs, localization and Kähler lowering on a manifold

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:cutoff`).

* `sigmaDbarG_eq_kahlerAntisym`: in a chart, `∂̄(σ^♭ W) = (gA_W)ᵀ - gA_W` for smooth `W` (Kähler
  lowering with a local potential of `σ`, `exists_sigma_potentialX`).
* `dRX χ`: the `σ`-unit cotangent vector `B*⁻¹ ∂̄χ` read in the reference chart;
  `norm_dRX_sq_le`: `‖B*⁻¹ ∂̄χ‖² ≤ c²/2` if `|dχ|_σ ≤ c` (the complete cut-offs).
* `exists_localizationX`: a chart-smooth function with compact support in `U` is a finite sum of
  chart-smooth functions supported in chart-frame domains (smooth partition of unity on `X` for the
  real structure underlying the holomorphic atlas).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Metric
open scoped Topology ContDiff ComplexConjugate Manifold ComplexOrder InnerProductSpace ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.OTChen

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### The real smooth structure -/

/-- The holomorphic atlas defines a real smooth manifold structure. -/
theorem isManifold_realX : IsManifold 𝓘(ℝ, ComplexModel n) ∞ X := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ComplexModel n) ∞ X
  intro e f he hf
  have h : ContDiffOn ℝ ∞ (chartTransition (n := n) ⟨e, he⟩ ⟨f, hf⟩)
      (chartTransition (n := n) ⟨e, he⟩ ⟨f, hf⟩).source :=
    fun z hz => (HolomorphicMaps.chartTransition_contDiffAt_real ⟨e, he⟩ ⟨f, hf⟩ hz).contDiffWithinAt
  simpa only [chartTransition, mfld_simps] using h

/-- A smooth function for the real structure is smooth in the holomorphic charts. -/
theorem chartSmooth_of_contMDiff {f : X → ℝ}
    (hf : ContMDiff 𝓘(ℝ, ComplexModel n) 𝓘(ℝ, ℝ) ∞ f) (c : ComplexChart n X) :
    ContDiffOn ℝ ∞ (fun z => f (c.val.symm z)) c.val.target := by
  have : IsManifold 𝓘(ℝ, ComplexModel n) ∞ X := isManifold_realX
  have he : c.val ∈ IsManifold.maximalAtlas 𝓘(ℝ, ComplexModel n) ∞ X :=
    IsManifold.subset_maximalAtlas c.property
  have he' : OpenPartialHomeomorph.refl ℝ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℝ) ∞ ℝ :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas ℝ (0 : ℝ))
  have h := (contMDiffOn_iff_of_mem_maximalAtlas' he he' subset_rfl
    (fun x _ => mem_univ _)).mp hf.contMDiffOn
  simp only [mfld_simps] at h
  rwa [c.val.image_source_eq_target] at h

/-- The function `ζ ∘ c⁻¹` on the chart target, extended by zero. -/
def chartFn (c : ComplexChart n X) (ζ : X → ℝ) (z : ComplexModel n) : ℝ :=
  c.val.target.indicator (fun z => ζ (c.val.symm z)) z

theorem chartFn_eventuallyEq {c : ComplexChart n X} (ζ : X → ℝ) {z : ComplexModel n}
    (hz : z ∈ c.val.target) : chartFn c ζ =ᶠ[𝓝 z] fun y => ζ (c.val.symm y) := by
  filter_upwards [c.val.open_target.mem_nhds hz] with y hy
  exact indicator_of_mem hy _

/-! ### Measurability -/

theorem continuousOn_mv' {α : Type*} [TopologicalSpace α] {S : Set α}
    {M : α → Matrix (Fin n) (Fin n) ℂ} {y : α → ComplexModel n}
    (hM : ∀ i j, ContinuousOn (fun z => M z i j) S) (hy : ContinuousOn y S) :
    ContinuousOn (fun z => mv (M z) (y z)) S := by
  have hfun : (fun z => mv (M z) (y z)) = fun z => ∑ i, ∑ j,
      (M z i j * y z j) • (EuclideanSpace.single i (1 : ℂ) : ComplexModel n) := by
    funext z
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hfun]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  have hyj : ContinuousOn (fun z => y z j) S :=
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous).comp_continuousOn hy
  exact ((hM i j).mul hyj).smul continuousOn_const

theorem measurable_ref_indicator' [MeasurableSpace X] [BorelSpace X] {β : Type*}
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Zero β] {S : Set X} (hS : IsOpen S)
    {F : ComplexChart n X → X → β} (hF : ∀ c, ContinuousOn (F c) (S ∩ c.val.source)) :
    Measurable fun x => S.indicator (fun x => F (cR n x) x) x := by
  have h := measurable_cR_comp (n := n) (f := fun c x => (S ∩ c.val.source).indicator (F c) x)
    fun c => measurable_indicator_of_continuousOn_ref (hS.inter c.val.open_source) (hF c)
  convert h using 1
  funext x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ S ∩ (cR n x).val.source from
      ⟨hx, mem_cR_source x⟩)]
  · rw [indicator_of_notMem hx, indicator_of_notMem fun h => hx h.1]

/-! ### Kähler lowering in a chart -/

section Lowering

variable {omega : KahlerBackground n X} {r : X → ℝ} {U : Set X} (hU : IsOpen U)
  (hr : IsKahlerModificationOn omega r U)
include hU hr

theorem contDiffOn_sigmaMatX (c : ComplexChart n X) (l k : Fin n) :
    ContDiffOn ℝ ∞ (fun y => sigmaMatX omega r c y l k) (c.val.target ∩ c.val.symm ⁻¹' U) := by
  intro z hz
  obtain ⟨V, R, hV, hzV, -, hR, hσ⟩ := exists_sigma_potentialX hU hr c hz.1 hz.2
  have hRc : ContDiffOn ℝ ∞ (fun y => (R y : ℂ)) V := contDiffOn_ofReal' hR
  have h : ContDiffOn ℝ ∞ (dbarDir (coordVec k) (dDir (coordVec l) fun x => (R x : ℂ))) V :=
    contDiffOn_dbarDir hV (contDiffOn_dDir hV hRc _) _
  have hev : (fun y => sigmaMatX omega r c y l k) =ᶠ[𝓝 z]
      dbarDir (coordVec k) (dDir (coordVec l) fun x => (R x : ℂ)) := by
    filter_upwards [hV.mem_nhds hzV] with y hy
    exact sigmaMatX_eq_hessian hV hR hσ hy l k
  exact ((h.contDiffAt (hV.mem_nhds hzV)).congr_of_eventuallyEq hev).contDiffWithinAt

/-- **Kähler lowering in a chart**: `∂̄(σ^♭ W) = (g A_W)ᵀ - g A_W` for smooth `W`. -/
theorem sigmaDbarG_eq_kahlerAntisym {c : ComplexChart n X} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hDU : D ⊆ c.val.target ∩ c.val.symm ⁻¹' U)
    {W : ComplexModel n → ComplexModel n} (hW : ContDiffOn ℝ ∞ W D) {z : ComplexModel n}
    (hz : z ∈ D) :
    sigmaDbarG (sigmaMatX omega r c) W z = kahlerAntisym (gX omega r c z) (Amat W z) := by
  obtain ⟨V, R, hV, hzV, -, hR, hσ⟩ := exists_sigma_potentialX hU hr c (hDU hz).1 (hDU hz).2
  have hO : IsOpen (V ∩ D) := hV.inter hD
  have hWl : ∀ l, ContDiffOn ℝ ∞ (fun y => W y l) (V ∩ D) := fun l =>
    contDiffOn_coord (hW.mono inter_subset_right) l
  have hK := kahlerLoweringStatement (V ∩ D) hO R (hR.mono inter_subset_left)
    (fun l y => W y l) hWl z ⟨hzV, hz⟩
  have hev : ∀ k, (fun y => lowS (sigmaMatX omega r c) W y k) =ᶠ[𝓝 z]
      lowerVector R (fun l y => W y l) k := by
    intro k
    filter_upwards [hV.mem_nhds hzV] with y hy
    simp only [lowS, lowerVector, sigmaMatX_eq_hessian hV hR hσ hy]
  ext j k
  simp only [sigmaDbarG, of_apply, dbarDir_congr_of_eventuallyEq (hev _)]
  rw [hK j k, kahlerAntisym, Matrix.sub_apply, transpose_apply, mul_apply, mul_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [gX, transpose_apply, Amat, of_apply, sigmaMatX_eq_hessian hV hR hσ hzV]

end Lowering

/-! ### Derivatives through a change of chart -/

theorem dbarV_comp_holo {ψ : ComplexModel n → ComplexModel n} {f : ComplexModel n → ℂ}
    {z : ComplexModel n} (hψ : DifferentiableAt ℂ ψ z) (hf : DifferentiableAt ℝ f (ψ z)) :
    TwistedDatum.dbarV (fun y => f (ψ y)) z =
      mv (linMat (fderiv ℂ ψ z))ᴴ (TwistedDatum.dbarV f (ψ z)) := by
  ext k
  simp only [TwistedDatum.dbarV, mv_apply, conjTranspose_apply, RCLike.star_def]
  rw [dbarDir_comp_holo hψ hf, ← eq_sum_coordVec (fderiv ℂ ψ z (coordVec k)), dbarDir_sum_dir]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [linMat, of_apply]

namespace TwistedDatum

variable [MeasurableSpace X] [BorelSpace X] (T : TwistedDatum n X)

/-! ### The `σ`-unit gradient of a cut-off -/

/-- `B*⁻¹ ∂̄χ` at `x`, read in the reference chart (zero off `U`). -/
def dRX (χ : X → ℝ) (x : X) : ComplexModel n :=
  T.U.indicator (fun x => mv (T.BiR x)
    (dbarV (fun y => (χ ((cR n x).val.symm y) : ℂ)) ((cR n x).val x))) x

variable {T}

theorem continuousOn_dbarV_chart {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (c : ComplexChart n X) :
    ContinuousOn (dbarV (fun y => (χ (c.val.symm y) : ℂ))) c.val.target :=
  (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr fun _ =>
    (contDiffOn_dbarDir c.val.open_target (contDiffOn_ofReal' (hχ c)) _).continuousOn)

theorem measurable_dRX {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) : Measurable (T.dRX χ) := by
  refine measurable_ref_indicator' (F := fun c x => mv (BiX T.omega T.r c (c.val x))
    (dbarV (fun y => (χ (c.val.symm y) : ℂ)) (c.val x))) T.isOpen_U fun c => ?_
  have h1 : ContinuousOn (fun x => BiX T.omega T.r c (c.val x)) (T.U ∩ c.val.source) :=
    (continuousOn_BiX T.isOpen_U T.kahler c).comp (c.val.continuousOn.mono inter_subset_right)
      fun x hx => ⟨c.val.map_source hx.2, by rw [mem_preimage, c.val.left_inv hx.2]; exact hx.1⟩
  have h2 : ContinuousOn (fun x => dbarV (fun y => (χ (c.val.symm y) : ℂ)) (c.val x))
      (T.U ∩ c.val.source) :=
    (continuousOn_dbarV_chart hχ c).comp (c.val.continuousOn.mono inter_subset_right)
      fun x hx => c.val.map_source hx.2
  exact continuousOn_mv' (fun i j => continuousOn_entry' h1 i j) h2

/-- **The dual bound for the gradient of a cut-off.** -/
theorem norm_dRX_sq_le {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) {C : ℝ}
    (hC : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, c.val.symm z ∈ T.U →
      ∀ v : ComplexModel n, fderiv ℝ (fun y => χ (c.val.symm y)) z v ^ 2 ≤
        C ^ 2 * modifiedKahlerQuad T.omega T.r c z v) (x : X) :
    ‖T.dRX χ x‖ ^ 2 ≤ C ^ 2 / 2 := by
  by_cases hx : x ∈ T.U
  · rw [dRX, indicator_of_mem hx]
    set c := cR n x
    have hz : c.val x ∈ c.val.target := c.val.map_source (mem_cR_source x)
    have hzU : c.val.symm (c.val x) ∈ T.U := by rw [c.val.left_inv (mem_cR_source x)]; exact hx
    have hd : DifferentiableAt ℝ (fun y => χ (c.val.symm y)) (c.val x) :=
      ((hχ c).contDiffAt (c.val.open_target.mem_nhds hz)).differentiableAt (by simp)
    refine norm_mv_BiX_sq_le T.isOpen_U T.kahler hz hzU (by positivity) fun v => ?_
    rw [inner_dbarV_eq_dbarDir, norm_dbarDir_ofReal_sq hd]
    have h1 := hC c _ hz hzU v
    have h2 := hC c _ hz hzU (Complex.I • v)
    have hI : sigmaQX T.omega T.r c (c.val x) (Complex.I • v) = sigmaQX T.omega T.r c (c.val x) v := by
      rw [sigmaQX_eq_norm_sq T.isOpen_U T.kahler hz hzU,
        sigmaQX_eq_norm_sq T.isOpen_U T.kahler hz hzU, mv_smul, norm_smul, Complex.norm_I, one_mul]
    change _ ≤ _ * sigmaQX T.omega T.r c (c.val x) (Complex.I • v) at h2
    change _ ≤ _ * sigmaQX T.omega T.r c (c.val x) v at h1
    rw [hI] at h2
    change _ ≤ C ^ 2 / 2 * sigmaQX T.omega T.r c (c.val x) v
    linarith
  · rw [dRX, indicator_of_notMem hx, norm_zero]
    have : (0 : ℝ) ≤ C ^ 2 / 2 := by positivity
    simpa using this

/-- The gradient of a sum of chart-smooth functions. -/
theorem dRX_sum {N : ℕ} {ζ : Fin N → X → ℝ} (hζ : ∀ i, ChartSmooth (n := n) (ζ i)) (x : X) :
    T.dRX (fun x => ∑ i, ζ i x) x = ∑ i, T.dRX (ζ i) x := by
  by_cases hx : x ∈ T.U
  · simp only [dRX, indicator_of_mem hx]
    rw [← mv_sum]
    congr 1
    have hz : (cR n x).val x ∈ (cR n x).val.target := (cR n x).val.map_source (mem_cR_source x)
    have hd : ∀ i ∈ (Finset.univ : Finset (Fin N)), DifferentiableAt ℝ
        (fun y => ((ζ i ((cR n x).val.symm y) : ℝ) : ℂ)) ((cR n x).val x) := fun i _ =>
      ((contDiffOn_ofReal' (hζ i (cR n x))).contDiffAt
        ((cR n x).val.open_target.mem_nhds hz)).differentiableAt (by simp)
    ext l
    simp only [dbarV, PiLp.toLp_apply, euclid_sum_apply]
    rw [← dbarDir_finset_sum_fun _ hd]
    congr 1
    funext y
    push_cast
    rfl
  · simp [dRX, indicator_of_notMem hx]

/-! ### Localization into chart-frame domains -/

/-- **Localization of a cut-off into chart-frame domains.** -/
theorem exists_localizationX {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ T.U) :
    ∃ (N : ℕ) (c : Fin N → ComplexChart n X) (e : Fin N → AtlasFrame T.L) (ζ : Fin N → X → ℝ)
      (D K : Fin N → Set (ComplexModel n)),
      (∀ i, ChartSmooth (n := n) (ζ i)) ∧ (∀ i, tsupport (ζ i) ⊆ T.cfd (c i) (e i)) ∧
      (∀ i, IsOpen (D i)) ∧ (∀ i, IsCompact (K i)) ∧ (∀ i, D i ⊆ K i) ∧
      (∀ i, K i ⊆ T.pieceDomain (c i) (e i)) ∧ (∀ i, ContDiff ℝ ∞ (chartFn (c i) (ζ i))) ∧
      (∀ i, HasCompactSupport (chartFn (c i) (ζ i))) ∧ (∀ i, tsupport (chartFn (c i) (ζ i)) ⊆ D i) ∧
      ∀ x, ∑ i, ζ i x = χ x := by
  have : IsManifold 𝓘(ℝ, ComplexModel n) ∞ X := isManifold_realX
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  have : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  set K0 := tsupport χ
  have hK0 : IsCompact K0 := hχc
  obtain ⟨t, ht⟩ := hK0.elim_finite_subcover (fun x : K0 =>
    T.cfd (complexChartAt (n := n) (x : X)) (atlasFrameAt T.L (x : X)))
    (fun x => T.isOpen_cfd _ _) fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩,
      ⟨⟨mem_complexChartAt_source x, mem_atlasFrameAt_baseSet T.L x⟩, hχU hx⟩⟩
  set N := t.card
  let f : Fin N ≃ t := t.equivFin.symm
  set c : Fin N → ComplexChart n X := fun i => complexChartAt (n := n) ((f i : K0) : X)
  set e : Fin N → AtlasFrame T.L := fun i => atlasFrameAt T.L ((f i : K0) : X)
  have hcov : K0 ⊆ ⋃ i, T.cfd (c i) (e i) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨f.symm ⟨y, hy⟩, by simpa [c, e] using hxy⟩
  obtain ⟨θ, hθ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ComplexModel n)
    (isClosed_tsupport χ) (fun i => T.cfd (c i) (e i)) (fun i => T.isOpen_cfd _ _) hcov
  set ζ : Fin N → X → ℝ := fun i x => θ i x * χ x
  have hζs : ∀ i, ChartSmooth (n := n) (ζ i) := fun i c' =>
    (chartSmooth_of_contMDiff (θ i).contMDiff c').mul (hχ c')
  have hζd : ∀ i, tsupport (ζ i) ⊆ T.cfd (c i) (e i) := fun i =>
    (tsupport_mul_subset_left (f := fun x => θ i x)).trans (hθ i)
  have hζc : ∀ i, HasCompactSupport (ζ i) := fun i => hχc.mul_left
  -- the supports in the charts
  set K' : Fin N → Set (ComplexModel n) := fun i => (c i).val '' tsupport (ζ i)
  have hK'c : ∀ i, IsCompact (K' i) := fun i =>
    (hζc i).isCompact.image_of_continuousOn ((c i).val.continuousOn.mono
      fun x hx => (hζd i hx).1.1)
  have hK'd : ∀ i, K' i ⊆ T.pieceDomain (c i) (e i) := by
    rintro i _ ⟨x, hx, rfl⟩
    exact chart_mem_pieceDomain (hζd i hx)
  have hsupp : ∀ i, tsupport (chartFn (c i) (ζ i)) ⊆ K' i := by
    intro i
    refine closure_minimal (fun z hz => ?_) (hK'c i).isClosed
    have hzt : z ∈ (c i).val.target := by
      by_contra h
      exact hz (indicator_of_notMem h _)
    have h1 : ζ i ((c i).val.symm z) ≠ 0 := by
      have := hz
      rwa [Function.mem_support, chartFn, indicator_of_mem hzt] at this
    exact ⟨(c i).val.symm z, subset_closure h1, (c i).val.right_inv hzt⟩
  have hδ : ∀ i, ∃ δ, 0 < δ ∧ cthickening δ (K' i) ⊆ T.pieceDomain (c i) (e i) := fun i =>
    (hK'c i).exists_cthickening_subset_open (T.isOpen_pieceDomain _ _) (hK'd i)
  choose δ hδpos hδsub using hδ
  refine ⟨N, c, e, ζ, fun i => thickening (δ i) (K' i), fun i => cthickening (δ i) (K' i), hζs,
    hζd, fun i => isOpen_thickening, fun i => (hK'c i).cthickening,
    fun i => thickening_subset_cthickening _ _, hδsub, fun i => ?_,
    fun i => HasCompactSupport.of_support_subset_isCompact (hK'c i)
      (subset_closure.trans (hsupp i)),
    fun i => (hsupp i).trans (self_subset_thickening (hδpos i) _), fun x => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ (c i).val.target
    · exact ((hζs i (c i)).contDiffAt ((c i).val.open_target.mem_nhds hz)).congr_of_eventuallyEq
        (chartFn_eventuallyEq _ hz)
    · have hzK : z ∉ K' i := fun h => hz ((hK'd i h).1.1)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(hK'c i).isClosed.isOpen_compl.mem_nhds hzK] with y hy
      exact image_eq_zero_of_notMem_tsupport fun h => hy (hsupp i h)
  · simp only [ζ, ← Finset.sum_mul]
    by_cases hx : x ∈ K0
    · rw [← finsum_eq_sum_of_fintype, θ.sum_eq_one hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

end TwistedDatum

end SGPT.Trace.TwistedL2
