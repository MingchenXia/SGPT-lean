import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes

set_option autoImplicit false

/-!
# Weighted limits of global mixed measures along decreasing smooth approximations

Let `M` be a compact complex manifold, `η₁, …, ηₙ` and `θ` closed real `(1,1)`-forms and `κ`
a closed real `(1,1)`-form (in applications a Kähler form). Let `zᵢ` be bounded `ηᵢ`-PSH
functions and `u` a bounded function, and suppose that

* `z_{k,i}` are chart-smooth `(ηᵢ + d_k κ)`-PSH functions decreasing to `zᵢ`,
* `u_k` are chart-smooth `(θ + d_k κ)`-PSH functions decreasing to `u`,

where `d_k` decreases to `0`. Then

  `∫_M u_k d(⋀ᵢ (ηᵢ + d_k κ + ddᶜ z_{k,i})) → ∫_M u d(⋀ᵢ (ηᵢ + ddᶜ zᵢ))`

(`tendsto_integral_globalMixedMeasure_of_antitone`). The right-hand side is the global mixed
(Bedford–Taylor) measure of the bounded tuple, the left-hand side that of the smooth one.

This is the global form of Bedford–Taylor's weighted convergence theorem for decreasing
smooth approximations (Błocki, *The complex Monge–Ampère operator in pluripotential theory*,
Thm. 2.2.1 and (2.2.2); here `BedfordTaylor.wClaim_of_pClaim BedfordTaylor.pClaim_all`).

*Proof.* A chart-smooth partition of unity subordinate to slot charts (charts carrying smooth
potentials `pᵢ`, `q`, `r` of `ηᵢ`, `κ`, `θ`) reduces the claim to one chart and a compactly
supported test `χ`. There the global measures are the transported Bedford–Taylor limits of the
corrected potentials, the slots `z_{k,i} + pᵢ + d_k (q + c)` and the weights
`u_k + r + d_k (q + c)` (with `q + c ≥ 0` on a relatively compact neighbourhood of the
support) are decreasing smooth plurisubharmonic approximations, and the smooth level-`k`
measure is the mixed density of its own slots. The corrections `r + d_k (q + c)` are
continuous and are removed with the unweighted convergence.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalWeightedDecreasingLimit

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar MixedMongeAmpere GlobalNonPluripolar BoundedGlobalProduct
open BedfordTaylor FirstPass.MongeAmpere GlobalSlotStokes

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Elementary helpers -/

/-- A product of a test supported in an open set with a function continuous there is
continuous. -/
theorem continuous_mul_of_tsupport_subset {U : Set (ComplexModel n)} (hU : IsOpen U)
    {φ g : ComplexModel n → ℝ} (hφ : Continuous φ) (hφU : tsupport φ ⊆ U)
    (hg : ContinuousOn g U) : Continuous fun y => φ y * g y :=
  continuous_of_continuousOn_of_eq_zero hU (isClosed_tsupport φ) hφU
    (hφ.continuousOn.mul hg) fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]

theorem tsupport_mul_subset {φ g : ComplexModel n → ℝ} :
    tsupport (fun y => φ y * g y) ⊆ tsupport φ :=
  tsupport_mul_subset_left

/-- A chart-smooth real function, coerced to `EReal`, is a bounded potential on a compact
manifold. -/
theorem isBoundedPotential_coe_of_continuous [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    IsBoundedPotential fun x => ((f x : ℝ) : EReal) := by
  obtain ⟨Q, hQ⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨-Q, Q, fun x => ?_⟩
  have hx := abs_le.mp (by simpa [Real.norm_eq_abs] using hQ x (mem_univ x))
  exact ⟨EReal.coe_le_coe_iff.mpr hx.1, EReal.coe_le_coe_iff.mpr hx.2⟩

/-! ### Slot charts with a potential for one more form -/

section Charts

variable {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}

/-- The same slot chart, read for the backgrounds `ηᵢ + d κ`: the potentials become
`pᵢ + d q`. -/
def shiftChart (J : GlobalSlotStokes.SlotChart η κ) (d : ℝ) :
    GlobalSlotStokes.SlotChart (fun i => η i + d • κ) κ where
  chart := J.chart
  domain := J.domain
  domain_le_target := J.domain_le_target
  potential i := fun z => J.potential i z + d • J.kahler z
  localPotential i := FirstPass.LocalPotentials.localPotential_add (J.localPotential i)
    (FirstPass.LocalPotentials.localPotential_smul J.kahlerLocal d)
  kahler := J.kahler
  kahlerLocal := J.kahlerLocal

/-- Every point lies in a slot chart on whose domain a further form `θ` has a smooth
potential. -/
theorem exists_mem_source_potential (η : Fin n → ClosedRealOneOneForm n M)
    (κ θ : ClosedRealOneOneForm n M) (x : M) :
    ∃ (J : GlobalSlotStokes.SlotChart η κ) (r : ComplexModel n → ℝ), x ∈ J.source ∧
      IsSmoothLocalPotential θ.val J.chart J.domain r := by
  obtain ⟨J, hJ⟩ := GlobalSlotStokes.SlotChart.exists_mem_source η κ x
  have hz : J.chart.val x ∈ J.chart.val.target := J.chart.val.map_source hJ.1
  obtain ⟨W, r, hzW, hr⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials θ J.chart (J.chart.val x) hz
  let D : Opens (ComplexModel n) := ⟨J.domain ∩ W, J.domain.isOpen.inter hr.1⟩
  have hDJ : (D : Set (ComplexModel n)) ⊆ J.domain := inter_subset_left
  have hDW : (D : Set (ComplexModel n)) ⊆ W := inter_subset_right
  refine ⟨{
    chart := J.chart
    domain := D
    domain_le_target := hDJ.trans J.domain_le_target
    potential := J.potential
    localPotential := fun i => (J.localPotential i).mono D.isOpen hDJ
    kahler := J.kahler
    kahlerLocal := J.kahlerLocal.mono D.isOpen hDJ }, r, ⟨hJ.1, hJ.2, hzW⟩,
    hr.mono D.isOpen hDW⟩

end Charts

/-! ### Smooth slots and weights in a chart -/

/-- The corrected chart function of a chart-smooth `(θ)`-PSH function is smooth PSD on any
open subset of a domain carrying a potential of `θ`. -/
theorem isSmoothPsdOn_chart {θ : ClosedRealOneOneForm n M} {f : M → ℝ}
    (hfs : ChartSmooth (n := n) f)
    (hf : ThetaPlurisubharmonic θ.val fun x => ((f x : ℝ) : EReal))
    (e : ComplexChart n M) {D : Opens (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e D ρ) {U : Opens (ComplexModel n)}
    (hUD : (U : Set (ComplexModel n)) ⊆ D) :
    IsSmoothPsdOn U fun y => f (e.val.symm y) + ρ y := by
  have hDt : (D : Set (ComplexModel n)) ⊆ e.val.target := hρ.2.1
  have hsm : ContDiffOn ℝ ∞ (fun y => f (e.val.symm y) + ρ y) U :=
    ((hfs e).mono (hUD.trans hDt)).add (hρ.2.2.1.mono hUD)
  refine UniformBoundedGlobalMass.isSmoothPsdOn_of_plurisubharmonicOn hsm ?_
  have hp := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hf e hρ
  have hfun : (fun y => chartFunction (fun x => ((f x : ℝ) : EReal)) e y + ((ρ y : ℝ) : EReal)) =
      fun y => ((f (e.val.symm y) + ρ y : ℝ) : EReal) := by
    funext y; simp [chartFunction, EReal.coe_add]
  rw [hfun] at hp
  exact hp.mono hUD

/-- Adding a constant keeps a smooth PSD function smooth PSD. -/
theorem isSmoothPsdOn_add_const {U : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : IsSmoothPsdOn U f) (a : ℝ) : IsSmoothPsdOn U fun y => f y + a := by
  refine ⟨hf.1.add contDiffOn_const, fun z hz => ?_⟩
  have h := complexHessian_sub_const f (-a) z
  have e : (fun y => f y - -a) = fun y => f y + a := by funext y; ring
  rw [e] at h
  rw [h]
  exact hf.2 z hz

/-- The level-`k` approximants in a chart: `g ∘ e⁻¹ + ρ + d (q + c)` is a decreasing smooth
PSD approximation of `gl ∘ e⁻¹ + ρ` on `U`, if `g` is `(θ + d κ)`-PSH, `ρ` and `q` are
potentials of `θ` and `κ`, and `q + c ≥ 0` on `U`. -/
theorem isDecApprox_chart [CompactSpace M] {θ κ : ClosedRealOneOneForm n M}
    (e : ComplexChart n M) {D : Opens (ComplexModel n)} {ρ q : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e D ρ) (hq : IsSmoothLocalPotential κ.val e D q)
    {U : Opens (ComplexModel n)} (hUD : (U : Set (ComplexModel n)) ⊆ D) {c : ℝ}
    (hc : ∀ y ∈ (U : Set (ComplexModel n)), 0 ≤ q y + c)
    {d : ℕ → ℝ} (hd : Antitone d) (hd0 : Tendsto d atTop (𝓝 0))
    {g : ℕ → M → ℝ} (hgs : ∀ k, ChartSmooth (n := n) (g k))
    (hg : ∀ k, ThetaPlurisubharmonic (θ + d k • κ).val fun x => ((g k x : ℝ) : EReal))
    (hganti : ∀ x, Antitone fun k => g k x) {gl : M → ℝ}
    (hglim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (gl x)))
    (hgb : ∃ Q : ℝ, ∀ x, |gl x| ≤ Q) :
    IsDecApprox U (fun y => gl (e.val.symm y) + ρ y)
      (fun k y => g k (e.val.symm y) + ρ y + d k * (q y + c)) := by
  have hd0' : ∀ k, 0 ≤ d k := hd.le_of_tendsto hd0
  refine ⟨fun k => ?_, fun y hy => ?_, fun y hy => ?_, fun K hK hKU => ?_⟩
  · have hpot : IsSmoothLocalPotential (θ + d k • κ).val e D fun z => ρ z + d k • q z :=
      FirstPass.LocalPotentials.localPotential_add hρ
        (FirstPass.LocalPotentials.localPotential_smul hq (d k))
    have h := isSmoothPsdOn_add_const (isSmoothPsdOn_chart (hgs k) (hg k) e hpot hUD) (d k * c)
    have e1 : (fun y => g k (e.val.symm y) + ρ y + d k * (q y + c)) =
        fun y => g k (e.val.symm y) + (ρ y + d k • q y) + d k * c := by
      funext y; simp only [smul_eq_mul]; ring
    show IsSmoothPsdOn U (fun y => g k (e.val.symm y) + ρ y + d k * (q y + c))
    rw [e1]
    exact h
  · intro i j hij
    have h1 := hganti (e.val.symm y) hij
    have h2 : d j * (q y + c) ≤ d i * (q y + c) := mul_le_mul_of_nonneg_right (hd hij) (hc y hy)
    simp only
    linarith
  · have h := ((hglim (e.val.symm y)).add_const (ρ y)).add
      ((hd0.mul_const (q y + c)))
    simpa using h
  · obtain ⟨Q, hQ⟩ := hgb
    have hρc : ContinuousOn ρ K := hρ.2.2.1.continuousOn.mono (hKU.trans hUD)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hρc
    refine ⟨-(Q + B), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := abs_le.mp (hQ (e.val.symm y))
    have h2 := abs_le.mp (by simpa [Real.norm_eq_abs] using hB y hy)
    simp only
    linarith [h1.1, h2.1]

/-! ### One chart -/

section Local

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}

omit [CompactSpace M] in
/-- Integration of a function vanishing off a slot chart against a global measure whose
restriction to the chart is a transported coordinate measure. -/
theorem integral_eq_integral_chart (J : GlobalSlotStokes.SlotChart η κ) {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (η i).val (u i)) {μ : Measure M}
    {ν : Measure (ComplexModel n)} (hν : ν (J.domain : Set (ComplexModel n))ᶜ = 0)
    (hμ : μ.restrict (J.source : Set M) = (J.patch u hu).pushMeasure ν)
    {F : M → ℝ} (hF : ∀ x, x ∉ (J.source : Set M) → F x = 0) :
    ∫ x, F x ∂μ = ∫ y, F (J.chart.val.symm y) ∂ν := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF, hμ]
  exact (J.patch u hu).integral_pushMeasure hν F

/-- **The weighted limit in one slot chart.** For a chart-smooth test `χ` supported in a slot
chart on whose domain `θ` has a potential, `∫ χ u_k dμ_k → ∫ χ u dμ`. -/
theorem tendsto_integral_mul_slotChart (J : GlobalSlotStokes.SlotChart η κ)
    {θ : ClosedRealOneOneForm n M} {r : ComplexModel n → ℝ}
    (hr : IsSmoothLocalPotential θ.val J.chart J.domain r)
    {z : Fin n → M → EReal} (hz : ∀ i, ThetaPlurisubharmonic (η i).val (z i))
    (hzb : ∀ i, IsBoundedPotential (z i))
    {d : ℕ → ℝ} (hd : Antitone d) (hd0 : Tendsto d atTop (𝓝 0))
    {zk : ℕ → Fin n → M → ℝ} (hzks : ∀ k i, ChartSmooth (n := n) (zk k i))
    (hzk : ∀ k i, ThetaPlurisubharmonic (η i + d k • κ).val fun x => ((zk k i x : ℝ) : EReal))
    (hzanti : ∀ i x, Antitone fun k => zk k i x)
    (hzlim : ∀ i x, Tendsto (fun k => zk k i x) atTop (𝓝 (z i x).toReal))
    {u : M → EReal} (hub : IsBoundedPotential u) {uk : ℕ → M → ℝ}
    (huks : ∀ k, ChartSmooth (n := n) (uk k))
    (huk : ∀ k, ThetaPlurisubharmonic (θ + d k • κ).val fun x => ((uk k x : ℝ) : EReal))
    (huanti : ∀ x, Antitone fun k => uk k x)
    (hulim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x).toReal))
    {χ : M → ℝ} (hχs : ChartSmooth (n := n) χ) (hχJ : tsupport χ ⊆ (J.source : Set M))
    (hχK : IsCompact (tsupport χ)) :
    Tendsto (fun k => ∫ x, χ x * uk k x ∂(globalMixedMeasure (fun i => η i + d k • κ)
        (fun i x => ((zk k i x : ℝ) : EReal)) (hzk k)))
      atTop (𝓝 (∫ x, χ x * (u x).toReal ∂(globalMixedMeasure η z hz))) := by
  classical
  set e := J.chart with he
  set D := J.domain with hD
  have hDt : (D : Set (ComplexModel n)) ⊆ e.val.target := J.domain_le_target
  -- the coordinate test and a relatively compact neighbourhood of its support
  obtain ⟨φ, hφs, hφc, hφD, hφeq, -⟩ := J.exists_coordinate_test hχs hχJ hχK
  have hφcont : Continuous φ := hφs.continuous
  obtain ⟨U₀, hU₀o, hφU₀, hU₀D, hU₀c⟩ :=
    exists_open_between_and_isCompact_closure hφc D.isOpen hφD
  set U : Opens (ComplexModel n) := ⟨U₀, hU₀o⟩ with hU_def
  have hU : RelativelyCompactIn U D := ⟨hU₀c, hU₀D⟩
  have hUD : (U : Set (ComplexModel n)) ⊆ D := subset_closure.trans hU₀D
  have hφU : tsupport φ ⊆ (U : Set (ComplexModel n)) := hφU₀
  -- the constant making `q + B` nonnegative on `U`
  obtain ⟨B, hB⟩ := hU₀c.exists_bound_of_continuousOn
    (J.kahlerLocal.2.2.1.continuousOn.mono hU₀D)
  have hc : ∀ y ∈ (U : Set (ComplexModel n)), 0 ≤ J.kahler y + B := fun y hy => by
    have := abs_le.mp (by simpa [Real.norm_eq_abs] using hB y (subset_closure hy))
    linarith [this.1]
  -- the bounded limits
  have hzbd : ∀ i, ∃ Q : ℝ, ∀ x, |(z i x).toReal| ≤ Q := fun i =>
    IsBoundedPotential.exists_abs_toReal_le (hzb i)
  have hubd : ∃ Q : ℝ, ∀ x, |(u x).toReal| ≤ Q := IsBoundedPotential.exists_abs_toReal_le hub
  -- the limit measure
  obtain ⟨ν, hν, hνeq⟩ := J.exists_isBTLimit hz hzb
  -- the level-`k` measures
  have hzkb : ∀ k i, IsBoundedPotential fun x => ((zk k i x : ℝ) : EReal) := fun k i =>
    isBoundedPotential_coe_of_continuous (ChartSmooth.continuous (hzks k i))
  have hνk' : ∀ k, ∃ μk : Measure (ComplexModel n),
      IsBTLimit D (fun i y => zk k i (e.val.symm y) + (J.potential i y + d k • J.kahler y)) μk ∧
      (globalMixedMeasure (fun i => η i + d k • κ) (fun i x => ((zk k i x : ℝ) : EReal))
        (hzk k)).restrict (J.source : Set M) =
        ((shiftChart J (d k)).patch (fun i x => ((zk k i x : ℝ) : EReal)) (hzk k)).pushMeasure μk := by
    intro k
    obtain ⟨μk, hμk, hμkeq⟩ := (shiftChart J (d k)).exists_isBTLimit (hzk k) (hzkb k)
    refine ⟨μk, hμk.congr fun i y _ => ?_, hμkeq⟩
    simp [shiftChart, EReal.toReal_coe, he]
  choose νk hνk hνkeq using hνk'
  -- the approximating families on `U`
  set s : Fin n → ComplexModel n → ℝ := fun i y => (z i (e.val.symm y)).toReal + J.potential i y
    with hs
  set F : Fin n → ℕ → ComplexModel n → ℝ :=
    fun i k y => zk k i (e.val.symm y) + J.potential i y + d k * (J.kahler y + B) with hF
  have hdec : ∀ i, IsDecApprox U (s i) (F i) := fun i =>
    isDecApprox_chart e (J.localPotential i) J.kahlerLocal hUD hc hd hd0
      (fun k => hzks k i) (fun k => hzk k i) (fun x => hzanti i x) (gl := fun x => (z i x).toReal)
      (hzlim i) (hzbd i)
  have hadm : IsAdmissible n U s F := ⟨hdec, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  set w : ComplexModel n → ℝ := fun y => (u (e.val.symm y)).toReal + r y with hw
  set G : ℕ → ComplexModel n → ℝ :=
    fun k y => uk k (e.val.symm y) + r y + d k * (J.kahler y + B) with hG
  have hGdec : IsDecApprox U w G :=
    isDecApprox_chart e hr J.kahlerLocal hUD hc hd hd0 huks huk huanti
      (gl := fun x => (u x).toReal) hulim hubd
  -- the weighted and unweighted Bedford–Taylor convergence on `U`
  have hνU0 : (ν.restrict (U : Set (ComplexModel n))) (U : Set (ComplexModel n))ᶜ = 0 := by
    rw [Measure.restrict_apply' U.isOpen.measurableSet]; simp
  have hνUf : ∀ K, IsCompact K → K ⊆ (U : Set (ComplexModel n)) →
      ν.restrict (U : Set (ComplexModel n)) K < ⊤ := fun K hK hKU =>
    lt_of_le_of_lt (Measure.restrict_le_self K) (hν.2.1 K hK (hKU.trans hUD))
  have hT : TendstoMixed U F (ν.restrict (U : Set (ComplexModel n))) :=
    hν.tendstoMixed_restrict hU hadm
  have hWC : WClaim n n := wClaim_of_pClaim pClaim_all
  have hWk := hWC U s (ν.restrict (U : Set (ComplexModel n))) hνU0 hνUf
    (fun F' hF' => hν.tendstoMixed_restrict hU hF') F hadm w G hGdec φ hφcont hφc hφU
  -- the corrections
  have hrU : ContinuousOn r U := hr.2.2.1.continuousOn.mono hUD
  have hqU : ContinuousOn (fun y => J.kahler y + B) U :=
    (J.kahlerLocal.2.2.1.continuousOn.mono hUD).add continuousOn_const
  have hφr : Continuous fun y => φ y * r y :=
    continuous_mul_of_tsupport_subset U.isOpen hφcont hφU hrU
  have hφq : Continuous fun y => φ y * (J.kahler y + B) :=
    continuous_mul_of_tsupport_subset U.isOpen hφcont hφU hqU
  have hTr := hT (fun y => φ y * r y) hφr (hφc.mul_right) (tsupport_mul_subset.trans hφU)
  have hTq := hT (fun y => φ y * (J.kahler y + B)) hφq (hφc.mul_right)
    (tsupport_mul_subset.trans hφU)
  -- the mixed densities
  set mD : ℕ → ComplexModel n → ℝ := fun k => mixedDensity fun i => F i k with hmD
  have hmDc : ∀ k, ContinuousOn (mD k) U := fun k =>
    continuousOn_mixedDensity fun i => ((hdec i).1 k).1
  have hint : ∀ k {ψ : ComplexModel n → ℝ}, Continuous ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (U : Set (ComplexModel n)) → Integrable fun y => ψ y * mD k y :=
    fun k _ hψ hψc hψU => integrable_mul_of_continuousOn (hmDc k) hψ hψc hψU
  have hukU : ∀ k, ContinuousOn (fun y => uk k (e.val.symm y)) U := fun k =>
    ((huks k) e).continuousOn.mono (hUD.trans hDt)
  have hφu : ∀ k, Continuous fun y => φ y * uk k (e.val.symm y) := fun k =>
    continuous_mul_of_tsupport_subset U.isOpen hφcont hφU (hukU k)
  have hφG : ∀ k, Continuous fun y => φ y * G k y := fun k =>
    continuous_mul_of_tsupport_subset U.isOpen hφcont hφU ((hGdec.1 k).1.continuousOn)
  -- the level-`k` measure is the mixed density of its smooth slots
  have hlevel : ∀ k, ∫ y, φ y * uk k (e.val.symm y) ∂(νk k) =
      ∫ y, φ y * uk k (e.val.symm y) * mD k y := by
    intro k
    set sk : Fin n → ComplexModel n → ℝ :=
      fun i y => zk k i (e.val.symm y) + (J.potential i y + d k • J.kahler y) with hsk
    have hskpsd : ∀ i, IsSmoothPsdOn U (sk i) := fun i =>
      isSmoothPsdOn_chart (hzks k i) (hzk k i) e ((shiftChart J (d k)).localPotential i) hUD
    have hconst : IsAdmissible n U sk fun i _ => sk i := by
      refine ⟨fun i => ⟨fun _ => hskpsd i, fun _ _ _ _ _ => le_rfl,
        fun _ _ => tendsto_const_nhds, fun K hK hKU => ?_⟩,
        fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((hskpsd i).1.continuousOn.mono hKU)
      refine ⟨-C, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have := abs_le.mp (by simpa [Real.norm_eq_abs] using hC y hy)
      linarith [this.1]
    have h := (hνk k).tendstoMixed hU hconst (fun y => φ y * uk k (e.val.symm y)) (hφu k)
      hφc.mul_right (tsupport_mul_subset.trans hφU)
    have heq := tendsto_nhds_unique tendsto_const_nhds h
    rw [← heq]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hh : mixedDensity (fun i => sk i) y = mD k y := by
      refine mixedDensity_congr_hessian fun i => ?_
      have e1 : F i k = fun y' => sk i y' - -(d k * B) := by
        funext y'; simp only [hF, hsk, smul_eq_mul]; ring
      rw [e1, complexHessian_sub_const]
    simp only [hh]
  -- splitting off the corrections
  have hsplit : ∀ k, ∫ y, φ y * uk k (e.val.symm y) * mD k y =
      (∫ y, φ y * G k y * mD k y) - (∫ y, φ y * r y * mD k y) -
        d k * ∫ y, φ y * (J.kahler y + B) * mD k y := by
    intro k
    have I1 := hint k (hφu k) hφc.mul_right (tsupport_mul_subset.trans hφU)
    have I2 := hint k hφr hφc.mul_right (tsupport_mul_subset.trans hφU)
    have I3 := hint k hφq hφc.mul_right (tsupport_mul_subset.trans hφU)
    have e1 : (fun y => φ y * G k y * mD k y) = fun y =>
        (φ y * uk k (e.val.symm y) * mD k y + φ y * r y * mD k y) +
          d k * (φ y * (J.kahler y + B) * mD k y) := by
      funext y; simp only [hG]; ring
    have e2 : ∫ y, φ y * G k y * mD k y = (∫ y, φ y * uk k (e.val.symm y) * mD k y) +
        (∫ y, φ y * r y * mD k y) + d k * ∫ y, φ y * (J.kahler y + B) * mD k y := by
      rw [e1, integral_add (f := fun y => φ y * uk k (e.val.symm y) * mD k y + φ y * r y * mD k y)
        (I1.add I2) (I3.const_mul (d k)), integral_add I1 I2, integral_const_mul]
    linarith
  have hlim := (hWk.sub hTr).sub (hd0.mul hTq)
  simp only [zero_mul, sub_zero] at hlim
  -- the limit value
  have hlimval : (∫ y, φ y * w y ∂(ν.restrict (U : Set (ComplexModel n)))) -
      ∫ y, φ y * r y ∂(ν.restrict (U : Set (ComplexModel n))) =
      ∫ y, φ y * (u (e.val.symm y)).toReal ∂ν := by
    rw [← integral_sub (hGdec.integrable_mul hνUf hφcont hφc hφU)
      (integrable_of_tsupport_subset hνUf hφr hφc.mul_right (tsupport_mul_subset.trans hφU))]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      simp [image_eq_zero_of_notMem_tsupport fun h => hy (hφU h)])]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hw]
    ring
  rw [hlimval] at hlim
  -- back to the manifold
  have hsrc : ∀ {g : M → ℝ} x, x ∉ (J.source : Set M) → χ x * g x = 0 := fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport fun h => hx (hχJ h)]
  have hae : ∀ (ρ : Measure (ComplexModel n)), ρ (D : Set (ComplexModel n))ᶜ = 0 →
      ∀ g : ComplexModel n → ℝ,
      ∫ y, χ (e.val.symm y) * g y ∂ρ = ∫ y, φ y * g y ∂ρ := fun ρ hρ g => by
    have hD' : ∀ᵐ y ∂ρ, y ∈ (D : Set (ComplexModel n)) := ae_iff.mpr hρ
    refine integral_congr_ae ?_
    filter_upwards [hD'] with y hy
    rw [hφeq hy]
  have hleft : ∀ k, ∫ x, χ x * uk k x ∂(globalMixedMeasure (fun i => η i + d k • κ)
      (fun i x => ((zk k i x : ℝ) : EReal)) (hzk k)) =
      ∫ y, φ y * uk k (e.val.symm y) * mD k y := by
    intro k
    rw [integral_eq_integral_chart (shiftChart J (d k)) (hzk k) (hνk k).1 (hνkeq k) (hsrc (g := uk k))]
    rw [← hlevel k]
    exact hae _ (hνk k).1 (fun y => uk k (e.val.symm y))
  have hright : ∫ x, χ x * (u x).toReal ∂(globalMixedMeasure η z hz) =
      ∫ y, φ y * (u (e.val.symm y)).toReal ∂ν := by
    rw [integral_eq_integral_chart J hz hν.1 hνeq (hsrc (g := fun x => (u x).toReal))]
    exact hae _ hν.1 (fun y => (u (e.val.symm y)).toReal)
  rw [hright]
  simp only [hleft, hsplit]
  exact hlim

end Local

/-! ### The global statement -/

section Global

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
/-- A bounded measurable function integrates as the sum of its products with a finite
partition of unity of bounded measurable functions. -/
theorem integral_eq_sum_mul {m : ℕ} {χ : Fin m → M → ℝ} (hχm : ∀ a, Measurable (χ a))
    (hχb : ∀ a, ∃ Q : ℝ, ∀ x, |χ a x| ≤ Q) (hsum : ∀ x, ∑ a, χ a x = 1)
    (ν : Measure M) [IsFiniteMeasure ν] {f : M → ℝ} (hf : Measurable f)
    (hfb : ∃ Q : ℝ, ∀ x, |f x| ≤ Q) :
    ∫ x, f x ∂ν = ∑ a, ∫ x, χ a x * f x ∂ν := by
  obtain ⟨Q, hQ⟩ := hfb
  have hint : ∀ a ∈ (Finset.univ : Finset (Fin m)), Integrable (fun x => χ a x * f x) ν := by
    intro a _
    obtain ⟨Qa, hQa⟩ := hχb a
    refine integrable_of_measurable_bounded ((hχm a).mul hf) (Q := Qa * Q) (fun x => ?_) ν
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hQa x) (hQ x) (abs_nonneg _) ((abs_nonneg _).trans (hQa x))
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [← Finset.sum_mul, hsum x, one_mul]

/-- **Weighted limit of global mixed measures along decreasing smooth approximations.**
Let `zᵢ` be bounded `ηᵢ`-PSH and `u` bounded. If chart-smooth `(ηᵢ + d_k κ)`-PSH functions
`z_{k,i}` decrease to `zᵢ` and chart-smooth `(θ + d_k κ)`-PSH functions `u_k` decrease to `u`,
where `d_k` decreases to `0`, then `∫ u_k dμ_k → ∫ u dμ` for the global mixed measures
`μ_k = ⋀ᵢ (ηᵢ + d_k κ + ddᶜ z_{k,i})` and `μ = ⋀ᵢ (ηᵢ + ddᶜ zᵢ)`. -/
theorem tendsto_integral_globalMixedMeasure_of_antitone
    {z : Fin n → M → EReal} (hz : ∀ i, ThetaPlurisubharmonic (η i).val (z i))
    (hzb : ∀ i, IsBoundedPotential (z i))
    {d : ℕ → ℝ} (hd : Antitone d) (hd0 : Tendsto d atTop (𝓝 0))
    {zk : ℕ → Fin n → M → ℝ} (hzks : ∀ k i, ChartSmooth (n := n) (zk k i))
    (hzk : ∀ k i, ThetaPlurisubharmonic (η i + d k • κ).val fun x => ((zk k i x : ℝ) : EReal))
    (hzanti : ∀ i x, Antitone fun k => zk k i x)
    (hzlim : ∀ i x, Tendsto (fun k => zk k i x) atTop (𝓝 (z i x).toReal))
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hub : IsBoundedPotential u)
    {uk : ℕ → M → ℝ} (huks : ∀ k, ChartSmooth (n := n) (uk k))
    (huk : ∀ k, ThetaPlurisubharmonic (θ + d k • κ).val fun x => ((uk k x : ℝ) : EReal))
    (huanti : ∀ x, Antitone fun k => uk k x)
    (hulim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x).toReal)) :
    Tendsto (fun k => ∫ x, uk k x ∂(globalMixedMeasure (fun i => η i + d k • κ)
        (fun i x => ((zk k i x : ℝ) : EReal)) (hzk k)))
      atTop (𝓝 (∫ x, (u x).toReal ∂(globalMixedMeasure η z hz))) := by
  classical
  choose J r hJ hr using fun x => exists_mem_source_potential η κ θ x
  obtain ⟨m, χ, idx, hsm, -, hsupp, hcpt, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n)
      (fun x => (J x).source) fun x => ⟨x, hJ x⟩
  have hχc : ∀ a, Continuous (χ a) := fun a => ChartSmooth.continuous (hsm a)
  have hχb : ∀ a, ∃ Q : ℝ, ∀ x, |χ a x| ≤ Q := fun a => by
    obtain ⟨Q, hQ⟩ := isCompact_univ.exists_bound_of_continuousOn (hχc a).continuousOn
    exact ⟨Q, fun x => by simpa [Real.norm_eq_abs] using hQ x (mem_univ x)⟩
  have hfin : IsFiniteMeasure (globalMixedMeasure η z hz) :=
    globalMixedMeasure_isFiniteMeasure_of_bounded hz hzb
  have hfink : ∀ k, IsFiniteMeasure (globalMixedMeasure (fun i => η i + d k • κ)
      (fun i x => ((zk k i x : ℝ) : EReal)) (hzk k)) := fun k =>
    globalMixedMeasure_isFiniteMeasure_of_bounded (hzk k) fun i =>
      isBoundedPotential_coe_of_continuous (ChartSmooth.continuous (hzks k i))
  have humeas : Measurable fun x => (u x).toReal :=
    measurable_of_tendsto_metrizable (fun k => (ChartSmooth.continuous (huks k)).measurable)
      (tendsto_pi_nhds.mpr hulim)
  have hukb : ∀ k, ∃ Q : ℝ, ∀ x, |uk k x| ≤ Q := fun k => by
    obtain ⟨Q, hQ⟩ :=
      isCompact_univ.exists_bound_of_continuousOn (ChartSmooth.continuous (huks k)).continuousOn
    exact ⟨Q, fun x => by simpa [Real.norm_eq_abs] using hQ x (mem_univ x)⟩
  rw [integral_eq_sum_mul (fun a => (hχc a).measurable) hχb hsum _ humeas
    (IsBoundedPotential.exists_abs_toReal_le hub)]
  have e : (fun k => ∫ x, uk k x ∂(globalMixedMeasure (fun i => η i + d k • κ)
      (fun i x => ((zk k i x : ℝ) : EReal)) (hzk k))) = fun k => ∑ a, ∫ x, χ a x * uk k x ∂(
        globalMixedMeasure (fun i => η i + d k • κ) (fun i x => ((zk k i x : ℝ) : EReal))
          (hzk k)) := by
    funext k
    exact integral_eq_sum_mul (fun a => (hχc a).measurable) hχb hsum _
      (ChartSmooth.continuous (huks k)).measurable (hukb k)
  rw [e]
  exact tendsto_finsetSum _ fun a _ =>
    tendsto_integral_mul_slotChart (J (idx a)) (hr (idx a)) hz hzb hd hd0 hzks hzk hzanti hzlim
      hub huks huk huanti hulim (hsm a) (hsupp a) (hcpt a)

end Global

end

end SGPT.Foundations.Analysis.Pending.GlobalWeightedDecreasingLimit
