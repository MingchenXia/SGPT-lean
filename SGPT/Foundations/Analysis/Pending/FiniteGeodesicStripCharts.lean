import SGPT.Foundations.Analysis.Pending.BedfordTaylorStripIBP
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
import SGPT.Foundations.Analysis.Pending.PatchOverlap
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation

set_option autoImplicit false

/-!
# Gluing chartwise integrations by parts on `X × (strip)` along a maximal subgeodesic

Let `U` be a curve of `θ`-PSH potentials on a complex manifold `X` with uniformly bounded slices,
and `φ` a bounded `θ`-PSH potential. A **strip chart** (`StripChart`) is a chart `e` of `X`, an
open `W ⊆ e(X)` with a smooth local potential `ρ` of `θ`, on which the corrected complexification
`h(z, τ) = U_{Re τ}(e⁻¹ z) + ρ(z)` is plurisubharmonic on `W × {0 < Re τ < 1}` and maximal:
`(ddᶜh)ⁿ⁺¹ = 0` (`FiniteGeodesicMaximality`). There `Φ(z, τ) = φ(e⁻¹ z) + ρ(z)` is another
locally bounded plurisubharmonic function with `(ddᶜΦ)ⁿ⁺¹ = 0` (`isBTLimit_comp_stripFst_eq_zero`).

* `chartRead e f` — a function on `X` read in the chart `e`, extended by `0` (smooth with compact
  support when `f` is chart-smooth with compact support in the chart source).
* `exists_chartSmooth_eq_one_nhds` — chart-smooth cutoffs equal to `1` near a compact set.
* `StripChart.defectPairing_transport` — **transport of pairings between two strip charts**:
  on the lifted overlap the slots change by the pluriharmonic gauge `ρ_b ∘ t - ρ_a`, so pairings
  of weights supported in the overlap agree (`IsDefectPairing.comp_biholomorphic`).
* `sum_sum_defectPairing_eq_zero` — **the gluing identity**: for a partition of unity `(χ_a)` of
  `X` subordinate to strip charts `J_a` and `ψ ∈ C_c^∞(strip)`,

    `Σ_j Σ_a ∫ χ_a (U - φ) ddᶜψ(τ) ∧ (ddᶜh_a)ʲ ∧ (ddᶜΦ_a)ⁿ⁻ʲ = 0`,

  the pairings being read in the strip chart `J_a`. Write `ψ = Σ_b χ_b ψ`, cut the weight
  `χ_a (U - φ)` off near `supp χ_b` (`IsDefectPairing.congr_weight'`), transport the `(a, b)` term to
  `J_b`, sum over `a` there (`Σ_a χ_a = 1`) and apply the local integration by parts
  `BedfordTaylorStripIBP.sum_defectPairing_endpointTuple_eq_zero` in `J_b`.

Source: Xia, SGPT, proof of Proposition 4.3.3 (`xia-sgpt:page-0171`): `ddᶜ_τ E(U_τ) = 0`, the
current computation on `X × (strip)`.
-/

open Set Filter MeasureTheory TopologicalSpace
open Function (support mem_support)
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts

open FirstPass FirstPass.MongeAmpere FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
  BedfordTaylor BedfordTaylorDefectPairing BedfordTaylorTimeSlot MixedDensityRankOneSlot
  BedfordTaylorFibreSlicing BedfordTaylorStripCovariance BedfordTaylorStripIBP
  FiniteGeodesicMaximality GlobalSlotStokes PatchOverlap BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-! ### Reading functions of `X` in a chart -/

section ChartRead

/-- `f` read in the chart `e`, extended by `0` off the chart target. -/
def chartRead (e : ComplexChart n M) (f : M → ℝ) : ComplexModel n → ℝ :=
  (e.val.target : Set (ComplexModel n)).indicator fun z => f (e.val.symm z)

variable {e : ComplexChart n M} {f : M → ℝ}

theorem chartRead_of_mem {z : ComplexModel n} (hz : z ∈ e.val.target) :
    chartRead e f z = f (e.val.symm z) :=
  indicator_of_mem hz _

theorem chartRead_of_notMem {z : ComplexModel n} (hz : z ∉ e.val.target) : chartRead e f z = 0 :=
  indicator_of_notMem hz _

theorem support_chartRead_subset (e : ComplexChart n M) (f : M → ℝ) :
    support (chartRead e f) ⊆ e.val '' tsupport f := by
  intro z hz
  by_cases hzt : z ∈ e.val.target
  · rw [mem_support, chartRead_of_mem hzt] at hz
    exact ⟨e.val.symm z, subset_tsupport f hz, e.val.right_inv hzt⟩
  · exact absurd (chartRead_of_notMem hzt) hz

theorem image_tsupport_subset_target (hfs : tsupport f ⊆ e.val.source) :
    e.val '' tsupport f ⊆ e.val.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact e.val.map_source (hfs hx)

theorem isCompact_image_tsupport (hfc : IsCompact (tsupport f)) (hfs : tsupport f ⊆ e.val.source) :
    IsCompact (e.val '' tsupport f) :=
  hfc.image_of_continuousOn (e.val.continuousOn.mono hfs)

theorem tsupport_chartRead_subset (hfc : IsCompact (tsupport f))
    (hfs : tsupport f ⊆ e.val.source) : tsupport (chartRead e f) ⊆ e.val '' tsupport f :=
  closure_minimal (support_chartRead_subset e f) (isCompact_image_tsupport hfc hfs).isClosed

theorem hasCompactSupport_chartRead (hfc : IsCompact (tsupport f))
    (hfs : tsupport f ⊆ e.val.source) : HasCompactSupport (chartRead e f) :=
  (isCompact_image_tsupport hfc hfs).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_chartRead_subset hfc hfs)

theorem chartRead_sum {ι : Type*} (s : Finset ι) (g : ι → M → ℝ) (z : ComplexModel n) :
    chartRead e (fun x => ∑ a ∈ s, g a x) z = ∑ a ∈ s, chartRead e (g a) z := by
  by_cases hz : z ∈ e.val.target
  · simp only [chartRead_of_mem hz]
  · simp only [chartRead_of_notMem hz, Finset.sum_const_zero]

theorem chartRead_transition {e' : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ e.val.target) (hx : e.val.symm z ∈ e'.val.source) :
    chartRead e' f (e'.val (e.val.symm z)) = chartRead e f z := by
  rw [chartRead_of_mem (e'.val.map_source hx), e'.val.left_inv hx, chartRead_of_mem hz]

/-- Points of the target in the closed support of `chartRead e f` come from `tsupport f`. -/
theorem symm_mem_tsupport_of_mem_tsupport_chartRead {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzs : z ∈ tsupport (chartRead e f)) : e.val.symm z ∈ tsupport f := by
  by_contra h
  have hev : f =ᶠ[𝓝 (e.val.symm z)] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp h
  have hc : ContinuousAt e.val.symm z := e.val.continuousAt_symm hz
  have hev' : chartRead e f =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hc.eventually hev, e.val.open_target.mem_nhds hz] with y hy hyt
    rw [chartRead_of_mem hyt]
    exact hy
  exact (notMem_tsupport_iff_eventuallyEq.mpr hev') hzs

variable [IsComplexManifold n M]

theorem contDiffOn_chartRead (hf : ChartSmooth (n := n) f) (e : ComplexChart n M) :
    ContDiffOn ℝ ∞ (chartRead e f) e.val.target :=
  (hf e).congr fun _ hz => chartRead_of_mem hz

theorem contDiff_chartRead (hf : ChartSmooth (n := n) f) (hfc : IsCompact (tsupport f))
    (hfs : tsupport f ⊆ e.val.source) : ContDiff ℝ ∞ (chartRead e f) := by
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hz : z ∈ e.val.target
  · exact (contDiffOn_chartRead hf e).contDiffAt (e.val.open_target.mem_nhds hz)
  · have hzK : z ∉ e.val '' tsupport f := fun h => hz (image_tsupport_subset_target hfs h)
    have hev : chartRead e f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isCompact_image_tsupport hfc hfs).isClosed.isOpen_compl.mem_nhds hzK]
        with y hy
      by_contra h
      exact hy (support_chartRead_subset e f h)
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem continuous_chartRead (hf : ChartSmooth (n := n) f) (hfc : IsCompact (tsupport f))
    (hfs : tsupport f ⊆ e.val.source) : Continuous (chartRead e f) :=
  (contDiff_chartRead hf hfc hfs).continuous

end ChartRead

variable [IsComplexManifold n M]

/-! ### Cutoffs -/

section Cutoff

/-- A chart-smooth cutoff with compact support in an open set `S`, equal to `1` near a compact
`K ⊆ S`. -/
theorem exists_chartSmooth_eq_one_nhds {K : Set M} (hK : IsCompact K) (S : Opens M)
    (hKS : K ⊆ S) :
    ∃ ζ : M → ℝ, ChartSmooth (n := n) ζ ∧ IsCompact (tsupport ζ) ∧ tsupport ζ ⊆ (S : Set M) ∧
      ∃ N : Set M, IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ζ x = 1 := by
  classical
  choose h hsm hnonneg _ hsupp hcpt hone using fun x : K =>
    ChartPartition.exists_chartSmooth_bump (n := n) (x : M) S (hKS x.2)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => interior {y | h x y = 1})
    (fun _ => isOpen_interior) fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hone ⟨x, hx⟩)⟩
  set H : M → ℝ := fun y => ∑ x ∈ t, h x y with hH
  set T : Set M := ⋃ x ∈ t, tsupport (h x) with hT
  have hTc : IsCompact T := t.isCompact_biUnion fun x _ => hcpt x
  have hsuppT : support (fun y => Real.smoothTransition (H y)) ⊆ T := by
    intro y hy
    by_contra hyT
    apply hy
    have hH0 : H y = 0 := Finset.sum_eq_zero fun x hx => by
      by_contra hne
      exact hyT (mem_biUnion hx (subset_tsupport _ hne))
    simp [hH0]
  refine ⟨fun y => Real.smoothTransition (H y), fun e => ?_, ?_, ?_,
    ⋃ x ∈ t, interior {y | h x y = 1}, isOpen_biUnion fun _ _ => isOpen_interior, ht,
    fun y hy => ?_⟩
  · exact Real.smoothTransition.contDiff.comp_contDiffOn
      (ContDiffOn.sum fun x _ => hsm x e)
  · exact hTc.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hsuppT hTc.isClosed)
  · exact (closure_minimal hsuppT hTc.isClosed).trans (iUnion₂_subset fun x _ => hsupp x)
  · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    have h1' : y ∈ {y | h x y = 1} := interior_subset hyx
    have h1 : h x y = 1 := h1'
    refine Real.smoothTransition.one_of_one_le ?_
    calc (1 : ℝ) = h x y := h1.symm
      _ ≤ H y := Finset.single_le_sum (fun x' _ => hnonneg x' y) hx

end Cutoff

/-! ### Product cutoffs on `ℂⁿ × ℂ` -/

section StripCutoff

theorem stripModelEquiv_snd (q : ComplexModel (n + 1)) :
    (stripModelEquiv n q).2 = q (Fin.last n) := by
  have h := stripModelEquiv_symm_apply_last (stripModelEquiv n q).1 (stripModelEquiv n q).2
  rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- `q = (z, τ) ↦ c(z) ζ(τ)`. -/
def stripCutoff (c : ComplexModel n → ℝ) (ζ : ℂ → ℝ) : ComplexModel (n + 1) → ℝ :=
  fun q => c (stripFst n q) * ζ (q (Fin.last n))

theorem continuous_stripCutoff {c : ComplexModel n → ℝ} {ζ : ℂ → ℝ} (hc : Continuous c)
    (hζ : Continuous ζ) : Continuous (stripCutoff c ζ) :=
  (hc.comp (stripFst n).continuous).mul (hζ.comp (lastCoordinate n).continuous)

theorem contDiff_stripCutoff {c : ComplexModel n → ℝ} {ζ : ℂ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hζ : ContDiff ℝ ∞ ζ) : ContDiff ℝ ∞ (stripCutoff c ζ) :=
  (hc.comp ((stripFst n).restrictScalars ℝ).contDiff).mul (hζ.comp (lastCoordinate n).contDiff)

theorem support_stripCutoff_subset (c : ComplexModel n → ℝ) (ζ : ℂ → ℝ) :
    support (stripCutoff c ζ) ⊆
      stripModelEquiv n ⁻¹' (tsupport c ×ˢ tsupport ζ) := by
  intro q hq
  have h1 : c (stripFst n q) ≠ 0 := left_ne_zero_of_mul hq
  have h2 : ζ (q (Fin.last n)) ≠ 0 := right_ne_zero_of_mul hq
  refine ⟨subset_tsupport c h1, ?_⟩
  rw [stripModelEquiv_snd]
  exact subset_tsupport ζ h2

theorem isCompact_stripModelEquiv_preimage {K : Set (ComplexModel n × ℂ)} (hK : IsCompact K) :
    IsCompact (stripModelEquiv n ⁻¹' K) := by
  have h := hK.image (stripModelEquiv n).symm.continuous
  rwa [ContinuousLinearEquiv.image_symm_eq_preimage] at h

theorem tsupport_stripCutoff_subset {c : ComplexModel n → ℝ} {ζ : ℂ → ℝ}
    (hc : HasCompactSupport c) (hζ : HasCompactSupport ζ) :
    tsupport (stripCutoff c ζ) ⊆ stripModelEquiv n ⁻¹' (tsupport c ×ˢ tsupport ζ) :=
  closure_minimal (support_stripCutoff_subset c ζ)
    (isCompact_stripModelEquiv_preimage (hc.prod hζ)).isClosed

theorem hasCompactSupport_stripCutoff {c : ComplexModel n → ℝ} {ζ : ℂ → ℝ}
    (hc : HasCompactSupport c) (hζ : HasCompactSupport ζ) : HasCompactSupport (stripCutoff c ζ) :=
  (isCompact_stripModelEquiv_preimage (hc.prod hζ)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_stripCutoff_subset hc hζ)

theorem tsupport_stripCutoff_subset_stripLift {c : ComplexModel n → ℝ} {ζ : ℂ → ℝ}
    (hc : HasCompactSupport c) (hζ : HasCompactSupport ζ) {A : Opens (ComplexModel n)}
    {S : Set ℂ} (hS : IsOpen S) (hcA : tsupport c ⊆ A) (hζS : tsupport ζ ⊆ S) :
    tsupport (stripCutoff c ζ) ⊆ stripLift A S hS := fun _ hq =>
  ⟨hcA (tsupport_stripCutoff_subset hc hζ hq).1, hζS (tsupport_stripCutoff_subset hc hζ hq).2⟩

theorem tsupport_stripCutoff_subset_fst (c : ComplexModel n → ℝ) (ζ : ℂ → ℝ) :
    tsupport (stripCutoff c ζ) ⊆ stripFst n ⁻¹' tsupport c :=
  closure_minimal (fun _ hq => subset_tsupport c (left_ne_zero_of_mul hq))
    ((isClosed_tsupport c).preimage (stripFst n).continuous)

theorem stripCutoff_stripMap (c c' : ComplexModel n → ℝ) (ζ : ℂ → ℝ)
    (t : ComplexModel n → ComplexModel n) (q : ComplexModel (n + 1))
    (hc : c' (t (stripFst n q)) = c (stripFst n q)) :
    stripCutoff c' ζ (stripMap t q) = stripCutoff c ζ q := by
  have hlast : stripMap t q (Fin.last n) = q (Fin.last n) := by
    rw [← stripModelEquiv_snd, ← stripModelEquiv_snd, stripModelEquiv_stripMap]
  simp only [stripCutoff, stripFst_stripMap, hlast, hc]

end StripCutoff

/-! ### Pairing values only see the slot function on the domain -/

theorem defectPairing_congr_slot {N : ℕ} {Ω : Opens (ComplexModel N)}
    {v : Fin N → ComplexModel N → ℝ} {i₀ : Fin N} {G G' F : ComplexModel N → ℝ}
    (hF : IsBoundedTest F) (hG : EqOn G G' Ω) :
    defectPairing Ω v i₀ G F = defectPairing Ω v i₀ G' F := by
  classical
  by_cases h : ∃ I, IsDefectPairing Ω v i₀ G F I
  · obtain ⟨I, hI⟩ := h
    rw [defectPairing_eq hF hI,
      defectPairing_eq hF (IsDefectPairing.congr (fun _ _ => fun _ _ => rfl) hG hI)]
  · have h' : ¬ ∃ I, IsDefectPairing Ω v i₀ G' F I := fun ⟨I, hI⟩ =>
      h ⟨I, IsDefectPairing.congr (fun _ _ => fun _ _ => rfl) hG.symm hI⟩
    unfold defectPairing
    rw [dif_neg h, dif_neg h']

/-! ### Strip charts -/

/-- A **strip chart** of a curve `U` of `θ`-PSH potentials: a chart, an open set of its target
with a smooth local potential `ρ` of `θ`, on which the corrected complexification
`(z, τ) ↦ U_{Re τ}(e⁻¹ z) + ρ(z)` is plurisubharmonic on `W × {0 < Re τ < 1}` and maximal. -/
structure StripChart (θ : ClosedRealOneOneForm n M) (U : ℝ → M → EReal) where
  chart : ComplexChart n M
  domain : Opens (ComplexModel n)
  potential : ComplexModel n → ℝ
  localPotential : IsSmoothLocalPotential θ.val chart domain potential
  psh : PlurisubharmonicOn (subgeodesicChartFunction U chart potential)
    (geodesicChartDomain (domain : Set (ComplexModel n)))
  maximal : ∀ μ : Measure (ComplexModel (n + 1)),
    IsBTLimit (modelStripOpens (domain : Set (ComplexModel n)) domain.isOpen)
      (fun _ => modelChartFunction U chart potential) μ → μ = 0

namespace StripChart

variable {θ : ClosedRealOneOneForm n M} {U : ℝ → M → EReal} (J : StripChart θ U)

/-- The manifold neighbourhood `e⁻¹(W)`. -/
def region : Opens M :=
  ⟨J.chart.val.source ∩ J.chart.val ⁻¹' J.domain,
    J.chart.val.isOpen_inter_preimage J.domain.isOpen⟩

theorem mem_region {x : M} :
    x ∈ J.region ↔ x ∈ J.chart.val.source ∧ J.chart.val x ∈ J.domain := Iff.rfl

theorem domain_subset_target : (J.domain : Set (ComplexModel n)) ⊆ J.chart.val.target :=
  J.localPotential.2.1

theorem image_subset_domain {K : Set M} (hK : K ⊆ J.region) :
    J.chart.val '' K ⊆ J.domain := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hK hx).2

/-- The strip `W × {0 < Re τ < 1}`, read in `ℂⁿ⁺¹`. -/
def strip : Opens (ComplexModel (n + 1)) :=
  stripLift J.domain complexTimeStrip isOpen_complexTimeStrip

theorem strip_eq : J.strip = modelStripOpens (J.domain : Set (ComplexModel n)) J.domain.isOpen :=
  rfl

theorem mem_strip {q : ComplexModel (n + 1)} :
    q ∈ J.strip ↔ stripFst n q ∈ J.domain ∧ (stripModelEquiv n q).2 ∈ complexTimeStrip :=
  Iff.rfl

/-- The corrected complexification `h(z, τ) = U_{Re τ}(e⁻¹ z) + ρ(z)`. -/
def liftCurve : ComplexModel (n + 1) → ℝ := modelChartFunction U J.chart J.potential

/-- The corrected model potential `φ(e⁻¹ z) + ρ(z)` on the chart domain. -/
def modelFn (φ : M → EReal) : ComplexModel n → ℝ :=
  fun z => (φ (J.chart.val.symm z)).toReal + J.potential z

/-- `Φ(z, τ) = φ(e⁻¹ z) + ρ(z)`. -/
def liftModel (φ : M → EReal) : ComplexModel (n + 1) → ℝ := fun q => J.modelFn φ (stripFst n q)

variable {A B : ℝ}

theorem liftCurve_eq
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    {q : ComplexModel (n + 1)} (hq : q ∈ J.strip) :
    J.liftCurve q = (U (q (Fin.last n)).re (J.chart.val.symm (stripFst n q))).toReal +
      J.potential (stripFst n q) := by
  have ht : (stripModelEquiv n q).2.re ∈ Ioo (0 : ℝ) 1 := hq.2
  obtain ⟨c, hc, -, -⟩ := exists_eq_coe_of_bounded hbd ht (J.chart.val.symm (stripModelEquiv n q).1)
  rw [← stripModelEquiv_snd, stripFst_apply]
  simp only [liftCurve, modelChartFunction, subgeodesicChartFunction, chartFunction, hc]
  rw [← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]

theorem isLocallyBoundedPshOn_liftCurve
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal)) :
    IsLocallyBoundedPshOn J.strip J.liftCurve :=
  isLocallyBoundedPshOn_modelChartFunction hbd J.chart J.domain.isOpen
    J.localPotential.2.2.1.continuousOn J.psh

theorem isLocallyBoundedPshOn_modelFn {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ.val φ)
    (hφb : IsBoundedPotential φ) : IsLocallyBoundedPshOn J.domain (J.modelFn φ) := by
  have hpsh := ThetaPlurisubharmonic.corrected_plurisubharmonicOn hφ J.chart J.localPotential
  obtain ⟨Q, hQ⟩ := IsBoundedPotential.exists_abs_toReal_le hφb
  have hcoe : (fun z => ((J.modelFn φ z : ℝ) : EReal)) =
      fun z => chartFunction φ J.chart z + (J.potential z : EReal) := by
    funext z
    simp only [modelFn, chartFunction]
    rw [EReal.coe_add, EReal.coe_toReal (hφb.ne_top _) (hφb.ne_bot _)]
  refine ⟨by rw [hcoe]; exact hpsh, fun z hz => ?_⟩
  have hρ0 : ContinuousAt J.potential z :=
    J.localPotential.2.2.1.continuousOn.continuousAt (J.domain.isOpen.mem_nhds hz)
  have hnb : {y | |J.potential y - J.potential z| < 1} ∈ 𝓝 z := by
    filter_upwards [hρ0 (Metric.ball_mem_nhds (J.potential z) one_pos)] with y hy
    simpa [Metric.mem_ball, Real.dist_eq] using hy
  obtain ⟨O, hOsub, hOopen, hzO⟩ := mem_nhds_iff.mp hnb
  refine ⟨J.domain ⊓ ⟨O, hOopen⟩, ⟨hz, hzO⟩, inf_le_left, Q + (|J.potential z| + 1),
    fun w hw => ?_⟩
  have hρw : |J.potential w - J.potential z| < 1 := hOsub hw.2
  have hρabs : |J.potential w| ≤ |J.potential z| + 1 := by
    have := abs_sub_abs_le_abs_sub (J.potential w) (J.potential z)
    linarith
  calc |J.modelFn φ w| ≤ |(φ (J.chart.val.symm w)).toReal| + |J.potential w| := abs_add_le _ _
    _ ≤ Q + (|J.potential z| + 1) := add_le_add (hQ _) hρabs

theorem isLocallyBoundedPshOn_comp_stripFst {D : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn D f) (S : Set ℂ) (hS : IsOpen S) :
    IsLocallyBoundedPshOn (stripLift D S hS) fun q => f (stripFst n q) := by
  refine ⟨(hf.1.comp_continuousLinearMap (stripFst n)).mono fun q hq => hq.1, fun q hq => ?_⟩
  obtain ⟨V, hzV, hVD, C, hC⟩ := hf.2 _ hq.1
  exact ⟨stripLift V S hS, ⟨hzV, hq.2⟩, stripLift_mono hVD S hS, C, fun w hw => hC _ hw.1⟩

theorem isLocallyBoundedPshOn_liftModel {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ.val φ)
    (hφb : IsBoundedPotential φ) : IsLocallyBoundedPshOn J.strip (J.liftModel φ) :=
  isLocallyBoundedPshOn_comp_stripFst (J.isLocallyBoundedPshOn_modelFn hφ hφb) _ _

/-- **Maximality** of the corrected complexification. -/
theorem isBTLimit_liftCurve
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal)) :
    IsBTLimit J.strip (fun _ => J.liftCurve) 0 := by
  obtain ⟨μ, hμ⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
    fun _ : Fin (n + 1) => J.isLocallyBoundedPshOn_liftCurve hbd
  have h0 : μ = 0 := J.maximal μ hμ
  rw [h0] at hμ
  exact hμ

/-- `(ddᶜΦ)ⁿ⁺¹ = 0`: `Φ` does not depend on `τ`. -/
theorem isBTLimit_liftModel {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ.val φ)
    (hφb : IsBoundedPotential φ) : IsBTLimit J.strip (fun _ => J.liftModel φ) 0 :=
  isBTLimit_comp_stripFst_eq_zero isOpen_complexTimeStrip (u := fun _ => J.modelFn φ)
    fun _ => J.isLocallyBoundedPshOn_modelFn hφ hφb

/-- The strip chart as a patch of the constant tuple `φ` (to use `PatchOverlap`). -/
def patch {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ.val φ) :
    Patch (fun _ : Fin n => θ) (fun _ => φ) where
  chart := J.chart
  domain := J.domain
  domain_le_target := J.domain_subset_target
  potential := fun _ => J.potential
  localPotential := fun _ => J.localPotential
  plurisubharmonic := fun _ =>
    ThetaPlurisubharmonic.corrected_plurisubharmonicOn hφ J.chart J.localPotential

end StripChart

/-! ### Transport between two strip charts -/

section Transport

variable {θ : ClosedRealOneOneForm n M} {U : ℝ → M → EReal} {φ : M → EReal} {A B : ℝ}

/-- The overlap of two strip charts, lifted to the strip and read in the first one. -/
def overlapStrip (Ja Jb : StripChart θ U) (hφ : ThetaPlurisubharmonic θ.val φ) :
    Opens (ComplexModel (n + 1)) :=
  stripLift (overlapDomain (Ja.patch hφ) (Jb.patch hφ)) complexTimeStrip isOpen_complexTimeStrip

theorem overlapStrip_le (Ja Jb : StripChart θ U) (hφ : ThetaPlurisubharmonic θ.val φ) :
    overlapStrip Ja Jb hφ ≤ Ja.strip := fun _ hq => ⟨hq.1.1, hq.2⟩

theorem symm_transition {Ja Jb : StripChart θ U} {hφ : ThetaPlurisubharmonic θ.val φ}
    {z : ComplexModel n} (hz : z ∈ overlapDomain (Ja.patch hφ) (Jb.patch hφ)) :
    Jb.chart.val.symm (transition (Ja.patch hφ) (Jb.patch hφ) z) = Ja.chart.val.symm z :=
  Jb.chart.val.left_inv hz.2.1

theorem stripMap_last (t : ComplexModel n → ComplexModel n) (q : ComplexModel (n + 1)) :
    stripMap t q (Fin.last n) = q (Fin.last n) := by
  rw [← stripModelEquiv_snd, ← stripModelEquiv_snd, stripModelEquiv_stripMap]

theorem stripMap_mem_strip {Ja Jb : StripChart θ U} {hφ : ThetaPlurisubharmonic θ.val φ}
    {q : ComplexModel (n + 1)} (hq : q ∈ overlapStrip Ja Jb hφ) :
    stripMap (transition (Ja.patch hφ) (Jb.patch hφ)) q ∈ Jb.strip := by
  refine ⟨?_, ?_⟩
  · rw [stripModelEquiv_stripMap]
    exact hq.1.2.2
  · rw [stripModelEquiv_stripMap]
    exact hq.2

theorem liftCurve_stripMap
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    {Ja Jb : StripChart θ U} {hφ : ThetaPlurisubharmonic θ.val φ} {q : ComplexModel (n + 1)}
    (hq : q ∈ overlapStrip Ja Jb hφ) :
    Jb.liftCurve (stripMap (transition (Ja.patch hφ) (Jb.patch hφ)) q) =
      Ja.liftCurve q + (Jb.potential (transition (Ja.patch hφ) (Jb.patch hφ) (stripFst n q)) -
        Ja.potential (stripFst n q)) := by
  rw [Jb.liftCurve_eq hbd (stripMap_mem_strip hq), Ja.liftCurve_eq hbd (overlapStrip_le _ _ _ hq),
    stripFst_stripMap, stripMap_last, symm_transition (z := stripFst n q) hq.1]
  ring

theorem liftModel_stripMap {Ja Jb : StripChart θ U} {hφ : ThetaPlurisubharmonic θ.val φ}
    {q : ComplexModel (n + 1)} (hq : q ∈ overlapStrip Ja Jb hφ) :
    Jb.liftModel φ (stripMap (transition (Ja.patch hφ) (Jb.patch hφ)) q) =
      Ja.liftModel φ q + (Jb.potential (transition (Ja.patch hφ) (Jb.patch hφ) (stripFst n q)) -
        Ja.potential (stripFst n q)) := by
  simp only [StripChart.liftModel, StripChart.modelFn]
  rw [stripFst_stripMap, symm_transition (z := stripFst n q) hq.1]
  ring

/-- The transported difference of the two local potentials is pluriharmonic. -/
theorem isSmoothPluriharmonicOn_potential_transition (Ja Jb : StripChart θ U)
    (hφ : ThetaPlurisubharmonic θ.val φ) :
    IsSmoothPluriharmonicOn (overlapDomain (Ja.patch hφ) (Jb.patch hφ))
      (fun z => Jb.potential (transition (Ja.patch hφ) (Jb.patch hφ) z) - Ja.potential z) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hτ : ContDiffOn ℂ ∞ (transition (Ja.patch hφ) (Jb.patch hφ))
        (overlapDomain (Ja.patch hφ) (Jb.patch hφ)) :=
      (PatchOverlap.isBiholomorphicPair (Ja.patch hφ) (Jb.patch hφ)).holo
    have hq : ContDiffOn ℝ ∞ Jb.potential Jb.domain := Jb.localPotential.2.2.1
    have hp : ContDiffOn ℝ ∞ Ja.potential (overlapDomain (Ja.patch hφ) (Jb.patch hφ)) :=
      Ja.localPotential.2.2.1.mono (overlapDomain_le (Ja.patch hφ) (Jb.patch hφ))
    refine ⟨(hq.comp (hτ.restrict_scalars ℝ)
      (transition_mapsTo_domain (Ja.patch hφ) (Jb.patch hφ))).sub hp, fun z _ => ?_⟩
    ext i
    exact i.elim0
  · exact PatchOverlap.isSmoothPluriharmonicOn_potential_sub (Ja.patch hφ) (Jb.patch hφ) ⟨0, hn⟩

/-- **Transport of pairings between two strip charts.** On the lifted overlap, the slots of
`J_b` read in `J_a` are those of `J_a` plus the pluriharmonic gauge `ρ_b ∘ t - ρ_a`; pairings of
weights supported in the overlap agree. -/
theorem defectPairing_transport
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : ThetaPlurisubharmonic θ.val φ) (hφb : IsBoundedPotential φ) (Ja Jb : StripChart θ U)
    (j : ℕ) {Ga Gb Fa Fb : ComplexModel (n + 1) → ℝ} (hGb : ContDiffOn ℝ ∞ Gb Jb.strip)
    (hFa : IsBoundedTest Fa) (hFb : IsBoundedTest Fb) (hFaA : tsupport Fa ⊆ overlapStrip Ja Jb hφ)
    (hFbB : tsupport Fb ⊆ overlapStrip Jb Ja hφ)
    (hG : ∀ q ∈ overlapStrip Ja Jb hφ,
      Gb (stripMap (transition (Ja.patch hφ) (Jb.patch hφ)) q) = Ga q)
    (hF : ∀ q ∈ overlapStrip Ja Jb hφ,
      Fb (stripMap (transition (Ja.patch hφ) (Jb.patch hφ)) q) = Fa q) :
    defectPairing Ja.strip (endpointTuple Ja.liftCurve (Ja.liftModel φ) j) (Fin.last n) Ga Fa =
      defectPairing Jb.strip (endpointTuple Jb.liftCurve (Jb.liftModel φ) j) (Fin.last n) Gb Fb := by
  have hadm : SlotsAdmissible Jb.strip (endpointTuple Jb.liftCurve (Jb.liftModel φ) j)
      (Fin.last n) :=
    slotsAdmissible_endpointTuple (Jb.isLocallyBoundedPshOn_liftCurve hbd)
      (Jb.isLocallyBoundedPshOn_liftModel hφ hφb) j _
  have hb := isDefectPairing_defectPairing hadm hGb hFb (hFbB.trans (overlapStrip_le _ _ _))
  have hb' := IsDefectPairing.restrict hFbB hb
  have hAB := isBiholomorphicPair_stripLift
    (PatchOverlap.isBiholomorphicPair (Ja.patch hφ) (Jb.patch hφ)) complexTimeStrip
    isOpen_complexTimeStrip
  have hπ := isSmoothPluriharmonicOn_comp_stripFst
    (isSmoothPluriharmonicOn_potential_transition Ja Jb hφ)
    (S := overlapStrip Ja Jb hφ) fun q hq => hq.1
  have ha := IsDefectPairing.comp_biholomorphic hAB
    (va := endpointTuple Ja.liftCurve (Ja.liftModel φ) j)
    (vb := endpointTuple Jb.liftCurve (Jb.liftModel φ) j) (π := fun _ => _) (fun _ => hπ)
    (fun i _ q hq => by
      by_cases hij : (i : ℕ) < j
      · simp only [endpointTuple, if_pos hij]
        exact liftCurve_stripMap hbd hq
      · simp only [endpointTuple, if_neg hij]
        exact liftModel_stripMap hq) hG hF hFa hFaA hb'
  exact defectPairing_eq hFa (IsDefectPairing.mono (overlapStrip_le _ _ _) ha)

end Transport

/-! ### The gluing identity -/

section Gluing

variable {θ : ClosedRealOneOneForm n M} {U : ℝ → M → EReal} {φ : M → EReal} {A B : ℝ}

namespace StripChart

/-- The weight `f(e⁻¹ z) ζ(τ) (h - Φ)` on the strip of `J`. -/
def weight (J : StripChart θ U) (φ : M → EReal) (ζ : ℂ → ℝ) (f : M → ℝ) :
    ComplexModel (n + 1) → ℝ :=
  fun q => stripCutoff (chartRead J.chart f) ζ q * (J.liftCurve q - J.liftModel φ q)

/-- The test function `f(e⁻¹ z) ψ(τ)` on the strip of `J`. -/
def test (J : StripChart θ U) (ψ : ℂ → ℝ) (f : M → ℝ) : ComplexModel (n + 1) → ℝ :=
  stripCutoff (chartRead J.chart f) ψ

/-- A chart-smooth function with compact support in the region of `J`. -/
def IsCutoff (J : StripChart θ U) (f : M → ℝ) : Prop :=
  ChartSmooth (n := n) f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ J.region

variable {J : StripChart θ U} {f : M → ℝ}

theorem IsCutoff.source (hf : J.IsCutoff f) : tsupport f ⊆ J.chart.val.source :=
  hf.2.2.trans fun _ hx => hx.1

theorem IsCutoff.tsupport_chartRead (hf : J.IsCutoff f) :
    tsupport (chartRead J.chart f) ⊆ J.domain :=
  (tsupport_chartRead_subset hf.2.1 hf.source).trans (J.image_subset_domain hf.2.2)

theorem IsCutoff.hasCompactSupport (hf : J.IsCutoff f) : HasCompactSupport (chartRead J.chart f) :=
  hasCompactSupport_chartRead hf.2.1 hf.source

theorem IsCutoff.mul_right (hf : J.IsCutoff f) {g : M → ℝ} (hg : ChartSmooth (n := n) g) :
    J.IsCutoff fun x => f x * g x :=
  ⟨fun e => (hf.1 e).mul (hg e),
    hf.2.1.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left,
    tsupport_mul_subset_left.trans hf.2.2⟩

theorem IsCutoff.mul_left {g : M → ℝ} (hg : J.IsCutoff g) (hf : ChartSmooth (n := n) f) :
    J.IsCutoff fun x => f x * g x :=
  ⟨fun e => (hf e).mul (hg.1 e),
    hg.2.1.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right,
    tsupport_mul_subset_right.trans hg.2.2⟩

theorem IsCutoff.continuous_stripCutoff (hf : J.IsCutoff f) {ζ : ℂ → ℝ} (hζ : Continuous ζ) :
    Continuous (stripCutoff (chartRead J.chart f) ζ) :=
  FiniteGeodesicStripCharts.continuous_stripCutoff (continuous_chartRead hf.1 hf.2.1 hf.source) hζ

theorem IsCutoff.hasCompactSupport_stripCutoff (hf : J.IsCutoff f) {ζ : ℂ → ℝ}
    (hζc : HasCompactSupport ζ) : HasCompactSupport (stripCutoff (chartRead J.chart f) ζ) :=
  FiniteGeodesicStripCharts.hasCompactSupport_stripCutoff hf.hasCompactSupport hζc

theorem IsCutoff.tsupport_stripCutoff (hf : J.IsCutoff f) {ζ : ℂ → ℝ}
    (hζc : HasCompactSupport ζ) (hζS : tsupport ζ ⊆ complexTimeStrip) :
    tsupport (stripCutoff (chartRead J.chart f) ζ) ⊆ J.strip :=
  tsupport_stripCutoff_subset_stripLift hf.hasCompactSupport hζc isOpen_complexTimeStrip
    hf.tsupport_chartRead hζS

theorem isBoundedTest_weight
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : ThetaPlurisubharmonic θ.val φ) (hφb : IsBoundedPotential φ) (hf : J.IsCutoff f)
    {ζ : ℂ → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (hζS : tsupport ζ ⊆ complexTimeStrip) : IsBoundedTest (J.weight φ ζ f) :=
  isBoundedTest_mul_sub (J.isLocallyBoundedPshOn_liftCurve hbd)
    (J.isLocallyBoundedPshOn_liftModel hφ hφb) (hf.continuous_stripCutoff hζ)
    (hf.hasCompactSupport_stripCutoff hζc) (hf.tsupport_stripCutoff hζc hζS)

theorem tsupport_weight_subset (hf : J.IsCutoff f) {ζ : ℂ → ℝ} (hζc : HasCompactSupport ζ)
    (hζS : tsupport ζ ⊆ complexTimeStrip) : tsupport (J.weight φ ζ f) ⊆ J.strip :=
  tsupport_mul_subset_left.trans (hf.tsupport_stripCutoff hζc hζS)

theorem contDiffOn_test (hf : ChartSmooth (n := n) f) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiffOn ℝ ∞ (J.test ψ f) J.strip :=
  ((contDiffOn_chartRead hf J.chart).comp ((stripFst n).restrictScalars ℝ).contDiff.contDiffOn
    fun _ hq => J.domain_subset_target hq.1).mul
      (hψ.comp (lastCoordinate n).contDiff).contDiffOn

theorem contDiff_test (hf : J.IsCutoff f) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (J.test ψ f) :=
  contDiff_stripCutoff (contDiff_chartRead hf.1 hf.2.1 hf.source) hψ

end StripChart

open StripChart

theorem tsupport_stripCutoff_subset_overlap {Ja Jb : StripChart θ U}
    (hφ : ThetaPlurisubharmonic θ.val φ) {f : M → ℝ} (hfa : Ja.IsCutoff f) (hfb : Jb.IsCutoff f)
    {ζ : ℂ → ℝ} (hζc : HasCompactSupport ζ) (hζS : tsupport ζ ⊆ complexTimeStrip) :
    tsupport (stripCutoff (chartRead Ja.chart f) ζ) ⊆ overlapStrip Ja Jb hφ := by
  refine tsupport_stripCutoff_subset_stripLift hfa.hasCompactSupport hζc isOpen_complexTimeStrip
    ((tsupport_chartRead_subset hfa.2.1 hfa.source).trans ?_) hζS
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(hfa.2.2 hx).2, ?_⟩
  change Ja.chart.val.symm (Ja.chart.val x) ∈ Jb.region
  rw [Ja.chart.val.left_inv (hfa.source hx)]
  exact hfb.2.2 hx

theorem chartRead_transition_strip {Ja Jb : StripChart θ U} {hφ : ThetaPlurisubharmonic θ.val φ}
    (f : M → ℝ) {q : ComplexModel (n + 1)} (hq : q ∈ overlapStrip Ja Jb hφ) :
    chartRead Jb.chart f (transition (Ja.patch hφ) (Jb.patch hφ) (stripFst n q)) =
      chartRead Ja.chart f (stripFst n q) :=
  chartRead_transition (Ja.domain_subset_target hq.1.1) hq.1.2.1

theorem weight_stripMap
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    {Ja Jb : StripChart θ U} {hφ : ThetaPlurisubharmonic θ.val φ} (ζ : ℂ → ℝ) (f : M → ℝ)
    {q : ComplexModel (n + 1)} (hq : q ∈ overlapStrip Ja Jb hφ) :
    Jb.weight φ ζ f (stripMap (transition (Ja.patch hφ) (Jb.patch hφ)) q) = Ja.weight φ ζ f q := by
  simp only [StripChart.weight]
  rw [stripCutoff_stripMap _ _ ζ _ q (chartRead_transition_strip f hq), liftCurve_stripMap hbd hq,
    liftModel_stripMap hq]
  ring

theorem test_stripMap {Ja Jb : StripChart θ U} {hφ : ThetaPlurisubharmonic θ.val φ}
    (ψ : ℂ → ℝ) (f : M → ℝ) {q : ComplexModel (n + 1)} (hq : q ∈ overlapStrip Ja Jb hφ) :
    Jb.test ψ f (stripMap (transition (Ja.patch hφ) (Jb.patch hφ)) q) = Ja.test ψ f q :=
  stripCutoff_stripMap _ _ ψ _ q (chartRead_transition_strip f hq)

/-- **The gluing identity.** For strip charts `J_a`, a partition of unity `(χ_a)` of `X`
subordinate to them and `ψ ∈ C_c^∞(strip)` (with a cutoff `ζ` equal to `1` near `supp ψ`),

  `Σ_j Σ_a ∫ χ_a (U - φ) ddᶜψ(τ) ∧ (ddᶜh_a)ʲ ∧ (ddᶜΦ_a)ⁿ⁻ʲ = 0`,

each pairing being read in its strip chart. -/
theorem sum_sum_defectPairing_eq_zero
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : ThetaPlurisubharmonic θ.val φ) (hφb : IsBoundedPotential φ) {m : ℕ}
    (J : Fin m → StripChart θ U) {χ : Fin m → M → ℝ} (hχ : ∀ a, (J a).IsCutoff (χ a))
    (hχ1 : ∀ x, ∑ a, χ a x = 1) {ψ ζ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψS : tsupport ψ ⊆ complexTimeStrip) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) (hζS : tsupport ζ ⊆ complexTimeStrip)
    {Nψ : Set ℂ} (hNψ : IsOpen Nψ) (hψN : tsupport ψ ⊆ Nψ) (hζ1 : ∀ τ ∈ Nψ, ζ τ = 1) :
    ∑ j : Fin (n + 1), ∑ a, defectPairing (J a).strip
      (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) (timeLift n ψ)
      ((J a).weight φ ζ (χ a)) = 0 := by
  classical
  -- cutoffs equal to one near the supports of the partition functions
  choose ζM hζMs hζMc hζMJ N hNo hχN hζM1 using fun b =>
    exists_chartSmooth_eq_one_nhds (n := n) (hχ b).2.1 (J b).region (hχ b).2.2
  have hcut : ∀ b, (J b).IsCutoff (ζM b) := fun b => ⟨hζMs b, hζMc b, hζMJ b⟩
  have hcutab : ∀ a b, (J a).IsCutoff fun x => χ a x * ζM b x := fun a b =>
    (hχ a).mul_right (hζMs b)
  have hcutba : ∀ a b, (J b).IsCutoff fun x => χ a x * ζM b x := fun a b =>
    (hcut b).mul_left (hχ a).1
  have hadm : ∀ a (j : ℕ), SlotsAdmissible (J a).strip
      (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) := fun a j =>
    slotsAdmissible_endpointTuple ((J a).isLocallyBoundedPshOn_liftCurve hbd)
      ((J a).isLocallyBoundedPshOn_liftModel hφ hφb) j _
  have hBT : ∀ a {f : M → ℝ}, (J a).IsCutoff f → IsBoundedTest ((J a).weight φ ζ f) :=
    fun a _ hf => isBoundedTest_weight hbd hφ hφb hf hζ.continuous hζc hζS
  have hTS : ∀ a {f : M → ℝ}, (J a).IsCutoff f → tsupport ((J a).weight φ ζ f) ⊆ (J a).strip :=
    fun a _ hf => tsupport_weight_subset hf hζc hζS
  -- (1) split the test function along the partition of unity
  have S1 : ∀ a (j : ℕ), defectPairing (J a).strip
      (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) (timeLift n ψ)
      ((J a).weight φ ζ (χ a)) = ∑ b, defectPairing (J a).strip
      (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) ((J a).test ψ (χ b))
      ((J a).weight φ ζ (χ a)) := by
    intro a j
    rw [defectPairing_congr_slot (hBT a (hχ a)) (G' := fun q => ∑ b, (J a).test ψ (χ b) q)
      fun q hq => ?_]
    · exact defectPairing_sum (hadm a j) Finset.univ
        (fun b _ => contDiffOn_test (hχ b).1 hψ) (hBT a (hχ a)) (hTS a (hχ a))
    · simp only [StripChart.test, stripCutoff, timeLift]
      rw [← Finset.sum_mul, ← chartRead_sum,
        chartRead_of_mem (z := stripFst n q) ((J a).domain_subset_target hq.1), hχ1, one_mul]
  -- (2) cut the weight off near `supp χ_b`, and (3) transport to `J_b`
  have S23 : ∀ a b (j : ℕ), defectPairing (J a).strip
      (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) ((J a).test ψ (χ b))
      ((J a).weight φ ζ (χ a)) = defectPairing (J b).strip
      (endpointTuple (J b).liftCurve ((J b).liftModel φ) j) (Fin.last n) ((J b).test ψ (χ b))
      ((J b).weight φ ζ fun x => χ a x * ζM b x) := by
    intro a b j
    have hG := contDiffOn_test (J := J a) (hχ b).1 hψ
    have e2 : defectPairing (J a).strip
        (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) ((J a).test ψ (χ b))
        ((J a).weight φ ζ (χ a)) = defectPairing (J a).strip
        (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) ((J a).test ψ (χ b))
        ((J a).weight φ ζ fun x => χ a x * ζM b x) := by
      refine IsDefectPairing.congr_weight' (hadm a j) hG (hBT a (hχ a)) (hBT a (hcutab a b))
        (hTS a (hχ a)) (hTS a (hcutab a b))
        (O := stripFst n ⁻¹' ((J a).chart.val.target ∩ (J a).chart.val.symm ⁻¹' N b))
        (((J a).chart.val.isOpen_inter_preimage_symm (hNo b)).preimage (stripFst n).continuous)
        (fun q hq hqs => ?_) (fun q hq => ?_)
        (isDefectPairing_defectPairing (hadm a j) hG (hBT a (hχ a)) (hTS a (hχ a)))
        (isDefectPairing_defectPairing (hadm a j) hG (hBT a (hcutab a b)) (hTS a (hcutab a b)))
      · have hz : stripFst n q ∈ (J a).chart.val.target := (J a).domain_subset_target hq.1
        exact ⟨hz, hχN b (symm_mem_tsupport_of_mem_tsupport_chartRead hz
          (tsupport_stripCutoff_subset_fst _ _ hqs))⟩
      · simp only [StripChart.weight, stripCutoff]
        rw [chartRead_of_mem hq.1, chartRead_of_mem hq.1, hζM1 b _ hq.2, mul_one]
    rw [e2]
    exact defectPairing_transport hbd hφ hφb (J a) (J b) j (contDiffOn_test (hχ b).1 hψ)
      (hBT a (hcutab a b)) (hBT b (hcutba a b))
      (tsupport_mul_subset_left.trans
        (tsupport_stripCutoff_subset_overlap hφ (hcutab a b) (hcutba a b) hζc hζS))
      (tsupport_mul_subset_left.trans
        (tsupport_stripCutoff_subset_overlap hφ (hcutba a b) (hcutab a b) hζc hζS))
      (fun q hq => test_stripMap ψ (χ b) hq) (fun q hq => weight_stripMap hbd ζ _ hq)
  -- (4) sum over `a` in `J_b`
  have S4 : ∀ b (j : ℕ), ∑ a, defectPairing (J b).strip
      (endpointTuple (J b).liftCurve ((J b).liftModel φ) j) (Fin.last n) ((J b).test ψ (χ b))
      ((J b).weight φ ζ fun x => χ a x * ζM b x) = defectPairing (J b).strip
      (endpointTuple (J b).liftCurve ((J b).liftModel φ) j) (Fin.last n) ((J b).test ψ (χ b))
      ((J b).weight φ ζ (ζM b)) := by
    intro b j
    rw [← defectPairing_sum_weight (hadm b j) (contDiffOn_test (hχ b).1 hψ) Finset.univ
      (fun a _ => hBT b (hcutba a b)) fun a _ => hTS b (hcutba a b)]
    congr 1
    funext q
    simp only [StripChart.weight, stripCutoff]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← chartRead_sum]
    congr 3
    funext x
    rw [← Finset.sum_mul, hχ1, one_mul]
  -- (5) the local integration by parts in `J_b`
  have S5 : ∀ b, ∑ j : Fin (n + 1), defectPairing (J b).strip
      (endpointTuple (J b).liftCurve ((J b).liftModel φ) j) (Fin.last n) ((J b).test ψ (χ b))
      ((J b).weight φ ζ (ζM b)) = 0 := by
    intro b
    refine sum_defectPairing_endpointTuple_eq_zero ((J b).isLocallyBoundedPshOn_liftCurve hbd)
      ((J b).isLocallyBoundedPshOn_liftModel hφ hφb) ((J b).isBTLimit_liftCurve hbd)
      ((J b).isBTLimit_liftModel hφ hφb) (contDiff_test (hχ b) hψ)
      ((hχ b).hasCompactSupport_stripCutoff hψc)
      ((hχ b).tsupport_stripCutoff hψc hψS) (hBT b (hcut b)) (hTS b (hcut b))
      (O := stripFst n ⁻¹' ((J b).chart.val.target ∩ (J b).chart.val.symm ⁻¹' N b) ∩
        lastCoordinate n ⁻¹' Nψ)
      ((((J b).chart.val.isOpen_inter_preimage_symm (hNo b)).preimage
        (stripFst n).continuous).inter (hNψ.preimage (lastCoordinate n).continuous))
      (fun q hq => ?_) (fun q hq _ => ?_)
    · have h := tsupport_stripCutoff_subset (hχ b).hasCompactSupport hψc hq
      obtain ⟨x, hx, hxz⟩ := tsupport_chartRead_subset (hχ b).2.1 (hχ b).source h.1
      have hz : stripFst n q ∈ (J b).chart.val.target := by
        rw [stripFst_apply, ← hxz]; exact (J b).chart.val.map_source ((hχ b).source hx)
      refine ⟨⟨hz, ?_⟩, ?_⟩
      · change (J b).chart.val.symm (stripFst n q) ∈ N b
        rw [stripFst_apply, ← hxz, (J b).chart.val.left_inv ((hχ b).source hx)]
        exact hχN b hx
      · change q (Fin.last n) ∈ Nψ
        rw [← stripModelEquiv_snd]
        exact hψN h.2
    · simp only [StripChart.weight, stripCutoff]
      rw [chartRead_of_mem hq.1.1, hζM1 b _ hq.1.2, hζ1 (q (Fin.last n)) hq.2, one_mul, one_mul]
  calc ∑ j : Fin (n + 1), ∑ a, defectPairing (J a).strip
        (endpointTuple (J a).liftCurve ((J a).liftModel φ) j) (Fin.last n) (timeLift n ψ)
        ((J a).weight φ ζ (χ a))
      = ∑ j : Fin (n + 1), ∑ a, ∑ b, defectPairing (J b).strip
        (endpointTuple (J b).liftCurve ((J b).liftModel φ) j) (Fin.last n) ((J b).test ψ (χ b))
        ((J b).weight φ ζ fun x => χ a x * ζM b x) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by
          rw [S1 a j]
          exact Finset.sum_congr rfl fun b _ => S23 a b j
    _ = ∑ j : Fin (n + 1), ∑ b, defectPairing (J b).strip
        (endpointTuple (J b).liftCurve ((J b).liftModel φ) j) (Fin.last n) ((J b).test ψ (χ b))
        ((J b).weight φ ζ (ζM b)) :=
        Finset.sum_congr rfl fun j _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => S4 b j
    _ = 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_eq_zero fun b _ => S5 b

end Gluing

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
