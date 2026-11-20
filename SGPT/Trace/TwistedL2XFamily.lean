import SGPT.Trace.TwistedL2XGauge

/-!
# Finite families of local pieces on a manifold as global fields

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:pieces`).  A finite family of local
test pieces `h_i` in chart-frames `(c_i, e_i)` (`TwistedDatum.XFam`) is one global `L`-valued
`(1,0)`-vector field; its coefficient field in a chart-frame `(c, e)` is
`tot c e = ∑_i transpX c_i e_i c e h_i`.  For a gauge form `F`, the `μ`-density of the `i`-th piece
is `pd F i x = F c_i e_i (tot c_i e_i) h_i (c_i x)` and `Φ F = ∑_i pd F i`.  Main results:

* `XFam.Φ_eq_diag`: at `x ∈ U`, `Φ F x = F c e (tot c e) (tot c e) (c x)` in every chart-frame at
  `x` (the pieces computed in their own charts add up to the diagonal value);
* `XFam.integral_pd`: `∫_X pd F i dμ = ∫ ρ_{c_i} F c_i e_i (tot c_i e_i) h_i dλ` (the chart integral
  of the piece), with `pd F i` continuous and integrable.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- A finite family of local test pieces `h_i` in arbitrary chart-frames `(c_i, e_i)`. -/
structure XFam where
  ι : Type
  s : Finset ι
  c : ι → ComplexChart n X
  e : ι → AtlasFrame T.L
  h : ι → ComplexModel n → ComplexModel n
  spec : ∀ i, IsLocalTestField T.L T.U (c i) (e i) (h i)

/-- The type of chart-frame-indexed integrands. -/
abbrev GForm := ComplexChart n X → AtlasFrame T.L → (ComplexModel n → ComplexModel n) →
  (ComplexModel n → ComplexModel n) → ComplexModel n → ℂ

variable {T}

namespace XFam

variable (F : T.XFam)

/-- The coefficient field of the family in the chart-frame `(c, e)`. -/
def tot (c : ComplexChart n X) (e : AtlasFrame T.L) (z : ComplexModel n) : ComplexModel n :=
  ∑ i ∈ F.s, transpX T.L (F.c i) (F.e i) c e (F.h i) z

theorem tsupport_subset_pd (i : F.ι) : tsupport (F.h i) ⊆ T.pieceDomain (F.c i) (F.e i) :=
  (F.spec i).2.2

theorem tsupport_subset (i : F.ι) : tsupport (F.h i) ⊆ chartFrameDomain T.L (F.c i) (F.e i) :=
  fun _ hz => (F.tsupport_subset_pd i hz).1

theorem contDiffOn_transp (i : F.ι) (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (transpX T.L (F.c i) (F.e i) c e (F.h i)) (T.pieceDomain c e) :=
  (contDiffOn_transpX (F.spec i).1 (F.spec i).2.1 (F.tsupport_subset i)).mono fun _ hz => hz.1

theorem contDiffOn_tot (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (F.tot c e) (T.pieceDomain c e) :=
  ContDiffOn.sum fun i _ => F.contDiffOn_transp i c e

theorem contDiffAt_of_pd {c : ComplexChart n X} {e : AtlasFrame T.L}
    {u : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u (T.pieceDomain c e))
    {z : ComplexModel n} (hz : z ∈ T.pieceDomain c e) : ContDiffAt ℝ ∞ u z :=
  hu.contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)

theorem isTransp_tot {c c' : ComplexChart n X} {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain T.L c e) (hz' : c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet) :
    IsTransp T.L c e c' e' (F.tot c e) (F.tot c' e') z :=
  isTransp_finset_sum F.s fun i _ => isTransp_transpX (F.spec i).2.1 (F.tsupport_subset i) hz hz'

open Classical in
/-- The `μ`-density on `X` of the `i`-th piece of the gauge form `G`. -/
def pd (G : T.GForm) (i : F.ι) (x : X) : ℂ :=
  if x ∈ (F.c i).val.source then G (F.c i) (F.e i) (F.tot (F.c i) (F.e i)) (F.h i) ((F.c i).val x)
  else 0

/-- The `μ`-density on `X` of the gauge form `G` on the family. -/
def Φ (G : T.GForm) (x : X) : ℂ := ∑ i ∈ F.s, F.pd G i x

theorem mem_pd_of_chart {c : ComplexChart n X} {e : AtlasFrame T.L} {x : X} (hxU : x ∈ T.U)
    (hx : x ∈ c.val.source ∩ e.val.baseSet) : c.val x ∈ T.pieceDomain c e := by
  refine ⟨⟨c.val.map_source hx.1, ?_⟩, ?_⟩
  · simp only [mem_preimage, c.val.left_inv hx.1]; exact hx.2
  · simp only [mem_preimage, c.val.left_inv hx.1]; exact hxU

/-- **A piece computed in its own chart-frame is the piece of the transported field.** -/
theorem pd_eq {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) {c : ComplexChart n X}
    {e : AtlasFrame T.L} {x : X} (hxU : x ∈ T.U) (hx : x ∈ c.val.source ∩ e.val.baseSet) :
    F.pd G i x = G c e (F.tot c e) (transpX T.L (F.c i) (F.e i) c e (F.h i)) (c.val x) := by
  classical
  have hz := mem_pd_of_chart hxU hx
  have hsymm : c.val.symm (c.val x) = x := c.val.left_inv hx.1
  by_cases hxs : x ∈ pieceSupport (F.c i) (F.h i)
  · have hxi := mem_of_mem_pieceSupport (F.tsupport_subset i) hxs
    have hz' : c.val.symm (c.val x) ∈ (F.c i).val.source ∩ (F.e i).val.baseSet := by
      rw [hsymm]; exact hxi
    have hg := hG.gauge c e (F.c i) (F.e i) (F.tot c e) (F.tot (F.c i) (F.e i))
      (transpX T.L (F.c i) (F.e i) c e (F.h i)) (F.h i) (c.val x) hz hz'
      (F.contDiffOn_tot c e) (F.contDiffOn_transp i c e) (F.contDiffOn_tot (F.c i) (F.e i))
      (F.spec i).1.contDiffOn (F.isTransp_tot hz.1 hz')
      (isTransp_piece (F.spec i).2.1 (F.tsupport_subset i) hz.1 hz')
    rw [chg_chart hx.1] at hg
    rw [pd, if_pos hxi.1, hg]
  · have hzero : transpX T.L (F.c i) (F.e i) c e (F.h i) =ᶠ[𝓝 (c.val x)] 0 :=
      transpX_eventuallyEq_zero (F.spec i).2.1
        ((F.tsupport_subset i).trans fun _ hz => hz.1) hz.1.1 (by rw [hsymm]; exact hxs)
    rw [hG.zero _ _ _ _ _ hzero, pd]
    split_ifs with hxi
    · refine hG.zero _ _ _ _ _ (notMem_tsupport_iff_eventuallyEq.mp fun h' => hxs ⟨hxi, h'⟩)
    · rfl

/-- **The pieces add up to the diagonal value** in any chart-frame at a point of `U`. -/
theorem Φ_eq_diag {G : T.GForm} (hG : T.IsGaugeFormX G) {c : ComplexChart n X}
    {e : AtlasFrame T.L} {x : X} (hxU : x ∈ T.U) (hx : x ∈ c.val.source ∩ e.val.baseSet) :
    F.Φ G x = G c e (F.tot c e) (F.tot c e) (c.val x) := by
  have hz := mem_pd_of_chart hxU hx
  rw [Φ, Finset.sum_congr rfl fun i _ => F.pd_eq hG i hxU hx,
    ← hG.add c e _ F.s _ _ hz (contDiffAt_of_pd (F.contDiffOn_tot c e) hz)
      fun i _ => contDiffAt_of_pd (F.contDiffOn_transp i c e) hz]
  rfl

theorem pd_eq_zero_of_notMem {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) {x : X}
    (hx : x ∉ pieceSupport (F.c i) (F.h i)) : F.pd G i x = 0 := by
  classical
  rw [pd]
  split_ifs with hxi
  · exact hG.zero _ _ _ _ _ (notMem_tsupport_iff_eventuallyEq.mp fun h' => hx ⟨hxi, h'⟩)
  · rfl

theorem Φ_eq_zero {G : T.GForm} (hG : T.IsGaugeFormX G) {x : X} (hx : x ∉ T.U) :
    F.Φ G x = 0 :=
  Finset.sum_eq_zero fun i _ => F.pd_eq_zero_of_notMem hG i fun hxs =>
    hx (T.pieceSupport_subset (F.spec i) hxs).1

/-! ### The piece as a function on the chart and on `X` -/

/-- The piece of `G` in its own chart. -/
def pc (G : T.GForm) (i : F.ι) (z : ComplexModel n) : ℂ :=
  G (F.c i) (F.e i) (F.tot (F.c i) (F.e i)) (F.h i) z

theorem pc_eq_zero {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) {z : ComplexModel n}
    (hz : z ∉ tsupport (F.h i)) : F.pc G i z = 0 :=
  hG.zero _ _ _ _ _ (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem continuous_pc {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) :
    Continuous (F.pc G i) :=
  continuous_of_continuousOn_of_eq_zero (T.isOpen_pieceDomain (F.c i) (F.e i))
    (hG.contOn _ _ _ _ (F.contDiffOn_tot _ _) (F.spec i).1.contDiffOn) (isClosed_tsupport _)
    (F.tsupport_subset_pd i) fun _ hz => F.pc_eq_zero hG i hz

theorem hasCompactSupport_pc {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) :
    HasCompactSupport (F.pc G i) :=
  HasCompactSupport.intro (F.spec i).2.1 fun _ hz => F.pc_eq_zero hG i hz

theorem pd_eq_pc (G : T.GForm) (i : F.ι) {x : X} (hx : x ∈ (F.c i).val.source) :
    F.pd G i x = F.pc G i ((F.c i).val x) := by
  classical
  rw [pd, if_pos hx]; rfl

theorem continuous_pd {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) : Continuous (F.pd G i) := by
  have hK : IsClosed (pieceSupport (F.c i) (F.h i)) :=
    isClosed_pieceSupport (F.spec i).2.1 ((F.tsupport_subset i).trans fun _ hz => hz.1)
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ (F.c i).val.source
  · have h1 : ContinuousAt (fun x => F.pc G i ((F.c i).val x)) x :=
      (F.continuous_pc hG i).continuousAt.comp
        ((F.c i).val.continuousOn.continuousAt ((F.c i).val.open_source.mem_nhds hx))
    refine h1.congr ?_
    filter_upwards [(F.c i).val.open_source.mem_nhds hx] with y hy
    exact (F.pd_eq_pc G i hy).symm
  · have hxs : x ∉ pieceSupport (F.c i) (F.h i) := fun h => hx h.1
    refine (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℂ)) x).congr ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hxs] with y hy
    exact (F.pd_eq_zero_of_notMem hG i hy).symm

theorem integrable_pd {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) :
    Integrable (F.pd G i) T.μ := by
  set c := F.c i
  have hρ := T.isChartDensity_ρX c
  have hKt : tsupport (F.h i) ⊆ c.val.target := (F.tsupport_subset i).trans fun _ hz => hz.1
  have hfin := measure_source_inter_preimage_lt_top c hρ.1.continuousOn hρ.2.2
    (F.spec i).2.1.isCompact hKt
  obtain ⟨C, hC⟩ := (F.continuous_pc hG i).bounded_above_of_compact_support
    (F.hasCompactSupport_pc hG i)
  have hsupp : Function.support (F.pd G i) ⊆ pieceSupport c (F.h i) := fun x hx => by
    by_contra h'
    exact hx (F.pd_eq_zero_of_notMem hG i h')
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  refine Measure.integrableOn_of_bounded (M := C) hfin.ne
    (F.continuous_pd hG i).aestronglyMeasurable ?_
  refine (ae_restrict_mem (measurableSet_source_inter_preimage c.val
    (isClosed_tsupport _))).mono fun x hx => ?_
  rw [F.pd_eq_pc G i hx.1]
  exact hC _

/-- **The integral of a piece over `X` is its chart integral.** -/
theorem integral_pd {G : T.GForm} (hG : T.IsGaugeFormX G) (i : F.ι) :
    ∫ x, F.pd G i x ∂T.μ = ∫ z, ((T.ρX (F.c i) z : ℝ) : ℂ) * F.pc G i z := by
  set c := F.c i
  have hρ := T.isChartDensity_ρX c
  have hKt : tsupport (F.h i) ⊆ c.val.target := (F.tsupport_subset i).trans fun _ hz => hz.1
  have hK := (F.spec i).2.1.isCompact
  have h := setIntegral_source_inter_preimage c hρ.1.continuousOn hρ.2.1 hρ.2.2 hK hKt
    (F.continuous_pd hG i).measurable
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := c.val.source ∩ c.val ⁻¹' tsupport (F.h i)) fun x hx =>
    F.pd_eq_zero_of_notMem hG i hx] at h
  have h2 : ∫ z, ((T.ρX c z : ℝ) : ℂ) * F.pc G i z =
      ∫ z in tsupport (F.h i), ((T.ρX c z : ℝ) : ℂ) * F.pc G i z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [F.pc_eq_zero hG i hz, mul_zero]).symm
  rw [h, h2]
  refine setIntegral_congr_fun hK.measurableSet fun z hz => ?_
  rw [F.pd_eq_pc G i (c.val.map_target (hKt hz)), c.val.right_inv (hKt hz)]

theorem integrable_Φ {G : T.GForm} (hG : T.IsGaugeFormX G) : Integrable (F.Φ G) T.μ :=
  integrable_finsetSum _ fun i _ => F.integrable_pd hG i

theorem integral_Φ {G : T.GForm} (hG : T.IsGaugeFormX G) :
    ∫ x, F.Φ G x ∂T.μ = ∑ i ∈ F.s, ∫ z, ((T.ρX (F.c i) z : ℝ) : ℂ) * F.pc G i z := by
  unfold Φ
  rw [integral_finsetSum _ fun i _ => F.integrable_pd hG i]
  exact Finset.sum_congr rfl fun i _ => F.integral_pd hG i

theorem continuous_Φ {G : T.GForm} (hG : T.IsGaugeFormX G) : Continuous (F.Φ G) :=
  continuous_finsetSum _ fun i _ => F.continuous_pd hG i

end XFam

end TwistedDatum

end SGPT.Trace.TwistedL2
