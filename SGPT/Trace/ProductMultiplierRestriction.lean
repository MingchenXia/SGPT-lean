import SGPT.PSH.OhsawaTakegoshiPullback
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison

/-!
# Multiplier germs on a constant product

This module supplies the product-restriction bridge for the global-generation
clause E5' in the proof of `thm:Bert`. Its projection argument uses upper
semicontinuity of the weight, so it applies to local quasi-psh weights without
assuming that a nonconstant weight on a compact base is globally psh.

The chosen mathematical route is recorded in
`work/sgpt-resume-20261114/bert-e5/blueprint/bert-e5-global-generation.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.PSH.MultiplierPullback

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

variable {m : ℕ} {ψ : ComplexModel m → EReal} {W : Set (ComplexModel m)}

/-- The reverse projection inclusion needs only an upper semicontinuous weight.
Fubini supplies nearby integrable slices and the holomorphic slice-closure
criterion puts the germ in the actual pullback ideal. No psh hypothesis is
assumed on the weight. -/
theorem mem_pullback_of_multiplierIdeal_comp_initCoords_of_upperSemicontinuousOn (hW : IsOpen W)
    (hψ : UpperSemicontinuousOn ψ W) {p : ComplexModel (m + 1)} (hp : initCoords p ∈ W) {c : ℝ}
    {f : ComplexModel (m + 1) → ℂ}
    (hf : (multiplierIdeal (n := m + 1) c (fun x => ψ (initCoords x))).mem p f) :
    (GermIdeal.pullback (m := m + 1) initCoords (multiplierIdeal (n := m) c ψ)).mem p f := by
  obtain ⟨-, hc, U, hU, hpU, hfU, hmeas, hfin⟩ := hf
  set x₀ := initCoords p with hx₀
  have hW' : IsOpen (initCoords ⁻¹' W) := hW.preimage continuous_initCoords
  obtain ⟨ρ, hρ, hρsub⟩ := exists_polydiscN_subset (hU.inter hW') ⟨hpU, hp⟩
  have hρU : polydiscN p ρ ⊆ U := fun x hx => (hρsub hx).1
  have hx₀W : polydiscN x₀ ρ ⊆ W := by
    intro w hw
    have h1 : sliceMap m (p (Fin.last m)) w ∈ polydiscN p ρ := by
      rw [← mem_preimage, sliceMap_preimage_polydiscN p (by simpa using hρ)]
      exact hw
    have := (hρsub h1).2
    simpa [mem_preimage, initCoords_sliceMap] using this
  set G : ComplexModel (m + 1) → ℝ≥0∞ := multiplierDensity (fun x => ψ (initCoords x)) c f
    with hG
  have hGmeas : AEMeasurable G (volume.restrict (polydiscN p ρ)) :=
    hmeas.mono_measure (Measure.restrict_mono hρU le_rfl)
  have hGfin : ∫⁻ x in polydiscN p ρ, G x ≠ ⊤ :=
    ne_top_of_le_ne_top hfin.ne (lintegral_mono_set hρU)
  obtain ⟨hpmeas, hpfin⟩ := aemeasurable_lintegral_sliceMap_prod p ρ hGmeas hGfin
  set s : ℝ := ρ / 4 with hs
  set s' : ℝ := ρ / 2 with hs'
  have hspos : 0 < s := by positivity
  have hss' : s < s' := by rw [hs, hs']; linarith
  have hs'ρ : s' < ρ := by rw [hs']; linarith
  -- the slices
  have hslices : ∀ k : ℕ, ∃ t : ℂ, t ≠ 0 ∧ ‖t‖ < min (1 / ((k : ℝ) + 1)) (s / 2) ∧
      ∫⁻ w in polydiscN x₀ ρ, G (sliceMap m (p (Fin.last m) + t) w) ≠ ⊤ := by
    intro k
    have hε : 0 < min (1 / ((k : ℝ) + 1)) (s / 2) := lt_min Nat.one_div_pos_of_nat (by positivity)
    obtain ⟨t, ht0, htε, -, hbound⟩ := exists_good_slice (μ := volume) (B := polydiscN x₀ ρ)
      (a := p (Fin.last m)) hρ hpmeas hpfin hε
    refine ⟨t, ht0, htε, ?_⟩
    have htpos : ENNReal.ofReal (‖t‖ ^ 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      have := norm_pos_iff.mpr ht0
      positivity
    intro htop
    rw [htop, ENNReal.mul_top htpos] at hbound
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)
  choose t ht0 htlt htfin using hslices
  have hts : ∀ k, ‖t k‖ < s / 2 := fun k => (htlt k).trans_le (min_le_right _ _)
  have htρ : ∀ k, ‖p (Fin.last m) + t k - p (Fin.last m)‖ < ρ := fun k => by
    rw [add_sub_cancel_left]
    exact (hts k).trans (by rw [hs]; linarith)
  have htlim : Tendsto t atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
      (fun k => ((htlt k).trans_le (min_le_left _ _)).le) ?_)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- the slice functions and their pullbacks
  set fs : ℕ → ComplexModel m → ℂ := fun k w => f (sliceMap m (p (Fin.last m) + t k) w)
    with hfs
  have hmapsS : ∀ k, MapsTo (sliceMap m (p (Fin.last m) + t k)) (polydiscN x₀ ρ)
      (polydiscN p ρ) := fun k w hw => by
    rw [← mem_preimage, sliceMap_preimage_polydiscN p (htρ k)]
    exact hw
  have hfsdiff : ∀ k, DifferentiableOn ℂ (fs k) (polydiscN x₀ ρ) := fun k =>
    (hfU.mono hρU).comp (differentiable_sliceMap _).differentiableOn (hmapsS k)
  have hfsmem : ∀ k, (multiplierIdeal (n := m) c ψ).mem x₀ (fs k) := by
    intro k
    have hopen := isOpen_polydiscN x₀ ρ
    have hx₀mem := mem_polydiscN_self x₀ hρ
    refine ⟨holomorphicAt_model_iff.mpr ?_, hc, polydiscN x₀ ρ, hopen, hx₀mem, hfsdiff k,
      ?_, ?_⟩
    · filter_upwards [hopen.mem_nhds hx₀mem] with w hw
      exact (hfsdiff k).differentiableAt (hopen.mem_nhds hw)
    · exact RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn
        hopen (hψ.mono hx₀W) (hfsdiff k).continuousOn hc.ne'
    · have hdens : ∀ w, multiplierDensity ψ c (fs k) w =
          G (sliceMap m (p (Fin.last m) + t k) w) := fun w => by
        rw [hG]
        simp only [multiplierDensity]
        rw [initCoords_sliceMap]
      exact lt_of_eq_of_lt (lintegral_congr fun w => hdens w) (lt_top_iff_ne_top.mpr (htfin k))
  set F : ℕ → ComplexModel (m + 1) → ℂ := fun k x => fs k (initCoords x) with hF
  have hmapsI : MapsTo initCoords (openPolydisc p s') (polydiscN x₀ ρ) := fun x hx =>
    initCoords_mem_polydiscN (fun i => (hx i).trans hs'ρ)
  have hFdiff : ∀ k, DifferentiableOn ℂ (F k) (openPolydisc p s') := fun k =>
    (hfsdiff k).comp differentiable_initCoords.differentiableOn hmapsI
  have hFJ : ∀ k,
      (GermIdeal.pullback (m := m + 1) initCoords (multiplierIdeal (n := m) c ψ)).mem p (F k) := by
    intro k
    have hhol : HolomorphicAt (m + 1) (F k) p := by
      refine holomorphicAt_model_iff.mpr ?_
      have hopen := isOpen_openPolydisc p s'
      have hpmem : p ∈ openPolydisc p s' := fun i => by
        simpa using (show (0 : ℝ) < s' by positivity)
      filter_upwards [hopen.mem_nhds hpmem] with x hx
      exact (hFdiff k).differentiableAt (hopen.mem_nhds hx)
    show IsInSpanAt (n := m + 1) (fun s => ∃ a, (multiplierIdeal (n := m) c ψ).mem
      (initCoords p) a ∧ s = a ∘ initCoords) p (F k)
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨fs k, hfsmem k, rfl⟩ hhol
  have hslice : ∀ k, ∀ z ∈ openPolydisc p s', z (Fin.last m) = p (Fin.last m) + t k →
      F k z = f z := by
    intro k z _ hz
    show f (sliceMap m (p (Fin.last m) + t k) (initCoords z)) = f z
    rw [← hz, sliceMap_initCoords]
  -- a bound for `f` on the closed polydisc
  have hcomp : IsCompact (closedPolydiscN p s) := isCompact_closedPolydiscN p hspos.le
  have hcl : closedPolydiscN p s ⊆ U := (closedPolydiscN_subset_polydiscN p
    (show s < ρ by rw [hs]; linarith)).trans hρU
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn (hfU.continuousOn.mono hcl)
  have hbound : ∀ k θ, ‖t k‖ * ‖F k (torusPoint p s θ)‖ ≤ ‖t k‖ * max M 0 := by
    intro k θ
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hmem : sliceMap m (p (Fin.last m) + t k) (initCoords (torusPoint p s θ)) ∈
        closedPolydiscN p s := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [sliceMap_last, add_sub_cancel_left]
        exact (hts k).le.trans (by linarith)
      · rw [sliceMap_castSucc, initCoords_apply, norm_torusPoint_sub p hspos.le]
    show ‖f (sliceMap m (p (Fin.last m) + t k) (initCoords (torusPoint p s θ)))‖ ≤ max M 0
    exact (hM _ hmem).trans (le_max_left _ _)
  have hδ : Tendsto (fun k => ‖t k‖ * max M 0) atTop (𝓝 0) := by
    simpa using (tendsto_norm_zero.comp htlim).mul_const (max M 0)
  have hfpoly : DifferentiableOn ℂ f (openPolydisc p s') :=
    hfU.mono fun x hx => hρU fun i => (hx i).trans hs'ρ
  exact germIdeal_mem_of_slice_extensions (germKrullIntersection m)
    (isHolomorphicGermIdeal_pullback c) hspos hss' hfpoly t ht0 hts htlim F hFJ hFdiff hslice
    _ hδ hbound

/-- A multiplier germ of a constant product weight restricts to a multiplier
germ on the actual central slice. Only the base weight's local quasi-psh
property is used to absorb holomorphic combinations. -/
theorem multiplierIdeal_slice_mem_of_mem_comp_initCoords
    (hW : IsOpen W) (hψ : UpperSemicontinuousOn ψ W)
    {p : ComplexModel (m + 1)} (hp : initCoords p ∈ W)
    (hψq : QuasiPlurisubharmonicAt ψ (initCoords p)) {c : ℝ} (hc : 0 < c)
    {f : ComplexModel (m + 1) → ℂ}
    (hf : (multiplierIdeal (n := m + 1) c (fun z => ψ (initCoords z))).mem p f) :
    (multiplierIdeal (n := m) c ψ).mem (initCoords p)
      (fun w => f (sliceMap m (p (Fin.last m)) w)) := by
  have hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (sliceMap m (p (Fin.last m))) := by
    rw [contMDiff_iff_contDiff]
    change ContDiff ℂ ∞ (fun w =>
      hyperplaneEmbedding m w + EuclideanSpace.single (Fin.last m) (p (Fin.last m)))
    simpa only [hyperplaneCLM_apply] using
      (hyperplaneCLM m).contDiff.add
        (contDiff_const (c := EuclideanSpace.single (Fin.last m) (p (Fin.last m))))
  have hpull :=
    mem_pullback_of_multiplierIdeal_comp_initCoords_of_upperSemicontinuousOn hW hψ hp hf
  have hspan : IsInSpanAt (n := m)
      (fun g => (multiplierIdeal (n := m) c ψ).mem (initCoords p) g)
      (initCoords p) (fun w => f (sliceMap m (p (Fin.last m)) w)) := by
    apply SGPT.PSH.MultiplierPullback.isInSpanAt_comp (sliceMap_initCoords p)
      (Eventually.of_forall fun _ => hι.contMDiffAt) ?_
      (mem_pullback_initCoords_iff.mp hpull)
    rintro s ⟨g, hg, rfl⟩
    refine ⟨g, hg, Eventually.of_forall ?_⟩
    intro w
    simp only [Function.comp_apply, initCoords_sliceMap]
  obtain ⟨hhol, N, s, a, hs, ha, heq⟩ := hspan
  exact ⟨hhol, multiplierIntegrableAt_of_eq_sum hψq hc (fun i => (hs i).2)
    (fun i => holomorphicAt_model_iff.mp (ha i)) heq⟩

/-- Constant projection preserves weighted local integrability for an upper
semicontinuous base weight. -/
theorem multiplierIntegrableAt_comp_initCoords_of_upperSemicontinuousOn (hW : IsOpen W) (hψ : UpperSemicontinuousOn ψ W)
    {p : ComplexModel (m + 1)} (hp : initCoords p ∈ W) {c : ℝ} {a : ComplexModel m → ℂ}
    (ha : MultiplierIntegrableAt ψ c a (initCoords p) volume) :
    MultiplierIntegrableAt (fun x => ψ (initCoords x)) c (fun x => a (initCoords x)) p volume := by
  obtain ⟨hc, U, hU, hpU, haU, hmeas, hfin⟩ := ha
  obtain ⟨r, hr, hrUW⟩ := exists_polydiscN_subset (hU.inter hW) ⟨hpU, hp⟩
  set Δ := polydiscN p r with hΔ
  have hΔopen : IsOpen Δ := isOpen_polydiscN p r
  have hmaps : MapsTo initCoords Δ (polydiscN (initCoords p) r) :=
    fun x hx => initCoords_mem_polydiscN hx
  refine ⟨hc, Δ, hΔopen, mem_polydiscN_self p hr, ?_, ?_, ?_⟩
  · exact (haU.mono fun w hw => (hrUW hw).1).comp differentiable_initCoords.differentiableOn
      hmaps
  · have husc : UpperSemicontinuousOn (fun x => ψ (initCoords x)) Δ :=
      hψ.comp continuous_initCoords.continuousOn (fun x hx => (hrUW (hmaps hx)).2)
    have hcont : ContinuousOn (fun x => a (initCoords x)) Δ :=
      ((haU.mono fun w hw => (hrUW hw).1).comp differentiable_initCoords.differentiableOn
        hmaps).continuousOn
    exact RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn
      hΔopen husc hcont hc.ne'
  · have hsub : polydiscN (initCoords p) r ⊆ U := fun w hw => (hrUW hw).1
    have hmeas' : AEMeasurable (multiplierDensity ψ c a)
        (volume.restrict (polydiscN (initCoords p) r)) := hmeas.mono_measure
      (Measure.restrict_mono hsub le_rfl)
    have hfin' : ∫⁻ w in polydiscN (initCoords p) r, multiplierDensity ψ c a w ≠ ⊤ :=
      ne_top_of_le_ne_top hfin.ne (lintegral_mono_set hsub)
    exact lt_top_iff_ne_top.mpr
      (lintegral_polydiscN_comp_initCoords_lt_top p r hmeas' hfin')

end SGPT.PSH.MultiplierPullback

namespace SGPT.Trace.ProductMultiplierRestriction

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped ProductComplexManifold

/-- Projection is open, so every genuine product neighborhood contains a
non-pole point of the constant pullback. -/
theorem locallyNondegenerate_comp_fst {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {φ : X → EReal} (hφ : LocallyNondegenerate φ) :
    LocallyNondegenerate (fun q : X × Y => φ q.1) := by
  intro q U hU hqU
  obtain ⟨x, hx, hφx⟩ := hφ q.1 (Prod.fst '' U) (isOpenMap_fst U hU) ⟨q, hqU, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, hφx⟩

/-- The actual native first-projection pullback retains the full pulled
background and produces its local nondegeneracy internally. -/
theorem isThetaPshPotential_comp_fst {n m : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    IsThetaPshPotential
      (ClosedRealOneOneForm.pullback
        (ProductComplexManifold.contMDiff_fst (n := n) (m := m) (X := X) (Y := Y)) θ).val
      (fun q : X × Y => φ q.1) := by
  exact GlobalPotentialPullback.isThetaPshPotential_comp
    (ProductComplexManifold.contMDiff_fst (n := n) (m := m) (X := X) (Y := Y)) hφ.1
    (locallyNondegenerate_comp_fst hφ.2)

open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.MultiplierPullback

/-- The first component of the native product model is the coordinate projection. -/
theorem prodModelEquiv_symm_fst {n : ℕ} (z : ComplexModel (n + 1)) :
    ((ProductComplexManifold.prodModelEquiv n 1).symm z).1 = initCoords z := by
  ext i
  rfl

section Native

variable {n : ℕ} {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel 1) Y] [IsComplexManifold 1 Y]

omit [IsComplexManifold n X] [IsComplexManifold 1 Y] in
/-- Preferred product charts express a constant pullback by the literal first coordinates. -/
theorem chartFunction_comp_fst (φ : X → EReal) (x : X) (y : Y) :
    chartFunction (fun q : X × Y => φ q.1) (complexChartAt (n := n + 1) (x, y)) =
      fun z => chartFunction φ (complexChartAt (n := n) x) (initCoords z) := by
  funext z
  change φ ((chartAt (ComplexModel n) x).symm
    (((ProductComplexManifold.prodModelEquiv n 1).symm z).1)) = _
  rw [prodModelEquiv_symm_fst]
  rfl

/-- A base multiplier germ pulls back to the actual product multiplier ideal. -/
theorem multiplierIdeal_mem_comp_fst {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} {x : X} (y : Y)
    {g : X → ℂ} (hg : (multiplierIdeal (n := n) c φ).mem x g) :
    (multiplierIdeal (n := n + 1) c (fun q : X × Y => φ q.1)).mem (x, y)
      (fun q => g q.1) := by
  let e := complexChartAt (n := n) x
  let eP := complexChartAt (n := n + 1) (x, y)
  let p := eP.val (x, y)
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hp : initCoords p = e.val x := by
    rw [← prodModelEquiv_symm_fst]
    exact congrArg Prod.fst ((ProductComplexManifold.prodModelEquiv n 1).symm_apply_apply _)
  have hint := multiplierIntegrableAt_comp_initCoords_of_upperSemicontinuousOn
    e.val.open_target (hφ e).upperSemicontinuousOn
    (p := p) (by rw [hp]; exact e.val.map_source hx) (by rw [hp]; exact hg.2)
  refine ⟨hg.1.comp_contMDiff
    (Eventually.of_forall fun _ => ProductComplexManifold.contMDiff_fst.contMDiffAt), ?_⟩
  rw [chartFunction_comp_fst]
  change MultiplierIntegrableAt (fun z => chartFunction φ e (initCoords z)) c
    (fun z => g (eP.val.symm z).1) p volume
  simpa only [eP, complexChartAt, ProductComplexManifold.chartAt_prod,
    ProductComplexManifold.prodChart_symm_apply, prodModelEquiv_symm_fst] using hint

/-- Restriction to any constant slice retains native multiplier membership.
The proof transports the actual coordinate pullback span, rather than adding a
slice-integrability premise to the section. -/
theorem multiplierIdeal_mem_restrict {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} (hc : 0 < c)
    {x : X} (y : Y) {f : X × Y → ℂ}
    (hf : (multiplierIdeal (n := n + 1) c (fun q : X × Y => φ q.1)).mem (x, y) f) :
    (multiplierIdeal (n := n) c φ).mem x (fun z => f (z, y)) := by
  let e := complexChartAt (n := n) x
  let eP := complexChartAt (n := n + 1) (x, y)
  let p := eP.val (x, y)
  let F : ComplexModel (n + 1) → ℂ := fun z => f (eP.val.symm z)
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hxy : (x, y) ∈ eP.val.source := mem_complexChartAt_source (x, y)
  have hp : initCoords p = e.val x := by
    rw [← prodModelEquiv_symm_fst]
    exact congrArg Prod.fst ((ProductComplexManifold.prodModelEquiv n 1).symm_apply_apply _)
  have hfint : MultiplierIntegrableAt (fun z => chartFunction φ e (initCoords z)) c F p volume := by
    simpa only [chartFunction_comp_fst] using hf.2
  have hfmodel : (multiplierIdeal (n := n + 1) c
      (fun z => chartFunction φ e (initCoords z))).mem p F := by
    refine ⟨holomorphicAt_model_iff.mpr ?_, hfint⟩
    obtain ⟨-, U, hU, hpU, hdiff, -⟩ := hfint
    filter_upwards [hU.mem_nhds hpU] with z hz
    exact hdiff.differentiableAt (hU.mem_nhds hz)
  have hpull := mem_pullback_of_multiplierIdeal_comp_initCoords_of_upperSemicontinuousOn
    e.val.open_target (hφ e).upperSemicontinuousOn
    (by rw [hp]; exact e.val.map_source hx) hfmodel
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + 1)) ∞
      (fun z : X => (z, y)) :=
    ProductComplexManifold.contMDiff_prodMk contMDiff_id contMDiff_const
  have hemax : eP.val ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel (n + 1)) ∞ (X × Y) :=
    IsManifold.subset_maximalAtlas eP.property
  have hC : ∀ᶠ z in 𝓝 x, ContMDiffAt 𝓘(ℂ, ComplexModel n)
      𝓘(ℂ, ComplexModel (n + 1)) ∞ (fun z => eP.val (z, y)) z := by
    filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds
      (eP.val.open_source.mem_nhds hxy)] with z hz
    exact (contMDiffAt_of_mem_maximalAtlas hemax hz).comp z hi.contMDiffAt
  have hspan := isInSpanAt_comp (h := fun z : X => eP.val (z, y)) (x := x) (y := p) rfl hC
    (T := fun s => (multiplierIdeal (n := n) c φ).mem x s)
    (fun s hs => by
      obtain ⟨a, ha, rfl⟩ := hs
      refine ⟨fun z => a (e.val z), ⟨?_, ?_⟩, Eventually.of_forall ?_⟩
      · rw [hp] at ha
        exact DerivativeIdeal.holomorphicAt_comp_chart e hx (holomorphicAt_model_iff.mp ha.1)
      · rw [hp] at ha
        refine ha.2.congr (EventuallyEq.refl _ _) ?_
        filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hx)] with z hz
        show a z = a (e.val (e.val.symm z))
        rw [e.val.right_inv hz]
      · intro z
        change a (initCoords (eP.val (z, y))) = a (e.val z)
        rw [← prodModelEquiv_symm_fst]
        exact congrArg a (congrArg Prod.fst ((ProductComplexManifold.prodModelEquiv n 1).symm_apply_apply _)))
    (mem_pullback_initCoords_iff.mp hpull)
  apply MultiplierIdealProductComparison.mem_multiplierIdeal_of_isInSpanAt hφ hc
  apply InvertibleIdealQuotient.IsInSpanAt.congr' hspan
  filter_upwards [hi.continuous.continuousAt.preimage_mem_nhds
    (eP.val.open_source.mem_nhds hxy)] with z hz
  exact congrArg f (eP.val.left_inv hz)

end Native

end SGPT.Trace.ProductMultiplierRestriction
