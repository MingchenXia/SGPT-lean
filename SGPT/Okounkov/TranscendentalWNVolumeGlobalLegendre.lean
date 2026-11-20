import SGPT.Okounkov.TranscendentalWNVolumeGlobalStatement
import SGPT.Foundations.Analysis.Pending.PatchOverlap

/-!
# The global Monge–Ampère identity of the partial Legendre transform from the local one (WN-VF2)

Blueprint node `tok-wn-vf:global-legendre-ma` (chapter `claude-tok-wn-vf`, sub-lemmas in
`claude-tok-wn-vf2`); source WN21 Theorem 3.5 ("this follows from Theorem 3.3 together with the
fact that the Monge–Ampère measures put no mass on the analytic subsets").

Let `Y` be compact, `u` as in `IsGlobalLegendreMAData`, and `ν` its non-pluripolar measure on
`Y × ℂ*` (`IsPuncturedProductMAMeasure`).  In a chart `e` of `Y`, with a local potential `ρ` of
`θ` on `W`, the function `u'(z, τ) = u(e⁻¹ z, τ) + ρ(z)` satisfies the local hypotheses
`IsLegendreMAData W u' a b (e(A))` (`isLegendreMAData_chart`), its partial Legendre transform is
`û_λ ∘ e⁻¹ + ρ` (`partialLegendre_stripChartFunction`), and the global measures of `û_λ` and
`ν` are, on the patch, the local measures of `û_λ ∘ e⁻¹ + ρ` and `u'` (`legendrePatch`,
`globalMixedMeasure_legendre_apply_of_subset`).  So the local identity
`PartialLegendreMALocalStatement N` gives, for every Borel `B` inside one patch,

  `ν (B × ℂ*) = (N + 1) ∫⁻_{[a, b]} ⟨(θ + dd^c û_λ)^N⟩(B) dλ`   (`measure_prod_eq_of_subset`).

A general Borel `B` is cut into the pieces `Bⱼ = B ∩ Dⱼ` of the disjointed finite cover of `Y` by
patch sources; summing over `j` needs the interchange `Σⱼ ∫⁻ = ∫⁻ Σⱼ`, i.e. the a.e.-measurability
of `λ ↦ ⟨(θ + dd^c û_λ)^N⟩(Bⱼ)`.  This is the local statement `LegendreMAMeasurableStatement N`
(the measures of `û_λ` on a Borel set depend measurably on `λ`), proved in
`TranscendentalWNVolumeGlobalMeasurable.lean`.

* `globalLegendreMA_of_local_of_measurable`:
  `PartialLegendreMALocalStatement N → LegendreMAMeasurableStatement N →
   GlobalLegendreMAStatement N` for `0 < N`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar

/-! ### The measurability statement -/

/-- **Measurable dependence on `λ`** of the Monge–Ampère measures of the partial Legendre
transforms: under the hypotheses of `tok-wn:legendre-ma`, for every Borel `E ⊆ ℂᴺ` the function
`λ ↦ ⟨(dd^c û_λ)^N⟩(E)` is a.e.-measurable on `[a, b]`. -/
def LegendreMAMeasurableStatement (N : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal) (a b : ℝ)
    (A : Set (ComplexModel N)), IsLegendreMAData Ω u a b A →
    ∀ (hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre u lam) Ω)
      (E : Set (ComplexModel N)), MeasurableSet E →
      AEMeasurable (fun lam => MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) E)
        (volume.restrict (Icc a b))

theorem truncationLimitMeasure_congr_fun {n : ℕ} {Ω : Opens (ComplexModel n)}
    {f g : ComplexModel n → EReal} (h : f = g) (hf : PlurisubharmonicOn f Ω)
    (hg : PlurisubharmonicOn g Ω) :
    MongeAmpere.truncationLimitMeasure Ω f hf = MongeAmpere.truncationLimitMeasure Ω g hg := by
  subst h; rfl

/-! ### Chart data -/

section Chart

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The local function `u'(z, τ) = u(e⁻¹ z, τ) + ρ(z)`. -/
abbrev chartLegendreFunction (u : Y → ℂ → EReal) (e : ComplexChart N Y)
    (ρ : ComplexModel N → ℝ) : ComplexModel N → ℂ → EReal :=
  fun z τ => stripChartFunction u e ρ (z, τ)

omit [IsComplexManifold N Y] in
theorem partialLegendre_chartLegendreFunction (u : Y → ℂ → EReal) (e : ComplexChart N Y)
    (ρ : ComplexModel N → ℝ) (lam : ℝ) :
    partialLegendre (chartLegendreFunction u e ρ) lam =
      fun z => chartFunction (partialLegendre u lam) e z + (ρ z : EReal) :=
  funext (partialLegendre_stripChartFunction u e ρ lam)

omit [IsComplexManifold N Y] in
theorem plurisubharmonicOn_partialLegendre_chart {u : Y → ℂ → EReal} (hinv : IsCircleInvariant u)
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} (hW : IsOpen W) {ρ : ComplexModel N → ℝ}
    (hpsh : PlurisubharmonicOn (stripChartFunction u e ρ) (W ×ˢ puncturedPlane)) (lam : ℝ) :
    PlurisubharmonicOn (partialLegendre (chartLegendreFunction u e ρ) lam) W :=
  plurisubharmonicOn_partialLegendre hW (u := chartLegendreFunction u e ρ) hpsh
    (isCircleInvariant_stripChartFunction hinv e ρ) lam

/-- The common patch of the partial Legendre transform `û_λ` in the chart `e`, on `W`, with the
potential `ρ`. -/
def legendrePatch (θ : ClosedRealOneOneForm N Y) {u : Y → ℂ → EReal} (hinv : IsCircleInvariant u)
    (e : ComplexChart N Y) (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ)
    (hρ : IsSmoothLocalPotential θ.val e (W : Set (ComplexModel N)) ρ)
    (hpsh : PlurisubharmonicOn (stripChartFunction u e ρ) ((W : Set (ComplexModel N)) ×ˢ
      puncturedPlane)) (lam : ℝ) :
    Patch (fun _ : Fin N => θ) (fun _ => partialLegendre u lam) where
  chart := e
  domain := W
  domain_le_target := hρ.2.1
  potential := fun _ => ρ
  localPotential := fun _ => hρ
  plurisubharmonic := fun _ => by
    have h := plurisubharmonicOn_partialLegendre_chart hinv W.isOpen hpsh lam
    rwa [partialLegendre_chartLegendreFunction] at h

variable [MeasurableSpace Y] [BorelSpace Y]

/-- On a Borel subset of a patch source, the global measure of `û_λ` is the local measure of
`û_λ ∘ e⁻¹ + ρ = partialLegendre u' λ` of the coordinate image. -/
theorem globalMixedMeasure_legendre_apply_of_subset [CompactSpace Y] (hN : 0 < N)
    (θ : ClosedRealOneOneForm N Y) {u : Y → ℂ → EReal}
    (hu : ∀ lam, ThetaPlurisubharmonic θ.val (partialLegendre u lam))
    (hinv : IsCircleInvariant u)
    (e : ComplexChart N Y) (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ)
    (hρ : IsSmoothLocalPotential θ.val e (W : Set (ComplexModel N)) ρ)
    (hpsh : PlurisubharmonicOn (stripChartFunction u e ρ) ((W : Set (ComplexModel N)) ×ˢ
      puncturedPlane)) (lam : ℝ) {B : Set Y}
    (hB : B ⊆ (legendrePatch θ hinv e W ρ hρ hpsh lam).source) :
    globalMixedMeasure (fun _ : Fin N => θ) (fun _ => partialLegendre u lam) (fun _ => hu lam) B =
      MongeAmpere.truncationLimitMeasure W (partialLegendre (chartLegendreFunction u e ρ) lam)
        (plurisubharmonicOn_partialLegendre_chart hinv W.isOpen hpsh lam)
        ((W : Set (ComplexModel N)) ∩ e.val.symm ⁻¹' B) := by
  set P := legendrePatch θ hinv e W ρ hρ hpsh lam
  have h1 := globalMixedMeasure_restrict_patch (fun _ => hu lam) P
  rw [← Measure.restrict_eq_self _ hB, h1, patchMeasure, Patch.pushMeasure_apply]
  have hv : PlurisubharmonicOn (fun z => chartFunction (partialLegendre u lam) e z +
      (ρ z : EReal)) W := P.plurisubharmonic ⟨0, hN⟩
  have hdiag := MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hN hv
  change MixedNonPluripolar.mixedTruncationLimitMeasure W (fun _ => fun z =>
      chartFunction (partialLegendre u lam) e z + (ρ z : EReal)) (fun _ => hv) _ = _
  rw [hdiag]
  exact congrFun (congrArg _ (truncationLimitMeasure_congr_fun
    (partialLegendre_chartLegendreFunction u e ρ lam).symm hv _)) _

end Chart

/-! ### The local data in a chart -/

section LocalData

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **The local hypotheses in a chart**: `u'(z, τ) = u(e⁻¹ z, τ) + ρ(z)` satisfies
`IsLegendreMAData W u' a b (e(A))`. -/
theorem isLegendreMAData_chart {θ : SmoothRealForm N Y 2} {u : Y → ℂ → EReal} {a b : ℝ}
    {A : Set Y} (h : IsGlobalLegendreMAData θ u a b A) (e : ComplexChart N Y)
    (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ)
    (hρ : IsSmoothLocalPotential θ e (W : Set (ComplexModel N)) ρ)
    (hpsh : PlurisubharmonicOn (stripChartFunction u e ρ) ((W : Set (ComplexModel N)) ×ˢ
      puncturedPlane)) :
    IsLegendreMAData W (chartLegendreFunction u e ρ) a b
      (SGPT.Foundations.Analysis.FirstPass.pluripolarChartSet A e) where
  psh := hpsh
  circleInvariant := isCircleInvariant_stripChartFunction h.circleInvariant e ρ
  le := h.le
  eq_bot_of_notMem := by
    intro lam hlam z _
    rw [partialLegendre_chartLegendreFunction]
    simp only [chartFunction, h.eq_bot_of_notMem lam hlam, EReal.bot_add]
  pluripolar := (h.pluripolar e).mono_domain hρ.2.1
  locallyBounded := by
    intro lam hlam z hz
    have hzt : z ∈ e.val.target := hρ.2.1 hz.1
    have hzA : e.val.symm z ∉ A := fun hA => hz.2 ⟨hzt, hA⟩
    obtain ⟨C, hC⟩ := h.locallyBounded lam hlam _ hzA
    have hcont : ContinuousAt e.val.symm z := e.val.continuousAt_symm hzt
    have hρc : ContinuousAt ρ z :=
      (hρ.2.2.1.continuousOn.continuousAt (W.isOpen.mem_nhds hz.1))
    have hρb : ∀ᶠ w in 𝓝 z, |ρ w - ρ z| < 1 := by
      have := hρc.eventually (Metric.ball_mem_nhds (ρ z) one_pos)
      filter_upwards [this] with w hw
      simpa [Real.dist_eq] using hw
    refine ⟨C + |ρ z| + 1, ?_⟩
    filter_upwards [hcont.eventually hC, hρb] with w hw hwρ
    rw [partialLegendre_chartLegendreFunction]
    simp only [chartFunction]
    obtain ⟨hlo, hhi⟩ := hw
    have hρlo : -(|ρ z| + 1) ≤ ρ w := by
      have := abs_sub_lt_iff.mp hwρ; have := neg_abs_le (ρ z); linarith
    have hρhi : ρ w ≤ |ρ z| + 1 := by
      have := abs_sub_lt_iff.mp hwρ; have := le_abs_self (ρ z); linarith
    constructor
    · calc ((-(C + |ρ z| + 1) : ℝ) : EReal) = ((-C : ℝ) : EReal) + ((-(|ρ z| + 1) : ℝ) : EReal) := by
            rw [← EReal.coe_add]; ring_nf
        _ ≤ partialLegendre u lam (e.val.symm w) + (ρ w : EReal) :=
            add_le_add hlo (EReal.coe_le_coe_iff.mpr hρlo)
    · calc partialLegendre u lam (e.val.symm w) + (ρ w : EReal)
          ≤ (C : EReal) + ((|ρ z| + 1 : ℝ) : EReal) := add_le_add hhi (EReal.coe_le_coe_iff.mpr hρhi)
        _ = ((C + |ρ z| + 1 : ℝ) : EReal) := by rw [← EReal.coe_add, add_assoc]

end LocalData

/-! ### One patch -/

section OnePatch

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem puncturedProductOpens_inter_preimage (e : ComplexChart N Y) (W : Opens (ComplexModel N))
    (B : Set Y) :
    (puncturedProductOpens W : Set (ComplexModel (N + 1))) ∩
        productChartInverse e ⁻¹' (B ×ˢ puncturedPlane) =
      stripModelEquiv N ⁻¹' (((W : Set (ComplexModel N)) ∩ e.val.symm ⁻¹' B) ×ˢ puncturedPlane) := by
  ext w
  simp only [puncturedProductOpens, productChartInverse, mem_inter_iff, mem_preimage, mem_prod,
    Opens.coe_mk]
  tauto

/-- **The identity on one patch**: for `B` Borel inside the source of a chart patch, the local
statement gives `ν (B × ℂ*) = (N + 1) ∫⁻_{[a, b]} ⟨(θ + dd^c û_λ)^N⟩(B) dλ`. -/
theorem measure_prod_eq_of_subset (hN : 0 < N) (hloc : PartialLegendreMALocalStatement N)
    (θ : ClosedRealOneOneForm N Y) {u : Y → ℂ → EReal} {a b : ℝ} {A : Set Y}
    (h : IsGlobalLegendreMAData θ.val u a b A) {ν : Measure (Y × ℂ)}
    (hν : IsPuncturedProductMAMeasure θ.val u ν)
    (e : ComplexChart N Y) (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ)
    (hρ : IsSmoothLocalPotential θ.val e (W : Set (ComplexModel N)) ρ)
    (hpsh : PlurisubharmonicOn (stripChartFunction u e ρ) ((W : Set (ComplexModel N)) ×ˢ
      puncturedPlane)) {B : Set Y} (hBm : MeasurableSet B)
    (hB : B ⊆ e.val.source ∩ e.val ⁻¹' W) :
    ν (B ×ˢ puncturedPlane) = ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Icc a b,
      globalMixedMeasure (fun _ : Fin N => θ) (fun _ => partialLegendre u lam)
        (fun _ => thetaPlurisubharmonic_partialLegendre h.psh h.circleInvariant lam) B := by
  have hpsh' : PlurisubharmonicOn (productModelFunction (chartLegendreFunction u e ρ))
      (puncturedProductOpens W) := plurisubharmonicOn_comp_stripModelEquiv hpsh
  have hT : B ×ˢ puncturedPlane ⊆ puncturedChartSource e W := fun p hp =>
    ⟨(hB hp.1).1, (hB hp.1).2, hp.2⟩
  have hE : MeasurableSet ((W : Set (ComplexModel N)) ∩ e.val.symm ⁻¹' B) :=
    PatchOverlap.measurableSet_inter_preimage (e.val.continuousOn_symm.mono hρ.2.1) hBm
  rw [hν e W ρ hρ hpsh' _ (hBm.prod (isOpen_puncturedPlane.measurableSet)) hT,
    puncturedProductOpens_inter_preimage,
    hloc W (chartLegendreFunction u e ρ) a b _ (isLegendreMAData_chart h e W ρ hρ hpsh) hpsh'
      (fun lam => plurisubharmonicOn_partialLegendre_chart h.circleInvariant W.isOpen hpsh lam) _ hE]
  congr 1
  refine lintegral_congr fun lam => ?_
  exact (globalMixedMeasure_legendre_apply_of_subset hN θ _ h.circleInvariant e W ρ hρ hpsh lam
    hB).symm

/-- The integrand on one patch is a.e.-measurable. -/
theorem aemeasurable_globalMixedMeasure_of_subset (hN : 0 < N)
    (hmeas : LegendreMAMeasurableStatement N)
    (θ : ClosedRealOneOneForm N Y) {u : Y → ℂ → EReal} {a b : ℝ} {A : Set Y}
    (h : IsGlobalLegendreMAData θ.val u a b A)
    (e : ComplexChart N Y) (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ)
    (hρ : IsSmoothLocalPotential θ.val e (W : Set (ComplexModel N)) ρ)
    (hpsh : PlurisubharmonicOn (stripChartFunction u e ρ) ((W : Set (ComplexModel N)) ×ˢ
      puncturedPlane)) {B : Set Y} (hBm : MeasurableSet B)
    (hB : B ⊆ e.val.source ∩ e.val ⁻¹' W) :
    AEMeasurable (fun lam => globalMixedMeasure (fun _ : Fin N => θ)
        (fun _ => partialLegendre u lam)
        (fun _ => thetaPlurisubharmonic_partialLegendre h.psh h.circleInvariant lam) B)
      (volume.restrict (Icc a b)) := by
  have hE : MeasurableSet ((W : Set (ComplexModel N)) ∩ e.val.symm ⁻¹' B) :=
    PatchOverlap.measurableSet_inter_preimage (e.val.continuousOn_symm.mono hρ.2.1) hBm
  have := hmeas W (chartLegendreFunction u e ρ) a b _ (isLegendreMAData_chart h e W ρ hρ hpsh)
    (fun lam => plurisubharmonicOn_partialLegendre_chart h.circleInvariant W.isOpen hpsh lam) _ hE
  refine this.congr (Eventually.of_forall fun lam => ?_)
  exact (globalMixedMeasure_legendre_apply_of_subset hN θ _ h.circleInvariant e W ρ hρ hpsh lam
    hB).symm

end OnePatch

/-! ### Gluing -/

section Gluing

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [CompactSpace Y]

omit [CompactSpace Y] in
/-- Chart patch data at every point: a chart, an open `W`, a local potential `ρ` with `u'` psh
on `W × ℂ*`, and the point in the source. -/
theorem exists_patchData {θ : SmoothRealForm N Y 2} {u : Y → ℂ → EReal}
    (hu : IsPullbackThetaPshPunctured θ u) (y : Y) :
    ∃ (e : ComplexChart N Y) (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ),
      IsSmoothLocalPotential θ e (W : Set (ComplexModel N)) ρ ∧
      PlurisubharmonicOn (stripChartFunction u e ρ) ((W : Set (ComplexModel N)) ×ˢ
        puncturedPlane) ∧ y ∈ e.val.source ∩ e.val ⁻¹' W := by
  set e := complexChartAt (n := N) y
  have hy : y ∈ e.val.source := mem_complexChartAt_source y
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu e (e.val y) (e.val.map_source hy)
  exact ⟨e, ⟨W, hρ.1⟩, ρ, hρ, hpsh, hy, hzW⟩

/-- A sequence of points whose patch sources cover the compact `Y`. -/
theorem exists_seq_cover (S : Y → Set Y) (hS : ∀ y, IsOpen (S y)) (hyS : ∀ y, y ∈ S y)
    [Nonempty Y] : ∃ ys : ℕ → Y, (⋃ n, S (ys n)) = univ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover S hS
    (fun y _ => mem_iUnion.mpr ⟨y, hyS y⟩)
  let y₀ : Y := Classical.arbitrary Y
  refine ⟨fun n => if hn : n < t.card then (t.equivFin.symm ⟨n, hn⟩).val else y₀, ?_⟩
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  refine mem_iUnion.mpr ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
  have hlt : ((t.equivFin ⟨y, hyt⟩ : Fin t.card) : ℕ) < t.card := (t.equivFin ⟨y, hyt⟩).isLt
  simp only [hlt, dite_true, Fin.eta, Equiv.symm_apply_apply]
  exact hxy

variable [MeasurableSpace Y] [BorelSpace Y]

/-- **`tok-wn-vf:global-legendre-ma`** (WN21 Theorem 3.5) from the local statement and the
measurability of the integrands. -/
theorem globalLegendreMA_of_local_of_measurable (hN : 0 < N)
    (hloc : PartialLegendreMALocalStatement N) (hmeas : LegendreMAMeasurableStatement N) :
    GlobalLegendreMAStatement.{u} N := by
  intro Y _ _ _ _ _ _ θ u a b A h ν hν B hB
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · have hB0 : B = ∅ := eq_empty_of_isEmpty B
    subst hB0
    simp
  choose e W ρ hρ hpsh hmem using fun y => exists_patchData h.psh y
  set S : Y → Set Y := fun y => (e y).val.source ∩ (e y).val ⁻¹' (W y) with hSdef
  have hSo : ∀ y, IsOpen (S y) := fun y => (e y).val.isOpen_inter_preimage (W y).isOpen
  obtain ⟨ys, hys⟩ := exists_seq_cover S hSo hmem
  set D : ℕ → Set Y := disjointed fun n => S (ys n) with hD
  have hDm : ∀ n, MeasurableSet (D n) :=
    MeasurableSet.disjointed fun n => (hSo (ys n)).measurableSet
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed _
  have hDcov : (⋃ n, D n) = univ := by rw [hD, iUnion_disjointed, hys]
  have hDS : ∀ n, D n ⊆ S (ys n) := disjointed_subset _
  have hBD : B = ⋃ n, B ∩ D n := by rw [← inter_iUnion, hDcov, inter_univ]
  have hBDm : ∀ n, MeasurableSet (B ∩ D n) := fun n => hB.inter (hDm n)
  have hBDdisj : Pairwise (Function.onFun Disjoint fun n => B ∩ D n) := fun i j hij =>
    ((hDdisj hij).mono inter_subset_right inter_subset_right)
  have hsub : ∀ n, B ∩ D n ⊆ S (ys n) := fun n => inter_subset_right.trans (hDS n)
  -- the left side
  have hL : ν (B ×ˢ puncturedPlane) = ∑' n, ν ((B ∩ D n) ×ˢ puncturedPlane) := by
    conv_lhs => rw [hBD, iUnion_prod_const]
    exact measure_iUnion (fun i j hij => (hBDdisj hij).set_prod_left _ _)
      (fun n => (hBDm n).prod isOpen_puncturedPlane.measurableSet)
  rw [hL]
  simp_rw [fun n => measure_prod_eq_of_subset hN hloc θ h hν (e (ys n)) (W (ys n)) (ρ (ys n))
    (hρ (ys n)) (hpsh (ys n)) (hBDm n) (hsub n)]
  rw [ENNReal.tsum_mul_left]
  congr 1
  rw [← lintegral_tsum fun n => aemeasurable_globalMixedMeasure_of_subset hN hmeas θ h
    (e (ys n)) (W (ys n)) (ρ (ys n)) (hρ (ys n)) (hpsh (ys n)) (hBDm n) (hsub n)]
  refine lintegral_congr fun lam => ?_
  conv_rhs => rw [hBD]
  exact (measure_iUnion hBDdisj hBDm).symm

end Gluing

end SGPT.Okounkov.TranscendentalWN
