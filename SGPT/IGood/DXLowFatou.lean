import SGPT.IGood.DXLowTrace

/-!
# The Fatou step: the integral of the pointwise Bergman limit bounds `liminf n! h⁰ / kⁿ`

Blueprint `claude-dx-low`, node `claude-dx-low:fatou`. Lower bound of the asymptotic
Riemann–Roch formula (source `thm:DXmain1`, `prop:DXmainanalytic`), Bergman-kernel route.

Let `φ ∈ PSH(X, θ - δω)` (`θ = c₁(L, h_L)`, so `θ_φ` is a Kähler current) be smooth off its pole
set `P = {φ = -∞}` (`SmoothOffPoleSet`). Fix cover data `D` (`claude-global-l2:cover`, for
`δ/2`). For each chart `a` of the cover, the pieces
`E_a = (S_a \ ⋃_{b < a} S_b) \ P` (`S_a = z_a⁻¹ B(z_a, R_a/4)`) partition `X \ P`, and on `E_a` the
pointwise limit density is `G_a = smoothDensity(Φ_a) ∘ z_a / ρ_a ∘ z_a`, with
`Φ_a = φ ∘ z_a⁻¹ - log |e_L|²` (`canonicalWeight`) and `ρ_a` the density of `μ` in the chart.

`sum_lintegral_le_liminf_finrank`: `∑_a ∫_{E_a} G_a dμ ≤ liminf_k (n!/kⁿ) h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`.

Proof: Fatou for the measurable Bergman majorants `D_k` (`exists_bergman_majorant`), with
`∫ D_k = h⁰` and `D_k ≥ B_k ≥ ` the peak bound, and the pointwise lower bound
`G_a(x) ≤ liminf (n!/kⁿ) B_k(x)` (`le_liminf_bergmanDensity`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.MultiplierSectionsDraft
open SGPT.PSH.GlobalL2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace SGPT.IGood.DXLow

/-- `smoothDensity` only depends on the germ of the function. -/
theorem smoothDensity_congr {u v : ComplexModel n → ℝ} {z : ComplexModel n}
    (h : u =ᶠ[𝓝 z] v) : smoothDensity u z = smoothDensity v z := by
  have h2 : fderiv ℝ (fderiv ℝ u) z = fderiv ℝ (fderiv ℝ v) z := h.fderiv.fderiv_eq
  have hH : complexHessian u z = complexHessian v z := by
    ext j k
    simp only [complexHessian, realHessian_eq_fderiv, h2]
  simp only [smoothDensity, hH]

end SGPT.IGood.DXLow

namespace SGPT.PSH.GlobalL2.CoverData

open SGPT.IGood.DXLow

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

/-- The small region `S_a = z_a⁻¹ B(z_a, R_a/4)` of chart `a`. -/
def smallRegion (a : Fin D.m) : Set X :=
  (D.chartA a).val.source ∩ (D.chartA a).val ⁻¹' ball (ctr (n := n) (D.pt a)) (D.R a / 4)

theorem isOpen_smallRegion (a : Fin D.m) : IsOpen (D.smallRegion a) :=
  (D.chartA a).val.isOpen_inter_preimage isOpen_ball

/-- The small regions cover `X`. -/
theorem exists_mem_smallRegion (x : X) : ∃ a, x ∈ D.smallRegion a := by
  have hne : ∑ a, D.χ a x ≠ 0 := by rw [D.sum_χ x]; exact one_ne_zero
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨a, D.tsupport_χ a (subset_tsupport _ ha)⟩

/-- The disjoint pieces `E_a = (S_a \ ⋃_{b < a} S_b) \ P`. -/
def piece (φ : X → EReal) (a : Fin D.m) : Set X :=
  (D.smallRegion a \ ⋃ b < a, D.smallRegion b) \ poleSet φ

theorem measurableSet_piece {φ : X → EReal} (hφm : Measurable φ) (a : Fin D.m) :
    MeasurableSet (D.piece φ a) := by
  refine ((D.isOpen_smallRegion a).measurableSet.diff ?_).diff ?_
  · exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ =>
      (D.isOpen_smallRegion b).measurableSet
  · exact hφm (measurableSet_singleton ⊥)

theorem piece_subset (φ : X → EReal) (a : Fin D.m) : D.piece φ a ⊆ D.smallRegion a :=
  fun _ hx => hx.1.1

theorem pairwise_disjoint_piece (φ : X → EReal) {a b : Fin D.m} (hab : a ≠ b) :
    Disjoint (D.piece φ a) (D.piece φ b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  rcases lt_or_gt_of_ne hab with h | h
  · exact hxb.1.2 (mem_iUnion₂.mpr ⟨a, h, hxa.1.1⟩)
  · exact hxa.1.2 (mem_iUnion₂.mpr ⟨b, h, hxb.1.1⟩)

/-- Off the pole set, every point lies in a piece. -/
theorem exists_mem_piece (φ : X → EReal) {x : X} (hx : x ∉ poleSet φ) :
    ∃ a, x ∈ D.piece φ a := by
  classical
  obtain ⟨a₀, ha₀⟩ := D.exists_mem_smallRegion x
  set s := Finset.univ.filter (fun a => x ∈ D.smallRegion a) with hs
  have hne : s.Nonempty := ⟨a₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₀⟩⟩
  obtain ⟨a, has, hmin⟩ := s.exists_min_image (fun a => a) hne
  have ha : x ∈ D.smallRegion a := (Finset.mem_filter.mp has).2
  refine ⟨a, ⟨ha, fun hb => ?_⟩, hx⟩
  obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hb
  have := hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb⟩)
  exact absurd hb (not_lt.mpr this)

/-- The canonical local weight `Φ_a = φ ∘ z_a⁻¹ - log |e_L|²` (`toReal` of the potential). -/
def canonicalWeight (a : Fin D.m) (φ : X → EReal) (z : ComplexModel n) : ℝ :=
  (φ ((D.chartA a).val.symm z)).toReal + frameWeight (prefFrame L (D.pt a)) (D.chartA a) z

/-- The pointwise limit density `G_a = smoothDensity(Φ_a) ∘ z_a / ρ_a ∘ z_a` on chart `a`. -/
def limitDensity (a : Fin D.m) (φ : X → EReal) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (smoothDensity (D.canonicalWeight a φ) ((D.chartA a).val x) /
    D.dens a ((D.chartA a).val x))

end SGPT.PSH.GlobalL2.CoverData

namespace SGPT.IGood.DXLow

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}

/-- Superadditivity of the lower integral over a finite sum. -/
theorem sum_lintegral_le_lintegral_sum {ι : Type*} (s : Finset ι) (f : ι → X → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
      rw [Finset.sum_insert hb]
      simp_rw [Finset.sum_insert hb]
      exact (add_le_add_right ih _).trans (le_lintegral_add (fun x => f b x) _)

/-- **The pointwise bound at every non-polar point** (blueprint `claude-dx-low:fatou`):
`G_a(x) ≤ liminf (n!/kⁿ) B_k(x)` on the piece `E_a`. -/
theorem limitDensity_le_liminf (hn : 0 < n) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (hδ : 0 < δ)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (hsm : SmoothOffPoleSet (n := n) φ)
    (D : CoverData ωb μ L T θ (δ / 2)) (a : Fin D.m) {x : X} (hx : x ∈ D.piece φ a) :
    D.limitDensity a φ x ≤ liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        bergmanDensity μ L T φ k x) atTop := by
  have hxa : x ∈ (D.chartA a).val.source := hx.1.1.1
  have hxr : (D.chartA a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4) := hx.1.1.2
  set c := D.chartA a with hc
  set p := c.val x with hp
  have hpt : p ∈ c.val.target := c.val.map_source hxa
  have hnp : c.val.symm p ∉ poleSet φ := by rw [c.val.left_inv hxa]; exact hx.2
  obtain ⟨g, hgs, hgφ⟩ := hsm c p hpt hnp
  -- an open set around `p` where `g` is smooth and equals `φ ∘ z_a⁻¹`
  obtain ⟨U, hUo, hpU, hU⟩ : ∃ U : Set (ComplexModel n), IsOpen U ∧ p ∈ U ∧
      ∀ z ∈ U, ContDiffAt ℝ ∞ g z ∧ chartFunction φ c z = (g z : EReal) := by
    have h := hgs.and hgφ
    obtain ⟨U, hU, hUo, hpU⟩ := _root_.mem_nhds_iff.mp h
    exact ⟨U, hUo, hpU, fun z hz => hU hz⟩
  have hg : ContDiffOn ℝ ∞ g U := fun z hz => (hU z hz).1.contDiffWithinAt
  have hgφ' : ∀ z ∈ U, φ (c.val.symm z) = (g z : EReal) := fun z hz => (hU z hz).2
  have h := le_liminf_bergmanDensity hn hL hT hδ hφ D a hxa hxr hUo hpU hg hgφ'
  have heq : smoothDensity (D.canonicalWeight a φ) p = smoothDensity (D.peakWeight a g) p := by
    apply smoothDensity_congr
    filter_upwards [hUo.mem_nhds hpU] with z hz
    simp only [CoverData.canonicalWeight, CoverData.peakWeight]
    rw [hgφ' z hz, EReal.toReal_coe]
  simp only [CoverData.limitDensity]
  rw [heq]
  exact h

/-- **The Fatou step** (blueprint `claude-dx-low:fatou`): for `φ ∈ PSH(X, θ - δω)` smooth off its
pole set, `∑_a ∫_{E_a} G_a dμ ≤ liminf_k (n!/kⁿ) h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. -/
theorem sum_lintegral_le_liminf_finrank [CompactSpace X] (hn : 0 < n)
    (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (hδ : 0 < δ)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (hsm : SmoothOffPoleSet (n := n) φ)
    (D : CoverData ωb μ L T θ (δ / 2)) :
    ∑ a, ∫⁻ x in D.piece φ a, D.limitDensity a φ x ∂μ ≤
      liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ≥0∞)) atTop := by
  classical
  have hφm : Measurable φ := hφ.quasiPshPotential.1.upperSemicontinuous.measurable
  choose Dk hDm hBD hDint using fun k : ℕ => exists_bergman_majorant (L := L) (T := T) (k := k) hμ hφ
  -- the pieces
  have hsum_le : ∀ x, ∑ a, (D.piece φ a).indicator (D.limitDensity a φ) x ≤
      liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) * Dk k x) atTop := by
    intro x
    by_cases hx : x ∈ poleSet φ
    · have : ∀ a, (D.piece φ a).indicator (D.limitDensity a φ) x = 0 := fun a =>
        indicator_of_notMem (fun h => h.2 hx) _
      simp [this]
    · obtain ⟨a, ha⟩ := D.exists_mem_piece φ hx
      rw [Finset.sum_eq_single a (fun b _ hba => indicator_of_notMem
        (fun hb => Set.disjoint_left.mp (D.pairwise_disjoint_piece φ hba) hb ha) _)
        (fun h => absurd (Finset.mem_univ a) h), indicator_of_mem ha]
      refine (limitDensity_le_liminf hn hL hT hδ hφ hsm D a ha).trans ?_
      exact liminf_le_liminf (Eventually.of_forall fun k => mul_le_mul_of_nonneg_left (hBD k x) zero_le)
  calc ∑ a, ∫⁻ x in D.piece φ a, D.limitDensity a φ x ∂μ
      = ∑ a, ∫⁻ x, (D.piece φ a).indicator (D.limitDensity a φ) x ∂μ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [lintegral_indicator (D.measurableSet_piece hφm a)]
    _ ≤ ∫⁻ x, ∑ a, (D.piece φ a).indicator (D.limitDensity a φ) x ∂μ :=
        sum_lintegral_le_lintegral_sum _ _
    _ ≤ ∫⁻ x, liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
          Dk k x) atTop ∂μ := lintegral_mono hsum_le
    _ ≤ liminf (fun k : ℕ => ∫⁻ x, ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
          Dk k x ∂μ) atTop :=
        lintegral_liminf_le fun k => (hDm k).const_mul _
    _ = liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
          (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ≥0∞)) atTop := by
        congr 1
        funext k
        rw [lintegral_const_mul _ (hDm k), hDint k]

end SGPT.IGood.DXLow
