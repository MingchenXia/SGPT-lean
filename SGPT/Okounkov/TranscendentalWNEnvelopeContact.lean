import SGPT.Okounkov.TranscendentalWNEnvelopeLocal
import SGPT.Envelopes.SourceObstacleConcentration
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

/-!
# Monge–Ampère measures on contact sets are bounded by the obstacle (package WN-ENV)

Blueprint nodes `tok-wn:contact-positivity` and `tok-wn:contact-upper` of the WN chapter
(`claude-tok-wn`), with the sub-lemmas of `claude-tok-wn-env`.  This is the inequality "`≤`" of
the Di Nezza–Trapani contact formula (the book's `thm:DNTcontact`), for smooth obstacles,
proved without regularity theory.

Let `M` be a compact complex manifold of dimension `n` with a Kähler background `ω`, `θ` a
closed real `(1,1)`-form, `f` a smooth function, `u ∈ PSH(M, θ)` with `u ≤ f` and contact set
`E = {u = f}`.  Write `(θ + ddᶜf)ⁿ` for the measure of the smooth top form
`formPow (θ + ddᶜf) n`, i.e. `topFormMeasure w Φ = (Φ / ωⁿ) ωⁿ` (truncated at `0` where `Φ` is
negative; on `E` it is the genuine measure of the form, since `θ + ddᶜf ≥ 0` there).

* `coefficientSemipositive_of_contact` (`tok-wn:contact-positivity`): at every contact point
  `θ + ddᶜf ≥ 0`, in every chart; `topRatio_nonneg_of_contact`: so `(θ + ddᶜf)ⁿ ≥ 0` there.
* `diagonalPotentialMeasure_restrict_contact_le` (`tok-wn:contact-upper`):
  `𝟙_E ⟨(θ + ddᶜu)ⁿ⟩ ≤ 𝟙_E (θ + ddᶜf)ⁿ` as measures.
* `diagonalPotentialMeasure_rooftopEnvelope_le_contact`: for `u = P_θ(f)`,
  `⟨(θ + ddᶜu)ⁿ⟩ ≤ 𝟙_E (θ + ddᶜf)ⁿ` (the non-pluripolar measure of the envelope is carried by
  the contact set, `ActualQuasiContinuousEnvelopeContact`).
* `sourcePotentialNonPluripolarMeasure_restrict_contact_le`: the statement for the source-facing
  measures `sourcePotentialNonPluripolarMeasure`.

## Proof

Fix `δ > 0`.  By positivity at contact points, `θ + δω + ddᶜf` is strictly positive at every
contact point, hence on a neighbourhood; in a chart around a contact point, with a local
potential `ρ` of `θ + δω`, `q = f + ρ` is smooth plurisubharmonic on a small ball and
`U = u + ρ ≤ q` with contact set `E`.  The local bound
`EnvelopeLocal.truncationLimitMeasure_contact_le`, transported through a potential patch of
the global measure (`GlobalNonPluripolar.globalMixedMeasure_restrict_patch`) and the chart
formula of the smooth measure (`topFormMeasure_image_eq`), gives the inequality on subsets of
`E` near the point; compactness of `E` globalizes it (`le_of_local_le`).  Since
`⟨(θ + ddᶜu)ⁿ⟩ ≤ ⟨(θ + δω + ddᶜu)ⁿ⟩` (`AmbientMassBackgroundMonotone`) and
`(θ + δω + ddᶜf)ⁿ` is a polynomial in `δ` (`NefMixedMass.topRatio_slotForm_add_smul`), the
limit `δ → 0` (dominated convergence) gives the theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff

namespace SGPT.Okounkov.TranscendentalWN

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.KahlerPerturbation
open SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Positivity at contact points -/

/-- **Positivity at contact points** (`tok-wn:contact-positivity`).  Let `u` be `θ`-psh, `f`
smooth, `u ≤ f` near `x` and `u x = f x`.  Then `θ + ddᶜf` is semipositive at `x`, in every
chart. -/
theorem coefficientSemipositive_of_contact (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ.val u) {f : M → ℝ} (hf : ChartSmooth (n := n) f) {x : M}
    (hle : ∀ᶠ y in 𝓝 x, u y ≤ (f y : EReal)) (hx : u x = (f x : EReal))
    (e : ComplexChart n M) (hxe : x ∈ e.val.source) :
    CoefficientSemipositive ((θ + ddcClosedForm f hf).val.coeff e (e.val x)) := by
  have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hu e (e.val x) hz₀
  have hfchart : ContDiffOn ℝ ∞ (fun y => f (e.val.symm y)) W := (hf e).mono hρ.2.1
  have hq : ContDiffOn ℝ ∞ (fun y => f (e.val.symm y) + ρ y) W := hfchart.add hρ.2.2.1
  have hx' : e.val.symm (e.val x) = x := e.val.left_inv hxe
  have hle' : ∀ᶠ y in 𝓝 (e.val x),
      chartFunction u e y + (ρ y : EReal) ≤ ((f (e.val.symm y) + ρ y : ℝ) : EReal) := by
    have hcont : ContinuousAt e.val.symm (e.val x) := e.val.continuousAt_symm hz₀
    rw [← hx'] at hle
    filter_upwards [hcont.eventually hle] with y hy
    rw [chartFunction, EReal.coe_add]
    exact add_le_add_left hy _
  have heq : chartFunction u e (e.val x) + (ρ (e.val x) : EReal) =
      ((f (e.val.symm (e.val x)) + ρ (e.val x) : ℝ) : EReal) := by
    rw [chartFunction, EReal.coe_add, hx', hx]
  intro v
  have hlevi := EnvelopeLocal.leviForm_nonneg_of_contact hρ.1 hpsh hq hz₀W hle' heq v
  have hq2 : ContDiffAt ℝ 2 (fun y => f (e.val.symm y) + ρ y) (e.val x) :=
    ((hq _ hz₀W).contDiffAt (hρ.1.mem_nhds hz₀W)).of_le EnvelopeLocal.two_le_infty
  have hdiag : 0 ≤ smoothDDC (fun y => f (e.val.symm y) + ρ y) (e.val x) ![v, Complex.I • v] := by
    rw [smoothDDC_complexDiagonal_eq_leviForm hq2 v]
    exact div_nonneg hlevi Real.pi_pos.le
  rw [smoothDDC_add hρ.1 hfchart hρ.2.2.1 hz₀W, hρ.2.2.2 hz₀W] at hdiag
  simp only [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
    ContinuousAlternatingMap.add_apply] at hdiag ⊢
  linarith

/-- The contact set of a `θ`-psh function below a smooth obstacle is closed. -/
theorem isClosed_contact {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ.val u) {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hle : ∀ x, u x ≤ (f x : EReal)) : IsClosed {x | u x = (f x : EReal)} := by
  have husc : UpperSemicontinuous u := hu.quasiPlurisubharmonic.upperSemicontinuous
  have hfc : Continuous f := ProductTestForms.ChartSmooth.continuous hf
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
  have hlt : u x < (f x : EReal) := lt_of_le_of_ne (hle x) hx
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have h1 : ∀ᶠ y in 𝓝 x, u y < (c : EReal) := husc x _ hc1
  have h2 : ∀ᶠ y in 𝓝 x, c < f y :=
    (hfc.continuousAt).eventually (lt_mem_nhds (EReal.coe_lt_coe_iff.mp hc2))
  filter_upwards [h1, h2] with y hy1 hy2
  exact fun h => (lt_irrefl (u y)) (hy1.trans ((EReal.coe_lt_coe_iff.mpr hy2).trans_eq h.symm))

/-- The densities agree: the smooth density of `f + ρ` in a chart is the coefficient density of
`(θ + ddᶜf)ⁿ` when `ρ` is a local potential of `θ`. -/
theorem smoothDensity_eq_topDensity_formPow (θ : ClosedRealOneOneForm n M) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f) {e : ComplexChart n M} {W : Set (ComplexModel n)}
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ.val e W ρ) {z : ComplexModel n}
    (hz : z ∈ W) :
    smoothDensity (fun y => f (e.val.symm y) + ρ y) z =
      topDensity ((formPow (θ + ddcClosedForm f hf).val n).coeff e z) := by
  have hfchart : ContDiffOn ℝ ∞ (fun y => f (e.val.symm y)) W := (hf e).mono hρ.2.1
  have hq2 : ContDiffAt ℝ 2 (fun y => f (e.val.symm y) + ρ y) z :=
    (((hfchart.add hρ.2.2.1) z hz).contDiffAt (hρ.1.mem_nhds hz)).of_le
      EnvelopeLocal.two_le_infty
  have hcoeff : smoothDDC (fun y => f (e.val.symm y) + ρ y) z =
      (θ + ddcClosedForm f hf).val.coeff e z := by
    rw [smoothDDC_add hρ.1 hfchart hρ.2.2.1 hz, hρ.2.2.2 hz, ClosedRealOneOneForm.coeff_add,
      ddcClosedForm_coeff, add_comm]
  rw [← MixedMongeAmpere.mixedDensity_diagonal,
    ← actualMixedTopDensity_smoothDDC (fun _ => hq2), formPow_coeff, topDensity_formPower,
    ← actualMixedTopDensity_const, hcoeff]

/-! ### The measure of a smooth top form -/

section Measures

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The measure `(Φ / ωⁿ) ωⁿ` of a smooth top-degree form `Φ`, truncated at `0` where the
density ratio is negative. -/
def topFormMeasure (w : KahlerBackground n M) (Φ : SmoothRealForm n M (2 * n)) : Measure M :=
  (kahlerVolume w).withDensity fun x => ENNReal.ofReal (topRatio w.form.val Φ x)

/-- **Chart formula.**  On the inverse image of a measurable piece `K` of a chart target,
`topFormMeasure w Φ` is the Lebesgue integral of the coefficient density of `Φ` (in
particular, it does not depend on `ω`). -/
theorem topFormMeasure_image_eq (w : KahlerBackground n M) (Φ : SmoothRealForm n M (2 * n))
    (e : ComplexChart n M) {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKe : K ⊆ e.val.target) :
    topFormMeasure w Φ (e.val.symm '' K) = ∫⁻ z in K, ENNReal.ofReal (topDensity (Φ.coeff e z)) := by
  have hω : ∀ _ : Fin n, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin n => w.form) (fun _ _ => 0) hω := rfl
  have hgm : Measurable fun x => ENNReal.ofReal (topRatio w.form.val Φ x) :=
    ENNReal.measurable_ofReal.comp (continuous_topRatio w.isKahler.1 Φ).measurable
  rw [topFormMeasure, withDensity_apply _ (measurableSet_chartSymm_image e hK hKe), hvol,
    setLIntegral_image_eq hω e hK hKe hgm]
  refine setLIntegral_congr_fun hK fun z hz => ?_
  have hzt : z ∈ e.val.target := hKe hz
  have hx : e.val.symm z ∈ e.val.source := e.val.map_target hzt
  have hR : topRatio w.form.val Φ (e.val.symm z) = chartRatio w.form.val Φ e z := by
    rw [topRatio_eq_chartRatio w.isKahler.1 Φ hx, e.val.right_inv hzt]
  have hden : topDensity ((formPow w.form.val n).coeff e z) =
      actualMixedTopDensity fun _ : Fin n => w.form.val.coeff e z := by
    rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
  have hpos := topDensity_formPow_pos w.isKahler.1 hzt
  simp only [chartDensity]
  rw [hR, chartRatio, ← hden, ← ENNReal.ofReal_mul hpos.le, mul_div_cancel₀ _ hpos.ne']

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The top power of a closed form, read as a slot form. -/
theorem topRatio_formPow_eq_slotForm (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (x : M) :
    topRatio w.form.val (formPow θ.val n) x =
      topRatio w.form.val (MixedMassClassInvariance.slotForm fun _ => θ) x := by
  simp only [topRatio, chartRatio]
  rw [MixedMassClassInvariance.topDensity_slotForm_coeff, formPow_coeff, topDensity_formPower,
    actualMixedTopDensity_const]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The density of `(α + δγ)ⁿ` is a polynomial in `δ`. -/
theorem topRatio_formPow_add_smul (w : KahlerBackground n M) (α γ : ClosedRealOneOneForm n M)
    (δ : ℝ) (x : M) :
    topRatio w.form.val (formPow (α + δ • γ).val n) x =
      ∑ s : Finset (Fin n), (∏ i, if i ∈ s then (1 : ℝ) else δ) *
        topRatio w.form.val (MixedMassClassInvariance.slotForm
          (s.piecewise (fun _ => α) (fun _ => γ))) x := by
  rw [topRatio_formPow_eq_slotForm]
  exact NefMixedMass.topRatio_slotForm_add_smul w (fun _ => α) (fun _ => γ) δ x

omit [CompactSpace M] in
/-- **Finite covers.**  If `μ ≤ ν` on measurable subsets of `E` near every point of the
compact set `E`, then `μ ≤ ν` on every measurable subset of `E`. -/
theorem le_of_local_le {μ ν : Measure M} {E : Set M} (hE : IsCompact E)
    (hloc : ∀ x ∈ E, ∃ N : Set M, IsOpen N ∧ x ∈ N ∧
      ∀ S, MeasurableSet S → S ⊆ N ∩ E → μ S ≤ ν S)
    {S : Set M} (hS : MeasurableSet S) (hSE : S ⊆ E) : μ S ≤ ν S := by
  classical
  choose N hNo hxN hN using hloc
  obtain ⟨t, ht⟩ := hE.elim_finite_subcover (fun x : E => N x.1 x.2)
    (fun x => hNo x.1 x.2) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxN x hx⟩)
  have key : ∀ s : Finset E, ∀ S, MeasurableSet S → S ⊆ E →
      S ⊆ ⋃ i ∈ s, N i.1 i.2 → μ S ≤ ν S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro S _ _ hSs
      have : S = ∅ := by simpa using hSs
      simp [this]
    | insert i s hi ih =>
      intro S hS hSE hSs
      have hNm : MeasurableSet (N i.1 i.2) := (hNo i.1 i.2).measurableSet
      rw [← measure_inter_add_sdiff S hNm, ← measure_inter_add_sdiff (μ := ν) S hNm]
      refine add_le_add (hN i.1 i.2 _ (hS.inter hNm) fun y hy => ⟨hy.2, hSE hy.1⟩) ?_
      refine ih _ (hS.diff hNm) (fun y hy => hSE hy.1) fun y hy => ?_
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp (hSs hy.1)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact absurd hyj hy.2
      · exact mem_iUnion₂.mpr ⟨j, hj, hyj⟩
  exact key t S hS hSE (hSE.trans ht)

/-! ### The contact bound for a strictly positive obstacle form -/

/-- **The contact bound, strictly positive case.**  If `θ + ddᶜf` is strictly positive at
every contact point, then `⟨(θ + ddᶜu)ⁿ⟩ ≤ (θ + ddᶜf)ⁿ` on every measurable subset of the
contact set. -/
theorem diagonalPotentialMeasure_contact_le_of_strictPos (hn : 0 < n) (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal))
    (hpos : ∀ x, u x = (f x : EReal) → StrictPosAt (θ + ddcClosedForm f hf).val x)
    {S : Set M} (hS : MeasurableSet S) (hSE : S ⊆ {x | u x = (f x : EReal)}) :
    diagonalPotentialMeasure θ u hu S ≤
      topFormMeasure w (formPow (θ + ddcClosedForm f hf).val n) S := by
  set E : Set M := {x | u x = (f x : EReal)} with hE
  have hEc : IsCompact E := (isClosed_contact hu.1 hf hle).isCompact
  refine le_of_local_le hEc ?_ hS hSE
  intro x hx
  set e := complexChartAt (n := n) x with he
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hu.1 e (e.val x) hz₀
  set O : Set M := {y | StrictPosAt (θ + ddcClosedForm f hf).val y} with hO
  have hOo : IsOpen O := isOpen_setOf_strictPosAt _
  set W₁ : Set (ComplexModel n) := W ∩ (e.val.target ∩ e.val.symm ⁻¹' O) with hW₁
  have hW₁o : IsOpen W₁ := hρ.1.inter (e.val.isOpen_inter_preimage_symm hOo)
  have hz₀W₁ : e.val x ∈ W₁ := by
    refine ⟨hz₀W, hz₀, ?_⟩
    change StrictPosAt _ (e.val.symm (e.val x))
    rw [e.val.left_inv hxe]
    exact hpos x hx
  have hW₁W : W₁ ⊆ W := inter_subset_left
  have hW₁t : W₁ ⊆ e.val.target := fun y hy => hy.2.1
  let Ω : Opens (ComplexModel n) := ⟨W₁, hW₁o⟩
  set q : ComplexModel n → ℝ := fun y => f (e.val.symm y) + ρ y with hqdef
  have hfchart : ContDiffOn ℝ ∞ (fun y => f (e.val.symm y)) W := (hf e).mono hρ.2.1
  have hqW : ContDiffOn ℝ ∞ q W := hfchart.add hρ.2.2.1
  -- `q` is smooth plurisubharmonic on `W₁`
  have hlevi : ∀ y ∈ W₁, ∀ v, 0 ≤ leviForm q y v := by
    intro y hy v
    have hq2 : ContDiffAt ℝ 2 q y :=
      ((hqW y hy.1).contDiffAt (hρ.1.mem_nhds hy.1)).of_le EnvelopeLocal.two_le_infty
    have hspos : IsStrictlyPositive ((θ + ddcClosedForm f hf).val.coeff e y) := by
      have h := StrictPosAt.isStrictlyPositive hy.2.2 e (e.val.map_target hy.2.1)
      rwa [e.val.right_inv hy.2.1] at h
    have hcoeff : smoothDDC q y = (θ + ddcClosedForm f hf).val.coeff e y := by
      rw [hqdef, smoothDDC_add hρ.1 hfchart hρ.2.2.1 hy.1, hρ.2.2.2 hy.1,
        ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff, add_comm]
    have hsemi : 0 ≤ smoothDDC q y ![v, Complex.I • v] := by
      rw [hcoeff]
      by_cases hv : v = 0
      · subst hv
        rw [((θ + ddcClosedForm f hf).val.coeff e y).map_coord_zero (0 : Fin 2) rfl]
      · exact (hspos v hv).le
    rw [smoothDDC_complexDiagonal_eq_leviForm hq2 v] at hsemi
    have hmul : 0 ≤ (leviForm q y v / Real.pi) * Real.pi := mul_nonneg hsemi Real.pi_pos.le
    rwa [div_mul_cancel₀ _ Real.pi_ne_zero] at hmul
  have hqΩ : IsSmoothPshOn Ω q := by
    refine ⟨hqW.mono hW₁W,
      EnvelopeLocal.plurisubharmonicOn_of_leviForm_nonneg_on hW₁o (hqW.mono hW₁W) hlevi,
      fun y hy => ?_⟩
    exact SmoothDDCHessianPositivity.complexHessian_posSemidef_of_leviForm_nonneg
      (((hqW y hy.1).contDiffAt (hρ.1.mem_nhds hy.1)).of_le EnvelopeLocal.two_le_infty)
      (hlevi y hy)
  -- the corrected potential
  set U : ComplexModel n → EReal := fun y => chartFunction u e y + (ρ y : EReal) with hUdef
  have hU : PlurisubharmonicOn U Ω := hpsh.mono hW₁W
  have hUq : ∀ y ∈ Ω, U y ≤ (q y : EReal) := by
    intro y _
    simp only [hUdef, hqdef, chartFunction, EReal.coe_add]
    exact add_le_add_left (hle _) _
  -- a small ball
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW₁o (e.val x) hz₀W₁
  set R := ε / 3 with hR
  have hR0 : 0 < R := by positivity
  have hball : closedBall (e.val x) (2 * R) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hεW
  refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val x) R,
    e.val.isOpen_inter_preimage isOpen_ball, ⟨hxe, mem_ball_self hR0⟩, ?_⟩
  intro S hS hSN
  -- the coordinate image
  have hSsrc : S ⊆ e.val.source := fun y hy => (hSN hy).1.1
  set T : Set (ComplexModel n) := e.val '' S with hT
  have hTeq : T = e.val.target ∩ e.val.symm ⁻¹' S :=
    e.val.image_eq_target_inter_inv_preimage hSsrc
  have hTm : MeasurableSet T := by
    rw [hTeq]
    exact measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
      e.val.continuousOn_symm hS
  have hTt : T ⊆ e.val.target := by rw [hTeq]; exact inter_subset_left
  have hST : S = e.val.symm '' T := (e.val.symm_image_image_of_subset_source hSsrc).symm
  have hTball : T ⊆ ball (e.val x) R := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hSN hy).1.2
  have hTΩ : T ⊆ Ω := hTball.trans (ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hball))
  have hTC : T ⊆ {z | z ∈ Ω ∧ U z = (q z : EReal)} ∩ ball (e.val x) R := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨hTΩ ⟨y, hy, rfl⟩, ?_⟩, hTball ⟨y, hy, rfl⟩⟩
    have hyE : u y = (f y : EReal) := (hSN hy).2
    simp only [hUdef, hqdef, chartFunction, e.val.left_inv (hSsrc hy), EReal.coe_add, hyE]
  -- the patch of the global measure
  let P : Patch (fun _ : Fin n => θ) (fun _ => u) :=
    { chart := e
      domain := Ω
      domain_le_target := hW₁t
      potential := fun _ => ρ
      localPotential := fun _ => hρ.mono hW₁o hW₁W
      plurisubharmonic := fun _ => hpsh.mono hW₁W }
  have hSP : S ⊆ (P.source : Set M) := by
    intro y hy
    refine ⟨hSsrc hy, hTΩ ⟨y, hy, rfl⟩⟩
  have hlhs : diagonalPotentialMeasure θ u hu S =
      truncationLimitMeasure Ω U hU T := by
    have h1 : diagonalPotentialMeasure θ u hu S =
        (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu.1)).restrict
          (P.source : Set M) S := (Measure.restrict_eq_self _ hSP).symm
    rw [h1, globalMixedMeasure_restrict_patch, patchMeasure, Patch.pushMeasure_apply_image,
      inter_eq_left.mpr hSP]
    change MixedNonPluripolar.mixedTruncationLimitMeasure Ω (fun _ => U) (fun _ => hU) T = _
    rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn hU]
  rw [hlhs, hST, topFormMeasure_image_eq w _ e hTm hTt]
  refine (EnvelopeLocal.truncationLimitMeasure_contact_le hn hU hqΩ hUq hR0 hball hTC).trans
    (le_of_eq ?_)
  refine setLIntegral_congr_fun hTm fun z hz => ?_
  rw [smoothDensity_eq_topDensity_formPow θ hf hρ (hW₁W (hTΩ hz))]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- On the contact set the density of `(θ + ddᶜf)ⁿ` is nonnegative, so that `topFormMeasure`
restricted to the contact set is the genuine measure of the top form. -/
theorem topRatio_nonneg_of_contact (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ.val u) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal)) {x : M}
    (hx : u x = (f x : EReal)) :
    0 ≤ topRatio w.form.val (formPow (θ + ddcClosedForm f hf).val n) x := by
  set e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz := e.val.map_source hxe
  have hsemi : IsSemipositiveOneOne ((θ + ddcClosedForm f hf).val.coeff e (e.val x)) :=
    ⟨(θ + ddcClosedForm f hf).2.2 e _ hz,
      coefficientSemipositive_of_contact θ hu hf (Eventually.of_forall hle) hx e hxe⟩
  simp only [topRatio, chartRatio]
  rw [formPow_coeff, topDensity_formPower, ← actualMixedTopDensity_const]
  exact div_nonneg (actualMixedTopDensity_nonneg fun _ => hsemi)
    (topDensity_formPow_pos w.isKahler.1 hz).le

/-- **`tok-wn:contact-upper`** (the inequality "`≤`" of the Di Nezza–Trapani contact formula).
Let `M` be a compact complex manifold with a Kähler background `w`, `θ` a closed real
`(1,1)`-form, `f` smooth, `u ∈ PSH(M, θ)` with `u ≤ f`, and `E = {u = f}`.  Then
`𝟙_E ⟨(θ + ddᶜu)ⁿ⟩ ≤ 𝟙_E (θ + ddᶜf)ⁿ`. -/
theorem diagonalPotentialMeasure_restrict_contact_le (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} ≤
      (topFormMeasure w (formPow (θ + ddcClosedForm f hf).val n)).restrict
        {x | u x = (f x : EReal)} := by
  set E : Set M := {x | u x = (f x : EReal)} with hE
  have hEm : MeasurableSet E := (isClosed_contact hu.1 hf hle).measurableSet
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : diagonalPotentialMeasure θ u hu = kahlerVolume w :=
      AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples (Subsingleton.elim _ _)
        (Subsingleton.elim _ _) _ (fun _ =>
          ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1)
    have h2 : topFormMeasure w (formPow (θ + ddcClosedForm f hf).val 0) = kahlerVolume w := by
      have hd : (fun x => ENNReal.ofReal
          (topRatio w.form.val (formPow (θ + ddcClosedForm f hf).val 0) x)) = fun _ => 1 := by
        funext x
        have : formPow (θ + ddcClosedForm f hf).val 0 = formPow w.form.val 0 := rfl
        rw [this, topRatio_formPow w.isKahler.1, ENNReal.ofReal_one]
      rw [topFormMeasure, hd]
      exact withDensity_one
    rw [h1, h2]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  have hAE : MeasurableSet (A ∩ E) := hA.inter hEm
  set α : ClosedRealOneOneForm n M := θ + ddcClosedForm f hf with hα
  -- the bound for each `δ > 0`
  have hδ : ∀ δ : ℝ, 0 < δ → diagonalPotentialMeasure θ u hu (A ∩ E) ≤
      ∫⁻ x in A ∩ E, ENNReal.ofReal (topRatio w.form.val (formPow (α + δ • w.form).val n) x)
        ∂kahlerVolume w := by
    intro δ hδ
    have hsemi : (δ • w.form).val.IsSemipositive := fun e z hz v => by
      simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul]
      exact mul_nonneg hδ.le (w.isSemipositive e z hz v)
    have huδ : IsThetaPshPotential (θ + δ • w.form).val u :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hu hsemi
    have hmono : diagonalPotentialMeasure θ u hu ≤
        diagonalPotentialMeasure (θ + δ • w.form) u huδ :=
      AmbientMassBackgroundMonotone.globalMixedMeasure_diagonal_le_add_smul w.isSemipositive hδ
        hu huδ.1
    have hform : θ + δ • w.form + ddcClosedForm f hf = α + δ • w.form := by
      rw [hα]
      abel
    have hposδ : ∀ x, u x = (f x : EReal) →
        StrictPosAt (θ + δ • w.form + ddcClosedForm f hf).val x := by
      intro x hx v hv
      rw [hform]
      set e := complexChartAt (n := n) x
      have hxe : x ∈ e.val.source := mem_complexChartAt_source x
      have h1 := coefficientSemipositive_of_contact θ hu.1 hf (Eventually.of_forall hle) hx e
        hxe v
      have h2 := (w.isKahler.1 e (e.val x) (e.val.map_source hxe)).2 v hv
      change 0 < (α + δ • w.form).val.coeff e (e.val x) ![v, Complex.I • v]
      rw [hα]
      simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
        ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at h1 h2 ⊢
      nlinarith
    calc diagonalPotentialMeasure θ u hu (A ∩ E)
        ≤ diagonalPotentialMeasure (θ + δ • w.form) u huδ (A ∩ E) := hmono _
      _ ≤ topFormMeasure w (formPow (θ + δ • w.form + ddcClosedForm f hf).val n) (A ∩ E) :=
          diagonalPotentialMeasure_contact_le_of_strictPos hn w (θ + δ • w.form) huδ hf hle hposδ
            hAE inter_subset_right
      _ = _ := by rw [hform, topFormMeasure, withDensity_apply _ hAE]
  -- the limit `δ → 0`
  have hcs : ∀ s : Finset (Fin n), ∃ C : ℝ, ∀ x, |topRatio w.form.val
      (MixedMassClassInvariance.slotForm (s.piecewise (fun _ => α) (fun _ => w.form))) x| ≤ C := by
    intro s
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_topRatio w.isKahler.1 (MixedMassClassInvariance.slotForm
        (s.piecewise (fun _ => α) (fun _ => w.form)))).continuousOn
    exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x (mem_univ x)⟩
  choose C hC using hcs
  have hbound : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ x,
      |topRatio w.form.val (formPow (α + δ • w.form).val n) x| ≤ ∑ s, C s := by
    intro δ h0 h1 x
    rw [topRatio_formPow_add_smul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul]
    have hp : |∏ i : Fin n, (if i ∈ s then (1 : ℝ) else δ)| ≤ 1 := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_one (fun i _ => abs_nonneg _) fun i _ => ?_
      by_cases hi : i ∈ s
      · simp [hi]
      · simp only [hi, if_false, abs_of_nonneg h0]
        exact h1
    calc _ ≤ 1 * C s := mul_le_mul hp (hC s x) (abs_nonneg _) zero_le_one
      _ = C s := one_mul _
  have hcont : ∀ x, Continuous fun δ : ℝ =>
      topRatio w.form.val (formPow (α + δ • w.form).val n) x := by
    intro x
    simp_rw [topRatio_formPow_add_smul]
    exact continuous_finsetSum _ fun s _ => Continuous.mul (continuous_finsetProd _ fun i _ =>
      continuous_if_const _ (fun _ => continuous_const) fun _ => continuous_id) continuous_const
  set δs : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hδs
  have hδs0 : ∀ j, 0 < δs j := fun j => by positivity
  have hδs1 : ∀ j, δs j ≤ 1 := fun j => by
    rw [hδs, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hδslim : Tendsto δs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun j => ∫⁻ x in A ∩ E, ENNReal.ofReal
      (topRatio w.form.val (formPow (α + δs j • w.form).val n) x) ∂kahlerVolume w) atTop
      (𝓝 (∫⁻ x in A ∩ E, ENNReal.ofReal (topRatio w.form.val (formPow α.val n) x)
        ∂kahlerVolume w)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (∑ s, C s))
      (fun j => ENNReal.measurable_ofReal.comp (continuous_topRatio w.isKahler.1 _).measurable)
      (fun j => Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (hbound _ (hδs0 j).le (hδs1 j) x))) ?_ ?_
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · refine Eventually.of_forall fun x => ?_
      have h0 : topRatio w.form.val (formPow α.val n) x =
          topRatio w.form.val (formPow (α + (0 : ℝ) • w.form).val n) x := by
        rw [zero_smul, add_zero]
      rw [h0]
      exact (ENNReal.continuous_ofReal.tendsto _).comp (((hcont x).tendsto 0).comp hδslim)
  rw [topFormMeasure, withDensity_apply _ hAE]
  exact ge_of_tendsto' hlim fun j => hδ (δs j) (hδs0 j)

/-- **The envelope of a smooth obstacle** (`tok-wn:contact-upper`, last assertion).  For
`u = P_θ(f)` (the rooftop envelope of the smooth obstacle `f`) a genuine `θ`-psh function,
`⟨(θ + ddᶜu)ⁿ⟩ ≤ 𝟙_{u = f} (θ + ddᶜf)ⁿ`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_le_contact [ConnectedSpace M]
    (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f)
    (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal))) :
    diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP ≤
      (topFormMeasure w (formPow (θ + ddcClosedForm f hf).val n)).restrict
        {x | rooftopEnvelope θ.val (fun y => (f y : EReal)) x = (f x : EReal)} := by
  set P := rooftopEnvelope θ.val fun x => (f x : EReal) with hPdef
  have hfc : Continuous f := ProductTestForms.ChartSmooth.continuous hf
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hnb : P ≠ fun _ => ⊥ := by
    intro h
    obtain ⟨y, -, hy⟩ := hP.2 x₀ univ isOpen_univ (mem_univ x₀)
    exact hy (congrFun h y)
  have hnt : P ≠ fun _ => ⊤ := by
    intro h
    exact hP.1.quasiPlurisubharmonic.ne_top x₀ (congrFun h x₀)
  have hne : (rooftopCompetitors θ.val fun x => (f x : EReal)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    apply hnb
    rw [hPdef, rooftopEnvelope, rooftopSupremum, hemp, sSup_empty]
    exact uscRegularization_const ⊥
  have hle : ∀ x, P x ≤ (f x : EReal) := fun x =>
    ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous hfc hne hP.1 x
  have hqc : ActualExtendedObstacleQuasiContinuity.QuasiContinuousERealFor
      (ThetaCapacity.thetaCapacity w.form (fun _ => 0)) fun x => (f x : EReal) := by
    intro η hη
    refine ⟨∅, isOpen_empty, ?_, ?_⟩
    · rw [ThetaCapacity.thetaCapacity_empty]
      exact hη
    · exact (continuous_coe_real_ereal.comp hfc).continuousOn
  obtain ⟨hP', -, hneq⟩ :=
    ActualQuasiContinuousEnvelopeContact.exists_genuine_envelope_and_contact w θ hqc hnb hnt
  have hcarried : diagonalPotentialMeasure θ P hP =
      (diagonalPotentialMeasure θ P hP).restrict {x | P x = (f x : EReal)} := by
    refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
    rw [ae_iff]
    exact hneq
  rw [hcarried]
  exact diagonalPotentialMeasure_restrict_contact_le w θ hP hf hle

end Measures

/-! ### The source-facing statements -/

section Source

open SGPT.PSH.VariableComplexAtlas

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **`tok-wn:contact-upper`** for the source-facing non-pluripolar measures: for
`u ∈ PSH(M, θ)` with `u ≤ f`, `𝟙_E ⟨(θ + ddᶜu)ⁿ⟩ ≤ 𝟙_E (θ + ddᶜf)ⁿ` on `E = {u = f}`. -/
theorem sourcePotentialNonPluripolarMeasure_restrict_contact_le (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hle : ∀ x, u x ≤ (f x : EReal)) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | u x = (f x : EReal)} ≤
      (topFormMeasure w (formPow (atlasClosedFormToNative θ + ddcClosedForm f hf).val n)).restrict
        {x | u x = (f x : EReal)} :=
  diagonalPotentialMeasure_restrict_contact_le w (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hf hle

/-- **The envelope of a smooth obstacle**, source-facing form: for the source envelope
`P = P_θ(f)` (`sourceRelativeEnvelope θ ⊤ f`) a genuine `θ`-psh function,
`⟨(θ + ddᶜP)ⁿ⟩ ≤ 𝟙_{P = f} (θ + ddᶜf)ⁿ`. -/
theorem sourceObstacleEnvelope_measure_le_contact [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hP : (ofFixedModel n M).IsThetaPSH θ
      (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal))) :
    sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP ≤
      (topFormMeasure w (formPow (atlasClosedFormToNative θ + ddcClosedForm f hf).val n)).restrict
        {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x = (f x : EReal)} := by
  have heq := sourceObstacleEnvelope_eq_native θ (fun x => (f x : EReal))
  have hP' : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (rooftopEnvelope (atlasClosedFormToNative θ).val fun x => (f x : EReal)) := by
    rw [← heq]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mp hP
  have h := diagonalPotentialMeasure_rooftopEnvelope_le_contact w (atlasClosedFormToNative θ) hf hP'
  calc sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP
      = diagonalPotentialMeasure (atlasClosedFormToNative θ)
          (rooftopEnvelope (atlasClosedFormToNative θ).val fun x => (f x : EReal)) hP' :=
        MaxMassDecomposition.diagonalPotentialMeasure_congr _ hP' heq
    _ ≤ _ := h
    _ = _ := by rw [heq]

end Source

end SGPT.Okounkov.TranscendentalWN
