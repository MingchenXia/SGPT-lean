import SGPT.Foundations.Analysis.Pending.DecreasingLimitOpenMeasure
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.FirstPass.PotentialL1
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord
import SGPT.Foundations.Analysis.PshRegularDistribution

set_option autoImplicit false

/-!
# Contact mass along a decreasing sequence (Xia, Corollary 2.4.2)

For nonpositive `theta`-PSH potentials `u_j` decreasing to `v`,

  `limsup_j theta^n_{u_j}({u_j = 0}) ≤ theta^n_v({v = 0})`

(`contactMeasure_limsup_le_of_antitone_of_tendsto`), and the same under the
chart-local `L¹` hypothesis of `RooftopMassDiamondLimit`
(`contactMeasure_limsup_le_of_manifoldL1LocallyTendsto`).  This is Xia's
Corollary 2.4.2 (`xia-sgpt:page-0077`--`page-0078`) in the antitone case, where
Xia's `psi_k = sup*_{j ≥ k} phi_j` is `u_k` itself.

## The proof

Xia truncates at `V_theta - C`; we truncate at `psi = u_0 - 1` instead, which
needs no envelope and has the two properties used: `psi < 0` (so the contact sets
`{u_j = 0}` and `{v = 0}` lie in the plurifine open sets `{u_j > psi}`, `{v > psi}`,
where plurifine locality identifies `theta^n_{u_j}` with `theta^n_{w_j}`,
`w_j = max(u_j, psi)`), and `u_0 - 1 ≤ w_j ≤ u_0` (so every `w_j` and
`w = max(v, psi)` has the mass of `u_0`, by the monotonicity theorem in its
Kähler form `diagonalPotentialMass_mono_of_kahler`).  The decreasing
semicontinuity theorem with equal masses
(`DecreasingLimitOpenMeasure.diagonalPotentialMeasure_limsup_le_of_antitone`)
then bounds `limsup_j theta^n_{w_j}(F)` by `theta^n_w(F)` on the closed sets
`F_m = {u_m ≥ -1/(m+1)}`, which contain `{u_j = 0}` for `j ≥ m` and decrease to
`{v = 0}`.

Under the `L¹` hypothesis the pointwise limit is identified first
(`tendsto_of_antitone_of_manifoldL1LocallyTendsto`): the `L¹` limit of a
decreasing sequence agrees with its pointwise infimum almost everywhere in every
chart, hence everywhere, both being `theta`-PSH
(`ThetaPlurisubharmonic.le_of_ae_in_charts_le`).
-/

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DecreasingContactMassLimit

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

/-! ### The pointwise limit of an `L¹`-convergent decreasing sequence -/

section L1

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The canonical absolute difference of two finite extended reals is the
ordinary absolute difference of their real parts. -/
theorem canonicalERealAbsDiff_eq_ofReal_abs {a b : EReal} (ha : a ≠ ⊤) (ha' : a ≠ ⊥)
    (hb : b ≠ ⊤) (hb' : b ≠ ⊥) :
    canonicalERealAbsDiff a b = ENNReal.ofReal |a.toReal - b.toReal| := by
  conv_lhs => rw [← EReal.coe_toReal ha ha', ← EReal.coe_toReal hb hb']
  exact canonicalERealAbsDiff_coe_coe _ _

/-- On a compact subset of a chart target, the chart-local `L¹` limit of a
decreasing sequence of `theta`-PSH potentials agrees almost everywhere with its
pointwise infimum. -/
theorem ae_chartFunction_eq_iInf_of_manifoldL1LocallyTendsto
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hanti : Antitone u)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hL1 : ManifoldL1LocallyTendsto (n := n) u atTop v)
    (e : ComplexChart n M) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKe : K ⊆ e.val.target) :
    ∀ᵐ z ∂(volume.restrict K), chartFunction v e z = ⨅ j, chartFunction (u j) e z := by
  have hfin : ∀ᵐ z ∂(volume.restrict K),
      (chartFunction v e z ≠ ⊤ ∧ chartFunction v e z ≠ ⊥) ∧
        ∀ j, chartFunction (u j) e z ≠ ⊤ ∧ chartFunction (u j) e z ≠ ⊥ := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hKe (hv.quasiPshPotential.ae_finite_chart e)
    have h2 : ∀ᵐ z ∂(volume.restrict K), ∀ j,
        chartFunction (u j) e z ≠ ⊤ ∧ chartFunction (u j) e z ≠ ⊥ := by
      rw [ae_all_iff]
      exact fun j => ae_restrict_of_ae_restrict_of_subset hKe
        ((hu j).quasiPshPotential.ae_finite_chart e)
    filter_upwards [h1, h2] with z hz1 hz2
    exact ⟨hz1, hz2⟩
  have hmeasv : AEMeasurable (fun z => (chartFunction v e z).toReal) (volume.restrict K) :=
    measurable_ereal_toReal.comp_aemeasurable
      (hv.quasiPshPotential.aemeasurable_chart_restrict e hKe)
  have hmeasu : ∀ j, AEMeasurable (fun z => (chartFunction (u j) e z).toReal)
      (volume.restrict K) := fun j =>
    measurable_ereal_toReal.comp_aemeasurable
      ((hu j).quasiPshPotential.aemeasurable_chart_restrict e hKe)
  have hmeasinf : AEMeasurable (fun z => (⨅ j, chartFunction (u j) e z).toReal)
      (volume.restrict K) :=
    measurable_ereal_toReal.comp_aemeasurable
      (AEMeasurable.iInf fun j => (hu j).quasiPshPotential.aemeasurable_chart_restrict e hKe)
  -- a nonnegative function dominated by all late distances has zero integral
  have hzero : ∀ (f : ComplexModel n → ℝ≥0∞) (j : ℕ),
      (∀ k, j ≤ k → ∫⁻ z in K, f z ≤ chartL1EDistance (u k) v e K) → ∫⁻ z in K, f z = 0 :=
    fun f j hf => le_antisymm (ge_of_tendsto (hL1 e K hK hKe)
      ((eventually_ge_atTop j).mono hf)) bot_le
  -- Step 1: `v ≤ u_j` almost everywhere, for each `j`
  have h1 : ∀ j, ∀ᵐ z ∂(volume.restrict K), chartFunction v e z ≤ chartFunction (u j) e z := by
    intro j
    have hint : ∫⁻ z in K, ENNReal.ofReal ((chartFunction v e z).toReal -
        (chartFunction (u j) e z).toReal) = 0 := by
      refine hzero _ j fun k hjk => lintegral_mono_ae ?_
      filter_upwards [hfin] with z ⟨hvz, huz⟩
      rw [canonicalERealAbsDiff_eq_ofReal_abs (huz k).1 (huz k).2 hvz.1 hvz.2]
      refine ENNReal.ofReal_le_ofReal ?_
      have hkj : (chartFunction (u k) e z).toReal ≤ (chartFunction (u j) e z).toReal :=
        EReal.toReal_le_toReal (hanti hjk (e.val.symm z)) (huz k).2 (huz j).1
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    have hae := (lintegral_eq_zero_iff' (hmeasv.sub (hmeasu j)).ennreal_ofReal).mp hint
    filter_upwards [hae, hfin] with z hz ⟨hvz, huz⟩
    have hle : (chartFunction v e z).toReal ≤ (chartFunction (u j) e z).toReal := by
      simp only [Pi.sub_apply, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
      linarith
    rw [← EReal.coe_toReal hvz.1 hvz.2, ← EReal.coe_toReal (huz j).1 (huz j).2]
    exact EReal.coe_le_coe_iff.mpr hle
  have h1all : ∀ᵐ z ∂(volume.restrict K), chartFunction v e z ≤ ⨅ j, chartFunction (u j) e z :=
    (ae_all_iff.mpr h1).mono fun z hz => le_iInf hz
  -- Step 2: the infimum is at most `v` almost everywhere
  have hint2 : ∫⁻ z in K, ENNReal.ofReal ((⨅ j, chartFunction (u j) e z).toReal -
      (chartFunction v e z).toReal) = 0 := by
    refine hzero _ 0 fun k _ => lintegral_mono_ae ?_
    filter_upwards [hfin, h1all] with z ⟨hvz, huz⟩ hvinf
    rw [canonicalERealAbsDiff_eq_ofReal_abs (huz k).1 (huz k).2 hvz.1 hvz.2]
    refine ENNReal.ofReal_le_ofReal ?_
    have hinfk : (⨅ j, chartFunction (u j) e z) ≤ chartFunction (u k) e z := iInf_le _ k
    have hinfbot : (⨅ j, chartFunction (u j) e z) ≠ ⊥ := ne_bot_of_le_ne_bot hvz.2 hvinf
    have hle : (⨅ j, chartFunction (u j) e z).toReal ≤ (chartFunction (u k) e z).toReal :=
      EReal.toReal_le_toReal hinfk hinfbot (huz k).1
    exact le_trans (by linarith) (le_abs_self _)
  have hae2 := (lintegral_eq_zero_iff' (hmeasinf.sub hmeasv).ennreal_ofReal).mp hint2
  filter_upwards [hae2, hfin, h1all] with z hz ⟨hvz, huz⟩ hvinf
  have hinfbot : (⨅ j, chartFunction (u j) e z) ≠ ⊥ := ne_bot_of_le_ne_bot hvz.2 hvinf
  have hinftop : (⨅ j, chartFunction (u j) e z) ≠ ⊤ :=
    ne_top_of_le_ne_top (huz 0).1 (iInf_le _ 0)
  have hle : (⨅ j, chartFunction (u j) e z).toReal ≤ (chartFunction v e z).toReal := by
    simp only [Pi.sub_apply, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
    linarith
  refine le_antisymm hvinf ?_
  rw [← EReal.coe_toReal hvz.1 hvz.2, ← EReal.coe_toReal hinftop hinfbot]
  exact EReal.coe_le_coe_iff.mpr hle

/-- **A decreasing sequence of `theta`-PSH potentials converges pointwise to its
chart-local `L¹` limit.**  The `L¹` limit and the pointwise infimum agree almost
everywhere in every chart, and both are `theta`-PSH, so they agree everywhere. -/
theorem tendsto_of_antitone_of_manifoldL1LocallyTendsto
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hanti : Antitone u)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hL1 : ManifoldL1LocallyTendsto (n := n) u atTop v) :
    ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)) := by
  have hanti' : ∀ x : M, Antitone fun j => u j x := fun x a b h => hanti h x
  have hinf : ThetaPlurisubharmonic theta.val (fun x => ⨅ j, u j x) :=
    ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone (fun k => (hu k).1) hanti'
  have hae : ∀ e : ComplexChart n M,
      ∀ᵐ z ∂((volume : Measure (ComplexModel n)).restrict e.val.target),
        v (e.val.symm z) = ⨅ j, u j (e.val.symm z) := by
    intro e
    apply ae_restrict_of_open_neighborhood_ae
    intro z hz
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp e.val.open_target z hz
    refine ⟨ball z (ε / 2), isOpen_ball, mem_ball_self (half_pos hε), ?_⟩
    have hK : closedBall z (ε / 2) ⊆ e.val.target :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεsub
    exact ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall
      (ae_chartFunction_eq_iInf_of_manifoldL1LocallyTendsto u hu hanti hv hL1 e
        (isCompact_closedBall z (ε / 2)) hK)
  have hle1 : v ≤ fun x => ⨅ j, u j x :=
    RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hv.1 hinf
      fun e => (hae e).mono fun z hz => hz.le
  have hle2 : (fun x => ⨅ j, u j x) ≤ v :=
    RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hinf hv.1
      fun e => (hae e).mono fun z hz => hz.ge
  intro x
  rw [show v x = ⨅ j, u j x from le_antisymm (hle1 x) (hle2 x)]
  exact tendsto_atTop_iInf (hanti' x)

end L1

/-! ### The contact mass -/

section Contact

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia, Corollary 2.4.2, antitone sequence form, pointwise hypothesis.**
If nonpositive `theta`-PSH potentials `u_j` decrease pointwise to a `theta`-PSH
potential `v`, the masses of their zero-contact sets satisfy
`limsup_j theta^n_{u_j}({u_j = 0}) ≤ theta^n_v({v = 0})`. -/
theorem contactMeasure_limsup_le_of_antitone_of_tendsto
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0) (v : M → EReal)
    (hv : IsThetaPshPotential theta.val v)
    (hanti : Antitone u) (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x))) :
    limsup (fun j => diagonalPotentialMeasure theta (u j) (hu j) {x | u j x = 0}) atTop ≤
      diagonalPotentialMeasure theta v hv {x | v x = 0} := by
  have hanti' : ∀ x : M, Antitone fun j => u j x := fun x a b h => hanti h x
  have hvu : ∀ j x, v x ≤ u j x := fun j x => (hanti' x).le_of_tendsto (hlim x) j
  have hv0 : ∀ x, v x ≤ 0 := fun x => (hvu 0 x).trans (hu0 0 x)
  -- the floor `psi = u_0 - 1`
  have hψ : IsThetaPshPotential theta.val (fun x => u 0 x + ((-1 : ℝ) : EReal)) :=
    (hu 0).add_const (-1)
  have hψneg : ∀ x, u 0 x + ((-1 : ℝ) : EReal) < 0 := by
    intro x
    calc u 0 x + ((-1 : ℝ) : EReal) ≤ 0 + ((-1 : ℝ) : EReal) := add_le_add (hu0 0 x) le_rfl
      _ < 0 := by rw [zero_add]; exact EReal.coe_lt_coe_iff.mpr (by norm_num)
  have hψle : ∀ x, u 0 x + ((-1 : ℝ) : EReal) ≤ u 0 x := by
    intro x
    calc u 0 x + ((-1 : ℝ) : EReal) ≤ u 0 x + 0 :=
          add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by norm_num))
      _ = u 0 x := add_zero _
  -- plurifine locality on the contact sets
  have hloc : ∀ {a : M → EReal} (ha : IsThetaPshPotential theta.val a)
      (hm : IsThetaPshPotential theta.val (fun x => max (a x) (u 0 x + ((-1 : ℝ) : EReal)))),
      diagonalPotentialMeasure theta a ha {x | a x = 0} =
        diagonalPotentialMeasure theta (fun x => max (a x) (u 0 x + ((-1 : ℝ) : EReal))) hm
          {x | a x = 0} := by
    intro a ha hm
    have h := MaxMassDecomposition.diagonalPotentialMeasure_restrict_max_eq theta ha hψ hm
    have hE : MeasurableSet {x | a x = 0} :=
      measurableSet_eq_fun ha.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
        measurable_const
    have hsub : {x | a x = 0} ⊆ {x | u 0 x + ((-1 : ℝ) : EReal) < a x} := by
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx]
      exact hψneg x
    have h' := congrArg (fun μ : Measure M => μ {x | a x = 0}) h
    simp only [Measure.restrict_apply hE, inter_eq_left.mpr hsub] at h'
    exact h'.symm
  -- equal total masses, by the monotonicity theorem
  have hmassw : ∀ {a : M → EReal}
      (hm : IsThetaPshPotential theta.val (fun x => max (a x) (u 0 x + ((-1 : ℝ) : EReal)))),
      (∀ x, a x ≤ u 0 x) →
      diagonalPotentialMass theta (fun x => max (a x) (u 0 x + ((-1 : ℝ) : EReal))) hm =
        diagonalPotentialMass theta (u 0) (hu 0) := by
    intro a hm hle
    refine le_antisymm (diagonalPotentialMass_mono_of_kahler omega hm (hu 0)
      (MoreSingularOn.of_le fun x _ => max_le (hle x) (hψle x)))
      (diagonalPotentialMass_mono_of_kahler omega (hu 0) hm ⟨1, fun x _ => ?_⟩)
    calc u 0 x = u 0 x + ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; norm_num
      _ ≤ max (a x) (u 0 x + ((-1 : ℝ) : EReal)) + ((1 : ℝ) : EReal) :=
          add_le_add (le_max_right _ _) le_rfl
  have hw : ∀ j, IsThetaPshPotential theta.val
      (fun x => max (u j x) (u 0 x + ((-1 : ℝ) : EReal))) := fun j =>
    Pending.IsThetaPshPotential.max (hu j) hψ
  have hwv : IsThetaPshPotential theta.val
      (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) :=
    Pending.IsThetaPshPotential.max hv hψ
  have hmass : ∀ j, diagonalPotentialMass theta
      (fun x => max (u j x) (u 0 x + ((-1 : ℝ) : EReal))) (hw j) =
        diagonalPotentialMass theta (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) hwv :=
    fun j => (hmassw (hw j) fun x => hanti (Nat.zero_le j) x).trans
      (hmassw hwv fun x => hvu 0 x).symm
  have hwanti : Antitone fun j x => max (u j x) (u 0 x + ((-1 : ℝ) : EReal)) :=
    fun i j hij x => max_le_max (hanti hij x) le_rfl
  have hwlim : ∀ x, Tendsto (fun j => max (u j x) (u 0 x + ((-1 : ℝ) : EReal))) atTop
      (𝓝 (max (v x) (u 0 x + ((-1 : ℝ) : EReal)))) :=
    fun x => (hlim x).max tendsto_const_nhds
  -- the closed sets `F_m = {u_m ≥ -1/(m+1)}`
  set F : ℕ → Set M := fun m => {x | ((-(1 / ((m : ℝ) + 1)) : ℝ) : EReal) ≤ u m x} with hFdef
  have hFc : ∀ m, IsClosed (F m) := fun m =>
    (hu m).1.quasiPlurisubharmonic.upperSemicontinuous.isClosed_preimage _
  have hFanti : Antitone F := by
    intro m m' hmm' x hx
    simp only [hFdef, mem_ofPred_eq] at hx ⊢
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hx.trans (hanti hmm' x))
    exact neg_le_neg (Nat.one_div_le_one_div hmm')
  have hsubF : ∀ m j, m ≤ j → {x | u j x = 0} ⊆ F m := by
    intro m j hmj x hx
    simp only [hFdef, mem_ofPred_eq] at hx ⊢
    refine le_trans ?_ (le_of_eq_of_le hx.symm (hanti hmj x))
    exact EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr (by positivity))
  have hinter : (⋂ m, F m) ⊆ {x | v x = 0} := by
    intro x hx
    simp only [mem_iInter, hFdef, mem_ofPred_eq] at hx
    simp only [mem_ofPred_eq]
    have hge : ∀ m₀ : ℕ, ((-(1 / ((m₀ : ℝ) + 1)) : ℝ) : EReal) ≤ v x := by
      intro m₀
      refine ge_of_tendsto (hlim x) ((eventually_ge_atTop m₀).mono fun m hm => ?_)
      exact le_trans (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.one_div_le_one_div hm))) (hx m)
    have hbot : v x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hge 0)
    have htop : v x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hv0 x)
    have hv0x := hv0 x
    rw [← EReal.coe_toReal htop hbot] at hge hv0x ⊢
    have hle0 : (v x).toReal ≤ 0 := EReal.coe_le_coe_iff.mp hv0x
    have hge0 : 0 ≤ (v x).toReal := by
      by_contra hneg
      obtain ⟨m₀, hm₀⟩ := exists_nat_one_div_lt (neg_pos.mpr (not_le.mp hneg))
      have := EReal.coe_le_coe_iff.mp (hge m₀)
      linarith
    exact_mod_cast le_antisymm hle0 hge0
  -- assemble
  have hfinite : IsFiniteMeasure (diagonalPotentialMeasure theta
      (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) hwv) :=
    GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega (fun _ => hwv.1)
  have hstep : ∀ m, limsup (fun j => diagonalPotentialMeasure theta (u j) (hu j)
      {x | u j x = 0}) atTop ≤ diagonalPotentialMeasure theta
        (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) hwv (F m) := by
    intro m
    refine le_trans (limsup_le_limsup ?_) (DecreasingLimitOpenMeasure.diagonalPotentialMeasure_limsup_le_of_antitone
      omega _ hw hwanti hwv hwlim hmass (hFc m))
    filter_upwards [eventually_ge_atTop m] with j hj
    rw [hloc (hu j) (hw j)]
    exact measure_mono (hsubF m j hj)
  have hiInter := hFanti.measure_iInter (μ := diagonalPotentialMeasure theta
      (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) hwv)
    (fun m => (hFc m).measurableSet.nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  calc limsup (fun j => diagonalPotentialMeasure theta (u j) (hu j) {x | u j x = 0}) atTop
      ≤ ⨅ m, diagonalPotentialMeasure theta
          (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) hwv (F m) := le_iInf hstep
    _ = diagonalPotentialMeasure theta
          (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) hwv (⋂ m, F m) := hiInter.symm
    _ ≤ diagonalPotentialMeasure theta
          (fun x => max (v x) (u 0 x + ((-1 : ℝ) : EReal))) hwv {x | v x = 0} :=
        measure_mono hinter
    _ = diagonalPotentialMeasure theta v hv {x | v x = 0} := (hloc hv hwv).symm

/-- **Xia, Corollary 2.4.2, antitone sequence form, chart-local `L¹` hypothesis**
-- exactly the hypotheses of
`RooftopMassDiamondLimit.contactMass_limsup_le_of_manifoldL1LocallyTendsto`. -/
theorem contactMeasure_limsup_le_of_manifoldL1LocallyTendsto
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0) (v : M → EReal)
    (hv : IsThetaPshPotential theta.val v)
    (hanti : Antitone u)
    (hL1 : ManifoldL1LocallyTendsto (n := n) u atTop v) :
    limsup (fun j => diagonalPotentialMeasure theta (u j) (hu j) {x | u j x = 0}) atTop ≤
      diagonalPotentialMeasure theta v hv {x | v x = 0} :=
  contactMeasure_limsup_le_of_antitone_of_tendsto omega theta u hu hu0 v hv hanti
    (tendsto_of_antitone_of_manifoldL1LocallyTendsto u hu hanti hv hL1)

end Contact

end

end SGPT.Foundations.Analysis.Pending.DecreasingContactMassLimit
