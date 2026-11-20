import SGPT.Hodge.ExceptionalScalar
import SGPT.Hodge.Trace
import SGPT.BDivisor.Modification3AugmentedNef
import SGPT.Foundations.Analysis.Pending.GlobalSmoothScalarDistribution
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
import SGPT.Foundations.Analysis.Pending.MeteredDivisorWeightBounds
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

/-!
# Independence of the classes of exceptional divisors

Let `π : Y → X` be a modification of compact complex manifolds (`IsAnalyticModification`: proper,
holomorphic, biholomorphic off nowhere dense analytic sets). A prime divisor `E` of `Y` is
`π`-exceptional if `E ⊆ Exc π`.

* `ddc_liouville` (`claude-hodge:lem-ddc-liouville`): on a compact connected Kähler manifold a
  compatible family of scalar distributions with `ddᶜ = 0` is a constant.
* `exceptional_independence` (`claude-hodge:prop-exceptional-independence`): **if
  `∑_{E ∈ F} a_E {E} = π^*β` for a finite set `F` of `π`-exceptional prime divisors, then all
  `a_E = 0` and `β = 0`.**

This replaces the argument "factoring `π` into blow-ups and using `prop:blowup_cone` at each step,
the classes of `π`-exceptional prime divisors are linearly independent" of the proof of
`lma:pushIpo` (chapter *The theory of b-divisors*); it holds for every modification, without
Hironaka's Chow lemma, and needs neither a Kähler form nor connectedness.

Proof. Pushing forward, `β = π_*π^*β = ∑ a_E π_*{E} = 0`. Write `[E] = Θ_E + ddᶜψ_E` (Lelong–Poincaré:
the chosen metric of `E`, `ψ_E` smooth off `E` and `→ -∞` at `E`). As `{∑ a_E Θ_E} = 0`,
`∑ a_E Θ_E = ddᶜv` with `v` smooth, so `∑ a_E [E] = ddᶜ[S]` for the function
`S = v + ∑ a_E ψ_E`. Then `ddᶜ π_*[S] = π_*∑ a_E[E] = 0`, so `π_*[S] = [F]` for a smooth function
`F` on `X` (local Weyl lemma and gluing). Since `π_*[F ∘ π] = [F]`, the current `[S] - [F ∘ π]`
has zero push-forward, hence vanishes off `Exc π`, and `S = F ∘ π` there. At a point `p` of `E₀`
outside the other members of `F`, `F ∘ π` and all `ψ_E`, `E ≠ E₀`, are bounded, while
`ψ_{E₀} → -∞`; as `Exc π` has empty interior, `a_{E₀} = 0`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.Hodge.Exceptional

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalCurrents
  SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose
  SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.ProductTestForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor SGPT.Currents.AnalyticSupport

/-! ### `ddᶜ`-Liouville -/

section Liouville

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`ddᶜ`-Liouville** (`claude-hodge:lem-ddc-liouville`): on a compact connected Kähler manifold,
a global scalar distribution (a compatible family of chart distributions) with `ddᶜ = 0` is a
constant. -/
theorem ddc_liouville [CompactSpace M] [ConnectedSpace M] (w : KahlerBackground n M)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ)) (hR : ScalarFamilyCompatible R)
    (hdd : ∀ e, ddC (R e) = 0) :
    ∃ c : ℝ, ∀ e, R e = regularDistribution b.addHaar (fun _ => c) (locallyIntegrableOn_const c) := by
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  obtain ⟨h, hsm, hreg, hcoeff⟩ :=
    GlobalSmoothScalarDistribution.exists_global_smooth_of_smooth_ddC b 0 R hR
      (fun e => by rw [hdd e, smoothFormDistribution_zero])
  have hlap : ∀ y, KahlerLaplacianChart.laplacian w.form.val h y = 0 := by
    intro y
    have h1 := SGPT.Hodge.trace_eq_add_laplacian_of_coeff w.form.val
      (γ := (0 : ClosedRealOneOneForm n M).val) (γ' := (0 : ClosedRealOneOneForm n M).val) hsm
      (fun e z hz => by rw [hcoeff e z hz, ClosedRealOneOneForm.coeff_zero, zero_add]) y
    linarith
  obtain ⟨c, hc⟩ := KahlerLaplacianStokes.exists_eq_const_of_laplacian_eq_zero w
    (fun e => (hsm e).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hlap
  refine ⟨c, fun e => ?_⟩
  obtain ⟨hL, he⟩ := hreg e
  rw [he]
  congr 1
  funext z
  exact hc _

end Liouville

/-! ### Linear algebra of scalar currents -/

section Linear

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem cast_add' {k k' : CurrentDegree n} (h : k = k') (x y : GlobalCurrent n M k) :
    (h ▸ (x + y) : GlobalCurrent n M k') = h ▸ x + h ▸ y := by
  subst h
  rfl

theorem cast_smul' {k k' : CurrentDegree n} (h : k = k') (c : ℝ) (x : GlobalCurrent n M k) :
    (h ▸ (c • x) : GlobalCurrent n M k') = c • (h ▸ x) := by
  subst h
  rfl

/-- `ddᶜ` from degree zero to degree two, as a linear map. -/
def ddcTwoLM (hn : 0 < n) : GlobalCurrent n M (scalarDegree hn) →ₗ[ℝ]
    GlobalCurrent n M (degreeTwo hn) where
  toFun := ddcTwo hn
  map_add' U V := by
    unfold ddcTwo
    rw [map_add, cast_add']
  map_smul' c U := by
    unfold ddcTwo
    rw [map_smul, cast_smul']
    rfl

theorem ddcTwoLM_apply (hn : 0 < n) (U : GlobalCurrent n M (scalarDegree hn)) :
    ddcTwoLM hn U = ddcTwo hn U := rfl

variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- The scalar coefficient in a chart, as a linear map. -/
def scalarCoeffLM (hn : 0 < n) (e : ComplexChart n M) :
    GlobalCurrent n M (scalarDegree hn) →ₗ[ℝ] 𝓓'(chartTarget e, ℝ) where
  toFun U := scalarCoeff b (finrank_sub_two_add_two hn) U e
  map_add' U V := by
    simp only [scalarCoeff_eq_coefficients, GlobalCurrent.coefficients_add]
    rfl
  map_smul' c U := by
    simp only [scalarCoeff_eq_coefficients, GlobalCurrent.coefficients_smul]
    rfl

theorem scalarCoeffLM_apply (hn : 0 < n) (e : ComplexChart n M)
    (U : GlobalCurrent n M (scalarDegree hn)) :
    scalarCoeffLM b hn e U = scalarCoeff b (finrank_sub_two_add_two hn) U e := rfl

/-- The smooth current of a closed real `(1,1)`-form, as a linear map. -/
def smoothClosedCurrentLM (hn : 0 < n) :
    ClosedRealOneOneForm n M →ₗ[ℝ] ClosedOneOneCurrent (M := M) b hn where
  toFun := smoothClosedCurrent b hn
  map_add' := smoothClosedCurrent_add b hn
  map_smul' := smoothClosedCurrent_smul b hn

end Linear

/-! ### Scalar currents of locally integrable functions -/

section Regular

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Local integrability of a function in all charts. -/
def ChartLocInt (f : M → ℝ) : Prop :=
  ∀ e : ComplexChart n M,
    LocallyIntegrableOn (fun z => f (e.val.symm z)) (chartTarget e) (canonicalBasis n).addHaar

/-- **The scalar current `[f]`** of a function `f` locally integrable in all charts. -/
def regCurrent (hn : 0 < n) (f : M → ℝ) (hf : ChartLocInt (n := n) f) :
    GlobalCurrent n M (scalarDegree hn) :=
  scalarFamilyCurrent (canonicalBasis n) (finrank_sub_two_add_two hn)
    (fun e => regularDistribution (canonicalBasis n).addHaar (fun z => f (e.val.symm z)) (hf e))
    (scalarFamilyCompatible_regular (canonicalBasis n).addHaar f hf)

theorem scalarCoeff_regCurrent (hn : 0 < n) (f : M → ℝ) (hf : ChartLocInt (n := n) f)
    (e : ComplexChart n M) :
    scalarCoeff (canonicalBasis n) (finrank_sub_two_add_two hn) (regCurrent hn f hf) e =
      regularDistribution (canonicalBasis n).addHaar (fun z => f (e.val.symm z)) (hf e) :=
  scalarCoeff_scalarFamilyCurrent _ _ _ _ e

theorem chartLocInt_of_chartSmooth {f : M → ℝ} (hf : ChartSmooth (n := n) f) :
    ChartLocInt (n := n) f :=
  fun e => chartSmooth_locallyIntegrableOn _ hf e

omit [IsComplexManifold n M] in
theorem chartLocInt_finsetSum {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ChartLocInt (n := n) (f i)) :
    ChartLocInt (n := n) (fun y => ∑ i ∈ s, f i y) := by
  classical
  intro e
  induction s using Finset.induction_on with
  | empty => simpa using locallyIntegrableOn_const (0 : ℝ)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _) e).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The current `[f]` of a chart-smooth function is `funCurrent`. -/
theorem regCurrent_eq_funCurrent (hn : 0 < n) {f : M → ℝ} (hf : ChartSmooth (n := n) f) :
    regCurrent hn f (chartLocInt_of_chartSmooth hf) = funCurrent hn f hf := by
  apply eq_of_scalarCoeff_eq (canonicalBasis n) hn
  intro e
  rw [scalarCoeff_regCurrent, scalarCoeff_funCurrent]

theorem chartLocInt_toReal (hn : 0 < n) {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) : ChartLocInt (n := n) (fun y => (u y).toReal) := by
  intro e
  exact quasiPsh_chart_locallyIntegrable (canonicalBasis n) hn u hu e

/-- `ddᶜ` of the scalar current of a global quasi-psh potential `u` is `ddᶜ u`. -/
theorem globalDDC_eq_ddcTwo (hn : 0 < n) (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u) :
    globalDDC (canonicalBasis n) hn u hu =
      ddcTwo hn (regCurrent hn (fun y => (u y).toReal) (chartLocInt_toReal hn hu)) := by
  apply LelongPoincareDivisor.globalCurrent_ext (canonicalBasis n)
  intro e
  rw [globalDDC_coefficients, coefficients_ddcTwo, scalarCoeff_regCurrent]
  rfl

end Regular


/-! ### Independence -/

section Independence

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- **A generic point of a prime divisor**: a prime divisor `E₀` meets every open set `U` it
meets outside any finite set of other prime divisors. -/
theorem exists_mem_prime_notMem (E₀ : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y)
    (G : Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) Y)) (hG : E₀ ∉ G) {U : Set Y}
    (hU : IsOpen U) (hne : (E₀.val ∩ U).Nonempty) :
    ∃ p ∈ E₀.val ∩ U, ∀ E ∈ G, p ∉ E.val := by
  classical
  induction G using Finset.induction_on generalizing U with
  | empty =>
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, by simp⟩
  | insert E G hEG ih =>
    have hE₀E : E₀ ≠ E := fun h => hG (h ▸ Finset.mem_insert_self _ _)
    have hnot : ¬ E₀.val ⊆ E.val := fun hsub => hE₀E (SGPT.Siu.eq_of_subset hsub)
    obtain ⟨x, hxE₀, hxU⟩ := hne
    have hcl := PrimePushforward.primeCarrier_subset_closure_diff E₀
      (SGPT.Siu.isComplexAnalyticSubset_primeCarrier E) hnot hxE₀
    obtain ⟨y, hyU, hyE₀, hyE⟩ := mem_closure_iff.mp hcl U hU hxU
    obtain ⟨p, ⟨hpE₀, hpU, hpE⟩, hp⟩ := ih (fun h => hG (Finset.mem_insert_of_mem h))
      (hU.inter E.isClosed.isOpen_compl) ⟨y, hyE₀, hyU, hyE⟩
    refine ⟨p, ⟨hpE₀, hpU⟩, fun E' hE' => ?_⟩
    rcases Finset.mem_insert.mp hE' with rfl | h
    · exact hpE
    · exact hp E' h

omit [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] in
theorem continuousAt_of_chartSmooth {f : Y → ℝ} (hf : ChartSmooth (n := m + 1) f) (y : Y) :
    ContinuousAt f y :=
  MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn isOpen_univ
    (fun e => by simpa only [preimage_univ, inter_univ] using hf e) (mem_univ y)

omit [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] in
/-- The weight of a metered divisor is continuous (as a real function) off its support. -/
theorem continuousAt_weight_toReal (F : MeteredEffectiveQDivisor (m + 1) Y) {y : Y}
    (hy : y ∉ F.support) : ContinuousAt (fun z => (F.weight z).toReal) y := by
  obtain ⟨G, hG, hev⟩ :=
    MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support F hy
  refine hG.congr ?_
  filter_upwards [hev] with z hz
  rw [hz, EReal.toReal_coe]

omit [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] in
theorem weight_eq_coe_toReal (F : MeteredEffectiveQDivisor (m + 1) Y) {y : Y}
    (hy : y ∉ F.support) : F.weight y = ((F.weight y).toReal : EReal) := by
  obtain ⟨G, -, hev⟩ :=
    MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support F hy
  rw [hev.self_of_nhds, EReal.toReal_coe]

theorem regularDistribution_combo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} (μ : Measure E) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) {f g : E → ℝ} {w : ι → E → ℝ} (hf : LocallyIntegrableOn f Ω μ)
    (hg : LocallyIntegrableOn g Ω μ) (hw : ∀ i, LocallyIntegrableOn (w i) Ω μ)
    (h : LocallyIntegrableOn (fun x => f x + ∑ i ∈ s, c i * w i x - g x) Ω μ) :
    regularDistribution μ (fun x => f x + ∑ i ∈ s, c i * w i x - g x) h =
      regularDistribution μ f hf + ∑ i ∈ s, c i • regularDistribution μ (w i) (hw i) -
        regularDistribution μ g hg := by
  ext φ
  simp only [regularDistribution_apply, sub_apply, add_apply, sum_apply, smul_apply, smul_eq_mul]
  have hif : Integrable (fun x => φ x * f x) μ := φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hf
  have hig : Integrable (fun x => φ x * g x) μ := φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hg
  have hiw : ∀ i, Integrable (fun x => φ x * (c i * w i x)) μ := fun i =>
    (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hw i)).const_mul (c i) |>.congr
      (Eventually.of_forall fun x => by simp only [ContinuousLinearMap.mul_apply']; ring)
  have hsum : Integrable (fun x => ∑ i ∈ s, φ x * (c i * w i x)) μ :=
    integrable_finsetSum s fun i _ => hiw i
  have e1 : (fun x => φ x * (f x + ∑ i ∈ s, c i * w i x - g x)) =
      fun x => φ x * f x + ∑ i ∈ s, φ x * (c i * w i x) - φ x * g x := by
    funext x
    rw [mul_sub, mul_add, Finset.mul_sum]
  have i1 := integral_sub (hif.add hsum) hig
  have i2 := integral_add hif hsum
  simp only [Pi.add_apply] at i1
  rw [e1, i1, i2, integral_finsetSum s fun i _ => hiw i]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

set_option maxHeartbeats 2000000 in
/-- **The core of the independence of exceptional classes**: if `∑_{E ∈ F} a_E {E} = 0` for a
finite set `F` of `π`-exceptional prime divisors of `Y`, then all `a_E` vanish. -/
theorem exceptional_coeff_eq_zero [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (F : Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) Y))
    (hF : ∀ E ∈ F, E.val ⊆ exceptionalLocus (m + 1) π)
    (a : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y → ℝ)
    (h : ∑ E ∈ F, a E • primeDivisorClass E = 0) : ∀ E ∈ F, a E = 0 := by
  classical
  -- the chosen metrics `[E] = Θ_E + ddᶜψ_E`
  let P : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y → MeteredEffectiveQDivisor (m + 1) Y :=
    fun E => Classical.choose (DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor E))
  have hPm : ∀ E, DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor E) (P E) := fun E =>
    (Classical.choose_spec (DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor E))).2
  have hsupp : ∀ E, (P E).support = E.val := fun E => PrimePushforward.support_primeDivisorMetric E
  have hψ : ∀ E, IsThetaPshPotential (P E).curvature.val (P E).weight := fun E =>
    SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ _ (hPm E)
  have hcur : ∀ E, SGPT.Siu.primeDivisorCurrent E =
      thetaPotentialCurrent (P E).curvature.val (P E).weight (hψ E) := fun E =>
    SGPT.Siu.primeDivisorCurrent_eq_thetaPotentialCurrent E (P E) (hPm E)
  have hcls : ∀ E, primeDivisorClass E = RealBottChern.ofRepresentative (P E).curvature := by
    intro E
    have h1 : (SGPT.Siu.primeDivisorBookCurrent E).val =
        thetaClosedCurrent (P E).curvature (P E).weight (hψ E) := Subtype.ext (hcur E)
    rw [primeDivisorClass, SGPT.PSH.BookCurrent.currentClass, h1, bottChernClass_thetaClosedCurrent]
  -- `Θ = ∑ a_E Θ_E` is `ddᶜ`-exact
  let Θ : ClosedRealOneOneForm (m + 1) Y := ∑ E ∈ F, a E • (P E).curvature
  have hΘ0 : RealBottChern.ofRepresentative (0 : ClosedRealOneOneForm (m + 1) Y) =
      RealBottChern.ofRepresentative Θ := by
    rw [RealBottChern.ofRepresentative_zero, ← h]
    change _ = RealBottChern.ofRepresentativeLinearMap Θ
    rw [map_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [map_smul, hcls]
    rfl
  obtain ⟨v, hv, hveq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hΘ0
  -- the scalar current `V = [v] + ∑ a_E [ψ_E]` with `ddᶜV = ∑ a_E [E]`
  let ψr : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y → Y → ℝ := fun E y => ((P E).weight y).toReal
  have hψr : ∀ E, ChartLocInt (n := m + 1) (ψr E) := fun E =>
    chartLocInt_toReal (Nat.succ_pos m) (hψ E).quasiPshPotential
  let V : GlobalCurrent (m + 1) Y (scalarDegree (Nat.succ_pos m)) :=
    regCurrent (Nat.succ_pos m) v (chartLocInt_of_chartSmooth hv) + ∑ E ∈ F, a E • regCurrent (Nat.succ_pos m) (ψr E) (hψr E)
  have hDV : ∑ E ∈ F, a E • SGPT.Siu.primeDivisorCurrent E = ddcTwo (Nat.succ_pos m) V := by
    have h1 := smoothClosedCurrent_sub_eq_ddcTwo (canonicalBasis (m + 1)) (Nat.succ_pos m) v hv (θ := 0) (θ' := Θ) hveq
    have h2 : (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) Θ).val =
        ∑ E ∈ F, a E • smoothGlobalCurrent (canonicalBasis (m + 1)) (k := degreeTwo (Nat.succ_pos m)) (P E).curvature.val := by
      change (smoothClosedCurrentLM (canonicalBasis (m + 1)) (Nat.succ_pos m) Θ).val = _
      rw [map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [map_smul, Submodule.coe_smul]
      rfl
    have h3 : (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) (0 : ClosedRealOneOneForm (m + 1) Y)).val = 0 := by
      change (smoothClosedCurrentLM (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m) 0).val = 0
      rw [map_zero]
      rfl
    replace h1 : ∑ E ∈ F, a E • smoothGlobalCurrent (canonicalBasis (m + 1)) (k := degreeTwo (Nat.succ_pos m)) (P E).curvature.val =
        ddcTwo (Nat.succ_pos m) (regCurrent (Nat.succ_pos m) v (chartLocInt_of_chartSmooth hv)) := by
      refine Eq.trans ?_ h1
      rw [h2, h3]
      exact (sub_zero (∑ E ∈ F, a E •
        smoothGlobalCurrent (canonicalBasis (m + 1)) (k := degreeTwo (Nat.succ_pos m)) (P E).curvature.val)).symm
    have h4 : ∑ E ∈ F, a E • SGPT.Siu.primeDivisorCurrent E =
        ∑ E ∈ F, a E • smoothGlobalCurrent (canonicalBasis (m + 1)) (k := degreeTwo (Nat.succ_pos m)) (P E).curvature.val +
          ∑ E ∈ F, a E • ddcTwo (Nat.succ_pos m) (regCurrent (Nat.succ_pos m) (ψr E) (hψr E)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [← smul_add, hcur E, thetaPotentialCurrent, globalDDC_eq_ddcTwo]
    refine h4.trans ((congrArg
      (· + ∑ E ∈ F, a E • ddcTwo (Nat.succ_pos m) (regCurrent (Nat.succ_pos m) (ψr E) (hψr E))) h1).trans ?_)
    change _ = ddcTwoLM (Nat.succ_pos m) (regCurrent (Nat.succ_pos m) v (chartLocInt_of_chartSmooth hv) +
      ∑ E ∈ F, a E • regCurrent (Nat.succ_pos m) (ψr E) (hψr E))
    rw [map_add, map_sum]
    simp only [map_smul, ddcTwoLM_apply]
  -- push forward: `ddᶜ π_*V = π_* ∑ a_E [E] = 0`
  have hpushD : currentPushforward hπ.1 (∑ E ∈ F, a E • SGPT.Siu.primeDivisorCurrent E) = 0 := by
    have hs : currentPushforward hπ.1 (∑ E ∈ F, a E • SGPT.Siu.primeDivisorCurrent E) =
        ∑ E ∈ F, a E • currentPushforward hπ.1 (SGPT.Siu.primeDivisorCurrent E) := by
      rw [← currentPushforwardLM_apply, map_sum]
      exact Finset.sum_congr rfl fun E _ =>
        map_smul (currentPushforwardLM (k := degreeTwo (Nat.succ_pos m)) hπ.1) (a E) _
    rw [hs]
    exact Finset.sum_eq_zero fun E hE => by
      rw [PrimePushforward.currentPushforward_primeDivisorCurrent_eq_zero hπ E (hF E hE), smul_zero]
  have hddV : ddcTwo (Nat.succ_pos m) (currentPushforward hπ.1 V) = 0 := by
    rw [← currentPushforward_ddcTwo hπ.1 (Nat.succ_pos m) V, ← hDV, hpushD]
  -- `π_*V` is the current of a smooth function `Fx` on `X`
  have hdd0 : ∀ d : ComplexChart (m + 1) X,
      ddC (scalarCoeff (canonicalBasis (m + 1)) (finrank_sub_two_add_two (Nat.succ_pos m)) (currentPushforward hπ.1 V) d) =
        smoothFormDistribution (canonicalBasis (m + 1)) (0 : ClosedRealOneOneForm (m + 1) X).val d := by
    intro d
    rw [smoothFormDistribution_zero, ← coefficients_ddcTwo (canonicalBasis (m + 1)) (Nat.succ_pos m), hddV,
      GlobalCurrent.coefficients_zero]
  obtain ⟨Fx, hFx, hreadF, -⟩ := GlobalSmoothScalarDistribution.exists_global_smooth_of_smooth_ddC (canonicalBasis (m + 1)) 0
    (scalarCoeff (canonicalBasis (m + 1)) (finrank_sub_two_add_two (Nat.succ_pos m)) (currentPushforward hπ.1 V))
    (scalarFamilyCompatible_scalarCoeff (canonicalBasis (m + 1)) (finrank_sub_two_add_two (Nat.succ_pos m)) (currentPushforward hπ.1 V))
    hdd0
  have hpushV : currentPushforward hπ.1 V = funCurrent (Nat.succ_pos m) Fx hFx := by
    apply eq_of_scalarCoeff_eq (canonicalBasis (m + 1)) (Nat.succ_pos m)
    intro d
    obtain ⟨hL, hd⟩ := hreadF d
    rw [hd, scalarCoeff_funCurrent]
  -- `W = V - [Fx ∘ π]` has zero push-forward, hence vanishes off `Exc π`
  let W := V - funCurrent (Nat.succ_pos m) (fun y => Fx (π y)) (chartSmooth_comp hπ.1 hFx)
  have hpushW : currentPushforward hπ.1 W = 0 := by
    have hsub : currentPushforward hπ.1
        (V - funCurrent (Nat.succ_pos m) (fun y => Fx (π y)) (chartSmooth_comp hπ.1 hFx)) =
        currentPushforward hπ.1 V -
          currentPushforward hπ.1 (funCurrent (Nat.succ_pos m) (fun y => Fx (π y)) (chartSmooth_comp hπ.1 hFx)) :=
      map_sub (currentPushforwardLM (k := scalarDegree (Nat.succ_pos m)) hπ.1) V _
    change currentPushforward hπ.1
      (V - funCurrent (Nat.succ_pos m) (fun y => Fx (π y)) (chartSmooth_comp hπ.1 hFx)) = 0
    rw [hsub, hpushV, currentPushforward_funCurrent_comp hπ (Nat.succ_pos m) Fx hFx]
    exact sub_self (funCurrent (Nat.succ_pos m) Fx hFx)
  have hW0 := currentEqOn_zero_of_currentPushforward_eq_zero hπ hpushW
  rw [AnalyticModificationExceptionalFibres.preimage_image_exceptionalLocus hπ] at hW0
  -- the density `S = v + ∑ a_E ψ_E - Fx ∘ π` of `W`
  let S : Y → ℝ := fun y => v y + ∑ E ∈ F, a E * ψr E y - Fx (π y)
  have hSL : ChartLocInt (n := m + 1) S := fun e =>
    ((chartLocInt_of_chartSmooth hv e).add
      (chartLocInt_finsetSum F (f := fun E y => a E * ψr E y)
        (fun E _ e' => (hψr E e').smul (a E)) e)).sub
      (chartLocInt_of_chartSmooth (chartSmooth_comp hπ.1 hFx) e)
  have hWcoeff : ∀ e, scalarCoeff (canonicalBasis (m + 1)) (finrank_sub_two_add_two (Nat.succ_pos m)) W e =
      regularDistribution (canonicalBasis (m + 1)).addHaar (fun z => S (e.val.symm z)) (hSL e) := by
    intro e
    change scalarCoeffLM (canonicalBasis (m + 1)) (Nat.succ_pos m) e (regCurrent (Nat.succ_pos m) v (chartLocInt_of_chartSmooth hv) +
      ∑ E ∈ F, a E • regCurrent (Nat.succ_pos m) (ψr E) (hψr E) -
        funCurrent (Nat.succ_pos m) (fun y => Fx (π y)) (chartSmooth_comp hπ.1 hFx)) = _
    rw [map_sub (scalarCoeffLM (canonicalBasis (m + 1)) (Nat.succ_pos m) e), map_add (scalarCoeffLM (canonicalBasis (m + 1)) (Nat.succ_pos m) e),
      map_sum (scalarCoeffLM (canonicalBasis (m + 1)) (Nat.succ_pos m) e)]
    simp only [map_smul, scalarCoeffLM_apply, scalarCoeff_regCurrent, scalarCoeff_funCurrent]
    exact (regularDistribution_combo (canonicalBasis (m + 1)).addHaar F a (chartLocInt_of_chartSmooth hv e)
      (chartLocInt_of_chartSmooth (chartSmooth_comp hπ.1 hFx) e) (fun E => hψr E e) (hSL e)).symm
  -- `S` is continuous off `Exc π`
  have hExcE : ∀ E ∈ F, ∀ y, y ∉ exceptionalLocus (m + 1) π → y ∉ (P E).support := by
    intro E hE y hy hyE
    rw [hsupp] at hyE
    exact hy (hF E hE hyE)
  have hScont : ContinuousOn S (exceptionalLocus (m + 1) π)ᶜ := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    refine ((continuousAt_of_chartSmooth hv y).add
      (MeteredDivisorWeightBounds.continuousAt_finsetSum F fun E hE =>
        continuousAt_const.mul (continuousAt_weight_toReal (P E) (hExcE E hE y hy)))).sub
      ((continuousAt_of_chartSmooth hFx (π y)).comp hπ.1.continuous.continuousAt)
  have hS0 : ∀ y ∉ exceptionalLocus (m + 1) π, S y = 0 :=
    eq_zero_of_currentEqOn_zero (Nat.succ_pos m) hSL hWcoeff
      (StrictTransformComposition.isOpen_compl_exceptionalLocus hπ.1) hScont hW0
  -- the generic point argument
  by_contra hcon
  push Not at hcon
  obtain ⟨E₀, hE₀F, ha₀⟩ := hcon
  obtain ⟨p, ⟨hpE₀, -⟩, hpG⟩ := exists_mem_prime_notMem E₀ (F.erase E₀) (Finset.notMem_erase _ _)
    isOpen_univ (by simpa using E₀.nonempty)
  let R : Y → ℝ := fun y => v y + ∑ E ∈ F.erase E₀, a E * ψr E y - Fx (π y)
  have hSR : ∀ y, S y = a E₀ * ψr E₀ y + R y := by
    intro y
    simp only [S, R]
    rw [← Finset.add_sum_erase F _ hE₀F]
    ring
  have hRcont : ContinuousAt R p := by
    refine ((continuousAt_of_chartSmooth hv p).add
      (MeteredDivisorWeightBounds.continuousAt_finsetSum _ fun E hE =>
        continuousAt_const.mul (continuousAt_weight_toReal (P E) ?_))).sub
      ((continuousAt_of_chartSmooth hFx (π p)).comp hπ.1.continuous.continuousAt)
    rw [hsupp]
    exact hpG E hE
  set K : ℝ := |R p| + 1 with hK
  have hKpos : 0 < K := by positivity
  have haabs : 0 < |a E₀| := abs_pos.mpr ha₀
  have hev1 : ∀ᶠ y in 𝓝 p, |R y| < K :=
    (continuous_abs.continuousAt.comp hRcont).eventually_lt continuousAt_const (lt_add_one _)
  have hpbot : (P E₀).weight p = ⊥ := by
    have : p ∈ (P E₀).support := by rw [hsupp]; exact hpE₀
    exact this
  have hev2 : ∀ᶠ y in 𝓝 p, (P E₀).weight y < ((-(K / |a E₀|) : ℝ) : EReal) :=
    ManifoldQuasiPlurisubharmonic.upperSemicontinuous (hψ E₀).quasiPshPotential.1 p _ (by show (P E₀).weight p < _; rw [hpbot]; exact EReal.bot_lt_coe _)
  have hdense : Dense (exceptionalLocus (m + 1) π)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (Modification4.interior_exceptionalLocus_eq_empty hπ)
  obtain ⟨y, ⟨hy1, hy2⟩, hyE⟩ := mem_closure_iff_nhds.mp (hdense.closure_eq ▸ mem_univ p) _
    (hev1.and hev2)
  have hyE₀ : y ∉ (P E₀).support := hExcE E₀ hE₀F y hyE
  have hfin := weight_eq_coe_toReal (P E₀) hyE₀
  have ht : ψr E₀ y < -(K / |a E₀|) := by
    have := hy2
    rw [hfin] at this
    exact EReal.coe_lt_coe_iff.mp this
  have heq : a E₀ * ψr E₀ y = -R y := by
    have := hS0 y hyE
    rw [hSR] at this
    linarith
  have h1 : K < |a E₀ * ψr E₀ y| := by
    rw [abs_mul]
    have hneg : ψr E₀ y < 0 := ht.trans (neg_neg_of_pos (div_pos hKpos haabs))
    rw [abs_of_neg hneg]
    have : K / |a E₀| < -ψr E₀ y := by linarith
    calc K = |a E₀| * (K / |a E₀|) := by field_simp
      _ < |a E₀| * -ψr E₀ y := mul_lt_mul_of_pos_left this haabs
  rw [heq, abs_neg] at h1
  linarith

/-- **Independence of exceptional classes** (`claude-hodge:prop-exceptional-independence`): for a
modification `π : Y → X` of compact complex manifolds, a finite set `F` of `π`-exceptional prime
divisors of `Y`, real numbers `a_E` and a class `β ∈ H^{1,1}(X, ℝ)` with
`∑_{E ∈ F} a_E {E} = π^*β`, all `a_E` vanish and `β = 0`. -/
theorem exceptional_independence [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (F : Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) Y))
    (hF : ∀ E ∈ F, E.val ⊆ exceptionalLocus (m + 1) π)
    (a : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y → ℝ) (β : RealBottChern (m + 1) X)
    (h : ∑ E ∈ F, a E • primeDivisorClass E = classPullback hπ.1 β) :
    (∀ E ∈ F, a E = 0) ∧ β = 0 := by
  have hpushE : ∀ E ∈ F, classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (primeDivisorClass E) = 0 := by
    intro E hE
    rw [primeDivisorClass, SGPT.PSH.BookCurrent.currentClass,
      ← bottChernClass_closedCurrentPushforward]
    have h0 : closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (SGPT.Siu.primeDivisorBookCurrent E).val = 0 :=
      Subtype.ext (PrimePushforward.currentPushforward_primeDivisorCurrent_eq_zero hπ E (hF E hE))
    rw [h0]
    exact (bottChernClassLinearMap (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_zero
  have hβ : β = 0 := by
    have h1 := congrArg (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)) h
    rw [classPushforward_classPullback hπ (Nat.succ_pos m), map_sum] at h1
    rw [← h1]
    exact Finset.sum_eq_zero fun E hE => by rw [map_smul, hpushE E hE, smul_zero]
  refine ⟨exceptional_coeff_eq_zero hπ F hF a ?_, hβ⟩
  rw [h, hβ, map_zero]

end Independence

end SGPT.Hodge.Exceptional
