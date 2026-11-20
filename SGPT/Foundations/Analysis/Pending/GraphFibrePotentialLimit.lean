import SGPT.Foundations.Analysis.Pending.TwoFactorStokesLevi
import SGPT.Foundations.Analysis.Pending.FibrePotentialKahlerLimit
import SGPT.Foundations.Analysis.Pending.GraphFibreIntegration

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The limit of the fibre integrals on `V × X` with a semipositive lower bound

Source: Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`), Boucksom, proof of
Theorem 4.8 and Lemma 4.10 (`bou02-volume:4.8`, `bou02-volume:4.10`), in the GRAPH form of the TN.4
plan (§1 F6 "(P) GRAPH ROUTE", step U3).

On the graph route the lower bound of the limit current `R = p₁_*(Θ ∧ p₂^*ω_X)` on a blowup `V` of
`X` is `λ μ^*ω_X`, which is only SEMIPOSITIVE (it degenerates on the exceptional set).  The limit
theorems of `SupNormalizedPotentialLimit` / `FibrePotentialKahlerLimit` conclude a `KahlerCurrent`,
whose lower bound must be Kähler; the Kähler property is used there only as packaging
(`ThetaPshChartLimitGluing.exists_kahlerCurrent_of_isChartLimit` is
`exists_isThetaPshPotential_of_isChartLimit` plus the record, and the positivity-to-Levi link
`PositivityLeviLink.isLocallyThetaPshDistribution_sub_of_leviTest` holds for every closed `σ`).  Here
the limit concludes a `(θ' - σ)`-psh POTENTIAL for an arbitrary closed real `(1,1)`-form `σ` with
`R - [V] ∧ σ ≥ 0`:

* `exists_isThetaPshPotential_of_tendsto_leviTest` — the general limit (any `σ`);
* `exists_isThetaPshPotential_of_tendsto_graph` — the graph case on `V × X`: if
  `[V × X] ∧ (p₁^*(b + ε_i ω_V) + p₂^*ω_X + ddᶜg_i)^n → Θ` along an ultrafilter with `ε_i → 0` and
  `Θ - λ [Γ_μ] ≥ 0`, then `m b - λ μ^*ω_X` has a psh potential on `V`, `m = n ∫_X ω_Xⁿ`.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.Foundations.Analysis.Pending.GraphFibrePotentialLimit

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent TopDegreeDensity
  SmoothCurrentTraceMeasure SmoothDDCForm ManifoldTubePositivity PositivityLeviLink
  FibrePushforwardProductForm DiagonalFibreIntegration ProductStokesLevi
  SupNormalizedPotentialLimit TwoFactorStokesLevi GraphFibreIntegration
open scoped ProductComplexManifold
open ProductComplexManifold

/-! ### The limit with an arbitrary closed lower bound -/

section General

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] [CompactSpace V] [MeasurableSpace V] [BorelSpace V]

/-- **The limit potential, any closed lower bound** (F6 with the Kähler packaging removed).  Let
`P_i` satisfy the Levi identity with backgrounds `θ_i` and continuous `θ_i`-psh potentials `v_i`,
all `θ_i` dominated by one closed `(1,1)`-form.  If `P_i → R` and `[V] ∧ θ_i → [V] ∧ θ'` along an
ultrafilter and `R - [V] ∧ σ` is positive for a closed real `(1,1)`-form `σ`, then `θ' - σ` has a
psh potential. -/
theorem exists_isThetaPshPotential_of_tendsto_leviTest [ConnectedSpace V] [Nonempty V]
    (w : KahlerBackground (q + 1) V) {ι : Type*} (U : Ultrafilter ι)
    (P : ι → ProductCurrent (q + 1) V q) (R : ProductCurrent (q + 1) V q)
    (hPR : ∀ η, Tendsto (fun i => P i η) (U : Filter ι) (𝓝 (R η)))
    (θ : ι → ClosedRealOneOneForm (q + 1) V) (θ' : ClosedRealOneOneForm (q + 1) V)
    (hθ : ∀ η, Tendsto (fun i => smoothCurrent (q := q) (p := 1) w ![θ i] η) (U : Filter ι)
      (𝓝 (smoothCurrent (q := q) (p := 1) w ![θ'] η)))
    (Θ : ClosedRealOneOneForm (q + 1) V) (hdom : ∀ i, (Θ - θ i).val.IsSemipositive)
    (v : ι → V → ℝ) (hv : ∀ i, Continuous (v i))
    (hpsh : ∀ i, ThetaPlurisubharmonic (θ i).val fun x => ((v i x : ℝ) : EReal))
    (hlevi : ∀ i, LeviTestIdentity w (P i) (θ i) fun e =>
      regularDistribution volume (fun z => v i (e.val.symm z))
        (locallyIntegrableOn_comp_symm (hv i) e))
    (σ : ClosedRealOneOneForm (q + 1) V)
    (hR : IsPositive (R - smoothCurrent (q := q) (p := 1) w ![σ])) :
    ∃ u : V → EReal, IsThetaPshPotential (θ' - σ).val u := by
  obtain ⟨T, hT⟩ := exists_isChartLimit_supNormalize U Θ θ v hv hpsh hdom
  have hRT : LeviTestIdentity w R θ' T :=
    LeviTestIdentity.of_isChartLimit w (fun i => supNormalize (v i))
      (fun i e => locallyIntegrableOn_comp_symm (continuous_supNormalize (hv i)) e) hPR hθ hT
      (Eventually.of_forall fun i => LeviTestIdentity.supNormalize w (hv i) (hlevi i))
  obtain ⟨u, hu, -⟩ := ThetaPshChartLimitGluing.exists_isThetaPshPotential_of_isChartLimit
    (fun i => supNormalize (v i)) T hT
    (isLocallyThetaPshDistribution_sub_of_leviTest w θ' σ hR
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) T hRT)
  exact ⟨u, hu⟩

end General

/-! ### The graph case on `V × X` -/

section Graph

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] [CompactSpace V] [MeasurableSpace V] [BorelSpace V]
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The fibre constant `m = (q + 1) ∫_X ω_X^q ∧ ω_X`. -/
def fibreConst (wX : KahlerBackground (q + 1) X) : ℝ :=
  ((q + 1 : ℕ) : ℝ) * fibreIntegral wX wX.form wX.form.val

/-- `[V] ∧ (m (b + ε ω_V)) → [V] ∧ (m b)` on test forms as `ε → 0`. -/
theorem tendsto_smoothCurrent_smul_add_smul (wV : KahlerBackground (q + 1) V) (m : ℝ)
    (b : ClosedRealOneOneForm (q + 1) V) {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (η : testSpace (q + 1) V q) :
    Tendsto (fun i => smoothCurrent (q := q) (p := 1) wV ![m • (b + ε i • wV.form)] η) l
      (𝓝 (smoothCurrent (q := q) (p := 1) wV ![m • b] η)) := by
  simp_rw [smoothCurrent_smul_apply, FibrePotentialKahlerLimit.smoothCurrent_add_apply,
    smoothCurrent_smul_apply]
  have hb : Tendsto (fun i => smoothCurrent (q := q) (p := 1) wV ![b] η +
      ε i * smoothCurrent (q := q) (p := 1) wV ![wV.form] η) l
      (𝓝 (smoothCurrent (q := q) (p := 1) wV ![b] η)) := by
    have := (tendsto_const_nhds (x := smoothCurrent (q := q) (p := 1) wV ![b] η)).add
      (hε.mul_const (smoothCurrent (q := q) (p := 1) wV ![wV.form] η))
    simpa only [zero_mul, add_zero] using this
  exact hb.const_mul m

/-- `λ [V] ∧ μ^*β = [V] ∧ (λ μ^*β)` as currents, for the graph fibre integral. -/
theorem smul_wedge_pullback_eq {μ : V → X}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ μ)
    (wV : KahlerBackground (q + 1) V) (β : ClosedRealOneOneForm (q + 1) X) (lam : ℝ) :
    lam • wedge (isTypeOneOne_pullback hμ β.2.2) (integrationCurrent wV) =
      smoothCurrent (q := q) (p := 1) wV ![lam • ClosedRealOneOneForm.pullback hμ β] := by
  ext η
  rw [smoothCurrent_smul_apply, LinearMap.smul_apply, smul_eq_mul,
    ← fibrePushforward_graphCurrent hμ wV β.2.2, fibrePushforward_graphCurrent_eq_smoothCurrent]

/-- **The graph limit** (step U3 of the uniform nef core).  Along an ultrafilter on which
`ε_i ∈ [0, 1]` tends to `0`, let `Θ_i = [V × X] ∧ (p₁^*(b + ε_i ω_V) + p₂^*ω_X + ddᶜg_i)^{q+1}`
(semipositive `α_i`) converge to `Θ` with `Θ - λ [Γ_μ]` positive.  Then the form
`m b - λ μ^*ω_X` (`m = (q + 1) ∫_X ω_X^q ∧ ω_X`) has a psh potential on `V`. -/
theorem exists_isThetaPshPotential_of_tendsto_graph [ConnectedSpace V] [Nonempty V]
    (wV : KahlerBackground (q + 1) V) (wX : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) V) {ι : Type*} (U : Ultrafilter ι) (ε : ι → ℝ)
    (hε : ∀ i, ε i ∈ Icc (0 : ℝ) 1) (hε0 : Tendsto ε (U : Filter ι) (𝓝 0))
    (g : ι → V × X → ℝ) (hg : ∀ i, ChartSmooth (n := (q + 1) + (q + 1)) (g i))
    (hα : ∀ i, ThetaPlurisubharmonic
      (prodForm (b + ε i • wV.form) wX.form + ddcClosedForm (g i) (hg i)).val (fun _ => 0))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (V × X) (q + 1)}
    (hΘ : ∀ φ, Tendsto (fun i => smoothCurrent (q := q + 1) (p := q + 1)
      (prodKahlerBackground wV wX)
      (fun _ => prodForm (b + ε i • wV.form) wX.form + ddcClosedForm (g i) (hg i)) φ)
      (U : Filter ι) (𝓝 (Θ φ)))
    {μ : V → X} (hμ : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ μ)
    {lam : ℝ} (hΘlam : IsPositive (Θ - lam • pushforward (contMDiff_graph hμ) (integrationCurrent wV))) :
    ∃ u : V → EReal, IsThetaPshPotential
      (fibreConst wX • b - lam • ClosedRealOneOneForm.pullback hμ wX.form).val u := by
  set m := fibreConst wX with hmdef
  -- domination of the backgrounds `m (b + ε_i ω_V)`
  obtain ⟨K, hK⟩ := exists_isSemipositive_smul_sub wV b |m|
  -- the positivity `R - λ [V] ∧ μ^*ω_X ≥ 0`
  have hR : IsPositive (fibrePushforward wX.form.2.2 Θ -
      smoothCurrent (q := q) (p := 1) wV ![lam • ClosedRealOneOneForm.pullback hμ wX.form]) := by
    have h := isPositive_fibrePushforward_sub_graph hμ wV wX.form.2.2
      (fun e z hz => isSemipositiveOneOne_of_isHermitian wX.isKahler.1 e hz) hΘlam
    rwa [smul_wedge_pullback_eq hμ wV wX.form lam] at h
  exact exists_isThetaPshPotential_of_tendsto_leviTest wV U
    (fun i => fibrePushforward wX.form.2.2 (smoothCurrent (q := q + 1) (p := q + 1)
      (prodKahlerBackground wV wX)
      (fun _ => prodForm (b + ε i • wV.form) wX.form + ddcClosedForm (g i) (hg i))))
    (fibrePushforward wX.form.2.2 Θ) (fun η => tendsto_fibrePushforward_apply wX.form.2.2 hΘ η)
    (fun i => m • (b + ε i • wV.form)) (m • b)
    (tendsto_smoothCurrent_smul_add_smul wV m b hε0) (K • wV.form)
    (fun i => hK m (ε i) le_rfl (hε i).1 (hε i).2)
    (fun i => fibreV wV wX (prodForm (b + ε i • wV.form) wX.form)
      (prodForm (b + ε i • wV.form) wX.form + ddcClosedForm (g i) (hg i)) (g i))
    (fun i => continuous_fibreV wV wX _ _ (ChartSmooth.continuous (hg i)))
    (fun i => thetaPlurisubharmonic_fibreV wV wX (b + ε i • wV.form) wX.form (hg i) (hα i))
    (fun i => leviTestIdentity_fibrePushforward wV wX (b + ε i • wV.form) wX.form (hg i))
    (lam • ClosedRealOneOneForm.pullback hμ wX.form) hR

end Graph

end SGPT.Foundations.Analysis.Pending.GraphFibrePotentialLimit
