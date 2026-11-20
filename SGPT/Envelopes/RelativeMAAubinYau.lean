import SGPT.Envelopes.RelativeMAExistence
import SGPT.Envelopes.SourceRelativeEnergy
import SGPT.NPP.PluripolarCapacity
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
import SGPT.Foundations.Analysis.Pending.DominationPrinciple
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The relative Aubin–Yau equation `θ_u^n = e^{λ u} μ`

Source `thm:AY_rel` (`author/chapter_envelopes.tex`, lines 1029–1039): let `X` be a
connected compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form in a big
class, `φ` a model potential with positive mass, `λ > 0` and `μ` a non-pluripolar
measure with `μ(X) > 0`. Then there is a unique `u ∈ E(X, θ; φ)` with
`θ_u^n = e^{λ u} μ`, and every `v ∈ E(X, θ; φ)` with `θ_v^n ≥ e^{λ v} μ`
satisfies `v ≤ u`.

The book refers to Darvas–Di Nezza–Lu for the proof; we follow Xia,
*Foundations of pluripotential theory*,
`thm:nonpluripolar-relative-exponential-equation` and
`prop:relative-exponential-equation-domination`:
* existence: a maximizer of `E(v) - λ⁻¹ ∫ e^{λ v} dμ` on `E¹(X, θ; φ)`
  (`RelativeMAExistence`) solves the equation by the Euler–Lagrange equation
  (`RelativeMAEuler`);
* comparison: on `{u < v}` the comparison principle gives
  `∫ e^{λ v} dμ ≤ θ_v^n ≤ θ_u^n = ∫ e^{λ u} dμ`, hence `μ({u < v}) = 0`,
  so `θ_u^n({u < v}) = 0` and the domination principle gives `v ≤ u`;
* uniqueness follows from the comparison in both directions.

A *non-pluripolar measure* is a Radon measure (`Measure.Regular`; finite since `X` is
compact) vanishing on every pluripolar set (outer measure, i.e. the completion).
The density `e^{λ u}` is `EReal.exp (λ u)`, which vanishes on the pole set of `u`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance

theorem coe_mul_lt_coe_mul_of_pos {lam : ℝ} (hlam : 0 < lam) {a b : EReal} (hab : a < b)
    (hb : b ≠ ⊤) : (lam : EReal) * a < (lam : EReal) * b := by
  have hbbot : b ≠ ⊥ := ne_bot_of_gt hab
  have hb' : ((b.toReal : ℝ) : EReal) = b := EReal.coe_toReal hb hbbot
  rw [← hb', ← EReal.coe_mul]
  induction a using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hlam]; exact EReal.bot_lt_coe _
  | coe a =>
    rw [← EReal.coe_mul]
    rw [← hb'] at hab
    exact EReal.coe_lt_coe_iff.mpr (mul_lt_mul_of_pos_left (EReal.coe_lt_coe_iff.mp hab) hlam)
  | top => exact absurd hab (not_lt.mpr le_top)

theorem ereal_exp_mul_coe (lam r : ℝ) :
    EReal.exp ((lam : EReal) * (r : EReal)) = ENNReal.ofReal (Real.exp (lam * r)) := by
  rw [← EReal.coe_mul, EReal.exp_coe]

theorem ereal_exp_mul_eq_expWeight {X : Type*} (lam : ℝ) {u : X → EReal} {x : X} (hx : u x ≠ ⊥)
    (htop : u x ≠ ⊤) :
    EReal.exp ((lam : EReal) * u x) = ENNReal.ofReal (expWeight lam u x) := by
  rw [← EReal.coe_toReal htop hx, ereal_exp_mul_coe]
  rfl

theorem measurable_ereal_exp_mul {X : Type*} [MeasurableSpace X] (lam : ℝ) {u : X → EReal}
    (hu : Measurable u) : Measurable fun x => EReal.exp ((lam : EReal) * u x) :=
  EReal.measurable_exp.comp (measurable_const.mul hu)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

omit [ConnectedSpace M] in
/-- The maximum of a full-mass potential and a potential of the same singularity order
has full mass (copied from TN `SingularModelFullMassComparison.relativeFullMassPreceq_max`,
a module that is not part of the shared TN build). -/
theorem relativeFullMassPreceq_max' (omega : KahlerBackground n M) {u v : M → EReal}
    (hu : RelativeFullMassPreceq θ φ u hφ) (hv : RelativePSHPreceq θ φ v) :
    RelativeFullMassPreceq θ φ (fun x => max (u x) (v x)) hφ :=
  RelativePreceqStatements.relativeFullMassPreceq_of_singularity_between omega hu
    (SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hu.plurisubharmonic hv.1)
    (MoreSingularOn.of_le fun _ _ => le_max_left _ _)
    (DominationPrincipleReduction.moreSingularOn_max hu.relativePSHPreceq.2 hv.2)

omit [ConnectedSpace M] in
/-- Strict comparison principle on `{u < v}` for `u ∈ E(X, θ; φ)` and `v ⪯ φ`
(the proof of TN `SingularModelFullMassComparison.diagonalPotentialMeasure_strict_comparison`,
reproduced because that module is not part of the shared TN build). -/
theorem diagonalPotentialMeasure_strict_comparison' (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : RelativeFullMassPreceq θ φ u hφ) (hv : RelativePSHPreceq θ φ v) :
    diagonalPotentialMeasure θ v hv.1 {x | u x < v x} ≤
      diagonalPotentialMeasure θ u hu.plurisubharmonic {x | u x < v x} := by
  let S := {x | u x < v x}
  let μu := diagonalPotentialMeasure θ u hu.plurisubharmonic
  let μv := diagonalPotentialMeasure θ v hv.1
  have hm := relativeFullMassPreceq_max' omega hu hv
  have hkey := MaxMassDecomposition.measure_max_ge' omega hu.plurisubharmonic hv.1
    hm.plurisubharmonic (E := univ) MeasurableSet.univ
  rw [univ_inter, univ_inter] at hkey
  have hmass : diagonalPotentialMeasure θ (fun x => max (u x) (v x)) hm.plurisubharmonic univ =
      μu univ := (hm.mass_eq hm.plurisubharmonic).trans (hu.mass_eq hu.plurisubharmonic).symm
  rw [hmass] at hkey
  have hSm : MeasurableSet S :=
    MaxMassDecomposition.measurableSet_potential_lt hv.1 hu.plurisubharmonic
  have hcompl : {x | v x ≤ u x} = Sᶜ := by ext x; simp [S, not_lt]
  change μu {x | v x ≤ u x} + μv S ≤ μu univ at hkey
  rw [hcompl, ← measure_add_measure_compl (μ := μu) hSm, add_comm (μu Sᶜ)] at hkey
  have hfin : μu Sᶜ ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega
      (fun _ : Fin n => hu.plurisubharmonic.1) _).ne
  exact (ENNReal.add_le_add_iff_right hfin).mp hkey

omit [BorelSpace M] [ConnectedSpace M] in
theorem diagonalPotentialMeasure_congr_fun {u v : M → EReal} (huv : u = v)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) :
    diagonalPotentialMeasure θ u hu = diagonalPotentialMeasure θ v hv := by
  subst huv; rfl

/-- **Native existence** for the exponential equation: there is `u ∈ E¹(X, θ; φ)` with
`θ_u^n = e^{λ u} ν`. -/
theorem exists_relativeFiniteEnergy_exp_solution (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {ν : Measure M} [IsFiniteMeasure ν]
    (hν : DoesNotChargeManifoldPluripolar (n := n) ν) (hν0 : 0 < ν univ) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ u : M → EReal, ∃ hu : RelativeFiniteEnergyPreceq θ φ u hφ,
      diagonalPotentialMeasure θ u hu.1.plurisubharmonic =
        ν.withDensity (fun x => EReal.exp ((lam : EReal) * u x)) := by
  obtain ⟨u, hu, hmax⟩ := exists_expFunctional_max (hφ := hφ) omega hν hν0 hlam
    (inv_pos.mpr hlam)
  obtain ⟨a, hbF, hbs, -, -, -⟩ :=
    ActualSmoothVolumeVariationalFoundation.exists_normalized_translate omega hu
  set b : M → EReal := fun x => u x + (a : EReal) with hbdef
  have hb0 : ∀ x, b x ≤ 0 := fun x => hbs ▸ le_iSup b x
  have hub : u = fun x => b x + ((-a : ℝ) : EReal) := (translate_translate_neg u a).symm
  set κ' : ℝ := lam⁻¹ * Real.exp (-(lam * a)) with hκ'
  have hκ'pos : 0 < κ' := mul_pos (inv_pos.mpr hlam) (Real.exp_pos _)
  set m := modelVolume θ φ hφ
  have hshift : ∀ y, RelativeFiniteEnergyPreceq θ φ y hφ →
      expFunctional θ φ hφ ν lam lam⁻¹ (fun x => y x + ((-a : ℝ) : EReal)) =
        expFunctional θ φ hφ ν lam κ' y - a * m := by
    intro y hy
    unfold expFunctional
    rw [toReal_energy_add_const omega hy (-a),
      integral_expWeight_add_const hν hy.1.plurisubharmonic (-a)]
    rw [hκ', show lam * -a = -(lam * a) by ring]
    ring
  have hbmax : ∀ y, RelativeFiniteEnergyPreceq θ φ y hφ →
      expFunctional θ φ hφ ν lam κ' y ≤ expFunctional θ φ hφ ν lam κ' b := by
    intro y hy
    have h1 := hmax _ (RelativeFiniteEnergyPreceq.add_const omega hy (-a))
    rw [hshift y hy] at h1
    have h2 : expFunctional θ φ hφ ν lam lam⁻¹ u = expFunctional θ φ hφ ν lam κ' b - a * m := by
      conv_lhs => rw [hub]
      exact hshift b hbF
    rw [h2] at h1
    linarith
  have hEuler := diagonalPotentialMeasure_eq_of_expFunctional_max omega hn hbig hν hlam
    hκ'pos.le hbF hb0 hbmax
  refine ⟨u, hu, ?_⟩
  have hmeas : diagonalPotentialMeasure θ u hu.1.plurisubharmonic =
      diagonalPotentialMeasure θ b hbF.1.plurisubharmonic := by
    rw [diagonalPotentialMeasure_congr_fun hub hu.1.plurisubharmonic
      (hbF.1.plurisubharmonic.add_const (-a))]
    exact DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ
      hbF.1.plurisubharmonic (-a) _
  rw [hmeas, hEuler]
  apply withDensity_congr_ae
  filter_upwards [ae_ne_bot_of_doesNotCharge hν hbF.1.plurisubharmonic] with x hx
  have hux : u x ≠ ⊥ := by
    rw [hub]
    intro h
    have h' : b x = ⊥ := by
      rcases EReal.add_eq_bot_iff.mp h with h | h
      · exact h
      · exact absurd h (EReal.coe_ne_bot _)
    exact hx h'
  rw [ereal_exp_mul_eq_expWeight lam hux (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)]
  congr 1
  rw [hub, expWeight_add_const hbF.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top (-a) hx,
    hκ']
  have hexp : Real.exp (-(lam * a)) = Real.exp (lam * -a) := by ring_nf
  rw [hexp]
  field_simp

/-- **Native comparison principle** for the exponential equation. If `u, v ∈ E(X, θ; φ)`,
`θ_u^n = e^{λ u} ν` and `θ_v^n ≥ e^{λ v} ν`, then `v ≤ u`. -/
theorem le_of_exp_solution (omega : KahlerBackground n M) {ν : Measure M} {lam : ℝ}
    (hlam : 0 < lam)
    {u v : M → EReal} (hu : RelativeFullMassPreceq θ φ u hφ) (hv : RelativeFullMassPreceq θ φ v hφ)
    (hsol : diagonalPotentialMeasure θ u hu.plurisubharmonic =
      ν.withDensity (fun x => EReal.exp ((lam : EReal) * u x)))
    (hsub : ν.withDensity (fun x => EReal.exp ((lam : EReal) * v x)) ≤
      diagonalPotentialMeasure θ v hv.plurisubharmonic) :
    v ≤ u := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  have huP := hu.plurisubharmonic
  have hvP := hv.plurisubharmonic
  have humeas : Measurable u := huP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvmeas : Measurable v := hvP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  set A : Set M := {x | u x < v x} with hAdef
  have hA : MeasurableSet A := measurableSet_lt humeas hvmeas
  set eu : M → ℝ≥0∞ := fun x => EReal.exp ((lam : EReal) * u x)
  set ev : M → ℝ≥0∞ := fun x => EReal.exp ((lam : EReal) * v x)
  let : IsFiniteMeasure (diagonalPotentialMeasure θ u huP) :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ huP
  have hcomp := diagonalPotentialMeasure_strict_comparison' omega hu hv.relativePSHPreceq
  have hint : ∫⁻ x in A, ev x ∂ν ≤ ∫⁻ x in A, eu x ∂ν := by
    rw [← withDensity_apply _ hA, ← withDensity_apply _ hA]
    calc (ν.withDensity ev) A ≤ diagonalPotentialMeasure θ v hvP A := hsub A
      _ ≤ diagonalPotentialMeasure θ u huP A := hcomp
      _ = (ν.withDensity eu) A := by rw [hsol]
  have hfin : ∫⁻ x in A, eu x ∂ν ≠ ∞ := by
    rw [← withDensity_apply _ hA, ← hsol]
    exact measure_ne_top _ _
  have hlt : ∀ x ∈ A, eu x < ev x := by
    intro x hx
    exact EReal.exp_strictMono (coe_mul_lt_coe_mul_of_pos hlam hx
      (hvP.1.quasiPlurisubharmonic.ne_top x))
  have hle : eu ≤ᵐ[ν.restrict A] ev := by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact (hlt x hx).le
  have heq := ae_eq_of_ae_le_of_lintegral_le hle hfin
    (measurable_ereal_exp_mul lam hvmeas).aemeasurable hint
  have hnull : ν A = 0 := by
    have heq' := (ae_restrict_iff' hA).mp heq
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [heq'] with x hx hxA
    exact (hlt x hxA).ne (hx hxA)
  have hzero : diagonalPotentialMeasure θ u huP A = 0 := by
    rw [hsol]
    exact withDensity_absolutelyContinuous ν _ hnull
  have hupos : HasPositivePotentialMass θ u huP := by
    unfold HasPositivePotentialMass
    rw [hu.mass_eq huP]
    exact hφ.positive_mass
  have hvpos : HasPositivePotentialMass θ v hvP := by
    unfold HasPositivePotentialMass
    rw [hv.mass_eq hvP]
    exact hφ.positive_mass
  exact DominationPrinciple.le_of_diagonalPotentialMeasure_lt_eq_zero omega θ huP hvP
    hφ.plurisubharmonic hupos hvpos hu.relativePSHPreceq.2 hv.relativePSHPreceq.2
    (hu.mass_eq huP) (hv.mass_eq hvP) hzero

end SGPT.Envelopes.RelativeMA

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.RelativeMA

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Source definition (`chapter_envelopes.tex`, line 1020): a *non-pluripolar measure*
on `X` is a Radon measure giving zero (outer, i.e. completed) mass to every
pluripolar set. -/
def SourceNonPluripolarMeasure (μ : Measure M) : Prop :=
  μ.Regular ∧ ∀ S : Set M, (ofFixedModel n M).LocallyPluripolar S → μ S = 0

theorem SourceNonPluripolarMeasure.doesNotCharge {μ : Measure M}
    (hμ : SourceNonPluripolarMeasure (n := n) μ) : DoesNotChargeManifoldPluripolar (n := n) μ :=
  fun S hS => hμ.2 S (SGPT.NPP.source_locallyPluripolar_of_manifold hS)

variable [CompactSpace M]

theorem SourceNonPluripolarMeasure.isFiniteMeasure {μ : Measure M}
    (hμ : SourceNonPluripolarMeasure (n := n) μ) : IsFiniteMeasure μ := by
  have := hμ.1
  exact ⟨IsCompact.measure_lt_top isCompact_univ⟩

/-- The relative exponential equation `θ_u^n = e^{λ u} μ` for a source potential:
`u` is `θ`-psh and its non-pluripolar Monge–Ampère measure is `μ` with density
`e^{λ u}` (equal to `0` on the pole set of `u`). -/
def SourceSolvesExpEquation (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (lam : ℝ)
    (μ : Measure M) (u : M → EReal) : Prop :=
  ∃ hu : (ofFixedModel n M).IsThetaPSH θ u, sourcePotentialNonPluripolarMeasure θ u hu =
    μ.withDensity (fun x => EReal.exp ((lam : EReal) * u x))

/-- The subsolution inequality `θ_u^n ≥ e^{λ u} μ`. -/
def SourceExpSubsolution (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (lam : ℝ)
    (μ : Measure M) (u : M → EReal) : Prop :=
  ∃ hu : (ofFixedModel n M).IsThetaPSH θ u,
    μ.withDensity (fun x => EReal.exp ((lam : EReal) * u x)) ≤
      sourcePotentialNonPluripolarMeasure θ u hu

variable [BorelSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}

/-- Source `thm:AY_rel`, comparison clause: a solution in `E(X, θ; φ)` dominates every
subsolution in `E(X, θ; φ)`. (This clause holds for every measure `μ`.) -/
theorem source_relative_aubinYau_comparison (ω : KahlerBackground n M)
    (hφ : SourceModelPotential θ φ) {lam : ℝ} (hlam : 0 < lam) {μ : Measure M} {u v : M → EReal}
    (hu : SourceRelativeFullMass θ φ u hφ) (hus : SourceSolvesExpEquation θ lam μ u)
    (hv : SourceRelativeFullMass θ φ v hφ) (hvs : SourceExpSubsolution θ lam μ v) :
    v ≤ u := by
  have hu' := (sourceRelativeFullMass_iff_native θ φ u hφ).mp hu
  have hv' := (sourceRelativeFullMass_iff_native θ φ v hφ).mp hv
  obtain ⟨hu₁, hus⟩ := hus
  obtain ⟨hv₁, hvs⟩ := hvs
  exact le_of_exp_solution (hφ := hφ.toNative) ω hlam hu' hv' hus hvs

/-- Source `thm:AY_rel`, existence clause: there is `u ∈ E(X, θ; φ)` (indeed in
`E¹(X, θ; φ)`) with `θ_u^n = e^{λ u} μ`. -/
theorem source_relative_aubinYau_exists (ω : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {lam : ℝ} (hlam : 0 < lam) {μ : Measure M}
    (hμ : SourceNonPluripolarMeasure (n := n) μ) (hμ0 : 0 < μ univ) :
    ∃ u : M → EReal, SourceRelativeFiniteEnergy θ φ u hφ ∧ SourceSolvesExpEquation θ lam μ u := by
  have := hμ.isFiniteMeasure
  obtain ⟨u, hu, hsol⟩ := exists_relativeFiniteEnergy_exp_solution (hφ := hφ.toNative) ω hn hbig
    hμ.doesNotCharge hμ0 hlam
  refine ⟨u, (sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mpr hu,
    (isThetaPSH_iff_nativeThetaPotential θ u).mpr hu.1.plurisubharmonic, hsol⟩

/-- Source `thm:AY_rel` for `dim X > 0` (relative Aubin–Yau theorem). For a model potential `φ` with
positive mass in a big class, `λ > 0` and a non-pluripolar measure `μ` with `μ(X) > 0`,
there is a unique `u ∈ E(X, θ; φ)` with `θ_u^n = e^{λ u} μ`; moreover, for every solution
`u ∈ E(X, θ; φ)`, every `v ∈ E(X, θ; φ)` with `θ_v^n ≥ e^{λ v} μ` satisfies `v ≤ u`. -/
theorem source_relative_aubinYau_of_pos (ω : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {lam : ℝ} (hlam : 0 < lam) {μ : Measure M}
    (hμ : SourceNonPluripolarMeasure (n := n) μ) (hμ0 : 0 < μ univ) :
    (∃! u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesExpEquation θ lam μ u) ∧
      ∀ u v : M → EReal, SourceRelativeFullMass θ φ u hφ → SourceSolvesExpEquation θ lam μ u →
        SourceRelativeFullMass θ φ v hφ → SourceExpSubsolution θ lam μ v → v ≤ u := by
  obtain ⟨u, hu, hus⟩ := source_relative_aubinYau_exists ω hn hbig hφ hlam hμ hμ0
  have huF : SourceRelativeFullMass θ φ u hφ := hu.1
  refine ⟨⟨u, ⟨huF, hus⟩, ?_⟩, fun u v hu hus hv hvs =>
    source_relative_aubinYau_comparison ω hφ hlam hu hus hv hvs⟩
  rintro v ⟨hv, hvs⟩
  apply le_antisymm
  · exact source_relative_aubinYau_comparison ω hφ hlam huF hus hv
      ⟨hvs.1, hvs.2.symm ▸ le_rfl⟩
  · exact source_relative_aubinYau_comparison ω hφ hlam hv hvs huF
      ⟨hus.1, hus.2.symm ▸ le_rfl⟩

end SGPT.PSH.VariableComplexAtlas
