import SGPT.Envelopes.RelativeMAAubinYau
import SGPT.NPP.CapacityConvergenceGlobal
import SGPT.NPP.CapacityConvergenceMonotone
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

/-!
# Approximating the rooftop operator by Monge–Ampère equations

Source `lma:rooftop_MAequation` (`author/chapter_envelopes.tex`, lines 1538–1543): for
`φ, ψ ∈ E^∞(X, θ; ϕ)` there is `γ ∈ E^∞(X, θ; ϕ)` with
`θ_γ^n = e^{γ - φ} θ_φ^n + e^{γ - ψ} θ_ψ^n`.

We follow the book's proof. With `φ_j = max(φ, -j)`, `ψ_j = max(ψ, -j)` and
`μ_j = e^{-φ_j} θ_φ^n + e^{-ψ_j} θ_ψ^n`, the relative Aubin–Yau theorem
(`thm:AY_rel`, `RelativeMAAubinYau`) gives `γ_j ∈ E(X, θ; ϕ)` with
`θ_{γ_j}^n = e^{γ_j} μ_j`. The barrier `η = (φ + ψ)/2 - C - (n + 1)` is a subsolution,
because `θ_{(φ+ψ)/2}^n ≥ 2^{-n} θ_φ^n` and `≥ 2^{-n} θ_ψ^n` (TN
`GlobalDiagonalConvexScaling`), hence `≥ 2^{-n-1}(θ_φ^n + θ_ψ^n)` (the book uses
`2^{-n}` from multilinearity; the extra factor `2` is absorbed in the constant). The
comparison clause of `thm:AY_rel` gives `η ≤ γ_{j+1} ≤ γ_j`; the decreasing limit
`γ` lies in `E^∞(X, θ; ϕ)`, `θ_{γ_j}^n → θ_γ^n` weakly (`thm:semicon`, in the form
`SGPT.NPP.CapacityConvergence.tendsto_integral_moving`), and dominated convergence
identifies the limit of the right-hand sides.

The densities are `EReal.exp (γ x - φ x)`; on the pole set of `φ` (which `θ_φ^n` does
not charge) the value is irrelevant.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance

theorem ereal_eq_coe_toReal {a : EReal} (ha : a ≠ ⊥) (ht : a ≠ ⊤) : a = ((a.toReal : ℝ) : EReal) :=
  (EReal.coe_toReal ht ha).symm

theorem ereal_half_mul_coe (r : ℝ) : ((1 / 2 : ℝ) : EReal) * (r : EReal) = ((r / 2 : ℝ) : EReal) := by
  rw [← EReal.coe_mul]; congr 1; ring

/-- The barrier potential `(u + v)/2 - K`. -/
def rooftopBarrier {X : Type*} (u v : X → EReal) (K : ℝ) : X → EReal :=
  fun x => ThetaPshConvexCombination.convexComb (1 / 2) u v x + ((-K : ℝ) : EReal)

theorem rooftopBarrier_of_bot {X : Type*} {u v : X → EReal} {K : ℝ} {x : X} (hu : u x = ⊥)
    (hv : v x = ⊥) :
    rooftopBarrier u v K x = ⊥ := by
  simp only [rooftopBarrier, ThetaPshConvexCombination.convexComb, hu, hv,
    EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 - 1 / 2), EReal.bot_add]

theorem rooftopBarrier_of_coe {X : Type*} {u v : X → EReal} {K : ℝ} {x : X} {U V : ℝ}
    (hu : u x = U) (hv : v x = V) : rooftopBarrier u v K x = ((U / 2 + V / 2 - K : ℝ) : EReal) := by
  simp only [rooftopBarrier, ThetaPshConvexCombination.convexComb, hu, hv]
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add]
  congr 1; ring

theorem toReal_le_toReal_add_of_le_add {a b : EReal} {c : ℝ} (h : a ≤ b + (c : EReal))
    (ha : a ≠ ⊥) (hat : a ≠ ⊤) (hb : b ≠ ⊥) (hbt : b ≠ ⊤) : a.toReal ≤ b.toReal + c := by
  rw [ereal_eq_coe_toReal ha hat, ereal_eq_coe_toReal hb hbt, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.mp h

theorem max_coe_ne_bot (a : EReal) (c : ℝ) : max a (c : EReal) ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) (le_max_right _ _)

theorem max_coe_ne_top {a : EReal} (ha : a ≠ ⊤) (c : ℝ) : max a (c : EReal) ≠ ⊤ := by
  rcases le_total a (c : EReal) with h | h
  · rw [max_eq_right h]; exact EReal.coe_ne_top c
  · rw [max_eq_left h]; exact ha

/-- The truncated exponential weight `e^{-max(u, -j)}` (real form). -/
def truncWeight {X : Type*} (u : X → EReal) (j : ℕ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(max (u x) ((-(j : ℝ) : ℝ) : EReal)).toReal))

theorem truncWeight_mono {X : Type*} {u : X → EReal} (hu : ∀ x, u x ≠ ⊤) (x : X) :
    Monotone fun j => truncWeight u j x := by
  apply monotone_nat_of_le_succ
  intro j
  unfold truncWeight
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply EReal.toReal_le_toReal _ (max_coe_ne_bot _ _) (max_coe_ne_top (hu x) _)
  apply max_le_max le_rfl
  apply EReal.coe_le_coe_iff.mpr
  push_cast
  linarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal}

omit [CompactSpace M] [ConnectedSpace M] in
theorem measurable_truncWeight {u : M → EReal} (hu : IsThetaPshPotential θ.val u) (j : ℕ) :
    Measurable (truncWeight u j) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (measurable_ereal_toReal.comp
      (hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable.max measurable_const)).neg)

/-- **Native form of `lma:rooftop_MAequation`.** -/
theorem exists_rooftop_MA_solution (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hφ : IsModelPotential θ φ)
    {u v : M → EReal}
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v) :
    ∃ γ : M → EReal, ∃ hγ : RelativeEInfinity θ φ γ,
      diagonalPotentialMeasure θ γ hγ.1 =
        (diagonalPotentialMeasure θ u hu.1).withDensity (fun x => EReal.exp (γ x - u x)) +
        (diagonalPotentialMeasure θ v hv.1).withDensity (fun x => EReal.exp (γ x - v x)) := by
  classical
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  let : TopologicalSpace.PseudoMetrizableSpace M :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n M
  have huP := hu.1
  have hvP := hv.1
  have hφP := hφ.plurisubharmonic
  set μu := diagonalPotentialMeasure θ u huP with hμu
  set μv := diagonalPotentialMeasure θ v hvP with hμv
  have : IsFiniteMeasure μu :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ huP
  have : IsFiniteMeasure μv :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hvP
  have huF : RelativeFiniteEnergyPreceq θ φ u hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hu
  have hvF : RelativeFiniteEnergyPreceq θ φ v hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hv
  have hutop : ∀ x, u x ≠ ⊤ := huP.1.quasiPlurisubharmonic.ne_top
  have hvtop : ∀ x, v x ≠ ⊤ := hvP.1.quasiPlurisubharmonic.ne_top
  have hφtop : ∀ x, φ x ≠ ⊤ := hφP.1.quasiPlurisubharmonic.ne_top
  obtain ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩⟩ := hu.2
  obtain ⟨⟨b1, hb1⟩, ⟨b2, hb2⟩⟩ := hv.2
  -- pole sets coincide
  have hbot_add : ∀ c : ℝ, (⊥ : EReal) + (c : EReal) = ⊥ := fun c => EReal.bot_add _
  have hpu : ∀ x, u x = ⊥ ↔ φ x = ⊥ := by
    intro x
    constructor
    · intro h; have := ha2 x (mem_univ x); rw [h, hbot_add] at this; exact le_bot_iff.mp this
    · intro h; have := ha1 x (mem_univ x); rw [h, hbot_add] at this; exact le_bot_iff.mp this
  have hpv : ∀ x, v x = ⊥ ↔ φ x = ⊥ := by
    intro x
    constructor
    · intro h; have := hb2 x (mem_univ x); rw [h, hbot_add] at this; exact le_bot_iff.mp this
    · intro h; have := hb1 x (mem_univ x); rw [h, hbot_add] at this; exact le_bot_iff.mp this
  -- real bounds off the poles
  have hreal : ∀ x, φ x ≠ ⊥ →
      (u x).toReal ≤ (φ x).toReal + a1 ∧ (φ x).toReal ≤ (u x).toReal + a2 ∧
      (v x).toReal ≤ (φ x).toReal + b1 ∧ (φ x).toReal ≤ (v x).toReal + b2 := by
    intro x hx
    have hux : u x ≠ ⊥ := fun h => hx ((hpu x).mp h)
    have hvx : v x ≠ ⊥ := fun h => hx ((hpv x).mp h)
    exact ⟨toReal_le_toReal_add_of_le_add (ha1 x (mem_univ x)) hux (hutop x) hx (hφtop x),
      toReal_le_toReal_add_of_le_add (ha2 x (mem_univ x)) hx (hφtop x) hux (hutop x),
      toReal_le_toReal_add_of_le_add (hb1 x (mem_univ x)) hvx (hvtop x) hx (hφtop x),
      toReal_le_toReal_add_of_le_add (hb2 x (mem_univ x)) hx (hφtop x) hvx (hvtop x)⟩
  -- the barrier
  set C : ℝ := |a1| + |a2| + |b1| + |b2| with hC
  set K : ℝ := C + ((n : ℝ) + 1) with hK
  set η : M → EReal := rooftopBarrier u v K with hηdef
  have hηP : IsThetaPshPotential θ.val η :=
    (ThetaPshConvexCombination.isThetaPshPotential_convexComb huP hvP (by norm_num)
      (by norm_num)).add_const (-K)
  have hηval : ∀ x, φ x ≠ ⊥ →
      η x = (((u x).toReal / 2 + (v x).toReal / 2 - K : ℝ) : EReal) := by
    intro x hx
    exact rooftopBarrier_of_coe (ereal_eq_coe_toReal (fun h => hx ((hpu x).mp h)) (hutop x))
      (ereal_eq_coe_toReal (fun h => hx ((hpv x).mp h)) (hvtop x))
  have hηbot : ∀ x, φ x = ⊥ → η x = ⊥ := fun x hx =>
    rooftopBarrier_of_bot ((hpu x).mpr hx) ((hpv x).mpr hx)
  have hηE : RelativeEInfinity θ φ η := by
    refine ⟨hηP, ⟨(a1 + b1) / 2 - K, fun x _ => ?_⟩, ⟨K + (a2 + b2) / 2, fun x _ => ?_⟩⟩
    · by_cases hx : φ x = ⊥
      · rw [hηbot x hx]; exact bot_le
      · obtain ⟨h1, -, h3, -⟩ := hreal x hx
        rw [hηval x hx, ereal_eq_coe_toReal hx (hφtop x), ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
    · by_cases hx : φ x = ⊥
      · rw [hx]; exact bot_le
      · obtain ⟨-, h2, -, h4⟩ := hreal x hx
        rw [hηval x hx, ereal_eq_coe_toReal hx (hφtop x), ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hηF : RelativeFiniteEnergyPreceq θ φ η hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hηE
  -- the approximating measures
  set μ : ℕ → Measure M := fun j =>
    μu.withDensity (truncWeight u j) + μv.withDensity (truncWeight v j) with hμ
  have hdu := measurable_truncWeight huP
  have hdv := measurable_truncWeight hvP
  have hweight_le : ∀ (w : M → EReal) (j : ℕ) x, truncWeight w j x ≤ ENNReal.ofReal (Real.exp j) := by
    intro w j x
    unfold truncWeight
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h : ((-(j : ℝ) : ℝ) : EReal) ≤ max (w x) ((-(j : ℝ) : ℝ) : EReal) := le_max_right _ _
    rcases eq_or_ne (max (w x) ((-(j : ℝ) : ℝ) : EReal)) ⊤ with ht | ht
    · rw [ht, EReal.toReal_top]; simp
    · have := EReal.toReal_le_toReal h (EReal.coe_ne_bot _) ht
      rw [EReal.toReal_coe] at this
      linarith
  have hfinw : ∀ (ρ : Measure M) [IsFiniteMeasure ρ] (w : M → EReal) (j : ℕ),
      IsFiniteMeasure (ρ.withDensity (truncWeight w j)) := by
    intro ρ _ w j
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ x, truncWeight w j x ∂ρ ≤ ∫⁻ _x, ENNReal.ofReal (Real.exp j) ∂ρ :=
          lintegral_mono (hweight_le w j)
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hμfin : ∀ j, IsFiniteMeasure (μ j) := fun j => by
    have := hfinw μu u j; have := hfinw μv v j
    simp only [hμ]; infer_instance
  have hnc : ∀ j, DoesNotChargeManifoldPluripolar (n := n) (μ j) := by
    intro j S hS
    simp only [hμ, Measure.coe_add, Pi.add_apply]
    rw [withDensity_absolutelyContinuous _ _
      (DominationPrincipleReduction.diagonalPotentialMeasure_doesNotChargeManifoldPluripolar θ huP
        S hS),
      withDensity_absolutelyContinuous _ _
      (DominationPrincipleReduction.diagonalPotentialMeasure_doesNotChargeManifoldPluripolar θ hvP
        S hS), add_zero]
  have hmassu : 0 < μu univ := by
    rw [hμu]
    change 0 < diagonalPotentialMass θ u huP
    rw [huF.1.mass_eq huP]
    exact hφ.positive_mass
  have hμpos : ∀ j, 0 < μ j univ := by
    intro j
    simp only [hμ, Measure.coe_add, Pi.add_apply]
    refine lt_of_lt_of_le ?_ le_self_add
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hlow : ∀ x, ENNReal.ofReal (Real.exp (-(max |a1| (j : ℝ)))) ≤ truncWeight u j x := by
      intro x
      unfold truncWeight
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have hφ0 : φ x ≤ 0 := ModelRaySupremum.iSup_model_eq_zero hφ ▸ le_iSup φ x
      have hux : u x ≤ ((max |a1| (j : ℝ) : ℝ) : EReal) := by
        refine (ha1 x (mem_univ x)).trans ?_
        calc φ x + (a1 : EReal) ≤ 0 + (a1 : EReal) := add_le_add hφ0 le_rfl
          _ = (a1 : EReal) := zero_add _
          _ ≤ _ := EReal.coe_le_coe_iff.mpr ((le_abs_self a1).trans (le_max_left _ _))
      have hm : max (u x) ((-(j : ℝ) : ℝ) : EReal) ≤ ((max |a1| (j : ℝ) : ℝ) : EReal) :=
        max_le hux (EReal.coe_le_coe_iff.mpr (by
          have := le_max_right |a1| (j : ℝ)
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith))
      have := EReal.toReal_le_toReal hm (max_coe_ne_bot _ _) (EReal.coe_ne_top _)
      rwa [EReal.toReal_coe] at this
    calc (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-(max |a1| (j : ℝ)))) * μu univ :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hmassu.ne'
      _ = ∫⁻ _x, ENNReal.ofReal (Real.exp (-(max |a1| (j : ℝ)))) ∂μu := (lintegral_const _).symm
      _ ≤ ∫⁻ x, truncWeight u j x ∂μu := lintegral_mono hlow
  -- solutions of the approximate equations
  have hsolex : ∀ j, ∃ γ : M → EReal, ∃ hγ : RelativeFiniteEnergyPreceq θ φ γ hφ,
      diagonalPotentialMeasure θ γ hγ.1.plurisubharmonic =
        (μ j).withDensity (fun x => EReal.exp (((1 : ℝ) : EReal) * γ x)) := by
    intro j
    have := hμfin j
    exact exists_relativeFiniteEnergy_exp_solution omega hn hbig (hnc j) (hμpos j) one_pos
  choose γs hγsF hγsol using hsolex
  have hγsP : ∀ j, IsThetaPshPotential θ.val (γs j) := fun j => (hγsF j).1.plurisubharmonic
  have hγsm : ∀ j, Measurable (γs j) := fun j =>
    (hγsP j).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  set e : (M → EReal) → M → ℝ≥0∞ := fun w x => EReal.exp (((1 : ℝ) : EReal) * w x) with he
  have hem : ∀ w : M → EReal, Measurable w → Measurable (e w) := fun w hw =>
    measurable_ereal_exp_mul 1 hw
  have hdecomp : ∀ j (f : M → ℝ≥0∞), Measurable f → (μ j).withDensity f =
      μu.withDensity (truncWeight u j * f) + μv.withDensity (truncWeight v j * f) := by
    intro j f hf
    simp only [hμ]
    rw [withDensity_add_measure, ← withDensity_mul μu (hdu j) hf, ← withDensity_mul μv (hdv j) hf]
  -- the barrier is a subsolution
  have hηm : Measurable η := hηP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  set c : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) with hc
  have hexpK : Real.exp (C - K) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    have h1 : C - K = ((n + 1 : ℕ) : ℝ) * (-1) := by rw [hK]; push_cast; ring
    rw [h1, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    have h2 := Real.add_one_le_exp 1
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hbd : ∀ j (w : M → EReal), (∀ x, w x ≠ ⊤) → (∀ x, w x = ⊥ ↔ φ x = ⊥) →
      (∀ x, φ x ≠ ⊥ → (u x).toReal / 2 + (v x).toReal / 2 - (w x).toReal ≤ C) →
      ∀ x, φ x ≠ ⊥ → truncWeight w j x * e η x ≤ c := by
    intro j w hwtop hw hwC x hx
    have hwx : w x ≠ ⊥ := fun h => hx ((hw x).mp h)
    unfold truncWeight
    simp only [he]
    rw [hηval x hx, ← EReal.coe_mul, one_mul, EReal.exp_coe,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    have hmax : (w x).toReal ≤ (max (w x) ((-(j : ℝ) : ℝ) : EReal)).toReal :=
      EReal.toReal_le_toReal (le_max_left _ _) hwx (max_coe_ne_top (hwtop x) _)
    have h := hwC x hx
    refine le_trans (Real.exp_le_exp.mpr ?_) hexpK
    linarith
  have hbdu : ∀ j x, φ x ≠ ⊥ → truncWeight u j x * e η x ≤ c := fun j =>
    hbd j u hutop hpu (fun x hx => by
      obtain ⟨-, h2, h3, -⟩ := hreal x hx
      have : a2 + b1 ≤ 2 * C := by
        rw [hC]; linarith [le_abs_self a2, le_abs_self b1, abs_nonneg a1, abs_nonneg b2,
          abs_nonneg a2, abs_nonneg b1]
      linarith)
  have hbdv : ∀ j x, φ x ≠ ⊥ → truncWeight v j x * e η x ≤ c := fun j =>
    hbd j v hvtop hpv (fun x hx => by
      obtain ⟨h1, -, -, h4⟩ := hreal x hx
      have : a1 + b2 ≤ 2 * C := by
        rw [hC]; linarith [le_abs_self a1, le_abs_self b2, abs_nonneg a2, abs_nonneg b1,
          abs_nonneg a1, abs_nonneg b2]
      linarith)
  have hμu_ae : ∀ᵐ x ∂μu, φ x ≠ ⊥ := by
    filter_upwards [ae_ne_bot_of_doesNotCharge
      (DominationPrincipleReduction.diagonalPotentialMeasure_doesNotChargeManifoldPluripolar θ huP)
      huP] with x hx
    exact fun h => hx ((hpu x).mpr h)
  have hμv_ae : ∀ᵐ x ∂μv, φ x ≠ ⊥ := by
    filter_upwards [ae_ne_bot_of_doesNotCharge
      (DominationPrincipleReduction.diagonalPotentialMeasure_doesNotChargeManifoldPluripolar θ hvP)
      hvP] with x hx
    exact fun h => hx ((hpv x).mpr h)
  -- the barrier measure dominates `2^{-n-1}(θ_u^n + θ_v^n)`
  have hwP := ThetaPshConvexCombination.isThetaPshPotential_convexComb huP hvP
    (t := 1 / 2) (by norm_num) (by norm_num)
  have hηmeas : diagonalPotentialMeasure θ η hηP =
      diagonalPotentialMeasure θ (ThetaPshConvexCombination.convexComb (1 / 2) u v) hwP :=
    DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hwP (-K) hηP
  have hsymm : ThetaPshConvexCombination.convexComb (1 / 2) u v =
      ThetaPshConvexCombination.convexComb (1 / 2) v u := by
    rw [ConvexCombEnvelopeMass.convexComb_symm]; norm_num
  have hlowu : ∀ S, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μu S ≤ diagonalPotentialMeasure θ η hηP S := by
    intro S
    rw [hηmeas]
    exact GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le huP hvP
      (by norm_num) (by norm_num) S
  have hlowv : ∀ S, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μv S ≤ diagonalPotentialMeasure θ η hηP S := by
    intro S
    have hwP' := ThetaPshConvexCombination.isThetaPshPotential_convexComb hvP huP
      (t := 1 / 2) (by norm_num) (by norm_num)
    rw [hηmeas, diagonalPotentialMeasure_congr_fun hsymm hwP hwP']
    exact GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le hvP huP
      (by norm_num) (by norm_num) S
  have hηsub : ∀ j, (μ j).withDensity (e η) ≤ diagonalPotentialMeasure θ η hηP := by
    intro j
    rw [hdecomp j _ (hem η hηm)]
    have h1 : μu.withDensity (truncWeight u j * e η) ≤ c • μu := by
      rw [← withDensity_const]
      apply withDensity_mono
      filter_upwards [hμu_ae] with x hx
      exact hbdu j x hx
    have h2 : μv.withDensity (truncWeight v j * e η) ≤ c • μv := by
      rw [← withDensity_const]
      apply withDensity_mono
      filter_upwards [hμv_ae] with x hx
      exact hbdv j x hx
    refine (add_le_add h1 h2).trans ?_
    intro S
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hc' : c = ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [hc, ← ENNReal.ofReal_mul (by norm_num), pow_succ, mul_comm]
    rw [hc', mul_assoc, mul_assoc, ← mul_add]
    calc ENNReal.ofReal (1 / 2) * (ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μu S +
          ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * μv S)
        ≤ ENNReal.ofReal (1 / 2) * (diagonalPotentialMeasure θ η hηP S +
          diagonalPotentialMeasure θ η hηP S) := by gcongr; exacts [hlowu S, hlowv S]
      _ = diagonalPotentialMeasure θ η hηP S := by
          rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  -- comparison: `η ≤ γ_j` and `γ_{j+1} ≤ γ_j`
  have hηle : ∀ j, η ≤ γs j := fun j =>
    le_of_exp_solution omega one_pos (hγsF j).1 hηF.1 (hγsol j) (hηsub j)
  have hanti_succ : ∀ j, γs (j + 1) ≤ γs j := by
    intro j
    refine le_of_exp_solution omega one_pos (hγsF j).1 (hγsF (j + 1)).1 (hγsol j) ?_
    rw [hγsol (j + 1), hdecomp j _ (hem _ (hγsm (j + 1))),
      hdecomp (j + 1) _ (hem _ (hγsm (j + 1)))]
    refine add_le_add (withDensity_mono (Eventually.of_forall fun x => ?_))
      (withDensity_mono (Eventually.of_forall fun x => ?_))
    · exact mul_le_mul' (truncWeight_mono hutop x (Nat.le_succ j)) le_rfl
    · exact mul_le_mul' (truncWeight_mono hvtop x (Nat.le_succ j)) le_rfl
  have hanti : ∀ x, Antitone fun j => γs j x := fun x =>
    antitone_nat_of_succ_le fun j => hanti_succ j x
  -- the decreasing limit
  set γ : M → EReal := fun x => ⨅ j, γs j x with hγdef
  obtain ⟨x0, -, hx0bot, -⟩ :=
    hφP.quasiPshPotential.exists_finite (Classical.arbitrary M) isOpen_univ (mem_univ _)
  have hηγ : η ≤ γ := fun x => le_iInf fun j => hηle j x
  have hγγ0 : γ ≤ γs 0 := fun x => iInf_le (fun j => γs j x) 0
  have hγP : IsThetaPshPotential θ.val γ :=
    ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
      (ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone (fun j => (hγsP j).1) hanti)
      ⟨x0, ne_bot_of_le_ne_bot (by rw [hηval x0 hx0bot]; exact EReal.coe_ne_bot _) (hηγ x0)⟩
  obtain ⟨c0, hc0⟩ := (hγsF 0).1.relativePSHPreceq.2
  obtain ⟨-, ⟨cη, hcη⟩⟩ := hηE.2
  have hγE : RelativeEInfinity θ φ γ :=
    ⟨hγP, ⟨c0, fun x _ => (hγγ0 x).trans (hc0 x (mem_univ x))⟩,
      ⟨cη, fun x _ => (hcη x (mem_univ x)).trans (add_le_add (hηγ x) le_rfl)⟩⟩
  have hγF : RelativeFiniteEnergyPreceq θ φ γ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hγE
  refine ⟨γ, hγE, ?_⟩
  -- real values off the poles
  have hγsfin : ∀ j x, φ x ≠ ⊥ → γs j x ≠ ⊥ ∧ γs j x ≠ ⊤ := fun j x hx =>
    ⟨ne_bot_of_le_ne_bot (by rw [hηval x hx]; exact EReal.coe_ne_bot _) (hηle j x),
      (hγsP j).1.quasiPlurisubharmonic.ne_top x⟩
  have hγfin : ∀ x, φ x ≠ ⊥ → γ x ≠ ⊥ ∧ γ x ≠ ⊤ := fun x hx =>
    ⟨ne_bot_of_le_ne_bot (by rw [hηval x hx]; exact EReal.coe_ne_bot _) (hηγ x),
      hγP.1.quasiPlurisubharmonic.ne_top x⟩
  have hγsup : ∀ j x, φ x ≠ ⊥ → (γs j x).toReal ≤ (φ x).toReal + c0 := fun j x hx =>
    toReal_le_toReal_add_of_le_add (((hanti x) (Nat.zero_le j)).trans (hc0 x (mem_univ x)))
      (hγsfin j x hx).1 (hγsfin j x hx).2 hx (hφtop x)
  have hγup : ∀ x, φ x ≠ ⊥ → (γ x).toReal ≤ (φ x).toReal + c0 := fun x hx =>
    toReal_le_toReal_add_of_le_add ((hγγ0 x).trans (hc0 x (mem_univ x)))
      (hγfin x hx).1 (hγfin x hx).2 hx (hφtop x)
  -- the densities in real form
  have hdens : ∀ (w : M → EReal) (j : ℕ) (x : M), φ x ≠ ⊥ →
      (truncWeight w j x * e (γs j) x).toReal =
        Real.exp ((γs j x).toReal - (max (w x) ((-(j : ℝ) : ℝ) : EReal)).toReal) := by
    intro w j x hx
    unfold truncWeight
    simp only [he]
    rw [ereal_eq_coe_toReal (hγsfin j x hx).1 (hγsfin j x hx).2, ← EReal.coe_mul, one_mul,
      EReal.exp_coe, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, EReal.toReal_coe, ← Real.exp_add]
    ring_nf
  have hconv : ∀ (w : M → EReal), (∀ x, w x ≠ ⊤) → (∀ x, w x = ⊥ ↔ φ x = ⊥) → ∀ x, φ x ≠ ⊥ →
      Tendsto (fun j => (truncWeight w j x * e (γs j) x).toReal) atTop
        (𝓝 (Real.exp ((γ x).toReal - (w x).toReal))) := by
    intro w hwtop hw x hx
    have hwx : w x ≠ ⊥ := fun h => hx ((hw x).mp h)
    have hG : Tendsto (fun j => (γs j x).toReal) atTop (𝓝 (γ x).toReal) :=
      (EReal.tendsto_toReal (hγfin x hx).2 (hγfin x hx).1).comp (tendsto_atTop_iInf (hanti x))
    have hM : ∀ᶠ j : ℕ in atTop, (max (w x) ((-(j : ℝ) : ℝ) : EReal)).toReal = (w x).toReal := by
      obtain ⟨N, hN⟩ := exists_nat_ge (-(w x).toReal)
      filter_upwards [eventually_ge_atTop N] with j hj
      rw [max_eq_left]
      rw [ereal_eq_coe_toReal hwx (hwtop x)]
      apply EReal.coe_le_coe_iff.mpr
      have : (N : ℝ) ≤ j := Nat.cast_le.mpr hj
      linarith
    have hlim : Tendsto (fun j : ℕ => Real.exp ((γs j x).toReal -
        (max (w x) ((-(j : ℝ) : ℝ) : EReal)).toReal)) atTop
        (𝓝 (Real.exp ((γ x).toReal - (w x).toReal))) := by
      have h1 : Tendsto (fun j : ℕ => Real.exp ((γs j x).toReal - (w x).toReal)) atTop
          (𝓝 (Real.exp ((γ x).toReal - (w x).toReal))) :=
        (Real.continuous_exp.tendsto _).comp (hG.sub_const _)
      refine h1.congr' ?_
      filter_upwards [hM] with j hj
      rw [hj]
    exact hlim.congr fun j => (hdens w j x hx).symm
  have hdbound : ∀ (w : M → EReal) (a : ℝ), (∀ x, w x ≠ ⊤) → (∀ x, w x = ⊥ ↔ φ x = ⊥) →
      (∀ x, φ x ≠ ⊥ → (φ x).toReal ≤ (w x).toReal + a) → ∀ j x, φ x ≠ ⊥ →
      (truncWeight w j x * e (γs j) x).toReal ≤ Real.exp (a + c0) := by
    intro w a hwtop hw hwa j x hx
    have hwx : w x ≠ ⊥ := fun h => hx ((hw x).mp h)
    rw [hdens w j x hx]
    apply Real.exp_le_exp.mpr
    have hmax : (w x).toReal ≤ (max (w x) ((-(j : ℝ) : ℝ) : EReal)).toReal :=
      EReal.toReal_le_toReal (le_max_left _ _) hwx (max_coe_ne_top (hwtop x) _)
    have := hγsup j x hx
    have := hwa x hx
    linarith
  have hlbound : ∀ (w : M → EReal) (a : ℝ), (∀ x, φ x ≠ ⊥ → (φ x).toReal ≤ (w x).toReal + a) →
      ∀ x, φ x ≠ ⊥ → Real.exp ((γ x).toReal - (w x).toReal) ≤ Real.exp (a + c0) := by
    intro w a hwa x hx
    apply Real.exp_le_exp.mpr
    have := hγup x hx
    have := hwa x hx
    linarith
  -- weak convergence of the left-hand sides
  have hmeasEq : ∀ j, diagonalPotentialMass θ (γs j) (hγsP j) = diagonalPotentialMass θ γ hγP :=
    fun j => ((hγsF j).1.mass_eq _).trans (hγF.1.mass_eq _).symm
  have hLHS : ∀ q : M →ᵇ ℝ, Tendsto (fun j => ∫ x, q x ∂diagonalPotentialMeasure θ (γs j) (hγsP j))
      atTop (𝓝 (∫ x, q x ∂diagonalPotentialMeasure θ γ hγP)) := by
    intro q
    have hqc : CapacityWeightedConvergence.QuasiContinuousFor
        (ThetaCapacity.thetaCapacity omega.form (fun _ => 0)) (fun _ : M => (1 : ℝ)) := by
      intro eta heta
      exact ⟨∅, isOpen_empty, by simpa using heta, continuousOn_const⟩
    have hχcap : ∀ c : ℝ, 0 < c → Tendsto (fun j : ℕ => ThetaCapacity.thetaCapacity omega.form
        (fun _ => 0) {x : M | c < |(fun (_ : ℕ) (_ : M) => (1 : ℝ)) j x - (fun _ : M => (1 : ℝ)) x|})
        atTop (𝓝 0) := by
      intro c hc
      have hset : {x : M | c < |(fun (_ : ℕ) (_ : M) => (1 : ℝ)) 0 x - (fun _ : M => (1 : ℝ)) x|} = ∅ := by
        ext x
        simp only [sub_self, abs_zero, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact hc.le
      simp only [sub_self, abs_zero] at hset ⊢
      simp only [hset, ThetaCapacity.thetaCapacity_empty]
      exact tendsto_const_nhds
    have h := SGPT.NPP.CapacityConvergence.tendsto_integral_moving omega
      (θ := fun _ : Fin n => θ) (u := fun j _ => γs j) (v := fun _ => γ)
      (fun j _ => hγsP j) (fun _ => hγP)
      (fun _ a ha => SGPT.NPP.CapacityConvergence.tendsto_capacity_gap_of_antitone omega hγsP hγP
        hanti (fun x => tendsto_atTop_iInf (hanti x)) a ha)
      (tendsto_const_nhds.congr fun j => (hmeasEq j).symm)
      (C := 1) zero_le_one (χ := fun _ _ => (1 : ℝ)) (χ₀ := fun _ => (1 : ℝ))
      (fun _ _ => ⟨zero_le_one, le_rfl⟩) (fun _ => ⟨zero_le_one, le_rfl⟩)
      (fun _ => measurable_const) measurable_const hqc hχcap q.toContinuousMap
    simp only [mul_one] at h
    exact h
  -- the right-hand sides
  set ρ : Measure M := μu.withDensity (fun x => EReal.exp (γ x - u x)) +
    μv.withDensity (fun x => EReal.exp (γ x - v x)) with hρ
  have hρ' : ρ = μu.withDensity (fun x => ENNReal.ofReal (Real.exp ((γ x).toReal - (u x).toReal))) +
      μv.withDensity (fun x => ENNReal.ofReal (Real.exp ((γ x).toReal - (v x).toReal))) := by
    rw [hρ]
    congr 1
    · apply withDensity_congr_ae
      filter_upwards [hμu_ae] with x hx
      rw [ereal_eq_coe_toReal (hγfin x hx).1 (hγfin x hx).2,
        ereal_eq_coe_toReal (fun h => hx ((hpu x).mp h)) (hutop x), ← EReal.coe_sub,
        EReal.exp_coe, EReal.toReal_coe, EReal.toReal_coe]
    · apply withDensity_congr_ae
      filter_upwards [hμv_ae] with x hx
      rw [ereal_eq_coe_toReal (hγfin x hx).1 (hγfin x hx).2,
        ereal_eq_coe_toReal (fun h => hx ((hpv x).mp h)) (hvtop x), ← EReal.coe_sub,
        EReal.exp_coe, EReal.toReal_coe, EReal.toReal_coe]
  have hγm : Measurable γ := hγP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have humeas : Measurable u := huP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvmeas : Measurable v := hvP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hrm : ∀ w : M → EReal, Measurable w →
      Measurable fun x => Real.exp ((γ x).toReal - (w x).toReal) := fun w hw =>
    Real.continuous_exp.measurable.comp
      ((measurable_ereal_toReal.comp hγm).sub (measurable_ereal_toReal.comp hw))
  have hρfin : ∀ (ν : Measure M) [IsFiniteMeasure ν] (w : M → EReal) (a : ℝ),
      (∀ᵐ x ∂ν, φ x ≠ ⊥) → (∀ x, φ x ≠ ⊥ → (φ x).toReal ≤ (w x).toReal + a) →
      IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (Real.exp ((γ x).toReal - (w x).toReal))) := by
    intro ν _ w a hνae hwa
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ x, ENNReal.ofReal (Real.exp ((γ x).toReal - (w x).toReal)) ∂ν
        ≤ ∫⁻ _x, ENNReal.ofReal (Real.exp (a + c0)) ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hνae] with x hx
          exact ENNReal.ofReal_le_ofReal (hlbound w a hwa x hx)
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hreal_u : ∀ x, φ x ≠ ⊥ → (φ x).toReal ≤ (u x).toReal + a2 := fun x hx => (hreal x hx).2.1
  have hreal_v : ∀ x, φ x ≠ ⊥ → (φ x).toReal ≤ (v x).toReal + b2 := fun x hx => (hreal x hx).2.2.2
  have : IsFiniteMeasure (μu.withDensity fun x =>
      ENNReal.ofReal (Real.exp ((γ x).toReal - (u x).toReal))) := hρfin μu u a2 hμu_ae hreal_u
  have : IsFiniteMeasure (μv.withDensity fun x =>
      ENNReal.ofReal (Real.exp ((γ x).toReal - (v x).toReal))) := hρfin μv v b2 hμv_ae hreal_v
  have : IsFiniteMeasure ρ := by rw [hρ']; infer_instance
  have : IsFiniteMeasure (diagonalPotentialMeasure θ γ hγP) :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hγP
  -- integrals along the approximations
  have hsplit : ∀ (q : M →ᵇ ℝ) j, ∫ x, q x ∂diagonalPotentialMeasure θ (γs j) (hγsP j) =
      ∫ x, (truncWeight u j x * e (γs j) x).toReal * q x ∂μu +
        ∫ x, (truncWeight v j x * e (γs j) x).toReal * q x ∂μv := by
    intro q j
    have : IsFiniteMeasure (diagonalPotentialMeasure θ (γs j) (hγsP j)) :=
      DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ (hγsP j)
    have hdec := hdecomp j _ (hem _ (hγsm j))
    have hsol := hγsol j
    rw [hdec] at hsol
    have hle1 : μu.withDensity (truncWeight u j * e (γs j)) ≤
        diagonalPotentialMeasure θ (γs j) (hγsP j) := by
      rw [hsol]; exact Measure.le_add_right le_rfl
    have hle2 : μv.withDensity (truncWeight v j * e (γs j)) ≤
        diagonalPotentialMeasure θ (γs j) (hγsP j) := by
      rw [hsol]; exact Measure.le_add_left le_rfl
    have : IsFiniteMeasure (μu.withDensity (truncWeight u j * e (γs j))) := isFiniteMeasure_of_le _ hle1
    have : IsFiniteMeasure (μv.withDensity (truncWeight v j * e (γs j))) := isFiniteMeasure_of_le _ hle2
    have hfin1 : ∀ᵐ x ∂μu, (truncWeight u j * e (γs j)) x < ⊤ := by
      filter_upwards [hμu_ae] with x hx
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        simp only [he]
        rw [ereal_eq_coe_toReal (hγsfin j x hx).1 (hγsfin j x hx).2, ← EReal.coe_mul, EReal.exp_coe]
        exact ENNReal.ofReal_lt_top)
    have hfin2 : ∀ᵐ x ∂μv, (truncWeight v j * e (γs j)) x < ⊤ := by
      filter_upwards [hμv_ae] with x hx
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        simp only [he]
        rw [ereal_eq_coe_toReal (hγsfin j x hx).1 (hγsfin j x hx).2, ← EReal.coe_mul, EReal.exp_coe]
        exact ENNReal.ofReal_lt_top)
    rw [hsol, integral_add_measure (q.integrable _) (q.integrable _),
      integral_withDensity_eq_integral_toReal_smul ((hdu j).mul (hem _ (hγsm j))) hfin1,
      integral_withDensity_eq_integral_toReal_smul ((hdv j).mul (hem _ (hγsm j))) hfin2]
    simp only [smul_eq_mul, Pi.mul_apply]
  have hRHS : ∀ q : M →ᵇ ℝ, Tendsto (fun j => ∫ x, q x ∂diagonalPotentialMeasure θ (γs j) (hγsP j))
      atTop (𝓝 (∫ x, q x ∂ρ)) := by
    intro q
    obtain ⟨Bq, hBq⟩ := (isCompact_range q.continuous.abs).bddAbove
    have hqB : ∀ x, ‖q x‖ ≤ Bq := fun x => by rw [Real.norm_eq_abs]; exact hBq ⟨x, rfl⟩
    have hconvu : Tendsto (fun j => ∫ x, (truncWeight u j x * e (γs j) x).toReal * q x ∂μu) atTop
        (𝓝 (∫ x, Real.exp ((γ x).toReal - (u x).toReal) * q x ∂μu)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (a2 + c0) * Bq) ?_
        (integrable_const _) ?_ ?_
      · intro j
        exact ((ENNReal.measurable_toReal.comp ((hdu j).mul (hem _ (hγsm j)))).mul
          q.continuous.measurable).aestronglyMeasurable
      · intro j
        filter_upwards [hμu_ae] with x hx
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul (hdbound u a2 hutop hpu hreal_u j x hx) (hqB x) (norm_nonneg _)
          (Real.exp_pos _).le
      · filter_upwards [hμu_ae] with x hx
        exact (hconv u hutop hpu x hx).mul_const _
    have hconvv : Tendsto (fun j => ∫ x, (truncWeight v j x * e (γs j) x).toReal * q x ∂μv) atTop
        (𝓝 (∫ x, Real.exp ((γ x).toReal - (v x).toReal) * q x ∂μv)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (b2 + c0) * Bq) ?_
        (integrable_const _) ?_ ?_
      · intro j
        exact ((ENNReal.measurable_toReal.comp ((hdv j).mul (hem _ (hγsm j)))).mul
          q.continuous.measurable).aestronglyMeasurable
      · intro j
        filter_upwards [hμv_ae] with x hx
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul (hdbound v b2 hvtop hpv hreal_v j x hx) (hqB x) (norm_nonneg _)
          (Real.exp_pos _).le
      · filter_upwards [hμv_ae] with x hx
        exact (hconv v hvtop hpv x hx).mul_const _
    have hlim := hconvu.add hconvv
    have hρint : ∫ x, q x ∂ρ = ∫ x, Real.exp ((γ x).toReal - (u x).toReal) * q x ∂μu +
        ∫ x, Real.exp ((γ x).toReal - (v x).toReal) * q x ∂μv := by
      rw [hρ', integral_add_measure (q.integrable _) (q.integrable _),
        integral_withDensity_eq_integral_toReal_smul (hrm u humeas).ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
        integral_withDensity_eq_integral_toReal_smul (hrm v hvmeas).ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [hρint]
    exact hlim.congr fun j => (hsplit q j).symm
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro q
  exact tendsto_nhds_unique (hLHS q) (hRHS q)

end SGPT.Envelopes.RelativeMA

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.RelativeMA

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}

/-- Source `lma:rooftop_MAequation` for `dim X > 0`. For a model potential `φ` with positive mass in a
big class and `u, v ∈ E^∞(X, θ; φ)` there is `γ ∈ E^∞(X, θ; φ)` with
`θ_γ^n = e^{γ - u} θ_u^n + e^{γ - v} θ_v^n`. -/
theorem source_rooftop_MAequation_of_pos (ω : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {u v : M → EReal}
    (hu : SourceRelativeEInfinity θ φ u) (hv : SourceRelativeEInfinity θ φ v) :
    ∃ γ : M → EReal, ∃ hγ : SourceRelativeEInfinity θ φ γ,
      sourcePotentialNonPluripolarMeasure θ γ hγ.1 =
        (sourcePotentialNonPluripolarMeasure θ u hu.1).withDensity
            (fun x => EReal.exp (γ x - u x)) +
          (sourcePotentialNonPluripolarMeasure θ v hv.1).withDensity
            (fun x => EReal.exp (γ x - v x)) := by
  obtain ⟨γ, hγ, hmeas⟩ := exists_rooftop_MA_solution ω hn hbig hφ.toNative
    ((sourceRelativeEInfinity_iff_native θ φ u).mp hu)
    ((sourceRelativeEInfinity_iff_native θ φ v).mp hv)
  exact ⟨γ, (sourceRelativeEInfinity_iff_native θ φ γ).mpr hγ, hmeas⟩

end SGPT.PSH.VariableComplexAtlas
