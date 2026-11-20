import SGPT.PSH.GlobalL2PointMain
import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Bergman.SourceTwistedMultiplierSections
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-!
# Multiplier sections of positive-mass potentials (`lma:existsecposmass`)

Blueprint `claude-global-l2:existsecposmass`.  Source `lma:existsecposmass`
(`chapter_npp.tex` 1188--1197): *Let `L` be a holomorphic line bundle on `X` with `θ ∈ c₁(L)`.
If `φ ∈ PSH(X, θ)_{>0}`, there is `k₀ > 0` with `H⁰(X, L^k ⊗ 𝓘(kφ)) ≠ 0` for all `k ≥ k₀`.*

Formal statement (`existsecposmass`):
* `X` a compact connected complex manifold with a Kähler background `ω` (the book's standing
  assumption);
* `L` a holomorphic line bundle carrying a smooth Hermitian metric (`IsSourceSmoothHermitianMetric
  L`; every holomorphic line bundle carries one, and `H⁰(X, L^k ⊗ 𝓘(kφ))` does not depend on it);
* `θ ∈ c₁(L)`: `θ` is Bott--Chern cohomologous to the first Chern form `c₁(L, h_L)`
  (`IsOwnFirstChernForm`);
* `φ ∈ PSH(X, θ)` with positive non-pluripolar mass `∫ θ_φ^n > 0`
  (`sourcePotentialNonPluripolarMeasure θ φ hφ univ > 0`, the convention of the verified
  `lma:kahcurrentposmass`);
* conclusion: `H⁰(X, L^k ⊗ 𝓘(kφ))`, the literal sheaf-theoretic space
  `LiteralTwistedMultiplierSections L unit k φ` of the Bergman chapter (`L^k ⊗ 𝒪 ⊗ 𝓘(kφ)`), is
  nonzero for `k ≥ k₀`.

Proof (the book's, with the global `L²` input made explicit): by `lma:kahcurrentposmass` there are
`δ > 0` and `ψ ≤ φ` with `ψ ∈ PSH(X, θ - δω)`; with `θ = c₁(L, h_L) + ddᶜf`, `ψ' = ψ + f ∈
PSH(X, c₁(L, h_L) - δω)`.  The uniform point extension (`globalPointExtension`, with `T` trivial)
gives, for `k ≥ k₀`, a section `s` with `s(x) = v ≠ 0` at a point where `ψ'(x) > -∞` and
`∫ |s|² e^{-kψ'} < ∞`; since `ψ ≤ φ` and `f` is bounded, `∫ |s|² e^{-kφ} < ∞`, i.e.
`s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` (`fullHolomorphicDegreeIdealSections_iff_finite_integral`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The trivial line bundle with the standard metric has a smooth metric. -/
theorem isSourceSmoothHermitianMetric_unit :
    IsSourceSmoothHermitianMetric (unit (n := n) (M := X)) := by
  intro c e
  have he : e.val = Bundle.Trivial.trivialization X ℂ := Set.mem_singleton_iff.mp e.property.out
  refine (contDiffOn_const (c := (1 : ℝ))).congr fun z _ => ?_
  show ‖e.val.symm (c.val.symm z) 1‖ ^ 2 = 1
  rw [he]
  change ‖(Bundle.Trivial.trivialization X ℂ).symm (c.val.symm z) 1‖ ^ 2 = 1
  rw [Bundle.Trivial.trivialization_symm_apply, norm_one, one_pow]

/-- `θ ∈ PSH(X, η)` and `η = θ' + ddᶜ f` (`f` smooth) give `u + f ∈ PSH(X, θ')`. -/
theorem isThetaPshPotential_add_of_bottChernRel {θ' η : ClosedRealOneOneForm n X} {f : X → ℝ}
    (hf : ChartSmooth (n := n) f)
    (hrel : ∀ (e : ComplexChart n X) (z : ComplexModel n), z ∈ e.val.target →
      η.val.coeff e z = θ'.val.coeff e z + smoothDDC (fun y => f (e.val.symm y)) z)
    {δ : ℝ} {ωb : KahlerBackground n X} {u : X → EReal}
    (hu : IsThetaPshPotential (η - δ • ωb.form).val u) :
    IsThetaPshPotential (θ' - δ • ωb.form).val (fun x => u x + (f x : EReal)) := by
  have hneg : ChartSmooth (n := n) (fun x => -f x) := fun e => (hf e).neg
  have hrel' : ∀ (e : ComplexChart n X) (z : ComplexModel n), z ∈ e.val.target →
      (θ' - δ • ωb.form).val.coeff e z = (η - δ • ωb.form).val.coeff e z +
        smoothDDC (fun y => -f (e.val.symm y)) z := by
    intro e z hz
    rw [coeff_sub_smul, coeff_sub_smul, hrel e z hz,
      smoothDDC_neg e.val.open_target (hf e) hz]
    abel
  have h := FirstPass.GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hneg hrel' hu.1
  refine ⟨?_, fun x U hU hxU => ?_⟩
  · refine (congrArg (ThetaPlurisubharmonic _) ?_).mp h
    funext x
    rw [EReal.coe_neg, sub_eq_add_neg, neg_neg]
  · obtain ⟨y, hyU, hy⟩ := hu.2 x U hU hxU
    exact ⟨y, hyU, fun h => (EReal.add_eq_bot_iff.mp h).elim hy (EReal.coe_ne_bot _)⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- **`lma:existsecposmass`**: for `θ ∈ c₁(L)` and `φ ∈ PSH(X, θ)` of positive mass,
`H⁰(X, L^k ⊗ 𝓘(kφ)) ≠ 0` for all `k ≥ k₀`. -/
theorem existsecposmass [CompactSpace X] [ConnectedSpace X] (ωb : KahlerBackground n X)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hθL : ∃ θL : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θL ∧
      RealBottChern.ofRepresentative θL = RealBottChern.ofRepresentative (atlasClosedFormToNative θ))
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      Nontrivial (LiteralTwistedMultiplierSections L (unit (n := n) (M := X)) k φ) := by
  obtain ⟨δ, hδ, ψ, -, hstrict, hψφ⟩ := sourcePositiveMass_strictMinorant ωb hφ hpos
  have hψn : IsThetaPshPotential (atlasClosedFormToNative θ - δ • ωb.form).val ψ := by
    have := (isThetaPSH_iff_nativeThetaPotential _ ψ).mp hstrict
    rwa [sourceNativeAtlasForm_roundTrip] at this
  obtain ⟨θL, hθLown, hcls⟩ := hθL
  obtain ⟨f, hf, hrel⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hcls
  set ψ' : X → EReal := fun x => ψ x + (f x : EReal) with hψ'def
  have hψ' : IsThetaPshPotential (θL - δ • ωb.form).val ψ' :=
    isThetaPshPotential_add_of_bottChernRel hf hrel hψn
  -- the point extension with the trivial twist and the Kähler volume
  set μ : Measure X := Pending.IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ : IsSmoothPositiveVolume (n := n) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  obtain ⟨k₀, C, hC, hext⟩ := globalPointExtension (n := n) (X := X) ‹CompactSpace X› ωb μ hμ L
    unit hL isSourceSmoothHermitianMetric_unit θL hθLown δ hδ
  refine ⟨k₀ + 1, Nat.succ_pos _, fun k hk => ?_⟩
  -- a point where `ψ'` is finite
  have hne : (univ : Set X).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨x₀, -⟩ := hne
  obtain ⟨x, -, hx⟩ := hψ'.2 x₀ univ isOpen_univ (mem_univ x₀)
  -- a nonzero vector at `x`
  set e := prefFrame (twistedPower L unit k) x
  set v : (twistedPower L unit k).Fiber x := e.val.symm x 1 with hv
  have hv0 : v ≠ 0 := by
    have := frameNorm_pos (twistedPower L unit k).Fiber e.val (mem_prefFrame _ x)
    exact norm_pos_iff.mp this
  obtain ⟨s, hsx, hsint⟩ := hext k (by omega) ψ' hψ' x hx v
  -- `f` is bounded
  have hfc : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    set d := complexChartAt (n := n) y
    have hy : y ∈ d.val.source := mem_complexChartAt_source y
    have h1 : ContinuousAt (fun z => f (d.val.symm z)) (d.val y) :=
      ((hf d).continuousOn).continuousAt (d.val.open_target.mem_nhds (d.val.map_source hy))
    have h2 : ContinuousAt d.val y := d.val.continuousOn.continuousAt (d.val.open_source.mem_nhds hy)
    refine (h1.comp h2).congr ?_
    filter_upwards [d.val.open_source.mem_nhds hy] with y' hy'
    simp [d.val.left_inv hy']
  obtain ⟨Cf, hCf⟩ := isCompact_univ.exists_bound_of_continuousOn hfc.continuousOn
  -- `s` lies in `H⁰(X, L^k ⊗ 𝓘(kφ))`
  have hφn : IsThetaPshPotential (atlasClosedFormToNative θ).val φ :=
    (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hk0 : 0 < k := by omega
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hweight : ∀ y, multiplierWeight (k : ℝ) (φ y) ≤
      multiplierWeight (k : ℝ) (ψ' y) * ENNReal.ofReal (Real.exp ((k : ℝ) * Cf)) := by
    intro y
    have hfy : |f y| ≤ Cf := by have := hCf y (mem_univ y); rwa [Real.norm_eq_abs] at this
    have hψtop : ψ' y ≠ ⊤ := hψ'.1.quasiPlurisubharmonic.ne_top y
    have hle : ψ' y + ((-Cf : ℝ) : EReal) ≤ φ y := by
      calc ψ' y + ((-Cf : ℝ) : EReal) = ψ y + ((f y + -Cf : ℝ) : EReal) := by
            rw [hψ'def, EReal.coe_add, add_assoc]
        _ ≤ ψ y + 0 := add_le_add le_rfl (EReal.coe_nonpos.mpr (by linarith [le_abs_self (f y)]))
        _ = ψ y := add_zero _
        _ ≤ φ y := hψφ y
    calc multiplierWeight (k : ℝ) (φ y) ≤ multiplierWeight (k : ℝ) (ψ' y + ((-Cf : ℝ) : EReal)) :=
          multiplierWeight_antitone (Nat.cast_nonneg k) hle
      _ = _ := by rw [multiplierWeight_add_coe hk0' hψtop]; congr 3; ring
  have hfin : (∫⁻ y, originalSectionDensity (n := n) (twistedPower L unit k).Fiber φ k s y ∂μ) < ⊤ := by
    calc ∫⁻ y, originalSectionDensity (n := n) (twistedPower L unit k).Fiber φ k s y ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (ψ' y) *
            ENNReal.ofReal (Real.exp ((k : ℝ) * Cf)) ∂μ := by
          refine lintegral_mono fun y => ?_
          show ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤ _
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hweight y) zero_le
      _ = (∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (ψ' y) ∂μ) *
            ENNReal.ofReal (Real.exp ((k : ℝ) * Cf)) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (lt_of_le_of_lt hsint ?_) ENNReal.ofReal_lt_top
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
          obtain ⟨r, hr⟩ : ∃ r : ℝ, ψ' x = (r : EReal) :=
            ⟨(ψ' x).toReal, (EReal.coe_toReal (hψ'.1.quasiPlurisubharmonic.ne_top x) hx).symm⟩
          rw [hr, multiplierWeight_coe]; exact ENNReal.ofReal_lt_top
  have hmem : s ∈ fullHolomorphicIdealSections (n := n) (twistedPower L unit k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k φ) :=
    (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) (twistedPower L unit k).Fiber
      k hφn.quasiPshPotential s hμ).mpr hfin
  have hs0 : s ≠ 0 := by
    intro h
    apply hv0
    rw [← hsx, h]
    rfl
  have : Nontrivial ↥(fullHolomorphicIdealSections (n := n) (twistedPower L unit k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k φ)) :=
    ⟨⟨⟨s, hmem⟩, 0, fun h => hs0 (congrArg Subtype.val h)⟩⟩
  exact (literalTwistedMultiplierSectionEquiv L unit k φ).toEquiv.nontrivial

end SGPT.PSH.GlobalL2
