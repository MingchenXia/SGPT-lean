import SGPT.Bergman.Quant2SmoothWeakConv
import SGPT.Bergman.SourcePartialDonaldsonDerivative
import SGPT.Bergman.SourcePartialEnergyDifferentiability
import SGPT.Bergman.SourceGlobalWeightSmoothApproximation

/-!
# Energy quantization for smooth volume forms

Source `prop:quant_I_smooth` (`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`,
lines 953--1010) and
`cor:Ninfdifflim` (lines 1034--1042).

For `w ∈ C⁰(X)` let `N^k_{w,ωⁿ}` be the weighted `L²` norm on `H⁰(X, L^k ⊗ T ⊗ I(kφ))` with respect
to the probability measure `ωⁿ`, `L_{k,φ}` the partial Donaldson functional and
`E^φ_{θ,X}(w)` the partial equilibrium energy. For `φ` with analytic singularities and `θ_φ` a
Kähler current the book proves `L_{k,φ}(N^k_{w,ωⁿ}) - L_{k,φ}(N^k_{w',ωⁿ}) → E^φ_{θ,X}(w) -
E^φ_{θ,X}(w')`.

This file contains the finite-degree ingredients of the proof, all unconditional:

* `hasDerivAt_donaldsonL2`: `d/dt L_{k,φ}(N^k_{w+tu,ωⁿ}) = ∫_X u dβ^k_{w+tu,φ,ωⁿ}`;
* `donaldsonL2_sub_eq_integral`: the fundamental theorem of calculus for this derivative;
* `energyX_sub_eq_integral`: the same for the energy (`prop:differential_P`);
* `abs_donaldsonL2_sub_le`, `abs_energyX_sub_le`: Lipschitz bounds in the weight.

The asymptotic statements are proved in `Quant2EnergyLimit` under `RiemannRochLowerBound`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant2

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport SGPT.Bergman.NormAxioms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.PartialDonaldson SGPT.Bergman.QuantizationFrontier
open SGPT.Bergman.RelativeEnvelopeCases
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

/-! ### A calculus lemma -/

/-- Fundamental theorem of calculus on `[0,1]` for a function with a bounded derivative
everywhere. -/
theorem sub_eq_intervalIntegral_of_hasDerivAt {F d : ℝ → ℝ} {C : ℝ}
    (hF : ∀ t, HasDerivAt F (d t) t) (hd : ∀ t, |d t| ≤ C) :
    IntervalIntegrable d MeasureTheory.volume 0 1 ∧ F 1 - F 0 = ∫ t in (0:ℝ)..1, d t := by
  have hdd : d = deriv F := funext fun t => (hF t).deriv.symm
  have hmeas : Measurable d := by rw [hdd]; exact measurable_deriv F
  have hint : IntervalIntegrable d MeasureTheory.volume 0 1 :=
    (intervalIntegrable_const (c := C)).mono_fun hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        simp only [Real.norm_eq_abs]
        exact (hd t).trans (le_abs_self C))
  exact ⟨hint, (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hint).symm⟩

/-- A uniform bound for the integral of a continuous function against a finite measure. -/
theorem abs_integral_le_norm_mul {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [CompactSpace Y] (μ : Measure Y) [IsFiniteMeasure μ] (u : C(Y, ℝ)) :
    |∫ x, u x ∂μ| ≤ ‖u‖ * μ.real univ := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x =>
    ContinuousMap.norm_coe_le_norm u x)

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-! ### The data on `K = X` with the volume form `ωⁿ` -/

/-- The probability measure `ωⁿ`, seen on the subtype `X = univ`. -/
abbrev volX (omega : KahlerBackground n X) : Measure (univ : Set X) :=
  (kahlerVolume omega).comap (Subtype.val : ↥(univ : Set X) → X)

/-- `ωⁿ ∈ BM(X,w)` for every continuous `w` (`[BBWN11]`, proved in `SourceVolumeBernsteinMarkov`). -/
theorem volX_BM (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (w : C(X, ℝ)) :
    IsBernsteinMarkov L T (wholeWeightedSubset w) (volX omega) := by
  let : IsProbabilityMeasure (kahlerVolume omega) := ⟨hvol⟩
  exact smoothPositiveProbabilityVolume_general_BM L T w (kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)

/-- `L_{k,φ}(N^k_{w,ωⁿ})` for `k ≥ 1` (the value `0` at `k = 0` is irrelevant). -/
def donaldsonL2 (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (w : C(X, ℝ)) (k : ℕ) : ℝ :=
  if hk : 0 < k then
    partialDonaldsonFunctional L T omega hvol k hk φ
      (l2Norm L T (wholeWeightedSubset w) (volX omega) (volX_BM omega hvol L T w) k hk φ)
  else 0

/-- The partial Bergman measure `β^k_{w,φ,ωⁿ}` on `X`. -/
abbrev bergmanX (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle n X)
    (φ : X → EReal) (w : C(X, ℝ)) (k : ℕ) : Measure X :=
  sourcePartialBergmanMeasure L T (wholeWeightedSubset w) (volX omega) k φ

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
/-- `univ` is non-pluripolar. -/
theorem nonPluripolar_univ : (ofFixedModel n X).NonPluripolar (univ : Set X) :=
  (wholeWeightedSubset (n := n) (0 : C(X, ℝ))).nonPluripolar_carrier

/-- The partial equilibrium energy `E^φ_{θ,X}(w)` of a continuous weight on `K = X`. -/
def energyX (omega : KahlerBackground n X) {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) (w : C(X, ℝ)) : ℝ :=
  partialEquilibriumEnergy omega hφ hφpos isClosed_univ (nonPluripolar_univ (n := n))
    (wholeWeightedSubset (n := n) w).weight

/-! ### Total masses -/

theorem bergmanX_mass (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (w : C(X, ℝ)) (k : ℕ)
    (hk : 0 < k) : bergmanX omega L T φ w k univ = normalizedH0 L T φ k := by
  rw [sourcePartialBergmanMeasure_mass L T _ _ (volX_BM omega hvol L T w) k hk φ, normalizedH0,
    sourceBergmanNormalization, ENNReal.ofReal_mul (by positivity)]

theorem bergmanX_isFinite (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (w : C(X, ℝ)) (k : ℕ)
    (hk : 0 < k) : IsFiniteMeasure (bergmanX omega L T φ w k) :=
  ⟨by rw [bergmanX_mass omega hvol L T φ w k hk]; exact ENNReal.ofReal_lt_top⟩

theorem bergmanX_real_mass (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (w : C(X, ℝ)) (k : ℕ)
    (hk : 0 < k) : (bergmanX omega L T φ w k).real univ = (normalizedH0 L T φ k).toReal := by
  rw [measureReal_def, bergmanX_mass omega hvol L T φ w k hk]

/-! ### Derivative of `t ↦ L_{k,φ}(N^k_{w+tu,ωⁿ})` -/

/-- Two complex norms with the same values are equal. -/
theorem complexNorm_ext {E : Type*} [AddCommGroup E] [Module ℂ E] {N M : ComplexNorm E}
    (h : ∀ x, N.toAddGroupNorm x = M.toAddGroupNorm x) : N = M := by
  rcases N with ⟨N, hN⟩
  rcases M with ⟨M, hM⟩
  have hNM : N = M := AddGroupNorm.ext h
  subst hNM
  rfl

/-- The perturbed norm `N^k_{w+r u,ωⁿ}` of the Gram-variation API is the `L²` norm of the weight
`w + r u`. -/
theorem perturbed_eq_l2Norm (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) (hk : 0 < k)
    (w u : C(X, ℝ)) (r : ℝ) :
    sourcePerturbedPartialL2Norm L T (wholeWeightedSubset w) (volX omega)
        (volX_BM omega hvol L T w) k hk φ (sourceBergmanTestRestriction (wholeWeightedSubset w) u) r =
      l2Norm L T (wholeWeightedSubset (w + r • u)) (volX omega)
        (volX_BM omega hvol L T (w + r • u)) k hk φ := by
  apply complexNorm_ext
  intro s
  apply (ENNReal.ofReal_eq_ofReal_iff (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [sourcePerturbedPartialL2Norm_ofReal, l2Norm_ofReal]
  congr 2

theorem donaldsonL2_pos (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (w : C(X, ℝ)) (k : ℕ)
    (hk : 0 < k) :
    donaldsonL2 omega hvol L T φ w k = partialDonaldsonFunctional L T omega hvol k hk φ
      (l2Norm L T (wholeWeightedSubset w) (volX omega) (volX_BM omega hvol L T w) k hk φ) := by
  rw [donaldsonL2, dif_pos hk]

/-- `d/dt L_{k,φ}(N^k_{w+tu,ωⁿ}) = ∫_X u dβ^k_{w+tu,φ,ωⁿ}` (differentiation of the Gram matrix,
as in the proof of `prop:quant_I_smooth`). -/
theorem hasDerivAt_donaldsonL2 (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) (hk : 0 < k)
    (w u : C(X, ℝ)) (t : ℝ) :
    HasDerivAt (fun s => donaldsonL2 omega hvol L T φ (w + s • u) k)
      (∫ x, u x ∂bergmanX omega L T φ (w + t • u) k) t := by
  have h := hasDerivAt_sourcePartialDonaldson_eq_global_Bergman L T (wholeWeightedSubset (w + t • u))
    (volX omega) (volX_BM omega hvol L T (w + t • u)) k hk φ omega hvol u
  have heq : (fun s => donaldsonL2 omega hvol L T φ (w + s • u) k) =
      fun s => (fun r => partialDonaldsonFunctional L T omega hvol k hk φ
        (sourcePerturbedPartialL2Norm L T (wholeWeightedSubset (w + t • u)) (volX omega)
          (volX_BM omega hvol L T (w + t • u)) k hk φ
          (sourceBergmanTestRestriction (wholeWeightedSubset (w + t • u)) u) r)) (s - t) := by
    funext s
    simp only
    rw [perturbed_eq_l2Norm omega hvol L T φ k hk, donaldsonL2_pos omega hvol L T φ _ k hk]
    have hw : w + s • u = w + t • u + (s - t) • u := by
      ext x; simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]; ring
    rw [hw]
  rw [heq]
  exact HasDerivAt.comp_sub_const t t (by simpa only [sub_self] using h)

/-- `|∫ u dβ^k_{w,φ,ωⁿ}| ≤ ‖u‖ · n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ))`. -/
theorem abs_integral_bergmanX_le (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (w u : C(X, ℝ)) (k : ℕ)
    (hk : 0 < k) :
    |∫ x, u x ∂bergmanX omega L T φ w k| ≤ ‖u‖ * (normalizedH0 L T φ k).toReal := by
  let := bergmanX_isFinite omega hvol L T φ w k hk
  rw [← bergmanX_real_mass omega hvol L T φ w k hk]
  exact abs_integral_le_norm_mul _ u

/-- The fundamental theorem of calculus in the proof of `prop:quant_I_smooth`:
`L_{k,φ}(N^k_{w'+u,ωⁿ}) - L_{k,φ}(N^k_{w',ωⁿ}) = ∫₀¹ ∫_X u dβ^k_{w'+tu,φ,ωⁿ} dt`. -/
theorem donaldsonL2_sub_eq_integral (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) (hk : 0 < k)
    (w u : C(X, ℝ)) :
    IntervalIntegrable (fun t => ∫ x, u x ∂bergmanX omega L T φ (w + t • u) k)
      MeasureTheory.volume 0 1 ∧
    donaldsonL2 omega hvol L T φ (w + u) k - donaldsonL2 omega hvol L T φ w k =
      ∫ t in (0:ℝ)..1, ∫ x, u x ∂bergmanX omega L T φ (w + t • u) k := by
  have h := sub_eq_intervalIntegral_of_hasDerivAt
    (F := fun s => donaldsonL2 omega hvol L T φ (w + s • u) k)
    (hasDerivAt_donaldsonL2 omega hvol L T φ k hk w u)
    (fun t => abs_integral_bergmanX_le omega hvol L T φ (w + t • u) u k hk)
  simpa only [one_smul, zero_smul, add_zero] using h

/-! ### Derivative of the energy -/

omit [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Integrals over the subtype `univ` with the comap measure are integrals over `X`. -/
theorem integral_univ_comap {μ : Measure X} (u : C(X, ℝ)) :
    ∫ x : (univ : Set X), u x ∂(μ.comap Subtype.val) = ∫ x, u x ∂μ := by
  rw [integral_subtype_comap MeasurableSet.univ (fun x => u x), Measure.restrict_univ]

/-- `d/dt E^φ_{θ,X}(w+tu) = ∫_X u dθⁿ_{P_{θ,X}[φ]_I(w+tu)}` (`prop:differential_P` on `K = X`). -/
theorem hasDerivAt_energyX (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) (w u : C(X, ℝ)) (t : ℝ) :
    ∃ hPI : (ofFixedModel n X).IsThetaPSH θ
        (partialIEnvelope θ φ univ (fun y : (univ : Set X) => ((w + t • u) y.val : EReal))),
      HasDerivAt (fun s : ℝ => energyX omega hφ hφpos (w + s • u))
        (∫ x, u x ∂sourcePotentialNonPluripolarMeasure θ
          (partialIEnvelope θ φ univ (fun y : (univ : Set X) => ((w + t • u) y.val : EReal))) hPI) t := by
  let v : C((univ : Set X), ℝ) := (wholeWeightedSubset (n := n) w).weight
  let f : C((univ : Set X), ℝ) := (wholeWeightedSubset (n := n) u).weight
  have h := partialEquilibriumEnergy_hasDerivAt omega hφ hφpos isClosed_univ (nonPluripolar_univ (n := n)) v f t
  have hweight (s : ℝ) : (wholeWeightedSubset (n := n) (w + s • u)).weight = v + s • f := by
    ext x; rfl
  refine ⟨(partialIEnvelope_eInfinity_continuous omega hφ hφpos isClosed_univ (nonPluripolar_univ (n := n))
    (v + t • f)).1, ?_⟩
  have heq : (fun s : ℝ => energyX omega hφ hφpos (w + s • u)) =
      fun s => partialEquilibriumEnergy omega hφ hφpos isClosed_univ (nonPluripolar_univ (n := n)) (v + s • f) := by
    funext s
    rw [energyX, hweight]
  rw [heq]
  convert h using 1
  exact (integral_univ_comap u).symm

/-- The energy derivative is bounded by `‖u‖ · vol(θ_φ)`. -/
theorem abs_energy_derivative_le (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) (w u : C(X, ℝ))
    (hPI : (ofFixedModel n X).IsThetaPSH θ
        (partialIEnvelope θ φ univ (fun y : (univ : Set X) => (w y.val : EReal)))) :
    |∫ x, u x ∂sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ φ univ (fun y : (univ : Set X) => (w y.val : EReal))) hPI| ≤
      ‖u‖ * (sourceIVolume θ φ hφ).toReal := by
  let := sourcePotentialMeasure_finite omega hPI
  have hmass := partialIEnvelope_mass_eq_sourceIVolume omega hφ hφpos isClosed_univ
    nonPluripolar_univ (wholeWeightedSubset (n := n) w).weight hPI
  calc _ ≤ ‖u‖ * (sourcePotentialNonPluripolarMeasure θ
        (partialIEnvelope θ φ univ (fun y : (univ : Set X) => (w y.val : EReal))) hPI).real univ :=
        abs_integral_le_norm_mul _ u
    _ = _ := by rw [measureReal_def, ← hmass]; rfl

/-- The fundamental theorem of calculus for the energy (`prop:differential_P`):
`E^φ_{θ,X}(w+u) - E^φ_{θ,X}(w) = ∫₀¹ ∫_X u dθⁿ_{P_{θ,X}[φ]_I(w+tu)} dt`; the integrand is
written as `deriv` of `t ↦ E^φ_{θ,X}(w+tu)`, identified by `hasDerivAt_energyX`. -/
theorem energyX_sub_eq_integral (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) (w u : C(X, ℝ)) :
    IntervalIntegrable (deriv fun s : ℝ => energyX omega hφ hφpos (w + s • u)) MeasureTheory.volume 0 1 ∧
    energyX omega hφ hφpos (w + u) - energyX omega hφ hφpos w =
      ∫ t in (0:ℝ)..1, deriv (fun s : ℝ => energyX omega hφ hφpos (w + s • u)) t := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => energyX omega hφ hφpos (w + s • u))
      (deriv (fun s : ℝ => energyX omega hφ hφpos (w + s • u)) t) t := by
    obtain ⟨_, h⟩ := hasDerivAt_energyX omega hφ hφpos w u t
    exact h.differentiableAt.hasDerivAt
  have hb (t : ℝ) : |deriv (fun s : ℝ => energyX omega hφ hφpos (w + s • u)) t| ≤
      ‖u‖ * (sourceIVolume θ φ hφ).toReal := by
    obtain ⟨hPI, h⟩ := hasDerivAt_energyX omega hφ hφpos w u t
    rw [h.deriv]
    exact abs_energy_derivative_le omega hφ hφpos (w + t • u) u hPI
  have h := sub_eq_intervalIntegral_of_hasDerivAt hd hb
  simpa only [one_smul, zero_smul, add_zero] using h

/-! ### Lipschitz bounds in the weight and normalizations -/

/-- `|L_{k,φ}(N^k_{w+u,ωⁿ}) - L_{k,φ}(N^k_{w,ωⁿ})| ≤ n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ)) · ‖u‖`
(the estimate used for continuous weights in the proof of `prop:quant_I_smooth`). -/
theorem abs_donaldsonL2_sub_le (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) (hk : 0 < k)
    (w u : C(X, ℝ)) :
    |donaldsonL2 omega hvol L T φ (w + u) k - donaldsonL2 omega hvol L T φ w k| ≤
      ‖u‖ * (normalizedH0 L T φ k).toReal := by
  rw [(donaldsonL2_sub_eq_integral omega hvol L T φ k hk w u).2, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := ‖u‖ * (normalizedH0 L T φ k).toReal)
    (f := fun t => ∫ x, u x ∂bergmanX omega L T φ (w + t • u) k)
    (fun t _ => by
      rw [Real.norm_eq_abs]
      exact abs_integral_bergmanX_le omega hvol L T φ (w + t • u) u k hk)
  simpa only [sub_zero, abs_one, mul_one] using h

/-- `|E^φ_{θ,X}(w+u) - E^φ_{θ,X}(w)| ≤ vol(θ_φ) · ‖u‖` (`prop:differential_P`). -/
theorem abs_energyX_sub_le (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) (w u : C(X, ℝ)) :
    |energyX omega hφ hφpos (w + u) - energyX omega hφ hφpos w| ≤
      ‖u‖ * (sourceIVolume θ φ hφ).toReal := by
  rw [(energyX_sub_eq_integral omega hφ hφpos w u).2, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := ‖u‖ * (sourceIVolume θ φ hφ).toReal)
    (f := deriv fun s : ℝ => energyX omega hφ hφpos (w + s • u))
    (fun t _ => by
      obtain ⟨hPI, h⟩ := hasDerivAt_energyX omega hφ hφpos w u t
      rw [h.deriv, Real.norm_eq_abs]
      exact abs_energy_derivative_le omega hφ hφpos (w + t • u) u hPI)
  simpa only [sub_zero, abs_one, mul_one] using h

/-- `N^k_{0,ωⁿ}` is the reference norm of `def:Bergman:L942`, so `L_{k,φ}(N^k_{0,ωⁿ}) = 0`. -/
theorem donaldsonL2_zero (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) :
    donaldsonL2 omega hvol L T φ 0 k = 0 := by
  by_cases hk : 0 < k
  · rw [donaldsonL2_pos omega hvol L T φ 0 k hk]
    have heq : l2Norm L T (wholeWeightedSubset (n := n) (0 : C(X, ℝ))) (volX omega)
        (volX_BM omega hvol L T 0) k hk φ = referenceNorm L T omega hvol k hk φ := by
      apply complexNorm_ext
      intro s
      apply (ENNReal.ofReal_eq_ofReal_iff (apply_nonneg _ _) (apply_nonneg _ _)).mp
      rw [l2Norm_ofReal, referenceNorm_ofReal]
      rfl
    rw [heq, partialDonaldsonFunctional]
    exact sourceDonaldsonFunctional_self _ n k _
  · rw [donaldsonL2, dif_neg hk]

/-- `E^φ_{θ,X}(0) = E^{P_θ[φ]_I}_θ(P_θ[φ]_I) = 0`. -/
theorem energyX_zero (omega : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ) :
    energyX omega hφ hφpos 0 = 0 := by
  have hPI : partialIEnvelope θ φ univ
      (fun x => ((wholeWeightedSubset (n := n) (0 : C(X, ℝ))).weight x : EReal)) =
      sourceIEnvelope θ φ := by
    rw [← partialIEnvelope_univ_zero hφ]
    congr 1
  rw [energyX, partialEquilibriumEnergy_eq_mixed_integrals]
  apply div_eq_zero_iff.mpr
  left
  apply Finset.sum_eq_zero
  intro j _
  have hz : ∀ a b : EReal, a = b → canonicalERealDiffToReal a b = 0 := by
    rintro a b rfl
    exact canonicalERealDiffToReal_self a
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => hz _ _ (congrFun hPI x))

end SGPT.Bergman.Quant2
