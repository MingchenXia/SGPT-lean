import SGPT.Bergman.SourceMultiplierSectionGlobalMass
import SGPT.Bergman.SourceActualIdealModuleSheaf
import SGPT.Bergman.SourceTensorDictionary

/-!
# TwistedMultiplierSections

The space `H⁰(X, L^k ⊗ T ⊗ I(kφ))` of source `def:Bergman:L778`: global sections of the sheaf tensor product, identified with the multiplier-ideal sections of `L^k ⊗ T`; finite-dimensionality and the `L²` description.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MultiplierSectionsDraft

open Bundle Set Filter TopologicalSpace CategoryTheory Opposite TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]


open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

/-- Literal source H0(X,L^k tensor T tensor I(k phi)), as Gamma of the genuine original SHEAF tensor. -/
abbrev LiteralTwistedMultiplierSections (L T : HermitianHolomorphicLineBundle n X)
    (k : ℕ) (φ : X → EReal) :=
  (originalBundleIdealTensorSheaf (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)).val.obj (op (⊤ : Opens X))

/-- The literal original tensor Gamma retains the SAME original complex constant-section action. -/
instance literalTwistedMultiplierComplexModule (L T : HermitianHolomorphicLineBundle n X)
    (k : ℕ) (φ : X → EReal) : Module ℂ (LiteralTwistedMultiplierSections L T k φ) :=
  tensorIdealGammaComplexModule (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)

/-- BOTH actual maps identify literal source Gamma with ALL same-degree/twist native holomorphic
sections whose genuine original coefficients belong to the ENTIRE original multiplier stalks. -/
def literalTwistedMultiplierSectionEquiv (L T : HermitianHolomorphicLineBundle n X)
    (k : ℕ) (φ : X → EReal) :
    LiteralTwistedMultiplierSections L T k φ ≃ₗ[ℂ]
      ↥(fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ)) :=
  tensorIdealGlobalSectionEquiv (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)

/-- Exact literal source degree-zero multiplier sections are ALL actual holomorphic sections. -/
theorem fullHolomorphicDegreeIdealSections_zero_eq_top
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal) :
    fullHolomorphicIdealSections (n := n) (twistedPower L T 0).Fiber
      (sourceDegreeMultiplierIdeal (n := n) 0 φ) = ⊤ := by
  rw [sourceDegreeMultiplierIdeal_zero]
  apply Submodule.eq_top_iff'.mpr
  intro s
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) (twistedPower L T 0).Fiber
    _ originalUnitGermIdeal_isCoherent s]
  intro x
  exact originalSectionCoefficient_holomorphicAt (n := n) (twistedPower L T 0).Fiber
    (preferredOriginalFrame (twistedPower L T 0).Fiber x) s
    (mem_baseSet_trivializationAt ℂ (twistedPower L T 0).Fiber x)

/-- Compact actual H0 finiteness restricts to the genuine FULL original multiplier submodule. -/
theorem fullTwistedMultiplierSections_finiteDimensional [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) (φ : X → EReal) :
    FiniteDimensional ℂ ↥(fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k φ)) := by
  let := twistedSections_finiteDimensional L T k
  infer_instance

/-- The LITERAL original Gamma space is finite-dimensional by actual BOTH-direction sheaf maps
and genuine compact H0 finiteness; there is no finite basis/family certificate. -/
theorem literalTwistedMultiplierSections_finiteDimensional [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) (φ : X → EReal) :
    FiniteDimensional ℂ (LiteralTwistedMultiplierSections L T k φ) := by
  let := fullTwistedMultiplierSections_finiteDimensional L T k φ
  exact FiniteDimensional.of_injective (literalTwistedMultiplierSectionEquiv L T k φ).toLinearMap
    (literalTwistedMultiplierSectionEquiv L T k φ).injective

variable [MeasurableSpace X] [BorelSpace X]

/-- Genuine finite original phi-weighted L2 section module for the SAME actual h^k tensor h_T.
The carrier is the ACTUAL extended integral predicate; its closure is proved from the established
original stalk/integral theorem, rather than supplied as data. -/
def twistedMultiplierL2Submodule [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
    (hμ : IsSmoothPositiveVolume (n := n) μ) : Submodule ℂ (twistedSections L T k) where
  carrier := {s | (∫⁻ x, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k s x ∂μ) < ⊤}
  zero_mem' := (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
    (twistedPower L T k).Fiber k hφ 0 hμ).mp (Submodule.zero_mem _)
  add_mem' := by
    intro s t hs ht
    exact (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
      (twistedPower L T k).Fiber k hφ (s + t) hμ).mp
      (Submodule.add_mem _
        ((fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
          (twistedPower L T k).Fiber k hφ s hμ).mpr hs)
        ((fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
          (twistedPower L T k).Fiber k hφ t hμ).mpr ht))
  smul_mem' := by
    intro r s hs
    exact (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
      (twistedPower L T k).Fiber k hφ (r • s) hμ).mp
      (Submodule.smul_mem _ r ((fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
        (twistedPower L T k).Fiber k hφ s hμ).mpr hs))

/-- BOTH directions identify the actual integral-defined full module with the original ideal-stalk submodule. -/
theorem twistedMultiplierL2Submodule_eq_originalIdeal [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
    (hμ : IsSmoothPositiveVolume (n := n) μ) :
    twistedMultiplierL2Submodule L T k hφ μ hμ =
      fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ) := by
  ext s
  exact (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
    (twistedPower L T k).Fiber k hφ s hμ).symm

/-- The LITERAL source sheaf-tensor Gamma has actual BOTH-direction complex linear maps to the
TRUE SAME-metric original phi-weighted finite-L2 module, retaining ALL sections and ALL degrees. -/
def literalTwistedMultiplierL2Equiv [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
    (hμ : IsSmoothPositiveVolume (n := n) μ) :
    LiteralTwistedMultiplierSections L T k φ ≃ₗ[ℂ] twistedMultiplierL2Submodule L T k hφ μ hμ :=
  (literalTwistedMultiplierSectionEquiv L T k φ).trans
    (LinearEquiv.ofEq _ _ (twistedMultiplierL2Submodule_eq_originalIdeal L T k hφ μ hμ).symm)

omit [BorelSpace X] in
/-- Literal original extended-potential readback into the PREEXISTING source weighted-L2 norm,
on the SAME actual full-X subtype and comapped SAME original volume, including every pole. -/
theorem originalWeightedL2Norm_univ (L T : HermitianHolomorphicLineBundle n X)
    (k : ℕ) (φ : X → EReal) (μ : Measure X) (s : twistedSections L T k) :
    weightedL2Norm (twistedPower L T k).Fiber k (fun x : ↥(univ : Set X) => φ x.val)
      (μ.comap (Subtype.val : ↥(univ : Set X) → X)) s =
      (∫⁻ x, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k s x ∂μ) ^ (1 / 2 : ℝ) := by
  unfold weightedL2Norm
  have hi := lintegral_subtype_comap (μ := μ) MeasurableSet.univ
    (originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k s)
  exact congrArg (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ)) (by
    simpa only [weightedSectionDensity, originalSectionDensity, Measure.restrict_univ] using hi)

/-- BOTH source finite-norm directions are proved at SAME unscaled phi and SAME h^k tensor h_T,
with literal original I(k phi), ALL sections and ALL degrees, rather than assumed. -/
theorem fullTwistedMultiplierSections_iff_sourceNorm_finite [CompactSpace X]
    (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
    (hμ : IsSmoothPositiveVolume (n := n) μ) (s : twistedSections L T k) :
    s ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ) ↔
      weightedL2Norm (twistedPower L T k).Fiber k (fun x : ↥(univ : Set X) => φ x.val)
        (μ.comap (Subtype.val : ↥(univ : Set X) → X)) s < ⊤ := by
  rw [originalWeightedL2Norm_univ, ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
    (twistedPower L T k).Fiber k hφ s hμ

end SGPT.Bergman.MultiplierSectionsDraft
