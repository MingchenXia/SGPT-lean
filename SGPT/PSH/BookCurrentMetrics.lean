import SGPT.PSH.BookFubiniStudyMetrics
import SGPT.PSH.GlobalPComparison
import SGPT.Bergman.SourceGlobalWeightSmoothApproximation

/-!
# Hermitian pseudo-effective line bundles and elementary metrics

Sources: `chapter_Igood.tex`, `def:Hermpsef`; `chapter_comp.tex`, `def:elemetric`.

* `HermitianPseudoeffective L` (`def:Hermpsef`): a holomorphic line bundle `L` together with a
  plurisubharmonic metric on it (`def:pshfunctions:L1836`, `SGPT.PSH.LineBundleMetric.IsPSHMetric`).
* `IsElementaryMetric L h` (`def:elemetric`): `h` is a psh metric and there is a generalized
  Fubini–Study metric `h'` (`def:gFSmetric`) with `dd^c h ∼_P dd^c h'`.  The Chern current of a
  psh metric presented as `h = h₀ e^{-φ}` is `dd^c h = c₁(L, h₀) + dd^c φ`
  (`SGPT.PSH.LineBundleMetric.chernCurrent`), and by the convention of `rmk:qpshtocurrents` a
  notion depending only on the (`P`-)singularity type is read on the potentials: `dd^c h ∼_P dd^c h'`
  means `φ ∼_P φ'` (`def:Pmoresing`, `SGPT.PSH.GlobalPComparison.sourcePEquivalent`) for the
  potentials of presentations of `h` and `h'`.  This is independent of the presentations
  (`chernCurrentPEquivalent_iff_of_presentations`): two presentations of the same metric differ by
  the smooth function `log (h₀ / h₁)`, which is bounded on the compact manifold.
* `IsElementaryPotential` ("we also say `φ` is elementary").

The standing assumptions of the source (`X` a connected compact Kähler manifold, `L`
pseudo-effective) are kept as hypotheses where they are used (`P`-equivalence is defined on
compact connected manifolds and its properties use a Kähler form); pseudo-effectivity of `L` is
context for the definition and is not needed to state it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.PSH.LineBundleMetric

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-! ### Hermitian pseudo-effective line bundles (`def:Hermpsef`) -/

section Hermpsef

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (n) in
/-- **A Hermitian pseudo-effective line bundle** `(L, h)` (`def:Hermpsef`): the holomorphic line
bundle `L` (a complex line bundle with holomorphic transition functions over the complex
manifold `X`) together with a plurisubharmonic metric `h` on `L`. -/
structure HermitianPseudoeffective (L : X → Type*) [∀ x, AddCommGroup (L x)]
    [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace ℂ L)]
    [FiberBundle ℂ L] [VectorBundle ℂ ℂ L] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)] where
  /-- The plurisubharmonic metric. -/
  metric : (x : X) → L x → ℝ≥0∞
  isPSHMetric : IsPSHMetric (n := n) L metric

end Hermpsef

/-! ### Presentations of a psh metric -/

section Presentation

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- Two presentations `h = h₀ e^{-φ} = h₁ e^{-ψ}` of the same metric differ by
`log (h₀ / h₁)`: `ψ = φ - log (h₀/h₁)`. -/
theorem IsPSHMetricWith.potential_eq {q : (x : X) → L x → ℝ≥0∞}
    {h₀ h₁ : HermitianMetric (n := n) L} {φ ψ : X → EReal}
    (hφ : IsPSHMetricWith q h₀ φ) (hψ : IsPSHMetricWith q h₁ ψ) :
    ψ = fun x => φ x - (logRatio h₀ h₁ x : EReal) := by
  apply twistedForm_injective h₁
  funext x v
  rw [← hψ.eq_twisted, ← twistedForm_changeReference h₀ h₁, ← hφ.eq_twisted]

/-- On a compact manifold two presentations of the same metric have potentials of the same
singularity type. -/
theorem IsPSHMetricWith.sameSingularityType [CompactSpace X] {q : (x : X) → L x → ℝ≥0∞}
    {h₀ h₁ : HermitianMetric (n := n) L} {φ ψ : X → EReal}
    (hφ : IsPSHMetricWith q h₀ φ) (hψ : IsPSHMetricWith q h₁ ψ) :
    MoreSingularOn φ ψ univ ∧ MoreSingularOn ψ φ univ := by
  have hcont : Continuous (logRatio h₀ h₁) :=
    SGPT.Bergman.GlobalWeightSmoothApproximation.continuous_of_chartSmooth
      (chartSmooth_logRatio h₀ h₁)
  obtain ⟨C, hC⟩ := (isCompact_univ.image hcont).isBounded.exists_norm_le
  have hb : ∀ x, |logRatio h₀ h₁ x| ≤ C := fun x => by
    simpa [Real.norm_eq_abs] using hC _ ⟨x, mem_univ x, rfl⟩
  have hψeq := hφ.potential_eq hψ
  subst hψeq
  have hne : ∀ x, φ x ≠ ⊤ := fun y => hφ.thetaPsh.1.quasiPlurisubharmonic.ne_top y
  refine ⟨⟨C, fun x _ => ?_⟩, ⟨C, fun x _ => ?_⟩⟩
  · -- `φ ≤ (φ - g) + C`
    show φ x ≤ (φ x - (logRatio h₀ h₁ x : EReal)) + (C : EReal)
    have hg : logRatio h₀ h₁ x ≤ C := (le_abs_self _).trans (hb x)
    induction hφx : φ x using EReal.rec with
    | bot => simp
    | top => exact absurd hφx (hne x)
    | coe a =>
      rw [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
  · -- `φ - g ≤ φ + C`
    show φ x - (logRatio h₀ h₁ x : EReal) ≤ φ x + (C : EReal)
    have hg : -C ≤ logRatio h₀ h₁ x := by
      have := neg_abs_le (logRatio h₀ h₁ x)
      linarith [hb x]
    induction hφx : φ x using EReal.rec with
    | bot => simp
    | top => exact absurd hφx (hne x)
    | coe a =>
      rw [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith

end Presentation

/-! ### Elementary metrics (`def:elemetric`) -/

section Elementary

open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **`dd^c h ∼_P dd^c h'`** for psh metrics `h, h'` on `L`: the potentials of all presentations
`h = h₀ e^{-φ}`, `h' = h₀' e^{-φ'}` (i.e. `dd^c h = c₁(L,h₀) + dd^c φ`,
`dd^c h' = c₁(L,h₀') + dd^c φ'`) have the same `P`-singularity type. -/
def ChernCurrentPEquivalent (L : HermitianHolomorphicLineBundle.{u,v} n M)
    (h h' : (x : M) → L.Fiber x → ℝ≥0∞) : Prop :=
  ∀ (h₀ h₀' : HermitianMetric (n := n) L.Fiber) (φ φ' : M → EReal),
    IsPSHMetricWith h h₀ φ → IsPSHMetricWith h' h₀' φ' →
      SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n) φ φ'

/-- **Independence of the presentations**: `dd^c h ∼_P dd^c h'` holds as soon as it holds for one
pair of presentations. -/
theorem chernCurrentPEquivalent_iff_of_presentations (omega : KahlerBackground n M)
    (L : HermitianHolomorphicLineBundle.{u,v} n M) {h h' : (x : M) → L.Fiber x → ℝ≥0∞}
    {h₀ h₀' : HermitianMetric (n := n) L.Fiber} {φ φ' : M → EReal}
    (hφ : IsPSHMetricWith h h₀ φ) (hφ' : IsPSHMetricWith h' h₀' φ') :
    ChernCurrentPEquivalent L h h' ↔
      SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n) φ φ' := by
  refine ⟨fun H => H h₀ h₀' φ φ' hφ hφ', fun H h₁ h₁' ψ ψ' hψ hψ' => ?_⟩
  have hq := hψ.thetaPsh.quasiPshPotential
  have hq' := hψ'.thetaPsh.quasiPshPotential
  have hp := hφ.thetaPsh.quasiPshPotential
  have hp' := hφ'.thetaPsh.quasiPshPotential
  obtain ⟨h1, h2⟩ := hψ.sameSingularityType hφ
  obtain ⟨h3, h4⟩ := hφ'.sameSingularityType hψ'
  refine ⟨?_, ?_⟩
  · exact SGPT.PSH.GlobalPComparison.sourcePOrder_trans omega
      (SGPT.PSH.GlobalPComparison.sourcePOrder_of_moreSingular omega hq hp h1)
      (SGPT.PSH.GlobalPComparison.sourcePOrder_trans omega H.1
        (SGPT.PSH.GlobalPComparison.sourcePOrder_of_moreSingular omega hp' hq' h3))
  · exact SGPT.PSH.GlobalPComparison.sourcePOrder_trans omega
      (SGPT.PSH.GlobalPComparison.sourcePOrder_of_moreSingular omega hq' hp' h4)
      (SGPT.PSH.GlobalPComparison.sourcePOrder_trans omega H.2
        (SGPT.PSH.GlobalPComparison.sourcePOrder_of_moreSingular omega hp hq h2))

/-- **Elementary metrics** (`def:elemetric`): psh metrics `h` on `L` for which there is a
generalized Fubini–Study metric `h'` with `dd^c h ∼_P dd^c h'`. -/
def IsElementaryMetric (L : HermitianHolomorphicLineBundle.{u,v} n M)
    (h : (x : M) → L.Fiber x → ℝ≥0∞) : Prop :=
  IsPSHMetric (n := n) L.Fiber h ∧
    ∃ h', IsGeneralizedFubiniStudyMetric L h' ∧ ChernCurrentPEquivalent L h h'

/-- `Ele(L)`. -/
def elementaryMetrics (L : HermitianHolomorphicLineBundle.{u,v} n M) :
    Set ((x : M) → L.Fiber x → ℝ≥0∞) :=
  {h | IsElementaryMetric L h}

/-- "We also say `φ` is elementary": `h₀ e^{-φ}` is an elementary metric. -/
def IsElementaryPotential (L : HermitianHolomorphicLineBundle.{u,v} n M)
    (h₀ : HermitianMetric (n := n) L.Fiber) (φ : M → EReal) : Prop :=
  IsElementaryMetric L (twistedForm h₀ φ)

/-- With a fixed reference metric `h₀`, `h = h₀ e^{-φ}` is elementary iff there is a generalized
Fubini–Study metric `h₀ e^{-φ'}` with `φ ∼_P φ'`. -/
theorem isElementaryMetric_iff_of_reference (omega : KahlerBackground n M)
    (L : HermitianHolomorphicLineBundle.{u,v} n M) (h₀ : HermitianMetric (n := n) L.Fiber)
    {h : (x : M) → L.Fiber x → ℝ≥0∞} {φ : M → EReal} (hφ : IsPSHMetricWith h h₀ φ) :
    IsElementaryMetric L h ↔
      ∃ φ' : M → EReal, IsGeneralizedFubiniStudyMetric L (twistedForm h₀ φ') ∧
        IsThetaPshPotential (firstChernForm h₀).val φ' ∧
        SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n) φ φ' := by
  constructor
  · rintro ⟨-, h', hgfs, hP⟩
    obtain ⟨φ', hφ'⟩ := (isPSHMetric_iff_exists_potential h₀ h').mp hgfs.isPSHMetric
    have heq : h' = twistedForm h₀ φ' := funext fun x => funext fun w => hφ'.eq_twisted x w
    refine ⟨φ', heq ▸ hgfs, hφ'.thetaPsh, hP h₀ h₀ φ φ' hφ hφ'⟩
  · rintro ⟨φ', hgfs, hth, hP⟩
    refine ⟨IsPSHMetric.of_with hφ, twistedForm h₀ φ', hgfs, ?_⟩
    exact (chernCurrentPEquivalent_iff_of_presentations omega L hφ
      ⟨hth, fun _ _ => rfl⟩).mpr hP

end Elementary

end SGPT.PSH.LineBundleMetric
