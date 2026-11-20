import SGPT.Hodge.Trace
import SGPT.Foundations.Analysis.Pending.NaturalHermitianCompactWeakGreen

/-!
# Finite dimensionality of `H^{1,1}(X, ℝ)` from coclosed constant-trace representatives

Blueprint `claude-hodge`, package `HodgeFinite`, node
`claude-hodge:thm-finite-dimensional`; route of Xia, *Foundations of pluripotential theory*,
`def:real-one-one-cohomology` and the paragraph after it ("every class contains exactly one
harmonic form, so `H^{1,1}(X, ℝ)` is isomorphic to the space of harmonic real `(1,1)`-forms; in
particular it is finite dimensional").

Let `(X, ω)` be a compact connected Kähler manifold.  By `SGPT.Hodge.Trace` every real
Bott–Chern class contains a closed real `(1,1)`-form of constant `ω`-trace.  If such forms are
**coclosed** (`ConstantTraceCoclosed w`, the statement of package `HodgeStar`, node
`claude-hodge:prop-constant-trace-coclosed`: `d*γ = 0`, from the Kähler identity
`*γ = (Λγ) ω^{n-1}/(n-1)! - γ ∧ ω^{n-2}/(n-2)!`), then their `L²` classes lie in the weak harmonic
kernel of the Hodge Laplacian on `L²` two-forms, which TN proves finite dimensional
(`NaturalHermitianCompactWeakGreen.harmonicKernel_finiteDimensional`: the shifted weak resolvent is
a compact operator, Rellich).  A constant-trace form whose `L²` class vanishes is geometrically
zero, hence has class zero.  So `H^{1,1}(X, ℝ)` is a quotient of a subspace of a
finite-dimensional space:

* `SGPT.Hodge.finiteDimensional_realBottChern_of_coclosed`.

No `sorry`, no axioms: the coclosedness is an explicit hypothesis (a `def … : Prop`), to be
discharged by package `HodgeStar`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NaturalHermitianFormL2
  SGPT.Foundations.Analysis.Pending.NaturalHermitianGraphEnergy
  SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakHarmonicKernel
  SGPT.Foundations.Analysis.Pending.NaturalHermitianCompactWeakGreen
  SGPT.Foundations.Analysis.Pending.NaturalHermitianCodifferential

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Coclosedness of constant-trace forms** (statement of package `HodgeStar`,
`claude-hodge:prop-constant-trace-coclosed`): every closed real `(1,1)`-form of constant
`ω`-trace has vanishing codifferential `d*γ = -*d*γ` (TN `coderivativeForm` for the Riemannian
metric of `ω`). -/
def ConstantTraceCoclosed (w : KahlerBackground n M) : Prop :=
  ∀ γ ∈ constantTraceSubmodule w,
    (coderivativeForm w.form.val w.isKahler.1 2 γ.val).GeometricallyEq 0

section Compact

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The `L²` class of a closed real `(1,1)`-form, as a real-linear map. -/
def toL2 (w : KahlerBackground n M) :
    ClosedRealOneOneForm n M →ₗ[ℝ] HilbertFormL2 w.form.val w.isKahler.1 2 where
  toFun γ := toHilbertFormL2 w.form.val w.isKahler.1 γ.val
  map_add' γ γ' := (toHilbertFormL2Linear w.form.val w.isKahler.1 2).map_add γ.val γ'.val
  map_smul' c γ := (toHilbertFormL2Linear w.form.val w.isKahler.1 2).map_smul c γ.val

theorem toL2_apply (w : KahlerBackground n M) (γ : ClosedRealOneOneForm n M) :
    toL2 w γ = toHilbertFormL2 w.form.val w.isKahler.1 γ.val := rfl

/-- A smooth form that vanishes on every chart target has zero `L²` class. -/
theorem toHilbertFormL2_eq_zero_of_geometricallyEq_zero (w : KahlerBackground n M) {q : ℕ}
    {α : SmoothRealForm n M q} (h : α.GeometricallyEq 0) :
    toHilbertFormL2 w.form.val w.isKahler.1 α = 0 := by
  rw [(toHilbertFormL2_eq_iff w.form.val w.isKahler.1 α 0).mpr h]
  exact (toHilbertFormL2Linear w.form.val w.isKahler.1 q).map_zero

/-- **A closed coclosed real `(1,1)`-form is weakly harmonic**: its `L²` class lies in TN's weak
harmonic kernel. -/
theorem toL2_mem_harmonicKernel (w : KahlerBackground n M) (γ : ClosedRealOneOneForm n M)
    (hco : (coderivativeForm w.form.val w.isKahler.1 2 γ.val).GeometricallyEq 0) :
    toL2 w γ ∈ harmonicKernel w 2 := by
  rw [toL2_apply, ← energyInclusion_smooth w γ.val]
  refine (energyInclusion_mem_harmonicKernel_iff w _).mpr ⟨?_, ?_⟩
  · rw [energyDerivative_smooth]
    exact toHilbertFormL2_eq_zero_of_geometricallyEq_zero w γ.property.1
  · rw [energyCoderivative_smooth]
    exact toHilbertFormL2_eq_zero_of_geometricallyEq_zero w hco

variable [ConnectedSpace M]

/-- **Finite dimensionality of `H^{1,1}(X, ℝ)`** (`claude-hodge:thm-finite-dimensional`), for a
compact connected Kähler manifold, given the coclosedness of constant-trace forms. -/
theorem finiteDimensional_realBottChern_of_coclosed (w : KahlerBackground n M)
    (hco : ConstantTraceCoclosed w) : FiniteDimensional ℝ (RealBottChern n M) := by
  classical
  set Z := constantTraceSubmodule w
  -- `L₁ : Z → L²`, with range in the finite-dimensional weak harmonic kernel
  set L₁ : Z →ₗ[ℝ] HilbertFormL2 w.form.val w.isKahler.1 2 := (toL2 w).comp Z.subtype
  -- `L₂ : Z → H^{1,1}`, onto
  set L₂ : Z →ₗ[ℝ] RealBottChern n M := RealBottChern.ofRepresentativeLinearMap.comp Z.subtype
  have hrange : LinearMap.range L₁ ≤ harmonicKernel w 2 := by
    rintro _ ⟨γ, rfl⟩
    exact toL2_mem_harmonicKernel w γ.val (hco γ.val γ.property)
  have : FiniteDimensional ℝ (harmonicKernel w 2) := harmonicKernel_finiteDimensional w 2
  have : FiniteDimensional ℝ (LinearMap.range L₁) :=
    Submodule.finiteDimensional_of_le hrange
  have : FiniteDimensional ℝ (Z ⧸ LinearMap.ker L₁) :=
    LinearEquiv.finiteDimensional (L₁.quotKerEquivRange).symm
  have hker : LinearMap.ker L₁ ≤ LinearMap.ker L₂ := by
    intro γ hγ
    rw [LinearMap.mem_ker] at hγ ⊢
    have hgeo : γ.val.val.GeometricallyEq (0 : ClosedRealOneOneForm n M).val := by
      have h0 : toHilbertFormL2 w.form.val w.isKahler.1 γ.val.val =
          toHilbertFormL2 w.form.val w.isKahler.1 (0 : SmoothRealForm n M 2) :=
        hγ.trans (toHilbertFormL2Linear w.form.val w.isKahler.1 2).map_zero.symm
      exact (toHilbertFormL2_eq_iff w.form.val w.isKahler.1 _ _).mp h0
    change RealBottChern.ofRepresentative γ.val = 0
    rw [← RealBottChern.ofRepresentative_zero]
    exact ((RealBottChern.ofRepresentative_eq_iff _ _).mpr
      (ClosedRealOneOneForm.bottChernRel_of_geometricallyEq hgeo.symm)).symm
  have hsurj : Function.Surjective L₂ := by
    intro α
    obtain ⟨γ, hγ, hα⟩ := exists_constantTrace_representative w α
    exact ⟨⟨γ, hγ⟩, hα⟩
  set F : (Z ⧸ LinearMap.ker L₁) →ₗ[ℝ] RealBottChern n M := (LinearMap.ker L₁).liftQ L₂ hker
  have hFsurj : Function.Surjective F := by
    intro α
    obtain ⟨γ, hγ⟩ := hsurj α
    exact ⟨Submodule.Quotient.mk γ, by simp [F, hγ]⟩
  exact Module.Finite.of_surjective F hFsurj

end Compact

end SGPT.Hodge
