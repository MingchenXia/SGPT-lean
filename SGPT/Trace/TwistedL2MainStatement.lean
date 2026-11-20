import SGPT.Trace.TwistedL2Flat
import SGPT.Foundations.Analysis.Pending.HormanderAbstract
import SGPT.Foundations.Analysis.Pending.WeakDbarWeyl
import SGPT.Foundations.Analysis.Pending.OTWeakDbar

/-!
# The global twisted `L²` estimate: the key functional bound

Blueprint `claude-twisted-l2-b.tex` (lane TL2-B, package E1.B).  This file fixes the objects of
the Hilbert-space proof of `TwistedL2CorrectionStatement` (`claude-twisted-l2:main`) and states
its analytic core, the **functional bound** of Hörmander's method:

`|⟨τ, ∂̄G⟩|² ≤ (∫_U D e^{-φ} dμ) · ‖T* τ‖²_{H₁}`        for all test forms `τ`,

`H₁ = L²(U, L; e^{-φ}/(a+b) dμ)`, `T* τ = (a+b) ϑ τ`.

## Test forms as sums of local pieces

As in `TwistedL2Statement.lean`, an `L`-valued `(0,1)`-form `τ` is represented by the vector
field `W = σ^♯ τ`; then `⟨∂̄G, τ⟩_σ = ⟨∂̄G_e, W_e⟩ |e|²_h` (`dbarPairing`, no metric) and
`ϑ τ = -div_p W = ∑_j -δ_j W_j` with `δ_j = ∂_j - ∂_j p` (`chartTheta`, no metric).

A *local piece* is a chart `c`, a frame `e`, the density `ρ` of `μ` in `c` and a smooth
coefficient vector `h` with compact support in `c(U ∩ dom e)` (`IsLocalTestField`): it is the
vector field `h ⊗ e` in the chart.  Every test form is a finite sum of local pieces (partition of
unity), so we state the bound for finite families of pieces.  Each piece contributes

* `T* = (a+b) ϑ`, the section `x ↦ (a+b)(x) ϑ_c h (c x) · e(x)` (`TwistedDatum.localTStar`), and
* the data pairing `∫ ⟨∂̄G_e, h⟩ e^{-p} dλ` (`TwistedDatum.localDataPairing`),

both computed in the piece's own chart: no chart-independence is built into the definitions; the
sums `∑ T*` and `∑ ⟨∂̄G, ·⟩` are the true values for the global test form `∑ h_i ⊗ e_i`
(chart-independence of `ϑ` and of the pairing), which is where the proof of the bound uses it.

## Main definitions

* `chartTheta p h`: `ϑ = -∑_j δ_j h_j`, the formal adjoint of `∂̄` in `L²(e^{-p} dλ)`.
* `IsLocalTestField L U c e h`.
* `TwistedDatum n X`: the data and hypotheses of `TwistedL2CorrectionStatement`.
* `TwistedFunctionalBoundStatement n X`: the functional bound (the analytic core: global
  Bochner--Kodaira--Nakano with twist, and density of test forms).

The reduction `TwistedFunctionalBoundStatement n X → TwistedL2CorrectionStatement n X` (the
Hilbert-space step and Weyl's lemma) is `SGPT/Trace/TwistedL2MainAssembly.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

/-- `ϑ h = -∑_j δ_j h_j`, `δ_j = ∂_j - (∂_j p)`: the formal adjoint of `∂̄` in `L²(e^{-p} dλ)`
applied to the vector field `h` (for `h = σ^♯ τ` this is `ϑ τ = -div_p W`). -/
def chartTheta {n : ℕ} (p : ComplexModel n → ℝ) (h : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  -∑ j, deltaDir (coordVec j) p (fun y => h y j) z

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `h` is the coefficient vector, in the chart `c` and the frame `e`, of a *local test field*: a
smooth `L`-valued `(1,0)`-vector field with compact support in `U ∩ c.source ∩ e.baseSet`. -/
def IsLocalTestField (L : HermitianHolomorphicLineBundle.{0, 0} n X) (U : Set X)
    (c : ComplexChart n X) (e : AtlasFrame L) (h : ComplexModel n → ComplexModel n) : Prop :=
  ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ tsupport h ⊆ chartFrameDomain L c e ∩ c.val.symm ⁻¹' U

variable (n X) [MeasurableSpace X] [BorelSpace X]

/-- The data and the hypotheses of `TwistedL2CorrectionStatement` (`claude-twisted-l2:main`):
an open `U` with a complete Kähler form `σ = ω + ddᶜr`, a smooth positive volume `μ`, a Hermitian
line bundle with smooth metric, weights `φ, a, b`, positive twisted curvature, and a smooth
section `G` with data densities `D` (for the twisted curvature) and `Dσ` (for `σ`). -/
structure TwistedDatum where
  omega : KahlerBackground n X
  U : Set X
  isOpen_U : IsOpen U
  r : X → ℝ
  kahler : IsKahlerModificationOn omega r U
  complete : HasCompleteCutoffs omega r U
  μ : Measure X
  volume_smooth : IsSmoothPositiveVolume (n := n) μ
  L : HermitianHolomorphicLineBundle.{0, 0} n X
  metric_smooth : IsSourceSmoothHermitianMetric L
  φ : X → ℝ
  a : X → ℝ
  b : X → ℝ
  φ_smooth : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) φ U
  a_smooth : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) a U
  b_smooth : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) b U
  bounds : ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ U, m ≤ a x ∧ a x ≤ M ∧ m ≤ b x ∧ b x ≤ M
  curvature_pos : ∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ),
    IsChartDensity μ c ρ → ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U →
      ∀ v : ComplexModel n, v ≠ 0 →
        0 < twistedCurvature (fun y => a (c.val.symm y)) (fun y => b (c.val.symm y))
          (localWeight L c e ρ φ) z v
  G : (x : X) → L.Fiber x
  G_smooth : IsSmoothSectionOn L G U
  D : X → ℝ
  Dσ : X → ℝ
  D_bound : ∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ),
    IsChartDensity μ c ρ → ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U →
      ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          D (c.val.symm z) * twistedCurvature (fun y => a (c.val.symm y))
            (fun y => b (c.val.symm y)) (localWeight L c e ρ φ) z v
  Dσ_bound : ∀ (c : ComplexChart n X) (e : AtlasFrame L),
    ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U → ∀ v : ComplexModel n,
      ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
        Dσ (c.val.symm z) * modifiedKahlerQuad omega r c z v
  Dσ_integrable : ∫⁻ x in U, ENNReal.ofReal (Dσ x * Real.exp (-φ x)) ∂μ < ⊤

variable {n X}

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The weight `e^{-φ}/(a+b)` of `H₁ = L²(U, L; e^{-φ}/(a+b) dμ)`. -/
def H1weight (x : X) : ℝ := Real.exp (-T.φ x) / (T.a x + T.b x)

open Classical in
/-- `T* = (a+b) ϑ` of the local test field `h ⊗ e` in the chart `c` (with the density `ρ` of `μ`):
the section `x ↦ (a+b)(x) · ϑ_c h (c x) · e(x)` of `L`, zero off the chart-frame domain. -/
def localTStar (c : ComplexChart n X) (e : AtlasFrame T.L) (ρ : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) : (x : X) → T.L.Fiber x := fun x =>
  if x ∈ c.val.source ∩ e.val.baseSet then
    (((T.a x + T.b x : ℝ) : ℂ) * chartTheta (localWeight T.L c e ρ T.φ) h (c.val x)) •
      e.val.symm x 1
  else 0

/-- The data pairing `⟨∂̄G, h ⊗ e⟩ = ∫ ⟨∂̄G_e, h⟩ e^{-p} dλ` of the local test field `h ⊗ e`
(`e^{-p} = |e|²_h e^{-φ} ρ`, so this is `∫_U ⟨∂̄G, τ⟩_{σ,h} e^{-φ} dμ` for `τ = σ^♭(h ⊗ e)`). -/
def localDataPairing (c : ComplexChart n X) (e : AtlasFrame T.L) (ρ : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) : ℂ :=
  ∫ z, dbarPairing (chartCoeff T.L c e T.G) z (h z) * cweight (localWeight T.L c e ρ T.φ) z

end TwistedDatum

variable (n X)

/-- **The functional bound of Hörmander's method for the twisted estimate**
(`claude-twisted-l2-b:functional-bound`).  For every finite family of local test fields
`h_i ⊗ e_i` (in charts `c_i` with densities `ρ_i`), whose sum is the test form `τ = ∑_i h_i ⊗ e_i`,

`|⟨τ, ∂̄G⟩|² ≤ (∫_U D e^{-φ} dμ) · ∫_U |T* τ|²_h e^{-φ}/(a+b) dμ`,   `T* τ = ∑_i (a+b) ϑ (h_i ⊗ e_i)`,

provided `∫_U D e^{-φ} dμ < ∞`.  This is the twisted a priori inequality
(`claude-twisted-l2:twisted-bkn`) combined with the density of test forms in
`Dom T* ∩ ker S` (`claude-twisted-l2:density`), through `norm_inner_le_of_approx'`. -/
def TwistedFunctionalBoundStatement : Prop :=
  ∀ T : TwistedDatum n X, ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤ →
  ∀ (ι : Type) (s : Finset ι) (c : ι → ComplexChart n X) (e : ι → AtlasFrame T.L)
    (ρ : ι → ComplexModel n → ℝ) (h : ι → ComplexModel n → ComplexModel n),
    (∀ i ∈ s, IsChartDensity T.μ (c i) (ρ i)) → (∀ i ∈ s, IsLocalTestField T.L T.U (c i) (e i) (h i)) →
    ENNReal.ofReal (‖∑ i ∈ s, T.localDataPairing (c i) (e i) (ρ i) (h i)‖ ^ 2) ≤
      (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ) *
        ∫⁻ x in T.U, ENNReal.ofReal
          (‖∑ i ∈ s, T.localTStar (c i) (e i) (ρ i) (h i) x‖ ^ 2 * T.H1weight x) ∂T.μ

end SGPT.Trace.TwistedL2
