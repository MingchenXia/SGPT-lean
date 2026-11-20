import SGPT.Bergman.SourceSmoothMetricPolynomialBound
import SGPT.PSH.BookLineBundleMetrics
import SGPT.Foundations.Analysis.Pending.HormanderInterface
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import SGPT.Foundations.Analysis.Pending.WeightedWirtingerAdjoint
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import SGPT.Foundations.Analysis.FirstPass.MultiplierIdeals
import SGPT.Foundations.Analysis.LeviForm

/-!
# Global twisted `L²` estimates: the published statements

Blueprint `claude-twisted-l2.tex` (lane GLOBAL-TWISTED-L2, package E1 of the Bertini plan).
This file only *states* the intermediate results of the route to the global twisted
(Ohsawa--Takegoshi / Demailly) `L²` estimate for `∂̄` on line-bundle-valued `(n,1)`-forms, with
constants independent of the weight, so that independent pieces can be proved in parallel.  None
of the definitions below is assumed anywhere as a hypothesis of a result presented as proved.

## Conventions

All statements are phrased with *sections* of a Hermitian holomorphic line bundle `L` and a smooth
positive volume `μ`: an `L`-valued function `s` is identified with the `L ⊗ K_X^{-1}`-valued
`(n,0)`-form `s ⊗ (dz₁ ∧ ⋯ ∧ dzₙ)^{-1} ⊗ dz₁ ∧ ⋯ ∧ dzₙ`, the metric of `K_X^{-1}` being the one
induced by `μ` (Xia, *Foundations of pluripotential theory*, q07, proof of
`thm:compact-submanifold-extension`, Step 1).  Under this identification `|u|² dV = |s|²_h e^{-φ} dμ`
for every Kähler form, and in a chart `c` with a frame `e` of `L` and `μ = ρ dλ` the full local
weight of the twisted bundle is

`p = -log |e|²_h + φ - log ρ`                                  (`localWeight`),

whose Levi form is `2π c₁(L, h e^{-φ}) + Ric(μ)`.  For twist functions `a, b > 0` the twisted
curvature is the Hermitian form

`H(ξ) = a Levi(p)(ξ) - Levi(a)(ξ) - |∂a(ξ)|² / b`              (`twistedCurvature`),

(`H = a·2πc₁ - i∂∂̄a - b⁻¹ i∂a ∧ ∂̄a`, FPT `lem:twisted-kahler-line-estimate`).  The datum is
`∂̄G` for a smooth section `G`; its twisted norm `⟨B⁻¹∂̄G, ∂̄G⟩` is encoded, as in
`SGPT.Foundations.Analysis.Pending.Hormander.HormanderL2Estimate`, by a density `D` with
`|⟨∂̄G, ξ⟩|²_h ≤ D · H(ξ)` for all `ξ` (the least such `D` is `⟨H⁻¹∂̄G, ∂̄G⟩_h`).

## Statements

* `TwistedL2CorrectionStatement n X` (`claude-twisted-l2:main`): FPT
  `lem:twisted-kahler-line-estimate` for `∂̄`-exact data on an open set `U` of a Kähler manifold
  which carries a complete Kähler form `σ = ω + ddᶜr` (in the sense of cut-offs with
  `|dχ_k|_σ ≤ C/k`).
* `CompactTwistedL2CorrectionStatement n X` (`claude-twisted-l2:compact`): the same on a compact
  Kähler manifold for a quasi-psh weight `ψ` smooth off an analytic pole set (gentle analytic
  singularities, log poles along submanifolds), solution holomorphic on all of `X`.
* `WeaklyPseudoconvexTwistedL2CorrectionStatement n X` (`claude-twisted-l2:weakly-pseudoconvex`):
  the same on a weakly pseudoconvex Kähler manifold (smooth psh exhaustion).
* `AnalyticComplementCutoffStatement n X` (`claude-twisted-l2:complement-cutoffs`): FPT
  `lem:analytic-complement-cutoffs`.
* `L2RemovableSingularityStatement n X` (`claude-twisted-l2:l2-removable`): FPT
  `lem:l2-holomorphic-analytic-removal`.
* `FriedrichsStatement n N N'` (`claude-twisted-l2:friedrichs`): Friedrichs' lemma for first order
  systems with smooth coefficients on open sets of `ℂⁿ`.
* `KahlerLoweringStatement n` (`claude-twisted-l2:kahler-lowering`): for a Kähler potential `r`,
  `∂̄(r^♭ W)` is the antisymmetrization of `r^♭ ∂̄W` (the only place where `dσ = 0` is used).

Proved bottom pieces (`SGPT/Trace/TwistedL2Twist.lean`, `TwistedL2Pointwise.lean`,
`TwistedL2Flat.lean`, `TwistedL2KahlerLowering.lean`): the critical twist functions (FPT
`lem:critical-twist-functions`), the pointwise Kähler identity `|∂̄τ|²_σ + tr(A Ā) = |A|²_σ`, the
polarized flat Morrey--Kohn--Hörmander identity with one compactly supported factor, and
`KahlerLoweringStatement` (`kahlerLoweringStatement`).
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

/-! ### Euclidean notation -/

section Euclidean

variable {n : ℕ}

/-- `|∂f(v)|² = (Df(v)² + Df(iv)²)/4` for a real function `f`: the Hermitian form
`i ∂f ∧ ∂̄f` evaluated on `v` (the normalization of TN's `leviForm_comp`). -/
def holDerivSq (f : ComplexModel n → ℝ) (z v : ComplexModel n) : ℝ :=
  (fderiv ℝ f z v ^ 2 + fderiv ℝ f z (Complex.I • v) ^ 2) / 4

/-- The twisted curvature `H(v) = a Levi(p)(v) - Levi(a)(v) - |∂a(v)|²/b` of the local weight `p`
for the twist functions `a, b` (FPT `lem:twisted-kahler-line-estimate`). -/
def twistedCurvature (a b p : ComplexModel n → ℝ) (z v : ComplexModel n) : ℝ :=
  a z * leviForm p z v - leviForm a z v - holDerivSq a z v / b z

/-- The pairing `⟨∂̄f(z), v⟩ = ∑_j conj(v_j) ∂f/∂z̄_j(z)` of the `(0,1)`-form `∂̄f` with a vector. -/
def dbarPairing (f : ComplexModel n → ℂ) (z v : ComplexModel n) : ℂ :=
  ∑ j, conj (v j) * dbarDir (coordVec j) f z

/-- The Kähler-lowering of a vector field by a potential `r`: `(r^♭ W)_k = ∑_l r_{l k̄} W_l`,
with `r_{l k̄} = ∂²r/∂z_l ∂z̄_k`. -/
def lowerVector (r : ComplexModel n → ℝ) (W : Fin n → ComplexModel n → ℂ) (k : Fin n)
    (z : ComplexModel n) : ℂ :=
  ∑ l, dbarDir (coordVec k) (dDir (coordVec l) (fun y => (r y : ℂ))) z * W l z

/-- **Kähler lowering** (`claude-twisted-l2:kahler-lowering`).  For a smooth real `r` on an open
`D ⊆ ℂⁿ` and a smooth vector field `W`, the `(0,2)`-form `∂̄(r^♭ W)` has the coefficients
`∂_{j̄}(r^♭W)_k - ∂_{k̄}(r^♭W)_j = ∑_l (r_{l k̄} ∂_{j̄}W_l - r_{l j̄} ∂_{k̄}W_l)`: the terms with
derivatives of `r_{l k̄}` cancel because `∂_{j̄} r_{l k̄} = ∂_{k̄} r_{l j̄}` (`dσ = 0` for `σ = ddᶜr`). -/
def KahlerLoweringStatement (n : ℕ) : Prop :=
  ∀ D : Set (ComplexModel n), IsOpen D → ∀ r : ComplexModel n → ℝ, ContDiffOn ℝ ∞ r D →
  ∀ W : Fin n → ComplexModel n → ℂ, (∀ l, ContDiffOn ℝ ∞ (W l) D) →
  ∀ z ∈ D, ∀ j k : Fin n,
    dbarDir (coordVec j) (lowerVector r W k) z - dbarDir (coordVec k) (lowerVector r W j) z =
      ∑ l, (dbarDir (coordVec k) (dDir (coordVec l) (fun y => (r y : ℂ))) z *
          dbarDir (coordVec j) (W l) z -
        dbarDir (coordVec j) (dDir (coordVec l) (fun y => (r y : ℂ))) z *
          dbarDir (coordVec k) (W l) z)

/-- A first order system `P w = ∑_j (A_j ∂_j w + A'_j ∂_{j̄} w) + B w` with matrix coefficients,
applied to `w = (w_i)_{i < N}`; component `i'` of the result. -/
def firstOrderApply {N N' : ℕ} (A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ)
    (B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ) (w : Fin N → ComplexModel n → ℂ)
    (i' : Fin N') (z : ComplexModel n) : ℂ :=
  ∑ j, ∑ i, (A j z i' i * dDir (coordVec j) (w i) z + A' j z i' i * dbarDir (coordVec j) (w i) z) +
    ∑ i, B z i' i * w i z

/-- The formal adjoint `P† h = ∑_j (-∂_{j̄}(A_j^* h) - ∂_j(A'_j^* h)) + B^* h` (flat `L²`). -/
def firstOrderAdjointApply {N N' : ℕ} (A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ)
    (B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ) (h : Fin N' → ComplexModel n → ℂ)
    (i : Fin N) (z : ComplexModel n) : ℂ :=
  ∑ j, ∑ i', (-dbarDir (coordVec j) (fun y => conj (A j y i' i) * h i' y) z -
      dDir (coordVec j) (fun y => conj (A' j y i' i) * h i' y) z) +
    ∑ i', conj (B z i' i) * h i' z

/-- **Friedrichs' lemma** (`claude-twisted-l2:friedrichs`; Hörmander, *An introduction to complex
analysis in several variables*, Lemma 4.1.3 for a general first order system).  On an open
`D ⊆ ℂⁿ`, let `P` have coefficients smooth on `D`, let `w ∈ L²` be supported in a compact
`K ⊆ D` and `P w = f ∈ L²` weakly in `D`.  Then there are smooth `w_k` compactly supported in `D`
with `w_k → w` in `L²(ℂⁿ)` and `P w_k → f` in `L²(D)` (`f` is only determined on `D`). -/
def FriedrichsStatement (n N N' : ℕ) : Prop :=
  ∀ D : Set (ComplexModel n), IsOpen D →
  ∀ (A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ)
    (B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ),
    (∀ j i' i, ContDiffOn ℝ ∞ (fun z => A j z i' i) D) →
    (∀ j i' i, ContDiffOn ℝ ∞ (fun z => A' j z i' i) D) →
    (∀ i' i, ContDiffOn ℝ ∞ (fun z => B z i' i) D) →
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
  ∀ (w : Fin N → ComplexModel n → ℂ) (f : Fin N' → ComplexModel n → ℂ),
    (∀ i, MemLp (w i) 2 volume) → (∀ i, ∀ z ∉ K, w i z = 0) → (∀ i', MemLp (f i') 2 volume) →
    (∀ h : Fin N' → ComplexModel n → ℂ, (∀ i', IsTestFunctionOn D (h i')) →
      ∑ i', ∫ z, f i' z * conj (h i' z) =
        ∑ i, ∫ z, w i z * conj (firstOrderAdjointApply A A' B h i z)) →
  ∃ ws : ℕ → Fin N → ComplexModel n → ℂ,
    (∀ k i, IsTestFunctionOn D (ws k i)) ∧
    (∀ i, Tendsto (fun k => eLpNorm (fun z => ws k i z - w i z) 2 volume) atTop (𝓝 0)) ∧
    ∀ i', Tendsto (fun k => eLpNorm (fun z => firstOrderApply A A' B (ws k) i' z - f i' z) 2
      (volume.restrict D)) atTop (𝓝 0)

end Euclidean

/-! ### Manifold notation -/

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

section Manifold

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The coefficient of a section `G` of `L` in the frame `e` (the second component of the
trivialization). -/
def frameCoeff (e : AtlasFrame L) (G : (x : X) → L.Fiber x) (x : X) : ℂ :=
  (e.val ⟨x, G x⟩).2

/-- The coefficient of `G` in the chart `c` and the frame `e`, as a function on the chart target. -/
def chartCoeff (c : ComplexChart n X) (e : AtlasFrame L) (G : (x : X) → L.Fiber x)
    (z : ComplexModel n) : ℂ :=
  frameCoeff L e G (c.val.symm z)

/-- `|e(x)|²_h`, the squared norm of the frame vector. -/
def frameNormSq (e : AtlasFrame L) (x : X) : ℝ :=
  ‖e.val.symm x 1‖ ^ 2

/-- The chart points over the base set of the frame. -/
def chartFrameDomain (c : ComplexChart n X) (e : AtlasFrame L) : Set (ComplexModel n) :=
  c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet

/-- `G` is smooth on `U`: its coefficients are smooth in all charts and frames. -/
def IsSmoothSectionOn (G : (x : X) → L.Fiber x) (U : Set X) : Prop :=
  ∀ (c : ComplexChart n X) (e : AtlasFrame L),
    ContDiffOn ℝ ∞ (chartCoeff L c e G) (chartFrameDomain L c e ∩ c.val.symm ⁻¹' U)

/-- The full local weight `p = -log |e|²_h + φ - log ρ` in the chart `c` and the frame `e`, for the
density `ρ` of the volume in the chart. -/
def localWeight (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ) (φ : X → ℝ)
    (z : ComplexModel n) : ℝ :=
  -Real.log (frameNormSq L e (c.val.symm z)) + φ (c.val.symm z) - Real.log (ρ z)

end Manifold

section Volume

variable [MeasurableSpace X] [BorelSpace X]

/-- `ρ` is the density of `μ` in the chart `c`. -/
def IsChartDensity (μ : Measure X) (c : ComplexChart n X) (ρ : ComplexModel n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ ρ c.val.target ∧ (∀ z ∈ c.val.target, 0 < ρ z) ∧
    Measure.map c.val (μ.restrict c.val.source) =
      (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z))

end Volume

/-- The quadratic form `v ↦ ω(v, iv)` of a Kähler form in a chart. -/
def kahlerQuad (omega : KahlerBackground n X) (c : ComplexChart n X) (z v : ComplexModel n) : ℝ :=
  omega.form.val.coeff c z ![v, Complex.I • v]

/-- The quadratic form of `σ = ω + ddᶜ r` in a chart: `ω(v, iv) + Levi(r)(v)/π`
(`smoothDDC u z ![v, i v] = leviForm u z v / π`, TN `smoothDDC_complexDiagonal_eq_leviForm`). -/
def modifiedKahlerQuad (omega : KahlerBackground n X) (r : X → ℝ) (c : ComplexChart n X)
    (z v : ComplexModel n) : ℝ :=
  kahlerQuad omega c z v + leviForm (fun y => r (c.val.symm y)) z v / Real.pi

/-- `σ = ω + ddᶜ r` is a Kähler form on the open set `U`: `r` is smooth on `U` and `σ` is
positive definite there (it is closed, being `ω + ddᶜ r`). -/
def IsKahlerModificationOn (omega : KahlerBackground n X) (r : X → ℝ) (U : Set X) : Prop :=
  SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) r U ∧
    ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, c.val.symm z ∈ U → ∀ v : ComplexModel n,
      v ≠ 0 → 0 < modifiedKahlerQuad omega r c z v

/-- **Completeness of `σ = ω + ddᶜ r` on `U`** in the form used by the `L²` method (FPT
`lem:cutoff-mollifier-density`): smooth cut-offs `χ_k`, compactly supported in `U`, with values in
`[0,1]`, converging to `1` on `U`, and `|dχ_k|_σ ≤ C/(k+1)`. -/
def HasCompleteCutoffs (omega : KahlerBackground n X) (r : X → ℝ) (U : Set X) : Prop :=
  ∃ (χ : ℕ → X → ℝ) (C : ℝ), (∀ k, ChartSmooth (n := n) (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
    (∀ k, tsupport (χ k) ⊆ U) ∧ (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧
    (∀ x ∈ U, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
    ∀ (k : ℕ) (c : ComplexChart n X), ∀ z ∈ c.val.target, c.val.symm z ∈ U →
      ∀ v : ComplexModel n,
        fderiv ℝ (fun y => χ k (c.val.symm y)) z v ^ 2 ≤
          (C / ((k : ℝ) + 1)) ^ 2 * modifiedKahlerQuad omega r c z v

/-- The pole set `A = {ψ = -∞}` lies locally in the zero set of a holomorphic function which does
not vanish identically on any open set (so `A` is contained in a nowhere dense analytic set). -/
def IsLocallyAnalyticNull (A : Set X) : Prop :=
  ∀ x : X, ∃ (c : ComplexChart n X) (W : Set (ComplexModel n)) (g : ComplexModel n → ℂ),
    x ∈ c.val.source ∧ IsOpen W ∧ c.val x ∈ W ∧ W ⊆ c.val.target ∧ DifferentiableOn ℂ g W ∧
    (∀ W' ⊆ W, IsOpen W' → W'.Nonempty → ∃ z ∈ W', g z ≠ 0) ∧
    ∀ z ∈ W, c.val.symm z ∈ A → g z = 0

/-- An admissible singular weight: quasi-psh, never `+∞`, with a closed pole set
`A = {ψ = -∞}` locally contained in a nowhere dense analytic set, and smooth on `X \ A`.  This is
the class of FPT `lem:analytic-complement-cutoffs` (sums of potentials with gentle analytic
singularities and of logarithmic poles along submanifolds). -/
def IsAdmissibleSingularWeight (ψ : X → EReal) : Prop :=
  ManifoldQuasiPlurisubharmonic (n := n) ψ ∧ (∀ x, ψ x ≠ ⊤) ∧ IsClosed {x | ψ x = ⊥} ∧
    IsLocallyAnalyticNull (n := n) {x | ψ x = ⊥} ∧
    SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) (fun x => (ψ x).toReal) {x | ψ x ≠ ⊥}

variable (n X) [MeasurableSpace X] [BorelSpace X]

/-- **The global twisted `L²` estimate** (`claude-twisted-l2:main`; Xia, *Foundations of
pluripotential theory*, q07, `lem:twisted-kahler-line-estimate`, for `∂̄`-exact data; the twisted
Bochner--Kodaira--Nakano method of Ohsawa--Takegoshi, Demailly, *Analytic methods in algebraic
geometry*, §12).

`X` is a complex manifold with a Kähler form `ω`, `U ⊆ X` open, and `σ = ω + ddᶜr` a Kähler form on
`U` which is complete in the sense of `HasCompleteCutoffs`.  `μ` is a smooth positive volume,
`L` a Hermitian holomorphic line bundle with smooth metric `h`, `φ` a smooth weight on `U` and
`a, b` smooth twist functions on `U`, bounded above and below by positive constants.  Suppose the
twisted curvature `H` of the local weights `p = -log |e|²_h + φ - log ρ` is positive definite on
`U`.  Let `G` be a smooth section on `U` such that `|⟨∂̄G, ξ⟩|²_h ≤ D · H(ξ)` and
`|⟨∂̄G, ξ⟩|²_h ≤ D_σ · σ(ξ)` on `U`, with `∫_U D_σ e^{-φ} dμ < ∞` (the datum is in `L²(σ)`).
Then there is a section `S`, holomorphic on `U`, with

`∫_U |G - S|²_h e^{-φ} / (a + b) dμ ≤ ∫_U D e^{-φ} dμ`. -/
def TwistedL2CorrectionStatement : Prop :=
  ∀ (omega : KahlerBackground n X) (U : Set X), IsOpen U →
  ∀ r : X → ℝ, IsKahlerModificationOn omega r U → HasCompleteCutoffs omega r U →
  ∀ μ : Measure X, IsSmoothPositiveVolume (n := n) μ →
  ∀ L : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric L →
  ∀ φ a b : X → ℝ, SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) φ U →
    SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) a U →
    SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) b U →
    (∃ m M : ℝ, 0 < m ∧ ∀ x ∈ U, m ≤ a x ∧ a x ≤ M ∧ m ≤ b x ∧ b x ≤ M) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U → ∀ v : ComplexModel n, v ≠ 0 →
        0 < twistedCurvature (fun y => a (c.val.symm y)) (fun y => b (c.val.symm y))
          (localWeight L c e ρ φ) z v) →
  ∀ G : (x : X) → L.Fiber x, IsSmoothSectionOn L G U →
  ∀ D Dσ : X → ℝ,
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          D (c.val.symm z) * twistedCurvature (fun y => a (c.val.symm y))
            (fun y => b (c.val.symm y)) (localWeight L c e ρ φ) z v) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L),
      ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          Dσ (c.val.symm z) * modifiedKahlerQuad omega r c z v) →
    ∫⁻ x in U, ENNReal.ofReal (Dσ x * Real.exp (-φ x)) ∂μ < ⊤ →
  ∃ S : (x : X) → L.Fiber x, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S U ∧
    ∫⁻ x in U, ENNReal.ofReal (‖G x - S x‖ ^ 2 * Real.exp (-φ x) / (a x + b x)) ∂μ ≤
      ∫⁻ x in U, ENNReal.ofReal (D x * Real.exp (-φ x)) ∂μ

/-- **The twisted `L²` estimate on a compact Kähler manifold with an admissible singular weight**
(`claude-twisted-l2:compact`; FPT `lem:twisted-kahler-line-estimate` applied on
`M = X \ {ψ = -∞}` with the metric of `lem:analytic-complement-cutoffs`, followed by
`lem:l2-holomorphic-analytic-removal`; this is the form used in Steps 1--4 of the proof of FPT
`thm:compact-submanifold-extension`, hence for the book's `thm:OT_ext`).

`X` compact Kähler, `μ` a smooth positive volume, `L` with smooth metric `h`, `ψ` an admissible
singular weight with pole set `A`, `a, b > 0` smooth.  If the twisted curvature of
`p = -log |e|²_h + ψ - log ρ` is positive definite on `X \ A`, `G` is a smooth section with
`|⟨∂̄G, ξ⟩|²_h ≤ D · H(ξ)` and `|⟨∂̄G, ξ⟩|²_h ≤ D_ω · ω(ξ)` on `X \ A` and
`∫ D_ω e^{-ψ} dμ < ∞`, then there is `S ∈ H⁰(X, L)` with
`∫_X |G - S|²_h e^{-ψ} / (a + b) dμ ≤ ∫_X D e^{-ψ} dμ`. -/
def CompactTwistedL2CorrectionStatement : Prop :=
  CompactSpace X →
  ∀ (omega : KahlerBackground n X) (μ : Measure X), IsSmoothPositiveVolume (n := n) μ →
  ∀ L : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric L →
  ∀ ψ : X → EReal, IsAdmissibleSingularWeight (n := n) ψ →
  ∀ a b : X → ℝ, ChartSmooth (n := n) a → ChartSmooth (n := n) b → (∀ x, 0 < a x) →
    (∀ x, 0 < b x) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n, v ≠ 0 →
        0 < twistedCurvature (fun y => a (c.val.symm y)) (fun y => b (c.val.symm y))
          (localWeight L c e ρ fun x => (ψ x).toReal) z v) →
  ∀ G : (x : X) → L.Fiber x, IsSmoothSectionOn L G univ →
  ∀ D Domega : X → ℝ,
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          D (c.val.symm z) * twistedCurvature (fun y => a (c.val.symm y))
            (fun y => b (c.val.symm y)) (localWeight L c e ρ fun x => (ψ x).toReal) z v) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L),
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          Domega (c.val.symm z) * kahlerQuad omega c z v) →
    ∫⁻ x, ENNReal.ofReal (Domega x) * multiplierWeight 1 (ψ x) ∂μ < ⊤ →
  ∃ S : (x : X) → L.Fiber x,
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
    ∫⁻ x, ENNReal.ofReal (‖G x - S x‖ ^ 2 / (a x + b x)) * multiplierWeight 1 (ψ x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (D x) * multiplierWeight 1 (ψ x) ∂μ

/-- **The twisted `L²` estimate on a weakly pseudoconvex Kähler manifold**
(`claude-twisted-l2:weakly-pseudoconvex`; Demailly, *Analytic methods*, Theorem 5.1 and §12,
twisted form; input of the Ohsawa--Takegoshi theorem on families over a disc, package E2).

As `CompactTwistedL2CorrectionStatement`, with compactness replaced by a smooth psh exhaustion
`Ψ` (`Levi Ψ ≥ 0`, all sublevel sets `{Ψ ≤ t}` compact), the twist functions bounded above and
below by positive constants, and the `ω`-norm of the datum integrable against `e^{-ψ}` on compact
sets. -/
def WeaklyPseudoconvexTwistedL2CorrectionStatement : Prop :=
  ∀ (omega : KahlerBackground n X) (Ψ : X → ℝ), ChartSmooth (n := n) Ψ →
    (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun y => Ψ (c.val.symm y)) z v) →
    (∀ t : ℝ, IsCompact {x | Ψ x ≤ t}) →
  ∀ μ : Measure X, IsSmoothPositiveVolume (n := n) μ →
  ∀ L : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric L →
  ∀ ψ : X → EReal, IsAdmissibleSingularWeight (n := n) ψ →
  ∀ a b : X → ℝ, ChartSmooth (n := n) a → ChartSmooth (n := n) b →
    (∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ a x ∧ a x ≤ M ∧ m ≤ b x ∧ b x ≤ M) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n, v ≠ 0 →
        0 < twistedCurvature (fun y => a (c.val.symm y)) (fun y => b (c.val.symm y))
          (localWeight L c e ρ fun x => (ψ x).toReal) z v) →
  ∀ G : (x : X) → L.Fiber x, IsSmoothSectionOn L G univ →
  ∀ D Domega : X → ℝ,
    (∀ (c : ComplexChart n X) (e : AtlasFrame L) (ρ : ComplexModel n → ℝ), IsChartDensity μ c ρ →
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          D (c.val.symm z) * twistedCurvature (fun y => a (c.val.symm y))
            (fun y => b (c.val.symm y)) (localWeight L c e ρ fun x => (ψ x).toReal) z v) →
    (∀ (c : ComplexChart n X) (e : AtlasFrame L),
      ∀ z ∈ chartFrameDomain L c e, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          Domega (c.val.symm z) * kahlerQuad omega c z v) →
    (∀ K : Set X, IsCompact K →
      ∫⁻ x in K, ENNReal.ofReal (Domega x) * multiplierWeight 1 (ψ x) ∂μ < ⊤) →
  ∃ S : (x : X) → L.Fiber x,
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
    ∫⁻ x, ENNReal.ofReal (‖G x - S x‖ ^ 2 / (a x + b x)) * multiplierWeight 1 (ψ x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (D x) * multiplierWeight 1 (ψ x) ∂μ

/-- **Complete Kähler metrics on complements of pole sets** (`claude-twisted-l2:complement-cutoffs`;
FPT `lem:analytic-complement-cutoffs`).  On a compact Kähler manifold, for a quasi-psh `ψ` which is
smooth off its closed pole set `A`, there is `r` smooth on `U = X \ A` such that
`σ = ω + ddᶜr ≥ ω/2` on `U` and `σ` has complete cut-offs on `U` (one may take
`r = -log(-ψ + C)` and `χ_k = χ(log(C - ψ)/(k + 1))`). -/
def AnalyticComplementCutoffStatement : Prop :=
  CompactSpace X → ∀ omega : KahlerBackground n X, ∀ ψ : X → EReal,
    ManifoldQuasiPlurisubharmonic (n := n) ψ → (∀ x, ψ x ≠ ⊤) → IsClosed {x | ψ x = ⊥} →
    SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) (fun x => (ψ x).toReal) {x | ψ x ≠ ⊥} →
  ∃ r : X → ℝ, IsKahlerModificationOn omega r {x | ψ x ≠ ⊥} ∧
    (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
      kahlerQuad omega c z v / 2 ≤ modifiedKahlerQuad omega r c z v) ∧
    HasCompleteCutoffs omega r {x | ψ x ≠ ⊥}

/-- **`L²` removable singularities across analytic sets** (`claude-twisted-l2:l2-removable`; FPT
`lem:l2-holomorphic-analytic-removal`).  A section of `L`, holomorphic on `U \ A` for a closed
`A` locally contained in a nowhere dense analytic set, which is locally square integrable near
every compact subset of `U`, agrees on `U \ A` with a section holomorphic on `U`. -/
def L2RemovableSingularityStatement : Prop :=
  ∀ μ : Measure X, IsSmoothPositiveVolume (n := n) μ →
  ∀ L : HermitianHolomorphicLineBundle.{0, 0} n X,
  ∀ U A : Set X, IsOpen U → IsClosed A → IsLocallyAnalyticNull (n := n) A →
  ∀ S : (x : X) → L.Fiber x,
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S (U \ A) →
    (∀ K : Set X, IsCompact K → K ⊆ U → ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ < ⊤) →
  ∃ S' : (x : X) → L.Fiber x,
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S' U ∧ ∀ x ∈ U \ A, S' x = S x

end SGPT.Trace.TwistedL2
