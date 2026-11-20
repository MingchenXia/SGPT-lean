import SGPT.PSH.CompactPrimeOver
import SGPT.PSH.NativeQPSHPullback
import SGPT.Foundations.Analysis.Pending.UniformLelongBound

/-!
# Uniform bound for generic Lelong numbers along a prime divisor over `X`

Source `prop:Lelongnumberupperbound` (chapter `chapter_pshfunctions.tex`): if `X` is compact,
`θ` is a closed real smooth `(1,1)`-form on `X` and `E` is a prime divisor over `X`, then
`sup {ν(φ, E) : φ ∈ PSH(X, θ)} < ∞`.

The prime divisor over `X` is read through the project's formalization of `def:primdiv`
(`SGPT.PSH.CompactPrimeOver.PrimePresentation`: a proper bimeromorphic morphism `π : Y → X`
from a complex manifold `Y` and a connected closed hypersurface `E ⊆ Y`), and the generic
Lelong number `ν(φ, E) = ν(π^* φ, E)` is the verified reader of `def:pshfunctions:L1112`
(`presentationReader`, and `directReader` on the quotient `DirectPrimeOver` for compact
connected `X`).

The proof does not follow the book's `L¹`-semicontinuity argument.  Instead: `Y` is compact
because `π` is proper, `π^* φ` is `π^* θ`-psh on `Y`, and the Lelong numbers of all
`π^* θ`-psh functions on the compact manifold `Y` are bounded at all points by one constant
(`SGPT.Foundations.Analysis.Pending.UniformLelongBound.hasUniformLelongBound`).  The generic
Lelong number along `E` is at most the Lelong number at any point of `E`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.BookDeep2LelongBound

universe u

open Set
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SquaredLogLelongSourceNormalization

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- A `θ`-psh function (book definition, `def:psh` / `IsThetaPSH` on the native atlas) is
quasi-plurisubharmonic in every chart; this is the regularity used by the reader. -/
theorem manifoldQuasiPlurisubharmonic_of_isThetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ) :
    ManifoldQuasiPlurisubharmonic (n := n) φ :=
  ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1.quasiPlurisubharmonic

/-- **Uniform bound, representative form.**  For compact `X` (not necessarily connected), a
closed real smooth `(1,1)`-form `θ` and a prime divisor `E ⊆ Y` over `X` presented by
`π : Y → X`, there is one real constant bounding `ν(φ, E) = ν(π^* φ, E)` for every
`φ ∈ PSH(X, θ)`. -/
theorem exists_presentationReader_le [CompactSpace X]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (p : PrimePresentation n X) :
    ∃ C : ℝ, ∀ φ : X → EReal, (ofFixedModel n X).IsThetaPSH θ φ →
      presentationReader φ p ≤ ENNReal.ofReal C := by
  have : CompactSpace p.model :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification p.modification
  let θY : ClosedRealOneOneForm n p.model :=
    ClosedRealOneOneForm.pullback p.modification.1 (atlasClosedFormToNative θ)
  obtain ⟨N, hN⟩ := UniformLelongBound.hasUniformLelongBound p.dimension_pos θY
  obtain ⟨y₀, hy₀⟩ : p.divisor.Nonempty := p.smooth.2.1.nonempty
  refine ⟨N, fun φ hφ => ?_⟩
  have hpot : IsThetaPshPotential θY.val (φ ∘ p.projection) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      p.modification (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
  have hn : n ≠ 0 := Nat.ne_of_gt p.dimension_pos
  calc presentationReader φ p
      = ⨅ q ∈ p.divisor, (ofFixedModel n p.model).sourceLelong (φ ∘ p.projection) q := rfl
    _ ≤ (ofFixedModel n p.model).sourceLelong (φ ∘ p.projection) y₀ := iInf₂_le y₀ hy₀
    _ = squaredLogLelongNumber (n := n) (φ ∘ p.projection) y₀ :=
        sourceLelong_ofFixedModel_eq _ _
    _ ≤ 2 * squaredLogLelongNumber (n := n) (φ ∘ p.projection) y₀ := by
        conv_lhs => rw [← one_mul (squaredLogLelongNumber (n := n) (φ ∘ p.projection) y₀)]
        gcongr
        norm_num
    _ = lelongNumber (n := n) (φ ∘ p.projection) y₀ :=
        (lelongNumber_eq_two_mul_squaredLog hn _ _).symm
    _ ≤ ENNReal.ofReal N := hN _ hpot y₀

/-- **Source `prop:Lelongnumberupperbound`, representative form.**  For compact `X`,
`sup {ν(φ, E) : φ ∈ PSH(X, θ)} < ∞` for every prime divisor `E` over `X` (given by any
presentation `π : Y → X`, `E ⊆ Y`). -/
theorem iSup_presentationReader_lt_top [CompactSpace X]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (p : PrimePresentation n X) :
    (⨆ (φ : X → EReal) (_ : (ofFixedModel n X).IsThetaPSH θ φ), presentationReader φ p) < ⊤ := by
  obtain ⟨C, hC⟩ := exists_presentationReader_le θ p
  exact lt_of_le_of_lt (iSup₂_le fun φ hφ => hC φ hφ) ENNReal.ofReal_lt_top

/-- **Source `prop:Lelongnumberupperbound`, on the class `E`.**  For compact connected `X`,
where the prime divisors over `X` form the quotient `DirectPrimeOver n X` and `ν(φ, E)` is
the descended reader `directReader`, the supremum of `ν(φ, E)` over `PSH(X, θ)` is finite. -/
theorem lelongNumber_upper_bound [CompactSpace X] [ConnectedSpace X]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (E : DirectPrimeOver n X) :
    (⨆ (φ : X → EReal) (hφ : (ofFixedModel n X).IsThetaPSH θ φ),
      directReader φ (manifoldQuasiPlurisubharmonic_of_isThetaPSH hφ) E) < ⊤ := by
  induction E using Quot.ind with
  | mk p =>
    obtain ⟨C, hC⟩ := exists_presentationReader_le θ p
    refine lt_of_le_of_lt (iSup₂_le fun φ hφ => ?_) (ENNReal.ofReal_lt_top (r := C))
    exact hC φ hφ

end SGPT.PSH.BookDeep2LelongBound
