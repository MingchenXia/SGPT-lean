import SGPT.GAGA.SmoothFlagsBertini
import SGPT.GAGA.OkoCloseDXMain

/-!
# Smooth flags exist on every integral smooth projective complex scheme; `thm:DXmain1` for all `X`


* `contMDiff_of_isHolomorphicEmbedding`: a holomorphic embedding `M → ℙᴺ` in the sense of lane
  H0-GAGA2 (`SGPT.GAGA.H0S.IsHolomorphicEmbedding`: holomorphic in the affine charts of `ℙᴺ`) is
  holomorphic in mathlib's sense (`ContMDiff`).
* **`smoothFlagsExist`**: the statement `SGPT.GAGA.OkoClose.SmoothFlagsExist`. For
  `X` an integral smooth projective complex scheme of dimension `m + 1` with `X(ℂ) ≠ ∅`, the
  compact (`E.analyticCompact`) connected (`SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral`)
  complex manifold `X(ℂ)` embeds holomorphically and injectively into `ℙᴺ`
  (`SGPT.GAGA.H0S.projectivePoint`), so it carries a smooth flag by
  `SGPT.GAGA.SmoothFlags.exists_isSmoothFlag_of_injective` (Bertini). The flag is analytic
  (closed connected complex submanifolds of `X(ℂ)`), as in `SGPT.Okounkov.IsSmoothFlag`.
* **`dxMain1Statement`**, **`dxMain1UntwistedStatement`**: the projective statements of
  `thm:DXmain1` (every twist `T`, resp. `T = 𝒪_X`) for every integral smooth projective `X`.
* `exists_schemeSmoothFlag_one_eq`: every closed connected complex submanifold of `X(ℂ)` of
  dimension `m` (a smooth prime divisor) is the first member `Y₁` of a smooth flag.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.SmoothFlags

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Okounkov

section Embedding

variable {n N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- A holomorphic embedding into `ℙᴺ` (holomorphic in the affine charts of `ℙᴺ` and the preferred
charts of `M`) is holomorphic in mathlib's sense. -/
theorem contMDiff_of_isHolomorphicEmbedding {Φ : M → ComplexProjectiveSpace N}
    (hΦ : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := n) Φ) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ Φ := by
  intro p
  have hi : Φ p ∈ (affineChart (chartIndex (Φ p))).source := mem_affineChart_chartIndex _
  obtain ⟨S, hSd, hSo, hpS⟩ := _root_.eventually_nhds_iff.mp (hΦ.holomorphic p _ hi)
  have hcd : ContDiffAt ℂ ∞ (SGPT.GAGA.H0S.chartMap Φ p (chartIndex (Φ p)))
      ((complexChartAt (n := n) p).val p) :=
    (contDiffOn_of_differentiableOn_complex (fun z hz => (hSd z hz).differentiableWithinAt)
      hSo).contDiffAt (hSo.mem_nhds hpS)
  rw [contMDiffAt_iff]
  refine ⟨hΦ.continuous.continuousAt, ?_⟩
  have hrange : range (𝓘(ℂ, ComplexModel n) : ComplexModel n → ComplexModel n) = univ := by simp
  rw [hrange, contDiffWithinAt_univ]
  exact hcd

end Embedding

/-- **Existence of smooth flags** (the `SmoothFlagsExist`; source: the smooth flags of
`def:Okounkov:L170`, whose existence the book takes for granted, via Bertini's theorem): every
integral smooth projective complex scheme `X` of dimension `m + 1` with `X(ℂ) ≠ ∅` carries a
smooth flag `X(ℂ) = Y₀ ⊇ Y₁ ⊇ ⋯ ⊇ Y_{m+1}` of closed connected complex submanifolds,
`dim Yᵢ = m + 1 - i`. -/
theorem smoothFlagsExist : SGPT.GAGA.OkoClose.SmoothFlagsExist := by
  intro X f E _ m _ _
  let := schemeAnalyticPointTopology f
  let := schemeAnalyticTNChartedSpace f (m + 1)
  let := E.isSeparated
  let := E.quasiCompact
  have := schemeAnalyticTN_isComplexManifold f (m + 1)
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  exact exists_isSmoothFlag_of_injective (SGPT.GAGA.H0S.projectivePoint f E (m + 1))
    (contMDiff_of_isHolomorphicEmbedding
      (SGPT.GAGA.H0S.isHolomorphicEmbedding_projectivePoint f E (m + 1)))
    (SGPT.GAGA.H0S.injective_projectivePoint f E (m + 1))

/-- **Source `thm:DXmain1`, projective statement, every twist `T`, every `X`**: on every integral
smooth projective complex scheme `X` of dimension `n = m + 1` with `X(ℂ) ≠ ∅`, for all line
bundles `T`, `L` (with atlases), every smooth metric `H` on `L` and every `φ ∈ PSH(X, c₁(L, H))`,
`lim_k n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ` (the limit exists). -/
theorem dxMain1Statement : SGPT.IGood.DXMain.DXMain1Statement :=
  SGPT.GAGA.OkoClose.dxMain1Statement_of_smoothFlagsExist smoothFlagsExist

/-- **Source `thm:DXmain1` with `T = 𝒪_X`, projective statement, every `X`**:
`lim_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ`. -/
theorem dxMain1UntwistedStatement : SGPT.IGood.DXMain.DXMain1UntwistedStatement :=
  SGPT.GAGA.OkoClose.dxMain1UntwistedStatement_of_smoothFlagsExist smoothFlagsExist

section Hypersurface

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance smoothFlagsSchemeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance smoothFlagsSchemeCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)

include E in
/-- **Every smooth connected hypersurface of `X(ℂ)` is the first member of a smooth flag**
(`X` integral smooth projective of dimension `m + 1`; the step "since `X` is projective, we can
always find a flag with `E` being the first component" of the proof of `cor:numin`, for a smooth
prime divisor, i.e. a closed connected complex submanifold `W` of dimension `m`). -/
theorem exists_schemeSmoothFlag_one_eq {W : Set (SchemeComplexPoint f)}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    ∃ Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f), IsSmoothFlag Y ∧ Y 1 = W := by
  let := E.isSeparated
  let := E.quasiCompact
  have := schemeAnalyticTN_isComplexManifold f (m + 1)
  have : Nonempty (SchemeComplexPoint f) := ⟨hW.2.1.nonempty.some⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  obtain ⟨Y, hY, h1⟩ := SGPT.GAGA.SmoothFlags.exists_isSmoothFlag_one_eq
    (SGPT.GAGA.H0S.projectivePoint f E (m + 1))
    (contMDiff_of_isHolomorphicEmbedding
      (SGPT.GAGA.H0S.isHolomorphicEmbedding_projectivePoint f E (m + 1)))
    (SGPT.GAGA.H0S.injective_projectivePoint f E (m + 1)) (by omega) (W := W)
    (by simpa using hW)
  exact ⟨Y, hY, h1⟩

end Hypersurface

end SGPT.GAGA.SmoothFlags
