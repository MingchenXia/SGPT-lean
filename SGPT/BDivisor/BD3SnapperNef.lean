import SGPT.BDivisor.BD3SnapperGeneral
import SGPT.Projective.OriginalRealMixedEuler
import SGPT.Hodge.SourceSmoothMixedCohomology
import SGPT.Hodge.SourceCartierMixedAlgebra
import SGPT.GAGA.OkoCloseDXMain

/-!
# Dang–Favre numbers of nef classes and the book's product (root model)

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Dang–Favre extend the Snapper–Kleiman
numbers of Cartier divisors multilinearly to real classes (in particular to nef classes) of
`N¹(X)_ℝ`; since ample classes span `N¹(X)_ℝ`, the extension is determined by the numbers of ample
line bundles.  Codex's EP-free `originalRealMixedEuler` is the real multilinear extension of the
mixed Euler differences.  Here, EP-free:

* `originalRealMixedEuler_ample_eq_slotIntegral_bd3`: for real combinations `αᵢ = ∑_P vᵢ(P) [P]` of
  ample line bundles, the multilinear extension of the Snapper–Kleiman numbers equals
  `∫_{X(ℂ)} θ₁ ∧ ⋯ ∧ θₙ`, `θᵢ = ∑_P vᵢ(P) c₁(P, K_P)` (any smooth metrics `K_P`): it depends only on
  the classes and agrees with the classical intersection number;
* `nefIntersectionReal_eq_snapperKleiman_bd3`: the book's product (`def:DF_ext`,
  `nefIntersectionReal`) of Weil b-divisors over `X(ℂ)` realized on the root model by `c₁(Lᵢ)`,
  `Lᵢ` ample, is the Snapper–Kleiman number `(L₁ ⋯ Lₙ)` (the mixed version of
  `Kleiman.nefIntersectionReal_eq_selfIntersection` of lane BD2);
* `nefIntersectionReal_eq_originalRealMixedEuler_bd3`: the book's product of b-divisors realized on
  the root model by NEF real classes `∑_P vᵢ(P) c₁(P)` (nef Cartier b-divisors determined on `X`) is
  Dang–Favre's multilinearly extended Snapper–Kleiman number.
* `originalRealMixedEuler_eq_slotIntegral_bd3`, `nefIntersectionReal_eq_originalRealMixedEuler_general_bd3`:
  the same for real combinations of ARBITRARY line bundles (all real Cartier classes of the
  algebraic `N¹(X)_ℝ`), using Snapper's theorem `BD3SnapperGeneral`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped BigOperators

/-- Two real multilinear maps on finitely supported real combinations agree as soon as they agree
on all tuples of single generators. -/
theorem multilinearMap_finsupp_ext_bd3 {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (M₁ M₂ : MultilinearMap ℝ (fun _ : ι => α →₀ ℝ) ℝ)
    (h : ∀ (a : ι → α) (r : ι → ℝ), M₁ (fun i => Finsupp.single (a i) (r i)) =
      M₂ (fun i => Finsupp.single (a i) (r i)))
    (v : ι → α →₀ ℝ) : M₁ v = M₂ v := by
  classical
  have hv : v = fun i => ∑ a ∈ (v i).support, Finsupp.single a (v i a) := by
    funext i
    exact (Finsupp.sum_single (v i)).symm
  rw [hv, MultilinearMap.map_sum_finset, MultilinearMap.map_sum_finset]
  exact Finset.sum_congr rfl fun a _ => h a (fun i => v i (a i))

local instance bd3NefTopology {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd3NefCharts {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd3NefManifold {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

section RealExtension

variable {X : Scheme.{0}} (k : ℕ) (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

/-- **Dang–Favre's real extension of Snapper–Kleiman numbers on ample combinations (EP-free).**
For real combinations `vᵢ` of ample (positively curved) line bundles and ANY smooth metrics `K_P`,
the multilinear extension of the mixed Euler differences equals
`∫ θ₁ ∧ ⋯ ∧ θ_{k+1}` with `θᵢ = ∑_P vᵢ(P) c₁(P, K_P)`. -/
theorem originalRealMixedEuler_ample_eq_slotIntegral_bd3 (B : IntrinsicLineBundle X)
    (K : ∀ P : OriginalPositiveLine f (k + 1) E, SchemeLineBundleMetric f (k + 1) E P.sheaf)
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f))
    (v : Fin (k + 1) → OriginalPositiveLine f (k + 1) E →₀ ℝ) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    originalRealMixedEuler f E (k + 1) B (fun i => (v i).mapDomain (positiveLine_bd3 k f E)) =
      slotIntegral κ (fun i => Finsupp.linearCombination ℝ
        (fun P : OriginalPositiveLine f (k + 1) E => (K P).curvature P.atlas) (v i)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  dsimp only
  let M₁ := (originalRealMixedEuler f E (k + 1) B).compLinearMap
    (fun _ : Fin (k + 1) => Finsupp.lmapDomain ℝ ℝ (positiveLine_bd3 k f E))
  let M₂ := (slotIntegralMultilinear κ).compLinearMap
    (fun _ : Fin (k + 1) => Finsupp.linearCombination ℝ
      (fun P : OriginalPositiveLine f (k + 1) E => (K P).curvature P.atlas))
  have h := multilinearMap_finsupp_ext_bd3 M₁ M₂ ?_ v
  · exact h
  intro P r
  simp only [M₁, M₂, MultilinearMap.compLinearMap_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.linearCombination_single]
  rw [originalRealMixedEuler_single]
  change _ = slotIntegral κ (fun i => r i • (K (P i)).curvature (P i).atlas)
  have hsmul := (slotIntegralMultilinear κ).map_smul_univ r
    (fun i => (K (P i)).curvature (P i).atlas)
  simp only [slotIntegralMultilinear, MultilinearMap.mk'_apply, smul_eq_mul] at hsmul
  rw [hsmul, snapperKleiman_eq_slotIntegral_bd3 k f E P B (fun i => K (P i)) κ]

/-- **Dang–Favre's real extension of Snapper–Kleiman numbers (EP-free), all line bundles.**  For
real combinations `vᵢ` of ARBITRARY line bundles (Cartier classes) and ANY smooth metrics `K_A`,
Codex's real multilinear extension of the mixed Euler differences equals
`∫ θ₀ ∧ ⋯ ∧ θ_k`, `θᵢ = ∑_A vᵢ(A) c₁(A, K_A)`; in particular it only depends on the classes. -/
theorem originalRealMixedEuler_eq_slotIntegral_bd3 (B : IntrinsicLineBundle X)
    (K : ∀ A : IntrinsicLineBundle X, SchemeLineBundleMetric f (k + 1) E A.sheaf)
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f))
    (v : Fin (k + 1) → IntrinsicLineBundle X →₀ ℝ) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    originalRealMixedEuler f E (k + 1) B v =
      slotIntegral κ (fun i => Finsupp.linearCombination ℝ
        (fun A : IntrinsicLineBundle X => (K A).curvature A.atlas) (v i)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  dsimp only
  let M₂ := (slotIntegralMultilinear κ).compLinearMap
    (fun _ : Fin (k + 1) => Finsupp.linearCombination ℝ
      (fun A : IntrinsicLineBundle X => (K A).curvature A.atlas))
  have h := multilinearMap_finsupp_ext_bd3 (originalRealMixedEuler f E (k + 1) B) M₂ ?_ v
  · exact h
  intro A r
  simp only [M₂, MultilinearMap.compLinearMap_apply, Finsupp.linearCombination_single]
  rw [originalRealMixedEuler_single]
  change _ = slotIntegral κ (fun i => r i • (K (A i)).curvature (A i).atlas)
  have hsmul := (slotIntegralMultilinear κ).map_smul_univ r
    (fun i => (K (A i)).curvature (A i).atlas)
  simp only [slotIntegralMultilinear, MultilinearMap.mk'_apply, smul_eq_mul] at hsmul
  have hSK := snapperKleiman_general_eq_slotIntegral_bd3 k f E B κ
    (fun i => ⟨(A i).sheaf, (A i).atlas, K (A i)⟩)
  rw [hsmul]
  exact congrArg (fun t : ℝ => (∏ i, r i) * t) hSK

end RealExtension

section BookProduct

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {k : ℕ} [SmoothOfRelativeDimension (k + 1) f]
  [Nonempty (SchemeComplexPoint f)]

local instance bd3BookMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance bd3BookBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- **Book product = Snapper–Kleiman number for ample bundles (mixed, root model).**  Let `X` be
an integral scheme, smooth projective of dimension `k + 1` over `ℂ`, `L₀, …, L_k` ample
(positively curved) line bundles, `Hᵢ` any smooth metrics, `B` any line bundle, and `Dᵢ` Weil
b-divisors over `X(ℂ)` (book's blow-up models) realized on the root model by `c₁(Lᵢ)`.  Then the
book's product `(D₀, …, D_k)` is the Snapper–Kleiman number `Δ_{L₀} ⋯ Δ_{L_k} χ(B)`. -/
theorem nefIntersectionReal_eq_snapperKleiman_bd3
    (P : Fin (k + 1) → OriginalPositiveLine f (k + 1) E)
    (H : ∀ i, SchemeLineBundleMetric f (k + 1) E (P i).sheaf) (B : IntrinsicLineBundle X) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ D : Fin (k + 1) → WeilFamilyAny (SGPT.BDivisor.ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
      (∀ i, IsRealizationAny (D i) SGPT.BDivisor.ModelSystem.Model.root ((H i).chernClass (P i).atlas)) →
      nefIntersectionReal D =
        (originalMixedEulerDifference f E (List.ofFn (fun i => positiveLine_bd3 k f E (P i))) B : ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro D hD
  let κ : KahlerBackground (k + 1) (SchemeComplexPoint f) := ⟨(P 0).curvature, (P 0).positive⟩
  have hr : ∀ i, IsRealizationAny (D i) SGPT.BDivisor.ModelSystem.Model.root
      (RealBottChern.ofRepresentative ((P i).metric.curvature (P i).atlas)) := by
    intro i
    have hclass : (H i).chernClass (P i).atlas =
        RealBottChern.ofRepresentative ((P i).metric.curvature (P i).atlas) :=
      (H i).chernClass_independent (P i).metric (P i).atlas (P i).atlas
    exact hclass ▸ hD i
  have hnef : ∀ i, NefWithRespectTo κ ((P i).metric.curvature (P i).atlas) := fun i =>
    nefWithRespectTo_of_semipositive κ
      (KahlerBackground.isSemipositive ⟨(P i).metric.curvature (P i).atlas, (P i).positive⟩)
  have hp := nefIntersectionReal_of_common_nef_realization κ D SGPT.BDivisor.ModelSystem.Model.root κ
    (fun i => (P i).metric.curvature (P i).atlas) hr hnef
  rw [hp]
  exact (snapperKleiman_eq_slotIntegral_bd3 k f E P B (fun i => (P i).metric) κ).symm

/-- **Book product = Dang–Favre number for nef classes on the root model.**  If the Weil
b-divisors `Dᵢ` over `X(ℂ)` are realized on the root model by the classes of
`θᵢ = ∑_P vᵢ(P) c₁(P, K_P)` (real combinations of ample line bundles), and these representatives
are nef with respect to some Kähler form, then the book's product `(D₀, …, D_k)` is the real
multilinear extension of the Snapper–Kleiman numbers evaluated at the classes `vᵢ`. -/
theorem nefIntersectionReal_eq_originalRealMixedEuler_bd3
    (K : ∀ P : OriginalPositiveLine f (k + 1) E, SchemeLineBundleMetric f (k + 1) E P.sheaf)
    (B : IntrinsicLineBundle X) (v : Fin (k + 1) → OriginalPositiveLine f (k + 1) E →₀ ℝ) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)),
      (∀ i, NefWithRespectTo κ (Finsupp.linearCombination ℝ
        (fun P : OriginalPositiveLine f (k + 1) E => (K P).curvature P.atlas) (v i))) →
      ∀ D : Fin (k + 1) → WeilFamilyAny (SGPT.BDivisor.ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
        (∀ i, IsRealizationAny (D i) SGPT.BDivisor.ModelSystem.Model.root
          (RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
            (fun P : OriginalPositiveLine f (k + 1) E => (K P).curvature P.atlas) (v i)))) →
        nefIntersectionReal D =
          originalRealMixedEuler f E (k + 1) B (fun i => (v i).mapDomain (positiveLine_bd3 k f E)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro κ hnef D hD
  have hp := nefIntersectionReal_of_common_nef_realization κ D SGPT.BDivisor.ModelSystem.Model.root κ _ hD hnef
  rw [hp]
  exact (originalRealMixedEuler_ample_eq_slotIntegral_bd3 k f E B K κ v).symm

/-- **Book product = Dang–Favre number for nef classes on the root model (all Cartier
classes).**  If the Weil b-divisors `Dᵢ` over `X(ℂ)` are realized on the root model by the classes
of `θᵢ = ∑_A vᵢ(A) c₁(A, K_A)` (real combinations of arbitrary line bundles, i.e. real Cartier
classes of the algebraic `N¹(X)_ℝ`), and these representatives are nef with respect to some
Kähler form, then the book's product is Dang–Favre's multilinearly extended Snapper–Kleiman
number of the classes `vᵢ`. -/
theorem nefIntersectionReal_eq_originalRealMixedEuler_general_bd3
    (K : ∀ A : IntrinsicLineBundle X, SchemeLineBundleMetric f (k + 1) E A.sheaf)
    (B : IntrinsicLineBundle X) (v : Fin (k + 1) → IntrinsicLineBundle X →₀ ℝ) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)),
      (∀ i, NefWithRespectTo κ (Finsupp.linearCombination ℝ
        (fun A : IntrinsicLineBundle X => (K A).curvature A.atlas) (v i))) →
      ∀ D : Fin (k + 1) → WeilFamilyAny (SGPT.BDivisor.ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
        (∀ i, IsRealizationAny (D i) SGPT.BDivisor.ModelSystem.Model.root
          (RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
            (fun A : IntrinsicLineBundle X => (K A).curvature A.atlas) (v i)))) →
        nefIntersectionReal D = originalRealMixedEuler f E (k + 1) B v := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro κ hnef D hD
  have hp := nefIntersectionReal_of_common_nef_realization κ D SGPT.BDivisor.ModelSystem.Model.root κ _ hD hnef
  rw [hp]
  exact (originalRealMixedEuler_eq_slotIntegral_bd3 k f E B K κ v).symm

end BookProduct

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
