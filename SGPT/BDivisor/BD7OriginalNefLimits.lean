import SGPT.BDivisor.BD7CartierDetermination
import SGPT.BDivisor.BD7IntegralNumericalKleimanUnconditional
import SGPT.BDivisor.BD7NefPullback
import SGPT.BDivisor.BD7Models
import SGPT.BDivisor.BD7AlgebraicHyperplaneMeter
import SGPT.BDivisor.BDDangFavreCartier

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Filter SGPT.Okounkov SGPT.Okounkov.OF13
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses CanonicalCurrentFrame
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
open SGPT.BDivisor.DFAlg
open scoped Manifold ContDiff Topology

local instance originalNefTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance originalNefCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d

local instance originalNefManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

variable {Z : Scheme.{0}} {f : Z ⟶ Spec (.of ℂ)} {m : ℕ}
    [IsIntegral Z] [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)

local notation "M" => SmoothAlgebraicModel f (m + 1)
local notation "N" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "Book" => BookBlowupModel (f := f) (d := m + 1)
local notation "Chosen" => fun π : Book => chooseBookModelAlgebraization E π
local notation "AlgebraicWeil" => compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
    (smoothModelOriginalCyclePushforward E)
local notation "Read" => canonicalOriginalNumericalWeilEquiv E

/-- Nefness of a numerical class is tested by degrees on all original integral curves. -/
def smoothModelOriginalNef (A : M) (v : N A) : Prop :=
  v ∈ originalIntegralDegreeNefCone_bd7 (A.p ≫ f) A.embedding

private theorem originalNefClass_readback (A : M) (v : N A) :
    letI := A.embedding.isSeparated
    letI := A.embedding.quasiCompact
    letI := A.embedding.analyticCompact
    letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
    originalIntegralQuotientChern_bd7 (A.p ≫ f) A.embedding (m + 1)
      normalizationProjectiveForCurves_bd7 v =
        (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m
          normalizationProjectiveForCurves_bd7 v).val := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  obtain ⟨u, rfl⟩ := (originalIntegralCurveDegreeRelations_bd7 (A.p ≫ f) A.embedding).mkQ_surjective v
  rw [originalIntegralQuotientChern_mkQ_bd7, numericalChern_mkQ]

/-- Ordinary pullback preserves algebraic nefness, as seen by the modelwise
comparison of the all-curve degree cone with the analytic nef cone. -/
theorem smoothModelOriginalNef_pullback {A B : M} (h : A ≤ B) {v : N A}
    (hv : smoothModelOriginalNef A v) :
    smoothModelOriginalNef B (smoothModelNumericalCartierPullback h v) := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  let κA := schemeProjectiveTNKahlerBackground (A.p ≫ f) (m + 1) A.embedding
  let κB := schemeProjectiveTNKahlerBackground (B.p ≫ f) (m + 1) B.embedding
  have hA := (originalIntegralDegreeNefCone_iff_nativeClassNef_bd7 _ A.embedding m κA v).mp hv
  apply (originalIntegralDegreeNefCone_iff_nativeClassNef_bd7 _ B.embedding m κB _).mpr
  rw [originalNefClass_readback A v] at hA
  rw [originalNefClass_readback B]
  simp only [smoothModelNumericalCartierPullback, numericalChern_numericalCartierPullback]
  exact classNefWithRespectTo_pullback_bd7
    (SmoothAlgebraicModel.homOfLE_point_contMDiff h) κB κA _ hA

/-- The numerical Chern comparison on a chosen original model preserves the
nef cone for every Kähler background on the corresponding book model. -/
theorem bookModelNumericalChern_nef_iff (π : Book) (v : N ((Chosen) π).A)
    (κ : KahlerBackground (m + 1) π.1.carrier) :
    smoothModelOriginalNef ((Chosen) π).A v ↔
      ClassNefWithRespectTo κ (bookModelNumericalChern Chosen π v).val := by
  let P := (Chosen) π
  let A := P.A
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI : CompactSpace (SchemeComplexPoint (A.p ≫ f)) := P.e.symm.toHomeomorph.compactSpace
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  let κA := schemeProjectiveTNKahlerBackground (A.p ≫ f) (m + 1) A.embedding
  let α := (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m
    normalizationProjectiveForCurves_bd7 v).val
  have hbook : (bookModelNumericalChern Chosen π v).val = classPullback P.e.symm.contMDiff α := by
    change classPushforward P.e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m) α = _
    have h := classPushforward_classPullback (isAnalyticModification_of_diffeomorph P.e)
      (Nat.succ_pos m) (classPullback P.e.symm.contMDiff α)
    rw [classPullback_symm_classPullback P.e.symm α] at h
    exact h
  rw [hbook]
  have hnef : smoothModelOriginalNef A v ↔ ClassNefWithRespectTo κA α := by
    simpa only [α, smoothModelOriginalNef, originalNefClass_readback A v] using
      originalIntegralDegreeNefCone_iff_nativeClassNef_bd7 _ A.embedding m κA v
  constructor
  · intro hv
    exact classNefWithRespectTo_pullback_bd7 P.e.symm.contMDiff κ κA α (hnef.mp hv)
  · intro hv
    apply hnef.mpr
    have h := classNefWithRespectTo_pullback_bd7 P.e.contMDiff κA κ _ hv
    rwa [classPullback_symm_classPullback P.e.symm α] at h

/-- The Cartier family has a genuine determining scheme model with a class
of nonnegative degree on all integral curves. -/
def IsOriginalNefCartier (D : AlgebraicWeil) : Prop :=
  ∃ A : M, ∃ v : N A, IsOriginalNumericallyDeterminedOn D A v ∧ smoothModelOriginalNef A v

/-- A nef numerical Weil family is a weak limit of genuine nef Cartier families. -/
def IsOriginalNefWeil (D : AlgebraicWeil) : Prop :=
  ∃ (ι : Type 1) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (C : ι → AlgebraicWeil), (∀ i, IsOriginalNefCartier E (C i)) ∧
      ∀ A, Tendsto (fun i => (C i).val A) atTop (@nhds _ (euclideanTopology (N A)) (D.val A))

/-- An algebraic Kähler class on the original base supplies a Kähler background
on each smooth tower in the book. -/
def bookModelKahlerForOriginalComparison (π : Book) : KahlerBackground (m + 1) π.1.carrier := by
  refine Classical.choice ?_
  letI := E.locallyOfFiniteType
  obtain ⟨D, H, hmetric, hH⟩ := exists_metered_hyperplane_isKahler f m E
  have hp := NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mpr
    ⟨H.curvature, hH, curvature_mem_neronSeveri (D := D) hmetric⟩
  obtain ⟨θ, hθ, _⟩ := NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp
    (blowup_model_isProjective hp π)
  exact ⟨⟨θ, hθ⟩⟩

/-- Algebraic nef Cartier families match the book's nef Cartier realizations. -/
theorem originalNefCartier_iff_book (D : AlgebraicWeil) :
    IsOriginalNefCartier E D ↔ IsAlgNefCartierAny (Read D).val := by
  constructor
  · rintro ⟨A, v, hD, hv⟩
    obtain ⟨π, h⟩ := bookModelAlgebraization_cofinal E Chosen A
    let w := smoothModelNumericalCartierPullback h v
    let c := bookModelNumericalChern Chosen π w
    exact ⟨π, c.val, c.property, canonicalBookRealization_of_originalDetermination E D π w
      (IsOriginalNumericallyDeterminedOn.of_le E hD h), bookModelKahlerForOriginalComparison E π,
      (bookModelNumericalChern_nef_iff E π w (bookModelKahlerForOriginalComparison E π)).mp
        (smoothModelOriginalNef_pullback h hv)⟩
  · rintro ⟨π, c, hc, hD, κ, hn⟩
    let v := (bookModelNumericalChern Chosen π).symm ⟨c, hc⟩
    have hcv : bookModelNumericalChern Chosen π v = ⟨c, hc⟩ :=
      (bookModelNumericalChern Chosen π).apply_symm_apply ⟨c, hc⟩
    refine ⟨((Chosen) π).A, v, canonicalOriginalDetermination_of_bookRealization E D π v ?_,
      (bookModelNumericalChern_nef_iff E π v κ).mpr ?_⟩
    · rwa [hcv]
    · rwa [hcv]

/-- The same actual weak convergence identifies the algebraic and analytic nef
Weil cones on the whole smooth algebraic model system. -/
theorem originalNefWeil_iff_book (D : AlgebraicWeil) :
    IsOriginalNefWeil E D ↔ IsAlgNefAny (Read D).val := by
  let comparison := fun ⦃A B : M⦄ (h : A ≤ B) => smoothModelOriginalCyclePushforward_eq_transport E h
  constructor
  · rintro ⟨ι, h₁, h₂, h₃, C, hC, hc⟩
    exact ⟨(Read D).property, ι, h₁, h₂, h₃, fun i => (Read (C i)).val,
      fun i => (originalNefCartier_iff_book E (C i)).mp (hC i),
      (originalNumericalAlgebraicWeilEquiv_tendsto E Chosen
        (smoothModelOriginalCyclePushforward E) comparison C D atTop).mp hc⟩
  · rintro ⟨_, ι, h₁, h₂, h₃, C, hC, hc⟩
    have hAlgebraic (i : ι) : IsAlgebraicAny (C i) := (hC i).isAlgebraicAny
    let C' (i : ι) : AlgebraicWeil := (Read).symm ⟨C i, hAlgebraic i⟩
    have hread (i : ι) : Read (C' i) = ⟨C i, hAlgebraic i⟩ :=
      (Read).apply_symm_apply _
    refine ⟨ι, h₁, h₂, h₃, C', fun i => (originalNefCartier_iff_book E (C' i)).mpr ?_, ?_⟩
    · rw [hread]; exact hC i
    · apply (originalNumericalAlgebraicWeilEquiv_tendsto E Chosen
        (smoothModelOriginalCyclePushforward E) comparison C' D atTop).mpr
      change ConvergesAny atTop (fun i => (Read (C' i)).val) (Read D).val
      convert hc using 1
      funext i
      exact congrArg Subtype.val (hread i)

end SGPT.BDivisor.BD7
