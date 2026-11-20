import SGPT.BDivisor.BD7OriginalMixedIntersection
import SGPT.BDivisor.BD7CanonicalApproximation

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Filter MeasureTheory Set SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses CanonicalCurrentFrame
open SGPT.BDivisor.DFAlg SGPT.BDivisor.DangFavre
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
open SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Manifold ContDiff Topology

local instance originalDFTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance originalDFCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d

local instance originalDFManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

variable {Z : Scheme.{0}} {f : Z ⟶ Spec (.of ℂ)} {m : ℕ}
    [IsIntegral Z] [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)] (E : ClosedProjectiveEmbedding f)

local notation "M" => SmoothAlgebraicModel f (m + 1)
local notation "N" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "Book" => BookBlowupModel (f := f) (d := m + 1)
local notation "AlgebraicWeil" => compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
    (smoothModelOriginalCyclePushforward E)
local notation "Read" => canonicalOriginalNumericalWeilEquiv E

/-- The original numerical order tests the closed effective cone at every
smooth projective algebraic model. -/
def OriginalEffectiveLE (a b : AlgebraicWeil) : Prop :=
  ∀ A, b.val A - a.val A ∈
    @closure _ (euclideanTopology (N A)) (finiteEffectiveCone (smoothModelOriginalPrimeNumerical A))

/-- Dang--Favre's ordinary scalar is the infimum of the mixed algebraic top
degrees of all original nef Cartier majorants. -/
def originalDangFavreTopDegree (D : Fin (m + 1) → AlgebraicWeil) : ℝ :=
  sInf {x : ℝ | ∃ C : Fin (m + 1) → AlgebraicWeil,
    (∀ i, IsOriginalNefCartier E (C i)) ∧ (∀ i, OriginalEffectiveLE E (D i) (C i)) ∧
      IsOriginalMixedTopDegree E C x}

/-- The genuine algebraic inverse-limit Chern comparison preserves and reflects
weak convergence for every filter. -/
theorem canonicalOriginalNumericalWeilEquiv_tendsto {J : Type*}
    (C : J → AlgebraicWeil) (D : AlgebraicWeil) (l : Filter J) :
    (∀ A, Tendsto (fun j => (C j).val A) l (@nhds _ (euclideanTopology (N A)) (D.val A))) ↔
      ConvergesAny l (fun j => (Read (C j)).val) (Read D).val := by
  exact originalNumericalAlgebraicWeilEquiv_tendsto E
    (fun π : Book => chooseBookModelAlgebraization E π) (smoothModelOriginalCyclePushforward E)
    (fun {A B} h => smoothModelOriginalCyclePushforward_eq_transport E (A := A) (B := B) h) C D l

/-- Ordinary mixed top degrees along any decreasing net of original nef Cartier
classes with weak numerical limits converge to the book's scalar. -/
theorem tendsto_originalMixedTopDegree_of_decreasing
    {J : Type*} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (C : Fin (m + 1) → J → AlgebraicWeil) (D : Fin (m + 1) → AlgebraicWeil)
    (hC : ∀ i j, IsOriginalNefCartier E (C i j))
    (hdec : ∀ i j k, j ≤ k → OriginalEffectiveLE E (C i k) (C i j))
    (hconv : ∀ i A, Tendsto (fun j => (C i j).val A) atTop
      (@nhds _ (euclideanTopology (N A)) ((D i).val A)))
    (s : J → ℝ) (hs : ∀ j, IsOriginalMixedTopDegree E (fun i => C i j) (s j)) :
    Tendsto s atTop (𝓝 (nefIntersection (fun i => (Read (D i)).val)).toReal) := by
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  letI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let κ := schemeProjectiveTNKahlerBackground f (m + 1) E
  let U (i : Fin (m + 1)) (j : J) := (Read (C i j)).val
  have hU (i : Fin (m + 1)) (j : J) : IsAlgNefCartierAny (U i j) :=
    (originalNefCartier_iff_book E (C i j)).mp (hC i j)
  have hdec' (i : Fin (m + 1)) (j k : J) (hjk : j ≤ k) : LEAny (U i k) (U i j) :=
    canonicalOriginalNumericalWeilEquiv_le_of_majorant E (bookModelKahlerForOriginalComparison E)
      (C i k) (C i j) (hdec i j k hjk)
  have hconv' (i : Fin (m + 1)) : ConvergesAny atTop (U i) (Read (D i)).val :=
    (canonicalOriginalNumericalWeilEquiv_tendsto E (C i) (D i) atTop).mp (hconv i)
  have r (j : J) : CommonNefRealization (fun i => U i j) := Classical.choice
    (nonempty_commonNefRealization κ _ (fun i => (hU i j).isNefCartierAny))
  have hlim := (tendsto_intersection_of_antitone_alg κ U
    (fun i => (Read (D i)).val) hU hdec' hconv' r).2
  exact hlim.congr' (Eventually.of_forall fun j =>
    (IsOriginalMixedTopDegree.unique E (hs j)
      (isOriginalMixedTopDegree_of_realization E (fun i => C i j) (r j))).symm)

/-- There is a common sequence of ordinary nef Cartier majorants that decreases in
the original effective numerical order and converges at every model. -/
theorem exists_originalDecreasingNefCartierApproximation
    (D : Fin (m + 1) → AlgebraicWeil) (hD : ∀ i, IsOriginalNefWeil E (D i)) :
    ∃ (C : Fin (m + 1) → ℕ → AlgebraicWeil) (s : ℕ → ℝ),
      (∀ i j, IsOriginalNefCartier E (C i j)) ∧
      (∀ i j k, j ≤ k → OriginalEffectiveLE E (C i k) (C i j)) ∧
      (∀ i j, OriginalEffectiveLE E (D i) (C i j)) ∧
      (∀ i A, Tendsto (fun j => (C i j).val A) atTop
        (@nhds _ (euclideanTopology (N A)) ((D i).val A))) ∧
      (∀ j, IsOriginalMixedTopDegree E (fun i => C i j) (s j)) := by
  classical
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  letI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  letI := E.locallyOfFiniteType
  obtain ⟨D₀, H, hmetric, hH⟩ := exists_metered_hyperplane_isKahler f m E
  have hnef (i : Fin (m + 1)) : IsAlgNefAny (Read (D i)).val :=
    (originalNefWeil_iff_book E (D i)).mp (hD i)
  choose F hF hFD hFconv using fun i => exists_effectively_antitone_algNefCartier_seq_pos
    H hmetric hH (Read (D i)).val (hnef i).isNefAny (hnef i).1.sourceRootClass_mem
  choose C _hread hC hdec hconv hdom using fun i => exists_canonicalInverseLimit_approximation E
    (D i) (fun j => (hF i j).1) (hFD i) (hFconv i)
  let κ := schemeProjectiveTNKahlerBackground f (m + 1) E
  let r (j : ℕ) : CommonNefRealization (fun i => (Read (C i j)).val) := Classical.choice
    (nonempty_commonNefRealization κ _ (fun i => (hC i j).isNefCartierAny))
  exact ⟨C, fun j => (r j).intersection, fun i j => (originalNefCartier_iff_book E (C i j)).mpr (hC i j),
    hdec, hdom, hconv, fun j => isOriginalMixedTopDegree_of_realization E (fun i => C i j) (r j)⟩

/-- **SGPT Remark at line 749, positive dimension.** Under the modelwise Chern
equivalence from the genuine smooth projective numerical inverse limit, the
book's top nef intersection equals Dang--Favre's ordinary top degree. -/
theorem originalDangFavreTopDegree_eq_book
    (D : Fin (m + 1) → AlgebraicWeil) (hD : ∀ i, IsOriginalNefWeil E (D i)) :
    originalDangFavreTopDegree E D = (nefIntersection (fun i => (Read (D i)).val)).toReal := by
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  letI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let κ := schemeProjectiveTNKahlerBackground f (m + 1) E
  let S := {x : ℝ | ∃ C : Fin (m + 1) → AlgebraicWeil,
    (∀ i, IsOriginalNefCartier E (C i)) ∧ (∀ i, OriginalEffectiveLE E (D i) (C i)) ∧
      IsOriginalMixedTopDegree E C x}
  have hlow : ∀ x ∈ S, (nefIntersection (fun i => (Read (D i)).val)).toReal ≤ x := by
    rintro x ⟨C, hC, hDC, hx⟩
    rw [hx.eq_book E hC]
    exact ENNReal.toReal_mono (nefIntersection_lt_top _).ne
      (source_nefIntersection_mono κ (fun i => (Read (D i)).val) (fun i => (Read (C i)).val)
        (fun i => ((originalNefWeil_iff_book E (D i)).mp (hD i)).isNefAny)
        (fun i => isNefAny_of_isNefCartierAny
          ((originalNefCartier_iff_book E (C i)).mp (hC i)).isNefCartierAny)
        (fun i => canonicalOriginalNumericalWeilEquiv_le_of_majorant E
          (bookModelKahlerForOriginalComparison E) (D i) (C i) (hDC i)))
  obtain ⟨C, s, hC, hdec, hdom, hconv, hs⟩ := exists_originalDecreasingNefCartierApproximation E D hD
  have hlim := tendsto_originalMixedTopDegree_of_decreasing E C D hC hdec hconv s hs
  have hmem (j : ℕ) : s j ∈ S := ⟨fun i => C i j, fun i => hC i j, fun i => hdom i j, hs j⟩
  have hglb : IsGLB S (nefIntersection (fun i => (Read (D i)).val)).toReal :=
    ⟨hlow, fun _ hb => ge_of_tendsto hlim (Eventually.of_forall fun j => hb (hmem j))⟩
  exact hglb.csInf_eq ⟨_, hmem 0⟩

end SGPT.BDivisor.BD7
