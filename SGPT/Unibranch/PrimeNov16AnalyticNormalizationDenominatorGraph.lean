import SGPT.Unibranch.PrimeNov16AnalyticNormalizationSpreading
import SGPT.Unibranch.ComplexSpaceThetaPSHPullbackFinite
import SGPT.Foundations.Analysis.Pending.ClosureDifferenceAnalytic
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Literal denominator equations, actual analytic closure and genuine original
source space/projection. Normality/properness/finite fibres are NOT assumed.
Blueprint: prime-nov16-analytic-normalization-denominator-graph.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Unibranch.SourceReducedComplexSpace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationDenominatorGraph

def baseProjection (n k : ℕ) : ComplexModel (n+k) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel k)).comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)).toContinuousLinearMap

def fibreProjection (n k : ℕ) : ComplexModel (n+k) →L[ℂ] ComplexModel k :=
  (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel k)).comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)).toContinuousLinearMap

def wideDomain {n : ℕ} (k : ℕ) (U : Opens (ComplexModel n)) : Opens (ComplexModel (n+k)) :=
  ⟨baseProjection n k ⁻¹' U,U.isOpen.preimage (baseProjection n k).continuous⟩

def basePoint {n k : ℕ} (U : Opens (ComplexModel n)) (z : wideDomain k U) : U :=
  ⟨baseProjection n k z.val,z.property⟩

def errorVector {n k : ℕ} (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (z : ComplexModel (n+k)) : ComplexModel k :=
  H (baseProjection n k z) • fibreProjection n k z -
    WithLp.toLp 2 (fun i => G i (baseProjection n k z))

def denominatorVector {n k : ℕ} (H : ComplexModel n → ℂ) (z : ComplexModel (n+k)) : ComplexModel 1 :=
  WithLp.toLp 2 (fun _ => H (baseProjection n k z))

def denominatorSet {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ) : Set (wideDomain k U) :=
  {z | basePoint U z ∈ C ∧ errorVector H G z.val = 0}

def badSet {n k : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ) : Set (wideDomain k U) :=
  {z | denominatorVector (k := k) H z.val = 0}

def rationalGraph {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ) : Set (wideDomain k U) :=
  denominatorSet U C H G \ badSet U H

def graphClosure {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ) : Set (wideDomain k U) :=
  closure (rationalGraph U C H G)

theorem mem_denominatorSet {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ) (z : wideDomain k U) :
    z ∈ denominatorSet U C H G ↔ basePoint U z ∈ C ∧
      ∀ i,H (baseProjection n k z.val) * fibreProjection n k z.val i = G i (baseProjection n k z.val) := by
  constructor
  · rintro ⟨hc,he⟩
    refine ⟨hc,fun i => ?_⟩
    have h := congrArg (fun v : ComplexModel k => v i) he
    change H (baseProjection n k z.val) * fibreProjection n k z.val i - G i (baseProjection n k z.val) = 0 at h
    exact sub_eq_zero.mp h
  · rintro ⟨hc,he⟩
    refine ⟨hc,?_⟩
    ext i
    change H (baseProjection n k z.val) * fibreProjection n k z.val i - G i (baseProjection n k z.val) = 0
    exact sub_eq_zero.mpr (he i)

theorem mem_badSet {n k : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ)
    (z : wideDomain k U) : z ∈ badSet U H ↔ H (baseProjection n k z.val) = 0 := by
  constructor
  · intro he
    have h := congrArg (fun v : ComplexModel 1 => v 0) he
    exact h
  · intro he
    change denominatorVector H z.val = 0
    ext i
    exact he

private theorem errorVector_smooth {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    ContDiffOn ℂ ∞ (errorVector H G) (wideDomain k U) := by
  have hm : MapsTo (baseProjection n k) (wideDomain k U) U := fun _ hz => hz
  have hHs := (contDiffOn_of_differentiableOn_complex hH U.isOpen).comp
    (baseProjection n k).contDiff.contDiffOn hm
  have hGs : ContDiffOn ℂ ∞ (fun z : ComplexModel n => WithLp.toLp 2 (fun i => G i z)) U :=
    (contDiffOn_piLp 2).mpr fun i => contDiffOn_of_differentiableOn_complex (hG i) U.isOpen
  exact (hHs.smul (fibreProjection n k).contDiff.contDiffOn).sub
    (hGs.comp (baseProjection n k).contDiff.contDiffOn hm)

private theorem denominatorVector_smooth {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (hH : DifferentiableOn ℂ H U) :
    ContDiffOn ℂ ∞ (denominatorVector (k := k) H) (wideDomain k U) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  exact (contDiffOn_of_differentiableOn_complex hH U.isOpen).comp
    (baseProjection n k).contDiff.contDiffOn (fun _ hz => hz)

/-- Analyticity comes from the actual original carrier and literal equations. -/
theorem denominatorSet_analytic {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    IsComplexAnalyticSubset (n := n+k) (denominatorSet U C H G) := by
  have hp : ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ComplexModel n) ∞ (basePoint (k := k) U) := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (baseProjection n k).contMDiff.comp contMDiff_subtype_val
  have hb := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hp hC
  have he : ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ComplexModel k) ∞
      (fun z : wideDomain k U => errorVector H G z.val) :=
    (errorVector_smooth U H G hH hG).contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hz := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage he
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel k))
  exact hb.inter hz

theorem badSet_analytic {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (hH : DifferentiableOn ℂ H U) :
    IsComplexAnalyticSubset (n := n+k) (badSet (k := k) U H) := by
  have he : ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ComplexModel 1) ∞
      (fun z : wideDomain k U => denominatorVector H z.val) :=
    (denominatorVector_smooth (k := k) U H hH).contMDiffOn.comp_contMDiff
      contMDiff_subtype_val (fun z => z.property)
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage he
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))

/-- The held COMPLETE closure-difference theorem acts on the SAME literal sets. -/
theorem graphClosure_analytic {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    IsComplexAnalyticSubset (n := n+k) (graphClosure U C H G) :=
  ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
    (denominatorSet_analytic U hC H G hH hG) (badSet_analytic U H hH)

theorem graphClosure_subset_denominatorSet {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    graphClosure U C H G ⊆ denominatorSet U C H G :=
  closure_minimal sdiff_subset (denominatorSet_analytic U hC H G hH hG).isClosed

/-- Genuine whole-space equality off H=0, not a supplied graph dictionary. -/
theorem mem_graphClosure_off_badSet {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (z : wideDomain k U) (hz : H (baseProjection n k z.val) ≠ 0) :
    z ∈ graphClosure U C H G ↔ z ∈ rationalGraph U C H G := by
  constructor
  · intro hs
    exact ⟨graphClosure_subset_denominatorSet U hC H G hH hG hs,
      fun he => hz ((mem_badSet U H z).mp he)⟩
  · intro h
    exact subset_closure h

/-- Actual analytic graph carrier with its ORIGINAL full quotient structure sheaf. -/
def sourceSpace {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) : SourceReducedComplexSpace :=
  sourceReducedComplexSpaceModel (wideDomain k U) (graphClosure U C H G)
    (graphClosure_analytic U hC H G hH hG)

/-- Full original sheaf/scalar projection is constructed by the genuine actual
analytic-model morphism; no desired finite/proper/normal map is input. -/
def projection {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    sourceSpace U hC H G hH hG ⟶ sourceReducedComplexSpaceModel U C hC :=
  analyticModelMorphism (graphClosure_analytic U hC H G hH hG) hC (baseProjection n k)
    (baseProjection n k).contDiff.contDiffOn (fun _ hz => hz)
    (fun c => (graphClosure_subset_denominatorSet U hC H G hH hG c.property).1)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationDenominatorGraph
