import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphProper

/-! ORIGINAL irreducible germ ONLY to a real proper finite analytic graph,
with SAME canonical generators and full representative readback retained.
Not yet a normalization: actual stalk normality and gluing remain open.
Blueprint: prime-nov16-analytic-normalization-local-graph.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric Polynomial TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolGerm
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite
open PrimeNov16AnalyticNormalizationGraphProper

def ballDomain {n : ℕ} (r : ℝ) : Opens (ComplexModel n) := ⟨ball 0 r,isOpen_ball⟩

/-- Genuine original finite equations internally manufacture an analytic
neighbourhood of the SAME ENTIRE original carrier. -/
theorem exists_analytic_ball {n : ℕ} {Z : Set (ComplexModel n)} (hZ : IsAnalyticGerm Z) :
    ∃ r : ℝ,0 < r ∧ IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z} := by
  obtain ⟨m,f,hf,heq⟩ := hZ
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      (∀ j,DifferentiableAt ℂ (f j) z) ∧ (z ∈ Z ↔ ∀ j,f j z = 0) :=
    (eventually_all.mpr hf).and heq
  obtain ⟨r,hrpos,hr⟩ := Metric.eventually_nhds_iff_ball.mp hev
  let F : ComplexModel n → ComplexModel m := fun z => WithLp.toLp 2 (fun j => f j z)
  have hfi : ∀ j,DifferentiableOn ℂ (f j) (ballDomain (n := n) r) :=
    fun j z hz => ((hr z hz).1 j).differentiableWithinAt
  have hF : ContDiffOn ℂ ∞ F (ballDomain (n := n) r) :=
    (contDiffOn_piLp 2).mpr fun j =>
      contDiffOn_of_differentiableOn_complex (hfi j) (ballDomain (n := n) r).isOpen
  have hMap : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞
      (fun z : ballDomain (n := n) r => F z.val) :=
    hF.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hZero := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hMap
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel m))
  refine ⟨r,hrpos,?_⟩
  convert hZero using 1
  ext z
  change z.val ∈ Z ↔ F z.val = 0
  rw [(hr z.val z.property).2]
  constructor
  · intro hfz
    ext j
    exact hfz j
  · intro hFz j
    exact congrArg (fun v : ComplexModel m => v j) hFz

/-- ONLY ORIGINAL irreducible germ plus prescribed neighbourhood. The SAME
canonical normal tuple, actual representatives, analytic carrier, real proper
projection and ALL finite fibres are produced internally. No source graph or
spreading/finite-map/normality certificate is supplied. -/
theorem exists_original_proper_finite_generator_graph {n : ℕ} {Z N : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    let A := HolGerm (ComplexModel n) ⧸ vanishingIdeal Z
    let B := integralClosure A (FractionRing A)
    ∃ (k : ℕ) (s : Fin k → B) (h : A) (g : Fin k → A) (p : Fin k → A[X]),
      h ≠ 0 ∧ Submodule.span A (range s) = ⊤ ∧
      (∀ i,algebraMap A (FractionRing A) (g i) = algebraMap A (FractionRing A) h *
        (s i : FractionRing A) ∧ (p i).Monic ∧ aeval (s i : FractionRing A) (p i) = 0) ∧
      ∃ (H : ComplexModel n → ℂ) (hH : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ H z)
        (G : Fin k → ComplexModel n → ℂ)
        (hG : ∀ i,∀ᶠ z in 𝓝 0,DifferentiableAt ℂ (G i) z)
        (a : Fin k → ℕ → ComplexModel n → ℂ)
        (ha : ∀ i j,∀ᶠ z in 𝓝 0,DifferentiableAt ℂ (a i j) z) (r : ℝ)
        (hHOn : DifferentiableOn ℂ H (ballDomain (n := n) r))
        (hGOn : ∀ i,DifferentiableOn ℂ (G i) (ballDomain (n := n) r))
        (hCarrier : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z}),
        0 < r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
        Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk H hH) = h ∧
        (∀ i,Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk (G i) (hG i)) = g i) ∧
        (∀ i j,Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk (a i j) (ha i j)) = (p i).coeff j) ∧
        (∀ i j,j < (p i).natDegree → DifferentiableOn ℂ (a i j) (ballDomain (n := n) r)) ∧
        (¬ ∀ᶠ z in 𝓝 0,z ∈ Z → H z = 0) ∧
        (∀ z ∈ Z,z ∈ ball 0 r → H z ≠ 0 → ∀ i,
          monicEval (p i).natDegree (a i) z (G i z/H z) = 0) ∧
        IsProperMap (projection (ballDomain (n := n) r) hCarrier H G hHOn hGOn).hom.left.base ∧
        ∀ x : (sourceReducedComplexSpaceModel (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} hCarrier).obj.left,
          ((projection (ballDomain (n := n) r) hCarrier H G hHOn hGOn).hom.left.base ⁻¹' {x}).Finite := by
  obtain ⟨r0,hr0,hCarrier0⟩ := exists_analytic_ball hZ.1
  have hNN : N ∩ ball (0 : ComplexModel n) r0 ∈ 𝓝 0 := Filter.inter_mem hN (ball_mem_nhds 0 hr0)
  obtain ⟨k,s,h,g,p,hh,hs,hp,H,hH,G,hG,a,ha,r,hrpos,hrN,hHclass,hGclass,haclass,
    hHOn,hGOn,haOn,hnonzero,hrel⟩ :=
    PrimeNov16AnalyticNormalizationSpreading.exists_original_normal_generators_spread hZ hNN
  have hU : ballDomain (n := n) r ≤ ballDomain (n := n) r0 := fun z hz => (hrN hz).2
  have hCarrier : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z} :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion hU) hCarrier0
  have hm : ∀ x : {z : ballDomain (n := n) r | z.val ∈ Z},H x.val.val ≠ 0 → ∀ i,
      monicEval (p i).natDegree (a i) x.val.val (G i x.val.val/H x.val.val) = 0 := by
    intro x hx i
    exact hrel x.val.val x.property x.val.property hx i
  refine ⟨k,s,h,g,p,hh,hs,hp,H,hH,G,hG,a,ha,r,hHOn,hGOn,hCarrier,hrpos,
    (fun z hz => (hrN hz).1),hHclass,hGclass,haclass,haOn,hnonzero,hrel,?_,?_⟩
  · exact projection_isProperMap (ballDomain (n := n) r) hCarrier H G hHOn hGOn
      (fun i => (p i).natDegree) a haOn hm
  · intro x
    exact projection_fibres_finite (ballDomain (n := n) r) hCarrier H G hHOn hGOn
      (fun i => (p i).natDegree) a haOn hm x

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationLocalGraph
