import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Okounkov.ValGen2Twisted
import SGPT.Okounkov.PobDimZeroCore

/-! ENTIRE prop:Deltaconvtwisted, SAME raw original twisted polytopes, EVERY dimension/twist.
Blueprint: okounkov-original-book-twisted.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
open scoped Topology

/-- Genuine original frame manufactures a SAME ordinary first-power nonzero global section. -/
theorem exists_plainSection_ne_zero_of_subsingleton {X : Scheme.{0}} [IsIntegral X]
    [Subsingleton X] {M : X.Modules} (b : LineBundleAtlas M) :
    ∃ s : bundleSections M ⊤, s ≠ 0 := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨i,hi⟩ := b.covers x
  have htop : (⊤ : X.Opens) ≤ b.opens i := fun y _ => (Subsingleton.elim y x) ▸ hi
  let e := (b.frame i).coefficients (homOfLE htop)
  refine ⟨e.symm 1, fun hz => ?_⟩
  have h1 : e (e.symm 1) = e 0 := congrArg e hz
  rw [LinearEquiv.apply_symm_apply,map_zero] at h1
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x,trivial⟩⟩
  have : IsDomain Γ(X,⊤) := inferInstance
  exact one_ne_zero (α:=Γ(X,⊤)) h1

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance originalBookTwistedTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalBookTwistedCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalBookTwistedManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

include f E in
/-- ALL original rank-zero twisted polytopes are genuinely nonempty and equal SAME whole R0. -/
theorem twistedDegreePolytope_eq_univ_zero [SmoothOfRelativeDimension 0 f]
    {L T : X.Modules} (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ))))
    (c : X) (k : ℕ) (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    AlgebraicValuation.twistedDegreePolytope v c k b = Set.univ := by
  let := schemeAnalyticTNChartedSpace f 0
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
  have := PobDimZero.subsingleton_scheme_of_flag f E Y hY
  apply PobDimZero.eq_univ_of_nonempty_fun
  obtain ⟨s,hs⟩ := exists_plainSection_ne_zero_of_subsingleton b
  exact (Set.Nonempty.image _ (⟨_,s,hs,rfl⟩ :
    (AlgebraicValuation.twistedValues v c k b).Nonempty)).convexHull

variable {L : X.Modules} (a : LineBundleAtlas L) (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
  (hv : Function.Surjective v) (c : X)
include f E hbig hv

/-- Entire source for actual raw polytopes at ANY genuine original nonnegative point. -/
theorem tendsto_hausdorffDist_twistedDegreePolytope_allDimensions
    (hc : IsNonnegAt v c) {T : X.Modules} (aT : LineBundleAtlas T)
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' AlgebraicValuation.twistedDegreePolytope v c k (b k))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' okounkovBody v c a)) atTop (𝓝 0) := by
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  cases n with
  | succ m =>
    obtain ⟨C,hC,hG⟩ := exists_original_admissibleCone_allDimensions f a (m+1) E hbig v hv c
    exact ValGen2.tendsto_hausdorffDist_twistedDegreePolytope f E Y hY a c v hc hC hG aT b
  | zero =>
    have hK := PobDimZero.valuation_okounkovBody_eq_univ f E Y hY a c v
    simp_rw [twistedDegreePolytope_eq_univ_zero f E v c, hK, hausdorffDist_self_zero]
    exact tendsto_const_nhds

/-- Printed canonical-center source, actual nonnegativity/center produced from original projectivity. -/
theorem tendsto_hausdorffDist_centreTwistedDegreePolytope_allDimensions
    {T : X.Modules} (aT : LineBundleAtlas T)
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    haveI := E.isProper
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' centreTwistedDegreePolytope f n E v k (b k))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' centreOkounkovBody f v a)) atTop (𝓝 0) := by
  let := E.isProper
  exact tendsto_hausdorffDist_twistedDegreePolytope_allDimensions f n E a hbig v hv
    (valuationCenter f v) (isNonnegAt_valuationCenter f v) aT b

end SGPT.Okounkov.OriginalBook
