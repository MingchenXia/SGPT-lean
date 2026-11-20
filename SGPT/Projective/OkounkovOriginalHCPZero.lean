import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Projective.OkounkovOriginalLeftUnitMultiplier
import SGPT.Okounkov.PobDimZeroBook

/-! Actual raw original zero-dimensional twisted multiplier polytopes and original own partial body.
Blueprint: okounkov-original-hcp-zero.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 0 f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance hcpZeroTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance hcpZeroCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance hcpZeroManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold 0 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 0

/-- EVERY actual raw degree polytope equals the genuine original own partial body in dimension zero. -/
theorem twistedMultiplierPolytope_eq_partialBody_zeroDimension {L T : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 0 E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ)))) (c : X)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      (∀ k, poly (fun k => AlgebraicValuation.twistedMultiplierValues f 0 E v c k (r k) φ) k =
        ValGen.partialBody f 0 E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) ∧
      Tendsto (fun k : ℕ => Metric.hausdorffDist
        (poly (fun k => AlgebraicValuation.twistedMultiplierValues f 0 E v c k (r k) φ) k)
        (ValGen.partialBody f 0 E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)) atTop (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f 0 E
  have hA := PobDimZero.valuation_okounkovBody_eq_univ f E Y hY a c v
  have hKc : IsCompact (okounkovBody v c a) := by rw [hA]; exact isCompact_univ
  have hKv : Convex ℝ (okounkovBody v c a) := by rw [hA]; exact convex_univ
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  have h1 : ((0:Fin 0 → ℝ),(1:ℝ))∈C.cone :=
    ⟨zero_le_one,0,by rw [hA]; exact mem_univ _,by simp⟩
  have hbody : ValGen.partialBody f 0 E v c a C φ = univ :=
    PobDimZero.valuation_partialBody_eq_univ f E Y hY a c v hφ.quasiPshPotential C h1
  have hpoly (k : ℕ) : poly (fun k => AlgebraicValuation.twistedMultiplierValues f 0 E v c k (r k) φ) k = univ := by
    obtain ⟨σ,hσ⟩ := PobDimZero.exists_section_ne_zero f E Y hY (r k) 1
    let M := bundleTensor T (bundleTensorPower L k)
    let s : Γ(M,⊤) := (bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) σ
    have hσeq : originalSectionUnit s = σ :=
      congr($((bundleTensorLeftUnitIso M).hom_inv_id).val.app (.op ⊤) |>.hom σ)
    have hs : s≠0 := (originalSectionUnit_ne_zero_iff s).mp (hσeq.symm ▸ hσ)
    have hI : k=0 ∨ IsPlainIdealSection f 0 E (multiplierIdeal (n:=0) (k:ℝ) φ) s := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact Or.inl hk
      · refine Or.inr fun U α p hp => ?_
        exact (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt hφ.quasiPshPotential
          (by exact_mod_cast hk) p _).mpr (PobDimZero.holomorphicAt_of_dim_zero f E Y hY _ p)
    have hQ : (AlgebraicValuation.twistedMultiplierValues f 0 E v c k (r k) φ).Nonempty :=
      ⟨_,s,hs,hI,rfl⟩
    exact PobDimZero.eq_univ_of_nonempty_euclidean ((hQ.image _).convexHull)
  refine ⟨hKc,hKv,fun k => (hpoly k).trans hbody.symm,?_⟩
  have hbody' : ValGen.partialBody f 0 E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ = univ := hbody
  simp only [hpoly,hbody',Metric.hausdorffDist_self_zero]
  exact tendsto_const_nhds
end SGPT.Okounkov.OriginalBook
