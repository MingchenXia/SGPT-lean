import SGPT.Projective.OkounkovOriginalRealKahlerConcavity
import SGPT.Projective.OkounkovOriginalPerturbGeometry

/-! Genuine real concavity of the SAME normalized positive rational perturbations.
Blueprint: okounkov-original-perturbed-real-concavity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal

theorem convexComb_positive_nat_smul {M : Type*} (φ ψ : M → EReal) (t : ℝ)
    (q : ℕ) (hq : 0<q) :
    convexComb t (fun x => (q:EReal)*φ x) (fun x => (q:EReal)*ψ x)=
      fun x => (q:EReal)*convexComb t φ ψ x := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hcoe : ((q:ℝ):EReal)=(q:EReal) := by simp
  funext x
  dsimp only [convexComb]
  rw [←hcoe,ValGen2.ereal_coe_mul_add hqR]
  congr 1 <;> ac_rfl

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance perturbedRealConcTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbedRealConcCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance perturbedRealConcManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

theorem original_normalized_positivePerturb_real_concavity {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas A) (K : SchemeLineBundleMetric f (m+1) E A)
    (hK : letI := E.isSeparated;letI := E.quasiCompact;(K.curvature b).val.IsKahler)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val ψ)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) (q p : ℕ) (hq : 0<q) (hp : 0<p) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (okounkovBody v (valuationCenter f v) (OkoNS.perturbAtlas a b q p)))
      (hKv : Convex ℝ (okounkovBody v (valuationCenter f v) (OkoNS.perturbAtlas a b q p))),
      let B := fun ρ => (q:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v (valuationCenter f v)
        (OkoNS.perturbAtlas a b q p) (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (fun x => (q:EReal)*ρ x);
      t•B φ+(1-t)•B ψ⊆B (convexComb t φ ψ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨hφK,_⟩ := original_positivePerturbation_kahler_and_big f (m+1) E a H b K hK hφ q p hq hp
  obtain ⟨hψK,_⟩ := original_positivePerturbation_kahler_and_big f (m+1) E a H b K hK hψ q p hq hp
  obtain ⟨hKc,hKv,hχK,hinc⟩ := original_partialBody_real_concavity_kahler f E
    (OkoNS.perturbAtlas a b q p) (originalPerturbMetric f (m+1) E a H b K q p) v hv hφK hψK ht0 ht1
  rw [convexComb_positive_nat_smul φ ψ t q hq] at hinc
  refine ⟨hKc,hKv,?_⟩
  dsimp only
  rintro z ⟨u,hu,w,hw,rfl⟩
  rcases hu with ⟨u,⟨x,hx,rfl⟩,rfl⟩
  rcases hw with ⟨w,⟨y,hy,rfl⟩,rfl⟩
  refine ⟨t•x+(1-t)•y,hinc ⟨t•x,⟨x,hx,rfl⟩,(1-t)•y,⟨y,hy,rfl⟩,rfl⟩,?_⟩
  simp only [smul_add,smul_comm t (q:ℝ)⁻¹,smul_comm (1-t) (q:ℝ)⁻¹]
end SGPT.Okounkov.OriginalBook
