import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkChart
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkRegular

/-! Actual function/denominator readback for the internally constructed coefficient map.
Blueprint: prime-nov16-analytic-normalization-graph-stalk-functions.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open HolGerm GermAlgebraicParametrization RegularLocusDense
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
open SGPT.Foundations.Analysis.Pending.HironakaActualWholeStalkHolomorphicPullback
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkFunctions
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationGraphOriginalStalk
open PrimeNov16AnalyticNormalizationGraphStalkCoordinates
open PrimeNov16AnalyticNormalizationGraphStalkChart
open PrimeNov16AnalyticNormalizationGraphStalkRegular

theorem chartTranslatedGerm_open_function {m : ℕ} (V : Opens (ComplexModel m)) (p : V)
    (F : ComplexModel m → ℂ) (hF : HolomorphicAt m F p.val)
    (hFV : HolomorphicAt m (fun z : V => F z.val) p) :
    chartTranslatedGerm p p (mem_chart_source (ComplexModel m) p) (fun z : V => F z.val) hFV =
      chartTranslatedGerm p.val p.val (mem_chart_source (ComplexModel m) p.val) F hF := by
  have h := actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : V → ComplexModel m)) contMDiff_subtype_val p F hF
  rw [HironakaActualOpenIntrinsicHS.actualHolomorphicGermPullback_val] at h
  exact h.symm

theorem native_baseFunction_holomorphicAt {n k : ℕ} (p : ComplexModel (n+k))
    (hp : baseProjection n k p = 0) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ F x) :
    HolomorphicAt (n+k) (fun z => F (baseProjection n k z)) p := by
  have ht : Tendsto (baseProjection n k) (𝓝 p) (𝓝 (0 : ComplexModel n)) := by
    simpa only [hp] using (baseProjection n k).continuous.tendsto p
  filter_upwards [ht.eventually hF] with z hz
  exact (hz.comp z (baseProjection n k).differentiableAt).mdifferentiableAt

theorem baseFunction_holomorphicAt {n k : ℕ} (U : Opens (ComplexModel n))
    (p : wideDomain k U) (hp : baseProjection n k p.val = 0) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ F x) :
    HolomorphicAt (n+k) (fun z : wideDomain k U => F (baseProjection n k z.val)) p :=
  (native_baseFunction_holomorphicAt p.val hp F hF).comp_contMDiff
    (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)

theorem baseFunction_chart_germ {n k : ℕ} (U : Opens (ComplexModel n))
    (p : wideDomain k U) (hp : baseProjection n k p.val = 0) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ F x) :
    chartTranslatedGerm p p (mem_chart_source (ComplexModel (n+k)) p)
      (fun z : wideDomain k U => F (baseProjection n k z.val))
      (baseFunction_holomorphicAt U p hp F hF) = projGerm (n+k) n (HolGerm.mk F hF) := by
  rw [chartTranslatedGerm_open_function (wideDomain k U) p _
    (native_baseFunction_holomorphicAt p.val hp F hF),projGerm_mk]
  simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun v => by
    change F (baseProjection n k (v+p.val)) = F (coordinateProjection (n+k) n v)
    rw [map_add,hp,add_zero,baseProjection_coordinateProjection]

theorem graph_base_function_readback {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) (hp : baseProjection n k p.val.val = 0)
    (F : ComplexModel n → ℂ) (hF : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ F x) :
    graphStalkStructureMap U C H G p (HolGerm.mk F hF) =
      (actualSubspaceInclusion (n := n+k) (graphClosure U C H G)).stalkMap p
        (actualOriginalFunctionGerm p.val
          (fun z : wideDomain k U => F (baseProjection n k z.val))
          (baseFunction_holomorphicAt U p.val hp F hF)) := by
  rw [← graphGermMap_base_square,graphGermMap_eq_intrinsic,
    ← baseFunction_chart_germ U p.val hp F hF]
  exact intrinsicGermMap_original_function _ p _ _

theorem graph_denominator_readback {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (p : graphClosure U C H G)
    (hp : baseProjection n k p.val.val = 0)
    (hH0 : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ H x) :
    graphStalkStructureMap U C H G p (HolGerm.mk H hH0) = denominatorStalk U C H G hH p := by
  rw [graph_base_function_readback U C H G p hp H hH0]
  have he := actualOriginalFunctionGerm_eq_section (⊤ : Opens (wideDomain k U)) p.val (by trivial)
    (ambientDenominatorSection U H hH)
    (fun z : wideDomain k U => H (baseProjection n k z.val))
    (baseFunction_holomorphicAt U p.val hp H hH0)
    (Eventually.of_forall fun z => sectionExtension_apply ⊤ (ambientDenominatorSection U H hH) z (by trivial))
  rw [he]
  exact AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply
    (actualSubspaceInclusion (n := n+k) (graphClosure U C H G)) ⊤ p (by trivial)
      (ambientDenominatorSection U H hH)

theorem graph_denominator_regular {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (p : graphClosure U C H G)
    (hp : baseProjection n k p.val.val = 0)
    (hH0 : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ H x) :
    graphStalkStructureMap U C H G p (HolGerm.mk H hH0) ∈
      nonZeroDivisors ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.stalk p).carrier := by
  rw [mem_nonZeroDivisors_iff_left,graph_denominator_readback U C H G hH p hp hH0]
  exact denominatorStalk_mul_eq_zero U C H G hH p

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkFunctions
