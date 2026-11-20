import SGPT.Projective.NativeRegularSectionMultiplicity
import SGPT.Projective.NativeSubmanifoldArea
import SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent

/-! SAME original native member tangent, scalar normal and actual divisor
density. Blueprint: `native-regular-member-conormal.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open DivisorRegularLocus DivisorIntegrationCurrent

variable {m N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (s : Fin (N + 1) → HolomorphicSections (n := m + 1) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
  (hl : IsSmoothHypersurfaceMember (m + 1)
    (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- Every normal and derivative here belongs to the SAME original physical
section and actual native member. The only point hypotheses are domain
membership in genuine chart, frame and regular-presentation opens. -/
theorem native_member_conormal_density :
    let p := sourceNativeFiniteSectionProjectiveMap L s hgen
    let hp := sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen
    let W := member p l
    let hW := fun x (hx : x ∈ W) => regularAtDim_member p hp hl hx
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hW
    ∀ (e : ComplexChart m W) (c : ComplexChart (m + 1) X) (E : AtlasFrame L)
      (x₀ : ComplexModel (m + 1))
      (P : RegularPresentation
        (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm) x₀)
      (_hPm : P.m = 1) (z : ComplexModel m)
      (_hz : z ∈ coordinateDomain (Subtype.val : W → X) e c)
      (_hE : ((e.val.symm z : W) : X) ∈ E.val.baseSet)
      (_hzP : coordinateMap (Subtype.val : W → X) e c z ∈ P.U),
      Function.Injective (fderiv ℂ (coordinateMap (Subtype.val : W → X) e c) z) ∧
      fderiv ℂ P.h (coordinateMap (Subtype.val : W → X) e c z) ≠ 0 ∧
      (fderiv ℂ P.h (coordinateMap (Subtype.val : W → X) e c z)).comp
        (fderiv ℂ (coordinateMap (Subtype.val : W → X) e c) z) = 0 ∧
      ∀ v w : ComplexModel (m + 1),
        divisorDensity
          (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm)
          v w (coordinateMap (Subtype.val : W → X) e c z) =
            lineForm (fderiv ℂ P.h (coordinateMap (Subtype.val : W → X) e c z)) v w := by
  let p := sourceNativeFiniteSectionProjectiveMap L s hgen
  let hp := sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen
  let W := member p l
  let hW := fun x (hx : x ∈ W) => regularAtDim_member p hp hl hx
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hW
  dsimp only
  intro e c E x₀ P hPm z hz hE hzP
  let G := coordinateMap (Subtype.val : W → X) e c
  let g := sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm
  have hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) hW
  have hGd : DifferentiableAt ℂ G z :=
    (coordinateMap_contDiffAt hι e c hz).differentiableAt (by simp)
  have hGi : Function.Injective (fderiv ℂ G z) := by
    have hi := SubmanifoldKahlerRestriction.injective_fderiv_coordinateMap_val
      (Nat.le_succ m) hW e c z hz
    intro u v huv
    apply hi
    rw [hGd.fderiv_restrictScalars ℝ]
    exact huv
  have hEcont : ContinuousAt (fun ζ => ((e.val.symm ζ : W) : X)) z :=
    (continuous_subtype_val.comp_continuousOn e.val.continuousOn_symm).continuousAt
      (e.val.open_target.mem_nhds hz.1)
  have hgzero : ∀ᶠ ζ in 𝓝 z, ζ ∈ coordinateDomain (Subtype.val : W → X) e c ∧
      g (G ζ) = 0 ∧ G ζ ∈ P.U := by
    filter_upwards [(coordinateDomain_isOpen hι e c).mem_nhds hz,
      hEcont.preimage_mem_nhds (E.val.open_baseSet.mem_nhds hE),
      hGd.continuousAt.preimage_mem_nhds (P.isOpen.mem_nhds hzP)] with ζ hζ hζE hζP
    refine ⟨hζ, ?_, hζP⟩
    let := E.property
    change sectionCoefficient L.Fiber E.val (linearSection L s l)
      (c.val.symm (c.val ((e.val.symm ζ : W) : X))) = 0
    rw [c.val.left_inv hζ.2]
    change (E.val.linearEquivAt ℂ ((e.val.symm ζ : W) : X) hζE)
      (linearSection L s l ((e.val.symm ζ : W) : X)) = 0
    rw [(linearSection_zero_iff L s hgen l _).mpr (e.val.symm ζ).2, map_zero]
  have hzero : P.h ∘ G =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
    filter_upwards [hgzero] with ζ hζ
    exact (P.g_eq_zero_iff hζ.2.2).mp hζ.2.1
  have hPd := (P.h_diff _ hzP).differentiableAt (P.isOpen.mem_nhds hzP)
  have hker : (fderiv ℂ P.h (G z)).comp (fderiv ℂ G z) = 0 := by
    rw [← fderiv_comp z hPd hGd, hzero.fderiv_eq]
    exact fderiv_const_apply (0 : ℂ)
  have hg0 : g (G z) = 0 := hgzero.self_of_nhds.2.1
  refine ⟨hGi, P.dh_ne _ hzP, hker, fun v w => ?_⟩
  rw [divisorDensity, indicator_of_mem (P.mem_regularLocus_of_mem hzP hg0),
    P.divisorMult_of_mem hzP hg0, hPm, Nat.cast_one, one_mul,
    P.transverseForm_of_mem hzP hg0]

end SGPT.Projective.NumEq.CompleteIntersections
