import SGPT.Trace.BertiniUniversalTargetPoint
import SGPT.Trace.BertiniAmbientPhysicalCoefficients

/-! The SAME physical numerator has an actual original-X scalar comparison
with the actual tensor metric, with geometric compact bounds produced. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Topology Manifold ContDiff BigOperators TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)
  (a : X) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (eL : AtlasFrame L) (m : Fin N)

def originalQPhysicalFrameFactor (x : X) : ℝ :=
  ‖parameterCoefficient p c.i c.j m x‖⁻¹ *
    ‖(eP.val ⟨x,nativeBertiniCoordinateSection p c.j x⟩).2‖⁻¹ *
    ‖(EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
      (Matrix.vecCons (EuclideanSpace.single c.m 1) (fun j => EuclideanSpace.single (c.m.succAbove j) 1))‖ *
    frameNorm L.Fiber eL.val x /
    frameNorm (OriginalAmbientPhysicalBundle p L).Fiber
      (tensorAtlasFrame (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) a) eP) eL).val x

theorem originalQPhysical_norm_factor (ha : c.e = complexChartAt (n := d + 1) a)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hP : c.tangentPoint q ∈ eP.val.baseSet) (hL : c.tangentPoint q ∈ eL.val.baseSet)
    (T : HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber) :
    ‖(parameterCoefficient p c.i c.j m (c.tangentPoint q))⁻¹ •
      c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ =
      originalQPhysicalFrameFactor p c a L eP eL m (c.tangentPoint q) * ‖T (c.tangentPoint q)‖ := by
  let eB := tensorAtlasFrame (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) a) eP) eL
  let := eB.property
  have hK : c.tangentPoint q ∈ (nativeCanonicalFrame (n := d + 1) a).val.baseSet := by
    change c.tangentPoint q ∈ (complexChartAt (n := d + 1) a).val.source
    rw [← ha]
    exact (c.tangentPoint_chart_coordinates q).1
  have hB : c.tangentPoint q ∈ eB.val.baseSet := ⟨⟨hK,hP⟩,hL⟩
  have hnorm := norm_eq_coefficient_mul_frameNorm (OriginalAmbientPhysicalBundle p L).Fiber eB.val T hB
  have hpos := frameNorm_pos (OriginalAmbientPhysicalBundle p L).Fiber eB.val hB
  rw [norm_smul,norm_inv,c.originalAmbientLValue_frameNorm a ha q L eP eL hP hL,
    norm_mul,norm_mul,norm_inv,hnorm]
  unfold originalQPhysicalFrameFactor
  change _ = _ / frameNorm (OriginalAmbientPhysicalBundle p L).Fiber eB.val (c.tangentPoint q) *
    (‖sectionCoefficient (OriginalAmbientPhysicalBundle p L).Fiber eB.val T (c.tangentPoint q)‖ *
      frameNorm (OriginalAmbientPhysicalBundle p L).Fiber eB.val (c.tangentPoint q))
  dsimp only [sectionCoefficient,eB]
  dsimp only [eB] at hpos
  field_simp [ne_of_gt hpos]

private def actualPhysicalFrameDomain : Set X :=
  {x | x ∈ c.e.val.source ∧ x ∈ eP.val.baseSet ∧ x ∈ eL.val.baseSet ∧
    p x ∈ (affineChart c.j).source ∧ parameterCoefficient p c.i c.j m x ≠ 0}

theorem originalQPhysicalFrameFactor_continuousOn (ha : c.e = complexChartAt (n := d + 1) a) :
    ContinuousOn (originalQPhysicalFrameFactor p c a L eP eL m)
      (actualPhysicalFrameDomain p c L eP eL m) := by
  intro x hx
  let eB := tensorAtlasFrame (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) a) eP) eL
  let := eP.property
  let := eL.property
  let := eB.property
  have hK : x ∈ (nativeCanonicalFrame (n := d + 1) a).val.baseSet := by
    change x ∈ (complexChartAt (n := d + 1) a).val.source
    rw [← ha]
    exact hx.1
  have hB : x ∈ eB.val.baseSet := ⟨⟨hK,hx.2.1⟩,hx.2.2.1⟩
  let cs : X → ℂ := fun y => (eP.val ⟨y,nativeBertiniCoordinateSection p c.j y⟩).2
  have hcs : ContinuousAt cs x :=
    ((eP.val.contMDiffAt_section_iff hx.2.1).mp ((nativeBertiniCoordinateSection p c.j).contMDiff x)).continuousAt
  have hcsne : cs x ≠ 0 := by
    intro hz
    apply nativeBertiniCoordinateSection_ne_zero p c.j x hx.2.2.2.1
    apply (eP.val.linearEquivAt ℂ x hx.2.1).injective
    exact hz.trans (map_zero _).symm
  have hc : ContinuousAt (parameterCoefficient p c.i c.j m) x := by
    have h : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞
        (parameterCoefficient p c.i c.j m) x :=
      contMDiffAt_of_eventually_mdifferentiableAt
        (holomorphicAt_affineLift_affineChart_comp p p.contMDiff c.j (c.i.succAbove m) hx.2.2.2.1)
    exact h.continuousAt
  have hLnorm := (frameNorm_continuousOn L.Fiber eL.val).continuousAt (eL.val.open_baseSet.mem_nhds hx.2.2.1)
  have hBnorm := (frameNorm_continuousOn (OriginalAmbientPhysicalBundle p L).Fiber eB.val).continuousAt
    (eB.val.open_baseSet.mem_nhds hB)
  have hBpos := frameNorm_pos (OriginalAmbientPhysicalBundle p L).Fiber eB.val hB
  exact (((((hc.norm.inv₀ (norm_ne_zero_iff.mpr hx.2.2.2.2)).mul
    (hcs.norm.inv₀ (norm_ne_zero_iff.mpr hcsne))).mul continuousAt_const).mul hLnorm).div
      hBnorm (ne_of_gt hBpos)).continuousWithinAt

theorem exists_originalQPhysical_density_bound (ha : c.e = complexChartAt (n := d + 1) a)
    {K : Set X} (hK : IsCompact K) (hKD : K ⊆ actualPhysicalFrameDomain p c L eP eL m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : (ball c.ζ₀ c.r) × c.tangentPatch), c.tangentPoint q ∈ K →
      ∀ (T : HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber) (w : ℝ≥0∞),
      ENNReal.ofReal (‖(parameterCoefficient p c.i c.j m (c.tangentPoint q))⁻¹ •
        c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) * w ≤
      ENNReal.ofReal C * (ENNReal.ofReal (‖T (c.tangentPoint q)‖ ^ 2) * w) := by
  have hcont := ((originalQPhysicalFrameFactor_continuousOn p c a L eP eL m ha).mono hKD).pow 2
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro q hq T w
  have hx := hKD hq
  rw [originalQPhysical_norm_factor p c a L eP eL m ha q hx.2.1 hx.2.2.1 T,mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  have hf : ENNReal.ofReal (originalQPhysicalFrameFactor p c a L eP eL m (c.tangentPoint q) ^ 2) ≤
      ENNReal.ofReal (max B 0) := by
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans ((hB _ hq).trans (le_max_left _ _)))
  calc
    _ ≤ (ENNReal.ofReal (max B 0) * ENNReal.ofReal (‖T (c.tangentPoint q)‖ ^ 2)) * w :=
      mul_le_mul' (mul_le_mul' hf le_rfl) le_rfl
    _ = _ := mul_assoc _ _ _

end SGPT.Trace.BertiniUniversal
