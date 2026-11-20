import SGPT.Bergman.SiuNativeSectionCartier
import SGPT.Bergman.SiuNSFinitePotential

/-! The actual physical log norm of a native section manufactures the
original divisor metric, with exactly the original native Chern curvature. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0,0} n X) (hL : IsSourceSmoothHermitianMetric L)
  (s : HolomorphicSections (n := n) L.Fiber)

/-- Exact physical logarithm in every genuine original frame, including
zero section coefficients and their genuine extended-real poles. -/
theorem nativeSectionLog_frame_eq (e : AtlasFrame L) {p : X} (hp : p ∈ e.val.baseSet) :
    sourceSectionLogNormSq L s p =
      generatorLog (fun _ : Fin 1 => sectionCoefficient L.Fiber e.val s) p +
        (Real.log (‖e.val.symm p 1‖ ^ 2) : EReal) := by
  let := e.property
  have hn : 0 < ‖e.val.symm p 1‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L e hp))
  rw [generatorLog_eq_log_sum, Fin.sum_univ_one]
  dsimp only [sourceSectionLogNormSq, logNormSq]
  rw [norm_eq_coefficient_mul_frameNorm L.Fiber e.val s hp, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos (show 0 < frameNorm L.Fiber e.val p ^ 2 from hn)]
  rfl

/-- The smooth native log frame norm gives the exact original curvature. -/
theorem nativeSection_frame_curvature (e : AtlasFrame L) (c : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ c.val.target) (he : c.val.symm z ∈ e.val.baseSet) :
    (sourceNativeFirstChernForm L hL).val.coeff c z =
      -smoothDDC (fun w => Real.log (‖e.val.symm (c.val.symm w) 1‖ ^ 2)) z := by
  apply (sourceNativeFirstChernForm_isOwn L hL c e z hz he).trans
  exact smoothDDC_neg (c.val.isOpen_inter_preimage_symm e.val.open_baseSet)
    ((hL c e).log (fun w hw =>
      (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L e hw.2))).ne')) ⟨hz, he⟩

/-- Actual section values manufacture a metered effective divisor whose
curvature is literally the original physical native Chern form. -/
def nativeSectionDivisorMetric
    (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0) :
    MeteredEffectiveQDivisor n X where
  weight := sourceSectionLogNormSq L s
  curvature := sourceNativeFirstChernForm L hL
  local_presentation p := by
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber p, inferInstance⟩
    refine ⟨e.val.baseSet, e.val.open_baseSet, mem_baseSet_trivializationAt ℂ L.Fiber p,
      1, fun _ => 1, fun _ => sectionCoefficient L.Fiber e.val s,
      fun y => Real.log (‖e.val.symm y 1‖ ^ 2), fun _ => zero_le_one, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ y hy
      exact (nativeSectionCoefficient_holomorphicAt L s e hy).self_of_nhds.mdifferentiableWithinAt
    · intro _ U hU hUe hUne
      obtain ⟨y, hy, hsy⟩ := hdense U hU hUne
      refine ⟨y, hy, ?_⟩
      intro h0
      change sectionCoefficient L.Fiber e.val s y = 0 at h0
      have hn := norm_eq_coefficient_mul_frameNorm L.Fiber e.val s (hUe hy)
      rw [h0, norm_zero, zero_mul] at hn
      exact hsy (norm_eq_zero.mp hn)
    · intro c
      exact (hL c e).log (fun z hz =>
        (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L e hz.2))).ne')
    · intro y hy
      simpa only [Fin.sum_univ_one, Rat.cast_one, EReal.coe_one, one_mul] using nativeSectionLog_frame_eq L s e hy
    · intro c z hz he
      exact nativeSection_frame_curvature L hL e c hz he

/-- The manufactured physical section metric is a metric on its actual
original whole Cartier ideal, rather than merely on its zero support. -/
theorem nativeSectionDivisorMetric_isDivisorMetric
    (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0) :
    DivisorMetric.IsDivisorMetric (nativeSectionCartierDivisor L s hdense)
      (nativeSectionDivisorMetric L hL s hdense) := by
  intro p
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber p, inferInstance⟩
  refine ⟨e.val.baseSet, e.val.open_baseSet, mem_baseSet_trivializationAt ℂ L.Fiber p,
    sectionCoefficient L.Fiber e.val s, ?_, ?_, fun y => Real.log (‖e.val.symm y 1‖ ^ 2), ?_, ?_⟩
  · intro y hy
    exact (nativeSectionCoefficient_holomorphicAt L s e hy).self_of_nhds.mdifferentiableWithinAt
  · intro y hy g
    exact nativeSectionIdeal_frame L s e hy g
  · intro c
    exact (hL c e).log (fun z hz =>
      (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L e hz.2))).ne')
  · intro y hy
    exact nativeSectionLog_frame_eq L s e hy

/-- An actual dense-nonzero native section produces the original native
Chern class in the existing NS_R span using its actual Cartier divisor. -/
theorem nativeSection_chern_mem_neronSeveri
    (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0) :
    RealBottChern.ofRepresentative (sourceNativeFirstChernForm L hL) ∈ DFAlg.neronSeveri n X :=
  DFAlg.curvature_mem_neronSeveri
    (D := nativeSectionCartierDivisor L s hdense)
    (E := nativeSectionDivisorMetric L hL s hdense)
    (nativeSectionDivisorMetric_isDivisorMetric L hL s hdense)

end SGPT.BDivisor.NSKodaira
