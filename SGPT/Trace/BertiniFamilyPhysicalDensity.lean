import SGPT.Trace.BertiniFamilyMatchedVolume
import SGPT.Trace.TwistedL2Statement

/-! Actual physical L coordinate values and matched norm/weight cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle (d + 1) X)

def familyPhysicalCoordinateEquiv :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source), (familyNativePhysicalModel p i a v U hsm L).Fiber q ≃ₗ[ℂ] L.Fiber q.val.2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  exact (TensorProduct.congr (familyCanonicalCoordinateEquiv p i a v U hsm e q hq)
    (LinearEquiv.refl ℂ (L.Fiber q.val.2))).trans (TensorProduct.lid ℂ (L.Fiber q.val.2))

theorem familyPhysicalCoordinateEquiv_tmul :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (α : (familyNativeCanonicalModel p i a v U hsm).Fiber q)
      (l : L.Fiber q.val.2), familyPhysicalCoordinateEquiv p i a v U hsm L e q hq (α ⊗ₜ[ℂ] l) =
        familyCanonicalCoordinateValue p i a v U hsm e q hq α • l := by
  intros
  rfl

theorem familyPhysicalCoordinateEquiv_symm :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (l : L.Fiber q.val.2),
      (familyPhysicalCoordinateEquiv p i a v U hsm L e q hq).symm l =
        familyCoordinateCanonicalUnit p i a v U hsm e q hq ⊗ₜ[ℂ] l := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq l
  apply (familyPhysicalCoordinateEquiv p i a v U hsm L e q hq).injective
  rw [LinearEquiv.apply_symm_apply, familyPhysicalCoordinateEquiv_tmul,
    familyCoordinateCanonicalUnit_value, one_smul]

theorem familyPhysicalCoordinate_norm_density :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (s : (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      ‖s‖ ^ 2 * familyMatchedChartDensity p i a v U hsm e q hq =
        ‖familyPhysicalCoordinateEquiv p i a v U hsm L e q hq s‖ ^ 2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq s
  let E := familyPhysicalCoordinateEquiv p i a v U hsm L e q hq
  let u := familyCoordinateCanonicalUnit p i a v U hsm e q hq
  have hs : s = u ⊗ₜ[ℂ] E s := by
    have h := familyPhysicalCoordinateEquiv_symm p i a v U hsm L e q hq (E s)
    rw [E.symm_apply_apply] at h
    exact h
  have hu : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (familyCoordinateCanonicalUnit_ne_zero p i a v U hsm e q hq))
  change ‖s‖ ^ 2 * (‖u‖ ^ 2)⁻¹ = ‖E s‖ ^ 2
  calc
    ‖s‖ ^ 2 * (‖u‖ ^ 2)⁻¹ = (‖u‖ ^ 2 * ‖E s‖ ^ 2) * (‖u‖ ^ 2)⁻¹ := by
      congr 1
      calc
        ‖s‖ ^ 2 = ‖u ⊗ₜ[ℂ] E s‖ ^ 2 := congrArg (fun t => ‖t‖ ^ 2) hs
        _ = _ := by rw [TensorProduct.norm_tmul, mul_pow]
    _ = ‖E s‖ ^ 2 := by rw [mul_right_comm, mul_inv_cancel₀ hu, one_mul]

theorem familyPhysical_localWeight :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (x₀ : X)
      (eP : AtlasFrame (nativeBertiniHyperplaneBundle p))
      (g : AtlasFrame (nativeHolomorphicPullbackBundle L (familyNativeXMap p i a v U hsm)))
      (φ : familyIncidence p i a v U → ℝ) (z : ComplexModel (d + 1))
      (_hz : z ∈ e.val.target)
      (_hx : (e.val.symm z).val.2 ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (_hP : (e.val.symm z).val.2 ∈ eP.val.baseSet) (_hg : e.val.symm z ∈ g.val.baseSet),
      SGPT.Trace.TwistedL2.localWeight (familyNativePhysicalModel p i a v U hsm L) e
        (tensorAtlasFrame (familyCanonicalModelFrame p i a v U hsm x₀ eP) g)
        (familyMatchedCoordinateDensity p i a v U hsm e) φ z =
      -Real.log (‖g.val.symm (e.val.symm z) 1‖ ^ 2) + φ (e.val.symm z) -
        Real.log (‖familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP (e.val.symm z)‖ ^ 2) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e x₀ eP g φ z hz hx hP hg
  let q := e.val.symm z
  let f := familyCanonicalModelFrame p i a v U hsm x₀ eP
  have hf : q ∈ f.val.baseSet := ⟨hx, hP⟩
  have hfn : ‖f.val.symm q 1‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (SGPT.Bergman.NativeHermitianMetric.sourceAtlasFrame_ne_zero _ f hf))
  have hgn : ‖g.val.symm q 1‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (SGPT.Bergman.NativeHermitianMetric.sourceAtlasFrame_ne_zero _ g hg))
  have hkn : ‖familyModelCanonicalFrameCoefficient p i a v U hsm e x₀ eP q‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr
      (familyModelCanonicalFrameCoefficient_ne_zero p i a v U hsm e x₀ eP q (e.val.map_target hz) hx hP))
  unfold SGPT.Trace.TwistedL2.localWeight SGPT.Trace.TwistedL2.frameNormSq
  rw [tensorAtlasFrame_norm_one f g ⟨hf, hg⟩, mul_pow]
  unfold familyMatchedCoordinateDensity
  rw [dif_pos hz, familyMatchedChartDensity_in_frame p i a v U hsm e x₀ eP q _ hx hP,
    Real.log_mul hfn hgn, Real.log_div hkn hfn]
  ring

end SGPT.Trace.BertiniFamilyCanonical
