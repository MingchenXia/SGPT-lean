import SGPT.Trace.BertiniUniversalLocalCOV

/-! Genuine original physical residue integral COV, with actual source/inverse
points, SAME original L norm and arbitrary extended X weights retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
attribute [local instance] Classical.propDecidable
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Topology Manifold ContDiff BigOperators TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

abbrev OriginalAmbientPhysicalBundle (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :=
  tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L

def originalMemberResidueSourceDensity (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : ∀ x, (OriginalAmbientPhysicalBundle p L).Fiber x) (w : X → ℝ≥0∞) (z : ComplexModel (N + d)) : ℝ≥0∞ :=
  if hz : z ∈ originalQSourceDomain p c then
    let q := originalQSourcePair p c ⟨z,hz⟩
    ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ •
      c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) * w (c.tangentPoint q)
  else 0

def originalQDividedSourceDensity (m : Fin N) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : ∀ x, (OriginalAmbientPhysicalBundle p L).Fiber x) (w : X → ℝ≥0∞)
    (z : originalQSourceDomain p c) : ℝ≥0∞ :=
  let q := originalQSourcePair p c z
  ENNReal.ofReal (‖(parameterCoefficient p c.i c.j m (c.tangentPoint q))⁻¹ •
    c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) * w (c.tangentPoint q)

def originalLocalQTargetDensity (m : Fin N) {z₀ : ComplexModel (N + d)}
    (Θ : LocalHolomorphicEquivAt (n := N + d) z₀) (hsrc : Θ.source ⊆ originalQSourceDomain p c)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : ∀ x, (OriginalAmbientPhysicalBundle p L).Fiber x) (w : X → ℝ≥0∞) (y : ComplexModel (N + d)) : ℝ≥0∞ :=
  if hy : y ∈ Θ.target then
    originalQDividedSourceDensity p c m L T w ⟨Θ.invFun y,hsrc (Θ.mapsTo_invFun hy)⟩
  else 0

theorem exists_originalPhysicalResidue_local_COV (m : Fin N)
    (q₀ : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hm : parameterCoefficient p c.i c.j m (c.tangentPoint q₀) ≠ 0) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := N + d) (prodModelEquiv N d (q₀.1.val,q₀.2.val)))
      (hsrc : Θ.source ⊆ originalQSourceDomain p c),
      Θ.toFun = originalQCoordinateMap p c m ∧
      (∀ z ∈ Θ.source, parameterCoefficient p c.i c.j m (originalQSourceX p c z) ≠ 0) ∧
      ∀ (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
        (T : ∀ x, (OriginalAmbientPhysicalBundle p L).Fiber x) (w : X → ℝ≥0∞),
      (∫⁻ z in Θ.source, originalMemberResidueSourceDensity p c L T w z) =
        ∫⁻ y in Θ.target, originalLocalQTargetDensity p c m Θ hsrc L T w y := by
  obtain ⟨Θ,hsrc,hfun,hcoeff,hcov⟩ := exists_originalQCoordinate_local_COV p c m q₀ hm
  refine ⟨Θ,hsrc,hfun,hcoeff,?_⟩
  intro L T w
  let g := originalLocalQTargetDensity p c m Θ hsrc L T w
  have hc := hcov g
  calc
    _ = ∫⁻ z in Θ.source,
        ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| *
          g (originalQCoordinateMap p c m z) := by
      apply setLIntegral_congr_fun Θ.isOpen_source.measurableSet
      intro z hz
      let q := originalQSourcePair p c ⟨z,hsrc hz⟩
      have hpoint : prodModelEquiv N d (q.1.val,q.2.val) = z := (prodModelEquiv N d).apply_symm_apply z
      have htarget : originalQCoordinateMap p c m z ∈ Θ.target := by
        rw [← hfun]
        exact Θ.mapsTo_toFun hz
      have hinv : Θ.invFun (originalQCoordinateMap p c m z) = z := by
        rw [← hfun]
        exact Θ.left_inv z hz
      have hpair : (⟨Θ.invFun (originalQCoordinateMap p c m z),
          hsrc (Θ.mapsTo_invFun htarget)⟩ : originalQSourceDomain p c) = ⟨z,hsrc hz⟩ := Subtype.ext hinv
      have hg : g (originalQCoordinateMap p c m z) = originalQDividedSourceDensity p c m L T w ⟨z,hsrc hz⟩ := by
        dsimp only [g,originalLocalQTargetDensity]
        rw [dif_pos htarget,hpair]
      have hphys := originalPhysicalResidueDensity_qJacobian p c m q L (T (c.tangentPoint q))
        (hcoeff z hz) (w (c.tangentPoint q))
      rw [hpoint] at hphys
      have hSource : originalMemberResidueSourceDensity p c L T w z =
          ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ •
            c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) * w (c.tangentPoint q) :=
        dif_pos (hsrc hz)
      exact hSource.trans (hphys.trans (congrArg
        (fun a : ℝ≥0∞ => ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| * a) hg.symm))
    _ = _ := hc.symm

end SGPT.Trace.BertiniUniversal
