import SGPT.Trace.BertiniUniversalResidueCancellation
import Mathlib.MeasureTheory.Function.Jacobian

/-! Actual original local q inverse and ordinary integral COV, produced
before EVERY integrand from true original derivative/nonzero coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Topology Manifold ContDiff BigOperators TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

def originalQSourceDomain : TopologicalSpace.Opens (ComplexModel (N + d)) :=
  ⟨(prodModelEquiv N d).symm ⁻¹' ((ball c.ζ₀ c.r) ×ˢ c.tangentPatch),
    (isOpen_ball.prod c.isOpen_tangentPatch).preimage (prodModelEquiv N d).symm.continuous⟩

def originalQSourcePair (z : originalQSourceDomain p c) : (ball c.ζ₀ c.r) × c.tangentPatch :=
  (⟨((prodModelEquiv N d).symm z.val).1,z.property.1⟩,
    ⟨((prodModelEquiv N d).symm z.val).2,z.property.2⟩)

def originalQSourceX (z : ComplexModel (N + d)) : X :=
  c.point ((prodModelEquiv N d).symm z).1 (c.tangentLift ((prodModelEquiv N d).symm z).2)

theorem differentiableAt_originalQCoordinateMap (m : Fin N) {z : ComplexModel (N + d)}
    (hz : z ∈ originalQSourceDomain p c) : DifferentiableAt ℂ (originalQCoordinateMap p c m) z := by
  let q := originalQSourcePair p c ⟨z,hz⟩
  have hq : prodModelEquiv N d (q.1.val,q.2.val) = z := (prodModelEquiv N d).apply_symm_apply z
  have ht : parameterZeroInsert (c.m.natAdd N) z ∈ c.Φ.target := by
    rw [← hq,originalZeroNormalPoint p c]
    exact c.mapsTo_target q.1.val q.1.property (c.tangentLift q.2.val) q.2.property
  exact (normalSliceMap_hasFDerivAt (d := N + d) (c.m.natAdd N) (m.castAdd (d + 1))
    (differentiableAt_sliceToParameterFlattening p c m ht).hasFDerivAt).differentiableAt

theorem originalQCoordinateMap_complex_det_norm (m : Fin N)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    ‖LinearMap.det (fderiv ℂ (originalQCoordinateMap p c m) (prodModelEquiv N d (q.1.val,q.2.val))).toLinearMap‖ =
      ‖parameterCoefficient p c.i c.j m (c.tangentPoint q) / c.tangentNormalDenominator q‖ := by
  let z := prodModelEquiv N d (q.1.val,q.2.val)
  have ht : parameterZeroInsert (c.m.natAdd N) z ∈ c.Φ.target := by
    rw [originalZeroNormalPoint p c]
    exact c.mapsTo_target q.1.val q.1.property (c.tangentLift q.2.val) q.2.property
  have hF := differentiableAt_sliceToParameterFlattening p c m ht
  have heq : (fun w => sliceToParameterFlattening p c m w (m.castAdd (d + 1)))
      =ᶠ[𝓝 (parameterZeroInsert (c.m.natAdd N) z)] (fun w => w (c.m.natAdd N)) := by
    filter_upwards [c.Φ.isOpen_target.mem_nhds ht] with w hw
    exact sliceToParameterFlattening_standard_normal p c m hw
  change ‖LinearMap.det (fderiv ℂ
    (normalSliceMap (d := N + d) (sliceToParameterFlattening (n := d + 1) p c m)
      (c.m.natAdd N) (m.castAdd (d + 1))) z).toLinearMap‖ = _
  rw [normalSliceMap_complex_det_norm (d := N + d) (c.m.natAdd N) (m.castAdd (d + 1)) hF heq]
  have h := congrArg norm (sliceToParameterFlattening_complex_det (n := d + 1) p c m ht)
  dsimp only [z] at h
  rw [originalZeroNormalPoint p c] at h
  exact (congrArg (fun v : ComplexModel (N + (d + 1)) =>
    ‖LinearMap.det (fderiv ℂ (sliceToParameterFlattening (n := d + 1) p c m) v).toLinearMap‖)
      (originalZeroNormalPoint p c q.1.val q.2.val)).trans h

theorem injective_originalQCoordinateMap_fderiv (m : Fin N)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hm : parameterCoefficient p c.i c.j m (c.tangentPoint q) ≠ 0) :
    Function.Injective (fderiv ℂ (originalQCoordinateMap p c m) (prodModelEquiv N d (q.1.val,q.2.val))) := by
  have hdet : LinearMap.det (fderiv ℂ (originalQCoordinateMap p c m)
      (prodModelEquiv N d (q.1.val,q.2.val))).toLinearMap ≠ 0 := by
    intro hz
    have h := originalQCoordinateMap_complex_det_norm p c m q
    rw [hz,norm_zero] at h
    exact (norm_ne_zero_iff.mpr (div_ne_zero hm (c.tangentNormalDenominator_ne_zero p.contMDiff q))) h.symm
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

theorem exists_originalQCoordinate_local_COV (m : Fin N)
    (q₀ : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hm : parameterCoefficient p c.i c.j m (c.tangentPoint q₀) ≠ 0) :
    ∃ Θ : LocalHolomorphicEquivAt (n := N + d) (prodModelEquiv N d (q₀.1.val,q₀.2.val)),
      Θ.source ⊆ originalQSourceDomain p c ∧ Θ.toFun = originalQCoordinateMap p c m ∧
      (∀ z ∈ Θ.source, parameterCoefficient p c.i c.j m (originalQSourceX p c z) ≠ 0) ∧
      ∀ g : ComplexModel (N + d) → ℝ≥0∞,
        (∫⁻ y in Θ.target, g y) = ∫⁻ z in Θ.source,
          ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| *
            g (originalQCoordinateMap p c m z) := by
  have hsource : prodModelEquiv N d (q₀.1.val,q₀.2.val) ∈ originalQSourceDomain p c := by
    change (prodModelEquiv N d).symm (prodModelEquiv N d (q₀.1.val,q₀.2.val)) ∈
      ((ball c.ζ₀ c.r) ×ˢ c.tangentPatch)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨q₀.1.property,q₀.2.property⟩
  have hdiff : DifferentiableOn ℂ (originalQCoordinateMap p c m) (originalQSourceDomain p c) :=
    fun z hz => (differentiableAt_originalQCoordinateMap p c m hz).differentiableWithinAt
  obtain ⟨Θ,hΘsrc,hΘfun,hΘinj⟩ := exists_localHolomorphicEquivAt (originalQSourceDomain p c).isOpen hsource
    hdiff (injective_originalQCoordinateMap_fderiv p c m q₀ hm)
  refine ⟨Θ,hΘsrc,hΘfun,?_,?_⟩
  · intro z hz
    let q := originalQSourcePair p c ⟨z,hΘsrc hz⟩
    have hq : prodModelEquiv N d (q.1.val,q.2.val) = z := (prodModelEquiv N d).apply_symm_apply z
    have hnorm := originalQCoordinateMap_complex_det_norm p c m q
    rw [hq] at hnorm
    have hdet : LinearMap.det (fderiv ℂ (originalQCoordinateMap p c m) z).toLinearMap ≠ 0 := by
      intro hd
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd) (LinearMap.ker_eq_bot.mpr (hΘinj z hz))
    change parameterCoefficient p c.i c.j m (c.tangentPoint q) ≠ 0
    intro hc
    rw [hc,zero_div,norm_zero] at hnorm
    exact hdet (norm_eq_zero.mp hnorm)
  · intro g
    have hderiv : ∀ z ∈ Θ.source,
        HasFDerivWithinAt (originalQCoordinateMap p c m) (fderiv ℝ (originalQCoordinateMap p c m) z) Θ.source z := by
      intro z hz
      exact ((differentiableAt_originalQCoordinateMap p c m (hΘsrc hz)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
    have hinj : InjOn (originalQCoordinateMap p c m) Θ.source := by
      intro a ha b hb hab
      calc
        a = Θ.invFun (Θ.toFun a) := (Θ.left_inv a ha).symm
        _ = Θ.invFun (Θ.toFun b) := congrArg Θ.invFun (by simpa only [hΘfun] using hab)
        _ = b := Θ.left_inv b hb
    have himage : (originalQCoordinateMap p c m) '' Θ.source = Θ.target := by
      rw [← hΘfun]
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact Θ.mapsTo_toFun hz
      · intro hy
        exact ⟨Θ.invFun y,Θ.mapsTo_invFun hy,Θ.right_inv y hy⟩
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume Θ.isOpen_source.measurableSet hderiv hinj g
    rwa [himage] at hcov

end SGPT.Trace.BertiniUniversal
