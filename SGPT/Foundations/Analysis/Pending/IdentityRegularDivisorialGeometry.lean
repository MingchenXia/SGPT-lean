import SGPT.Foundations.Analysis.Pending.IOrderDivisorialLelongForward
import SGPT.Foundations.Analysis.Pending.AnalyticJacobianSingularCore
import SGPT.Foundations.Analysis.Pending.CoordinateDensityGeneral

set_option autoImplicit false

/-!
# Actual identity-map geometry at regular hypersurface points

Supplementary specialization of the forward all-level ideal--Lelong
comparison.  Hypersurface regularity internally supplies the actual
flattening, nonzero holomorphic Jacobian of order zero and log
discrepancy bound one.  The identity has empty chart-null exceptional
set.  No all-prime-divisor dictionary or arbitrary-modification
factorization is claimed.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.IdentityRegularDivisorialGeometry

open FirstPass FirstPass.HolomorphicMaps FirstPass.PositiveClasses
  FirstPass.NonKahlerLocus FirstPass.IEnvelope
  DemaillyApproximantDivisorialLelong DivisorialChangeOfVariables

private theorem differentiableOn_complexJacobian {n : ℕ}
    {F : ComplexModel n → ComplexModel n} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (complexJacobian F) U := by
  classical
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector j)) i) U :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
      (FirstPass.differentiableOn_fderiv_apply_of_isOpen hF hU
        (FirstPass.MongeAmpere.coordinateVector j))
  have hdet : complexJacobian F = fun z =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector a)) (σ a) := by
    funext z
    rw [complexJacobian, ContinuousLinearMap.det,
      ← FirstPass.MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [FirstPass.MongeAmpere.standardMatrix_apply]
    rfl
  rw [hdet]
  refine DifferentiableOn.fun_sum fun σ _ =>
    (?_ : DifferentiableOn ℂ _ U).const_smul _
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih

private theorem complexJacobian_invFun_ne_zero {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) {z : ComplexModel n} (hz : z ∈ Φ.target) :
    complexJacobian Φ.invFun z ≠ 0 := by
  have hinv := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)
  have hf := Φ.toFun_holomorphic.differentiableAt
    (Φ.isOpen_source.mem_nhds (Φ.mapsTo_invFun hz))
  have heq : (Φ.toFun ∘ Φ.invFun) =ᶠ[𝓝 z] id := by
    filter_upwards [Φ.isOpen_target.mem_nhds hz] with w hw
    exact Φ.right_inv w hw
  have hcomp : (fderiv ℂ Φ.toFun (Φ.invFun z)).comp (fderiv ℂ Φ.invFun z) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    calc
      _ = fderiv ℂ (Φ.toFun ∘ Φ.invFun) z :=
        (hf.hasFDerivAt.comp z hinv.hasFDerivAt).fderiv.symm
      _ = _ := by rw [heq.fderiv_eq, fderiv_id]
  have hlin : (fderiv ℂ Φ.toFun (Φ.invFun z)).toLinearMap.comp
      (fderiv ℂ Φ.invFun z).toLinearMap = LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap hcomp
  have hdet := congrArg
    (fun L : ComplexModel n →ₗ[ℂ] ComplexModel n => LinearMap.det L) hlin
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  intro hzero
  change LinearMap.det (fderiv ℂ Φ.invFun z).toLinearMap = 0 at hzero
  rw [hzero, mul_zero] at hdet
  exact zero_ne_one hdet

/-- A genuine regular hypersurface flattening makes the identity Jacobian
holomorphic of order zero and nonzero at the centre. -/
theorem logDiscrepancyLE_id_of_regularAtDim
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {E : Set X} {x : X} (h : RegularAtDim (n := m + 1) E x m) :
    LogDiscrepancyLE m (id : X → X) E x 1 := by
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim h
  have hmap : EqOn (flatCoordMap (id : X → X) Φ) Φ.Φ.invFun Φ.Φ.target :=
    fun z hz => Φ.chart_point hz
  have hhol : DifferentiableOn ℂ (flatCoordMap (id : X → X) Φ) Φ.Φ.target :=
    Φ.Φ.invFun_holomorphic.congr hmap
  have hJ := differentiableOn_complexJacobian Φ.Φ.isOpen_target hhol
  have hJhol : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (complexJacobian (flatCoordMap (id : X → X) Φ)) z := by
    filter_upwards [Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target] with z hz
    exact hJ.differentiableAt (Φ.Φ.isOpen_target.mem_nhds hz)
  have hev : flatCoordMap (id : X → X) Φ =ᶠ[𝓝 0] Φ.Φ.invFun := by
    filter_upwards [Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target] with z hz
    exact hmap hz
  have hJ0 : complexJacobian (flatCoordMap (id : X → X) Φ) 0 ≠ 0 := by
    rw [complexJacobian, hev.fderiv_eq]
    exact complexJacobian_invFun_ne_zero Φ.Φ Φ.zero_mem_target
  refine ⟨Φ, 0, complexJacobian (flatCoordMap (id : X → X) Φ), by decide,
    hJhol, ?_, ?_⟩
  · exact Eventually.of_forall fun z => by simp
  · apply frequently_nhds_iff.mpr
    intro U hU _
    exact ⟨0, hU, by simp, hJ0⟩

/-- The identity supplies all null-injectivity and discrepancy geometry,
so all-level ideal order compares the bare hypersurface infima. -/
theorem divisorialLelongNumber_le_of_iOrder_regular
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] (omega : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) {u v : X → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hI : IOrderOnManifold (n := m + 1) u v)
    {E : Set X} (hE : ∀ x ∈ E, RegularAtDim (n := m + 1) E x m) :
    divisorialLelongNumber m v E ≤ divisorialLelongNumber m u E := by
  have hinj : IsInjectiveOffNull m (id : X → X) := by
    refine ⟨∅, ?_, ?_⟩
    · intro y
      simp
    · exact Function.injective_id.injOn
  exact IOrderDivisorialLelongForward.divisorialLelongNumber_comp_le_of_iOrder
    omega θ hu hv hI contMDiff_id hinj
      (fun x hx => logDiscrepancyLE_id_of_regularAtDim (hE x hx))

end SGPT.Foundations.Analysis.Pending.IdentityRegularDivisorialGeometry
