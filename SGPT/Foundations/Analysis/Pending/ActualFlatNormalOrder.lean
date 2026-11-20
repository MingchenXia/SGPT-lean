import SGPT.Foundations.Analysis.Pending.SNCHolomorphicTestNecessity
import SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualFlatNormalOrder

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.HolomorphicMaps
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreNearbyStalks HolomorphicGermJacobian
  HolomorphicGermReducednessBridge DivisorialChangeOfVariables

universe u

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y]
  {E : Set Y} {y : Y}

private def flatteningEquiv (Φ : DivisorFlattening (m := m) E y) :
    LocalHolomorphicEquivAt (n := m + 1) (0 : ComplexModel (m + 1)) :=
  actualNearbyEquiv Φ.Φ 0 Φ.zero_mem_target

private theorem flatteningEquiv_zero (Φ : DivisorFlattening (m := m) E y) :
    (flatteningEquiv Φ).toFun 0 = 0 := actualNearbyEquiv_zero Φ.Φ 0 Φ.zero_mem_target

/-- The genuine entire germ equivalence manufactured by this actual flattening. -/
def actualFlatteningGermEquiv (Φ : DivisorFlattening (m := m) E y) :
    HolGerm (ComplexModel (m + 1)) ≃ₐ[ℂ] HolGerm (ComplexModel (m + 1)) :=
  localGermAlgEquiv (flatteningEquiv Φ) (flatteningEquiv_zero Φ)

/-- Its coordinate equation is the SAME actual preferred normal equation. -/
theorem actualFlatteningGermEquiv_coordinate (Φ : DivisorFlattening (m := m) E y) :
    actualFlatteningGermEquiv Φ (HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m))) = divisorEquationGerm Φ := by
  unfold actualFlatteningGermEquiv
  rw [localGermAlgEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    simp only [Function.comp_apply, flatteningEquiv, actualNearbyEquiv, sub_zero, Φ.invFun_zero]

variable [IsComplexManifold (m + 1) Y]

private theorem flat_function_holomorphic (Φ : DivisorFlattening (m := m) E y)
    {f : Y → ℂ} (hf : HolomorphicAt (m + 1) f y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (fun z => f (Φ.point z)) z := by
  have ht : Tendsto Φ.point (𝓝 0) (𝓝 y) := by
    simpa only [Φ.point_zero] using (Φ.mdifferentiableAt_point Φ.zero_mem_target).continuousAt.tendsto
  filter_upwards [ht.eventually hf, Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target] with z hzf hzT
  exact mdifferentiableAt_iff_differentiableAt.mp (hzf.comp z (Φ.mdifferentiableAt_point hzT))

/-- The literal original local function in the actual flat inverse coordinates. -/
def flatFunctionGerm (Φ : DivisorFlattening (m := m) E y) (f : Y → ℂ)
    (hf : HolomorphicAt (m + 1) f y) : HolGerm (ComplexModel (m + 1)) :=
  HolGerm.mk (fun z => f (Φ.point z)) (flat_function_holomorphic Φ hf)

/-- The whole actual nonlinear inverse sends the actual flat function to its original chart germ. -/
theorem actualFlatteningGermEquiv_function (Φ : DivisorFlattening (m := m) E y)
    (f : Y → ℂ) (hf : HolomorphicAt (m + 1) f y) :
    actualFlatteningGermEquiv Φ (flatFunctionGerm Φ f hf) =
      chartTranslatedGerm y y (mem_chart_source _ y) f hf := by
  unfold actualFlatteningGermEquiv flatFunctionGerm
  rw [localGermAlgEquiv_mk]
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [(flatteningEquiv Φ).isOpen_source.mem_nhds
    (flatteningEquiv Φ).center_mem_source] with z hz
  have hzΦ : z + (complexChartAt (n := m + 1) y).val y ∈ Φ.Φ.source := by
    simpa only [flatteningEquiv, actualNearbyEquiv, mem_preimage, Φ.invFun_zero] using hz
  change f ((complexChartAt (n := m + 1) y).val.symm
      (Φ.Φ.invFun ((flatteningEquiv Φ).toFun z))) =
    f ((chartAt (ComplexModel (m + 1)) y).symm (z + (chartAt (ComplexModel (m + 1)) y) y))
  simp only [flatteningEquiv, actualNearbyEquiv, sub_zero, Φ.invFun_zero, Φ.Φ.left_inv _ hzΦ]
  rfl

/-- Actual flat coordinates compute the natural order, retaining zero and infinity. -/
theorem functionNormalOrder_eq_flat (Φ : DivisorFlattening (m := m) E y)
    (f : Y → ℂ) (hf : HolomorphicAt (m + 1) f y) :
    functionNormalOrder Φ f hf =
      emultiplicity (HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
        (eventually_differentiableAt_coordinate (Fin.last m))) (flatFunctionGerm Φ f hf) := by
  change emultiplicity (divisorEquationGerm Φ)
    (chartTranslatedGerm y y (mem_chart_source _ y) f hf) = _
  rw [← actualFlatteningGermEquiv_coordinate Φ, ← actualFlatteningGermEquiv_function Φ f hf]
  exact emultiplicity_map_eq (actualFlatteningGermEquiv Φ)

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- The literal preferred coordinate map, with actual source and target centres translated to zero. -/
def preferredCenteredMap (π : Y → X) (y : Y) : ComplexModel (m + 1) → ComplexModel (m + 1) :=
  fun z => coordinateMap π (complexChartAt (n := m + 1) y)
    (complexChartAt (n := m + 1) (π y)) (z + (complexChartAt (n := m + 1) y).val y) -
      (complexChartAt (n := m + 1) (π y)).val (π y)

/-- The SAME literal map read through the actual flattening inverse. -/
def flatCenteredMap (π : Y → X) (Φ : DivisorFlattening (m := m) E y) :
    ComplexModel (m + 1) → ComplexModel (m + 1) :=
  fun z => flatCoordMap π Φ z - (complexChartAt (n := m + 1) (π y)).val (π y)

private theorem preferred_map_holomorphic {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π) (y : Y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (preferredCenteredMap π y) z := by
  let e := complexChartAt (n := m + 1) y
  let d := complexChartAt (n := m + 1) (π y)
  have hp : e.val y ∈ coordinateDomain π e d :=
    mem_coordinateDomain (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))
  have hD := coordinateDomain_isOpen hπ e d
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e.val y) (𝓝 0) (𝓝 (e.val y)) := by
    simpa only [zero_add] using (continuous_add_const (e.val y)).tendsto 0
  filter_upwards [ht.eventually (hD.mem_nhds hp)] with z hz
  exact (((coordinateMap_contDiffOn hπ e d).contDiffAt
    (hD.mem_nhds hz)).differentiableAt (by simp)).comp z
      (differentiableAt_id.add_const (e.val y)) |>.sub_const (d.val (π y))

private theorem flat_map_holomorphic {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (Φ : DivisorFlattening (m := m) E y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (flatCenteredMap π Φ) z := by
  have hD := Φ.isOpen_flatDomain hπ.continuous
  filter_upwards [hD.mem_nhds (Φ.zero_mem_flatDomain π)] with z hz
  exact ((Φ.differentiableOn_flatCoordMap hπ).differentiableAt
    (hD.mem_nhds hz)).sub_const _

/-- The entire actual preferred Jacobian germ, without nonzero or finite-order hypotheses. -/
def preferredJacobianGerm {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π) (y : Y) :
    HolGerm (ComplexModel (m + 1)) := jacobianGerm (preferredCenteredMap π y) (preferred_map_holomorphic hπ y)

/-- The entire actual flat Jacobian germ for this SAME map and carrier. -/
def flatJacobianGerm {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (Φ : DivisorFlattening (m := m) E y) : HolGerm (ComplexModel (m + 1)) :=
  jacobianGerm (flatCenteredMap π Φ) (flat_map_holomorphic hπ Φ)

private theorem jacobianGerm_congr {n : ℕ} {F G : ComplexModel n → ComplexModel n}
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (hFG : F =ᶠ[𝓝 0] G) :
    jacobianGerm F hF = jacobianGerm G hG := by
  apply Subtype.ext
  rw [jacobianGerm_source, jacobianGerm_source]
  apply Germ.coe_eq.mpr
  filter_upwards [hFG.fderiv (𝕜 := ℂ)] with z hz
  exact congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L.det) hz

omit [IsComplexManifold (m + 1) Y] [IsComplexManifold (m + 1) X] in
private theorem preferred_eq_flat_comp {π : Y → X} (Φ : DivisorFlattening (m := m) E y) :
    preferredCenteredMap π y =ᶠ[𝓝 0] flatCenteredMap π Φ ∘ (flatteningEquiv Φ).toFun := by
  filter_upwards [(flatteningEquiv Φ).isOpen_source.mem_nhds
    (flatteningEquiv Φ).center_mem_source] with z hz
  have hzΦ : z + (complexChartAt (n := m + 1) y).val y ∈ Φ.Φ.source := by
    simpa only [flatteningEquiv, actualNearbyEquiv, mem_preimage, Φ.invFun_zero] using hz
  simp only [preferredCenteredMap, flatCenteredMap, Function.comp_apply,
    coordinateMap, flatCoordMap, DivisorFlattening.point, flatteningEquiv,
    actualNearbyEquiv, sub_zero, Φ.invFun_zero, Φ.Φ.left_inv _ hzΦ]

private theorem flat_comp_holomorphic {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (Φ : DivisorFlattening (m := m) E y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (flatCenteredMap π Φ ∘ (flatteningEquiv Φ).toFun) z := by
  have hξ := local_toFun_holomorphic (flatteningEquiv Φ)
  have ht : Tendsto (flatteningEquiv Φ).toFun (𝓝 0) (𝓝 0) := by
    simpa only [flatteningEquiv_zero Φ] using hξ.self_of_nhds.continuousAt.tendsto
  filter_upwards [hξ, ht.eventually (flat_map_holomorphic hπ Φ)] with z hz hQ
  exact hQ.comp z hz

/-- The true same-map/source-coordinate transport identifies the preferred and flat orders. -/
theorem preferredJacobianOrder_eq_flat {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (Φ : DivisorFlattening (m := m) E y) :
    normalOrder Φ (preferredJacobianGerm hπ y) =
      emultiplicity (HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
        (eventually_differentiableAt_coordinate (Fin.last m))) (flatJacobianGerm hπ Φ) := by
  let t := HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
    (eventually_differentiableAt_coordinate (Fin.last m))
  have hJ := jacobianGerm_congr (preferred_map_holomorphic hπ y)
    (flat_comp_holomorphic hπ Φ) (preferred_eq_flat_comp (π := π) Φ)
  change emultiplicity (divisorEquationGerm Φ) (jacobianGerm _ _) = _
  rw [hJ, ← actualFlatteningGermEquiv_coordinate Φ]
  exact emultiplicity_jacobian_comp_source t (flatCenteredMap π Φ) (flat_map_holomorphic hπ Φ)
    (flatteningEquiv Φ) (flatteningEquiv_zero Φ)

/-- Local relative Jacobian order; whole-prime canonical discrepancy is not claimed here. -/
def flatJacobianOrder {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (Φ : DivisorFlattening (m := m) E y) : ℕ∞ :=
  emultiplicity (HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
    (eventually_differentiableAt_coordinate (Fin.last m))) (flatJacobianGerm hπ Φ)

theorem flatJacobianOrder_independent {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (Φ Ψ : DivisorFlattening (m := m) E y) : flatJacobianOrder hπ Φ = flatJacobianOrder hπ Ψ := by
  rw [flatJacobianOrder, flatJacobianOrder, ← preferredJacobianOrder_eq_flat hπ Φ,
    ← preferredJacobianOrder_eq_flat hπ Ψ]
  exact normalOrder_independent Φ Ψ (preferredJacobianGerm hπ y)

/-- The entire literal original local pullback test times its actual flat Jacobian. -/
def weightedTestGerm {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ : DivisorFlattening (m := m) E y) (f : X → ℂ)
    (hf : HolomorphicAt (m + 1) f (π y)) : HolGerm (ComplexModel (m + 1)) :=
  flatFunctionGerm Φ (f ∘ π)
    (hf.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)) * flatJacobianGerm hπ.1 Φ

/-- Entire readback is the EXACT weighted test of the genuine strict-margin producer. -/
theorem weightedTestGerm_source {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ : DivisorFlattening (m := m) E y) (f : X → ℂ)
    (hf : HolomorphicAt (m + 1) f (π y)) :
    ((weightedTestGerm hπ Φ f hf : HolGerm (ComplexModel (m + 1))) :
      Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ) =
      (fun z => f ((complexChartAt (n := m + 1) (π y)).val.symm (flatCoordMap π Φ z)) *
        complexJacobian (flatCoordMap π Φ) z : Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ) := by
  unfold weightedTestGerm flatFunctionGerm flatJacobianGerm
  rw [Subring.coe_mul, HolGerm.coe_mk, jacobianGerm_source]
  change ((fun z => f (π (Φ.point z)) * complexJacobian (flatCenteredMap π Φ) z) :
    Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ) = _
  apply Germ.coe_eq.mpr
  filter_upwards [(Φ.isOpen_flatDomain hπ.1.continuous).mem_nhds (Φ.zero_mem_flatDomain π)] with z hz
  rw [Φ.chartSymm_flatCoordMap π hz]
  congr 1
  change (fderiv ℂ (fun w => flatCoordMap π Φ w -
    (complexChartAt (n := m + 1) (π y)).val (π y)) z).det =
      (fderiv ℂ (flatCoordMap π Φ) z).det
  rw [fderiv_sub_const]

theorem weightedTest_order_eq_sum {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ : DivisorFlattening (m := m) E y) (f : X → ℂ)
    (hf : HolomorphicAt (m + 1) f (π y)) :
    emultiplicity (HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m))) (weightedTestGerm hπ Φ f hf) =
      pullbackNormalOrder hπ Φ f hf + flatJacobianOrder hπ.1 Φ := by
  rw [weightedTestGerm, emultiplicity_mul (HolomorphicCoordinatePrime.prime_coordinate_germ (Fin.last m))]
  rw [← functionNormalOrder_eq_flat Φ (f ∘ π)
    (hf.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt))]
  rfl

private def coordinateGerm (j : Fin (m + 1)) : HolGerm (ComplexModel (m + 1)) :=
  HolGerm.mk (fun z : ComplexModel (m + 1) => z j) (eventually_differentiableAt_coordinate j)

private theorem coordinate_product_source (a : Fin (m + 1) → ℕ) :
    (((∏ j, coordinateGerm j ^ a j) : HolGerm (ComplexModel (m + 1))) :
      Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ) =
      (fun z : ComplexModel (m + 1) => ∏ j, z j ^ a j : Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ) := by
  rw [SubmonoidClass.coe_finsetProd]
  simp only [SubmonoidClass.coe_pow, coordinateGerm, HolGerm.coe_mk]
  have h := map_prod (Germ.coeRingHom (𝓝 (0 : ComplexModel (m + 1))) :
    (ComplexModel (m + 1) → ℂ) →+* Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ)
    (fun j z => z j ^ a j) Finset.univ
  simp only [Germ.coe_coeRingHom] at h
  simp_rw [← Germ.coe_pow]
  change (∏ i, ((fun z : ComplexModel (m + 1) => z i ^ a i) :
    Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ)) = _
  rw [← h, Finset.prod_fn]

/-- Actual coordinate factorization, not a supplied order equality, computes the genuine exponent. -/
theorem emultiplicity_coordinate_factorization (g : HolGerm (ComplexModel (m + 1)))
    (a : Fin (m + 1) → ℕ) (H : ComplexModel (m + 1) → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hfactor : (g : Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ) =
      (fun z => H z * ∏ j, z j ^ a j : Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ))
    (hnot : ¬coordinateGerm (Fin.last m) ∣ HolGerm.mk H hH) :
    emultiplicity (coordinateGerm (Fin.last m)) g = (a (Fin.last m) : ℕ∞) := by
  have heq : g = HolGerm.mk H hH * ∏ j, coordinateGerm j ^ a j := by
    apply Subtype.ext
    rw [Subring.coe_mul, HolGerm.coe_mk, coordinate_product_source]
    exact hfactor
  let t := coordinateGerm (Fin.last m)
  have ht : Prime t := HolomorphicCoordinatePrime.prime_coordinate_germ (Fin.last m)
  rw [heq, emultiplicity_mul ht, emultiplicity_eq_zero.mpr hnot, zero_add,
    Finset.emultiplicity_prod ht]
  rw [Finset.sum_eq_single (Fin.last m)]
  · exact emultiplicity_pow_self_of_prime ht _
  · intro j _ hj
    have hnd : ¬ t ∣ coordinateGerm j :=
      SNCHolomorphicTestNecessity.coordinate_germ_not_dvd_of_ne hj
    rw [emultiplicity_pow ht, emultiplicity_eq_zero.mpr hnd, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The exponent actually returned by the strict-margin factorization is the SUM of the natural orders. -/
theorem weightedTest_order_eq_factorization {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ : DivisorFlattening (m := m) E y) (f : X → ℂ)
    (hf : HolomorphicAt (m + 1) f (π y)) (a : Fin (m + 1) → ℕ)
    (H : ComplexModel (m + 1) → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hfactor : (fun z => f ((complexChartAt (n := m + 1) (π y)).val.symm (flatCoordMap π Φ z)) *
      complexJacobian (flatCoordMap π Φ) z) =ᶠ[𝓝 0] (fun z => H z * ∏ j, z j ^ a j))
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk H hH) :
    (a (Fin.last m) : ℕ∞) = pullbackNormalOrder hπ Φ f hf + flatJacobianOrder hπ.1 Φ := by
  have horder := emultiplicity_coordinate_factorization (weightedTestGerm hπ Φ f hf) a H hH
    ((weightedTestGerm_source hπ Φ f hf).trans (Germ.coe_eq.mpr hfactor)) hnot
  exact horder.symm.trans (weightedTest_order_eq_sum hπ Φ f hf)

end SGPT.Foundations.Analysis.Pending.ActualFlatNormalOrder
