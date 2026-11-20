import SGPT.Projective.CurveHolomorphicZeroPresentation
import SGPT.Okounkov.NativeHolomorphicGermRing
import SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder

/-! Actual singleton divisor coordinates on an original native curve and
literal model-coordinate equation. Blueprint: curve-point-normal-order.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Set Filter
open scoped Topology Manifold
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder
open SGPT.Okounkov
variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel 1) M]
  [IsComplexManifold 1 M]

/-- The SAME original point has literal translated preferred-chart divisor coordinates. -/
def curvePointFlattening (p : M) : DivisorFlattening (m := 0) ({p} : Set M) p := by
  let c := (complexChartAt (n := 1) p).val
  let x := c p
  let Φ : LocalHolomorphicEquivAt (n := 1) x := {
    source := c.target
    target := {z | z + x ∈ c.target}
    isOpen_source := c.open_target
    isOpen_target := c.open_target.preimage (continuous_add_const x)
    center_mem_source := c.map_source (mem_complexChartAt_source p)
    toFun := fun z => z - x
    invFun := fun z => z + x
    toFun_holomorphic := (differentiable_id.sub_const x).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const x).differentiableOn
    mapsTo_toFun := fun z hz => by simpa only [mem_ofPred_eq, sub_add_cancel] using hz
    mapsTo_invFun := fun z hz => hz
    left_inv := fun z _ => sub_add_cancel z x
    right_inv := fun z _ => add_sub_cancel_right z x }
  refine { Φ := Φ, source_subset := subset_rfl, map_center := sub_self x, mem_iff := ?_ }
  intro y hy _
  change y ∈ ({p} : Set M) ↔ (c y - c p) (Fin.last 0) = 0
  constructor
  · rintro rfl
    simp
  · intro h
    apply Set.mem_singleton_iff.mpr
    apply c.injOn hy (mem_complexChartAt_source p)
    ext i
    have hi : i = Fin.last 0 := Subsingleton.elim _ _
    subst i
    exact sub_eq_zero.mp h

omit [IsComplexManifold 1 M] in
/-- The SAME produced point equation is the literal original scalar coordinate germ. -/
theorem curvePointFlattening_equation (p : M) :
    divisorEquationGerm (curvePointFlattening p) =
      HolGerm.mk curveScalarCoordinate
        (Eventually.of_forall fun z => curveScalarCoordinate.differentiableAt (x := z)) := by
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [] with z
  change ((z + (complexChartAt (n := 1) p).val p) -
    (complexChartAt (n := 1) p).val p) (Fin.last 0) = curveScalarCoordinate z
  rw [add_sub_cancel_right]
  rfl

omit [IsComplexManifold 1 M] in
/-- Full normal order along ANY actual flattening of the SAME original point
is the analytic scalar order of the SAME original model representative. -/
theorem curvePoint_normalOrder_eq_analyticOrder (p : M)
    (Ψ : DivisorFlattening (m := 0) ({p} : Set M) p)
    (G : ComplexModel 1 → ℂ) (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z)
    (hgerm : HolGerm.mk G hG ≠ 0) :
    normalOrder Ψ (HolGerm.mk G hG) =
      analyticOrderAt (fun z : ℂ => G (curveScalarCoordinate.symm z)) 0 := by
  let e := curveScalarCoordinate
  let F : ℂ → ℂ := fun z => G (e.symm z)
  have he : Tendsto e (𝓝 0) (𝓝 0) := by simpa only [map_zero] using e.continuous.tendsto 0
  have hei : Tendsto e.symm (𝓝 0) (𝓝 0) := by simpa only [map_zero] using e.symm.continuous.tendsto 0
  have hF : AnalyticAt ℂ F 0 := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hei.eventually hG] with z hz
    exact hz.comp z e.symm.differentiableAt
  have hFne : ¬ ∀ᶠ z in 𝓝 0, F z = 0 := by
    intro h
    apply hgerm
    rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    change ∀ᶠ z in 𝓝 0, G z = 0
    simpa only [F, ContinuousLinearEquiv.symm_apply_apply] using he.eventually h
  obtain ⟨k, v, hv, hvne, hfac⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hFne
  have hV : ∀ᶠ z in 𝓝 (0 : ComplexModel 1), DifferentiableAt ℂ (fun y => v (e y)) z := by
    filter_upwards [he.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hv)] with z hz
    exact hz.comp z e.differentiableAt
  let t : HolGerm (ComplexModel 1) := HolGerm.mk e
    (Eventually.of_forall fun z => e.differentiableAt (x := z))
  let u : HolGerm (ComplexModel 1) := HolGerm.mk (fun z => v (e z)) hV
  have ht : Prime t := by
    rw [show t = divisorEquationGerm (curvePointFlattening p) from
      (curvePointFlattening_equation p).symm]
    exact prime_divisorEquationGerm _
  have hu : IsUnit u := by
    apply (HolGerm.isUnit_iff_eval_ne_zero u).mpr
    simpa only [u, HolGerm.eval_mk, map_zero] using hvne
  have hprod : ∀ᶠ z in 𝓝 (0 : ComplexModel 1),
      DifferentiableAt ℂ (fun y => (e y) ^ k * v (e y)) z := by
    filter_upwards [hV] with z hz
    exact (e.differentiableAt.pow k).mul hz
  have hfactor : HolGerm.mk G hG = t ^ k * u := by
    change HolGerm.mk G hG = HolGerm.mk (fun z => (e z) ^ k * v (e z)) hprod
    apply HolGerm.mk_eq_mk_iff.mpr
    change ∀ᶠ z in 𝓝 0, G z = (e z) ^ k * v (e z)
    simpa only [F, ContinuousLinearEquiv.symm_apply_apply, sub_zero, smul_eq_mul] using
      he.eventually hfac
  calc
    normalOrder Ψ (HolGerm.mk G hG) = normalOrder (curvePointFlattening p) (HolGerm.mk G hG) :=
      normalOrder_independent _ _ _
    _ = (k : ℕ∞) := by
      unfold normalOrder
      rw [curvePointFlattening_equation]
      change emultiplicity t (HolGerm.mk G hG) = _
      rw [hfactor, emultiplicity_mul ht, emultiplicity_pow_self_of_prime ht,
        emultiplicity_of_isUnit_right ht.not_isUnit hu, add_zero]
    _ = _ := (hF.analyticOrderAt_eq_natCast.mpr ⟨v, hv, hvne, hfac⟩).symm

end SGPT.Projective.NumEq.AlgebraicCurveDegree
