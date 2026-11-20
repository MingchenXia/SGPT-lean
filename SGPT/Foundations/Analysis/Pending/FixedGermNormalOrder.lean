import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.HolomorphicGermJacobian
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicMultiplierGermCovariance


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder

universe u

open FirstPass FirstPass.HolomorphicIdealSheaves DemaillyApproximantDivisorialLelong
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaNormalCrossingsBranchOverlap

section LocalPrime

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] {E : Set Y} {y : Y}

private theorem shifted_flattening_holomorphic (Φ : DivisorFlattening (m := m) E y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z => Φ.Φ.toFun
        (z + (complexChartAt (n := m + 1) y).val y)) z := by
  let p := (complexChartAt (n := m + 1) y).val y
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + p) (𝓝 0) (𝓝 p) := by
    simpa only [zero_add] using (continuous_add_const p).tendsto 0
  filter_upwards [ht.eventually (Φ.Φ.isOpen_source.mem_nhds Φ.chart_mem_source)] with z hz
  exact (Φ.Φ.toFun_holomorphic.differentiableAt
    (Φ.Φ.isOpen_source.mem_nhds hz)).comp z (differentiableAt_id.add_const p)

private theorem equation_holomorphic (Φ : DivisorFlattening (m := m) E y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z => Φ.Φ.toFun
        (z + (complexChartAt (n := m + 1) y).val y) (Fin.last m)) z := by
  filter_upwards [shifted_flattening_holomorphic Φ] with z hz
  exact (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiableAt.comp z hz

/-- The literal last-coordinate equation in the actual translated preferred chart. -/
def divisorEquationGerm (Φ : DivisorFlattening (m := m) E y) :
    HolGerm (ComplexModel (m + 1)) :=
  HolGerm.mk (fun z => Φ.Φ.toFun
    (z + (complexChartAt (n := m + 1) y).val y) (Fin.last m)) (equation_holomorphic Φ)

/-- Actual local inverse geometry makes the literal equation germ prime. -/
theorem prime_divisorEquationGerm (Φ : DivisorFlattening (m := m) E y) :
    Prime (divisorEquationGerm Φ) := by
  exact prime_coordinate_of_surjective_fderiv (shifted_flattening_holomorphic Φ)
    (by simpa only [zero_add] using Φ.map_center)
    (surjective_fderiv_shifted Φ.Φ) (Fin.last m)

/-- Natural extended normal order, retaining the zero germ with order infinity. -/
def normalOrder (Φ : DivisorFlattening (m := m) E y)
    (g : HolGerm (ComplexModel (m + 1))) : ℕ∞ := emultiplicity (divisorEquationGerm Φ) g

/-- The SAME actual carrier supplies the equation association; no association is an input. -/
theorem associated_divisorEquationGerm (Φ Ψ : DivisorFlattening (m := m) E y) :
    Associated (divisorEquationGerm Φ) (divisorEquationGerm Ψ) := by
  classical
  let e := (complexChartAt (n := m + 1) y).val
  let p := e y
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + p) (𝓝 0) (𝓝 p) := by
    simpa only [zero_add] using (continuous_add_const p).tendsto 0
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      Φ.Φ.toFun (z + p) (Fin.last m) = 0 ↔ Ψ.Φ.toFun (z + p) (Fin.last m) = 0 := by
    filter_upwards [ht.eventually (e.open_target.mem_nhds
        (e.map_source (mem_complexChartAt_source y))),
      ht.eventually (Φ.Φ.isOpen_source.mem_nhds Φ.chart_mem_source),
      ht.eventually (Ψ.Φ.isOpen_source.mem_nhds Ψ.chart_mem_source)] with z hzT hzΦ hzΨ
    have hys : e.symm (z + p) ∈ e.source := e.map_target hzT
    have hchart : e (e.symm (z + p)) = z + p := e.right_inv hzT
    have hΦ := Φ.mem_iff (e.symm (z + p)) hys (by
      change e (e.symm (z + p)) ∈ Φ.Φ.source
      rw [hchart]
      exact hzΦ)
    have hΨ := Ψ.mem_iff (e.symm (z + p)) hys (by
      change e (e.symm (z + p)) ∈ Ψ.Φ.source
      rw [hchart]
      exact hzΨ)
    have hh := hΦ.symm.trans hΨ
    change Φ.Φ.toFun (e (e.symm (z + p))) (Fin.last m) = 0 ↔
      Ψ.Φ.toFun (e (e.symm (z + p))) (Fin.last m) = 0 at hh
    rwa [hchart] at hh
  obtain ⟨σ, hσ, _⟩ := exists_unique_coordinate_branch_equiv Φ.Φ Ψ.Φ
    Φ.map_center Ψ.map_center {Fin.last m} {Fin.last m}
    (by simpa only [Finset.mem_singleton, exists_eq_left] using hzero)
  let i : ({Fin.last m} : Finset (Fin (m + 1))) := ⟨Fin.last m, by simp⟩
  have hσlast : (σ i).val = Fin.last m := by simpa only [Finset.mem_singleton] using (σ i).property
  have h := hσ i
  simpa only [divisorEquationGerm, i, hσlast] using h

/-- Every germ, including zero, has the same order in both actual flattenings. -/
theorem normalOrder_independent (Φ Ψ : DivisorFlattening (m := m) E y)
    (g : HolGerm (ComplexModel (m + 1))) : normalOrder Φ g = normalOrder Ψ g :=
  emultiplicity_eq_of_associated_left (associated_divisorEquationGerm Φ Ψ).symm

theorem normalOrder_mul (Φ : DivisorFlattening (m := m) E y)
    (g h : HolGerm (ComplexModel (m + 1))) :
    normalOrder Φ (g * h) = normalOrder Φ g + normalOrder Φ h :=
  emultiplicity_mul (prime_divisorEquationGerm Φ)

theorem normalOrder_zero (Φ : DivisorFlattening (m := m) E y) : normalOrder Φ 0 = ⊤ :=
  emultiplicity_zero _

theorem normalOrder_unit (Φ : DivisorFlattening (m := m) E y)
    {g : HolGerm (ComplexModel (m + 1))} (hg : IsUnit g) : normalOrder Φ g = 0 :=
  emultiplicity_of_isUnit_right (prime_divisorEquationGerm Φ).not_isUnit hg

/-- Finiteness follows from actual germ factoriality; it is not an input. -/
theorem normalOrder_ne_top (Φ : DivisorFlattening (m := m) E y)
    {g : HolGerm (ComplexModel (m + 1))} (hg : g ≠ 0) : normalOrder Φ g ≠ ⊤ := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  exact finiteMultiplicity_iff_emultiplicity_ne_top.mp
    (FiniteMultiplicity.of_prime_left (prime_divisorEquationGerm Φ) hg)

/-- The infimum over the ENTIRE actual local ideal, independent of generators. -/
def idealNormalOrder (Φ : DivisorFlattening (m := m) E y)
    (I : Ideal (HolGerm (ComplexModel (m + 1)))) : ℕ∞ := ⨅ g : I, normalOrder Φ g.val

theorem natCast_le_idealNormalOrder_iff (Φ : DivisorFlattening (m := m) E y)
    (I : Ideal (HolGerm (ComplexModel (m + 1)))) (k : ℕ) :
    (k : ℕ∞) ≤ idealNormalOrder Φ I ↔ I ≤ Ideal.span {divisorEquationGerm Φ ^ k} := by
  rw [idealNormalOrder, le_iInf_iff]
  constructor
  · intro h g hg
    exact Ideal.mem_span_singleton.mpr
      (pow_dvd_iff_le_emultiplicity.mpr (h ⟨g, hg⟩))
  · intro h g
    exact pow_dvd_iff_le_emultiplicity.mp (Ideal.mem_span_singleton.mp (h g.property))

/-- The actual full generating family computes the whole-ideal order, including empty families. -/
theorem idealNormalOrder_span (Φ : DivisorFlattening (m := m) E y)
    {ι : Type*} (g : ι → HolGerm (ComplexModel (m + 1))) :
    idealNormalOrder Φ (Ideal.span (range g)) = ⨅ i, normalOrder Φ (g i) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  rw [natCast_le_idealNormalOrder_iff, Ideal.span_le, Set.range_subset_iff, le_iInf_iff]
  constructor
  · intro h i
    exact pow_dvd_iff_le_emultiplicity.mp (Ideal.mem_span_singleton.mp (h i))
  · intro h i
    exact Ideal.mem_span_singleton.mpr (pow_dvd_iff_le_emultiplicity.mpr (h i))

theorem idealNormalOrder_independent (Φ Ψ : DivisorFlattening (m := m) E y)
    (I : Ideal (HolGerm (ComplexModel (m + 1)))) :
    idealNormalOrder Φ I = idealNormalOrder Ψ I := by
  exact iInf_congr fun g => normalOrder_independent Φ Ψ g.val

section OriginalFunctions

variable [IsComplexManifold (m + 1) Y]

/-- The original complete stalk is read through the actual translated preferred chart. -/
def originalStalkNormalOrder (Φ : DivisorFlattening (m := m) E y) (A : GermIdeal (m + 1) Y) : ℕ∞ :=
  idealNormalOrder Φ (wholeChartStalkIdeal A y y (mem_chart_source _ y))

/-- Only local holomorphy of this representative is required. -/
def functionNormalOrder (Φ : DivisorFlattening (m := m) E y) (f : Y → ℂ)
    (hf : HolomorphicAt (m + 1) f y) : ℕ∞ :=
  normalOrder Φ (chartTranslatedGerm y y (mem_chart_source _ y) f hf)

theorem originalStalkNormalOrder_eq_generators (Φ : DivisorFlattening (m := m) E y)
    (A : GermIdeal (m + 1) Y) {N : ℕ} (G : Fin N → Y → ℂ)
    (hG : ∀ i, HolomorphicAt (m + 1) (G i) y)
    (hgen : ∀ f, A.mem y f ↔ IsInSpanAt (n := m + 1) (· ∈ range G) y f) :
    originalStalkNormalOrder Φ A = ⨅ i, functionNormalOrder Φ (G i) (hG i) := by
  unfold originalStalkNormalOrder
  rw [HironakaSmoothCentreNearbyStalks.wholeChartStalkIdeal_eq_span_of_original_generators
    A y y (mem_chart_source _ y) G hG hgen, idealNormalOrder_span]
  rfl

/-- Equality of the original local representatives is enough; values outside their germ do not enter. -/
theorem functionNormalOrder_congr (Φ : DivisorFlattening (m := m) E y)
    {f g : Y → ℂ} (hf : HolomorphicAt (m + 1) f y) (hg : HolomorphicAt (m + 1) g y)
    (hfg : f =ᶠ[𝓝 y] g) : functionNormalOrder Φ f hf = functionNormalOrder Φ g hg := by
  apply congrArg (normalOrder Φ)
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := chartAt (ComplexModel (m + 1)) y
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e y) (𝓝 0) (𝓝 (e y)) := by
    simpa only [zero_add] using (continuous_add_const (e y)).tendsto 0
  have hInv : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e y)) (𝓝 0) (𝓝 y) := by
    simpa only [Function.comp_def, e.left_inv (mem_chart_source _ y)] using
      (e.continuousAt_symm (e.map_source (mem_chart_source _ y))).tendsto.comp ht
  exact hInv.eventually hfg

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- Literal pullback of a germ at the ACTUAL point pi(y); no whole-source holomorphy. -/
def pullbackNormalOrder {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ : DivisorFlattening (m := m) E y) (f : X → ℂ)
    (hf : HolomorphicAt (m + 1) f (π y)) : ℕ∞ :=
  functionNormalOrder Φ (f ∘ π)
    (hf.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt))

theorem pullbackNormalOrder_independent {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ Ψ : DivisorFlattening (m := m) E y) (f : X → ℂ)
    (hf : HolomorphicAt (m + 1) f (π y)) :
    pullbackNormalOrder hπ Φ f hf = pullbackNormalOrder hπ Ψ f hf :=
  normalOrder_independent Φ Ψ _

theorem pullbackNormalOrder_congr {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (Φ : DivisorFlattening (m := m) E y) {f g : X → ℂ}
    (hf : HolomorphicAt (m + 1) f (π y)) (hg : HolomorphicAt (m + 1) g (π y))
    (hfg : f =ᶠ[𝓝 (π y)] g) : pullbackNormalOrder hπ Φ f hf = pullbackNormalOrder hπ Φ g hg := by
  apply functionNormalOrder_congr
  exact hπ.1.continuous.continuousAt.tendsto.eventually hfg

end OriginalFunctions
end LocalPrime

section ActualJacobianUnits

open HolomorphicGermJacobian

variable {n : ℕ}

private theorem holomorphic_comp_vector (F G : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G ∘ F) z := by
  have ht : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hF0] using hF.self_of_nhds.continuousAt.tendsto
  filter_upwards [hF, ht.eventually hG] with z hf hg
  exact hg.comp z hf

/-- The actual inverse differentiates to a Jacobian unit; no unit certificate is supplied. -/
theorem jacobianGerm_isUnit_of_actual_equiv
    (Ξ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) :
    IsUnit (jacobianGerm Ξ.toFun (local_toFun_holomorphic Ξ)) := by
  obtain ⟨hJ, _hJinv, hJ0, _hJinv0⟩ :=
    LocalHolomorphicMultiplierGermCovariance.jacobian_units_of_local_holomorphic_equiv Ξ
  have heq : jacobianGerm Ξ.toFun (local_toFun_holomorphic Ξ) =
      HolGerm.mk (DivisorialChangeOfVariables.complexJacobian Ξ.toFun) hJ := by
    apply Subtype.ext
    exact jacobianGerm_source Ξ.toFun (local_toFun_holomorphic Ξ)
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  rw [heq, HolGerm.eval_mk]
  exact hJ0

/-- Genuine target-coordinate units preserve the ENTIRE Jacobian order, including zero/infinity. -/
theorem emultiplicity_jacobian_comp_target (p : HolGerm (ComplexModel n))
    (F : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (Ξ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) :
    emultiplicity p (jacobianGerm (Ξ.toFun ∘ F)
      (holomorphic_comp_vector F Ξ.toFun hF hF0 (local_toFun_holomorphic Ξ))) =
      emultiplicity p (jacobianGerm F hF) := by
  rw [jacobianGerm_comp F Ξ.toFun hF hF0 (local_toFun_holomorphic Ξ)]
  exact emultiplicity_eq_of_associated_right (associated_unit_mul_left _ _
    ((jacobianGerm_isUnit_of_actual_equiv Ξ).map (compAlgHom F hF hF0).toRingHom))

/-- Genuine source-coordinate units and the INTERNALLY built full germ equivalence
transport the actual equation and Jacobian together, including identically zero Jacobians. -/
theorem emultiplicity_jacobian_comp_source (p : HolGerm (ComplexModel n))
    (F : ComplexModel n → ComplexModel n)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z)
    (Ξ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΞ0 : Ξ.toFun 0 = 0) :
    emultiplicity (localGermAlgEquiv Ξ hΞ0 p)
      (jacobianGerm (F ∘ Ξ.toFun)
        (holomorphic_comp_vector Ξ.toFun F (local_toFun_holomorphic Ξ) hΞ0 hF)) =
      emultiplicity p (jacobianGerm F hF) := by
  rw [jacobianGerm_comp Ξ.toFun F (local_toFun_holomorphic Ξ) hΞ0 hF]
  calc
    _ = emultiplicity (localGermAlgEquiv Ξ hΞ0 p)
        (localGermAlgEquiv Ξ hΞ0 (jacobianGerm F hF)) :=
      emultiplicity_eq_of_associated_right (associated_mul_unit_left _ _
        (jacobianGerm_isUnit_of_actual_equiv Ξ))
    _ = _ := emultiplicity_map_eq (localGermAlgEquiv Ξ hΞ0)

end ActualJacobianUnits
end SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder
