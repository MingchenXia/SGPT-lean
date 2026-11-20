import SGPT.Unibranch.PrimeNov16AnalyticNormalizationDenominatorGraph
import SGPT.Unibranch.AnalyticParametrizationFiniteFibers

/-! Actual monic equations extend to the ENTIRE literal graph closure;
entire original fibres are then finite, including H=0 and discriminants.
Blueprint: prime-nov16-analytic-normalization-graph-finite.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphFinite
open PrimeNov16AnalyticNormalizationDenominatorGraph

private theorem coefficient_continuous {n k : ℕ} (U : Opens (ComplexModel n))
    {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Continuous (fun z : wideDomain k U => f (baseProjection n k z.val)) :=
  hf.continuousOn.comp_continuous
    ((baseProjection n k).continuous.comp continuous_subtype_val) (fun z => z.property)

/-- Continuity of the ACTUAL polynomial on the WHOLE wide ambient domain. -/
private theorem monic_continuous {n k : ℕ} (U : Opens (ComplexModel n))
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U) (i : Fin k) :
    Continuous (fun z : wideDomain k U => monicEval (d i) (a i)
      (baseProjection n k z.val) (fibreProjection n k z.val i)) := by
  have hw : Continuous (fun z : wideDomain k U => fibreProjection n k z.val i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp
      ((fibreProjection n k).continuous.comp continuous_subtype_val)
  exact (hw.pow (d i)).add (continuous_finsetSum (Finset.range (d i)) fun j hj =>
    (coefficient_continuous U (ha i j (Finset.mem_range.mp hj))).mul (hw.pow j))

/-- The SAME spread equations extend by closedness from the actual graph to
its ENTIRE closure. No desired whole-closure equation is an input. -/
theorem monic_on_graphClosure {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    {z : wideDomain k U} (hz : z ∈ graphClosure U C H G) (i : Fin k) :
    monicEval (d i) (a i) (baseProjection n k z.val) (fibreProjection n k z.val i) = 0 := by
  have hclosed : IsClosed {z : wideDomain k U | monicEval (d i) (a i)
      (baseProjection n k z.val) (fibreProjection n k z.val i) = 0} :=
    isClosed_eq (monic_continuous U d a ha i) continuous_const
  apply closure_minimal (s := rationalGraph U C H G) _ hclosed hz
  intro w hw
  have hD := (mem_denominatorSet U C H G w).mp hw.1
  have hH : H (baseProjection n k w.val) ≠ 0 := fun he => hw.2 ((mem_badSet U H w).mpr he)
  have hcoord : fibreProjection n k w.val i = G i (baseProjection n k w.val)/H (baseProjection n k w.val) :=
    (eq_div_iff hH).mpr ((mul_comm _ _).trans (hD.2 i))
  change monicEval (d i) (a i) (baseProjection n k w.val) (fibreProjection n k w.val i) = 0
  rw [hcoord]
  exact hmonic ⟨basePoint U w,hD.1⟩ hH i

/-- Actual linear coordinates jointly separate EVERY ambient point. -/
theorem coordinates_injective {n k : ℕ} {v w : ComplexModel (n+k)}
    (hb : baseProjection n k v = baseProjection n k w)
    (hf : fibreProjection n k v = fibreProjection n k w) : v = w := by
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)).injective
  exact Prod.ext hb hf

/-- Whole base fibre of the SAME actual closure is finite. No simple-root,
positive-degree, denominator-nonzero or normal-source assumption is needed. -/
theorem graphClosure_base_fibre_finite {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0) (x : U) :
    {c : graphClosure U C H G | basePoint U c.val = x}.Finite := by
  classical
  let choices : Fin k → Set ℂ := fun i => {t | monicEval (d i) (a i) x.val t = 0}
  let choicesFintype (i : Fin k) : Fintype (choices i) :=
    (AnalyticParametrization.monicEval_zeroSet_finite (d i) (a i) x.val).fintype
  let F := {c : graphClosure U C H G | basePoint U c.val = x}
  let lift : F → ∀ i : Fin k,choices i := fun c i => ⟨fibreProjection n k c.val.val.val i,by
    have h := monic_on_graphClosure U H G d a ha hmonic c.val.property i
    have hb := congrArg Subtype.val c.property
    change baseProjection n k c.val.val.val = x.val at hb
    rw [hb] at h
    exact h⟩
  have hlift : Function.Injective lift := by
    intro c e he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply coordinates_injective
    · exact (congrArg Subtype.val c.property).trans (congrArg Subtype.val e.property).symm
    · ext i
      exact congrArg Subtype.val (congrFun he i)
  have : Finite F := Finite.of_injective lift hlift
  exact Set.toFinite _

/-- Literal original morphism point-map readback, retaining full carrier values. -/
theorem projection_apply {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (c : graphClosure U C H G) :
    ((projection U hC H G hH hG).hom.left.base c).val = basePoint U c.val := rfl

/-- EVERY fibre of the actual original SHEAF morphism is finite. -/
theorem projection_fibres_finite {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    (x : (sourceReducedComplexSpaceModel U C hC).obj.left) :
    ((projection U hC H G hH hG).hom.left.base ⁻¹' {x}).Finite := by
  apply (graphClosure_base_fibre_finite U H G d a ha hmonic x.val).subset
  intro c hc
  have he := congrArg Subtype.val hc
  exact he

/-- Actual scalar Cauchy bounds at EVERY point of the SAME graph closure. -/
theorem coordinate_bound_on_graphClosure {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    {z : wideDomain k U} (hz : z ∈ graphClosure U C H G) (i : Fin k) :
    ‖fibreProjection n k z.val i‖ ≤ max 1 (∑ j ∈ Finset.range (d i),‖a i j (baseProjection n k z.val)‖) :=
  GermIntegrallyClosed.norm_le_of_monic_root (monic_on_graphClosure U H G d a ha hmonic hz i)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphFinite
