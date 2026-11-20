import SGPT.Foundations.Analysis.GermPshLeviPositivity
import SGPT.Foundations.Analysis.PositiveDistributionMeasure
import SGPT.Foundations.Analysis.SmoothDistribution
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality

set_option autoImplicit false

/-! # Actual transverse marginals of directional Levi measures

Independent slicing precursor for the codimension-two mass-nullity step
of Boucksom 2.5.  All marginals come from the actual positive directional
Levi distribution of the original psh potential, not an assumed density.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian

namespace SGPT.Foundations.Analysis.Pending.ActualDirectionalLeviMarginal

open FirstPass

variable {m : ℕ} {U : Opens ℂ} {V : Opens (ComplexModel m)}

private def rectangle (U : Opens ℂ) (V : Opens (ComplexModel m)) :
    Opens (ℂ × ComplexModel m) := ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩

private instance product_volume_isAddHaar :
    (volume : Measure (ℂ × ComplexModel m)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod, ← (stdOrthonormalBasis ℝ ℂ).addHaar_eq_volume,
    ← (stdOrthonormalBasis ℝ (ComplexModel m)).addHaar_eq_volume,
    ← Module.Basis.prod_addHaar]
  infer_instance

private theorem tsupport_product_subset (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ)) :
    tsupport (fun x : ℂ × ComplexModel m => β x.1 * γ x.2) ⊆ tsupport β ×ˢ tsupport γ := by
  apply closure_minimal _ ((isClosed_tsupport β).prod (isClosed_tsupport γ))
  intro x hx
  have h := mul_ne_zero_iff.mp hx
  exact ⟨subset_tsupport β h.1, subset_tsupport γ h.2⟩

private def productTest (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ)) : 𝓓(rectangle U V, ℝ) where
  toFun x := β x.1 * γ x.2
  contDiff' := (β.contDiff.comp contDiff_fst).mul (γ.contDiff.comp contDiff_snd)
  hasCompactSupport' := (β.hasCompactSupport.prod γ.hasCompactSupport).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_product_subset β γ)
  tsupport_subset' := (tsupport_product_subset β γ).trans
    (Set.prod_mono β.tsupport_subset γ.tsupport_subset)

private theorem productTest_apply (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ))
    (x : ℂ × ComplexModel m) : productTest β γ x = β x.1 * γ x.2 := rfl

private theorem firstDerivative_productTest (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ)) (v : ℂ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (v, (0 : ComplexModel m)) (productTest β γ) =
      productTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v β) γ := by
  apply TestFunction.ext
  intro x
  have hβ := (β.contDiff.differentiable (by simp) x.1).hasFDerivAt
  have hγ := (γ.contDiff.differentiable (by simp) x.2).hasFDerivAt
  have hp := (hβ.comp x hasFDerivAt_fst).mul (hγ.comp x hasFDerivAt_snd)
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp), productTest_apply,
    TestFunction.lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ ((β : ℂ → ℝ) ∘ Prod.fst * (γ : ComplexModel m → ℝ) ∘ Prod.snd)
    x (v, (0 : ComplexModel m)) = lineDeriv ℝ (β : ℂ → ℝ) x.1 v * γ x.2
  rw [hp.hasLineDerivAt (v, (0 : ComplexModel m)) |>.lineDeriv,
    hβ.hasLineDerivAt v |>.lineDeriv]
  simp [mul_comm]

private def firstLeviTest (β : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  (1 / 4 : ℝ) •
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ)
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ) β) +
      TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I β))

private theorem firstLeviTest_apply (β : 𝓓(U, ℝ)) (s : ℂ) :
    firstLeviTest β s = leviForm β s (1 : ℂ) := by
  have h2 : ContDiff ℝ 2 (β : ℂ → ℝ) := β.contDiff.of_le ENat.LEInfty.out
  have hdd (v : ℂ) : TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v β) s = realHessian β s v v := by
    rw [testFunction_lineDerivCLM_apply_eq_fderiv]
    have hfun : (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v β : ℂ → ℝ) =
        fun x => fderiv ℝ β x v :=
      funext fun x => testFunction_lineDerivCLM_apply_eq_fderiv β v x
    rw [hfun, fderiv_fderiv_apply_eq_realHessian h2]
  simp only [firstLeviTest, _root_.smul_apply, _root_.add_apply, smul_eq_mul,
    hdd, leviForm, smul_eq_mul, mul_one]
  ring

private theorem directionalLevi_productTest (T : 𝓓'(rectangle U V, ℝ))
    (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ)) :
    distributionalLeviCLM (1, (0 : ComplexModel m)) T (productTest β γ) =
      T (productTest (firstLeviTest β) γ) := by
  rw [distributionalLeviCLM_apply]
  have hI : Complex.I • (1, (0 : ComplexModel m)) = (Complex.I, (0 : ComplexModel m)) := by
    simp
  rw [hI]
  simp_rw [firstDerivative_productTest]
  have hproduct : productTest (firstLeviTest β) γ = (1 / 4 : ℝ) •
      (productTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ)
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ) β)) γ +
       productTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I β)) γ) := by
    apply TestFunction.ext
    intro x
    simp only [productTest_apply, firstLeviTest, _root_.smul_apply, _root_.add_apply,
      smul_eq_mul]
    ring
  rw [hproduct, map_smul, map_add]
  rfl

private theorem levi_regular_product_integral
    {f : ℂ × ComplexModel m → ℝ}
    (hf : LocallyIntegrableOn f (rectangle U V) volume)
    (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ)) :
    distributionalLeviCLM (1, (0 : ComplexModel m)) (regularDistribution volume f hf)
        (productTest β γ) =
      ∫ y, γ y * (∫ s, firstLeviTest β s * f (s, y)) := by
  rw [directionalLevi_productTest, regularDistribution_apply]
  have hint := (productTest (firstLeviTest β) γ).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℝ) hf
  change Integrable (fun x : ℂ × ComplexModel m => productTest (firstLeviTest β) γ x * f x)
    volume at hint
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [productTest_apply]
  ring

private theorem exists_directional_measure
    {f : ℂ × ComplexModel m → EReal} (hf : PlurisubharmonicOn f (rectangle U V))
    (hΩ : IsPreconnected ((rectangle U V) : Set (ℂ × ComplexModel m)))
    (hne : ∃ a ∈ rectangle U V, f a ≠ ⊥) :
    ∃ ν : Measure (rectangle U V), ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : 𝓓(rectangle U V, ℝ), (∫ x : rectangle U V, φ x ∂ν) =
        distributionalLeviCLM (1, (0 : ComplexModel m))
          (pshRegularDistribution hf volume hΩ hne) φ := by
  exact (hf.pshRegularDistribution_hasNonnegativeDistributionalLevi hΩ hne
    (μ := volume) (1, (0 : ComplexModel m))).exists_regular_measure

/-- The original unbounded psh potential produces an actual directional measure
and every signed compact product test has its genuine classical fibre integral. -/
theorem exists_directional_measure_and_fibre_integrals
    (U : Opens ℂ) (V : Opens (ComplexModel m)) (f : ℂ × ComplexModel m → EReal)
    (hf : PlurisubharmonicOn f ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hΩ : IsPreconnected ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hne : ∃ a ∈ ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))), f a ≠ ⊥) :
    let Ω : Opens (ℂ × ComplexModel m) :=
      ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      (∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) =
        distributionalLeviCLM (1, (0 : ComplexModel m))
          (pshRegularDistribution hf volume hΩ hne) φ) ∧
      ∀ (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ)),
        (∫ x : Ω, β x.val.1 * γ x.val.2 ∂ν) =
          ∫ y, γ y * (∫ s, leviForm β s (1 : ℂ) * (f (s, y)).toReal) := by
  obtain ⟨ν, hreg, hloc, hrep⟩ := exists_directional_measure hf hΩ hne
  refine ⟨ν, hreg, hloc, hrep, ?_⟩
  intro β γ
  change (∫ x : rectangle U V, productTest β γ x ∂ν) = _
  rw [hrep]
  change distributionalLeviCLM (1, (0 : ComplexModel m))
    (regularDistribution volume (fun x => (f x).toReal)
      (hf.locallyIntegrableOn_toReal volume hΩ hne)) (productTest β γ) = _
  have hfL : LocallyIntegrableOn (fun x => (f x).toReal) (rectangle U V) volume :=
    hf.locallyIntegrableOn_toReal volume hΩ hne
  have ht := levi_regular_product_integral hfL β γ
  simp_rw [firstLeviTest_apply] at ht
  exact ht

end SGPT.Foundations.Analysis.Pending.ActualDirectionalLeviMarginal
