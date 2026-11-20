import SGPT.PSH.HermitianProductsSmoothExpansion
import SGPT.PSH.HermitianProductsLocality
import SGPT.PSH.HermitianProductsDistinguishedSlot
import SGPT.PSH.HermitianProductsBaseAdditivity
import SGPT.PSH.HermitianComparisonOneFactor

/-! The genuine distinguished-factor difference of the actual Hermitian
products. The common residual contribution of the new factor cancels. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorCollar LocalBedfordTaylorContinuity LocalBedfordTaylorLocality
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorWedgeAssociation
  ConstantFormProducts TopDegreeDensity NormalDirectionVanishing
open HermitianComparisonOneFactor HermitianComparisonWeights

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Wedging a fixed smooth form is additive on finite families of arbitrary
currents, including signed nonclosed currents. -/
theorem wedgeForm_sum_current {r k m : ℕ} (h : r+k=m) {ι : Type*} [Fintype ι]
    (T : ι → LocalProductCurrent n U m)
    {α : ComplexModel n → RealForm n (2*k)} (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm h (∑ i, T i) hα = ∑ i, wedgeForm h (T i) hα := by
  classical
  ext γ φ
  simp only [wedgeForm_apply, LinearMap.sum_apply, _root_.sum_apply]
  exact Finset.sum_comm

/-- The actual unit Borel weight is multiplication by one on the current's
original domain. Off-domain ambient values play no role. -/
theorem mulBorel_indicator_one {q : ℕ} {T : LocalProductCurrent n U q}
    (hT : IsPositive T) :
    mulBorel T ((U : Set (ComplexModel n)).indicator (fun _ => (1 : ℝ))) = T := by
  have him : Measurable ((U : Set (ComplexModel n)).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator U.isOpen.measurableSet
  have hib : IsLocallyBoundedOn ((U : Set (ComplexModel n)).indicator
      (fun _ => (1 : ℝ))) U := by
    intro K _ hKU
    refine ⟨1, fun x hx => ?_⟩
    rw [indicator_of_mem (hKU hx)]
    norm_num
  have he := mulBorel_congr hT him hib measurable_const
    (fun K _ _ => ⟨1, by intros; simp⟩) (fun x hx => indicator_of_mem hx _)
  rw [he, mulBorel_const hT, one_smul]

/-- A smooth distinguished PSH slot is the same literal smooth wedge,
with multiplication by the actual unit performed on its positive current. -/
theorem weightedDdcResidual_one_smooth {k : ℕ}
    (R : LocalProductCurrent n U (k+1)) (hR : IsPositive R) (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2*k)} (hα : ContDiffOn ℝ ∞ α U)
    {u a b : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn U u)
    (hus : ContDiffOn ℝ ∞ u U) :
    weightedDdcResidual R hα u a b (fun _ => 1) =
      wedgeForm (r := 0) (k := 1) rfl
        (wedgeForm (by omega : 1+k=k+1) R hα) (contDiffOn_ddcForm hus) := by
  unfold weightedDdcResidual
  rw [mulBorel_indicator_one (isPositive_ddcMul hR hRc hu).1,
    ddcMul_eq_ddcWedge hR hRc hus, ddcWedge_eq_wedgeForm]
  exact (wedgeForm_exchange_one R hα (contDiffOn_ddcForm hus)).symm

/-- The actual finite residual presentation with a smooth distinguished
factor reads the original complete mixed current against its full Hessian. -/
theorem weightedDifference_one_smooth {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn U a) (hb : IsLocallyBoundedPshOn U b)
    (has : ContDiffOn ℝ ∞ a U) (hbs : ContDiffOn ℝ ∞ b U) :
    weightedDifference D a b (fun _ => 1) =
      wedgeForm (r := 0) (k := 1) rfl (mixedCurrent D) (contDiffOn_ddcForm hbs) -
      wedgeForm (r := 0) (k := 1) rfl (mixedCurrent D) (contDiffOn_ddcForm has) := by
  classical
  unfold weightedDifference
  have hbe (i : ι) := weightedDdcResidual_one_smooth (D i).current (D i).positive
    (D i).closed (D i).smooth (u := b) (a := a) (b := b) hb hbs
  have hae (i : ι) := weightedDdcResidual_one_smooth (D i).current (D i).positive
    (D i).closed (D i).smooth (u := a) (a := a) (b := b) ha has
  simp_rw [hbe, hae]
  rw [mixedCurrent, wedgeForm_sum_current, wedgeForm_sum_current]
  rw [Finset.sum_sub_distrib]
  rfl

/-- The complete smooth product with a distinguished first slot reads the
actual remaining Hermitian product against the full new one-one factor. -/
theorem backgroundExpansion_cons_smooth (p : ℕ)
    (T : LocalProductCurrent n U (1+p)) (hT : IsPositive T) (hTc : IsClosedAny (1+p) T)
    (v : Fin p → ComplexModel n → ℝ)
    (hvs : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {a : ComplexModel n → ℝ} (has : ContDiffOn ℝ ∞ a U)
    (hap : PlurisubharmonicOn (fun z => (a z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (p+1) 0 (Fin.cons a v) hσ
        (castLPC (by omega : 1+p=0+(p+1)) T) =
      wedgeForm (r := 0) (k := 1) rfl (backgroundExpansion p 1 v hσ T)
        ((contDiffOn_ddcForm has).add hσ) := by
  classical
  have hws (i : Fin (p+1)) : ContDiffOn ℝ ∞ ((Fin.cons a v : Fin (p+1) → ComplexModel n → ℝ) i) U := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact has
    · exact hvs i
  have hwp (i : Fin (p+1)) :
      PlurisubharmonicOn (fun z => ((Fin.cons a v : Fin (p+1) → ComplexModel n → ℝ) i z : EReal)) U := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hap
    · exact hvp i
  let hr := contDiffOn_wedgeProd p (fun i z => ddcForm (v i) z + σ z)
    (fun i => (contDiffOn_ddcForm (hvs i)).add hσ)
  have hrS : ∀ z ∈ U,
      wedgeProd p (fun i => ddcForm (v i) z + σ z) ∈ formSpan n p := by
    intro z hz
    apply wedgeProd_mem_formSpan
    intro i
    exact (formSpan n 1).add_mem
      (ddcForm_mem_formSpan (hvs i)
        (fun y hy d => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (hvs i) (hvp i) hy d) z hz)
      (hσS z hz)
  have haS : ∀ z ∈ U, ddcForm a z + σ z ∈ formSpan n 1 := by
    intro z hz
    exact (formSpan n 1).add_mem
      (ddcForm_mem_formSpan has
        (fun y hy d => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn has hap hy d) z hz)
      (hσS z hz)
  rw [backgroundExpansion_smooth (p+1) 0 _ hws hwp hσ hσS _
      (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc),
    backgroundExpansion_smooth p 1 v hvs hvp hσ hσS T hT hTc]
  rw [wedgeForm_wedge_two (r := 0) rfl T hr ((contDiffOn_ddcForm has).add hσ) hrS haS]
  rw [wedgeForm_castLPC (by omega : 1+p=0+(p+1)) (by omega : 0+(p+1)=1+p)]
  apply wedgeForm_congr
  intro z _
  have ht : (fun i => ddcForm ((Fin.cons a v : Fin (p+1) → ComplexModel n → ℝ) i) z + σ z) =
      Fin.cons (ddcForm a z + σ z) (fun i => ddcForm (v i) z + σ z) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  change wedgeProd (p+1) (fun i => ddcForm ((Fin.cons a v : Fin (p+1) → ComplexModel n → ℝ) i) z + σ z) = _
  rw [ht, ← wedgeProd_snoc_eq_cons, wedgeProd_snoc]

/-- Smooth distinguished-factor transgression for the literal expansion.
The residual part of the distinguished factor cancels exactly. -/
theorem backgroundExpansion_transgression_smooth (p : ℕ)
    (T : LocalProductCurrent n U (1+p)) (hT : IsPositive T) (hTc : IsClosedAny (1+p) T)
    (v : Fin p → ComplexModel n → ℝ)
    (hvs : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {a b : ComplexModel n → ℝ} (has : ContDiffOn ℝ ∞ a U) (hbs : ContDiffOn ℝ ∞ b U)
    (hap : PlurisubharmonicOn (fun z => (a z : EReal)) U)
    (hbp : PlurisubharmonicOn (fun z => (b z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    backgroundExpansion (p+1) 0 (Fin.cons b v) hσ (castLPC (by omega) T) -
      backgroundExpansion (p+1) 0 (Fin.cons a v) hσ (castLPC (by omega) T) =
      weightedDifference (backgroundResidual p T hT hTc v
        (fun i => locallyBoundedPshOn_of_smooth (hvs i) (hvp i)) hσ) a b (fun _ => 1) := by
  rw [backgroundExpansion_cons_smooth p T hT hTc v hvs hvp hbs hbp hσ hσS,
    backgroundExpansion_cons_smooth p T hT hTc v hvs hvp has hap hσ hσS,
    wedgeForm_add rfl _ (contDiffOn_ddcForm hbs) hσ,
    wedgeForm_add rfl _ (contDiffOn_ddcForm has) hσ,
    weightedDifference_one_smooth _ (locallyBoundedPshOn_of_smooth has hap)
      (locallyBoundedPshOn_of_smooth hbs hbp) has hbs,
    mixedCurrent_backgroundResidual]
  abel

end SGPT.PSH.HermitianProducts
