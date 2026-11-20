import SGPT.PSH.HermitianBackground
import SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Hermitian backgrounds on compact complex manifolds

Supported flat coordinate forms extend to actual global smooth forms.
A finite sum of semipositive pieces positive on a covering gives a
Hermitian form. No closedness is asserted or needed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Hermitian

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open NaturalSupportedChartFormExtension KahlerDomination ChartPartition
open scoped Topology ContDiff Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Holomorphic chart changes have injective real derivatives on their
actual overlap: differentiating the inverse identity proves this directly. -/
theorem chartTransitionDerivative_injective (e f : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ (chartTransition e f).source) :
    Function.Injective (chartTransitionDerivative e f z) := by
  let F := chartTransition e f
  let G := chartTransition f e
  have hzG : F z ∈ G.source := by
    refine ⟨f.val.map_source hz.2, ?_⟩
    change f.val.symm (f.val (e.val.symm z)) ∈ e.val.source
    have hf : f.val.symm (f.val (e.val.symm z)) = e.val.symm z :=
      f.val.left_inv (show e.val.symm z ∈ f.val.source from hz.2)
    rw [hf]
    exact e.val.map_target hz.1
  have heq : G ∘ F =ᶠ[𝓝 z] id := by
    filter_upwards [F.open_source.mem_nhds hz] with y hy
    change e.val (f.val.symm (f.val (e.val.symm y))) = y
    have hf : f.val.symm (f.val (e.val.symm y)) = e.val.symm y :=
      f.val.left_inv (show e.val.symm y ∈ f.val.source from hy.2)
    rw [hf, e.val.right_inv hy.1]
  have hder : (fderiv ℝ G (F z)).comp (fderiv ℝ F z) =
      ContinuousLinearMap.id ℝ (ComplexModel n) := by
    rw [← fderiv_comp z
      ((chartTransition_contDiffAt_real f e hzG).differentiableAt (by simp))
      ((chartTransition_contDiffAt_real e f hz).differentiableAt (by simp)),
      heq.fderiv_eq, fderiv_id]
  intro v w hvw
  have h := congrArg (fderiv ℝ G (F z)) hvw
  have hv := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L v) hder
  have hw := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L w) hder
  exact hv.symm.trans (h.trans hw)

/-- A supported coordinate multiple of the flat form, extended as a
genuine smooth form with the full tensor overlap law. -/
def supportedFlatForm (e : ComplexChart n M) (β : ComplexModel n → ℝ)
    (hβ : ContDiff ℝ ∞ β) (hc : IsCompact (tsupport β))
    (hs : tsupport β ⊆ e.val.target) : SmoothRealForm n M 2 :=
  extend e (fun z => β z • Kahler.fundamentalFormAlt)
    (hβ.smul contDiff_const)
    (hc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left β (fun _ => Kahler.fundamentalFormAlt)))
    ((tsupport_smul_subset_left β (fun _ => Kahler.fundamentalFormAlt)).trans hs)

theorem supportedFlatForm_isTypeOneOne (e : ComplexChart n M)
    (β : ComplexModel n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hc : IsCompact (tsupport β)) (hs : tsupport β ⊆ e.val.target) :
    (supportedFlatForm e β hβ hc hs).IsTypeOneOne := by
  intro f z _
  change IsOneOne (transportedCoeff e f (fun y => β y • Kahler.fundamentalFormAlt) z)
  by_cases ho : z ∈ (chartTransition f e).source
  · rw [transportedCoeff, indicator_of_mem ho]
    intro v w
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hpair (a b : ComplexModel n) :
        (⇑(chartTransitionDerivative f e z) ∘ ![a, b]) =
          ![chartTransitionDerivative f e z a, chartTransitionDerivative f e z b] := by
      funext i
      fin_cases i <;> rfl
    rw [hpair, hpair]
    rw [chartTransitionDerivative_complex_smul f e z ho Complex.I v,
      chartTransitionDerivative_complex_smul f e z ho Complex.I w,
      flatFundamentalForm_isOneOne n]
  · rw [transportedCoeff, indicator_of_notMem ho]
    intro v w
    rfl

theorem supportedFlatForm_isSemipositive (e : ComplexChart n M)
    (β : ComplexModel n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hc : IsCompact (tsupport β)) (hs : tsupport β ⊆ e.val.target)
    (hβ₀ : ∀ z, 0 ≤ β z) : (supportedFlatForm e β hβ hc hs).IsSemipositive := by
  intro f z _ v
  change 0 ≤ transportedCoeff e f (fun y => β y • Kahler.fundamentalFormAlt) z
    ![v, Complex.I • v]
  by_cases ho : z ∈ (chartTransition f e).source
  · rw [transportedCoeff, indicator_of_mem ho]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hv : (fun i => chartTransitionDerivative f e z (![v, Complex.I • v] i)) =
        ![chartTransitionDerivative f e z v,
          Complex.I • chartTransitionDerivative f e z v] := by
      funext i
      fin_cases i
      · rfl
      · exact chartTransitionDerivative_complex_smul f e z ho Complex.I v
    change 0 ≤ β (chartTransition f e z) * Kahler.fundamentalFormAlt
      (fun i => chartTransitionDerivative f e z (![v, Complex.I • v] i))
    rw [hv]
    apply mul_nonneg (hβ₀ _)
    by_cases hzero : chartTransitionDerivative f e z v = 0
    · simp [hzero]
    · exact (flatFundamentalForm_isStrictlyPositive n _ hzero).le
  · rw [transportedCoeff, indicator_of_notMem ho]
    exact le_rfl

theorem supportedFlatForm_strictlyPositive (e f : ComplexChart n M)
    (β : ComplexModel n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hc : IsCompact (tsupport β)) (hs : tsupport β ⊆ e.val.target)
    {z : ComplexModel n} (hz : z ∈ f.val.target)
    (he : f.val.symm z ∈ e.val.source)
    (hpos : 0 < β (e.val (f.val.symm z))) :
    IsStrictlyPositive ((supportedFlatForm e β hβ hc hs).coeff f z) := by
  intro v hv
  have ho : z ∈ (chartTransition f e).source := ⟨hz, he⟩
  change 0 < transportedCoeff e f (fun y => β y • Kahler.fundamentalFormAlt) z
    ![v, Complex.I • v]
  rw [transportedCoeff, indicator_of_mem ho]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hpair : (⇑(chartTransitionDerivative f e z) ∘ ![v, Complex.I • v]) =
      ![chartTransitionDerivative f e z v, Complex.I • chartTransitionDerivative f e z v] := by
    funext i
    fin_cases i
    · rfl
    · exact chartTransitionDerivative_complex_smul f e z ho Complex.I v
  rw [hpair]
  apply mul_pos hpos
  apply flatFundamentalForm_isStrictlyPositive n
  intro hzero
  apply hv
  apply chartTransitionDerivative_injective f e ho
  simpa using hzero

/-- A genuine global semipositive `(1,1)`-form is strictly positive near
any prescribed point. The supported coordinate form is produced internally. -/
theorem exists_semipositive_form_positive_near (x : M) :
    ∃ (a : SmoothRealForm n M 2) (U : Set M),
      a.IsTypeOneOne ∧ a.IsSemipositive ∧ IsOpen U ∧ x ∈ U ∧
      ∀ (e : ComplexChart n M) z, z ∈ e.val.target → e.val.symm z ∈ U →
        IsStrictlyPositive (a.coeff e z) := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  let Ω : Opens (ComplexModel n) := ⟨e.val.target, e.val.open_target⟩
  obtain ⟨β, hβ1, hβrange⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := Ω) isCompact_singleton (singleton_subset_iff.mpr (e.val.map_source hx))
  rw [nhdsSet_singleton] at hβ1
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hβ1
  let U : Set M := e.val.source ∩ e.val ⁻¹' V
  let a := supportedFlatForm e β β.contDiff β.hasCompactSupport β.tsupport_subset
  refine ⟨a, U, supportedFlatForm_isTypeOneOne _ _ _ _ _,
    supportedFlatForm_isSemipositive _ _ _ _ _ (fun z => (hβrange z).1),
    e.val.isOpen_inter_preimage hVo, ⟨hx, hzV⟩, ?_⟩
  intro f z hz hzU
  apply supportedFlatForm_strictlyPositive e f β β.contDiff
    β.hasCompactSupport β.tsupport_subset hz hzU.1
  rw [hVsub hzU.2]
  exact zero_lt_one

/-- Literal finite sums of smooth compatible tensors, without imposing
closedness or replacing forms by their diagonal values. -/
def finiteSumForm {ι : Type*} (s : Finset ι) (a : ι → SmoothRealForm n M 2) :
    SmoothRealForm n M 2 where
  coeff := fun e z => ∑ i ∈ s, (a i).coeff e z
  smooth := fun e => ContDiffOn.sum fun i _ => (a i).smooth e
  compatible := by
    intro e f z hz v
    simp only [ContinuousAlternatingMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (a i).compatible e f z hz v

/-- Every compact complex manifold admits an actual smooth positive
Hermitian background. Neither a metric nor a closed form is assumed. -/
theorem exists_background [CompactSpace M] : Nonempty (Background n M) := by
  classical
  choose a U hatype hapos hU hxU hstrict using
    (exists_semipositive_form_positive_near (n := n) (M := M))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨⟨finiteSumForm s a, ?_⟩⟩
  intro e z hz
  constructor
  · intro v w
    change (∑ i ∈ s, (a i).coeff e z) ![Complex.I • v, Complex.I • w] =
      (∑ i ∈ s, (a i).coeff e z) ![v, w]
    simp only [ContinuousAlternatingMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hatype i e z hz v w
  · intro v hv
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ (e.val.symm z)))
    obtain ⟨hxs, hxU⟩ := mem_iUnion.mp hx
    have hpos := hstrict x e z hz hxU v hv
    change 0 < (∑ i ∈ s, (a i).coeff e z) ![v, Complex.I • v]
    simp only [ContinuousAlternatingMap.sum_apply]
    exact hpos.trans_le (Finset.single_le_sum (fun i _ => hapos i e z hz v) hxs)

end SGPT.PSH.Hermitian
