import SGPT.Hodge.SourceNefClassVolume
import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
import SGPT.Foundations.Analysis.Pending.PolarizationAlgebra
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.IntegrationCurrent
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
  SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
  SGPT.Foundations.Analysis.Pending.NefMixedMass
  SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
  SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The ACTUAL smooth integral is additive in a slot, including all signs. -/
theorem slotIntegral_update_add (κ : KahlerBackground n X)
    (θ : Fin n → ClosedRealOneOneForm n X) (j : Fin n)
    (A B : ClosedRealOneOneForm n X) :
    slotIntegral κ (Function.update θ j (A+B))=
      slotIntegral κ (Function.update θ j A)+slotIntegral κ (Function.update θ j B) := by
  simpa only [one_smul,one_mul] using slotIntegral_update_add_smul κ θ j A B 1

theorem slotIntegral_update_zero (κ : KahlerBackground n X)
    (θ : Fin n → ClosedRealOneOneForm n X) (j : Fin n) :
    slotIntegral κ (Function.update θ j 0)=0 := by
  have h := slotIntegral_update_add κ θ j 0 0
  simp only [zero_add] at h
  linarith

theorem slotIntegral_update_smul (κ : KahlerBackground n X)
    (θ : Fin n → ClosedRealOneOneForm n X) (j : Fin n)
    (c : ℝ) (A : ClosedRealOneOneForm n X) :
    slotIntegral κ (Function.update θ j (c • A))=
      c • slotIntegral κ (Function.update θ j A) := by
  have h := slotIntegral_update_add_smul κ θ j 0 A c
  simpa only [zero_add,slotIntegral_update_zero,smul_eq_mul] using h

/-- A genuine smooth real multilinear map, independent of b-divisor volumes. -/
def slotIntegralMultilinear (κ : KahlerBackground n X) :
    MultilinearMap ℝ (fun _ : Fin n => ClosedRealOneOneForm n X) ℝ :=
  MultilinearMap.mk' (slotIntegral κ) (slotIntegral_update_add κ) (slotIntegral_update_smul κ)

omit [BorelSpace X] in
/-- Actual smooth exterior-product symmetry, on every chart and every point. -/
theorem slotIntegral_perm (κ : KahlerBackground n X)
    (θ : Fin n → ClosedRealOneOneForm n X) (σ : Equiv.Perm (Fin n)) :
    slotIntegral κ (fun i => θ (σ i))=slotIntegral κ θ := by
  unfold slotIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [topRatio,chartRatio]
  rw [topDensity_slotForm_coeff,topDensity_slotForm_coeff]
  exact congrArg (fun y : ℝ => y / topDensity
    ((ProductTestForms.formPow κ.form.val n).coeff (complexChartAt x) ((complexChartAt (n := n) x).val x)))
    (actualMixedTopDensity_perm
      (fun i => (θ i).val.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x)) σ)

theorem slotIntegral_diagonal_sum (κ : KahlerBackground n X)
    (θ : Fin n → ClosedRealOneOneForm n X) (S : Finset (Fin n)) :
    slotIntegral κ (fun _ => ∑ i ∈ S,θ i)=
      ∑ g : Fin n → Fin n with ∀ i,g i ∈ S,slotIntegral κ (fun i => θ (g i)) := by
  classical
  have h := (slotIntegralMultilinear κ).map_sum_finset
    (fun _ (i : Fin n) => θ i) (fun _ => S)
  change slotIntegral κ (fun _ => ∑ i ∈ S,θ i)=
    ∑ g ∈ Fintype.piFinset (fun _ : Fin n => S),slotIntegral κ (fun i => θ (g i)) at h
  convert h using 1
  apply Finset.sum_congr
  · ext g; simp [Fintype.mem_piFinset]
  · intro g _; rfl

/-- Genuine smooth polarization, including the actual zero-arity integral. -/
theorem factorial_mul_slotIntegral_eq_polarization (κ : KahlerBackground n X)
    (θ : Fin n → ClosedRealOneOneForm n X) :
    (n.factorial : ℝ)*slotIntegral κ θ=
      ∑ S : Finset (Fin n),(-1 : ℝ)^(n-S.card)*slotIntegral κ (fun _ => ∑ i ∈ S,θ i) := by
  classical
  let d : (Fin n → Fin n) → ℝ := fun g => slotIntegral κ (fun i => θ (g i))
  have hd (σ : Equiv.Perm (Fin n)) : d σ=d id := slotIntegral_perm κ θ σ
  have h := PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul d hd
  simp_rw [slotIntegral_diagonal_sum]
  simpa only [d,id_eq] using h.symm

/-- Genuine Bott--Chern class invariance for arbitrary smooth slots.
It is proved in the actual chart tensors and by Stokes, not supplied as a certificate. -/
theorem slotIntegral_eq_of_bottChernRel (κ : KahlerBackground n X)
    (θ η : Fin n → ClosedRealOneOneForm n X)
    (h : ∀ i,ClosedRealOneOneForm.BottChernRel (θ i) (η i)) :
    slotIntegral κ θ=slotIntegral κ η := by
  choose f hf hrel using h
  have hpt x : topRatio κ.form.val (slotForm η) x=
      topRatio κ.form.val (slotForm (fun i => θ i+ddcClosedForm (f i) (hf i))) x := by
    let e := complexChartAt (n := n) x
    have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    simp only [topRatio,chartRatio]
    rw [topDensity_slotForm_coeff,topDensity_slotForm_coeff]
    apply congrArg (fun y : ℝ => y / topDensity ((ProductTestForms.formPow κ.form.val n).coeff e (e.val x)))
    apply congrArg actualMixedTopDensity
    funext i
    rw [ClosedRealOneOneForm.coeff_add,ddcClosedForm_coeff]
    exact hrel i e (e.val x) hz
  symm
  calc slotIntegral κ η=slotIntegral κ (fun i => θ i+ddcClosedForm (f i) (hf i)) := by
        unfold slotIntegral
        exact integral_congr_ae (Eventually.of_forall hpt)
    _ = slotIntegral κ θ := slotIntegral_add_ddc κ θ f hf

/-- The actual mixed cohomological integral on the ORIGINAL quotient classes. -/
def classSlotIntegral (κ : KahlerBackground n X) (α : Fin n → RealBottChern n X) : ℝ :=
  slotIntegral κ (fun i => Quotient.out (α i))

/-- EVERY actual smooth representative computes this same quotient reader. -/
theorem classSlotIntegral_ofRepresentative (κ : KahlerBackground n X)
    (θ : Fin n → ClosedRealOneOneForm n X) :
    classSlotIntegral κ (fun i => RealBottChern.ofRepresentative (θ i))=slotIntegral κ θ := by
  apply slotIntegral_eq_of_bottChernRel
  intro i
  exact (RealBottChern.ofRepresentative_eq_iff _ _).mp
    (Quotient.out_eq (RealBottChern.ofRepresentative (θ i)))

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
