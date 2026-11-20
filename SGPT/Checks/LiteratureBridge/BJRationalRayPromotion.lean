import SGPT.Checks.LiteratureBridge.BJNativeGFInverse
import SGPT.Foundations.PublishedEnvelope.Source.ClassPromotion

/-! Actual rational finite-class promotion: genuine original sheaves,
Serre generators, tensor powers, true model norms and native Kleiman.
No caller numerical-ampleness/FD/output-closure certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.RationalPromotion
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.CanonicalGeometry
open SGPT.Foundations.PublishedEnvelope.Berkovich SGPT.Foundations.PublishedEnvelope.NativeNumericalFubiniStudy
open SGPT.Foundations.PublishedEnvelope.SchemeModuleIsoGlobalSections
open SGPT.Foundations.PublishedEnvelope.BundleTensorPowerPullback
open scoped Classical NNReal ENNReal
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {X : Scheme.{0}}

theorem toRayDatum_isRational (D : FSData X) (hR : D.IsRational)
    (M : X.Modules) (d : ℕ) (e : D.line≅bundleTensorPower M d) :
    (D.toRayDatum M d e).IsRational := by
  intro q hq
  obtain ⟨q0,hq0,rfl⟩ := Finset.mem_image.mp hq
  exact hR q0 hq0

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Actual iso transport retains rational sections and the ENTIRE function. -/
theorem exists_rationalRay_of_iso (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational)
    (M : X.Modules) (hM : IsInvertible M) (d : ℕ) (e : D.line≅bundleTensorPower M d) :
    ∃ R : NativeLineFubiniStudy.FSData M ((d:ℚ)/D.m),R.IsRational ∧
      (∃ q∈R.terms,q.1≠0) ∧ ∀ y,R.eval p hM y=D.eval p y := by
  refine ⟨D.toRayDatum M d e,toRayDatum_isRational D hR M d e,?_,?_⟩
  · obtain ⟨q,hq,hq0⟩ := hD
    exact ⟨(moduleIsoTopEquiv e q.1,q.2),Finset.mem_image_of_mem _ hq,
      (moduleIsoTopEquiv e).map_ne_zero_iff.mpr hq0⟩
  · exact D.toRayDatum_eval M hM d e p

variable [IsIntegral X]

/-- Genuine generated twisting internally preserves output rationality. -/
theorem exists_rationalRay_of_generatedTwist (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational)
    (T : X.Modules) (hT : IsInvertible T) (G : T.GeneratingSections) [Fintype G.I]
    (M : X.Modules) (hM : IsInvertible M) (d : ℕ)
    (e : D.line⊗T≅bundleTensorPower M d) :
    ∃ R : NativeLineFubiniStudy.FSData M ((d:ℚ)/D.m),R.IsRational ∧
      (∃ q∈R.terms,q.1≠0) ∧ ∀ y,R.eval p hM y=D.eval p y := by
  obtain ⟨R,hRat,hNZ,heval⟩ := exists_rationalRay_of_iso p (D.generatedTwist T hT G)
    (hD.generatedTwist T hT G p) (hR.generatedTwist T hT G) M hM d e
  exact ⟨R,hRat,hNZ,fun y => (heval y).trans (D.generatedTwist_eval T hT G p y)⟩

/-- Actual tensor-power functors and actual sheaf isos only. -/
def ampleTwistPowerIso (A T M : X.Modules) (r d q : ℕ)
    (e : bundleTensorPower A r⊗T≅bundleTensorPower M d) :
    bundleTensorPower A (r*q)⊗bundleTensorPower T q≅bundleTensorPower M (d*q) :=
  ((powerMulIso A r q).symm⊗ᵢIso.refl (bundleTensorPower T q)) ≪≫
    (BundleTensorPowerTensor.powerTensorIso (bundleTensorPower A r) T q).symm ≪≫
    BundleTensorPowerPullback.powerIso e q ≪≫ powerMulIso M d q

/-- Actual ampleness internally supplies the needed finite generators;
output rationality and function equality are proved, not supplied. -/
theorem exists_rationalRay_of_ampleTwist (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational)
    (T : X.Modules) (hT : SchemeLineAmpleness.IsAmple p T)
    (M : X.Modules) (hM : IsInvertible M) (r d : ℕ) (hr : 0<r)
    (e : bundleTensorPower D.line r⊗T≅bundleTensorPower M d) :
    ∃ R : NativeLineFubiniStudy.FSData M ((d:ℚ)/(D.m*r)),R.IsRational ∧
      (∃ q∈R.terms,q.1≠0) ∧ ∀ y,R.eval p hM y=D.eval p y := by
  obtain ⟨N,hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p T hT
  obtain ⟨q,hq,G,hG⟩ : ∃ q : ℕ,0<q ∧
      ∃ G : (bundleTensorPower T q).GeneratingSections,G.IsFiniteType :=
    ⟨max N 1,lt_of_lt_of_le Nat.one_pos (le_max_right N 1),hN (max N 1) (le_max_left N 1)⟩
  let : Finite G.I := hG.finite
  let : Fintype G.I := Fintype.ofFinite G.I
  have hrq : 0<r*q := Nat.mul_pos hr hq
  have hTq := TensorPowerBaseIdealGrading.tensorPower_isInvertible hT.isInvertible q
  obtain ⟨R,hRat,hNZ,heval⟩ := exists_rationalRay_of_generatedTwist p
    (D.powerDatum (r*q) hrq) (hD.powerDatum (r*q) hrq p) (hR.powerDatum (r*q) hrq)
    (bundleTensorPower T q) hTq G M hM (d*q) (ampleTwistPowerIso D.line T M r d q e)
  have hb : ((d*q:ℕ):ℚ)/((D.m*(r*q):ℕ):ℚ)=(d:ℚ)/(D.m*r) := by
    have hmQ : (D.m:ℚ)≠0 := by exact_mod_cast D.m_pos.ne'
    have hrQ : (r:ℚ)≠0 := by exact_mod_cast hr.ne'
    have hqQ : (q:ℚ)≠0 := by exact_mod_cast hq.ne'
    push_cast
    field_simp [hmQ,hrQ,hqQ]
  rw [← hb]
  exact ⟨R,hRat,hNZ,fun y => (heval y).trans (D.powerDatum_eval (r*q) hrq p y)⟩

/-- Actual invertibility internally supplies its dual tensor cancellation. -/
def differenceIso (A B : X.Modules) (hA : IsInvertible A) : A⊗(B⊗dualObj A)≅B :=
  (β_ A (B⊗dualObj A)) ≪≫ (α_ B (dualObj A) A) ≪≫
    whiskerLeftIso B ((β_ (dualObj A) A) ≪≫ hA.monoidalEvaluationIso) ≪≫ ρ_ B

theorem exists_rationalRay_of_ampleDifference (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational)
    (M : X.Modules) (hM : IsInvertible M) (r d : ℕ) (hr : 0<r)
    (hA : SchemeLineAmpleness.IsAmple p (bundleTensorPower M d⊗dualObj (bundleTensorPower D.line r))) :
    ∃ R : NativeLineFubiniStudy.FSData M ((d:ℚ)/(D.m*r)),R.IsRational ∧
      (∃ q∈R.terms,q.1≠0) ∧ ∀ y,R.eval p hM y=D.eval p y :=
  exists_rationalRay_of_ampleTwist p D hD hR _ hA M hM r d hr
    (differenceIso (bundleTensorPower D.line r) (bundleTensorPower M d)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible r))

/-- Genuine rational promotion from the ACTUAL numerical ample gap. Native
Kleiman is invoked internally, with no criterion/FD certificate as a premise. -/
theorem exists_rationalRay_of_numerical_ampleGap (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational)
    (M : X.Modules) (hM : IsInvertible M) (b : ℚ) (hb0 : 0≤b)
    (hb : (b:ℝ)•NativeRealNumericalClasses.lineClass p M hM-D.numericalClass p∈
      NativeRealNumericalClasses.ampleCone p) :
    ∃ R : NativeLineFubiniStudy.FSData M b,R.IsRational ∧
      (∃ q∈R.terms,q.1≠0) ∧ ∀ y,R.eval p hM y=D.eval p y := by
  have hden : 0<b.den := b.den_pos
  have hnum : ((b.num.toNat:ℕ):ℚ)=(b.num:ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hb0)
  have hm : (D.m:ℚ)≠0 := by exact_mod_cast D.m_pos.ne'
  have hq : ((D.m*b.num.toNat:ℕ):ℚ)/((D.m:ℚ)*(b.den:ℚ))=b := by
    rw [Nat.cast_mul,mul_div_mul_left _ _ hm,hnum,Rat.num_div_den]
  have hqR : ((D.m*b.num.toNat:ℕ):ℝ)/((D.m*b.den:ℕ):ℝ)=(b:ℝ) := by
    have h := congrArg (fun z : ℚ => (z:ℝ)) hq
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Nat.cast_mul] using h
  have hA := numericalAmplenessCriterion p _
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hM (D.m*b.num.toNat)).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible b.den).dual) (by
    rw [D.lineClass_ampleDifference p M hM b.den (D.m*b.num.toNat) hden,hqR]
    exact (NativeRealNumericalClasses.ampleCone p).smul_mem
      (by exact_mod_cast Nat.mul_pos D.m_pos hden) hb)
  have h := exists_rationalRay_of_ampleDifference p D hD hR M hM b.den (D.m*b.num.toNat) hden hA
  exact hq▸h

end SGPT.NAPotential.BJ.RationalPromotion
