import SGPT.Checks.LiteratureBridge.BJRationalRayPromotion

/-! Actual positive ray normalization and finite section union give genuine
rational GF maxima on the SAME original rational line, including poles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.FixedRay
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.CanonicalGeometry
open SGPT.Foundations.PublishedEnvelope.Berkovich SGPT.Foundations.PublishedEnvelope.NativeNumericalFubiniStudy
open SGPT.Foundations.PublishedEnvelope.SchemeModuleIsoGlobalSections
open SGPT.Foundations.PublishedEnvelope.SchemeGlobalSectionModelNormIsometries
open SGPT.Foundations.PublishedEnvelope.BundleTensorPowerPullback
open SGPT.NAPotential.BJ.RationalPromotion
open scoped Classical NNReal ENNReal
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {X : Scheme.{0}} (M : X.Modules) (hM : IsInvertible M) {b : ℚ}

/-- Actual powers + actual power-multiplication isomorphism, retaining the
SAME original ray class and no caller section/function matching output. -/
@[reducible]
def powerNormalize (R : NativeLineFubiniStudy.FSData M b) (k : ℕ) (hk : 0<k) :
    NativeLineFubiniStudy.FSData M b where
  m := R.m*k
  m_pos := Nat.mul_pos R.m_pos hk
  deg := R.deg*k
  deg_eq := by
    rw [Nat.cast_mul,R.deg_eq,Nat.cast_mul]
    ring
  terms := (((FSData.ofRay M hM R).powerDatum k hk).toRayDatum M (R.deg*k)
    (powerMulIso M R.deg k)).terms

theorem powerNormalize_isRational (R : NativeLineFubiniStudy.FSData M b) (hR : R.IsRational)
    (k : ℕ) (hk : 0<k) : (powerNormalize M hM R k hk).IsRational :=
  toRayDatum_isRational _ ((show (FSData.ofRay M hM R).IsRational from hR).powerDatum k hk)
    M (R.deg*k) (powerMulIso M R.deg k)

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

theorem powerNormalize_eval (R : NativeLineFubiniStudy.FSData M b) (k : ℕ) (hk : 0<k)
    (y : RelativeSchemeValuedPoint (1 : Valuation ℂ ℝ≥0) p) :
    (powerNormalize M hM R k hk).eval p hM y=R.eval p hM y := by
  change (((FSData.ofRay M hM R).powerDatum k hk).toRayDatum M (R.deg*k)
    (powerMulIso M R.deg k)).eval p hM y=R.eval p hM y
  rw [FSData.toRayDatum_eval,FSData.powerDatum_eval,FSData.ofRay_eval]

include p in
theorem powerNormalize_nonzero [IsIntegral X] (R : NativeLineFubiniStudy.FSData M b)
    (hNZ : ∃ q∈R.terms,q.1≠0) (k : ℕ) (hk : 0<k) :
    ∃ q∈(powerNormalize M hM R k hk).terms,q.1≠0 := by
  have hP := (show (FSData.ofRay M hM R).Nonzero from hNZ).powerDatum k hk p
  obtain ⟨q,hq,hq0⟩ := hP
  exact ⟨(moduleIsoTopEquiv (powerMulIso M R.deg k) q.1,q.2),
    Finset.mem_image_of_mem _ hq,(moduleIsoTopEquiv (powerMulIso M R.deg k)).map_ne_zero_iff.mpr hq0⟩

/-- Same genuine ray equations INTERNALLY produce the common degree. -/
theorem degree_cross_eq (R S : NativeLineFubiniStudy.FSData M b) : R.deg*S.m=S.deg*R.m := by
  have h : ((R.deg*S.m:ℕ):ℚ)=((S.deg*R.m:ℕ):ℚ) := by
    push_cast
    rw [R.deg_eq,S.deg_eq]
    ring
  exact_mod_cast h

def commonDegreeIso (R S : NativeLineFubiniStudy.FSData M b) :
    bundleTensorPower M (S.deg*R.m)≅bundleTensorPower M (R.deg*S.m) :=
  eqToIso (congrArg (bundleTensorPower M) (degree_cross_eq M R S).symm)

/-- Actual normalized section families and internally produced degree iso;
no common-power/maximum representation is supplied by a caller. -/
def maxDatum (R S : NativeLineFubiniStudy.FSData M b) : NativeLineFubiniStudy.FSData M b where
  m := R.m*S.m
  m_pos := Nat.mul_pos R.m_pos S.m_pos
  deg := R.deg*S.m
  deg_eq := (powerNormalize M hM R S.m S.m_pos).deg_eq
  terms := (powerNormalize M hM R S.m S.m_pos).terms ∪
    (powerNormalize M hM S R.m R.m_pos).terms.image
      (fun q => (moduleIsoTopEquiv (commonDegreeIso M R S) q.1,q.2))

theorem maxDatum_isRational (R S : NativeLineFubiniStudy.FSData M b)
    (hR : R.IsRational) (hS : S.IsRational) : (maxDatum M hM R S).IsRational := by
  intro q hq
  rcases Finset.mem_union.mp hq with hqR|hqS
  · exact powerNormalize_isRational M hM R hR S.m S.m_pos q hqR
  · obtain ⟨q0,hq0,rfl⟩ := Finset.mem_image.mp hqS
    exact powerNormalize_isRational M hM S hS R.m R.m_pos q0 hq0

include p in
theorem maxDatum_nonzero [IsIntegral X] (R S : NativeLineFubiniStudy.FSData M b)
    (hR : ∃ q∈R.terms,q.1≠0) : ∃ q∈(maxDatum M hM R S).terms,q.1≠0 := by
  obtain ⟨q,hq,hq0⟩ := powerNormalize_nonzero M hM p R hR S.m S.m_pos
  exact ⟨q,Finset.mem_union_left _ hq,hq0⟩

/-- Finite union at one genuine normalization is exactly pointwise max,
including the common negative-infinity polar case. -/
theorem weightedNormEval_union (m : ℕ) (A : X.Modules) (hA : IsInvertible A)
    (T U : Finset (Γ(A,⊤)×ℝ)) (y : RelativeSchemeValuedPoint (1 : Valuation ℂ ℝ≥0) p) :
    weightedNormEval Valuation.one_apply_le_one y m A hA (T∪U)=
      max (weightedNormEval Valuation.one_apply_le_one y m A hA T)
        (weightedNormEval Valuation.one_apply_le_one y m A hA U) := by
  unfold weightedNormEval
  rw [Finset.sup_union,ProjBerk.ereal_coe_mul_max (inv_nonneg.mpr (Nat.cast_nonneg m))]

/-- The entire actual native pointwise maximum, with no positivity/finite
value condition on the two original metric values. -/
theorem maxDatum_eval (R S : NativeLineFubiniStudy.FSData M b)
    (y : RelativeSchemeValuedPoint (1 : Valuation ℂ ℝ≥0) p) :
    (maxDatum M hM R S).eval p hM y=max (R.eval p hM y) (S.eval p hM y) := by
  let P := powerNormalize M hM R S.m S.m_pos
  let Q := powerNormalize M hM S R.m R.m_pos
  let hP := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM (R.deg*S.m)
  let hQ := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM (S.deg*R.m)
  change weightedNormEval Valuation.one_apply_le_one y (R.m*S.m)
    (bundleTensorPower M (R.deg*S.m)) hP
    (P.terms∪Q.terms.image (fun q => (moduleIsoTopEquiv (commonDegreeIso M R S) q.1,q.2)))=_
  rw [weightedNormEval_union]
  rw [← weightedNormEval_moduleIso Valuation.one_apply_le_one y (R.m*S.m)
    hQ hP (commonDegreeIso M R S) Q.terms]
  have hden : weightedNormEval Valuation.one_apply_le_one y (R.m*S.m)
      (bundleTensorPower M (S.deg*R.m)) hQ Q.terms=Q.eval p hM y := by
    change weightedNormEval Valuation.one_apply_le_one y (R.m*S.m) _ _ Q.terms=
      weightedNormEval Valuation.one_apply_le_one y (S.m*R.m) _ _ Q.terms
    rw [Nat.mul_comm R.m S.m]
  rw [hden]
  change max (P.eval p hM y) (Q.eval p hM y)=_
  rw [powerNormalize_eval,powerNormalize_eval]

end SGPT.NAPotential.BJ.FixedRay
