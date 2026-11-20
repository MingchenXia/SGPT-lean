import SGPT.Okounkov.SchemeAnalyticTNManifold
import SGPT.Okounkov.SchemeNativeFubiniStudyCoefficients
import SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-!
# Actual projective Fubini–Study coefficients in the SAME TN atlas

Coefficients are the actual global native tensor pulled back through the genuine
mixed-model inverse derivative. The native charted structure is retained for the
codomain; the actual preferred TN chart enters only in true-target readbacks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Manifold Set
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

local instance projectiveTNPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance projectiveTNNativeCharts : ChartedSpace (Fin n → ℂ) (SchemeComplexPoint f) :=
  smoothSchemeComplexChartedSpace f n
local instance projectiveTNNativeRealManifold :
    IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ (SchemeComplexPoint f) := smoothSchemeReal_isManifold f n ∞

/-- The actual mixed-model derivative, with ORIGINAL native codomain charts. -/
def schemeTNInverseNativeDerivative
    (e : OpenPartialHomeomorph (SchemeComplexPoint f) (ComplexModel n))
    (z : ComplexModel n) : ComplexModel n →L[ℝ] (Fin n → ℂ) :=
  mfderiv 𝓘(ℝ, ComplexModel n) 𝓘(ℝ, Fin n → ℂ) e.symm z

/-- The SAME native global FS tensor defines the coefficients intrinsically. -/
def schemeTNFubiniStudyCoefficients (E : ClosedProjectiveEmbedding f)
    (e : OpenPartialHomeomorph (SchemeComplexPoint f) (ComplexModel n))
    (z : ComplexModel n) : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ :=
  (E.nativeFubiniStudyFundamentalForm n (e.symm z)).compContinuousLinearMap
    (schemeTNInverseNativeDerivative f n e z)

/-- The genuine mixed-model chain rule gives the true preferred-chart derivative. -/
theorem schemeTNInverseNativeDerivative_preferred (p : SchemeComplexPoint f)
    (z : ComplexModel n) (hz : z ∈ (schemeAnalyticTNChart f n p).target) :
    schemeTNInverseNativeDerivative f n (schemeAnalyticTNChart f n p) z =
      (schemeNativeInverseChartDerivative f n p (schemeCoordinateModelEquiv n z)).comp
        ((schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ) := by
  have hn : schemeCoordinateModelEquiv n z ∈
      (schemeAnalyticCoordinateChart f n p).target := by
    rwa [schemeAnalyticTNChart_target] at hz
  have hc : (schemeAnalyticCoordinateChart f n p).MDifferentiable
      𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) := mdifferentiable_chart p
  let L := (schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ
  have h := mfderiv_comp z (hc.mdifferentiableAt_symm hn) L.mdifferentiableAt
  have hL : mfderiv 𝓘(ℝ, ComplexModel n) 𝓘(ℝ, Fin n → ℂ) L z = L := L.hasMFDerivAt.mfderiv
  change mfderiv 𝓘(ℝ, ComplexModel n) 𝓘(ℝ, Fin n → ℂ)
      ((schemeAnalyticCoordinateChart f n p).symm ∘ L) z =
    (schemeNativeInverseChartDerivative f n p (L z)).comp
      (mfderiv 𝓘(ℝ, ComplexModel n) 𝓘(ℝ, Fin n → ℂ) L z) at h
  rw [hL] at h
  exact h

/-- On every true preferred target these intrinsic coefficients are the literal linear pullback. -/
theorem schemeTNFubiniStudyCoefficients_preferred (E : ClosedProjectiveEmbedding f)
    (p : SchemeComplexPoint f) (z : ComplexModel n)
    (hz : z ∈ (schemeAnalyticTNChart f n p).target) :
    schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n p) z =
      (E.nativeFubiniStudyFormCoefficients n p (schemeCoordinateModelEquiv n z)).compContinuousLinearMap
        ((schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ) := by
  unfold schemeTNFubiniStudyCoefficients
  rw [schemeTNInverseNativeDerivative_preferred f n p z hz]
  ext v
  rfl

private theorem conjugate_derivative {H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : H ≃L[ℝ] V) (T : V → V) (z : H) (hT : DifferentiableAt ℝ T (L z)) :
    L.toContinuousLinearMap.comp (fderiv ℝ (fun w => L.symm (T (L w))) z) =
      (fderiv ℝ T (L z)).comp L.toContinuousLinearMap := by
  have h := (L.symm.hasFDerivAt.comp z (hT.hasFDerivAt.comp z L.hasFDerivAt)).fderiv
  change fderiv ℝ (fun w => L.symm (T (L w))) z = _ at h
  rw [h]
  ext v
  exact L.apply_symm_apply _

/-- The genuine real derivative of the SAME conjugate transition retains the whole linear law. -/
theorem schemeTNModelTransitionDerivative (p q : SchemeComplexPoint f)
    (z : ComplexModel n) (hz : z ∈ (schemeAnalyticTNTransition f n p q).source) :
    ((schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ).comp
        (fderiv ℝ (schemeAnalyticTNTransition f n p q) z) =
      (fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) (schemeCoordinateModelEquiv n z)).comp
        ((schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ) := by
  have hT := (schemeAnalyticCoordinateTransition_analyticOnNhd f n p q
    (schemeCoordinateModelEquiv n z) (schemeAnalyticTNTransition_source f n p q z hz)).differentiableAt
  let LR : ComplexModel n ≃L[ℝ] (Fin n → ℂ) :=
    { toLinearEquiv := (schemeCoordinateModelEquiv n).toLinearEquiv.restrictScalars ℝ
      continuous_toFun := (schemeCoordinateModelEquiv n).continuous
      continuous_invFun := (schemeCoordinateModelEquiv n).symm.continuous }
  have hh : DifferentiableAt ℝ (schemeAnalyticCoordinateTransition f n p q) (LR z) :=
    hT.restrictScalars ℝ
  exact conjugate_derivative LR (schemeAnalyticCoordinateTransition f n p q) z hh

/-- Actual native overlap and actual linear conjugation give the whole TN coefficient law. -/
theorem schemeTNFubiniStudyCoefficients_transition (E : ClosedProjectiveEmbedding f)
    (p q : SchemeComplexPoint f) (z : ComplexModel n)
    (hz : z ∈ (schemeAnalyticTNTransition f n p q).source) :
    schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n p) z =
      (schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n q)
        (schemeAnalyticTNTransition f n p q z)).compContinuousLinearMap
          (fderiv ℝ (schemeAnalyticTNTransition f n p q) z) := by
  have hq : schemeAnalyticTNTransition f n p q z ∈ (schemeAnalyticTNChart f n q).target :=
    (schemeAnalyticTNChart f n q).map_source hz.2
  rw [schemeTNFubiniStudyCoefficients_preferred f n E p z hz.1,
    schemeTNFubiniStudyCoefficients_preferred f n E q _ hq]
  have hn := schemeAnalyticTNTransition_source f n p q z hz
  have ht := schemeTNModelTransitionDerivative f n p q z hz
  rw [schemeAnalyticTNTransition_apply, ContinuousLinearEquiv.apply_symm_apply,
    schemeNativeFubiniStudyCoefficients_overlap f n E p q _ hn]
  ext v
  change (E.nativeFubiniStudyFormCoefficients n q
    (schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n z)))
      (fun i => fderiv ℝ (schemeAnalyticCoordinateTransition f n p q)
        (schemeCoordinateModelEquiv n z) (schemeCoordinateModelEquiv n (v i))) =
    (E.nativeFubiniStudyFormCoefficients n q
      (schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n z)))
        (fun i => schemeCoordinateModelEquiv n
          (fderiv ℝ (schemeAnalyticTNTransition f n p q) z (v i)))
  apply congrArg (E.nativeFubiniStudyFormCoefficients n q
    (schemeAnalyticCoordinateTransition f n p q (schemeCoordinateModelEquiv n z)))
  funext i
  exact (congrArg (fun A : ComplexModel n →L[ℝ] (Fin n → ℂ) => A (v i)) ht).symm

private theorem preferred_coefficients_smooth (E : ClosedProjectiveEmbedding f)
    (p : SchemeComplexPoint f) :
    ContDiffOn ℝ ∞ (schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n p))
      (schemeAnalyticTNChart f n p).target := by
  let L := (schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ
  have hmap : MapsTo L (schemeAnalyticTNChart f n p).target
      (schemeAnalyticCoordinateChart f n p).target := by
    intro z hz
    rwa [schemeAnalyticTNChart_target] at hz
  have hA := (E.nativeFubiniStudyFormCoefficients_contDiffOn n p).comp L.contDiff.contDiffOn hmap
  have h := SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback.contDiffOn_compContinuousLinearMap
    hA (contDiffOn_const (c := L))
  exact h.congr (fun z hz => schemeTNFubiniStudyCoefficients_preferred f n E p z hz)

private theorem preferred_coefficients_closed (E : ClosedProjectiveEmbedding f)
    (p : SchemeComplexPoint f) (z : ComplexModel n)
    (hz : z ∈ (schemeAnalyticTNChart f n p).target) :
    extDeriv (schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n p)) z = 0 := by
  let L := (schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ
  have hn : L z ∈ (schemeAnalyticCoordinateChart f n p).target := by
    rwa [schemeAnalyticTNChart_target] at hz
  have heq : schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n p) =ᶠ[𝓝 z]
      (fun w => (E.nativeFubiniStudyFormCoefficients n p (L w)).compContinuousLinearMap L) := by
    filter_upwards [(schemeAnalyticTNChart f n p).open_target.mem_nhds hz] with w hw
    exact schemeTNFubiniStudyCoefficients_preferred f n E p w hw
  rw [heq.extDeriv_eq]
  have hA := (E.nativeFubiniStudyFormCoefficients_contDiffOn n p).contDiffAt
    ((schemeAnalyticCoordinateChart f n p).open_target.mem_nhds hn)
  have h := extDeriv_pullback (hA.differentiableAt (by simp)) (L.contDiff.contDiffAt)
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  simp only [ContinuousLinearMap.fderiv] at h
  rw [h, E.nativeFubiniStudyFormCoefficients_closed n p (L z) hn]
  rfl

private theorem preferred_coefficients_hermitian (E : ClosedProjectiveEmbedding f)
    (p : SchemeComplexPoint f) (z : ComplexModel n)
    (hz : z ∈ (schemeAnalyticTNChart f n p).target) :
    IsOneOne (schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n p) z) ∧
      IsStrictlyPositive (schemeTNFubiniStudyCoefficients f n E (schemeAnalyticTNChart f n p) z) := by
  have hn : schemeCoordinateModelEquiv n z ∈
      (schemeAnalyticCoordinateChart f n p).target := by
    rwa [schemeAnalyticTNChart_target] at hz
  rw [schemeTNFubiniStudyCoefficients_preferred f n E p z hz]
  constructor
  · intro u v
    have hm (a b : ComplexModel n) :
        (schemeCoordinateModelEquiv n) ∘ ![a, b] =
          ![schemeCoordinateModelEquiv n a, schemeCoordinateModelEquiv n b] := by
      funext i
      fin_cases i <;> rfl
    change E.nativeFubiniStudyFormCoefficients n p (schemeCoordinateModelEquiv n z)
        ((schemeCoordinateModelEquiv n) ∘ ![Complex.I • u, Complex.I • v]) =
      E.nativeFubiniStudyFormCoefficients n p (schemeCoordinateModelEquiv n z)
        ((schemeCoordinateModelEquiv n) ∘ ![u, v])
    rw [hm, hm, map_smul, map_smul]
    exact schemeNativeFubiniStudyCoefficients_type_one_one f n E p _ hn _ _
  · intro v hv
    have hLv : schemeCoordinateModelEquiv n v ≠ 0 := by
      intro h
      exact hv ((schemeCoordinateModelEquiv n).injective
        (h.trans (schemeCoordinateModelEquiv n).map_zero.symm))
    have hm : (schemeCoordinateModelEquiv n) ∘ ![v, Complex.I • v] =
        ![schemeCoordinateModelEquiv n v, Complex.I • schemeCoordinateModelEquiv n v] := by
      funext i
      fin_cases i
      · rfl
      · exact (schemeCoordinateModelEquiv n).map_smul Complex.I v
    change 0 < E.nativeFubiniStudyFormCoefficients n p (schemeCoordinateModelEquiv n z)
      ((schemeCoordinateModelEquiv n) ∘ ![v, Complex.I • v])
    rw [hm]
    exact schemeNativeFubiniStudyCoefficients_pos f n E p _ hn _ hLv

/-- Actual projectivity internally supplies every TN manifold prerequisite; the
actual intrinsic coefficients and DERIVED overlap give a genuine smooth form. -/
def schemeProjectiveTNFubiniStudyForm (E : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticTNChartedSpace f n
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    SmoothRealForm n (SchemeComplexPoint f) 2 := by
  letI := schemeAnalyticTNChartedSpace f n
  letI := E.isSeparated
  letI := E.quasiCompact
  letI := schemeAnalyticTN_isComplexManifold f n
  refine { coeff := fun e => schemeTNFubiniStudyCoefficients f n E e.val
           smooth := ?_
           compatible := ?_ }
  · rintro ⟨e, he⟩
    change e ∈ Set.range (schemeAnalyticTNChart f n) at he
    obtain ⟨p, rfl⟩ := he
    exact preferred_coefficients_smooth f n E p
  · rintro ⟨e, he⟩ ⟨d, hd⟩ z hz v
    change e ∈ Set.range (schemeAnalyticTNChart f n) at he
    change d ∈ Set.range (schemeAnalyticTNChart f n) at hd
    obtain ⟨p, rfl⟩ := he
    obtain ⟨q, rfl⟩ := hd
    exact congrArg (fun A => A v) (schemeTNFubiniStudyCoefficients_transition f n E p q z hz)

/-- Whole actual coefficient readback, including its fixed original native codomain derivative. -/
theorem schemeProjectiveTNFubiniStudyForm_coeff (E : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticTNChartedSpace f n
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    ∀ (e : ComplexChart n (SchemeComplexPoint f)) (z : ComplexModel n),
      (schemeProjectiveTNFubiniStudyForm f n E).coeff e z =
        schemeTNFubiniStudyCoefficients f n E e.val z := by
  intros
  rfl

/-- Genuine exterior-derivative locality and actual native closedness give TN closedness. -/
theorem schemeProjectiveTNFubiniStudyForm_closed (E : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticTNChartedSpace f n
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    (schemeProjectiveTNFubiniStudyForm f n E).IsClosed := by
  let := schemeAnalyticTNChartedSpace f n
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  rintro ⟨e, he⟩ z hz
  change e ∈ Set.range (schemeAnalyticTNChart f n) at he
  obtain ⟨p, rfl⟩ := he
  exact preferred_coefficients_closed f n E p z hz

/-- Genuine native type/strict positivity and the actual complex linear equivalence
give the true TN Hermitian property, including dimension zero. -/
theorem schemeProjectiveTNFubiniStudyForm_isHermitian (E : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticTNChartedSpace f n
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    (schemeProjectiveTNFubiniStudyForm f n E).IsHermitian := by
  let := schemeAnalyticTNChartedSpace f n
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  rintro ⟨e, he⟩ z hz
  change e ∈ Set.range (schemeAnalyticTNChart f n) at he
  obtain ⟨p, rfl⟩ := he
  exact preferred_coefficients_hermitian f n E p z hz

/-- Actual source smoothness and a genuine closed projective embedding manufacture
the TN Kähler background on the SAME internally constructed source atlas. -/
def schemeProjectiveTNKahlerBackground (E : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticTNChartedSpace f n
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    PositiveClasses.KahlerBackground n (SchemeComplexPoint f) := by
  letI := schemeAnalyticTNChartedSpace f n
  letI := E.isSeparated
  letI := E.quasiCompact
  letI := schemeAnalyticTN_isComplexManifold f n
  exact
    { form := ⟨schemeProjectiveTNFubiniStudyForm f n E,
        schemeProjectiveTNFubiniStudyForm_closed f n E,
        fun e z hz => (schemeProjectiveTNFubiniStudyForm_isHermitian f n E e z hz).1⟩
      isKahler := ⟨schemeProjectiveTNFubiniStudyForm_isHermitian f n E,
        schemeProjectiveTNFubiniStudyForm_closed f n E⟩ }

/-- The manufactured background retains the WHOLE actual transported FS form. -/
theorem schemeProjectiveTNKahlerBackground_form (E : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticTNChartedSpace f n
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    (schemeProjectiveTNKahlerBackground f n E).form.val =
      schemeProjectiveTNFubiniStudyForm f n E := rfl

/-- Every true preferred target retains the literal original native FS pullback coefficient. -/
theorem schemeProjectiveTNKahlerBackground_preferred (E : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticTNChartedSpace f n
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    ∀ (p : SchemeComplexPoint f) (z : ComplexModel n),
      z ∈ (schemeAnalyticTNChart f n p).target →
      (schemeProjectiveTNKahlerBackground f n E).form.val.coeff ⟨schemeAnalyticTNChart f n p, ⟨p, rfl⟩⟩ z =
        (E.nativeFubiniStudyFormCoefficients n p (schemeCoordinateModelEquiv n z)).compContinuousLinearMap
          ((schemeCoordinateModelEquiv n).toContinuousLinearMap.restrictScalars ℝ) := by
  let := schemeAnalyticTNChartedSpace f n
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  intro p z hz
  exact schemeTNFubiniStudyCoefficients_preferred f n E p z hz

end SGPT.Okounkov
