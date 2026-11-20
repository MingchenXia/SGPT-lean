import SGPT.Trace.BertiniSectionMultiplication
import SGPT.Trace.BertiniRestrictionChart
import SGPT.PSH.DirImg2Det
import SGPT.BBJ.ProbabilityPshAverage
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

/-!+# Actual native slice norms and Fatou

This module proves joint lower semicontinuity of the literal extended
weighted squared norms of finite combinations of original sections, pulled
back by genuine moving slice charts. Poles are retained as ENNReal infinity.
The quotient-to-fibre adjunction and residue-normalization dictionary remains
separate: these integrals are not asserted to be the global source Hodge norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped ProductComplexManifold
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.MultiplierSectionsDraft ProductComplexManifold

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (E : HermitianHolomorphicLineBundle n X) {r : ℕ}

/-- The actual finite combination of the original native global sections. -/
def nativeSectionCombination (S : Fin r → HolomorphicSections (n := n) E.Fiber)
    (v : Fin r → ℂ) : HolomorphicSections (n := n) E.Fiber :=
  ∑ i, v i • S i

/-- Actual fibre norms are jointly continuous in the coefficient vector and
the original point. This follows from the original frame formula, rather
than an assumed norm-family continuity certificate. -/
theorem continuous_nativeSectionCombinationNorm
    (S : Fin r → HolomorphicSections (n := n) E.Fiber) :
    Continuous (fun q : (Fin r → ℂ) × X => ‖nativeSectionCombination E S q.1 q.2‖) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro q
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber q.2, inferInstance⟩
  let := e.property
  have he : q.2 ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber q.2
  have hcoeff : ContinuousAt (fun p : (Fin r → ℂ) × X =>
      ∑ i, p.1 i * sectionCoefficient E.Fiber e.val (S i) p.2) q := by
    apply tendsto_finsetSum Finset.univ
    intro i hi
    have hS : ContinuousAt (sectionCoefficient E.Fiber e.val (S i)) q.2 :=
      ((e.val.contMDiffAt_section_iff he).mp ((S i).contMDiff q.2)).continuousAt
    exact ((continuous_apply i).continuousAt.comp continuous_fst.continuousAt).mul
      (hS.comp continuous_snd.continuousAt)
  have hframe : ContinuousAt (fun p : (Fin r → ℂ) × X => frameNorm E.Fiber e.val p.2) q :=
    ((frameNorm_continuousOn E.Fiber e.val).continuousAt
      (e.val.open_baseSet.mem_nhds he)).comp continuous_snd.continuousAt
  apply (hcoeff.norm.mul hframe).congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually (e.val.open_baseSet.mem_nhds he)] with p hp
  rw [norm_eq_coefficient_mul_frameNorm E.Fiber e.val _ hp]
  congr 2
  change (e.val.linearEquivAt ℂ p.2 hp)
    (nativeSectionCombination E S p.1 p.2) = _
  let ev : HolomorphicSections (n := n) E.Fiber →ₗ[ℂ] E.Fiber p.2 := {
    toFun u := u p.2
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hsum : nativeSectionCombination E S p.1 p.2 = ∑ i, p.1 i • S i p.2 := by
    change ev (∑ i, p.1 i • S i) = _
    rw [map_sum]
    rfl
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, smul_eq_mul]
  rfl

/-- The SAME extended multiplier weight is lower semicontinuous for the
original quasi-PSH potential, including its actual minus-infinity poles. -/
theorem lowerSemicontinuous_originalMultiplierWeight {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    LowerSemicontinuous (fun x => multiplierWeight 1 (φ x)) := by
  have hc : Continuous (fun a : EReal => multiplierWeight 1 a) := by
    simpa only [multiplierWeight, EReal.coe_one, one_mul, Function.comp_def] using
      (ENNReal.continuous_exp.comp (continuous_neg : Continuous (fun a : EReal => -a)))
  exact hc.comp_upperSemicontinuous_antitone hφ.upperSemicontinuous
    (multiplierWeight_antitone zero_le_one)

section MovingPoints

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  (S : Fin r → HolomorphicSections (n := n) E.Fiber)
  (F : A × B → X) (φ : X → EReal)

/-- Literal original finite-section weighted density on a moving fibre patch. -/
def nativeMovingSectionDensity (p : A × (Fin r → ℂ)) (b : B) : ℝ≥0∞ :=
  ENNReal.ofReal (‖nativeSectionCombination E S p.2 (F (p.1, b))‖ ^ 2) *
    multiplierWeight 1 (φ (F (p.1, b)))

/-- All lower semicontinuity is derived from actual original section norms,
the actual moving point map and the original quasi-PSH potential. -/
theorem lowerSemicontinuous_nativeMovingSectionDensity
    (hF : Continuous F) (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    LowerSemicontinuous (fun q : (A × (Fin r → ℂ)) × B =>
      nativeMovingSectionDensity E S F φ q.1 q.2) := by
  have hpoint : Continuous (fun q : (A × (Fin r → ℂ)) × B => F (q.1.1, q.2)) :=
    hF.comp ((continuous_fst.fst).prodMk continuous_snd)
  have hnorm : Continuous (fun q : (A × (Fin r → ℂ)) × B =>
      ‖nativeSectionCombination E S q.1.2 (F (q.1.1, q.2))‖) :=
    (continuous_nativeSectionCombinationNorm E S).comp
      ((continuous_fst.snd).prodMk hpoint)
  have hweight := (lowerSemicontinuous_originalMultiplierWeight hφ).comp hpoint
  intro q
  exact SGPT.PSH.DirImg2.lowerSemicontinuousAt_mul
    ((ENNReal.continuous_ofReal.comp (hnorm.pow 2)).lowerSemicontinuous q) (hweight q)

/-- Fatou gives joint lower semicontinuity in the parameter and coefficient
vector for the actual extended weighted patch integral; no finite-integral
or metric-semicontinuity assumption is supplied. -/
theorem lowerSemicontinuous_nativeMovingSectionMass
    [FirstCountableTopology A] [MeasurableSpace B] [BorelSpace B]
    (μ : Measure B) (hF : Continuous F)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    LowerSemicontinuous (fun p : A × (Fin r → ℂ) =>
      ∫⁻ b, nativeMovingSectionDensity E S F φ p b ∂μ) := by
  have hl := lowerSemicontinuous_nativeMovingSectionDensity E S F φ hF hφ
  apply lowerSemicontinuousOn_univ_iff.mp
  apply SGPT.BBJ.lowerSemicontinuousOn_lintegral μ
    (fun b p => nativeMovingSectionDensity E S F φ p b) Set.univ
  · intro p
    exact (hl.comp (continuous_const.prodMk continuous_id)).measurable
  · intro b
    exact (hl.comp (continuous_id.prodMk continuous_const)).lowerSemicontinuousOn Set.univ

end MovingPoints

namespace SliceChart

variable {N : ℕ} {p : X → SGPT.Projective.ComplexProjectiveSpace N} {φ : X → EReal}
  (c : SliceChart n p φ)

/-- Joint continuity of the SAME moving slice points in the original manifold,
from the existing genuine holomorphic flattening inverse. -/
theorem continuous_joint_point :
    Continuous (fun q : (ball c.ζ₀ c.r) × (ball c.z₀ c.r) => c.point q.1.val q.2.val) := by
  have harg : Continuous (fun q : (ball c.ζ₀ c.r) × (ball c.z₀ c.r) =>
      flatProj c.m (prodModelEquiv N n (q.1.val, q.2.val))) :=
    (flatProj c.m).continuous.comp ((prodModelEquiv N n).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  have hinv := c.Φ.invFun_holomorphic.continuousOn.comp_continuous harg
    (fun q => c.mapsTo_target q.1.val q.1.property q.2.val q.2.property)
  have hslice := (continuous_snd.comp (prodModelEquiv N n).symm.continuous).comp hinv
  exact c.e.val.continuousOn_symm.comp_continuous hslice
    (fun q => c.V_subset (c.mapsTo_V q.1.val q.1.property q.2.val q.2.property))

/-- The original finite-section weighted mass in actual moving incidence
slice coordinates is jointly lower semicontinuous by actual Fatou. The
explicit patch measure may in particular be a lower-dimensional slice
measure; no duplicated ambient Lebesgue normalization is asserted. -/
theorem lowerSemicontinuous_nativeSliceSectionMass
    (S : Fin r → HolomorphicSections (n := n) E.Fiber)
    (μ : Measure (ball c.z₀ c.r))
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    LowerSemicontinuous (fun q : (ball c.ζ₀ c.r) × (Fin r → ℂ) =>
      ∫⁻ b, nativeMovingSectionDensity E S
        (fun q : (ball c.ζ₀ c.r) × (ball c.z₀ c.r) => c.point q.1.val q.2.val) φ q b ∂μ) :=
  lowerSemicontinuous_nativeMovingSectionMass E S _ φ μ c.continuous_joint_point hφ

end SliceChart

end SGPT.Trace.Bertini
