import SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose
import SGPT.Foundations.Analysis.Pending.CompactDifferentialOverlap
import SGPT.Foundations.Analysis.Pending.ActualGlobalBidimensionOneDdc

/-! # Original native current differentials without compactness

All six complete mathematical statements and ENTIRE proofs precede this
source. The existing original current product/submodule topology is used.
Actual whole LF test maps prove compatibility internally in all real degrees.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentDifferentials

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  StronglyPositiveForms NaturalFullCurrentTranspose CompactDifferentialTests CompactDifferentialOverlap

variable {n q r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual whole native test inclusion commutes with the original exterior operator. -/
theorem exteriorTestCLM_mono {U V : Opens (ComplexModel n)} (hUV : U ≤ V)
    (η : TestForm U q) :
    (TestFunction.monoCLM ℝ (exteriorTestCLM η) : TestForm V (q + 1)) =
      exteriorTestCLM (TestFunction.monoCLM ℝ η : TestForm V q) := by
  have hη : (TestFunction.monoCLM ℝ η : ComplexModel n → RealForm n q) =
      (η : ComplexModel n → RealForm n q) := funext (testForm_inclusion_apply hUV η)
  apply TestFunction.ext
  intro z
  rw [testForm_inclusion_apply hUV, exteriorTestCLM_apply, exteriorTestCLM_apply, hη]

/-- Actual whole native test inclusion preserves the exact normalized complex operator. -/
theorem localDcTestCLM_mono {U V : Opens (ComplexModel n)} (hUV : U ≤ V)
    (η : TestForm U q) :
    (TestFunction.monoCLM ℝ (localDcTestCLM η) : TestForm V (q + 1)) =
      localDcTestCLM (TestFunction.monoCLM ℝ η : TestForm V q) := by
  have hη : (TestFunction.monoCLM ℝ η : ComplexModel n → RealForm n q) =
      (η : ComplexModel n → RealForm n q) := funext (testForm_inclusion_apply hUV η)
  apply TestFunction.ext
  intro z
  rw [testForm_inclusion_apply hUV, localDcTestCLM_apply, localDcTestCLM_apply, hη]

/-- The same original compatible full native chart functional carrier, indexed by its test degree. -/
def compatibleNativeSubmodule (q : ℕ) :
    Submodule ℝ ((e : ComplexChart n M) → TestForm (chartTarget e) q →L[ℝ] ℝ) where
  carrier := {F | ∀ (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) q) (ζ : TestForm (overlapTarget e f) q),
    OverlapTestRelated e f η ζ →
      F e (TestFunction.monoCLM ℝ η) = F f (TestFunction.monoCLM ℝ ζ)}
  zero_mem' := by intro e f η ζ h; rfl
  add_mem' := by
    intro F G hF hG e f η ζ h
    exact congrArg₂ (· + ·) (hF e f η ζ h) (hG e f η ζ h)
  smul_mem' := by
    intro c F hF e f η ζ h
    exact congrArg (c • ·) (hF e f η ζ h)

/-- An abbreviation for that concrete original native compatible-family submodule. -/
abbrev NativeFamily (q : ℕ) := ↥(compatibleNativeSubmodule (n := n) (M := M) q)

/-- Exact degree identification is the identity on the original compatible chart family and topology. -/
def nativeDegreeEquiv {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q) :
    GlobalCurrent n M k ≃L[ℝ] NativeFamily (n := n) (M := M) q := by
  subst q
  exact ContinuousLinearEquiv.refl ℝ (GlobalCurrent n M k)

/-- The actual original chart functional in its naturally identified complementary degree. -/
def nativeChartFunctional {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
    (T : GlobalCurrent n M k) (e : ComplexChart n M) : TestForm (chartTarget e) q →L[ℝ] ℝ :=
  (nativeDegreeEquiv hk T).val e

/-- No chart values are changed by the exact complementary-degree identification. -/
theorem nativeChartFunctional_original {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
    (T : GlobalCurrent n M k) (e : ComplexChart n M) :
    HEq (nativeChartFunctional hk T e) (T.inChart e) := by
  subst q
  rfl

/-- The actual inverse cancels on every whole native chart test. -/
theorem nativeDegreeEquiv_symm_chart {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
    (F : NativeFamily (n := n) (M := M) q) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    nativeChartFunctional hk ((nativeDegreeEquiv hk).symm F) e η = F.val e η := by
  unfold nativeChartFunctional
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Fixed genuine whole native test transposition is continuous on the actual compatible submodules. -/
def signedNativeTransposeCLM (c : ℝ)
    (A : (U : Opens (ComplexModel n)) → TestForm U q →L[ℝ] TestForm U r)
    (hmono : ∀ (U V : Opens (ComplexModel n)) (_hUV : U ≤ V) (η : TestForm U q),
      (TestFunction.monoCLM ℝ (A U η) : TestForm V r) =
        A V (TestFunction.monoCLM ℝ η : TestForm V q))
    (hrel : ∀ (e f : ComplexChart n M) (η : TestForm (overlapSource e f) q)
      (ζ : TestForm (overlapTarget e f) q), OverlapTestRelated e f η ζ →
      OverlapTestRelated e f (A (overlapSource e f) η) (A (overlapTarget e f) ζ)) :
    NativeFamily (n := n) (M := M) r →L[ℝ] NativeFamily (n := n) (M := M) q := by
  let B : ((e : ComplexChart n M) → TestForm (chartTarget e) r →L[ℝ] ℝ) →L[ℝ]
      ((e : ComplexChart n M) → TestForm (chartTarget e) q →L[ℝ] ℝ) :=
    ContinuousLinearMap.pi fun e =>
      (c • (A (chartTarget e)).precomp ℝ).comp (ContinuousLinearMap.proj e)
  let C := B.comp (compatibleNativeSubmodule (n := n) (M := M) r).subtypeL
  exact C.codRestrict (compatibleNativeSubmodule (n := n) (M := M) q) (by
    intro T e f η ζ h
    change c * T.val e (A (chartTarget e) (TestFunction.monoCLM ℝ η)) =
      c * T.val f (A (chartTarget f) (TestFunction.monoCLM ℝ ζ))
    rw [← hmono _ _ (overlapSource_le e f) η, ← hmono _ _ (overlapTarget_le e f) ζ]
    exact congrArg (c * ·) (T.property e f _ _ (hrel e f η ζ h)))

omit [IsComplexManifold n M] in
/-- Literal entire full LF chart evaluation of the constructed compatible-family transpose. -/
theorem signedNativeTransposeCLM_apply (c : ℝ)
    (A : (U : Opens (ComplexModel n)) → TestForm U q →L[ℝ] TestForm U r)
    (hmono : ∀ (U V : Opens (ComplexModel n)) (_hUV : U ≤ V) (η : TestForm U q),
      (TestFunction.monoCLM ℝ (A U η) : TestForm V r) =
        A V (TestFunction.monoCLM ℝ η : TestForm V q))
    (hrel : ∀ (e f : ComplexChart n M) (η : TestForm (overlapSource e f) q)
      (ζ : TestForm (overlapTarget e f) q), OverlapTestRelated e f η ζ →
      OverlapTestRelated e f (A (overlapSource e f) η) (A (overlapTarget e f) ζ))
    (T : NativeFamily (n := n) (M := M) r) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    (signedNativeTransposeCLM c A hmono hrel T).val e η = c * T.val e (A (chartTarget e) η) :=
  rfl

/-- The original actual exterior native current operator, continuous without compactness. -/
def exteriorCurrentCLM (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    GlobalCurrent n M (complementDegree n (q + 1) hq) →L[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)) :=
  (nativeDegreeEquiv (complementDegree_complement n q (by omega))).symm.toContinuousLinearMap.comp
    ((signedNativeTransposeCLM ((-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1))
      (fun _ => exteriorTestCLM) (fun _ _ h η => exteriorTestCLM_mono h η)
      overlapTestRelated_exteriorTestCLM).comp
        (nativeDegreeEquiv (complementDegree_complement n (q + 1) hq)).toContinuousLinearMap)

/-- The entire original exterior current chart formula on every full native LF test. -/
theorem exteriorCurrentCLM_chart (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1) hq)) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    nativeChartFunctional (complementDegree_complement n q (by omega)) (exteriorCurrentCLM q hq T) e η =
      (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
        nativeChartFunctional (complementDegree_complement n (q + 1) hq) T e (exteriorTestCLM η) := by
  change nativeChartFunctional (complementDegree_complement n q (by omega))
    ((nativeDegreeEquiv (complementDegree_complement n q (by omega))).symm _) e η = _
  rw [nativeDegreeEquiv_symm_chart]
  rfl

/-- The original normalized native complex current operator in every admissible real degree. -/
def dcCurrentCLM (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    GlobalCurrent n M (complementDegree n (q + 1) hq) →L[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)) :=
  (nativeDegreeEquiv (complementDegree_complement n q (by omega))).symm.toContinuousLinearMap.comp
    ((signedNativeTransposeCLM ((-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1))
      (fun _ => localDcTestCLM) (fun _ _ h η => localDcTestCLM_mono h η)
      overlapTestRelated_localDcTestCLM).comp
        (nativeDegreeEquiv (complementDegree_complement n (q + 1) hq)).toContinuousLinearMap)

/-- The original exact normalized complex current chart formula on all full native LF tests. -/
theorem dcCurrentCLM_chart (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1) hq)) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    nativeChartFunctional (complementDegree_complement n q (by omega)) (dcCurrentCLM q hq T) e η =
      (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
        nativeChartFunctional (complementDegree_complement n (q + 1) hq) T e (localDcTestCLM η) := by
  change nativeChartFunctional (complementDegree_complement n q (by omega))
    ((nativeDegreeEquiv (complementDegree_complement n q (by omega))).symm _) e η = _
  rw [nativeDegreeEquiv_symm_chart]
  rfl

/-- The original positive native second current operator, continuous on any complex manifold. -/
def ddcCurrentCLM (q : ℕ) (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    GlobalCurrent n M (complementDegree n (q + 1 + 1) hq) →L[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)) :=
  (nativeDegreeEquiv (complementDegree_complement n q (by omega))).symm.toContinuousLinearMap.comp
    ((signedNativeTransposeCLM 1 (fun _ => localDdcTestCLM)
      (fun _ _ h η => ActualGlobalBidimensionOneDdc.localDdcTestCLM_mono h η)
      overlapTestRelated_localDdcTestCLM).comp
        (nativeDegreeEquiv (complementDegree_complement n (q + 1 + 1) hq)).toContinuousLinearMap)

/-- Positive second transposition reads the actual full original native test differential. -/
theorem ddcCurrentCLM_chart (q : ℕ) (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq)) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) :
    nativeChartFunctional (complementDegree_complement n q (by omega)) (ddcCurrentCLM q hq T) e η =
      nativeChartFunctional (complementDegree_complement n (q + 1 + 1) hq) T e (localDdcTestCLM η) := by
  change nativeChartFunctional (complementDegree_complement n q (by omega))
    ((nativeDegreeEquiv (complementDegree_complement n q (by omega))).symm _) e η = _
  rw [nativeDegreeEquiv_symm_chart]
  change (1 : ℝ) * _ = _
  rw [one_mul]
  rfl

end SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentDifferentials
