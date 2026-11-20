import SGPT.PSH.SourceComplexPositiveCurrentReality
import SGPT.PSH.OriginalGlobalBetaWedgeCurrent

/-! Literal SGPT def:pos_curr ALL N and ALL m: actual complex (m,m) currents,
global smooth beta positive wedge measures, derived REALNESS, and a genuine
ZERO space above geometric degree. Never truncate N-m to admit scalar currents. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open scoped Distributions
universe u
/-- The source Y has its declared dimension N in EVERY genuine original chart.
This retains arbitrary original atlases, empty/disconnected Y, and N=0; no
native/global second-countability or connectedness structure is required. -/
structure OriginalNDimensionalComplexAtlas (X : Type u) [TopologicalSpace X] (N : ℕ) where
  atlas : VariableComplexAtlas X
  dimension_eq : ∀ i : atlas.Index,atlas.dimension i=N

variable {X : Type u} [TopologicalSpace X] {N : ℕ}
  (A : OriginalNDimensionalComplexAtlas X N) (m : ℕ)

/-- Genuine complex (m,m) source currents: actual unrestricted complex LF
current with proved pure bidegree below N; the TRUE zero space when m>N. -/
def OriginalSourceComplexMMCurrent : Type u :=
  if m≤N then OriginalPureComplexCurrent A.atlas (N-m) else PUnit.{u+1}

/-- Entire complex current underlying the source bidegree object. -/
def OriginalSourceRawComplexMMCurrent : Type u :=
  if m≤N then OriginalComplexCurrent A.atlas (2*(N-m)) else PUnit.{u+1}

/-- Actual original REAL graded current space, to be PRODUCED by positivity. -/
def OriginalSourceRealMMCurrent : Type u :=
  if m≤N then OriginalRealCurrent A.atlas (2*(N-m)) else PUnit.{u+1}

def sourceComplexMMLowEquiv (h : m≤N) :
    OriginalSourceComplexMMCurrent A m ≃ OriginalPureComplexCurrent A.atlas (N-m) :=
  Equiv.cast (by simp [OriginalSourceComplexMMCurrent,h])

def sourceRawComplexMMLowEquiv (h : m≤N) :
    OriginalSourceRawComplexMMCurrent A m ≃ OriginalComplexCurrent A.atlas (2*(N-m)) :=
  Equiv.cast (by simp [OriginalSourceRawComplexMMCurrent,h])

def sourceRealMMLowEquiv (h : m≤N) :
    OriginalSourceRealMMCurrent A m ≃ OriginalRealCurrent A.atlas (2*(N-m)) :=
  Equiv.cast (by simp [OriginalSourceRealMMCurrent,h])

/-- Literal source positive predicate with the m>N clause preserved. In the
geometric range it quantifies genuine GLOBAL smooth (1,0) fields and actual
continuous wedge distributions, equivalent to genuine positive measures. -/
def OriginalSourceMMPositive (T : OriginalSourceComplexMMCurrent A m) : Prop :=
  if h : m≤N then OriginalSourceComplexPositive A.atlas (N-m)
    ((sourceComplexMMLowEquiv A m h T).val) else True

/-- Actual forgetful map from genuine bidegree source currents to all currents. -/
def sourceMMForget (T : OriginalSourceComplexMMCurrent A m) :
    OriginalSourceRawComplexMMCurrent A m := by
  classical
  by_cases h : m≤N
  · exact (sourceRawComplexMMLowEquiv A m h).symm
      (sourceComplexMMLowEquiv A m h T).val
  · simpa [OriginalSourceRawComplexMMCurrent,h] using (PUnit.unit : PUnit.{u+1})

/-- Genuine complexification of an ACTUAL original real graded current.
Its range is the unrestricted complex current space; no type/reality output
is a premise of the original complex bidegree current object. -/
def sourceMMComplexify (S : OriginalSourceRealMMCurrent A m) :
    OriginalSourceRawComplexMMCurrent A m := by
  classical
  by_cases h : m≤N
  · exact (sourceRawComplexMMLowEquiv A m h).symm
      (originalExtendComplexCurrent A.atlas (2*(N-m)) (sourceRealMMLowEquiv A m h S) 0)
  · simpa [OriginalSourceRawComplexMMCurrent,h] using (PUnit.unit : PUnit.{u+1})

/-- Exact genuine complexification readback in the geometric degree range. -/
theorem sourceMMComplexify_low (h : m≤N) (S : OriginalSourceRealMMCurrent A m) :
    sourceRawComplexMMLowEquiv A m h (sourceMMComplexify A m S)=
      originalExtendComplexCurrent A.atlas (2*(N-m)) (sourceRealMMLowEquiv A m h S) 0 := by
  simp [sourceMMComplexify,h]

theorem sourceMMForget_low (h : m≤N) (T : OriginalSourceComplexMMCurrent A m) :
    sourceRawComplexMMLowEquiv A m h (sourceMMForget A m T)=
      (sourceComplexMMLowEquiv A m h T).val := by
  simp [sourceMMForget,h]

/-- The HIGH grade is genuinely zero: no nonzero scalar currents arise from
Nat subtraction truncation. This is a theorem about the ACTUAL current space. -/
theorem sourceMM_high_complex_subsingleton (h : N<m) :
    Subsingleton (OriginalSourceComplexMMCurrent A m) := by
  simpa [OriginalSourceComplexMMCurrent,Nat.not_le_of_gt h] using
    (inferInstance : Subsingleton PUnit.{u+1})

theorem sourceMM_high_raw_complex_subsingleton (h : N<m) :
    Subsingleton (OriginalSourceRawComplexMMCurrent A m) := by
  simpa [OriginalSourceRawComplexMMCurrent,Nat.not_le_of_gt h] using
    (inferInstance : Subsingleton PUnit.{u+1})

theorem sourceMM_high_real_subsingleton (h : N<m) :
    Subsingleton (OriginalSourceRealMMCurrent A m) := by
  simpa [OriginalSourceRealMMCurrent,Nat.not_le_of_gt h] using
    (inferInstance : Subsingleton PUnit.{u+1})

/-- The source's entire high-degree positive clause, on the true zero space. -/
theorem sourceMM_high_positive (h : N<m) (T : OriginalSourceComplexMMCurrent A m) :
    OriginalSourceMMPositive A m T := by
  simp [OriginalSourceMMPositive,Nat.not_le_of_gt h]

/-- ALL-N/ALL-m literal source positive definition is exactly m>N OR the
actual positive regular wedge-measure condition for EVERY GLOBAL beta field. -/
theorem sourceMM_positive_iff_literal_measures (T : OriginalSourceComplexMMCurrent A m) :
    OriginalSourceMMPositive A m T ↔ N<m ∨
      ∃ h : m≤N,∀ beta : Fin (N-m) → OriginalGlobalOneZeroForm A.atlas,∀ i : A.atlas.Index,
        ∃ nu : Measure (originalCurrentTarget A.atlas i),nu.Regular ∧ IsLocallyFiniteMeasure nu ∧
          ∀ phi : 𝓓(originalCurrentTarget A.atlas i,ℝ),
            originalGlobalBetaWedgeFunctional A.atlas (N-m) ((sourceComplexMMLowEquiv A m h T).val) beta i phi=
              ((∫ x : originalCurrentTarget A.atlas i,phi x ∂nu : ℝ) : ℂ) := by
  by_cases h : m≤N
  · constructor
    · intro hT
      right
      refine ⟨h,?_⟩
      apply (original_source_positive_iff_actual_wedge_measures A.atlas (N-m) _).mp
      simpa [OriginalSourceMMPositive,h] using hT
    · rintro (hbad|⟨hgood,hmeasure⟩)
      · exact (not_lt_of_ge h hbad).elim
      · have hpos : OriginalSourceComplexPositive A.atlas (N-m)
            ((sourceComplexMMLowEquiv A m h T).val) :=
          (original_source_positive_iff_actual_wedge_measures A.atlas (N-m) _).mpr hmeasure
        simpa [OriginalSourceMMPositive,h] using hpos
  · simp [OriginalSourceMMPositive,h,Nat.lt_of_not_ge h]

/-- Whole source positive COMPLEX currents are REAL, including m>N, empty
Y, N=0 and all original atlas components. The real current exists uniquely
and its full actual complexification equals the original underlying current.
No real presentation, local positivity or output certificate is assumed. -/
theorem sourceMM_positive_exists_unique_real [T2Space X]
    (T : OriginalSourceComplexMMCurrent A m) (hT : OriginalSourceMMPositive A m T) :
    ∃! S : OriginalSourceRealMMCurrent A m,
      sourceMMComplexify A m S=sourceMMForget A m T := by
  by_cases h : m≤N
  · let t := sourceComplexMMLowEquiv A m h T
    have htpos : OriginalSourceComplexPositive A.atlas (N-m) t.val := by
      simpa [OriginalSourceMMPositive,h,t] using hT
    obtain ⟨S,hS,huniq⟩ := original_source_positive_exists_unique_real A.atlas (N-m) t.val t.property htpos
    refine ⟨(sourceRealMMLowEquiv A m h).symm S,?_,?_⟩
    · apply (sourceRawComplexMMLowEquiv A m h).injective
      rw [sourceMMComplexify_low,sourceMMForget_low,Equiv.apply_symm_apply]
      exact hS
    · intro R hR
      apply (sourceRealMMLowEquiv A m h).injective
      rw [Equiv.apply_symm_apply]
      apply huniq
      have hread := congrArg (sourceRawComplexMMLowEquiv A m h) hR
      rwa [sourceMMComplexify_low,sourceMMForget_low] at hread
  · have hr : Subsingleton (OriginalSourceRealMMCurrent A m) :=
      sourceMM_high_real_subsingleton A m (Nat.lt_of_not_ge h)
    have hc : Subsingleton (OriginalSourceRawComplexMMCurrent A m) :=
      sourceMM_high_raw_complex_subsingleton A m (Nat.lt_of_not_ge h)
    have hunit : Nonempty (OriginalSourceRealMMCurrent A m) := by
      simpa [OriginalSourceRealMMCurrent,h] using (inferInstance : Nonempty PUnit.{u+1})
    refine ⟨Classical.choice hunit,@Subsingleton.elim _ hc _ _,?_⟩
    intro R _
    exact @Subsingleton.elim _ hr _ _

end SGPT.PSH.ComplexCurrentDraft
