import SGPT.Toric.TropicalBedfordTaylor
import SGPT.Toric.ProjectiveToricNewtonGeometry
import SGPT.Convex.AlexandrovMass

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory SGPT.Convex
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ}

/-- Actual canonical local BT total mass is the original factorial-normalized
volume of the independently defined finite Legendre-domain closure. -/
theorem tropicalCanonicalBTMeasure_univ_eq_convexNewtonBody
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f) :
    tropicalCanonicalBTMeasure hc univ = (n.factorial : ENNReal) * volume
      (convexNewtonBody (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun a => (f a : EReal)))) := by
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have htotal := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ univ)
    (tropicalization_canonicalBTMeasure_eq_alexandrov hc)
  rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ] at htotal
  have hp := isProper_coe_of_convexOn hc
  have hfull : effectiveDomain (fun a => (f a : EReal)) = univ := by
    ext a
    simp [effectiveDomain]
  have hlsc := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_isProper_full_domain hp hfull)
  calc
    _ = alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (fun a => (f a : EReal)) univ := htotal
    _ = ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n))).factorial : ENNReal) * volume
        (closure (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
          (fun a => (f a : EReal)))) :=
      alexandrovMeasure_univ_eq_closure_rawSubgradientImage _ hp hlsc
    _ = _ := by
      rw [← convexNewtonBody_conjugate_eq_closure_rawSubgradientImage _ hp hlsc]
      simp

/-- Genuine support-growth internally bounds the actual full local mass;
no conjugate-domain containment or finite-mass certificate is supplied. -/
theorem tropicalCanonicalBTMeasure_univ_le_of_mem_growthClass
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f)
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hconv : Convex ℝ P)
    (hf : (fun a => (f a : EReal)) ∈ GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) P) :
    tropicalCanonicalBTMeasure hc univ ≤ (n.factorial : ENNReal) * volume P := by
  have hsub : convexNewtonBody (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => (f a : EReal))) ⊆ P :=
    closure_minimal (effectiveDomain_conjugate_subset_of_mem_growthClass _ hP hconv hf)
      hP.isClosed
  rw [tropicalCanonicalBTMeasure_univ_eq_convexNewtonBody hc]
  exact mul_le_mul_right (measure_mono hsub) _

/-- The actual compact-body upper bound internally supplies a finite-measure
instance on the SAME canonical local measure, including dimension zero. -/
theorem isFiniteMeasure_tropicalCanonicalBTMeasure_of_mem_growthClass
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f)
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hconv : Convex ℝ P)
    (hf : (fun a => (f a : EReal)) ∈ GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) P) :
    IsFiniteMeasure (tropicalCanonicalBTMeasure hc) := by
  refine ⟨lt_of_le_of_lt (tropicalCanonicalBTMeasure_univ_le_of_mem_growthClass hc hP hconv hf) ?_⟩
  exact ENNReal.mul_lt_top (by simp) hP.measure_lt_top

/-- The original GEOMETRIC full-mass class gives the actual complex local
total via the completed generic real theorem, with the empty-interior branch. -/
theorem tropicalCanonicalBTMeasure_univ_eq_body_of_mem_fullMassClass
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f)
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P)
    (hf : (fun a => (f a : EReal)) ∈ FullMassClass (innerₗ (EuclideanSpace ℝ (Fin n))) P) :
    tropicalCanonicalBTMeasure hc univ = (n.factorial : ENNReal) * volume P := by
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have htotal := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ univ)
    (tropicalization_canonicalBTMeasure_eq_alexandrov hc)
  rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ] at htotal
  exact htotal.trans (by simpa using
    (alexandrovMeasure_univ_eq_body_of_mem_fullMassClass
      (innerₗ (EuclideanSpace ℝ (Fin n))) hP hne hconv hf))

end SGPT.Toric
