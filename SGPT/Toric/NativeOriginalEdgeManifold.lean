import SGPT.Toric.NativeOriginalEdgeAnalyticCharts
import SGPT.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Topology Manifold ContDiff

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The genuine original closure is compact in its SAME quotient-subspace topology. -/
instance originalPolytopeNativeCompactSpace (γ : K → Fin n → ℤ) :
    CompactSpace (originalPolytopeNativeSpace γ) :=
  compactSpace_monomialProjectiveOrbitClosure (originalPolytopeFullExponents γ)

/-- Genuine Hausdorffness is inherited from that SAME original projectivization. -/
instance originalPolytopeNativeT2Space (γ : K → Fin n → ℤ) :
    T2Space (originalPolytopeNativeSpace γ) :=
  t2Space_monomialProjectiveOrbitClosure (originalPolytopeFullExponents γ)

/-- The actual original vertex charts give a native charted space on the
UNCHANGED original topological carrier. All atlas membership is literal. -/
@[instance_reducible]
def originalPolytopeNativeChartedSpace (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    ChartedSpace (ComplexModel n) (originalPolytopeNativeSpace γ) where
  atlas := Set.range (originalPolytopeNativeModelChart γ hsmooth)
  chartAt := fun p => originalPolytopeNativeModelChart γ hsmooth
    (originalPolytopeNativeModelChart_cover γ hsmooth p).choose
  mem_chart_source := fun p => (originalPolytopeNativeModelChart_cover γ hsmooth p).choose_spec
  chart_mem_atlas := fun p => ⟨(originalPolytopeNativeModelChart_cover γ hsmooth p).choose, rfl⟩

/-- The specified native atlas consists of ALL actual original vertex charts. -/
theorem mem_originalPolytopeNativeAtlas_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ)
    (e : OpenPartialHomeomorph (originalPolytopeNativeSpace γ) (ComplexModel n)) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    e ∈ atlas (ComplexModel n) (originalPolytopeNativeSpace γ) ↔
      ∃ v, originalPolytopeNativeModelChart γ hsmooth v = e := Iff.rfl

/-- Every actual complex smoothness order is manufactured by the genuine
analytic overlaps and the existing native manifold constructor. -/
theorem originalPolytopeNativeIsManifold (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (r : ℕ∞ω) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    IsManifold 𝓘(ℂ, ComplexModel n) r (originalPolytopeNativeSpace γ) := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  apply isManifold_of_contDiffOn 𝓘(ℂ, ComplexModel n) r (originalPolytopeNativeSpace γ)
  intro e f he hf
  obtain ⟨v, rfl⟩ := he
  obtain ⟨w, rfl⟩ := hf
  simpa only [originalPolytopeNativeModelTransition, mfld_simps] using
    contDiffOn_originalPolytopeNativeModelTransition γ hsmooth v w r

/-- The SAME native charts also give the genuine underlying real manifold. -/
theorem originalPolytopeNativeRealIsManifold (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (r : ℕ∞ω) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    IsManifold 𝓘(ℝ, ComplexModel n) r (originalPolytopeNativeSpace γ) := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  apply isManifold_of_contDiffOn 𝓘(ℝ, ComplexModel n) r (originalPolytopeNativeSpace γ)
  intro e f he hf
  obtain ⟨v, rfl⟩ := he
  obtain ⟨w, rfl⟩ := hf
  simpa only [originalPolytopeNativeModelTransition, mfld_simps] using
    contDiffOn_real_originalPolytopeNativeModelTransition γ hsmooth v w r

/-- Genuine compactness and the produced native atlas imply second countability. -/
theorem originalPolytopeNativeSecondCountable (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    SecondCountableTopology (originalPolytopeNativeSpace γ) := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  exact ChartedSpace.secondCountable_of_sigmaCompact (ComplexModel n) (originalPolytopeNativeSpace γ)

/-- An actual compact complex manifold, produced ONLY from original source
generators and book ALL-edge smoothness, with no manifold certificate input. -/
theorem originalPolytopeNativeIsComplexManifold (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    IsComplexManifold n (originalPolytopeNativeSpace γ) := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  exact {
    toT2Space := inferInstance
    toSecondCountableTopology := originalPolytopeNativeSecondCountable γ hsmooth
    toIsManifold := originalPolytopeNativeIsManifold γ hsmooth ∞ }

/-- The actual Borel sigma algebra of the unchanged original topological space. -/
instance originalPolytopeNativeMeasurableSpace (γ : K → Fin n → ℤ) :
    MeasurableSpace (originalPolytopeNativeSpace γ) := borel _

instance originalPolytopeNativeBorelSpace (γ : K → Fin n → ℤ) :
    BorelSpace (originalPolytopeNativeSpace γ) := ⟨rfl⟩

/-- Every actual original vertex chart belongs to this specified native atlas. -/
def originalPolytopeNativeComplexChart (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    ComplexChart n (originalPolytopeNativeSpace γ) :=
  ⟨originalPolytopeNativeModelChart γ hsmooth v, ⟨v, rfl⟩⟩

/-- No additional unspecified charts enter the native boundary assertions. -/
theorem originalPolytopeNativeComplexChart_exhaustive (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    ∀ e : ComplexChart n (originalPolytopeNativeSpace γ),
      ∃ v, e = originalPolytopeNativeComplexChart γ hsmooth v := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  intro e
  obtain ⟨v, hv⟩ := e.property
  exact ⟨v, Subtype.ext hv.symm⟩

/-- Literal boundary of the SAME original monomial torus, with no replacement orbit. -/
def originalPolytopeNativeBoundary (γ : K → Fin n → ℤ) : Set (originalPolytopeNativeSpace γ) :=
  {p | p.val ∉ Set.range (monomialProjectiveOrbit (originalPolytopeFullExponents γ))}

/-- Actual coordinate polynomial in the genuine native Euclidean model. -/
def originalPolytopeNativeBoundaryPolynomial (n : ℕ) (z : ComplexModel n) : ℂ :=
  ∏ j : Fin n, originalPolytopeNativeModelEquiv n z j

/-- The SAME original boundary is precisely the coordinate-product zero set in
EVERY original native chart, including the empty product one in dimension zero. -/
theorem originalPolytopeNativeBoundary_chart_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    (originalPolytopeNativeModelChart γ hsmooth v).symm z ∈ originalPolytopeNativeBoundary γ ↔
      originalPolytopeNativeBoundaryPolynomial n z = 0 :=
  (originalPolytopeNativePiChart_spec γ hsmooth v).2.2.2.2.1
    (originalPolytopeNativeModelEquiv n z)

/-- Genuine finite polynomial analyticity, using the actual continuous model map. -/
theorem analyticAt_originalPolytopeNativeBoundaryPolynomial (n : ℕ) (z : ComplexModel n) :
    AnalyticAt ℂ (originalPolytopeNativeBoundaryPolynomial n) z := by
  apply Finset.analyticAt_fun_prod Finset.univ
  intro j _
  exact ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _).comp
    ((originalPolytopeNativeModelEquiv n).toContinuousLinearMap.analyticAt z)

/-- A genuine nonzero point of the actual polynomial, also when the product is empty. -/
theorem originalPolytopeNativeBoundaryPolynomial_one (n : ℕ) :
    originalPolytopeNativeBoundaryPolynomial n
      ((originalPolytopeNativeModelEquiv n).symm (fun _ => 1)) = 1 := by
  simp [originalPolytopeNativeBoundaryPolynomial]

/-- The actual polynomial is holomorphic on the whole native Euclidean model. -/
theorem differentiable_originalPolytopeNativeBoundaryPolynomial (n : ℕ) :
    Differentiable ℂ (originalPolytopeNativeBoundaryPolynomial n) :=
  fun z => (analyticAt_originalPolytopeNativeBoundaryPolynomial n z).differentiableAt

/-- Genuine holomorphic zero-set nullity applies to the ORIGINAL boundary in
every original vertex chart, without any positive-dimension hypothesis. -/
theorem originalPolytopeNativeBoundary_chart_volume_eq_zero (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    volume {z : ComplexModel n |
      (originalPolytopeNativeModelChart γ hsmooth v).symm z ∈ originalPolytopeNativeBoundary γ} = 0 := by
  have h := Pending.HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero volume
    isOpen_univ (convex_univ : Convex ℝ (Set.univ : Set (ComplexModel n)))
    (differentiable_originalPolytopeNativeBoundaryPolynomial n).differentiableOn
    (x₁ := (originalPolytopeNativeModelEquiv n).symm (fun _ => 1)) (Set.mem_univ _)
    (by rw [originalPolytopeNativeBoundaryPolynomial_one]; exact one_ne_zero)
  have heq : {z : ComplexModel n |
      (originalPolytopeNativeModelChart γ hsmooth v).symm z ∈ originalPolytopeNativeBoundary γ} =
      Set.univ ∩ originalPolytopeNativeBoundaryPolynomial n ⁻¹' {0} := by
    ext z
    simpa only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, true_and,
      Set.mem_preimage, Set.mem_singleton_iff] using
        originalPolytopeNativeBoundary_chart_iff γ hsmooth v z
  rwa [heq]

/-- Every specified native chart has WHOLE target, by actual atlas exhaustion. -/
theorem originalPolytopeNativeComplexChart_target (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    ∀ e : ComplexChart n (originalPolytopeNativeSpace γ), e.val.target = Set.univ := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  intro e
  obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hsmooth e
  exact originalPolytopeNativeModelChart_target γ hsmooth v

/-- Literal boundary readback in ALL specified native complex charts. -/
theorem originalPolytopeNativeBoundary_all_chart_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    ∀ (e : ComplexChart n (originalPolytopeNativeSpace γ)) (z : ComplexModel n),
      e.val.symm z ∈ originalPolytopeNativeBoundary γ ↔
        originalPolytopeNativeBoundaryPolynomial n z = 0 := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  intro e z
  obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hsmooth e
  exact originalPolytopeNativeBoundary_chart_iff γ hsmooth v z

/-- Nullity in EVERY actual native chart, rather than a selected preferred chart. -/
theorem originalPolytopeNativeBoundary_all_chart_volume_eq_zero (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    ∀ e : ComplexChart n (originalPolytopeNativeSpace γ),
      volume {z : ComplexModel n | e.val.symm z ∈ originalPolytopeNativeBoundary γ} = 0 := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  intro e
  obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hsmooth e
  exact originalPolytopeNativeBoundary_chart_volume_eq_zero γ hsmooth v

/-- A true one-generator holomorphic presentation in the actual preferred
native chart at EVERY point proves that the ORIGINAL boundary is analytic. -/
theorem isComplexAnalyticSubset_originalPolytopeNativeBoundary (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    letI := originalPolytopeNativeIsComplexManifold γ hsmooth
    IsComplexAnalyticSubset (n := n) (originalPolytopeNativeBoundary γ) := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  let := originalPolytopeNativeIsComplexManifold γ hsmooth
  intro p
  refine ⟨{ generatorCount := 1
            generator := fun _ => originalPolytopeNativeBoundaryPolynomial n
            coordinateNeighborhood := Set.univ
            isOpen_coordinateNeighborhood := isOpen_univ
            center_mem_coordinateNeighborhood := Set.mem_univ _
            coordinateNeighborhood_subset_target := ?_
            generator_holomorphic := fun _ =>
              (differentiable_originalPolytopeNativeBoundaryPolynomial n).differentiableOn
            zeroLocus := ?_ }⟩
  · rw [originalPolytopeNativeComplexChart_target γ hsmooth]
  · intro y hy _
    have h := originalPolytopeNativeBoundary_all_chart_iff γ hsmooth
      (complexChartAt (n := n) p) ((complexChartAt (n := n) p).val y)
    rw [(complexChartAt (n := n) p).val.left_inv hy] at h
    simpa only [Fin.forall_fin_one] using h

end SGPT.Toric
