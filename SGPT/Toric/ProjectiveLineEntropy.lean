import SGPT.Toric.FacetEntropy
import SGPT.Convex.HalfLine
import SGPT.Convex.DerivativeConvergence
import SGPT.Toric.TropicalHessian

set_option autoImplicit false

noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Topology

/-- The original two projective-line facets have values m and 1-m. -/
def projectiveLineFacets : Fin 2 → ℝ →L[ℝ] ℝ :=
  ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ]

/-- The original facet offsets are zero and one. -/
def projectiveLineOffsets : Fin 2 → ℝ := ![0, 1]

/-- Literal entropy on the original closed interval, with 0 log 0 = 0. -/
def projectiveLineEntropyReal : ℝ → ℝ :=
  facetEntropyReal projectiveLineFacets projectiveLineOffsets

/-- The source projective-line entropy retains top values off its original interval. -/
def projectiveLineEntropy : ℝ → EReal :=
  facetEntropy projectiveLineFacets projectiveLineOffsets

/-- The actual logistic point that will attain the original conjugate supremum. -/
def projectiveLineLogistic (x : ℝ) : ℝ := Real.exp x / (1 + Real.exp x)

/-- Literal source log-partition function, with its original normalization. -/
def projectiveLineLogPartition (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

theorem projectiveLineFacetRegion_eq :
    facetRegion projectiveLineFacets projectiveLineOffsets = Icc 0 1 := by
  ext m
  constructor
  · intro hm
    constructor
    · simpa [facetValue, projectiveLineFacets, projectiveLineOffsets] using hm 0
    · have h := hm 1
      simp only [facetValue, projectiveLineFacets, projectiveLineOffsets,
        Matrix.cons_val_one, Matrix.cons_val_zero, neg_apply,
        ContinuousLinearMap.id_apply] at h
      linarith
  · intro hm i
    fin_cases i
    · simpa [facetValue, projectiveLineFacets, projectiveLineOffsets] using hm.1
    · simpa [facetValue, projectiveLineFacets, projectiveLineOffsets] using
        (sub_nonneg.mpr hm.2)

theorem projectiveLineEntropyReal_eq (m : ℝ) :
    projectiveLineEntropyReal m = m * Real.log m + (1-m) * Real.log (1-m) := by
  simp [projectiveLineEntropyReal, facetEntropyReal, facetValue,
    projectiveLineFacets, projectiveLineOffsets, Fin.sum_univ_two, sub_eq_add_neg,
    add_comm]

theorem projectiveLineEntropy_eq (m : ℝ) :
    projectiveLineEntropy m =
      if m ∈ Icc 0 1 then ((m * Real.log m + (1-m) * Real.log (1-m) : ℝ) : EReal) else ⊤ := by
  simp only [projectiveLineEntropy, facetEntropy, projectiveLineFacetRegion_eq]
  change (if m ∈ Icc 0 1 then (projectiveLineEntropyReal m : EReal) else ⊤) = _
  rw [projectiveLineEntropyReal_eq]

theorem convexOn_projectiveLineEntropyReal :
    ConvexOn ℝ (Icc 0 1) projectiveLineEntropyReal := by
  simpa only [projectiveLineEntropyReal, projectiveLineFacetRegion_eq] using
    convexOn_facetEntropyReal projectiveLineFacets projectiveLineOffsets

theorem isClosedConvex_projectiveLineEntropy : IsClosedConvex projectiveLineEntropy := by
  apply isClosedConvex_facetEntropy
  rw [projectiveLineFacetRegion_eq]
  exact ⟨0, by simp⟩

theorem projectiveLineLogistic_mem (x : ℝ) : projectiveLineLogistic x ∈ Ioo 0 1 := by
  have hx := Real.exp_pos x
  have hd : 0 < 1 + Real.exp x := by positivity
  exact ⟨div_pos hx hd, (div_lt_one hd).mpr (by linarith)⟩

theorem one_sub_projectiveLineLogistic (x : ℝ) :
    1 - projectiveLineLogistic x = 1 / (1 + Real.exp x) := by
  have hd : 1 + Real.exp x ≠ 0 := by positivity
  dsimp [projectiveLineLogistic]
  field_simp
  ring

theorem log_projectiveLineLogistic (x : ℝ) :
    Real.log (projectiveLineLogistic x) = x - projectiveLineLogPartition x := by
  exact (Real.log_div (Real.exp_pos x).ne' (by positivity)).trans
    (by rw [Real.log_exp]; rfl)

theorem log_one_sub_projectiveLineLogistic (x : ℝ) :
    Real.log (1 - projectiveLineLogistic x) = -projectiveLineLogPartition x := by
  rw [one_sub_projectiveLineLogistic,
    Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub]
  rfl

theorem projectiveLineEntropyReal_logistic (x : ℝ) :
    projectiveLineEntropyReal (projectiveLineLogistic x) =
      x * projectiveLineLogistic x - projectiveLineLogPartition x := by
  rw [projectiveLineEntropyReal_eq, log_projectiveLineLogistic,
    log_one_sub_projectiveLineLogistic]
  ring

/-- The previously proved facet derivative gives the actual scalar entropy derivative. -/
theorem hasDerivAt_projectiveLineEntropyReal {m : ℝ} (hm : m ∈ Ioo 0 1) :
    HasDerivAt projectiveLineEntropyReal (Real.log m - Real.log (1-m)) m := by
  have hx : m ∈ interior (facetRegion projectiveLineFacets projectiveLineOffsets) := by
    rw [projectiveLineFacetRegion_eq, interior_Icc]
    exact hm
  have h := (hasFDerivAt_facetEntropyReal_of_mem_interior
    projectiveLineFacets projectiveLineOffsets hx).hasDerivAt
  change HasDerivAt projectiveLineEntropyReal _ m at h
  have heq : ((∑ i, (Real.log (facetValue projectiveLineFacets projectiveLineOffsets i m) + 1) •
      projectiveLineFacets i) 1) = Real.log m - Real.log (1-m) := by
    simp [Fin.sum_univ_two, facetValue, projectiveLineFacets,
      projectiveLineOffsets, sub_eq_add_neg, add_comm]
    ring
  rwa [heq] at h

/-- The original logistic point has actual derivative equal to the conjugate argument. -/
theorem hasDerivAt_projectiveLineEntropyReal_logistic (x : ℝ) :
    HasDerivAt projectiveLineEntropyReal x (projectiveLineLogistic x) := by
  simpa only [log_projectiveLineLogistic, log_one_sub_projectiveLineLogistic,
    sub_neg_eq_add, sub_add_cancel] using
    hasDerivAt_projectiveLineEntropyReal (projectiveLineLogistic_mem x)

/-- Reuse the actual origin tangent producer after a genuine affine translation. -/
theorem projectiveLineEntropyReal_tangent_logistic (x : ℝ) {m : ℝ} (hm : m ∈ Icc 0 1) :
    projectiveLineEntropyReal (projectiveLineLogistic x) +
      x * (m - projectiveLineLogistic x) ≤ projectiveLineEntropyReal m := by
  let q := projectiveLineLogistic x
  let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ q + AffineMap.id ℝ ℝ
  have hA (t : ℝ) : A t = q + t := rfl
  have hcv := convexOn_projectiveLineEntropyReal.comp_affineMap A
  have hzero : 0 ∈ A ⁻¹' Icc 0 1 := by
    change A 0 ∈ Icc 0 1
    rw [hA, add_zero]
    exact Ioo_subset_Icc_self (projectiveLineLogistic_mem x)
  have hd : HasDerivAt (projectiveLineEntropyReal ∘ A) x 0 := by
    have hg : HasDerivAt projectiveLineEntropyReal x (q + id 0) := by
      simpa only [id_eq, add_zero, q] using hasDerivAt_projectiveLineEntropyReal_logistic x
    simpa only [Function.comp_def, hA, id_eq, mul_one] using
      hg.comp 0 ((hasDerivAt_id 0).const_add q)
  have hpoint : m-q ∈ A ⁻¹' Icc 0 1 := by
    change A (m-q) ∈ Icc 0 1
    rw [hA, add_sub_cancel]
    exact hm
  have h := convex_origin_tangent_le hcv hzero hd.differentiableAt hpoint
  simp only [Function.comp_apply, hA, add_zero, add_sub_cancel, hd.deriv] at h
  simpa only [q, mul_comm] using h

/-- The original logistic point attains the literal conjugate supremum. -/
theorem conjugate_projectiveLineEntropy (x : ℝ) :
    conjugate scalarPairing projectiveLineEntropy x = (projectiveLineLogPartition x : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro m
    by_cases hm : m ∈ Icc 0 1
    · have h := projectiveLineEntropyReal_tangent_logistic x hm
      rw [projectiveLineEntropyReal_logistic] at h
      have hb : m * x - projectiveLineEntropyReal m ≤ projectiveLineLogPartition x := by
        nlinarith
      simpa only [scalarPairing, LinearMap.mul_apply', projectiveLineEntropy,
        facetEntropy, projectiveLineFacetRegion_eq, if_pos hm, projectiveLineEntropyReal,
        ← EReal.coe_sub] using EReal.coe_le_coe hb
    · simp [projectiveLineEntropy, facetEntropy, projectiveLineFacetRegion_eq, hm]
  · have h := le_iSup (fun m ↦ (scalarPairing m x : EReal) - projectiveLineEntropy m)
      (projectiveLineLogistic x)
    have hq : projectiveLineLogistic x ∈ Icc 0 1 :=
      Ioo_subset_Icc_self (projectiveLineLogistic_mem x)
    have heq : (scalarPairing (projectiveLineLogistic x) x : EReal) -
        projectiveLineEntropy (projectiveLineLogistic x) = (projectiveLineLogPartition x : EReal) := by
      rw [projectiveLineEntropy_eq, if_pos hq, ← projectiveLineEntropyReal_eq,
        projectiveLineEntropyReal_logistic]
      simp only [scalarPairing, LinearMap.mul_apply', ← EReal.coe_sub]
      congr 1
      ring
    rwa [heq] at h

/-- Actual nonzero squared norm recovers the source log-square pullback exactly. -/
theorem projectiveLineLogPartition_log_normSq {z : ℂ} (hz : z ≠ 0) :
    projectiveLineLogPartition (Real.log (Complex.normSq z)) =
      Real.log (1 + Complex.normSq z) := by
  have hp : 0 < Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hz) 2
  simp only [projectiveLineLogPartition, Real.exp_log hp]

/-- Literal original open-torus potential; no global projective chart is substituted. -/
theorem projectiveLineLogPartition_tropicalization {z : ComplexModel 1}
    (hz : z 0 ≠ 0) :
    projectiveLineLogPartition (tropicalization z 0) = Real.log (1 + Complex.normSq (z 0)) := by
  rw [tropicalization_apply_eq_log_norm_sq, ← Complex.normSq_eq_norm_sq]
  exact projectiveLineLogPartition_log_normSq hz

/-- The genuine local identity preserves the complete normalized source ddC form. -/
theorem smoothDDC_projectiveLine_tropicalization {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    smoothDDC (fun w : ComplexModel 1 ↦ projectiveLineLogPartition (tropicalization w 0)) z =
      smoothDDC (fun w : ComplexModel 1 ↦ Real.log (1 + Complex.normSq (w 0))) z := by
  have hO : IsOpen {w : ComplexModel 1 | w 0 ≠ 0} :=
    isOpen_ne.preimage (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 ↦ ℂ) 0).continuous
  apply smoothDDC_congr
  filter_upwards [hO.mem_nhds hz] with w hw
  exact projectiveLineLogPartition_tropicalization hw

end SGPT.Toric
