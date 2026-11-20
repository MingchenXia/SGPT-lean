import SGPT.Toric.OriginalGuilleminBoundaryJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth inverse germs for the original Guillemin corner map

The existing all-face minimizers and boundary Jacobian supply the actual
orthant inverse. The smooth inverse-function theorem produces ambient germs
for that same inverse at every boundary stratum. The resulting finite corner
weights retain the literal original entropy and Legendre reference.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology Classical ContDiff

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- At every original nonnegative tuple, the same actual orthant inverse has a
smooth ambient germ. Domain membership and both inverse identities are outputs. -/
theorem exists_originalGuilleminCornerInverse_smoothExtension (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (s₀ : Ici (0 : Fin n → ℝ)) :
    ∃ f : (Fin n → ℝ) → (Fin n → ℝ),
      ContDiffAt ℝ ∞ f s₀.val ∧
      f s₀.val = originalGuilleminCornerInverse γ hsmooth v s₀ ∧
      ∀ᶠ s in 𝓝 s₀.val,
        f s ∈ originalVertexCornerOpen γ hsmooth v ∧
        originalGuilleminCornerMap γ hsmooth v (f s) = s ∧
        ∀ hs : s ∈ Ici (0 : Fin n → ℝ),
          f s = originalGuilleminCornerInverse γ hsmooth v ⟨s, hs⟩ := by
  let x := originalGuilleminCornerInverse γ hsmooth v s₀
  have hx : x ∈ originalVertexCornerDomain γ hsmooth v :=
    originalGuilleminCornerInverse_mem_domain γ hsmooth v s₀
  have hS : originalGuilleminCornerMap γ hsmooth v x = s₀.val :=
    originalGuilleminCornerMap_inverse γ hsmooth v s₀
  have hdiff : ContDiffAt ℝ ∞ (originalGuilleminCornerMap γ hsmooth v) x :=
    (contDiffOn_originalGuilleminCornerMap γ hsmooth v).contDiffAt
      ((isOpen_originalVertexCornerOpen γ hsmooth v).mem_nhds hx.1)
  have hderiv : HasFDerivAt (originalGuilleminCornerMap γ hsmooth v)
      (originalCornerJacobianEquiv γ hsmooth v hx :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x := by
    rw [originalCornerJacobianEquiv_toContinuousLinearMap]
    exact hasFDerivAt_originalGuilleminCornerMap γ hsmooth v hx.1
  let f := hdiff.localInverse hderiv (by simp)
  have hf : ContDiffAt ℝ ∞ f s₀.val := by
    simpa only [hS] using hdiff.to_localInverse hderiv (by simp)
  have hf₀ : f s₀.val = x := by
    rw [← hS]
    exact hdiff.localInverse_apply_image hderiv (by simp)
  have htend : Tendsto f (𝓝 s₀.val) (𝓝 x) := by
    have h : Tendsto f (𝓝 s₀.val) (𝓝 (f s₀.val)) := hf.continuousAt
    simpa only [hf₀] using h
  have hopen : ∀ᶠ s in 𝓝 s₀.val, f s ∈ originalVertexCornerOpen γ hsmooth v :=
    htend.eventually ((isOpen_originalVertexCornerOpen γ hsmooth v).mem_nhds hx.1)
  have hright : ∀ᶠ s in 𝓝 s₀.val, originalGuilleminCornerMap γ hsmooth v (f s) = s := by
    simpa only [f, ContDiffAt.localInverse, hS] using
      (hdiff.hasStrictFDerivAt' hderiv (by simp)).eventually_right_inverse
  refine ⟨f, hf, hf₀, ?_⟩
  filter_upwards [hopen, hright] with s hsopen hsright
  refine ⟨hsopen, hsright, ?_⟩
  intro hs
  have hnonneg : ∀ j, 0 ≤ f s j := by
    intro j
    have hj : 0 ≤ originalGuilleminCornerMap γ hsmooth v (f s) j := by
      rw [hsright]
      exact hs j
    change 0 ≤ f s j * Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j (f s)) at hj
    by_contra hneg
    have hm := mul_neg_of_neg_of_pos (lt_of_not_ge hneg)
      (Real.exp_pos (1 + originalCornerRemainderPartial γ hsmooth v j (f s)))
    exact (not_lt_of_ge hj) hm
  exact (existsUnique_originalGuilleminCornerMap_preimage γ hsmooth v s hs).choose_spec.2
    (f s) ⟨⟨hsopen, hnonneg⟩, hsright⟩

/-- The existing orthant inverse is continuous in its actual subtype topology. -/
theorem continuous_originalGuilleminCornerInverse (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Continuous (originalGuilleminCornerInverse γ hsmooth v) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  obtain ⟨f, hf, _, heq⟩ :=
    exists_originalGuilleminCornerInverse_smoothExtension γ hsmooth v s₀
  have hc : ContinuousAt (fun s : Ici (0 : Fin n → ℝ) => f s.val) s₀ :=
    hf.continuousAt.comp continuous_subtype_val.continuousAt
  apply hc.congr_of_eventuallyEq
  have htend : Tendsto (Subtype.val : Ici (0 : Fin n → ℝ) → (Fin n → ℝ))
      (𝓝 s₀) (𝓝 s₀.val) := continuous_subtype_val.continuousAt
  filter_upwards [htend.eventually heq] with s hs
  exact (hs.2.2 s.property).symm

/-- The literal finite original corner Legendre expression, without a real
readback of an infinite entropy value. -/
def originalCornerLegendreValue (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (x : Fin n → ℝ) : ℝ :=
  (∑ j, x j * (1 + originalCornerRemainderPartial γ hsmooth v j x)) -
    originalVertexCornerRemainder γ hsmooth v x

/-- Existing original remainder and partial-derivative smoothness give the
actual finite expression on the genuine inactive-slack open set. -/
theorem contDiffOn_originalCornerLegendreValue (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiffOn ℝ ∞ (originalCornerLegendreValue γ hsmooth v)
      (originalVertexCornerOpen γ hsmooth v) := by
  unfold originalCornerLegendreValue
  apply ContDiffOn.sub
  · apply ContDiffOn.sum
    intro j _
    exact (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.contDiffOn.mul
      (contDiffOn_const.add (contDiffOn_originalCornerRemainderPartial γ hsmooth v j))
  · exact contDiffOn_originalVertexCornerRemainder γ hsmooth v

/-- The original finite corner weight on the whole closed orthant. -/
def originalGuilleminCornerWeight (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (s : Ici (0 : Fin n → ℝ)) : ℝ :=
  originalCornerLegendreValue γ hsmooth v (originalGuilleminCornerInverse γ hsmooth v s)

/-- The literal whole-chart canonical weight, including every coordinate zero. -/
def originalGuilleminComplexCornerWeight (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (w : Fin n → ℂ) : ℝ :=
  originalGuilleminCornerWeight γ hsmooth v
    ⟨fun j => Complex.normSq (w j), fun j => Complex.normSq_nonneg (w j)⟩

/-- Each actual inverse germ supplies smoothness of the SAME literal complex
weight. No smooth extension by zero or common smooth neighborhood is assumed. -/
theorem contDiff_originalGuilleminComplexCornerWeight (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiff ℝ ∞ (originalGuilleminComplexCornerWeight γ hsmooth v) := by
  let s : (Fin n → ℂ) → (Fin n → ℝ) := fun w j => Complex.normSq (w j)
  have hsmoothNorm : ContDiff ℝ ∞ s := by
    apply contDiff_pi.mpr
    intro j
    simp only [s, ← Complex.sq_norm]
    exact (contDiff_norm_sq ℝ).comp
      ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  rw [contDiff_iff_contDiffAt]
  intro w₀
  let s₀ : Ici (0 : Fin n → ℝ) := ⟨s w₀, fun j => Complex.normSq_nonneg (w₀ j)⟩
  obtain ⟨f, hf, hf₀, heq⟩ :=
    exists_originalGuilleminCornerInverse_smoothExtension γ hsmooth v s₀
  have hmem : f s₀.val ∈ originalVertexCornerOpen γ hsmooth v := by
    rw [hf₀]
    exact (originalGuilleminCornerInverse_mem_domain γ hsmooth v s₀).1
  have hR : ContDiffAt ℝ ∞ (originalCornerLegendreValue γ hsmooth v) (f s₀.val) :=
    (contDiffOn_originalCornerLegendreValue γ hsmooth v).contDiffAt
      ((isOpen_originalVertexCornerOpen γ hsmooth v).mem_nhds hmem)
  have hcomp : ContDiffAt ℝ ∞ (fun w =>
      originalCornerLegendreValue γ hsmooth v (f (s w))) w₀ :=
    ContDiffAt.comp (f := fun w => f (s w))
      (g := originalCornerLegendreValue γ hsmooth v) w₀ hR
      (ContDiffAt.comp (f := s) (g := f) w₀ hf hsmoothNorm.contDiffAt)
  apply hcomp.congr_of_eventuallyEq
  have htend : Tendsto s (𝓝 w₀) (𝓝 s₀.val) := hsmoothNorm.continuous.continuousAt
  filter_upwards [htend.eventually heq] with w hw
  change originalCornerLegendreValue γ hsmooth v
    (originalGuilleminCornerInverse γ hsmooth v
      ⟨s w, fun j => Complex.normSq_nonneg (w j)⟩) = _
  exact congrArg (originalCornerLegendreValue γ hsmooth v)
    (hw.2.2 (fun j => Complex.normSq_nonneg (w j))).symm

/-- The actual finite orthant weight is exactly the original extended
Legendre reference minus its original vertex linear term on the torus. -/
theorem originalGuilleminCornerWeight_exp_eq_reference (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (y : Fin n → ℝ) :
    originalGuilleminCornerWeight γ hsmooth v
      ⟨fun j => Real.exp (originalCoordinatePairing n
          (integerCast (originalVertexHalfspaceBasis γ hsmooth v j)) y),
        fun j => (Real.exp_pos (originalCoordinatePairing n
          (integerCast (originalVertexHalfspaceBasis γ hsmooth v j)) y)).le⟩ =
      (originalCanonicalReference γ hsmooth y).toReal -
        originalCoordinatePairing n (integerCast v.val) y := by
  obtain ⟨x, hx, _, hval, hstation⟩ :=
    exists_originalCanonicalReference_corner_attainment γ hsmooth v y
  have hdom := originalVertexCornerStrict_subset_domain γ hsmooth v hx
  let s₀ : Ici (0 : Fin n → ℝ) :=
    ⟨fun j => Real.exp (originalCoordinatePairing n
        (integerCast (originalVertexHalfspaceBasis γ hsmooth v j)) y),
      fun j => (Real.exp_pos (originalCoordinatePairing n
        (integerCast (originalVertexHalfspaceBasis γ hsmooth v j)) y)).le⟩
  have hmap : originalGuilleminCornerMap γ hsmooth v x = s₀.val := by
    ext j
    have hj := hstation ⟨j, by simp⟩
    change Real.log (x j) + 1 + originalCornerRemainderPartial γ hsmooth v j x =
      originalCoordinatePairing n (integerCast (originalVertexHalfspaceBasis γ hsmooth v j)) y at hj
    change x j * Real.exp (1 + originalCornerRemainderPartial γ hsmooth v j x) =
      Real.exp (originalCoordinatePairing n
        (integerCast (originalVertexHalfspaceBasis γ hsmooth v j)) y)
    have he := congrArg Real.exp hj
    rw [show Real.log (x j) + 1 + originalCornerRemainderPartial γ hsmooth v j x =
      Real.log (x j) + (1 + originalCornerRemainderPartial γ hsmooth v j x) by ring,
      Real.exp_add, Real.exp_log (originalVertexCornerStrict_coord_pos γ hsmooth v hx j)] at he
    exact he
  have hinv : originalGuilleminCornerInverse γ hsmooth v s₀ = x := by
    simpa only [hmap] using originalGuilleminCornerInverse_map γ hsmooth v hdom
  change originalCornerLegendreValue γ hsmooth v
    (originalGuilleminCornerInverse γ hsmooth v s₀) = _
  rw [hinv]
  have hxsum : x = ∑ j, x j • Pi.basisFun ℝ (Fin n) j := by
    ext j
    simp [Pi.basisFun_apply, Pi.single_apply]
  have htilt : originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) x =
      ∑ j, x j * (Real.log (x j) + 1 + originalCornerRemainderPartial γ hsmooth v j x) := by
    calc
      originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) x =
          originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y)
            (∑ j, x j • Pi.basisFun ℝ (Fin n) j) := congrArg _ hxsum
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
        have hb : originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y)
            (Pi.basisFun ℝ (Fin n) j) =
              Real.log (x j) + 1 + originalCornerRemainderPartial γ hsmooth v j x := by
          rw [← originalCornerFreeEmbedding_basis ∅ ⟨j, by simp⟩,
            originalCornerFaceTilt_free_basis]
          exact (hstation ⟨j, by simp⟩).symm
        rw [hb]
        rfl
  have hreal : (originalCanonicalReference γ hsmooth y).toReal =
      originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v x) y -
        originalVertexCornerEntropyReal γ hsmooth v x := by
    rw [hval, EReal.toReal_coe]
  rw [hreal, originalCornerPoint_pairing, originalVertexCornerEntropyReal_split, htilt]
  have hsum : (∑ j, x j * (Real.log (x j) + 1 +
      originalCornerRemainderPartial γ hsmooth v j x)) =
      (∑ j, x j * Real.log (x j)) +
        ∑ j, x j * (1 + originalCornerRemainderPartial γ hsmooth v j x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  unfold originalCornerLegendreValue
  ring

end SGPT.Toric
