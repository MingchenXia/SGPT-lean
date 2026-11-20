import SGPT.Foundations.Analysis.Pending.DistributionCauchyGreenTranspose
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-! Actual arbitrary complex-distribution Dolbeault primitives. The complete
BP statements and ENTIRE proofs precede this source. No scalar ddC or global
Bott--Chern class is asserted here. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Complex Metric
open scoped ContDiff Distributions Topology
namespace SGPT.Foundations.Analysis.Pending.DistributionDolbeaultOne
open CauchyGreen DistributionCauchyGreenTranspose

variable {n : ℕ}
abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev ComplexDistribution (Ω : Opens (E n)) := 𝓓(Ω, ℂ) →L[ℂ] ℂ
variable {Ω U W : Opens (E n)}

/-- The derivative acts on the actual original complex tests by transpose. -/
def dbar (v : E n) (T : ComplexDistribution Ω) : ComplexDistribution Ω :=
  -(T.comp (dbarTestCLM v))

/-- Original test inclusion gives restriction of the actual distribution. -/
def restrict (T : ComplexDistribution Ω) (_hU : U ≤ Ω) : ComplexDistribution U :=
  T.comp (TestFunction.monoCLM ℂ)

private theorem derivative_apply (v : E n) (φ : 𝓓(Ω, ℂ)) (y : E n) :
    dbarTestCLM v φ y = dbarDir v φ y := by
  change (2:ℂ)⁻¹ *
    ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v φ) y +
      I * (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (I • v) φ) y) = _
  simp only [TestFunction.lineDerivCLM_apply, le_top, ↓reduceIte]
  rw [(φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv]
  simp only [dbarDir]
  ring

private theorem inclusion_apply (hU : U ≤ Ω) (φ : 𝓓(U, ℂ)) :
    ((TestFunction.monoCLM ℂ φ : 𝓓(Ω, ℂ)) : E n → ℂ) = φ := by
  simp [TestFunction.monoCLM_apply, hU]

@[simp] theorem dbar_sub (v : E n) (T S : ComplexDistribution Ω) :
    dbar v (T-S) = dbar v T - dbar v S := by
  ext φ
  simp [dbar, neg_sub]
  ring

@[simp] theorem dbar_add (v : E n) (T S : ComplexDistribution Ω) :
    dbar v (T+S) = dbar v T + dbar v S := by
  ext φ
  simp [dbar, neg_add_rev, add_comm]

@[simp] theorem dbar_zero (v : E n) : dbar v (0 : ComplexDistribution Ω) = 0 := by
  ext φ
  simp [dbar]

@[simp] theorem restrict_sub (hU : U ≤ Ω) (T S : ComplexDistribution Ω) :
    restrict (T-S) hU = restrict T hU - restrict S hU := by
  ext φ
  simp [restrict]

private theorem dbar_restrict (v : E n) (T : ComplexDistribution Ω) (hU : U ≤ Ω) :
    dbar v (restrict T hU) = restrict (dbar v T) hU := by
  ext φ
  change -T (TestFunction.monoCLM ℂ (dbarTestCLM v φ)) =
    -T (dbarTestCLM v (TestFunction.monoCLM ℂ φ))
  congr 2
  ext y
  rw [inclusion_apply hU, derivative_apply, derivative_apply]
  exact congrArg (fun f => dbarDir v f y) (inclusion_apply hU φ).symm

private theorem restrict_trans (T : ComplexDistribution Ω) (hU : U ≤ Ω) (hW : W ≤ U) :
    restrict (restrict T hU) hW = restrict T (hW.trans hU) := by
  ext φ
  change T (TestFunction.monoCLM ℂ (TestFunction.monoCLM ℂ φ : 𝓓(U, ℂ))) =
    T (TestFunction.monoCLM ℂ φ)
  congr 1
  ext y
  rw [inclusion_apply hU, inclusion_apply hW, inclusion_apply (hW.trans hU)]

private theorem dbar_comm (u v : E n) (T : ComplexDistribution Ω) :
    dbar u (dbar v T) = dbar v (dbar u T) := by
  ext φ
  change -(-T (dbarTestCLM v (dbarTestCLM u φ))) =
    -(-T (dbarTestCLM u (dbarTestCLM v φ)))
  simp only [neg_neg]
  congr 1
  ext y
  rw [derivative_apply, derivative_apply]
  have hu : (dbarTestCLM u φ : E n → ℂ) = dbarDir u φ := funext (derivative_apply u φ)
  have hv : (dbarTestCLM v φ : E n → ℂ) = dbarDir v φ := funext (derivative_apply v φ)
  rw [hu, hv]
  exact dbarDir_dbarDir_comm (φ.contDiff.contDiffAt.of_le (by norm_cast))

private theorem cauchyGreen_derivative_eq (j : Fin n) (φ : 𝓓(U, ℂ)) (y : E n) :
    cauchyGreen (basisVec j) (dbarTestCLM (basisVec j) φ) y = φ y := by
  have hj : basisVec j ≠ 0 := by simp [basisVec]
  have hc : ContDiff ℝ 1 φ := φ.contDiff.of_le (by simp)
  have hcomm := dbarDir_cauchyGreen_comm hc φ.hasCompactSupport hj (basisVec j) y
  have hi := dbarDir_cauchyGreen hc φ.hasCompactSupport hj y
  have heq : (dbarTestCLM (basisVec j) φ : E n → ℂ) =
      dbarDir (basisVec j) φ := funext (derivative_apply _ φ)
  rw [heq, ← hcomm, hi]

private theorem cutoff_derivative_comm (x : E n) {r : ℝ} (hr : 0 < r)
    (χ : 𝓓(Ω, ℂ)) (hχ : (χ : E n → ℂ) = fun z => (polydiscCutoff x hr z : ℂ))
    (hU : (U : Set (E n)) = {z | ∀ k, ‖z k-x k‖ < r})
    (i j : Fin n) (hij : i ≠ j) (φ : 𝓓(U, ℂ)) :
    dbarTestCLM (basisVec i) (cutoffTestCLM (v := basisVec j) χ (by simp [basisVec]) φ) =
      cutoffTestCLM (v := basisVec j) χ (by simp [basisVec]) (dbarTestCLM (basisVec i) φ) := by
  ext y
  rw [derivative_apply, cutoffTestCLM_apply]
  have hH : (cutoffTestCLM (v := basisVec j) χ (by simp [basisVec]) φ : E n → ℂ) =
      fun z => (polydiscCutoff x hr z : ℂ) * cauchyGreen (basisVec j) φ z := by
    funext z
    rw [cutoffTestCLM_apply, hχ]
  rw [hH, dbarDir_ofReal_mul ((contDiff_polydiscCutoff x hr).differentiable (by simp) y)
    ((contDiff_cauchyGreen φ.contDiff φ.hasCompactSupport
      (show basisVec j ≠ 0 by simp [basisVec])).differentiable (by simp) y),
    dbarDir_cauchyGreen_comm (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
      (show basisVec j ≠ 0 by simp [basisVec]), hχ]
  have heq : (dbarTestCLM (basisVec i) φ : E n → ℂ) =
      dbarDir (basisVec i) φ := funext (derivative_apply _ φ)
  rw [heq]
  have hzero : dbarDir (basisVec i) (fun z => (polydiscCutoff x hr z : ℂ)) y *
      cauchyGreen (basisVec j) φ y = 0 := by
    by_cases hy : ‖y i-x i‖ < r
    · rw [dbarDir_polydiscCutoff_eq_zero x hr hy, zero_mul]
    · have hf (w : ℂ) : φ (y-w • basisVec j) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        have hm := φ.tsupport_subset hs
        rw [hU] at hm
        have hcoord : (y-w • basisVec j) i = y i := by simp [basisVec, hij]
        exact hy (by simpa only [hcoord] using hm i)
      simp [cauchyGreen, hf]
  rw [hzero, zero_add]

/-- The cutoff and inner domain are internal, and the same solution preserves
all other zero coordinate derivatives. -/
theorem exists_preserving_solution (T : ComplexDistribution Ω) (j : Fin n)
    (x : E n) (hx : x ∈ Ω) :
    ∃ (U : Opens (E n)) (hU : U ≤ Ω) (S : ComplexDistribution U),
      x ∈ U ∧ dbar (basisVec j) S = restrict T hU ∧
      ∀ i : Fin n, i ≠ j → dbar (basisVec i) T = 0 → dbar (basisVec i) S = 0 := by
  classical
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  let r : ℝ := δ / (2 * (n+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hpoly (z : E n) (hz : ∀ k, ‖z k-x k‖ ≤ 2*r) : z ∈ Ω := by
    apply hδΩ
    rw [mem_ball, dist_eq_norm]
    calc ‖z-x‖ ≤ n*(2*r) := norm_sub_le_of_coord_le x (by positivity) hz
      _ < δ := by
        dsimp [r]
        have hn : (0:ℝ) < n+1 := by positivity
        rw [show (n:ℝ)*(2*(δ/(2*(n+1)))) = δ*(n/(n+1)) by field_simp]
        have : (n:ℝ)/(n+1) < 1 := by rw [div_lt_one hn]; linarith
        nlinarith
  let V : Set (E n) := {z | ∀ k, ‖z k-x k‖ < r}
  have hVopen : IsOpen V := by
    simp only [V, ofPred_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt
      (continuous_norm.comp ((EuclideanSpace.proj k : E n →L[ℂ] ℂ).continuous.sub continuous_const))
      continuous_const
  let U : Opens (E n) := ⟨V,hVopen⟩
  have hU : U ≤ Ω := fun z hz => hpoly z fun k => (hz k).le.trans (by linarith)
  let L : Compacts (E n) := ⟨tsupport (polydiscCutoff x hr), hasCompactSupport_polydiscCutoff x hr⟩
  have hL : (L:Set (E n)) ⊆ Ω := fun z hz => hpoly z (tsupport_polydiscCutoff_subset x hr hz)
  let χ : 𝓓(Ω,ℂ) := TestFunction.ofSupportedIn hL
    (ContDiffMapSupportedIn.of_support_subset
      (Complex.ofRealCLM.contDiff.comp (contDiff_polydiscCutoff x hr))
      (fun z hz => subset_tsupport _ (by simpa using hz)))
  have hχ : (χ:E n→ℂ) = fun z => (polydiscCutoff x hr z:ℂ) := rfl
  have hj : basisVec j ≠ 0 := by simp [basisVec]
  let H : 𝓓(U,ℂ) →L[ℂ] 𝓓(Ω,ℂ) := cutoffTestCLM χ hj
  let S : ComplexDistribution U := -(T.comp H)
  refine ⟨U,hU,S,(fun k => by simpa using hr),?_,?_⟩
  · ext φ
    change -(-T (H (dbarTestCLM (basisVec j) φ))) = T (TestFunction.monoCLM ℂ φ)
    rw [neg_neg]
    congr 1
    ext y
    rw [cutoffTestCLM_apply, cauchyGreen_derivative_eq]
    by_cases hy : y ∈ U
    · change (polydiscCutoff x hr y:ℂ)*φ y = _
      rw [polydiscCutoff_eq_one x hr (fun k => (hy k).le)]
      simp [inclusion_apply hU]
    · have hf : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (φ.tsupport_subset h))
      simp [hf, inclusion_apply hU]
  · intro i hij hT
    ext φ
    change -(-T (H (dbarTestCLM (basisVec i) φ))) = 0
    rw [neg_neg]
    have hc := cutoff_derivative_comm x hr χ hχ rfl i j hij φ
    have ht := congrArg (fun Q : ComplexDistribution Ω => Q (H φ)) hT
    change -T (dbarTestCLM (basisVec i) (H φ)) = 0 at ht
    rw [← hc]
    exact neg_eq_zero.mp ht

private theorem exists_primitive_aux (k : ℕ) :
    ∀ (Ω : Opens (E n)) (a : Fin n → ComplexDistribution Ω) (x : E n), x ∈ Ω →
      (∀ i j, dbar (basisVec i) (a j) = dbar (basisVec j) (a i)) →
      (∀ i : Fin n, k ≤ i.val → a i = 0) →
      ∃ (U : Opens (E n)) (hU : U ≤ Ω) (f : ComplexDistribution U),
        x ∈ U ∧ ∀ i, dbar (basisVec i) f = restrict (a i) hU := by
  induction k with
  | zero =>
    intro Ω a x hx _ hzero
    refine ⟨Ω,le_rfl,0,hx,fun i => ?_⟩
    rw [dbar_zero, hzero i (Nat.zero_le _)]
    ext φ
    simp [restrict]
  | succ k ih =>
    intro Ω a x hx hclosed hzero
    by_cases hk : k < n
    swap
    · exact ih Ω a x hx hclosed fun i hi => absurd i.isLt (by omega)
    let j : Fin n := ⟨k,hk⟩
    obtain ⟨U,hU,g,hxU,hg,hgzero⟩ := exists_preserving_solution (a j) j x hx
    let b : Fin n → ComplexDistribution U := fun i => restrict (a i) hU - dbar (basisVec i) g
    have hbclosed (i l : Fin n) : dbar (basisVec i) (b l) = dbar (basisVec l) (b i) := by
      simp only [b, dbar_sub, dbar_restrict]
      rw [hclosed i l, dbar_comm (basisVec i) (basisVec l)]
    have hbzero (i : Fin n) (hi : k ≤ i.val) : b i = 0 := by
      rcases hi.eq_or_lt with he | hl
      · have hij : i = j := Fin.ext he.symm
        subst hij
        exact sub_eq_zero.mpr hg.symm
      · have hij : i ≠ j := fun h => by rw [h] at hl; exact lt_irrefl _ hl
        have ht : dbar (basisVec i) (a j) = 0 := by
          rw [hclosed i j, hzero i hl, dbar_zero]
        simp only [b, hzero i hl, hgzero i hij ht]
        ext φ
        simp [restrict]
    obtain ⟨W,hW,f,hxW,hf⟩ := ih U b x hxU hbclosed hbzero
    refine ⟨W,hW.trans hU,f+restrict g hW,hxW,fun i => ?_⟩
    rw [dbar_add, hf i, dbar_restrict]
    simp only [b, restrict_sub, restrict_trans]
    exact sub_add_cancel _ _

/-- Every arbitrary closed distributional (0,1)-form receives a genuine
local primitive. The zero-dimensional coefficient family is empty. -/
theorem exists_local_primitive (a : Fin n → ComplexDistribution Ω)
    (hclosed : ∀ i j, dbar (basisVec i) (a j) = dbar (basisVec j) (a i))
    (x : E n) (hx : x ∈ Ω) :
    ∃ (U : Opens (E n)) (hU : U ≤ Ω) (f : ComplexDistribution U),
      x ∈ U ∧ ∀ i, dbar (basisVec i) f = restrict (a i) hU :=
  exists_primitive_aux n Ω a x hx hclosed fun i hi => absurd i.isLt (by omega)

end SGPT.Foundations.Analysis.Pending.DistributionDolbeaultOne
