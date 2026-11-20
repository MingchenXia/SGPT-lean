import SGPT.Foundations.Analysis.Pending.BoundedHolderMap
import SGPT.Foundations.Analysis.Pending.ContDiffUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

/-!
# The Hölder space `C^{k,r}_b(E, F)`

For `k : ℕ`, an exponent `r : ℝ≥0` and real normed spaces `E`, `F`, the space
`BoundedContDiffHolderMap k r E F` consists of the maps `f : E → F` of class `C^k` whose
derivatives `Dⁱ f` (`i ≤ k`) are bounded and whose `k`-th derivative is `r`-Hölder continuous.
It is normed by

`‖f‖ = ∑_{i < k} ‖Dⁱ f‖_∞ + ‖Dᵏ f‖_{C^{0,r}_b} = ∑_{i ≤ k} ‖Dⁱ f‖_∞ + [Dᵏ f]_r`,

the norm `|f|_{k,r}` of Gilbarg--Trudinger, (4.6) and §6.1, on the whole space `E`.  With
`E = ℝᵐ` it contains every `C^{k,r}` map with compact support, and it is the model space on which
the Hölder spaces of a compact manifold are defined through a partition of unity.

## Main definitions

* `BoundedContDiffHolderMap k r E F`: the space `C^{k,r}_b(E, F)`.
* `BoundedContDiffHolderMap.iteratedFDerivBCF i f`: `Dⁱ f` as a bounded continuous map (`0` for
  `i > k`).
* `BoundedContDiffHolderMap.iteratedFDerivHolder f`: `Dᵏ f` as an element of `C^{0,r}_b`.

## Main results

* `BoundedContDiffHolderMap.instNormedAddCommGroup`, `instNormedSpace`: the norm above.
* `BoundedContDiffHolderMap.instCompleteSpace`: `C^{k,r}_b(E, F)` is a Banach space when `F` is
  complete (uniform limits of `C^k` maps with uniformly convergent derivatives,
  `contDiff_of_tendstoUniformly_iteratedFDeriv`).

## Implementation notes

Scalars are real (the `ℝ`-structure is the one used by the Schauder theory); the algebraic
operations are those of `E → F`, so `⇑(f + g) = ⇑f + ⇑g` holds by `rfl`.

Part of the linear track `L1` of the plan for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal BoundedContinuousFunction

namespace SGPT.Foundations.Analysis.Pending

/-- Bounded continuous maps `E →ᵇ (E [×i]→L[ℝ] F)`, with the metric of the normed group
spelled out: the default instance `ContinuousMultilinearMap.instPseudoMetricSpace` found when
elaborating `E →ᵇ E [×i]→L[ℝ] F` does not unify with the normed-group metric at instance
transparency, which blocks the `NormedSpace` instances of `BoundedContinuousFunction`. -/
local notation "C_b(" E ", " i ", " F ")" =>
  @BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F) _
    SeminormedAddCommGroup.toPseudoMetricSpace

/-- The Hölder space `C^{k,r}_b(E, F)`: maps of class `C^k` with bounded derivatives of order
`≤ k` whose `k`-th derivative is `r`-Hölder continuous. -/
structure BoundedContDiffHolderMap (k : ℕ) (r : ℝ≥0) (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The underlying map. Use the coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ k toFun
  protected bounded' : ∀ i ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i toFun x‖ ≤ C
  protected memHolder' : MemHolder r (iteratedFDeriv ℝ k toFun)

namespace BoundedContDiffHolderMap

variable {k : ℕ} {r : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

instance instFunLike : FunLike (BoundedContDiffHolderMap k r E F) E F where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : BoundedContDiffHolderMap k r E F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : E → F) (h₁ h₂ h₃) :
    ⇑(⟨f, h₁, h₂, h₃⟩ : BoundedContDiffHolderMap k r E F) = f :=
  rfl

theorem contDiff (f : BoundedContDiffHolderMap k r E F) : ContDiff ℝ k f :=
  f.contDiff'

theorem bounded (f : BoundedContDiffHolderMap k r E F) {i : ℕ} (hi : i ≤ k) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
  f.bounded' i hi

theorem memHolder (f : BoundedContDiffHolderMap k r E F) : MemHolder r (iteratedFDeriv ℝ k f) :=
  f.memHolder'

theorem continuous_iteratedFDeriv (f : BoundedContDiffHolderMap k r E F) {i : ℕ} (hi : i ≤ k) :
    Continuous (iteratedFDeriv ℝ i f) :=
  f.contDiff.continuous_iteratedFDeriv (by exact_mod_cast hi)

/-! ### The derivatives as bounded continuous maps -/

/-- The `i`-th derivative of `f` as a bounded continuous map; it is `0` for `i > k`. -/
def iteratedFDerivBCF (i : ℕ) (f : BoundedContDiffHolderMap k r E F) :
    C_b(E, i, F) :=
  if hi : i ≤ k then
    BoundedContinuousFunction.ofNormedAddCommGroup (iteratedFDeriv ℝ i f)
      (f.continuous_iteratedFDeriv hi) (f.bounded hi).choose (f.bounded hi).choose_spec
  else 0

theorem coe_iteratedFDerivBCF (f : BoundedContDiffHolderMap k r E F) {i : ℕ} (hi : i ≤ k) :
    ⇑(f.iteratedFDerivBCF i) = iteratedFDeriv ℝ i f := by
  rw [iteratedFDerivBCF, dif_pos hi, BoundedContinuousFunction.coe_ofNormedAddCommGroup]

theorem iteratedFDerivBCF_of_lt (f : BoundedContDiffHolderMap k r E F) {i : ℕ} (hi : k < i) :
    f.iteratedFDerivBCF i = 0 := by
  rw [iteratedFDerivBCF, dif_neg (not_le.2 hi)]

/-- The `k`-th derivative of `f` as an element of `C^{0,r}_b`. -/
def iteratedFDerivHolder (f : BoundedContDiffHolderMap k r E F) :
    BoundedHolderMap r E (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
  ⟨f.iteratedFDerivBCF k, by
    change MemHolder r ⇑(f.iteratedFDerivBCF k)
    rw [f.coe_iteratedFDerivBCF le_rfl]
    exact f.memHolder⟩

@[simp]
theorem coe_iteratedFDerivHolder (f : BoundedContDiffHolderMap k r E F) :
    ⇑f.iteratedFDerivHolder = iteratedFDeriv ℝ k f :=
  f.coe_iteratedFDerivBCF le_rfl

theorem iteratedFDerivHolder_toBoundedContinuousFunction (f : BoundedContDiffHolderMap k r E F) :
    f.iteratedFDerivHolder.toBoundedContinuousFunction = f.iteratedFDerivBCF k :=
  rfl

/-! ### Algebraic structure -/

instance instZero : Zero (BoundedContDiffHolderMap k r E F) :=
  ⟨⟨fun _ => 0, contDiff_const, fun i _ => ⟨0, fun x => by simp [iteratedFDeriv_fun_zero]⟩, by
    simp only [iteratedFDeriv_fun_zero]; exact memHolder_zero⟩⟩

instance instAdd : Add (BoundedContDiffHolderMap k r E F) :=
  ⟨fun f g => ⟨⇑f + ⇑g, f.contDiff.add g.contDiff, fun i hi => by
    obtain ⟨Cf, hCf⟩ := f.bounded hi
    obtain ⟨Cg, hCg⟩ := g.bounded hi
    refine ⟨Cf + Cg, fun x => ?_⟩
    rw [iteratedFDeriv_add (f.contDiff.of_le (by exact_mod_cast hi))
      (g.contDiff.of_le (by exact_mod_cast hi)), Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x)), by
    rw [iteratedFDeriv_add f.contDiff g.contDiff]
    exact f.memHolder.add g.memHolder⟩⟩

instance instSMul : SMul ℝ (BoundedContDiffHolderMap k r E F) :=
  ⟨fun c f => ⟨c • ⇑f, f.contDiff.const_smul c, fun i hi => by
    obtain ⟨C, hC⟩ := f.bounded hi
    refine ⟨‖c‖ * C, fun x => ?_⟩
    rw [iteratedFDeriv_const_smul_apply (f.contDiff.of_le (by exact_mod_cast hi)).contDiffAt,
      norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c), by
    have : iteratedFDeriv ℝ k (c • ⇑f) = c • iteratedFDeriv ℝ k f := by
      funext x
      exact iteratedFDeriv_const_smul_apply f.contDiff.contDiffAt
    rw [this]
    exact f.memHolder.smul⟩⟩

instance instNeg : Neg (BoundedContDiffHolderMap k r E F) :=
  ⟨fun f => (-1 : ℝ) • f⟩

instance instSub : Sub (BoundedContDiffHolderMap k r E F) :=
  ⟨fun f g => f + -g⟩

instance instSMulNat : SMul ℕ (BoundedContDiffHolderMap k r E F) :=
  ⟨fun n f => (n : ℝ) • f⟩

instance instSMulInt : SMul ℤ (BoundedContDiffHolderMap k r E F) :=
  ⟨fun n f => (n : ℝ) • f⟩

@[simp] theorem coe_zero : ⇑(0 : BoundedContDiffHolderMap k r E F) = 0 := rfl

@[simp] theorem coe_add (f g : BoundedContDiffHolderMap k r E F) : ⇑(f + g) = ⇑f + ⇑g := rfl

@[simp] theorem coe_smul (c : ℝ) (f : BoundedContDiffHolderMap k r E F) : ⇑(c • f) = c • ⇑f :=
  rfl

@[simp] theorem coe_neg (f : BoundedContDiffHolderMap k r E F) : ⇑(-f) = -⇑f := by
  change (-1 : ℝ) • ⇑f = _
  rw [neg_one_smul]

@[simp] theorem coe_sub (f g : BoundedContDiffHolderMap k r E F) : ⇑(f - g) = ⇑f - ⇑g := by
  change ⇑f + ⇑(-g) = _
  rw [coe_neg, sub_eq_add_neg]

theorem coe_nsmul (n : ℕ) (f : BoundedContDiffHolderMap k r E F) : ⇑(n • f) = n • ⇑f := by
  change (n : ℝ) • ⇑f = _
  rw [Nat.cast_smul_eq_nsmul]

theorem coe_zsmul (n : ℤ) (f : BoundedContDiffHolderMap k r E F) : ⇑(n • f) = n • ⇑f := by
  change (n : ℝ) • ⇑f = _
  rw [Int.cast_smul_eq_zsmul]

instance instAddCommGroup : AddCommGroup (BoundedContDiffHolderMap k r E F) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun f n => coe_nsmul n f) (fun f n => coe_zsmul n f)

/-- The coercion to `E → F` as an additive group homomorphism. -/
def coeAddHom : BoundedContDiffHolderMap k r E F →+ (E → F) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℝ (BoundedContDiffHolderMap k r E F) :=
  DFunLike.coe_injective.module ℝ coeAddHom coe_smul

theorem iteratedFDerivBCF_add (i : ℕ) (f g : BoundedContDiffHolderMap k r E F) :
    (f + g).iteratedFDerivBCF i = f.iteratedFDerivBCF i + g.iteratedFDerivBCF i := by
  by_cases hi : i ≤ k
  · ext1 x
    rw [BoundedContinuousFunction.add_apply, coe_iteratedFDerivBCF _ hi,
      coe_iteratedFDerivBCF _ hi, coe_iteratedFDerivBCF _ hi, coe_add,
      iteratedFDeriv_add_apply (f.contDiff.of_le (by exact_mod_cast hi)).contDiffAt
        (g.contDiff.of_le (by exact_mod_cast hi)).contDiffAt]
  · simp only [iteratedFDerivBCF_of_lt _ (not_le.1 hi)]
    exact (add_zero _).symm

theorem iteratedFDerivBCF_smul (i : ℕ) (c : ℝ) (f : BoundedContDiffHolderMap k r E F) :
    (c • f).iteratedFDerivBCF i = c • f.iteratedFDerivBCF i := by
  by_cases hi : i ≤ k
  · ext1 x
    rw [BoundedContinuousFunction.smul_apply, coe_iteratedFDerivBCF _ hi,
      coe_iteratedFDerivBCF _ hi, coe_smul,
      iteratedFDeriv_const_smul_apply (f.contDiff.of_le (by exact_mod_cast hi)).contDiffAt]
  · simp only [iteratedFDerivBCF_of_lt _ (not_le.1 hi)]
    exact (smul_zero c).symm

/-- `f ↦ Dⁱ f` as a linear map to the bounded continuous maps. -/
def iteratedFDerivBCFLM (i : ℕ) :
    BoundedContDiffHolderMap k r E F →ₗ[ℝ] C_b(E, i, F)
    where
  toFun := iteratedFDerivBCF i
  map_add' := iteratedFDerivBCF_add i
  map_smul' := iteratedFDerivBCF_smul i

/-- `f ↦ Dᵏ f` as a linear map to `C^{0,r}_b`. -/
def iteratedFDerivHolderLM :
    BoundedContDiffHolderMap k r E F →ₗ[ℝ]
      BoundedHolderMap r E (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) where
  toFun := iteratedFDerivHolder
  map_add' f g := BoundedHolderMap.toBoundedContinuousFunction_injective
    (iteratedFDerivBCF_add k f g)
  map_smul' c f := BoundedHolderMap.toBoundedContinuousFunction_injective
    (iteratedFDerivBCF_smul k c f)

/-! ### The norm -/

/-- The norm `∑_{i < k} ‖Dⁱ f‖_∞ + ‖Dᵏ f‖_{C^{0,r}_b}` of `C^{k,r}_b(E, F)`. -/
instance instNorm : Norm (BoundedContDiffHolderMap k r E F) :=
  ⟨fun f => ∑ i ∈ Finset.range k, ‖f.iteratedFDerivBCF i‖ + ‖f.iteratedFDerivHolder‖⟩

theorem norm_def (f : BoundedContDiffHolderMap k r E F) :
    ‖f‖ = ∑ i ∈ Finset.range k, ‖f.iteratedFDerivBCF i‖ + ‖f.iteratedFDerivHolder‖ :=
  rfl

theorem norm_iteratedFDerivHolder_le (f : BoundedContDiffHolderMap k r E F) :
    ‖f.iteratedFDerivHolder‖ ≤ ‖f‖ :=
  le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => norm_nonneg (f.iteratedFDerivBCF i))

/-- `‖Dⁱ f‖_∞ ≤ ‖f‖` for every `i`. -/
theorem norm_iteratedFDerivBCF_le (f : BoundedContDiffHolderMap k r E F) (i : ℕ) :
    ‖f.iteratedFDerivBCF i‖ ≤ ‖f‖ := by
  rcases lt_trichotomy i k with hik | rfl | hik
  · exact (Finset.single_le_sum (f := fun j => ‖f.iteratedFDerivBCF j‖)
      (fun j _ => norm_nonneg (f.iteratedFDerivBCF j)) (Finset.mem_range.2 hik)).trans
      (le_add_of_nonneg_right (norm_nonneg f.iteratedFDerivHolder))
  · exact f.iteratedFDerivHolder.norm_toBoundedContinuousFunction_le.trans
      f.norm_iteratedFDerivHolder_le
  · rw [iteratedFDerivBCF_of_lt _ hik, norm_zero]
    exact add_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg (f.iteratedFDerivBCF j))
      (norm_nonneg f.iteratedFDerivHolder)

theorem norm_iteratedFDeriv_apply_le (f : BoundedContDiffHolderMap k r E F) {i : ℕ}
    (hi : i ≤ k) (x : E) : ‖iteratedFDeriv ℝ i f x‖ ≤ ‖f‖ := by
  rw [← f.coe_iteratedFDerivBCF hi]
  exact ((f.iteratedFDerivBCF i).norm_coe_le_norm x).trans (f.norm_iteratedFDerivBCF_le i)

theorem norm_apply_le (f : BoundedContDiffHolderMap k r E F) (x : E) : ‖f x‖ ≤ ‖f‖ := by
  simpa only [norm_iteratedFDeriv_zero] using f.norm_iteratedFDeriv_apply_le (Nat.zero_le k) x

private theorem normedSpaceCore : NormedSpace.Core ℝ (BoundedContDiffHolderMap k r E F) where
  norm_nonneg f := add_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg (f.iteratedFDerivBCF i))
    (norm_nonneg f.iteratedFDerivHolder)
  norm_smul c f := by
    rw [norm_def, norm_def, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        rw [iteratedFDerivBCF_smul, norm_smul]
    · exact (congrArg norm (iteratedFDerivHolderLM.map_smul c f)).trans (norm_smul _ _)
  norm_triangle f g := by
    rw [norm_def, norm_def, norm_def]
    have h1 : ∑ i ∈ Finset.range k, ‖(f + g).iteratedFDerivBCF i‖ ≤
        ∑ i ∈ Finset.range k, ‖f.iteratedFDerivBCF i‖ +
          ∑ i ∈ Finset.range k, ‖g.iteratedFDerivBCF i‖ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => by
        rw [iteratedFDerivBCF_add]
        exact norm_add_le (f.iteratedFDerivBCF i) (g.iteratedFDerivBCF i)
    have h2 : ‖(f + g).iteratedFDerivHolder‖ ≤ ‖f.iteratedFDerivHolder‖ +
        ‖g.iteratedFDerivHolder‖ := by
      rw [show (f + g).iteratedFDerivHolder = f.iteratedFDerivHolder + g.iteratedFDerivHolder
        from iteratedFDerivHolderLM.map_add f g]
      exact norm_add_le _ _
    linarith
  norm_eq_zero_iff f := by
    refine ⟨fun h => ext fun x => ?_, fun h => ?_⟩
    · have := f.norm_apply_le x
      rw [h] at this
      simpa using norm_le_zero_iff.1 this
    · subst h
      rw [norm_def]
      have h0 : ∀ i, (0 : BoundedContDiffHolderMap k r E F).iteratedFDerivBCF i = 0 := fun i =>
        by simpa using iteratedFDerivBCF_smul i 0 (0 : BoundedContDiffHolderMap k r E F)
      have hH : (0 : BoundedContDiffHolderMap k r E F).iteratedFDerivHolder = 0 :=
        iteratedFDerivHolderLM.map_zero
      simp [h0, hH]

instance instNormedAddCommGroup : NormedAddCommGroup (BoundedContDiffHolderMap k r E F) :=
  NormedAddCommGroup.ofCore normedSpaceCore

instance instNormedSpace : NormedSpace ℝ (BoundedContDiffHolderMap k r E F) :=
  NormedSpace.ofCore normedSpaceCore

/-- `f ↦ Dⁱ f` as a continuous linear map `C^{k,r}_b → C_b` (norm `≤ 1`). -/
def iteratedFDerivBCFCLM (i : ℕ) :
    BoundedContDiffHolderMap k r E F →L[ℝ] C_b(E, i, F) :=
  (iteratedFDerivBCFLM i).mkContinuous 1 fun f => by
    rw [one_mul]; exact f.norm_iteratedFDerivBCF_le i

/-- `f ↦ Dᵏ f` as a continuous linear map `C^{k,r}_b → C^{0,r}_b` (norm `≤ 1`). -/
def iteratedFDerivHolderCLM :
    BoundedContDiffHolderMap k r E F →L[ℝ]
      BoundedHolderMap r E (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
  iteratedFDerivHolderLM.mkContinuous 1 fun f => by
    rw [one_mul]; exact f.norm_iteratedFDerivHolder_le

/-! ### Completeness -/

/-- `C^{k,r}_b(E, F)` is a Banach space: the derivatives of a Cauchy sequence converge uniformly,
so the limit is `C^k` with the limits as derivatives
(`contDiff_of_tendstoUniformly_iteratedFDeriv`),
and the top derivatives converge in `C^{0,r}_b`. -/
instance instCompleteSpace [CompleteSpace F] :
    CompleteSpace (BoundedContDiffHolderMap k r E F) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- limits of the derivatives
  have hcau : ∀ i, CauchySeq fun n => (u n).iteratedFDerivBCF i := fun i =>
    (iteratedFDerivBCFCLM (k := k) (r := r) (E := E) (F := F) i).uniformContinuous.comp_cauchySeq hu
  set G : ∀ i : ℕ, C_b(E, i, F) := fun i =>
    limUnder atTop fun n => (u n).iteratedFDerivBCF i with hGdef
  have hG : ∀ i, Tendsto (fun n => (u n).iteratedFDerivBCF i) atTop (𝓝 (G i)) := fun i =>
    (hcau i).tendsto_limUnder
  have hcauH : CauchySeq fun n => (u n).iteratedFDerivHolder :=
    iteratedFDerivHolderCLM.uniformContinuous.comp_cauchySeq hu
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hcauH
  have hHG : H.toBoundedContinuousFunction = G k :=
    tendsto_nhds_unique
      (BoundedHolderMap.continuous_toBoundedContinuousFunction.tendsto H |>.comp hH)
      (hG k)
  -- the limit map
  set f₀ : E → F := fun x => continuousMultilinearCurryFin0 ℝ E F (G 0 x) with hf₀
  have hunif : ∀ i ≤ k, TendstoUniformly (fun n => iteratedFDeriv ℝ i (u n)) (⇑(G i)) atTop :=
    fun i hi => by
      have := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 (hG i)
      simpa only [coe_iteratedFDerivBCF _ hi] using this
  have hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f₀ x)) := fun x => by
    have h0 := (hunif 0 (Nat.zero_le k)).tendsto_at x
    have h1 := ((continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto _).comp h0
    simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp, hf₀] using h1
  have hcd := contDiff_of_tendstoUniformly_iteratedFDeriv (fun n => (u n).contDiff) hlim hunif
  have heq := iteratedFDeriv_eq_of_tendstoUniformly (fun n => (u n).contDiff) hlim hunif
  have hHol : MemHolder r (iteratedFDeriv ℝ k f₀) := by
    rw [heq k le_rfl, ← hHG]
    exact H.memHolder
  let F₀ : BoundedContDiffHolderMap k r E F :=
    ⟨f₀, hcd, fun i hi => ⟨‖G i‖, fun x => by rw [heq i hi]; exact (G i).norm_coe_le_norm x⟩,
      hHol⟩
  have hF₀ : ∀ i ≤ k, F₀.iteratedFDerivBCF i = G i := fun i hi => by
    ext1 x
    rw [coe_iteratedFDerivBCF _ hi]
    exact congrFun (heq i hi) x
  have hF₀H : F₀.iteratedFDerivHolder = H :=
    BoundedHolderMap.toBoundedContinuousFunction_injective ((hF₀ k le_rfl).trans hHG.symm)
  refine ⟨F₀, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun n => ∑ i ∈ Finset.range k,
      ‖(u n).iteratedFDerivBCF i - F₀.iteratedFDerivBCF i‖ +
        ‖(u n).iteratedFDerivHolder - F₀.iteratedFDerivHolder‖) atTop (𝓝 0) := by
    rw [← add_zero (0 : ℝ)]
    refine Tendsto.add ?_ ?_
    · rw [← Finset.sum_const_zero (s := Finset.range k)]
      refine tendsto_finsetSum _ fun i hi => ?_
      rw [hF₀ i (Finset.mem_range.1 hi).le]
      exact (tendsto_iff_norm_sub_tendsto_zero.1 (hG i))
    · rw [hF₀H]
      exact tendsto_iff_norm_sub_tendsto_zero.1 hH
  refine hsum.congr fun n => ?_
  rw [norm_def]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [show (u n - F₀).iteratedFDerivBCF i = (u n).iteratedFDerivBCF i - F₀.iteratedFDerivBCF i
        from (iteratedFDerivBCFLM i).map_sub _ _]
  · rw [show (u n - F₀).iteratedFDerivHolder = (u n).iteratedFDerivHolder - F₀.iteratedFDerivHolder
      from iteratedFDerivHolderLM.map_sub _ _]

end BoundedContDiffHolderMap

end SGPT.Foundations.Analysis.Pending
