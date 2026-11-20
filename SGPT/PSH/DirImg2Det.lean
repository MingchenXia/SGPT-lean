import SGPT.Foundations.Analysis.Plurisubharmonic
import SGPT.Foundations.Analysis.LogPole
import SGPT.Foundations.Analysis.FirstPass.PluripolarSets
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Singular norm families in a holomorphic frame and the determinant of the dual metric

Blueprint `claude-dirimg2.tex`, nodes `claude-dirimg2:norm-family`, `claude-dirimg2:det-dual`.
Source: Step 1.3--1.4 of the proof of `thm:Bert` (`chapter_trace.tex` 828--935) and
`rmk:generalABT`: the Hodge metric `h_𝓗` on the direct image `𝓕`, a vector bundle over a
parameter space off a proper analytic subset, is a *singular* Hermitian metric — its fibre
norm `h_𝓗(α, α) = ∫_{X_t} |α|² e^{-φ} ∈ [0, ∞]` is infinite exactly on the sections that are not
fibrewise `L²` — and the book concludes from the positivity of `det h_𝓗` that the set of
parameters where some fibre element is not `L²` is pluripolar.

In a local holomorphic frame of `𝓕` over an open set `U` of the parameter space `E`, the metric
is a family `q t : ℂʳ → [0, ∞]` of squared norms. This file introduces the determinant of the
dual metric in an elementary, frame-wise form which avoids any determinant of an infinite
matrix:

`detDual q t = sup_C |det C|² / ∏ⱼ q t (C j)`,

the supremum over frames `C = (C 0, …, C (r-1))` of `ℂʳ` (normalized to unit columns). For a
positive definite Hermitian form this is `det h⁻¹` (Hadamard), i.e. the determinant of the dual
metric `h*`; in general:

* `detRatio_le_detDual`: every frame is a competitor (columns can be rescaled);
* `detDual_eq_zero_of_exists_eq_top`: if some vector has infinite norm, `detDual q t = 0`;
* `detDual_ne_top`: `detDual q t < ∞` (positivity and lower semicontinuity);
* `upperSemicontinuousOn_detDual`: `t ↦ detDual q t` is upper semicontinuous (joint lower
  semicontinuity of the norms and compactness of the unit frames).

The hypotheses (`IsSingularNormFamily`) are those satisfied by fibrewise `L²` norms: homogeneity,
the quasi-triangle inequality (so that the finite-norm vectors form a subspace), positivity and
joint lower semicontinuity (Fatou). No Hermitian structure is needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric
open scoped Topology ENNReal

namespace SGPT.PSH.DirImg2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}

/-! ### Frames and determinants -/

/-- The determinant of the frame `C` of `ℂʳ` (the matrix with columns `C j`). -/
def colDet (C : Fin r → Fin r → ℂ) : ℂ := Matrix.det (Matrix.of fun i j => C j i)

/-- Rescaling the columns multiplies the determinant by the product of the factors. -/
theorem colDet_smul (c : Fin r → ℂ) (C : Fin r → Fin r → ℂ) :
    colDet (fun j => c j • C j) = (∏ j, c j) * colDet C := by
  unfold colDet
  rw [← Matrix.det_mul_row]
  rfl

/-- A frame with a zero column has determinant zero. -/
theorem colDet_eq_zero_of_eq_zero {C : Fin r → Fin r → ℂ} {j : Fin r} (h : C j = 0) :
    colDet C = 0 :=
  Matrix.det_eq_zero_of_column_eq_zero j fun i => by simp [h]

/-- A frame with nonzero determinant spans `ℂʳ`. -/
theorem exists_eq_sum_of_colDet_ne_zero {C : Fin r → Fin r → ℂ} (h : colDet C ≠ 0)
    (v : Fin r → ℂ) : ∃ b : Fin r → ℂ, v = ∑ j, b j • C j := by
  set M : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j => C j i
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr h
  refine ⟨M⁻¹.mulVec v, ?_⟩
  have hv : M.mulVec (M⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  conv_lhs => rw [← hv]
  funext i
  simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- `|det C| ≤ r!` for a frame with columns of norm at most `1`. -/
theorem norm_colDet_le {C : Fin r → Fin r → ℂ} (hC : ∀ j, ‖C j‖ ≤ 1) :
    ‖colDet C‖ ≤ (r.factorial : ℝ) := by
  have hentry : ∀ i j, ‖C j i‖ ≤ 1 := fun i j => (norm_le_pi_norm (C j) i).trans (hC j)
  unfold colDet
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
          ∏ i, (Matrix.of fun i j => C j i) (σ i) i‖
        ≤ ∑ σ : Equiv.Perm (Fin r), ‖Equiv.Perm.sign σ •
          ∏ i, (Matrix.of fun i j => C j i) (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), (1 : ℝ) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hp : ‖∏ i, (Matrix.of fun i j => C j i) (σ i) i‖ ≤ 1 := by
          rw [norm_prod]
          exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
            simpa using hentry (σ i) i
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h, norm_prod] using hp
    _ = (r.factorial : ℝ) := by simp [Fintype.card_perm]

/-- The unit frames: every column has norm `1` (a compact set). -/
def unitFrames (r : ℕ) : Set (Fin r → Fin r → ℂ) := Set.pi univ fun _ => sphere 0 1

theorem isCompact_unitFrames (r : ℕ) : IsCompact (unitFrames r) :=
  isCompact_univ_pi fun _ => isCompact_sphere 0 1

/-! ### The determinant of the dual metric -/

/-- `|det C|² / ∏ⱼ q (C j)`. -/
def detRatio (q : (Fin r → ℂ) → ℝ≥0∞) (C : Fin r → Fin r → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖colDet C‖ ^ 2) / ∏ j, q (C j)

/-- **The determinant of the dual metric** of a singular norm `q` in the standard frame:
`sup` over unit frames `C` of `|det C|² / ∏ⱼ q (C j)`. -/
def detDual (q : (Fin r → ℂ) → ℝ≥0∞) : ℝ≥0∞ := ⨆ C ∈ unitFrames r, detRatio q C

/-- A family `q t` of squared norms on `ℂʳ` (a singular metric in a holomorphic frame over `U`):
homogeneous, quasi-triangle inequality, positive on `U`, jointly lower semicontinuous at the
points of `U × ℂʳ`. Fibrewise `L²` norms `∫_{X_t} |∑ vⱼ sⱼ|² e^{-φ}` have these properties. -/
structure IsSingularNormFamily (q : E → (Fin r → ℂ) → ℝ≥0∞) (U : Set E) : Prop where
  smul : ∀ t (a : ℂ) v, q t (a • v) = ENNReal.ofReal (‖a‖ ^ 2) * q t v
  add_le : ∀ t v w, q t (v + w) ≤ 2 * q t v + 2 * q t w
  pos : ∀ t ∈ U, ∀ v, v ≠ 0 → q t v ≠ 0
  lsc : ∀ t ∈ U, ∀ v, LowerSemicontinuousAt (fun p : E × (Fin r → ℂ) => q p.1 p.2) (t, v)

variable {q : E → (Fin r → ℂ) → ℝ≥0∞} {U : Set E}

namespace IsSingularNormFamily

theorem zero (hq : IsSingularNormFamily q U) (t : E) : q t 0 = 0 := by
  simpa using hq.smul t 0 0

/-- Finite combinations of finite-norm vectors have finite norm. -/
theorem sum_ne_top (hq : IsSingularNormFamily q U) (t : E) {ι : Type*} (s : Finset ι)
    (w : ι → Fin r → ℂ) (hw : ∀ i ∈ s, q t (w i) ≠ ⊤) : q t (∑ i ∈ s, w i) ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hq.zero t]
  | insert i s his ih =>
    rw [Finset.sum_insert his]
    refine ne_top_of_le_ne_top ?_ (hq.add_le t _ _)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (hw i (Finset.mem_insert_self i s)), ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ih fun j hj => hw j (Finset.mem_insert_of_mem hj))⟩

/-- Rescaling the columns of a frame by nonzero factors does not change `detRatio`. -/
theorem detRatio_smul (hq : IsSingularNormFamily q U) (t : E) {c : Fin r → ℂ}
    (hc : ∀ j, c j ≠ 0) (C : Fin r → Fin r → ℂ) :
    detRatio (q t) (fun j => c j • C j) = detRatio (q t) C := by
  unfold detRatio
  rw [colDet_smul]
  simp_rw [hq.smul]
  rw [Finset.prod_mul_distrib, norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity),
    norm_prod, ← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
  refine ENNReal.mul_div_mul_left _ _ ?_ (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact pow_pos (norm_pos_iff.mpr (hc j)) 2

/-- **Every frame is a competitor:** `detRatio (q t) C ≤ detDual (q t)` for all frames `C`. -/
theorem detRatio_le_detDual (hq : IsSingularNormFamily q U) (t : E) (C : Fin r → Fin r → ℂ) :
    detRatio (q t) C ≤ detDual (q t) := by
  by_cases h0 : ∃ j, C j = 0
  · obtain ⟨j, hj⟩ := h0
    simp [detRatio, colDet_eq_zero_of_eq_zero hj]
  · push Not at h0
    set c : Fin r → ℂ := fun j => ((‖C j‖ : ℝ) : ℂ)⁻¹
    have hc : ∀ j, c j ≠ 0 := fun j => inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr (h0 j))
    rw [← hq.detRatio_smul t hc C]
    refine le_iSup₂_of_le (f := fun C _ => detRatio (q t) C) (fun j => c j • C j) ?_ le_rfl
    intro j _
    simp only [mem_sphere_iff_norm, sub_zero, c, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 j))

/-- **Infinite norms kill the dual determinant:** if some vector has infinite norm at `t ∈ U`,
then `detDual (q t) = 0`. -/
theorem detDual_eq_zero_of_exists_eq_top (hq : IsSingularNormFamily q U) {t : E} (ht : t ∈ U)
    (hv : ∃ v, q t v = ⊤) : detDual (q t) = 0 := by
  obtain ⟨v, hv⟩ := hv
  refine le_antisymm (iSup₂_le fun C hC => ?_) bot_le
  by_cases hdet : colDet C = 0
  · simp [detRatio, hdet]
  · obtain ⟨b, rfl⟩ := exists_eq_sum_of_colDet_ne_zero hdet v
    have hj : ∃ j, q t (C j) = ⊤ := by
      by_contra! hfin
      refine hq.sum_ne_top t Finset.univ _ (fun j _ => ?_) hv
      rw [hq.smul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin j)
    obtain ⟨j, hj⟩ := hj
    have hne : ∀ i, q t (C i) ≠ 0 := fun i => hq.pos t ht _ fun h0 => by
      have := hC i (mem_univ i)
      rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at this
      exact zero_ne_one this
    have hprod : ∏ i, q t (C i) = ⊤ := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), hj]
      exact ENNReal.top_mul (Finset.prod_ne_zero_iff.mpr fun i _ => hne i)
    simp [detRatio, hprod]

end IsSingularNormFamily

/-! ### Semicontinuity of products in `ℝ≥0∞` -/

section Semicontinuity

variable {α : Type*} [TopologicalSpace α]

/-- The product of two lower semicontinuous `ℝ≥0∞`-valued functions is lower semicontinuous. -/
theorem lowerSemicontinuousAt_mul {f g : α → ℝ≥0∞} {x : α} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x) : LowerSemicontinuousAt (fun y => f y * g y) x := by
  intro y hy
  have hf0 : f x ≠ 0 := by rintro h; simp [h] at hy
  have hg0 : g x ≠ 0 := by rintro h; simp [h] at hy
  have ht : Tendsto (fun z : ℝ≥0∞ × ℝ≥0∞ => z.1 * z.2) (𝓝[<] (f x) ×ˢ 𝓝[<] (g x))
      (𝓝 (f x * g x)) := by
    refine (ENNReal.tendsto_mul (Or.inl hf0) (Or.inl hg0)).mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have : (𝓝[<] (f x)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr hf0⟩
  have : (𝓝[<] (g x)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr hg0⟩
  obtain ⟨⟨a, b⟩, hab, ha, hb⟩ := ((ht.eventually (lt_mem_nhds hy)).and
    (prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin)).exists
  filter_upwards [hf a ha, hg b hb] with z hza hzb
  exact hab.trans_le (mul_le_mul' hza.le hzb.le)

/-- Finite products of lower semicontinuous `ℝ≥0∞`-valued functions are lower semicontinuous. -/
theorem lowerSemicontinuousAt_prod {ι : Type*} (s : Finset ι) {f : ι → α → ℝ≥0∞} {x : α}
    (hf : ∀ i ∈ s, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun y => ∏ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerSemicontinuousAt_const
  | insert i s his ih =>
    simp_rw [Finset.prod_insert his]
    exact lowerSemicontinuousAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The product of two upper semicontinuous `ℝ≥0∞`-valued functions which are finite at `x` is
upper semicontinuous at `x`. -/
theorem upperSemicontinuousAt_mul {f g : α → ℝ≥0∞} {x : α} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x) (hf' : f x ≠ ⊤) (hg' : g x ≠ ⊤) :
    UpperSemicontinuousAt (fun y => f y * g y) x := by
  intro y hy
  have ht : Tendsto (fun z : ℝ≥0∞ × ℝ≥0∞ => z.1 * z.2) (𝓝[>] (f x) ×ˢ 𝓝[>] (g x))
      (𝓝 (f x * g x)) := by
    refine (ENNReal.tendsto_mul (Or.inr hg') (Or.inr hf')).mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have : (𝓝[>] (f x)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, lt_top_iff_ne_top.mpr hf'⟩
  have : (𝓝[>] (g x)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, lt_top_iff_ne_top.mpr hg'⟩
  obtain ⟨⟨a, b⟩, hab, ha, hb⟩ := ((ht.eventually (gt_mem_nhds hy)).and
    (prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin)).exists
  filter_upwards [hf a ha, hg b hb] with z hza hzb
  exact (mul_le_mul' hza.le hzb.le).trans_lt hab

end Semicontinuity

theorem continuous_colDet : Continuous (colDet : (Fin r → Fin r → ℂ) → ℂ) :=
  Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply i).comp (continuous_apply j))

namespace IsSingularNormFamily

/-- **Finiteness:** `detDual (q t) < ∞` at every `t ∈ U` (`q t` is bounded below on the unit
sphere by a positive constant, and `|det C| ≤ r!` for unit frames). -/
theorem detDual_ne_top (hq : IsSingularNormFamily q U) {t : E} (ht : t ∈ U) :
    detDual (q t) ≠ ⊤ := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ≥0∞, m ≠ 0 ∧ ∀ v ∈ sphere (0 : Fin r → ℂ) 1, m ≤ q t v := by
    rcases (sphere (0 : Fin r → ℂ) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_ne_zero, by simp [he]⟩
    · have hlsc : LowerSemicontinuousOn (q t) (sphere 0 1) := fun v _ =>
        ((hq.lsc t ht v).comp (by fun_prop : ContinuousAt (fun w : Fin r → ℂ => (t, w)) v)
          ).lowerSemicontinuousWithinAt _
      obtain ⟨v₀, hv₀, hmin⟩ := hlsc.exists_isMinOn hne (isCompact_sphere 0 1)
      refine ⟨q t v₀, hq.pos t ht v₀ fun h => ?_, fun v hv => hmin hv⟩
      simp [h] at hv₀
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal ((r.factorial : ℝ) ^ 2) / m ^ r)
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top (pow_ne_zero _ hm0)) (iSup₂_le fun C hC => ?_)
  have hC1 : ∀ j, ‖C j‖ = 1 := fun j => by simpa using hC j (mem_univ j)
  unfold detRatio
  refine ENNReal.div_le_div (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
    (norm_colDet_le fun j => (hC1 j).le) 2)) ?_
  simpa using Finset.pow_card_le_prod Finset.univ (fun j => q t (C j)) m fun j _ =>
    hm (C j) (by simpa using hC1 j)

/-- Joint upper semicontinuity of `(t, C) ↦ |det C|² / ∏ⱼ q t (C j)` at unit frames. -/
theorem upperSemicontinuousAt_detRatio (hq : IsSingularNormFamily q U) {t₀ : E} (ht₀ : t₀ ∈ U)
    {C : Fin r → Fin r → ℂ} (hC : C ∈ unitFrames r) :
    UpperSemicontinuousAt (fun z : E × (Fin r → Fin r → ℂ) => detRatio (q z.1) z.2) (t₀, C) := by
  have hP : LowerSemicontinuousAt (fun z : E × (Fin r → Fin r → ℂ) => ∏ j, q z.1 (z.2 j))
      (t₀, C) :=
    lowerSemicontinuousAt_prod Finset.univ fun j _ =>
      (hq.lsc t₀ ht₀ (C j)).comp (g := fun z : E × (Fin r → Fin r → ℂ) => (z.1, z.2 j))
        (by fun_prop : ContinuousAt (fun z : E × (Fin r → Fin r → ℂ) => (z.1, z.2 j)) (t₀, C))
  have hPinv : UpperSemicontinuousAt
      (fun z : E × (Fin r → Fin r → ℂ) => (∏ j, q z.1 (z.2 j))⁻¹) (t₀, C) :=
    ContinuousAt.comp_lowerSemicontinuousAt_antitone (g := fun a : ℝ≥0∞ => a⁻¹)
      (continuous_inv : Continuous fun a : ℝ≥0∞ => a⁻¹).continuousAt hP
      fun a b h => ENNReal.inv_le_inv.mpr h
  have hdet : UpperSemicontinuousAt
      (fun z : E × (Fin r → Fin r → ℂ) => ENNReal.ofReal (‖colDet z.2‖ ^ 2)) (t₀, C) :=
    (ENNReal.continuous_ofReal.comp ((continuous_colDet.comp continuous_snd).norm.pow 2)
      ).continuousAt.upperSemicontinuousAt
  have hne : ∀ j, q t₀ (C j) ≠ 0 := fun j => hq.pos t₀ ht₀ _ fun h0 => by
    have := hC j (mem_univ j)
    rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at this
    exact zero_ne_one this
  have h := upperSemicontinuousAt_mul hdet hPinv ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => hne j))
  simpa only [detRatio, div_eq_mul_inv] using h

/-- **Upper semicontinuity of the dual determinant** on the open set `U` (supremum over the
compact set of unit frames of a jointly upper semicontinuous function). -/
theorem upperSemicontinuousOn_detDual (hq : IsSingularNormFamily q U) :
    UpperSemicontinuousOn (fun t => detDual (q t)) U := by
  intro t₀ ht₀
  refine UpperSemicontinuousAt.upperSemicontinuousWithinAt _ ?_
  intro y hy
  obtain ⟨y', hy₀, hy'⟩ := exists_between hy
  have hev : ∀ C ∈ unitFrames r,
      ∀ᶠ z : E × (Fin r → Fin r → ℂ) in 𝓝 (t₀, C), detRatio (q z.1) z.2 < y' := fun C hC =>
    hq.upperSemicontinuousAt_detRatio ht₀ hC y'
      ((le_iSup₂ (f := fun C _ => detRatio (q t₀) C) C hC).trans_lt hy₀)
  filter_upwards [(isCompact_unitFrames r).eventually_forall_of_forall_eventually
    (P := fun t C => detRatio (q t) C < y') hev] with t ht
  exact (iSup₂_le fun C hC => (ht C hC).le).trans_lt hy'

end IsSingularNormFamily

/-- `log det h*`: the logarithm of the dual determinant, the candidate plurisubharmonic weight. -/
def logDetDual (q : E → (Fin r → ℂ) → ℝ≥0∞) (t : E) : EReal := ENNReal.log (detDual (q t))

namespace IsSingularNormFamily

theorem upperSemicontinuousOn_logDetDual (hq : IsSingularNormFamily q U) :
    UpperSemicontinuousOn (logDetDual q) U :=
  ENNReal.continuous_log.comp_upperSemicontinuousOn hq.upperSemicontinuousOn_detDual
    ENNReal.log_monotone

theorem logDetDual_ne_top (hq : IsSingularNormFamily q U) {t : E} (ht : t ∈ U) :
    logDetDual q t ≠ ⊤ := by
  simpa [logDetDual] using hq.detDual_ne_top ht

theorem logDetDual_eq_bot_of_exists_eq_top (hq : IsSingularNormFamily q U) {t : E} (ht : t ∈ U)
    (hv : ∃ v, q t v = ⊤) : logDetDual q t = ⊥ := by
  simp [logDetDual, hq.detDual_eq_zero_of_exists_eq_top ht hv]

end IsSingularNormFamily

end SGPT.PSH.DirImg2
