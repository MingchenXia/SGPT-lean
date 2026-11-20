import SGPT.Trace.TwistedL2Statement
import SGPT.Trace.TwistedL2FriedrichsCore

/-!
# Friedrichs' lemma for first order systems (`FriedrichsStatement`)

Blueprint `claude-twisted-l2.tex`, node `claude-twisted-l2:friedrichs` (sub-lemmas in
`claude-twisted-l2-a.tex`, lane TL2-A).  We prove `FriedrichsStatement n N N'`: on an open
`D ⊆ ℂⁿ`, for a first order system `P = ∑_j (A_j ∂_j + A'_j ∂_{j̄}) + B` with coefficients smooth
on `D`, a compactly supported `w ∈ L²` with `P w = f ∈ L²` weakly on `D` is the `L²` limit of the
test functions `w_k = ρ_k ⋆ w` with `P w_k → f` in `L²(D)` (Hörmander, *An introduction to complex
analysis in several variables*, Lemma 4.1.3).

Proof.  Cut the coefficients off to globally smooth, compactly supported `At, At', Bt` equal to the
original ones near `K₂ = cthickening (δ/2) K ⊆ D`.  The weak equation tested against
`y ↦ ρ_k(z - y) e_{i'}` identifies the mollification `ρ_k ⋆ f` (with `f` replaced by `1_K f`,
legitimate because `f = 0` a.e. on `D \ K`) with the transposed mollification
`transposeMoll` (the local identity `hT` in the proof). The difference `P̃(ρ_k ⋆ w) - transposeMoll`
splits (`firstOrderApply_sub_transposeMoll`) into scalar Friedrichs commutators `dComm`,
`dbarComm` (for `a ∂_j`, `a ∂_{j̄}`, each a combination of two real-direction commutators
`friedrichsComm`) and zeroth order commutators `zeroComm`, which tend to `0` in `L²` by the
scalar Friedrichs lemma `tendsto_eLpNorm_friedrichsComm`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Function Filter Metric MeasureTheory ContinuousLinearMap Complex
open scoped ContDiff Convolution Topology ENNReal Pointwise ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.Hormander.Density SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Trace.TwistedL2.Friedrichs

namespace FriedrichsProof

variable {n : ℕ}

/-! ### Wirtinger commutators -/

/-- The Friedrichs commutator of `a ∂_e` (Wirtinger derivative `∂/∂w` along `e`). -/
def dComm (ρ : ContDiffBump (0 : ComplexModel n)) (a : ComplexModel n → ℂ) (e : ComplexModel n)
    (u : ComplexModel n → ℂ) (z : ComplexModel n) : ℂ :=
  a z * dDir e (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z +
    ∫ y, u y * dDir e (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y

/-- The Friedrichs commutator of `a ∂_{ē}` (Wirtinger derivative `∂/∂w̄` along `e`). -/
def dbarComm (ρ : ContDiffBump (0 : ComplexModel n)) (a : ComplexModel n → ℂ)
    (e : ComplexModel n) (u : ComplexModel n → ℂ) (z : ComplexModel n) : ℂ :=
  a z * dbarDir e (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z +
    ∫ y, u y * dbarDir e (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y

section Wirtinger

variable (ρ : ContDiffBump (0 : ComplexModel n)) {a : ComplexModel n → ℂ} (e : ComplexModel n)
  {u : ComplexModel n → ℂ}

theorem integrable_mul_dDir_mul_normed_sub (ha : ContDiff ℝ 1 a) (hu : LocallyIntegrable u)
    (z : ComplexModel n) :
    Integrable fun y ↦ u y * dDir e (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y := by
  have h1 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z e
  have h2 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z (I • e)
  refine ((h1.const_mul (1 / 2 : ℂ)).add (h2.const_mul (-I / 2))).congr
    (Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.add_apply, dDir]
  ring

theorem integrable_mul_dbarDir_mul_normed_sub (ha : ContDiff ℝ 1 a) (hu : LocallyIntegrable u)
    (z : ComplexModel n) :
    Integrable fun y ↦ u y * dbarDir e (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y := by
  have h1 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z e
  have h2 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z (I • e)
  refine ((h1.const_mul (1 / 2 : ℂ)).add (h2.const_mul (I / 2))).congr
    (Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.add_apply, dbarDir]
  ring

theorem dComm_eq (ha : ContDiff ℝ 1 a) (hu : LocallyIntegrable u) (z : ComplexModel n) :
    dComm ρ a e u z = (1 / 2 : ℂ) * friedrichsComm volume ρ a e u z +
      (-I / 2) * friedrichsComm volume ρ a (I • e) u z := by
  have h1 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z e
  have h2 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z (I • e)
  have hint : ∫ y, u y * dDir e (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y =
      (1 / 2 : ℂ) * (∫ y, u y * fderiv ℝ (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y e) +
        (-I / 2) * ∫ y, u y * fderiv ℝ (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y (I • e) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _)
      (h2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [dDir]
    ring
  rw [dComm, hint, friedrichsComm, friedrichsComm, dDir]
  ring

theorem dbarComm_eq (ha : ContDiff ℝ 1 a) (hu : LocallyIntegrable u) (z : ComplexModel n) :
    dbarComm ρ a e u z = (1 / 2 : ℂ) * friedrichsComm volume ρ a e u z +
      (I / 2) * friedrichsComm volume ρ a (I • e) u z := by
  have h1 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z e
  have h2 := integrable_mul_fderiv_mul_normed_sub ρ ha hu z (I • e)
  have hint : ∫ y, u y * dbarDir e (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y =
      (1 / 2 : ℂ) * (∫ y, u y * fderiv ℝ (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y e) +
        (I / 2) * ∫ y, u y * fderiv ℝ (fun y ↦ a y * (ρ.normed volume (z - y) : ℂ)) y (I • e) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _)
      (h2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [dbarDir]
    ring
  rw [dbarComm, hint, friedrichsComm, friedrichsComm, dbarDir]
  ring

end Wirtinger

theorem tendsto_eLpNorm_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℂ} (c : ℂ) (h : Tendsto (fun k ↦ eLpNorm (f k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (fun x ↦ c * f k x) 2 μ) atTop (𝓝 0) := by
  have e : ∀ k, eLpNorm (fun x ↦ c * f k x) 2 μ = ‖c‖ₑ * eLpNorm (f k) 2 μ :=
    fun k ↦ eLpNorm_const_smul c (f k) 2 μ
  simp_rw [e]
  simpa using ENNReal.Tendsto.const_mul h (Or.inr enorm_ne_top)

section Limits

variable {a : ComplexModel n → ℂ} (e : ComplexModel n) {u : ComplexModel n → ℂ}
  {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)

theorem aestronglyMeasurable_dComm (ρ : ContDiffBump (0 : ComplexModel n)) (ha : ContDiff ℝ 1 a)
    (hu : LocallyIntegrable u) : AEStronglyMeasurable (dComm ρ a e u) := by
  rw [show dComm ρ a e u = _ from funext (dComm_eq ρ e ha hu)]
  exact ((aestronglyMeasurable_friedrichsComm ρ e ha hu).const_mul _).add
    ((aestronglyMeasurable_friedrichsComm ρ (I • e) ha hu).const_mul _)

theorem aestronglyMeasurable_dbarComm (ρ : ContDiffBump (0 : ComplexModel n))
    (ha : ContDiff ℝ 1 a) (hu : LocallyIntegrable u) : AEStronglyMeasurable (dbarComm ρ a e u) := by
  rw [show dbarComm ρ a e u = _ from funext (dbarComm_eq ρ e ha hu)]
  exact ((aestronglyMeasurable_friedrichsComm ρ e ha hu).const_mul _).add
    ((aestronglyMeasurable_friedrichsComm ρ (I • e) ha hu).const_mul _)

theorem tendsto_eLpNorm_dComm (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (hu : MemLp u 2 volume) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (dComm (stdBump (r k) (hr k)) a e u) 2 volume) atTop (𝓝 0) := by
  have hul := hu.locallyIntegrable one_le_two
  simp_rw [show ∀ k, dComm (stdBump (r k) (hr k)) a e u = _ from
    fun k ↦ funext (dComm_eq (stdBump (r k) (hr k)) e ha hul)]
  exact tendsto_eLpNorm_add
    (fun k ↦ (aestronglyMeasurable_friedrichsComm _ e ha hul).const_mul _)
    (fun k ↦ (aestronglyMeasurable_friedrichsComm _ (I • e) ha hul).const_mul _)
    (tendsto_eLpNorm_const_mul _ (tendsto_eLpNorm_friedrichsComm ha hac e hu hr hr0))
    (tendsto_eLpNorm_const_mul _ (tendsto_eLpNorm_friedrichsComm ha hac (I • e) hu hr hr0))

theorem tendsto_eLpNorm_dbarComm (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (hu : MemLp u 2 volume) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (dbarComm (stdBump (r k) (hr k)) a e u) 2 volume) atTop (𝓝 0) := by
  have hul := hu.locallyIntegrable one_le_two
  simp_rw [show ∀ k, dbarComm (stdBump (r k) (hr k)) a e u = _ from
    fun k ↦ funext (dbarComm_eq (stdBump (r k) (hr k)) e ha hul)]
  exact tendsto_eLpNorm_add
    (fun k ↦ (aestronglyMeasurable_friedrichsComm _ e ha hul).const_mul _)
    (fun k ↦ (aestronglyMeasurable_friedrichsComm _ (I • e) ha hul).const_mul _)
    (tendsto_eLpNorm_const_mul _ (tendsto_eLpNorm_friedrichsComm ha hac e hu hr hr0))
    (tendsto_eLpNorm_const_mul _ (tendsto_eLpNorm_friedrichsComm ha hac (I • e) hu hr hr0))

end Limits

/-! ### Vanishing and congruence lemmas for first order systems -/

section Operators

variable {N N' : ℕ}

theorem dDir_eq_zero_of_eventuallyEq {F : ComplexModel n → ℂ} {y e : ComplexModel n}
    (hF : F =ᶠ[𝓝 y] 0) : dDir e F y = 0 := by
  simp [dDir, hF.fderiv_eq]

theorem dbarDir_eq_zero_of_eventuallyEq {F : ComplexModel n → ℂ} {y e : ComplexModel n}
    (hF : F =ᶠ[𝓝 y] 0) : dbarDir e F y = 0 := by
  simp [dbarDir, hF.fderiv_eq]

theorem mul_eventuallyEq_zero {c h : ComplexModel n → ℂ} {y : ComplexModel n}
    (hy : y ∉ tsupport h) : (fun x ↦ c x * h x) =ᶠ[𝓝 y] 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with x hx
  simp [hx]

/-- `P† h` vanishes outside the supports of the components of `h`. -/
theorem firstOrderAdjointApply_eq_zero_of_notMem
    (A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ)
    (B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ) (h : Fin N' → ComplexModel n → ℂ) (i : Fin N)
    {y : ComplexModel n} (hy : ∀ i', y ∉ tsupport (h i')) :
    firstOrderAdjointApply A A' B h i y = 0 := by
  unfold firstOrderAdjointApply
  have h1 : ∀ j i', -dbarDir (coordVec j) (fun y ↦ conj (A j y i' i) * h i' y) y -
      dDir (coordVec j) (fun y ↦ conj (A' j y i' i) * h i' y) y = 0 := fun j i' ↦ by
    rw [dbarDir_eq_zero_of_eventuallyEq (mul_eventuallyEq_zero (hy i')),
      dDir_eq_zero_of_eventuallyEq (mul_eventuallyEq_zero (hy i'))]
    simp
  have h2 : ∀ i', conj (B y i' i) * h i' y = 0 := fun i' ↦ by
    rw [image_eq_zero_of_notMem_tsupport (hy i'), mul_zero]
  simp [h1, h2]

/-- `P w` vanishes outside the supports of the components of `w`. -/
theorem firstOrderApply_eq_zero_of_notMem
    (A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ)
    (B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ) (w : Fin N → ComplexModel n → ℂ) (i' : Fin N')
    {z : ComplexModel n} (hz : ∀ i, z ∉ tsupport (w i)) :
    firstOrderApply A A' B w i' z = 0 := by
  unfold firstOrderApply
  have h1 : ∀ j i, A j z i' i * dDir (coordVec j) (w i) z +
      A' j z i' i * dbarDir (coordVec j) (w i) z = 0 := fun j i ↦ by
    rw [dDir_eq_zero_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 (hz i)),
      dbarDir_eq_zero_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 (hz i))]
    simp
  have h2 : ∀ i, B z i' i * w i z = 0 := fun i ↦ by
    rw [image_eq_zero_of_notMem_tsupport (hz i), mul_zero]
  simp [h1, h2]

variable {A A' At At' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ}
  {B Bt : ComplexModel n → Matrix (Fin N') (Fin N) ℂ} {S : Set (ComplexModel n)}

/-- `P† h` only depends on the coefficients on a set outside which `h` vanishes. -/
theorem firstOrderAdjointApply_congr (hA : ∀ j, ∀ y ∈ S, A j y = At j y)
    (hA' : ∀ j, ∀ y ∈ S, A' j y = At' j y) (hB : ∀ y ∈ S, B y = Bt y)
    {h : Fin N' → ComplexModel n → ℂ} (hS : ∀ i', ∀ y ∉ S, h i' y = 0) (i : Fin N)
    (y : ComplexModel n) :
    firstOrderAdjointApply A A' B h i y = firstOrderAdjointApply At At' Bt h i y := by
  have key : ∀ C Ct : ComplexModel n → Matrix (Fin N') (Fin N) ℂ, (∀ y ∈ S, C y = Ct y) →
      ∀ i', (fun y ↦ conj (C y i' i) * h i' y) = fun y ↦ conj (Ct y i' i) * h i' y := by
    intro C Ct hC i'
    funext y
    by_cases hy : y ∈ S
    · rw [hC y hy]
    · rw [hS i' y hy, mul_zero, mul_zero]
  unfold firstOrderAdjointApply
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i' _ ↦ ?_
    rw [key (A j) (At j) (hA j) i', key (A' j) (At' j) (hA' j) i']
  · exact Finset.sum_congr rfl fun i' _ ↦ congrFun (key B Bt hB i') y

/-- `P w (z)` only depends on the coefficients at `z`. -/
theorem firstOrderApply_congr_of_mem (hA : ∀ j, ∀ y ∈ S, A j y = At j y)
    (hA' : ∀ j, ∀ y ∈ S, A' j y = At' j y) (hB : ∀ y ∈ S, B y = Bt y)
    (w : Fin N → ComplexModel n → ℂ) (i' : Fin N') {z : ComplexModel n} (hz : z ∈ S) :
    firstOrderApply A A' B w i' z = firstOrderApply At At' Bt w i' z := by
  simp only [firstOrderApply, fun j ↦ hA j z hz, fun j ↦ hA' j z hz, hB z hz]

end Operators

/-! ### Testing against translated bumps -/

section BumpTest

variable {N N' : ℕ}

/-- The test vector `y ↦ ρ(z - y) e_{i'}`. -/
def bumpTest (ρ : ContDiffBump (0 : ComplexModel n)) (z : ComplexModel n) (i' : Fin N') :
    Fin N' → ComplexModel n → ℂ :=
  fun i'' y ↦ if i'' = i' then (ρ.normed volume (z - y) : ℂ) else 0

variable (ρ : ContDiffBump (0 : ComplexModel n)) (z : ComplexModel n) (i' : Fin N')

theorem tsupport_bumpTest_subset (i'' : Fin N') :
    tsupport (bumpTest ρ z i' i'') ⊆ closedBall z ρ.rOut := by
  refine closure_minimal (fun y hy ↦ ?_) isClosed_closedBall
  by_contra hy'
  have h : ρ.rOut < dist y z := not_le.1 (by simpa [mem_closedBall] using hy')
  apply hy
  simp [bumpTest, normed_sub_eq_zero (μ := volume) ρ h.le]

theorem isTestFunctionOn_bumpTest {D : Set (ComplexModel n)} (hz : closedBall z ρ.rOut ⊆ D)
    (i'' : Fin N') : IsTestFunctionOn D (bumpTest ρ z i' i'') := by
  refine ⟨?_, (isCompact_closedBall z ρ.rOut).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_bumpTest_subset ρ z i' i''), (tsupport_bumpTest_subset ρ z i' i'').trans hz⟩
  by_cases h : i'' = i'
  · have e : bumpTest ρ z i' i'' = fun y ↦ (ρ.normed volume (z - y) : ℂ) :=
      funext fun y ↦ by simp [bumpTest, h]
    rw [e]
    exact contDiff_normed_sub (μ := volume) (k := ⊤) ρ z
  · have e : bumpTest ρ z i' i'' = fun _ ↦ 0 := funext fun y ↦ by simp [bumpTest, h]
    rw [e]
    exact contDiff_const

/-- `conj (P†(ρ(z - ·) e_{i'}))_i = ∑_j (-∂_j(A_j ρ(z - ·)) - ∂_{j̄}(A'_j ρ(z - ·))) + B ρ(z - ·)`
(entries `(i', i)`). -/
theorem conj_firstOrderAdjointApply_bumpTest
    {A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ}
    {B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ}
    (hA : ∀ j i' i, ContDiff ℝ 1 fun y ↦ A j y i' i)
    (hA' : ∀ j i' i, ContDiff ℝ 1 fun y ↦ A' j y i' i)
    (i : Fin N) (y : ComplexModel n) :
    conj (firstOrderAdjointApply A A' B (bumpTest ρ z i') i y) =
      ∑ j, (-dDir (coordVec j) (fun y ↦ A j y i' i * (ρ.normed volume (z - y) : ℂ)) y -
        dbarDir (coordVec j) (fun y ↦ A' j y i' i * (ρ.normed volume (z - y) : ℂ)) y) +
      B y i' i * (ρ.normed volume (z - y) : ℂ) := by
  have hzero : ∀ (c : ComplexModel n → ℂ) (i'' : Fin N'), i'' ≠ i' →
      (fun y ↦ c y * bumpTest ρ z i' i'' y) = fun _ ↦ 0 := by
    intro c i'' h
    funext y
    simp [bumpTest, h]
  have hone : ∀ c : ComplexModel n → ℂ, (fun y ↦ conj (c y) * bumpTest ρ z i' i' y) =
      fun y ↦ conj (c y * (ρ.normed volume (z - y) : ℂ)) := by
    intro c
    funext y
    simp [bumpTest]
  have hin : ∀ j, ∑ i'', (-dbarDir (coordVec j)
      (fun y ↦ conj (A j y i'' i) * bumpTest ρ z i' i'' y) y
      - dDir (coordVec j) (fun y ↦ conj (A' j y i'' i) * bumpTest ρ z i' i'' y) y) =
      -dbarDir (coordVec j) (fun y ↦ conj (A j y i' i * (ρ.normed volume (z - y) : ℂ))) y -
        dDir (coordVec j) (fun y ↦ conj (A' j y i' i * (ρ.normed volume (z - y) : ℂ))) y := by
    intro j
    rw [Finset.sum_eq_single_of_mem i' (Finset.mem_univ _) fun i'' _ h ↦ by
      rw [hzero _ i'' h, hzero _ i'' h]; simp [dDir, dbarDir], hone, hone]
  have hB : ∑ i'', conj (B y i'' i) * bumpTest ρ z i' i'' y =
      conj (B y i' i * (ρ.normed volume (z - y) : ℂ)) := by
    rw [Finset.sum_eq_single_of_mem i' (Finset.mem_univ _) fun i'' _ h ↦ by simp [bumpTest, h]]
    simp [bumpTest]
  have hj : ∀ j, -dbarDir (coordVec j) (fun y ↦ conj (A j y i' i * (ρ.normed volume (z - y) : ℂ))) y
      - dDir (coordVec j) (fun y ↦ conj (A' j y i' i * (ρ.normed volume (z - y) : ℂ))) y =
      conj (-dDir (coordVec j) (fun y ↦ A j y i' i * (ρ.normed volume (z - y) : ℂ)) y -
        dbarDir (coordVec j) (fun y ↦ A' j y i' i * (ρ.normed volume (z - y) : ℂ)) y) := by
    intro j
    have h1 : DifferentiableAt ℝ (fun y ↦ A j y i' i * (ρ.normed volume (z - y) : ℂ)) y :=
      ((hA j i' i).mul (contDiff_normed_sub ρ z)).differentiable one_ne_zero y
    have h2 : DifferentiableAt ℝ (fun y ↦ A' j y i' i * (ρ.normed volume (z - y) : ℂ)) y :=
      ((hA' j i' i).mul (contDiff_normed_sub ρ z)).differentiable one_ne_zero y
    rw [dbarDir_conj h1, dDir_conj h2]
    simp
  have : firstOrderAdjointApply A A' B (bumpTest ρ z i') i y =
      conj (∑ j, (-dDir (coordVec j) (fun y ↦ A j y i' i * (ρ.normed volume (z - y) : ℂ)) y -
        dbarDir (coordVec j) (fun y ↦ A' j y i' i * (ρ.normed volume (z - y) : ℂ)) y) +
      B y i' i * (ρ.normed volume (z - y) : ℂ)) := by
    rw [firstOrderAdjointApply, Finset.sum_congr rfl fun j _ ↦ hin j, hB,
      Finset.sum_congr rfl fun j _ ↦ hj j, map_add, map_sum]
  rw [this, conj_conj]

end BumpTest

/-! ### The transposed mollification and the commutator decomposition -/

section Decomposition

variable {N N' : ℕ}

/-- The transposed mollification `z ↦ ∑_i ∫ w_i conj (P†(ρ(z - ·) e_{i'}))_i`: for a weak
solution of `P w = f` this is `(ρ ⋆ f_{i'})(z)`. -/
def transposeMoll (A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ)
    (B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ) (ρ : ContDiffBump (0 : ComplexModel n))
    (w : Fin N → ComplexModel n → ℂ) (i' : Fin N') (z : ComplexModel n) : ℂ :=
  ∑ i, ∫ y, w i y * conj (firstOrderAdjointApply A A' B (bumpTest ρ z i') i y)

/-- **Commutator decomposition**: `P(ρ ⋆ w) - transposeMoll` is a sum of scalar Friedrichs
commutators. -/
theorem firstOrderApply_sub_transposeMoll
    {A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ}
    {B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ}
    (hA : ∀ j i' i, ContDiff ℝ 1 fun y ↦ A j y i' i)
    (hA' : ∀ j i' i, ContDiff ℝ 1 fun y ↦ A' j y i' i)
    (hB : ∀ i' i, Continuous fun y ↦ B y i' i) (ρ : ContDiffBump (0 : ComplexModel n))
    {w : Fin N → ComplexModel n → ℂ} (hw : ∀ i, LocallyIntegrable (w i)) (i' : Fin N')
    (z : ComplexModel n) :
    firstOrderApply A A' B (fun i ↦ ρ.normed volume ⋆[lsmul ℝ ℝ, volume] w i) i' z -
        transposeMoll A A' B ρ w i' z =
      ∑ i, (∑ j, (dComm ρ (fun y ↦ A j y i' i) (coordVec j) (w i) z +
          dbarComm ρ (fun y ↦ A' j y i' i) (coordVec j) (w i) z) +
        zeroComm volume ρ (fun y ↦ B y i' i) (w i) z) := by
  have hint : ∀ i, ∫ y, w i y * conj (firstOrderAdjointApply A A' B (bumpTest ρ z i') i y) =
      ∑ j, (-(∫ y, w i y * dDir (coordVec j)
          (fun y ↦ A j y i' i * (ρ.normed volume (z - y) : ℂ)) y) -
        ∫ y, w i y * dbarDir (coordVec j)
          (fun y ↦ A' j y i' i * (ρ.normed volume (z - y) : ℂ)) y) +
      ∫ y, w i y * (B y i' i * (ρ.normed volume (z - y) : ℂ)) := by
    intro i
    set F1 : Fin n → ComplexModel n → ℂ := fun j y ↦ w i y * dDir (coordVec j)
      (fun y ↦ A j y i' i * (ρ.normed volume (z - y) : ℂ)) y with hF1
    set F2 : Fin n → ComplexModel n → ℂ := fun j y ↦ w i y * dbarDir (coordVec j)
      (fun y ↦ A' j y i' i * (ρ.normed volume (z - y) : ℂ)) y with hF2
    have h1 : ∀ j, Integrable (F1 j) := fun j ↦
      integrable_mul_dDir_mul_normed_sub ρ (coordVec j) (hA j i' i) (hw i) z
    have h2 : ∀ j, Integrable (F2 j) := fun j ↦
      integrable_mul_dbarDir_mul_normed_sub ρ (coordVec j) (hA' j i' i) (hw i) z
    have h12 : ∀ j, Integrable fun y ↦ -F1 j y - F2 j y := fun j ↦ (h1 j).neg.sub (h2 j)
    have h3 : Integrable fun y ↦ w i y * (B y i' i * (ρ.normed volume (z - y) : ℂ)) :=
      (hw i).integrable_smul_right_of_hasCompactSupport
        ((hB i' i).mul (contDiff_normed_sub (k := 0) ρ z).continuous)
        (hasCompactSupport_normed_sub ρ z).mul_left
    calc ∫ y, w i y * conj (firstOrderAdjointApply A A' B (bumpTest ρ z i') i y)
        = ∫ y, (∑ j, (-F1 j y - F2 j y) +
          w i y * (B y i' i * (ρ.normed volume (z - y) : ℂ))) := by
          refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
          simp only [hF1, hF2]
          rw [conj_firstOrderAdjointApply_bumpTest ρ z i' hA hA' i y, mul_add, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = _ := by
          rw [integral_add (integrable_finsetSum _ fun j _ ↦ h12 j) h3,
            integral_finsetSum _ fun j _ ↦ h12 j]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          have hn : Integrable fun y ↦ -F1 j y := (h1 j).neg
          rw [integral_sub hn (h2 j), integral_neg]
  have hswap : ∑ j, ∑ i, (A j z i' i *
      dDir (coordVec j) (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] w i) z
      + A' j z i' i * dbarDir (coordVec j) (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] w i) z) =
      ∑ i, ∑ j, (A j z i' i * dDir (coordVec j) (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] w i) z
      + A' j z i' i * dbarDir (coordVec j) (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] w i) z) :=
    Finset.sum_comm
  rw [firstOrderApply, transposeMoll, hswap, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hint i]
  simp only [dComm, dbarComm, zeroComm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

end Decomposition

/-! ### Cut-off coefficients -/

theorem contDiff_ofReal_mul_of_tsupport {D : Set (ComplexModel n)} (hD : IsOpen D)
    {θ : ComplexModel n → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθD : tsupport θ ⊆ D) {a : ComplexModel n → ℂ}
    (ha : ContDiffOn ℝ ∞ a D) : ContDiff ℝ ∞ fun z ↦ (θ z : ℂ) * a z := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  by_cases hx : x ∈ D
  · exact (Complex.ofRealCLM.contDiff.comp hθ).contDiffAt.mul (ha.contDiffAt (hD.mem_nhds hx))
  · have hxs : x ∉ tsupport θ := fun h ↦ hx (hθD h)
    have h0 : (fun z ↦ (θ z : ℂ) * a z) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxs] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem hasCompactSupport_ofReal_mul {θ : ComplexModel n → ℝ} (hθc : HasCompactSupport θ)
    (a : ComplexModel n → ℂ) : HasCompactSupport fun z ↦ (θ z : ℂ) * a z :=
  (hθc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) Complex.ofReal_zero).mul_right

end FriedrichsProof

open FriedrichsProof

/-- **Friedrichs' lemma** (`claude-twisted-l2:friedrichs`): `FriedrichsStatement n N N'` holds. -/
theorem friedrichsStatement (n N N' : ℕ) : FriedrichsStatement n N N' := by
  intro D hD A A' B hA hA' hB K hK hKD w f hw hwK hf hweak
  -- geometry
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
  set K₂ := cthickening (δ / 2) K with hK₂
  have hK₂c : IsCompact K₂ := hK.cthickening
  have hK₂D : K₂ ⊆ D := (cthickening_mono (by linarith) K).trans hδD
  -- cut-off coefficients
  obtain ⟨θ, hθ, hθc, hθD, hθ1, -⟩ := exists_contDiff_cutoff hK₂c hD hK₂D
  have hθK : ∀ z ∈ K₂, θ z = 1 := fun z hz ↦ (hθ1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  set At : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ :=
    fun j z ↦ Matrix.of fun i' i ↦ (θ z : ℂ) * A j z i' i with hAt_def
  set At' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ :=
    fun j z ↦ Matrix.of fun i' i ↦ (θ z : ℂ) * A' j z i' i with hAt'_def
  set Bt : ComplexModel n → Matrix (Fin N') (Fin N) ℂ :=
    fun z ↦ Matrix.of fun i' i ↦ (θ z : ℂ) * B z i' i with hBt_def
  have hAt : ∀ j i' i, ContDiff ℝ ∞ fun y ↦ At j y i' i := fun j i' i ↦
    contDiff_ofReal_mul_of_tsupport hD hθ hθD (hA j i' i)
  have hAt' : ∀ j i' i, ContDiff ℝ ∞ fun y ↦ At' j y i' i := fun j i' i ↦
    contDiff_ofReal_mul_of_tsupport hD hθ hθD (hA' j i' i)
  have hBt : ∀ i' i, ContDiff ℝ ∞ fun y ↦ Bt y i' i := fun i' i ↦
    contDiff_ofReal_mul_of_tsupport hD hθ hθD (hB i' i)
  have hAt1 : ∀ j i' i, ContDiff ℝ 1 fun y ↦ At j y i' i := fun j i' i ↦
    (hAt j i' i).of_le (by norm_cast)
  have hAt'1 : ∀ j i' i, ContDiff ℝ 1 fun y ↦ At' j y i' i := fun j i' i ↦
    (hAt' j i' i).of_le (by norm_cast)
  have hAtc : ∀ j i' i, HasCompactSupport fun y ↦ At j y i' i := fun j i' i ↦
    hasCompactSupport_ofReal_mul hθc _
  have hAt'c : ∀ j i' i, HasCompactSupport fun y ↦ At' j y i' i := fun j i' i ↦
    hasCompactSupport_ofReal_mul hθc _
  have hBtc : ∀ i' i, HasCompactSupport fun y ↦ Bt y i' i := fun i' i ↦
    hasCompactSupport_ofReal_mul hθc _
  have hAK : ∀ j, ∀ y ∈ K₂, A j y = At j y := fun j y hy ↦ by
    ext i' i
    simp [At, hθK y hy]
  have hA'K : ∀ j, ∀ y ∈ K₂, A' j y = At' j y := fun j y hy ↦ by
    ext i' i
    simp [At', hθK y hy]
  have hBK : ∀ y ∈ K₂, B y = Bt y := fun y hy ↦ by
    ext i' i
    simp [Bt, hθK y hy]
  -- mollifiers
  set r : ℕ → ℝ := fun k ↦ δ / 4 * (1 / ((k : ℝ) + 1)) with hr_def
  have hr : ∀ k, 0 < r k := fun k ↦ by simp only [r]; positivity
  have hrle : ∀ k, r k ≤ δ / 4 := fun k ↦ by
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    simp only [r]
    nlinarith
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (δ / 4)
    rwa [mul_zero] at h
  set ρ : ℕ → ContDiffBump (0 : ComplexModel n) := fun k ↦ stdBump (r k) (hr k) with hρ_def
  have hρr : ∀ k, (ρ k).rOut = r k := fun k ↦ rfl
  have hρ0 : Tendsto (fun k ↦ (ρ k).rOut) atTop (𝓝 0) := hr0
  set ws : ℕ → Fin N → ComplexModel n → ℂ :=
    fun k i ↦ (ρ k).normed volume ⋆[lsmul ℝ ℝ, volume] w i with hws_def
  -- supports
  have hwl : ∀ i, LocallyIntegrable (w i) := fun i ↦ (hw i).locallyIntegrable one_le_two
  have htsw : ∀ i, tsupport (w i) ⊆ K := fun i ↦
    closure_minimal (fun z hz ↦ by_contra fun h ↦ hz (hwK i z h)) hK.isClosed
  have htsws : ∀ k i, tsupport (ws k i) ⊆ cthickening (r k) K := by
    intro k i
    refine (tsupport_bump_convolution_subset (ρ k) (w i)).trans ?_
    rintro _ ⟨x, hx, b, hb, rfl⟩
    refine mem_cthickening_of_dist_le _ x _ _ (htsw i hx) ?_
    rw [dist_eq_norm, add_sub_cancel_left, ← hρr k]
    simpa using hb
  have hK4 : ∀ k, cthickening (r k) K ⊆ cthickening (δ / 4) K := fun k ↦ cthickening_mono (hrle k) K
  have hK42 : cthickening (δ / 4) K ⊆ K₂ := cthickening_mono (by linarith) K
  refine ⟨ws, fun k i ↦ ⟨contDiff_bump_convolution (ρ k) (hwl i),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) (htsws k i),
    (htsws k i).trans ((hK4 k).trans (hK42.trans hK₂D))⟩,
    fun i ↦ tendsto_eLpNorm_bump_convolution_sub (hw i) hρ0, fun i' ↦ ?_⟩
  -- `f = 0` a.e. on `D \ K`
  have hfK : ∀ i'', ∀ᵐ z, z ∈ D \ K → f i'' z = 0 := by
    intro i''
    refine (hD.sdiff hK.isClosed).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((hf i'').locallyIntegrable one_le_two).locallyIntegrableOn _) fun g hg hgc hgU ↦ ?_
    set h : Fin N' → ComplexModel n → ℂ := fun i y ↦ if i = i'' then (g y : ℂ) else 0 with h_def
    have hts : ∀ i, tsupport (h i) ⊆ tsupport g := by
      intro i
      refine closure_minimal (fun y hy ↦ subset_tsupport g ?_) (isClosed_tsupport g)
      intro h0
      apply hy
      simp [h, h0]
    have htest : ∀ i, IsTestFunctionOn D (h i) := by
      intro i
      refine ⟨?_, hgc.of_isClosed_subset (isClosed_tsupport _) (hts i),
        (hts i).trans (hgU.trans sdiff_subset)⟩
      by_cases hi : i = i''
      · have e : h i = fun y ↦ (g y : ℂ) := funext fun y ↦ by simp [h, hi]
        rw [e]
        exact Complex.ofRealCLM.contDiff.comp hg
      · have e : h i = fun _ ↦ 0 := funext fun y ↦ by simp [h, hi]
        rw [e]
        exact contDiff_const
    have hw0 : ∑ i, ∫ y, w i y * conj (firstOrderAdjointApply A A' B h i y) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have e : (fun y ↦ w i y * conj (firstOrderAdjointApply A A' B h i y)) = fun _ ↦ 0 := by
        funext y
        by_cases hyK : y ∈ K
        · rw [firstOrderAdjointApply_eq_zero_of_notMem A A' B h i fun i₀ hy ↦
            (hgU (hts i₀ hy)).2 hyK]
          simp
        · rw [hwK i y hyK, zero_mul]
      rw [e, integral_zero]
    have hsum := hweak h htest
    rw [hw0, Finset.sum_eq_single_of_mem i'' (Finset.mem_univ _)
      (fun i _ hi ↦ by simp [h, hi])] at hsum
    calc ∫ x, g x • f i'' x = ∫ x, f i'' x * conj (h i'' x) :=
          integral_congr_ae (Eventually.of_forall fun x ↦ by
            simp only [h, if_pos rfl, Complex.conj_ofReal, Complex.real_smul]
            ring)
      _ = 0 := hsum
  -- the truncated datum `g = 1_K f`
  set g := K.indicator (f i') with hg_def
  have hg2 : MemLp g 2 volume := (hf i').indicator hK.measurableSet
  have hfg : ∀ᵐ z, z ∈ D → f i' z = g z := by
    filter_upwards [hfK i'] with z hz hzD
    by_cases hzK : z ∈ K
    · simp [g, hzK]
    · simp [g, hzK, hz ⟨hzD, hzK⟩]
  -- the weak equation identifies the transposed mollification with `ρ ⋆ g`
  have hT : ∀ k z, transposeMoll At At' Bt (ρ k) w i' z =
      ((ρ k).normed volume ⋆[lsmul ℝ ℝ, volume] g) z := by
    intro k z
    by_cases hz : z ∈ cthickening (δ / 4) K
    · have hball : closedBall z (ρ k).rOut ⊆ K₂ := by
        refine (closedBall_subset_cthickening hz _).trans
          ((cthickening_cthickening_subset (hr k).le (by linarith) K).trans
            (cthickening_mono ?_ K))
        linarith [hrle k]
      have htest := isTestFunctionOn_bumpTest (ρ k) z i' (hball.trans hK₂D)
      have hW := hweak (bumpTest (ρ k) z i') htest
      have hL : ∑ i'', ∫ y, f i'' y * conj (bumpTest (ρ k) z i' i'' y) =
          ((ρ k).normed volume ⋆[lsmul ℝ ℝ, volume] g) z := by
        rw [Finset.sum_eq_single_of_mem i' (Finset.mem_univ _) fun i'' _ hi ↦ by
          simp [bumpTest, hi], bump_convolution_apply_eq_integral]
        refine integral_congr_ae ?_
        filter_upwards [hfg] with y hy
        by_cases hyD : y ∈ D
        · simp [bumpTest, hy hyD, mul_comm]
        · have hyb : y ∉ closedBall z (ρ k).rOut := fun h ↦ hyD (hK₂D (hball h))
          have h' : (ρ k).rOut < dist y z := not_le.1 (by simpa [mem_closedBall] using hyb)
          simp [bumpTest, normed_sub_eq_zero (μ := volume) (ρ k) h'.le]
      rw [← hL, hW, transposeMoll]
      refine Finset.sum_congr rfl fun i _ ↦ integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      have hS : ∀ i'', ∀ y ∉ K₂, bumpTest (ρ k) z i' i'' y = 0 := fun i'' y hy ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hy (hball (tsupport_bumpTest_subset _ _ _ _ h))
      simp only
      rw [firstOrderAdjointApply_congr hAK hA'K hBK hS i y]
    · have hfar : ∀ y ∈ K, δ / 4 < dist z y := fun y hy ↦
        not_le.1 fun h ↦ hz (mem_cthickening_of_dist_le z y _ K hy h)
      have h1 : transposeMoll At At' Bt (ρ k) w i' z = 0 := by
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        have e : (fun y ↦ w i y * conj (firstOrderAdjointApply At At' Bt
            (bumpTest (ρ k) z i') i y)) = fun _ ↦ 0 := by
          funext y
          by_cases hyK : y ∈ K
          · have hy : ∀ i'', y ∉ tsupport (bumpTest (ρ k) z i' i'') := fun i'' h ↦ by
              have h1 := mem_closedBall.1 (tsupport_bumpTest_subset _ _ _ _ h)
              have h2 := hfar y hyK
              rw [dist_comm] at h2
              linarith [hrle k, hρr k]
            rw [firstOrderAdjointApply_eq_zero_of_notMem At At' Bt _ i hy]
            simp
          · rw [hwK i y hyK, zero_mul]
        rw [e, integral_zero]
      rw [h1, bump_convolution_apply_eq_integral]
      symm
      refine (integral_congr_ae (Eventually.of_forall fun y ↦ ?_)).trans (integral_zero _ _)
      by_cases hyK : y ∈ K
      · have h' : (ρ k).rOut ≤ dist y z := by
          have h2 := hfar y hyK
          rw [dist_comm] at h2
          linarith [hrle k, hρr k]
        simp [normed_sub_eq_zero (μ := volume) (ρ k) h']
      · simp [g, hyK]
  -- the original operator agrees with the cut-off one on the mollifications
  have hP : ∀ k z, firstOrderApply A A' B (ws k) i' z = firstOrderApply At At' Bt (ws k) i' z := by
    intro k z
    by_cases hz : z ∈ K₂
    · exact firstOrderApply_congr_of_mem hAK hA'K hBK (ws k) i' hz
    · have hz' : ∀ i, z ∉ tsupport (ws k i) := fun i h ↦ hz (hK42 (hK4 k (htsws k i h)))
      rw [firstOrderApply_eq_zero_of_notMem _ _ _ _ _ hz',
        firstOrderApply_eq_zero_of_notMem _ _ _ _ _ hz']
  have hdec : ∀ k z, firstOrderApply At At' Bt (ws k) i' z - transposeMoll At At' Bt (ρ k) w i' z =
      ∑ i, (∑ j, (dComm (ρ k) (fun y ↦ At j y i' i) (coordVec j) (w i) z +
          dbarComm (ρ k) (fun y ↦ At' j y i' i) (coordVec j) (w i) z) +
        zeroComm volume (ρ k) (fun y ↦ Bt y i' i) (w i) z) := fun k z ↦
    firstOrderApply_sub_transposeMoll hAt1 hAt'1 (fun i' i ↦ (hBt i' i).continuous) (ρ k) hwl i' z
  have hae : ∀ k, (fun z ↦ firstOrderApply A A' B (ws k) i' z - f i' z) =ᵐ[volume.restrict D]
      fun z ↦ (firstOrderApply At At' Bt (ws k) i' z - transposeMoll At At' Bt (ρ k) w i' z) +
        (((ρ k).normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z) := by
    intro k
    filter_upwards [(ae_restrict_iff' hD.measurableSet).2 hfg] with z hz
    rw [hP k z, hT k z, hz]
    ring
  -- the scalar commutators tend to zero
  have hcomm : Tendsto (fun k ↦ eLpNorm (fun z ↦ firstOrderApply At At' Bt (ws k) i' z -
      transposeMoll At At' Bt (ρ k) w i' z) 2 volume) atTop (𝓝 0) := by
    simp_rw [show ∀ k, (fun z ↦ firstOrderApply At At' Bt (ws k) i' z -
        transposeMoll At At' Bt (ρ k) w i' z) = _ from fun k ↦ funext (hdec k)]
    have hBb : ∀ i, ∃ C, ∀ y, ‖Bt y i' i‖ ≤ C := fun i ↦
      (hBt i' i).continuous.bounded_above_of_compact_support (hBtc i' i)
    choose CB hCB using hBb
    refine tendsto_eLpNorm_sum
      (f := fun k i z ↦ ∑ j, (dComm (ρ k) (fun y ↦ At j y i' i) (coordVec j) (w i) z +
          dbarComm (ρ k) (fun y ↦ At' j y i' i) (coordVec j) (w i) z) +
        zeroComm volume (ρ k) (fun y ↦ Bt y i' i) (w i) z) (fun k i ↦ ?_) fun i ↦ ?_
    · exact (Finset.univ.aestronglyMeasurable_fun_sum fun j _ ↦
        (aestronglyMeasurable_dComm (coordVec j) (ρ k) (hAt1 j i' i) (hwl i)).add
          (aestronglyMeasurable_dbarComm (coordVec j) (ρ k) (hAt'1 j i' i) (hwl i))).add
        (aestronglyMeasurable_zeroComm (ρ k) (hBt i' i).continuous (hCB i) (hw i))
    · refine tendsto_eLpNorm_add
        (f := fun k z ↦ ∑ j, (dComm (ρ k) (fun y ↦ At j y i' i) (coordVec j) (w i) z +
          dbarComm (ρ k) (fun y ↦ At' j y i' i) (coordVec j) (w i) z))
        (g := fun k z ↦ zeroComm volume (ρ k) (fun y ↦ Bt y i' i) (w i) z)
        (fun k ↦ Finset.univ.aestronglyMeasurable_fun_sum fun j _ ↦
          (aestronglyMeasurable_dComm (coordVec j) (ρ k) (hAt1 j i' i) (hwl i)).add
            (aestronglyMeasurable_dbarComm (coordVec j) (ρ k) (hAt'1 j i' i) (hwl i)))
        (fun k ↦ aestronglyMeasurable_zeroComm (ρ k) (hBt i' i).continuous (hCB i) (hw i))
        ?_ (tendsto_eLpNorm_zeroComm (hBt i' i).continuous (hCB i) (hw i) hρ0)
      refine tendsto_eLpNorm_sum
        (f := fun k j z ↦ dComm (ρ k) (fun y ↦ At j y i' i) (coordVec j) (w i) z +
          dbarComm (ρ k) (fun y ↦ At' j y i' i) (coordVec j) (w i) z)
        (fun k j ↦ (aestronglyMeasurable_dComm (coordVec j) (ρ k) (hAt1 j i' i) (hwl i)).add
          (aestronglyMeasurable_dbarComm (coordVec j) (ρ k) (hAt'1 j i' i) (hwl i))) fun j ↦ ?_
      exact tendsto_eLpNorm_add
        (fun k ↦ aestronglyMeasurable_dComm (coordVec j) (ρ k) (hAt1 j i' i) (hwl i))
        (fun k ↦ aestronglyMeasurable_dbarComm (coordVec j) (ρ k) (hAt'1 j i' i) (hwl i))
        (tendsto_eLpNorm_dComm (coordVec j) hr (hAt1 j i' i) (hAtc j i' i) (hw i) hr0)
        (tendsto_eLpNorm_dbarComm (coordVec j) hr (hAt'1 j i' i) (hAt'c j i' i) (hw i) hr0)
  have hmain := tendsto_eLpNorm_add
    (f := fun k z ↦ firstOrderApply At At' Bt (ws k) i' z - transposeMoll At At' Bt (ρ k) w i' z)
    (g := fun k z ↦ ((ρ k).normed volume ⋆[lsmul ℝ ℝ, volume] g) z - g z)
    (fun k ↦ by
      rw [show (fun z ↦ firstOrderApply At At' Bt (ws k) i' z -
          transposeMoll At At' Bt (ρ k) w i' z) = _ from funext (hdec k)]
      have hBb : ∀ i, ∃ C, ∀ y, ‖Bt y i' i‖ ≤ C := fun i ↦
        (hBt i' i).continuous.bounded_above_of_compact_support (hBtc i' i)
      choose CB hCB using hBb
      exact Finset.univ.aestronglyMeasurable_fun_sum fun i _ ↦
        (Finset.univ.aestronglyMeasurable_fun_sum fun j _ ↦
          (aestronglyMeasurable_dComm (coordVec j) (ρ k) (hAt1 j i' i) (hwl i)).add
            (aestronglyMeasurable_dbarComm (coordVec j) (ρ k) (hAt'1 j i' i) (hwl i))).add
          (aestronglyMeasurable_zeroComm (ρ k) (hBt i' i).continuous (hCB i) (hw i)))
    (fun k ↦ (contDiff_bump_convolution (ρ k)
      (hg2.locallyIntegrable one_le_two)).continuous.aestronglyMeasurable.sub hg2.1)
    hcomm (tendsto_eLpNorm_bump_convolution_sub hg2 hρ0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmain (fun _ ↦ zero_le)
    fun k ↦ ?_
  rw [eLpNorm_congr_ae (hae k)]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

end SGPT.Trace.TwistedL2
