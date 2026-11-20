import SGPT.NPP.NonPluripolarCurrent5Slicing
import SGPT.NPP.BedfordTaylorTopDegree
import SGPT.Foundations.Analysis.Pending.FibrePushforwardProductForm

/-!
# Fubini for Bedford–Taylor products along a product `Q × D`

Source: `chapter_npp.tex`, `lma:boundedfibrefubini`.

Let `Q ⊆ ℂⁿ` and `D ⊆ ℂᵐ` be open, `p₂ : Q × D → D` the second projection, `η` a smooth real
`(m,m)`-form on `D` and `u₁, …, uₙ` locally bounded psh functions on `Q × D`.  Put
`M = dd^c u₁ ∧ ⋯ ∧ dd^c uₙ` (the Bedford–Taylor product, a closed positive current of bidimension
`(m,m)` on `Q × D`, TN's `btProduct`) and `M_z = dd^c_x (u₁)_z ∧ ⋯ ∧ dd^c_x (uₙ)_z` (top degree on
`Q`).  For every bounded Borel `h` with compact support in `Q × D`,

`∫_{Q×D} h p₂^*η ∧ M = ∫_D (∫_Q h_z M_z) η(z)` (`boundedFibreFubini`).

## Conventions

`Q × D` is the open subset `prodOpens Q D` of `ℂⁿ⁺ᵐ` (`ProductComplexManifold.prodModelEquiv`,
first `n` coordinates `x`, last `m` coordinates `z`).  A real `(m,m)`-form on `D ⊆ ℂᵐ` is a map
`η : ℂᵐ → RealForm m (2m)` (top degree); `∫_D g η = ∫_D g(z) η_z(e₁, i e₁, …) dλ(z)` with the
standard complex orientation (`TopDegreeDensity.topDensity`).  The pull-back `p₂^*η` is
`(p₂^*η)_q = η_{p₂ q} ∘ p₂` (`pullbackSnd`); it lies in the span of the strongly positive cone
(`pullbackSnd_eq`), so the top-degree current `p₂^*η ∧ M` is the signed measure
`L_q(p₂^*η_q) dσ_M(q)` (`σ_M` the trace measure of `M`, `L_q` its pointwise density form;
`wedgeForm_pullbackSnd_apply` identifies it with TN's current `M ∧ p₂^*η` on test functions).

## Proof

* `pullbackSnd_eq` — **linear algebra**: `p₂^*η = π^m η(e₁, i e₁, …) · dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²`
  (`dd^c|z_k|² = (i/2π) dz_k ∧ dz̄_k`, the top power density being `π^{-m}`).
* `btProduct_apply_baseForm` — by the reduction to top degree (`BedfordTaylorTopDegree`),
  `⟨M, φ · dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²⟩ = ∫ φ dν` with `ν` the Bedford–Taylor measure of
  `(u₁, …, uₙ, |z₁|², …, |z_m|²)`.
* `integral_mul_isBTLimit_eq_fibreIntegral` (`NonPluripolarCurrent5Slicing`):
  `∫ χ F dν = π^{-m} ∫ ∫ χ_z F_z dμ_z dz`.
* The fibre measures `μ_z` are the trace measures of `M_z` (`isBTLimit_fibreMeasure`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff Distributions ComplexOrder

namespace SGPT.NPP.FibreSlicing

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold

attribute [local instance] addCommGroupFormSpan

variable {n m : ℕ}

/-! ### The forms `dd^c |z_j|²` -/

section SqCoord

variable {N : ℕ}

/-- `|z_j|²` on `ℂᴺ`. -/
def sqCoord (j : Fin N) : ComplexModel N → ℝ := fun q => ‖q j‖ ^ 2

/-- The coordinate `z_j`, as a real continuous linear map. -/
def coordCLM' (j : Fin N) : ComplexModel N →L[ℝ] ℂ :=
  (EuclideanSpace.proj j : ComplexModel N →L[ℂ] ℂ).restrictScalars ℝ

@[simp] theorem coordCLM'_apply (j : Fin N) (q : ComplexModel N) : coordCLM' j q = q j := rfl

theorem contDiff_sqCoord (j : Fin N) : ContDiff ℝ ∞ (sqCoord j) := by
  have : sqCoord j = fun q => ‖coordCLM' j q‖ ^ 2 := rfl
  rw [this]
  exact (contDiff_norm_sq ℝ).comp (coordCLM' j).contDiff

theorem realHessian_sqCoord (j : Fin N) (q a b : ComplexModel N) :
    realHessian (sqCoord j) q a b = 2 * inner ℝ (a j) (b j) := by
  have h := realHessian_comp_affine (contDiff_norm_sq ℝ : ContDiff ℝ 2 fun x : ℂ => ‖x‖ ^ 2)
    (coordCLM' j) 0 q a b
  have hfun : (fun y : ComplexModel N => ‖(0 : ℂ) + coordCLM' j y‖ ^ 2) = sqCoord j := by
    funext y
    simp [sqCoord]
  rw [hfun] at h
  rw [h, realHessian_norm_sq]
  rfl

theorem smoothDDC_sqCoord_apply (j : Fin N) (q v w : ComplexModel N) :
    smoothDDC (sqCoord j) q ![v, w] =
      (2 * inner ℝ (w j) (Complex.I * v j) - 2 * inner ℝ (v j) (Complex.I * w j)) /
        (4 * Real.pi) := by
  rw [FirstPass.smoothDDC_apply_eq_realHessian
    (((contDiff_sqCoord j).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt),
    realHessian_sqCoord, realHessian_sqCoord]
  simp [PiLp.smul_apply]

theorem fin_two_eq (v : Fin 2 → ComplexModel N) : v = ![v 0, v 1] := by
  funext i
  fin_cases i <;> rfl

/-- `dd^c |z_j|²` is constant. -/
theorem smoothDDC_sqCoord (j : Fin N) (q : ComplexModel N) :
    smoothDDC (sqCoord j) q = smoothDDC (sqCoord j) 0 := by
  ext v
  rw [fin_two_eq v, smoothDDC_sqCoord_apply, smoothDDC_sqCoord_apply]

theorem isSemipositiveOneOne_smoothDDC_sqCoord (j : Fin N) (q : ComplexModel N) :
    IsSemipositiveOneOne (smoothDDC (sqCoord j) q) := by
  refine LocalBedfordTaylorCollar.isSemipositiveOneOne_smoothDDC_of_leviForm
    (((contDiff_sqCoord j).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt) fun v => ?_
  rw [leviForm, realHessian_sqCoord, realHessian_sqCoord]
  have h1 := real_inner_self_nonneg (x := v j)
  have h2 := real_inner_self_nonneg (x := (Complex.I • v) j)
  positivity

/-- The rank-one matrix `E_{jj}`. -/
def unitMat (j : Fin N) : Matrix (Fin N) (Fin N) ℂ := fun a b => if a = j ∧ b = j then 1 else 0

theorem complexHessian_sqCoord (j : Fin N) (q : ComplexModel N) :
    complexHessian (sqCoord j) q = unitMat j := by
  ext a b
  simp only [complexHessian, realHessian_sqCoord, unitMat]
  by_cases ha : a = j <;> by_cases hb : b = j
  · subst ha hb
    simp [coordinateVector]
    norm_num
  · simp [coordinateVector, hb, Ne.symm hb]
  · simp [coordinateVector, ha, Ne.symm ha]
  · simp [coordinateVector, ha, Ne.symm ha]

theorem mixedCoefficient_unitMat : mixedCoefficient (fun k : Fin N => unitMat k) = 1 := by
  classical
  unfold mixedCoefficient
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
  · have e : (fun j k => unitMat ((1 : Equiv.Perm (Fin N)) j) j k) =
        (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext j k
      by_cases hjk : j = k
      · subst hjk
        simp [unitMat]
      · simp [unitMat, hjk, Ne.symm hjk]
    rw [e, Matrix.det_one]
  · intro σ _ hσ
    obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hσ (Equiv.ext h)
    apply Matrix.det_eq_zero_of_row_eq_zero j
    intro k
    simp [unitMat, Ne.symm hj]
  · simp

/-- **`dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_N|²` has density `π^{-N}`.** -/
theorem topDensity_wedgeProd_sqCoord :
    topDensity (wedgeProd N fun k => smoothDDC (sqCoord k) (0 : ComplexModel N)) =
      (Real.pi ^ N)⁻¹ := by
  rw [topDensity_wedgeProd, FirstPass.MongeAmpere.actualMixedTopDensity_smoothDDC
    (fun i => ((contDiff_sqCoord i).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  simp only [mixedDensity, complexHessian_sqCoord, mixedCoefficient_unitMat, Complex.one_re,
    one_div]

/-- Top-degree forms are determined by their density. -/
theorem topDensity_injective' : Function.Injective (topDensity (n := N)) := by
  intro A B h
  have hA := A.toAlternatingMap.eq_smul_basis_det (topBasis N)
  have hB := B.toAlternatingMap.eq_smul_basis_det (topBasis N)
  ext v
  change A.toAlternatingMap v = B.toAlternatingMap v
  rw [hA, hB]
  exact congrArg (fun r : ℝ => (r • (topBasis N).det) v) h

end SqCoord

/-! ### The pull-back `p₂^*η` -/

section Pullback

open ProductMixedMeasure

theorem projSnd_apply_coord (q : ComplexModel (n + m)) (k : Fin m) :
    projSnd n m q k = q (Fin.natAdd n k) := by
  have hq : q = fibreMapM n m (projSnd n m q) (projFst n m q) := by
    simp only [fibreMapM, projSnd_apply, projFst_apply, Prod.mk.eta,
      ContinuousLinearEquiv.apply_symm_apply]
  conv_rhs => rw [hq]
  rw [fibreMapM_natAdd]

/-- The constant `(1,1)`-forms `dd^c|z_k|²` of the base coordinates on `ℂⁿ⁺ᵐ`. -/
def baseForm (n m : ℕ) (k : Fin m) : RealForm (n + m) 2 :=
  smoothDDC (sqCoord (Fin.natAdd n k)) 0

theorem baseForm_eq_comp (k : Fin m) :
    baseForm n m k =
      (smoothDDC (sqCoord k) (0 : ComplexModel m)).compContinuousLinearMap (projSnd n m) := by
  ext v
  rw [fin_two_eq v, baseForm, smoothDDC_sqCoord_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_vec, smoothDDC_sqCoord_apply,
    projSnd_apply_coord, projSnd_apply_coord]

/-- `dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²` on `ℂⁿ⁺ᵐ`. -/
def basePower (n m : ℕ) : RealForm (n + m) (2 * m) := wedgeProd m (baseForm n m)

theorem basePower_eq_comp :
    basePower n m = (wedgeProd m fun k => smoothDDC (sqCoord k) (0 : ComplexModel m)).compContinuousLinearMap
      (projSnd n m) := by
  rw [FibrePushforwardProductForm.wedgeProd_compContinuousLinearMap, basePower]
  congr 1
  funext k
  exact baseForm_eq_comp k

theorem basePower_mem_spCone : basePower n m ∈ spCone m := by
  have : ∀ (q : ℕ) (β : Fin q → RealForm (n + m) 2),
      (∀ j, IsSemipositiveOneOne (β j)) → wedgeProd q β ∈ spCone q := by
    intro q
    induction q with
    | zero => intro β _; exact unit_mem_spCone
    | succ q ih =>
      intro β hβ
      rw [wedgeProd_succ]
      exact wedge_mem_spCone (ih _ fun j => hβ _) (hβ _)
  exact this m _ fun k => isSemipositiveOneOne_smoothDDC_sqCoord _ _

theorem basePower_mem_formSpan : basePower n m ∈ formSpan (n + m) m :=
  mem_formSpan_of_mem_spCone basePower_mem_spCone

/-- **The pull-back of a top-degree form of the base**:
`p₂^* A = π^m A(e₁, i e₁, …) · dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²`. -/
theorem pullbackSnd_eq (A : RealForm m (2 * m)) :
    A.compContinuousLinearMap (projSnd n m) = (Real.pi ^ m * topDensity A) • basePower n m := by
  set W := wedgeProd m fun k => smoothDDC (sqCoord k) (0 : ComplexModel m)
  have hA : A = (Real.pi ^ m * topDensity A) • W := by
    apply topDensity_injective'
    rw [topDensity_smul, topDensity_wedgeProd_sqCoord]
    field_simp
  rw [basePower_eq_comp]
  conv_lhs => rw [hA]
  rfl

/-- The pull-back `p₂^*η` of a form `η` of top degree on the base, as a constant form of the span
`Λ_m` at every point of `ℂⁿ⁺ᵐ`. -/
def pullbackSnd (η : ComplexModel m → RealForm m (2 * m)) (q : ComplexModel (n + m)) :
    formSpan (n + m) m :=
  ⟨(η (projSnd n m q)).compContinuousLinearMap (projSnd n m), by
    rw [pullbackSnd_eq]
    exact Submodule.smul_mem _ _ basePower_mem_formSpan⟩

@[simp] theorem coe_pullbackSnd (η : ComplexModel m → RealForm m (2 * m))
    (q : ComplexModel (n + m)) :
    (pullbackSnd η q : RealForm (n + m) (2 * m)) =
      (η (projSnd n m q)).compContinuousLinearMap (projSnd n m) := rfl

/-- `p₂^*η = π^m (topDensity ∘ η ∘ p₂) · dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²` in `Λ_m`. -/
theorem pullbackSnd_eq_smul (η : ComplexModel m → RealForm m (2 * m))
    (q : ComplexModel (n + m)) :
    pullbackSnd η q = (Real.pi ^ m * topDensity (η (projSnd n m q))) •
      (⟨basePower n m, basePower_mem_formSpan⟩ : formSpan (n + m) m) := by
  apply Subtype.ext
  rw [coe_pullbackSnd, pullbackSnd_eq]
  rfl

end Pullback

theorem isLocallyBoundedPshOn_sqCoord {N : ℕ} (j : Fin N) (U : Opens (ComplexModel N)) :
    IsLocallyBoundedPshOn U (sqCoord j) := by
  refine ⟨plurisubharmonicOn_of_levi_nonneg ((contDiff_sqCoord j).of_le
    (WithTop.coe_le_coe.mpr le_top)) U.isOpen fun x _ v => ?_, fun z hz => ?_⟩
  · rw [leviForm, realHessian_sqCoord, realHessian_sqCoord]
    have h1 := real_inner_self_nonneg (x := v j)
    have h2 := real_inner_self_nonneg (x := (Complex.I • v) j)
    positivity
  · obtain ⟨C, hC⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn
      (contDiff_sqCoord j).continuous.continuousOn
    refine ⟨U ⊓ ⟨Metric.ball z 1, Metric.isOpen_ball⟩, ⟨hz, Metric.mem_ball_self one_pos⟩,
      inf_le_left, C, fun w hw => ?_⟩
    simpa [Real.norm_eq_abs] using hC w (Metric.ball_subset_closedBall hw.2)

/-! ### The reduction of `p₂^*η ∧ M` to a top-degree Bedford–Taylor measure -/

section Bridge

open LocalBedfordTaylorSmoothTraceMeasure LocalBedfordTaylorCanonicalTraceMeasure
  BedfordTaylorTopDegree

/-- `BedfordTaylorTopDegree.btProduct_apply_wedgeProd_of_ddc` for an ambient dimension `N` with
`q + p = N`. -/
theorem btProduct_apply_wedgeProd_of_ddc' {N : ℕ} (p q : ℕ) (hN : q + p = N)
    {U : Opens (ComplexModel N)} (u : Fin p → ComplexModel N → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (β : Fin q → RealForm N 2)
    (ℓ : Fin q → ComplexModel N → ℝ) (hℓs : ∀ i, ContDiffOn ℝ ∞ (ℓ i) U)
    (hℓ : ∀ i, IsLocallyBoundedPshOn U (ℓ i)) (hddc : ∀ i, ∀ x ∈ U, smoothDDC (ℓ i) x = β i)
    (hP : wedgeProd q β ∈ formSpan N q) (φ : 𝓓(U, ℝ)) :
    btProduct p q u (oneCurrentOf (U := U) hN) ⟨wedgeProd q β, hP⟩ φ =
      ∫ x, φ x ∂recursiveMixedTraceMeasure U (fun i => Fin.append ℓ u (Fin.cast hN.symm i))
        (fun _ => isLocallyBoundedPshOn_append hℓ hu _) := by
  subst hN
  exact btProduct_apply_wedgeProd_of_ddc p q u hu β ℓ hℓs hℓ hddc hP φ

/-- The base slots `|z_k|²`, `k < m`, on `ℂⁿ⁺ᵐ`. -/
def baseSlots (n m : ℕ) : Fin m → ComplexModel (n + m) → ℝ := fun k => sqCoord (Fin.natAdd n k)

/-- The tuple `(u₁, …, uₙ, |z₁|², …, |z_m|²)`. -/
def fullTuple (u : Fin n → ComplexModel (n + m) → ℝ) : Fin (n + m) → ComplexModel (n + m) → ℝ :=
  Fin.append u (baseSlots n m)

theorem fullTuple_natAdd (u : Fin n → ComplexModel (n + m) → ℝ) (k : Fin m) :
    fullTuple u (Fin.natAdd n k) = baseNormSq n m k := by
  rw [fullTuple, Fin.append_right]
  rfl

theorem fibreTupleM_fullTuple (u : Fin n → ComplexModel (n + m) → ℝ) (z : ComplexModel m) :
    fibreTupleM (fullTuple u) z = fun i => fibreRestrictM (u i) z := by
  funext i
  rw [fibreTupleM, fullTuple, Fin.append_left]

/-- The Bedford–Taylor measure of `(u₁, …, uₙ, |z₁|², …, |z_m|²)`. -/
def fullMeasure {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) : Measure (ComplexModel (n + m)) :=
  recursiveMixedTraceMeasure Ω
    (fun i => Fin.append (baseSlots n m) u (Fin.cast (Nat.add_comm m n).symm i))
    (fun _ => isLocallyBoundedPshOn_append (fun _ => isLocallyBoundedPshOn_sqCoord _ Ω) hu _)

variable {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → ℝ}

theorem baseForm_eq_smoothDDC (k : Fin m) (x : ComplexModel (n + m)) :
    smoothDDC (baseSlots n m k) x = baseForm n m k :=
  smoothDDC_sqCoord _ x

/-- **`⟨M, φ dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²⟩ = ∫ φ dν`.** -/
theorem btProduct_apply_basePower (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) (φ : 𝓓(Ω, ℝ)) :
    btProduct n m u (oneCurrentOf (U := Ω) (Nat.add_comm m n))
        ⟨basePower n m, basePower_mem_formSpan⟩ φ = ∫ x, φ x ∂fullMeasure hu :=
  btProduct_apply_wedgeProd_of_ddc' n m (Nat.add_comm m n) u hu (baseForm n m) (baseSlots n m)
    (fun _ => (contDiff_sqCoord _).contDiffOn) (fun _ => isLocallyBoundedPshOn_sqCoord _ Ω)
    (fun k x _ => baseForm_eq_smoothDDC k x) basePower_mem_formSpan φ

/-- **The measure `ν` is the Bedford–Taylor limit of `(u₁, …, uₙ, |z₁|², …, |z_m|²)`.** -/
theorem isBTLimit_fullMeasure (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    IsBTLimit Ω (fullTuple u) (fullMeasure hu) := by
  have h := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
      (Ω := Ω) (u := fun i => Fin.append (baseSlots n m) u (Fin.cast (Nat.add_comm m n).symm i))
      (fun i => isLocallyBoundedPshOn_append (fun _ => isLocallyBoundedPshOn_sqCoord _ Ω) hu _))
  have hp := h.comp_perm (finAddFlip.trans (finCongr (Nat.add_comm m n)))
  have e : (fun i => Fin.append (baseSlots n m) u (Fin.cast (Nat.add_comm m n).symm
      ((finAddFlip.trans (finCongr (Nat.add_comm m n))) i))) = fullTuple u := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [fullTuple, Fin.append_left, Fin.append_right]
    · simp [fullTuple, Fin.append_left, Fin.append_right]
  rw [e] at hp
  exact hp

end Bridge

/-! ### The measure `p₂^*η ∧ M` -/

section Measure

variable {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → ℝ}

/-- **The Bedford–Taylor product** `M = dd^c u₁ ∧ ⋯ ∧ dd^c uₙ` on `Ω ⊆ ℂⁿ⁺ᵐ`, a current of
bidimension `(m,m)`. -/
def productBT (Ω : Opens (ComplexModel (n + m))) (u : Fin n → ComplexModel (n + m) → ℝ) :
    LocalProductCurrent (n + m) Ω m :=
  btProduct n m u (oneCurrentOf (U := Ω) (Nat.add_comm m n))

theorem isPositive_productBT (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    IsPositive (productBT Ω u) :=
  (isPositive_btProduct n m u _ (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1

/-- `dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²` as an element of `Λ_m`. -/
def basePowerSpan (n m : ℕ) : formSpan (n + m) m := ⟨basePower n m, basePower_mem_formSpan⟩

theorem basePowerSpan_mem_posCone : basePowerSpan n m ∈ posCone (n + m) m :=
  basePower_mem_spCone

/-- **`dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|² ∧ M = ν`**: the measure `L_q(dd^c|z|²^m) dσ_M(q)` is the
Bedford–Taylor measure of `(u₁, …, uₙ, |z₁|², …, |z_m|²)`, tested on every Borel `g`. -/
theorem integral_mul_densityForm_basePower (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i))
    (g : ComplexModel (n + m) → ℝ) :
    ∫ q, g q * densityForm (isPositive_productBT hu) q (basePowerSpan n m)
        ∂(isPositive_productBT hu).traceMeasure = ∫ q, g q ∂fullMeasure hu := by
  set hM := isPositive_productBT hu
  set σ := hM.traceMeasure
  set L : ComplexModel (n + m) → ℝ := fun q => densityForm hM q (basePowerSpan n m) with hLdef
  have hL0 : ∀ᵐ q ∂σ, 0 ≤ L q := by
    filter_upwards [ae_densityForm_nonneg hM] with q hq
    exact hq _ basePowerSpan_mem_posCone
  have hLm : Measurable L := measurable_densityForm hM _
  obtain ⟨CL, -, hCL⟩ := exists_abs_densityForm_le hM (basePowerSpan n m)
  set ρ := σ.withDensity fun q => ENNReal.ofReal (L q) with hρdef
  have hfm : Measurable fun q => ENNReal.ofReal (L q) := ENNReal.measurable_ofReal.comp hLm
  have hflt : ∀ᵐ q ∂σ, ENNReal.ofReal (L q) < ⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hρint (f : ComplexModel (n + m) → ℝ) : ∫ q, f q ∂ρ = ∫ q, f q * L q ∂σ := by
    rw [hρdef, integral_withDensity_eq_integral_toReal_smul hfm hflt]
    refine integral_congr_ae ?_
    filter_upwards [hL0] with q hq
    rw [ENNReal.toReal_ofReal hq, smul_eq_mul, mul_comm]
  have hν := isBTLimit_fullMeasure hu
  have hρν : ρ = fullMeasure hu := by
    apply LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := Ω)
    · exact withDensity_absolutelyContinuous _ _ hM.traceMeasure_compl
    · exact hν.1
    · intro K hK hKU
      rw [hρdef, withDensity_apply _ hK.measurableSet]
      calc ∫⁻ q in K, ENNReal.ofReal (L q) ∂σ ≤ ∫⁻ _ in K, ENNReal.ofReal CL ∂σ :=
            lintegral_mono fun q => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hCL q))
        _ = ENNReal.ofReal CL * σ K := by
            rw [setLIntegral_const]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hM.traceMeasure_lt_top hK hKU)
    · exact hν.2.1
    · intro φ
      rw [hρint, ← btProduct_apply_basePower hu φ]
      exact (apply_eq_integral_densityForm hM _ φ).symm
  rw [← hρν, hρint]

end Measure

/-! ### The product `Q × D` and the fibre products `M_z` -/

section Product

/-- `Q × D ⊆ ℂⁿ⁺ᵐ` (first `n` coordinates in `Q`, last `m` coordinates in `D`). -/
def prodOpens (Q : Opens (ComplexModel n)) (D : Opens (ComplexModel m)) :
    Opens (ComplexModel (n + m)) :=
  ⟨ProductMixedMeasure.projFst n m ⁻¹' Q ∩ ProductMixedMeasure.projSnd n m ⁻¹' D,
    (Q.isOpen.preimage (ProductMixedMeasure.projFst n m).continuous).inter
      (D.isOpen.preimage (ProductMixedMeasure.projSnd n m).continuous)⟩

theorem mem_prodOpens {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {q : ComplexModel (n + m)} :
    q ∈ prodOpens Q D ↔ ProductMixedMeasure.projFst n m q ∈ Q ∧
      ProductMixedMeasure.projSnd n m q ∈ D := Iff.rfl

theorem projFst_fibreMapM (z : ComplexModel m) (x : ComplexModel n) :
    ProductMixedMeasure.projFst n m (fibreMapM n m z x) = x := by
  simp [ProductMixedMeasure.projFst_apply, fibreMapM]

theorem projSnd_fibreMapM (z : ComplexModel m) (x : ComplexModel n) :
    ProductMixedMeasure.projSnd n m (fibreMapM n m z x) = z := by
  simp [ProductMixedMeasure.projSnd_apply, fibreMapM]

theorem fibreOpensM_prodOpens {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {z : ComplexModel m} (hz : z ∈ D) : fibreOpensM (prodOpens Q D) z = Q := by
  ext x
  simp only [SetLike.mem_coe, mem_fibreOpensM, mem_prodOpens, projFst_fibreMapM,
    projSnd_fibreMapM]
  exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩

/-- **The fibre product** `M_z = dd^c_x (u₁)_z ∧ ⋯ ∧ dd^c_x (uₙ)_z` on `Q`, of top degree. -/
def fibreBT (Q : Opens (ComplexModel n)) (u : Fin n → ComplexModel (n + m) → ℝ)
    (z : ComplexModel m) : LocalProductCurrent n Q 0 :=
  btProduct n 0 (fun i => fibreRestrictM (u i) z) (oneCurrentOf (U := Q) (Nat.zero_add n))

/-- The measure `M_z` (zero if `M_z` is not a positive current, which does not occur for
`z ∈ D`, `isPositive_fibreBT`). -/
def fibreMeasure (Q : Opens (ComplexModel n)) (u : Fin n → ComplexModel (n + m) → ℝ)
    (z : ComplexModel m) : Measure (ComplexModel n) :=
  by classical exact if h : IsPositive (fibreBT Q u z) then h.traceMeasure else 0

variable {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
  {u : Fin n → ComplexModel (n + m) → ℝ}

theorem isLocallyBoundedPshOn_fibre (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i))
    {z : ComplexModel m} (hz : z ∈ D) (i : Fin n) :
    IsLocallyBoundedPshOn Q (fibreRestrictM (u i) z) := by
  have h := IsLocallyBoundedPshOn.fibreM (hu i) z
  rwa [fibreOpensM_prodOpens hz] at h

theorem isPositive_fibreBT (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i))
    {z : ComplexModel m} (hz : z ∈ D) : IsPositive (fibreBT Q u z) :=
  (isPositive_btProduct n 0 _ _ (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (isLocallyBoundedPshOn_fibre hu hz)).1

open LocalBedfordTaylorSmoothTraceMeasure LocalBedfordTaylorCanonicalTraceMeasure in
theorem isBTLimit_fibreMeasure (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i))
    {z : ComplexModel m} (hz : z ∈ D) :
    IsBTLimit Q (fun i => fibreRestrictM (u i) z) (fibreMeasure Q u z) := by
  have e : fibreMeasure Q u z =
      recursiveMixedTraceMeasure Q _ (isLocallyBoundedPshOn_fibre hu hz) := by
    unfold fibreMeasure
    rw [dif_pos (isPositive_fibreBT hu hz)]
    rfl
  rw [e]
  exact BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure _)

end Product

/-! ### The lemma -/

section Main

variable {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
  {u : Fin n → ComplexModel (n + m) → ℝ}

/-- The fibre measures used for slicing: `M_z` for `z ∈ D`, and any Bedford–Taylor limit of the
(empty) fibre otherwise. -/
def slicingFamily (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i)) (z : ComplexModel m) :
    Measure (ComplexModel n) :=
  by classical exact if z ∈ D then fibreMeasure Q u z else
    Classical.choose (exists_isBTLimit_fibreM (isBTLimit_fullMeasure hu) z)

theorem isBTLimit_slicingFamily (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i))
    (z : ComplexModel m) :
    IsBTLimit (fibreOpensM (prodOpens Q D) z) (fibreTupleM (fullTuple u) z)
      (slicingFamily hu z) := by
  classical
  by_cases hz : z ∈ D
  · have e : slicingFamily hu z = fibreMeasure Q u z := by
      unfold slicingFamily
      rw [if_pos hz]
    rw [e, fibreOpensM_prodOpens hz, fibreTupleM_fullTuple]
    exact isBTLimit_fibreMeasure hu hz
  · have e : slicingFamily hu z =
        Classical.choose (exists_isBTLimit_fibreM (isBTLimit_fullMeasure hu) z) := by
      unfold slicingFamily
      rw [if_neg hz]
    rw [e]
    exact Classical.choose_spec (exists_isBTLimit_fibreM (isBTLimit_fullMeasure hu) z)

theorem slicingFamily_of_mem (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i))
    {z : ComplexModel m} (hz : z ∈ D) : slicingFamily hu z = fibreMeasure Q u z := by
  classical
  unfold slicingFamily
  rw [if_pos hz]

/-- **Fubini for Bedford–Taylor products along `Q × D`** (`lma:boundedfibrefubini`).

Let `Q ⊆ ℂⁿ`, `D ⊆ ℂᵐ` be open, `u₁, …, uₙ` locally bounded psh on `Q × D`,
`M = dd^c u₁ ∧ ⋯ ∧ dd^c uₙ` (`productBT`), `M_z = dd^c_x (u₁)_z ∧ ⋯ ∧ dd^c_x (uₙ)_z`
(`fibreBT`, with measure `fibreMeasure`), and `η` a smooth real `(m,m)`-form on `D`.  For every
bounded Borel `h` with compact support in `Q × D`,
`∫_{Q×D} h p₂^*η ∧ M = ∫_D (∫_Q h_z M_z) η(z)`.

The left-hand side is the integral of `h` against the top-degree current `p₂^*η ∧ M`, i.e. against
the signed measure `L_q(p₂^*η_q) dσ_M(q)` (`σ_M` the trace measure of `M`, `L_q` its density
form); the right-hand side integrates `z ↦ ∫ h_z dM_z` against `η` on `D` with the standard
orientation. -/
theorem boundedFibreFubini (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i))
    {η : ComplexModel m → RealForm m (2 * m)} (hη : ContDiffOn ℝ ∞ η D)
    {h : ComplexModel (n + m) → ℝ} (hhm : Measurable h) {C : ℝ} (hhb : ∀ q, |h q| ≤ C)
    (hhc : HasCompactSupport h) (hhΩ : tsupport h ⊆ prodOpens Q D) :
    ∫ q, h q * densityForm (isPositive_productBT hu) q (pullbackSnd η q)
        ∂(isPositive_productBT hu).traceMeasure =
      ∫ z in (D : Set (ComplexModel m)),
        (∫ x, h (fibreMapM n m z x) ∂fibreMeasure Q u z) * topDensity (η z) := by
  classical
  set Ω := prodOpens Q D with hΩdef
  set hM := isPositive_productBT hu
  set c : ComplexModel m → ℝ := fun z => topDensity (η z) with hcdef
  have hc : ContinuousOn c D := continuous_topDensity.comp_continuousOn hη.continuousOn
  set c' : ComplexModel m → ℝ := (D : Set (ComplexModel m)).piecewise c 0 with hc'def
  have hc'm : Measurable c' :=
    hc.measurable_piecewise continuousOn_const D.isOpen.measurableSet
  have hsupp (q : ComplexModel (n + m)) (hq : h q ≠ 0) : q ∈ tsupport h := subset_tsupport _ hq
  set g : ComplexModel (n + m) → ℝ := fun q => h q * c' (ProductMixedMeasure.projSnd n m q)
    with hgdef
  have hg_eq (q : ComplexModel (n + m)) : h q * c (ProductMixedMeasure.projSnd n m q) = g q := by
    by_cases hq : h q = 0
    · simp [hgdef, hq]
    · have hD : ProductMixedMeasure.projSnd n m q ∈ D := (hhΩ (hsupp q hq)).2
      simp only [hgdef, hc'def, Set.piecewise_eq_of_mem _ _ _ hD]
  have hgm : Measurable g := hhm.mul (hc'm.comp (ProductMixedMeasure.projSnd n m).measurable)
  -- step 1: reduction to `dd^c|z|²^m ∧ M`
  have hstep1 : ∫ q, h q * densityForm hM q (pullbackSnd η q) ∂hM.traceMeasure =
      Real.pi ^ m * ∫ q, g q * densityForm hM q (basePowerSpan n m) ∂hM.traceMeasure := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only
    rw [pullbackSnd_eq_smul, map_smul, smul_eq_mul, ← hg_eq]
    change h q * (Real.pi ^ m * c (ProductMixedMeasure.projSnd n m q) *
      densityForm hM q (basePowerSpan n m)) = _
    ring
  -- step 2: the Bedford–Taylor measure of `(u, |z|²)`
  rw [hstep1, integral_mul_densityForm_basePower hu g]
  -- step 3: slicing with a cutoff equal to one on the support of `h`
  have hC : 0 ≤ C := (abs_nonneg _).trans (hhb 0)
  obtain ⟨B, hB⟩ := (hhc.image (ProductMixedMeasure.projSnd n m).continuous).exists_bound_of_continuousOn
    (hc.mono fun z ⟨q, hq, hqz⟩ => hqz ▸ (hhΩ hq).2)
  have hgb (q : ComplexModel (n + m)) : ‖g q‖ ≤ C * max B 0 := by
    by_cases hq : h q = 0
    · simp only [hgdef, hq, zero_mul, norm_zero]
      exact mul_nonneg hC (le_max_right _ _)
    · rw [← hg_eq, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hhb q) ((hB _ ⟨q, hsupp q hq, rfl⟩).trans (le_max_left _ _))
        (norm_nonneg _) hC
  obtain ⟨U, hUo, hKU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure hhc Ω.isOpen hhΩ
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hhc
    hUo.isClosed_compl (disjoint_compl_right_iff_subset.2 hKU)
  have hχΩ : tsupport f ⊆ Ω := by
    refine (closure_mono fun q hq => ?_).trans hUΩ
    by_contra hqU
    exact hq (hf0 hqU)
  have hχg : (fun q => f q * g q) = g := by
    funext q
    by_cases hq : h q = 0
    · simp [hgdef, hq]
    · rw [hf1 (hsupp q hq), Pi.one_apply, one_mul]
  have hs := integral_mul_isBTLimit_eq_fibreIntegral (fullTuple_natAdd u)
    (isBTLimit_fullMeasure hu) (isBTLimit_slicingFamily hu) f.continuous hfc hχΩ
    (fun q => (hf01 q).1) hgm hgb
  rw [hχg] at hs
  rw [hs.2]
  -- step 4: the fibre integrals
  have hfib (z : ComplexModel m) : fibreIntegral (slicingFamily hu) g z =
      (D : Set (ComplexModel m)).indicator
        (fun z => (∫ x, h (fibreMapM n m z x) ∂fibreMeasure Q u z) * c z) z := by
    simp only [fibreIntegral, hgdef, projSnd_fibreMapM]
    by_cases hz : z ∈ D
    · rw [indicator_of_mem hz, slicingFamily_of_mem hu hz, hc'def,
        Set.piecewise_eq_of_mem _ _ _ hz, integral_mul_const]
    · rw [indicator_of_notMem hz, hc'def, Set.piecewise_eq_of_notMem _ _ _ hz]
      simp
  simp only [hfib]
  rw [integral_indicator D.isOpen.measurableSet]
  field_simp
  rfl

end Main

/-! ### `p₂^*η ∧ M` as a current -/

section Current

open LocalBedfordTaylorForms LocalBedfordTaylorSmooth ConstantFormProducts

variable {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
  {u : Fin n → ComplexModel (n + m) → ℝ}

/-- `topDensity` as a continuous linear map. -/
def topDensityCLM (N : ℕ) : RealForm N (2 * N) →L[ℝ] ℝ :=
  ContinuousAlternatingMap.apply ℝ (ComplexModel N) ℝ (topBasis N)

theorem topDensityCLM_apply {N : ℕ} (A : RealForm N (2 * N)) : topDensityCLM N A = topDensity A :=
  rfl

theorem contDiffOn_topDensity_comp {η : ComplexModel m → RealForm m (2 * m)}
    (hη : ContDiffOn ℝ ∞ η D) :
    ContDiffOn ℝ ∞ (fun q => Real.pi ^ m * topDensity (η (ProductMixedMeasure.projSnd n m q)))
      (prodOpens Q D : Set (ComplexModel (n + m))) :=
  contDiffOn_const.mul ((topDensityCLM m).contDiff.comp_contDiffOn
    (hη.comp (ProductMixedMeasure.projSnd n m).contDiff.contDiffOn fun _ hq => hq.2))

/-- The pull-back `p₂^*η` is smooth on `Q × D`. -/
theorem contDiffOn_pullbackSnd {η : ComplexModel m → RealForm m (2 * m)}
    (hη : ContDiffOn ℝ ∞ η D) :
    ContDiffOn ℝ ∞ (fun q => (pullbackSnd η q : RealForm (n + m) (2 * m)))
      (prodOpens Q D : Set (ComplexModel (n + m))) := by
  have e : (fun q => (pullbackSnd η q : RealForm (n + m) (2 * m))) =
      fun q => (Real.pi ^ m * topDensity (η (ProductMixedMeasure.projSnd n m q))) •
        basePower n m := by
    funext q
    rw [coe_pullbackSnd, pullbackSnd_eq]
  rw [e]
  exact (contDiffOn_topDensity_comp hη).smul contDiffOn_const

/-- **The integrand of `boundedFibreFubini` is the current `M ∧ p₂^*η`**: on test functions,
TN's current `M ∧ p₂^*η` (`LocalBedfordTaylorForms.wedgeForm`, top degree) is integration against
the signed measure `L_q(p₂^*η_q) dσ_M(q)`. -/
theorem wedgeForm_pullbackSnd_apply (hu : ∀ i, IsLocallyBoundedPshOn (prodOpens Q D) (u i))
    {η : ComplexModel m → RealForm m (2 * m)} (hη : ContDiffOn ℝ ∞ η D)
    (φ : 𝓓(prodOpens Q D, ℝ)) :
    wedgeForm (Nat.zero_add m) (productBT (prodOpens Q D) u) (contDiffOn_pullbackSnd hη)
        (kahlerPower (n + m) 0) φ =
      ∫ q, φ q * densityForm (isPositive_productBT hu) q (pullbackSnd η q)
        ∂(isPositive_productBT hu).traceMeasure := by
  set hM := isPositive_productBT hu
  have hrep : ∀ q ∈ prodOpens Q D, (pullbackSnd η q : RealForm (n + m) (2 * m)) =
      ∑ j : Unit, (fun _ q => Real.pi ^ m * topDensity (η (ProductMixedMeasure.projSnd n m q))) j q •
        ((fun _ => basePowerSpan n m) j : RealForm (n + m) (2 * m)) := by
    intro q _
    simp only [Finset.univ_unique, Finset.sum_singleton, coe_pullbackSnd, pullbackSnd_eq]
    rfl
  rw [wedgeForm_apply_eq (Nat.zero_add m) _ _ (fun q _ => (pullbackSnd η q).2) _
    (fun _ => contDiffOn_topDensity_comp hη) _ hrep]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have eγ : wedgeSpan (n + m) (Nat.zero_add m) (kahlerPower (n + m) 0) (basePowerSpan n m) =
      basePowerSpan n m := by
    apply Subtype.ext
    rw [coe_wedgeSpan_apply (Nat.zero_add m) _ _ (by omega)]
    change wedgeTo (by omega : 0 + 2 * m = 2 * m) (coordinateWedgeUnit : RealForm (n + m) 0)
      (basePower n m) = _
    rw [wedgeTo_unit_left _ rfl]
    rfl
  rw [eγ, apply_eq_integral_densityForm hM]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [mulSmoothOnCLM_apply]
  rw [pullbackSnd_eq_smul, map_smul, smul_eq_mul, mul_assoc]
  rfl

end Current

end SGPT.NPP.FibreSlicing
