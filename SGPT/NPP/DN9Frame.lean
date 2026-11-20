import SGPT.NPP.DN5Frame

/-!
# Normalizing frames that are holomorphic to first order at a centre

Lane DN9 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 3: unitary coordinates of
`T_x X` chosen holomorphically to first order at the centre, step (W) of the hand-off).

Let `T(z) = hermOp (α z)` be the Hermitian operator of a smooth Kähler coefficient and `S₁` any
fixed operator.  For a centre `z₀` put

* `L₀(z₀, z) = S₁ - T(z₀)⁻¹ ∂T(z₀)(z - z₀) S₁`, `∂T(v) = ½(DT v - i DT(iv))` the `(1,0)`-part
  of the derivative (`holPart`; complex linear in `v`);
* `M(z₀, z) = L₀† T(z) L₀` (`frameM`);  its derivative in `z` vanishes at `z = z₀`
  (`hasFDerivAt_frameM`), because `(∂T v)† = ∂̄T v` for Hermitian `T`;
* `Λ(z₀, z) = L₀ (1 + G(M))` (`frame`), `G` the solution of `(1 + X)† M (1 + X) = 1` given by the
  implicit function theorem near `M = 1` (`exists_frameCorrection`).

Then `Λ(z₀, z)† T(z) Λ(z₀, z) = 1` exactly (`frame_normalizing`), `Λ` is smooth in `(z₀, z)` near
any `(z₁, z₁)` with `S₁† T(z₁) S₁ = 1` (`contDiffOn_frame`), and the derivative of
`z ↦ Λ(z₀, z)` at `z₀` is complex linear (`fderiv_frame_I`): this is the centre condition of
`SGPT.NPP.DN4.CenterData`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff RightActions

namespace SGPT.NPP.DN9

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NPP.DN5

variable {N : ℕ}

/-- Complex linear operators on `ℂⁿ`. -/
abbrev Op (N : ℕ) := ComplexModel N →L[ℂ] ComplexModel N

/-! ### Invertibility in finite dimension -/

/-- A left invertible operator on `ℂⁿ` is a unit. -/
theorem isUnit_of_mul_eq_one {A B : Op N} (h : B * A = 1) : IsUnit A := by
  have hinj : Function.Injective (A : ComplexModel N →ₗ[ℂ] ComplexModel N) := by
    intro x y hxy
    have hx : B (A x) = x := by
      have := congrArg (fun T : Op N => T x) h
      simpa using this
    have hy : B (A y) = y := by
      have := congrArg (fun T : Op N => T y) h
      simpa using this
    have hxy' : A x = A y := hxy
    rw [← hx, ← hy, hxy']
  set e := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv
  have he : ∀ x, e x = A x := fun x => rfl
  refine ⟨⟨A, (e.symm : Op N), ?_, ?_⟩, rfl⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    change A (e.symm x) = x
    rw [← he, ContinuousLinearEquiv.apply_symm_apply]
  · refine ContinuousLinearMap.ext fun x => ?_
    change e.symm (A x) = x
    rw [← he, ContinuousLinearEquiv.symm_apply_apply]

/-- A unit is an invertible continuous linear map. -/
theorem isInvertible_of_isUnit {A : Op N} (h : IsUnit A) : A.IsInvertible := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℂ (ComplexModel N) u,
    ContinuousLinearMap.ext fun x => ContinuousLinearEquiv.unitsEquiv_apply ℂ _ u x⟩

/-! ### The frame correction `G` -/

/-- The map `(M, X) ↦ (1 + X)† M (1 + X) - 1 + (X - X†)`. -/
def corrMap (p : Op N × Op N) : Op N :=
  star (1 + p.2) * p.1 * (1 + p.2) - 1 + (p.2 - star p.2)

theorem contDiff_corrMap : ContDiff ℝ ∞ (corrMap (N := N)) := by
  have hstar := contDiff_star_op (N := N)
  have h1 : ContDiff ℝ ∞ (fun p : Op N × Op N => (1 : Op N) + p.2) :=
    contDiff_const.add contDiff_snd
  exact ((((hstar.comp h1).mul contDiff_fst).mul h1).sub contDiff_const).add
    (contDiff_snd.sub (hstar.comp contDiff_snd))

/-- **The frame correction** (implicit function theorem at `(1, 0)`): a smooth `G` near `1` with
`G 1 = 0` and `(1 + G M)† M (1 + G M) = 1` for self-adjoint `M`. -/
theorem exists_frameCorrection :
    ∃ 𝒱 : Set (Op N), IsOpen 𝒱 ∧ (1 : Op N) ∈ 𝒱 ∧ ∃ G : Op N → Op N, ContDiffOn ℝ ∞ G 𝒱 ∧
      G 1 = 0 ∧ ∀ M ∈ 𝒱, star M = M → star (1 + G M) * M * (1 + G M) = 1 := by
  have hs1 : star (1 + 0 : Op N) = 1 := by rw [add_zero]; exact star_one _
  have hs0 : star (0 : Op N) = 0 := star_zero (Op N)
  have hslice : HasFDerivAt (fun X : Op N => corrMap ((1 : Op N), X))
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (Op N)) 0 := by
    have hfun : (fun X : Op N => corrMap ((1 : Op N), X)) =
        fun X => star (1 + X) * (1 + X) - 1 + (X - star X) := by
      funext X
      change star (1 + X) * 1 * (1 + X) - 1 + (X - star X) = _
      rw [mul_one]
    rw [hfun]
    set Ls := (isBoundedLinearMap_star (N := N)).toContinuousLinearMap
    have hs : HasFDerivAt (fun X : Op N => star X) Ls 0 :=
      isBoundedLinearMap_star.hasFDerivAt
    have h1 : HasFDerivAt (fun X : Op N => 1 + X) (ContinuousLinearMap.id ℝ _) 0 :=
      (hasFDerivAt_id _).const_add _
    have h2 : HasFDerivAt (fun X : Op N => star (1 + X)) Ls 0 := by
      have h := (isBoundedLinearMap_star (N := N)).hasFDerivAt (x := 1 + 0)
      have h' := h.comp (0 : Op N) h1
      rw [ContinuousLinearMap.comp_id] at h'
      exact h'
    have hq := h2.mul' h1
    have hlin : HasFDerivAt (fun X : Op N => X - star X) (ContinuousLinearMap.id ℝ _ - Ls) 0 :=
      (hasFDerivAt_id _).sub hs
    have htot := (hq.sub_const 1).add hlin
    refine htot.congr_fderiv (ContinuousLinearMap.ext fun Y => ?_)
    change star (1 + 0) * Y + star Y * (1 + 0) + (Y - star Y) = (2 : ℝ) • Y
    rw [hs1, add_zero, one_mul, mul_one]
    have h2Y : (2 : ℝ) • Y = Y + Y := two_smul ℝ Y
    rw [h2Y]
    abel
  have hinv : ((fderiv ℝ (corrMap (N := N)) ((1 : Op N), 0)).comp
      (ContinuousLinearMap.inr ℝ (Op N) (Op N))).IsInvertible := by
    have hfd : DifferentiableAt ℝ (corrMap (N := N)) ((1 : Op N), 0) :=
      (contDiff_corrMap (N := N)).differentiable (by simp) _
    have hcomp : HasFDerivAt (fun X : Op N => corrMap ((1 : Op N), X))
        ((fderiv ℝ (corrMap (N := N)) ((1 : Op N), 0)).comp (ContinuousLinearMap.inr ℝ _ _)) 0 :=
      hfd.hasFDerivAt.comp 0 ((hasFDerivAt_const (1 : Op N) 0).prodMk (hasFDerivAt_id 0))
    rw [hcomp.unique hslice]
    refine ⟨ContinuousLinearEquiv.equivOfInverse ((2 : ℝ) • ContinuousLinearMap.id ℝ (Op N))
      ((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ (Op N)) ?_ ?_, rfl⟩
    · intro X; simp [smul_smul]
    · intro X; simp [smul_smul]
  obtain ⟨U, hU, h1U, ψ, hψ, hψ1, hψf⟩ :=
    exists_smooth_implicit isOpen_univ (contDiff_corrMap (N := N)).contDiffOn
      (mem_univ ((1 : Op N), (0 : Op N))) hinv
  have hf0 : corrMap ((1 : Op N), (0 : Op N)) = 0 := by
    change star (1 + 0) * 1 * (1 + 0) - 1 + (0 - star 0) = (0 : Op N)
    rw [hs1, hs0]
    simp
  refine ⟨U, hU, h1U, ψ, hψ, hψ1, fun M hM hMsa => ?_⟩
  have hfz := (hψf M hM).2
  rw [hf0] at hfz
  set X := ψ M
  set R := star (1 + X) * M * (1 + X) - 1
  have hRsa : star R = R := star_conj_sub_one hMsa (1 + X)
  have hR : R = -(X - star X) := eq_neg_of_add_eq_zero_left hfz
  have hRR : R + R = 0 := self_add_self_of_sa_eq_neg_skew hRsa (star_sub_star_self X) hR
  have hR0 : R = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    have h := congrArg (fun T : Op N => T w) hRR
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply] at h
    have h2 : (2 : ℂ) • R w = 0 := by rw [two_smul]; exact h
    rw [ContinuousLinearMap.zero_apply]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  exact sub_eq_zero.mp hR0

/-! ### The `(1,0)`-part of a derivative -/

/-- `∂T(v) = ½ (DT v - i DT(i v))`. -/
def holPart (D : ComplexModel N →L[ℝ] Op N) : ComplexModel N →L[ℝ] Op N :=
  (2 : ℂ)⁻¹ • (D - Complex.I • D.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))

theorem holPart_apply (D : ComplexModel N →L[ℝ] Op N) (v : ComplexModel N) :
    holPart D v = (2 : ℂ)⁻¹ • (D v - Complex.I • D (Complex.I • v)) := by
  simp [holPart]

theorem half_sub_I_smul_I {R : Type*} [AddCommGroup R] [Module ℂ R] (x y : R) :
    (2 : ℂ)⁻¹ • (y - Complex.I • -x) = Complex.I • ((2 : ℂ)⁻¹ • (x - Complex.I • y)) := by
  rw [smul_neg, sub_neg_eq_add, smul_comm, smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul,
    sub_neg_eq_add, add_comm]

theorem holPart_I (D : ComplexModel N →L[ℝ] Op N) (v : ComplexModel N) :
    holPart D (Complex.I • v) = Complex.I • holPart D v := by
  have hII : Complex.I • Complex.I • v = -v := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hD : D (Complex.I • Complex.I • v) = -D v := by rw [hII, map_neg]
  rw [holPart_apply, holPart_apply, hD]
  exact half_sub_I_smul_I (R := Op N) (D v) (D (Complex.I • v))

/-- `(½ (a - i b))† + ½ (a - i b) = a` for self-adjoint `a`, `b`. -/
theorem star_half_sub_I_smul_add {R : Type*} [AddCommGroup R] [Module ℂ R] [StarAddMonoid R]
    [StarModule ℂ R] (a b : R) (ha : star a = a) (hb : star b = b) :
    star ((2 : ℂ)⁻¹ • (a - Complex.I • b)) + (2 : ℂ)⁻¹ • (a - Complex.I • b) = a := by
  rw [star_smul, star_sub, star_smul, ha, hb]
  have h2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [Complex.star_def, map_inv₀, map_ofNat]
  have hI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [h2, hI]
  module

/-- For a derivative with self-adjoint values, `(∂T v)† + ∂T v = DT v`. -/
theorem star_holPart_add {D : ComplexModel N →L[ℝ] Op N} (hD : ∀ v, star (D v) = D v)
    (v : ComplexModel N) : star (holPart D v) + holPart D v = D v := by
  rw [holPart_apply]
  exact star_half_sub_I_smul_add (R := Op N) _ _ (hD v) (hD _)

/-! ### The frame -/

variable (G : Op N → Op N) (S₁ : Op N) (T : ComplexModel N → Op N)

/-- `L₀(z₀, z) = S₁ - T(z₀)⁻¹ ∂T(z₀)(z - z₀) S₁`. -/
def frameL0 (z₀ z : ComplexModel N) : Op N :=
  S₁ - Ring.inverse (T z₀) * holPart (fderiv ℝ T z₀) (z - z₀) * S₁

/-- `M(z₀, z) = L₀† T(z) L₀`. -/
def frameM (z₀ z : ComplexModel N) : Op N :=
  star (frameL0 S₁ T z₀ z) * T z * frameL0 S₁ T z₀ z

/-- **The frame** `Λ(z₀, z) = L₀ (1 + G(M))`. -/
def frame (z₀ z : ComplexModel N) : Op N :=
  frameL0 S₁ T z₀ z * (1 + G (frameM S₁ T z₀ z))

theorem frameL0_self (z₀ : ComplexModel N) : frameL0 S₁ T z₀ z₀ = S₁ := by
  simp [frameL0]

theorem frameM_self (z₀ : ComplexModel N) : frameM S₁ T z₀ z₀ = star S₁ * T z₀ * S₁ := by
  simp [frameM, frameL0_self]

/-- `D_z L₀(z₀, ·) = -T(z₀)⁻¹ ∂T(z₀)(·) S₁`. -/
theorem hasFDerivAt_frameL0 (z₀ z : ComplexModel N) :
    ∃ L' : ComplexModel N →L[ℝ] Op N, HasFDerivAt (frameL0 S₁ T z₀) L' z ∧
      ∀ v, L' v = -(Ring.inverse (T z₀) * holPart (fderiv ℝ T z₀) v * S₁) := by
  have h1 : HasFDerivAt (fun z => holPart (fderiv ℝ T z₀) (z - z₀)) (holPart (fderiv ℝ T z₀)) z := by
    have := ((holPart (fderiv ℝ T z₀)).hasFDerivAt (x := z)).sub_const (holPart (fderiv ℝ T z₀) z₀)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only [map_sub]
  have h2 := ((h1.const_mul (Ring.inverse (T z₀))).mul_const' S₁).const_sub S₁
  exact ⟨_, h2, fun v => by simp⟩

section Generic

variable {R : Type*} [Ring R] [StarRing R]

/-- The ring identity behind `hasFDerivAt_frameM`. -/
theorem frameM_deriv_alg (S Ti T₀ h D : R) (hTi : star Ti = Ti) (hc1 : Ti * T₀ = 1)
    (hc2 : T₀ * Ti = 1) (hk : star h + h = D) :
    star S * T₀ * (-(Ti * h * S)) + (star S * D + star (-(Ti * h * S)) * T₀) * S = 0 := by
  have e1 : star S * T₀ * (-(Ti * h * S)) = -(star S * h * S) := by
    rw [mul_neg]
    congr 1
    calc star S * T₀ * (Ti * h * S) = star S * (T₀ * Ti) * h * S := by simp only [mul_assoc]
      _ = star S * h * S := by rw [hc2, mul_one]
  have hs : star (Ti * h * S) = star S * star h * Ti := by
    simp only [star_mul, hTi, mul_assoc]
  have e2 : star (-(Ti * h * S)) * T₀ * S = -(star S * star h * S) := by
    rw [star_neg, hs, neg_mul, neg_mul]
    congr 1
    calc star S * star h * Ti * T₀ * S = star S * star h * (Ti * T₀) * S := by
          simp only [mul_assoc]
      _ = star S * star h * S := by rw [hc1, mul_one]
  rw [add_mul, e1, e2, ← hk]
  noncomm_ring

end Generic

/-- The derivative of a map with self-adjoint values has self-adjoint values. -/
theorem star_fderiv_of_selfAdjoint {z₀ : ComplexModel N} (hT : DifferentiableAt ℝ T z₀)
    (hsa : ∀ᶠ z in 𝓝 z₀, star (T z) = T z) (v : ComplexModel N) :
    star (fderiv ℝ T z₀ v) = fderiv ℝ T z₀ v := by
  set Ls := (isBoundedLinearMap_star (N := N)).toContinuousLinearMap
  have h1 : HasFDerivAt (fun z => star (T z)) (Ls.comp (fderiv ℝ T z₀)) z₀ :=
    Ls.hasFDerivAt.comp z₀ hT.hasFDerivAt
  have h2 : HasFDerivAt (fun z => star (T z)) (fderiv ℝ T z₀) z₀ :=
    hT.hasFDerivAt.congr_of_eventuallyEq (hsa.mono fun z hz => hz)
  have := congrArg (fun L : ComplexModel N →L[ℝ] Op N => L v) (h1.unique h2)
  exact this

/-- **`D_z M(z₀, ·)(z₀) = 0`** for self-adjoint `T` invertible at `z₀`. -/
theorem hasFDerivAt_frameM {z₀ : ComplexModel N} (hT : DifferentiableAt ℝ T z₀)
    (hsa : ∀ᶠ z in 𝓝 z₀, star (T z) = T z) (hu : IsUnit (T z₀)) :
    HasFDerivAt (frameM S₁ T z₀) (0 : ComplexModel N →L[ℝ] Op N) z₀ := by
  set Ls := (isBoundedLinearMap_star (N := N)).toContinuousLinearMap
  obtain ⟨L', hL, hL'⟩ := hasFDerivAt_frameL0 S₁ T z₀ z₀
  have hLs : HasFDerivAt (fun z => star (frameL0 S₁ T z₀ z)) (Ls.comp L') z₀ :=
    Ls.hasFDerivAt.comp z₀ hL
  have hT' : HasFDerivAt T (fderiv ℝ T z₀) z₀ := hT.hasFDerivAt
  have h := (hLs.mul' hT').mul' hL
  have hfun : frameM S₁ T z₀ = (fun z => star (frameL0 S₁ T z₀ z)) * T * frameL0 S₁ T z₀ := by
    funext z; rfl
  rw [hfun]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have hsa0 : star (T z₀) = T z₀ := hsa.self_of_nhds
  have hTi : star (Ring.inverse (T z₀)) = Ring.inverse (T z₀) := by
    rw [← Ring.inverse_star, hsa0]
  have hc1 : Ring.inverse (T z₀) * T z₀ = 1 := Ring.inverse_mul_cancel _ hu
  have hc2 : T z₀ * Ring.inverse (T z₀) = 1 := Ring.mul_inverse_cancel _ hu
  have hkey := star_holPart_add (star_fderiv_of_selfAdjoint T hT hsa) v
  have hLsv : ∀ X : Op N, Ls X = star X := fun X => rfl
  have hval : ((fun z => star (frameL0 S₁ T z₀ z)) * T) z₀ = star S₁ * T z₀ := by
    simp [frameL0_self]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hval, hL', hLsv,
    frameL0_self]
  simp only [smul_eq_mul, op_smul_eq_mul]
  exact frameM_deriv_alg (R := Op N) S₁ _ _ _ _ hTi hc1 hc2 hkey

/-- `-(a (i h) b) c = i (-(a h b) c)` in a complex algebra. -/
theorem neg_mul_I_smul_alg {R : Type*} [Ring R] [Algebra ℂ R] (a h b c : R) :
    -(a * (Complex.I • h) * b) * c = Complex.I • (-(a * h * b) * c) := by
  simp only [mul_smul_comm, smul_mul_assoc, smul_neg, neg_mul]

/-- The derivative of the frame at the centre: `D_z Λ(z₀, ·)(z₀) v = -T(z₀)⁻¹ ∂T(v) S₁ (1 + G M₀)`. -/
theorem hasFDerivAt_frame_center {z₀ : ComplexModel N} (hT : DifferentiableAt ℝ T z₀)
    (hsa : ∀ᶠ z in 𝓝 z₀, star (T z) = T z) (hu : IsUnit (T z₀))
    (hG : DifferentiableAt ℝ G (frameM S₁ T z₀ z₀)) :
    ∃ L' : ComplexModel N →L[ℝ] Op N, HasFDerivAt (frame G S₁ T z₀) L' z₀ ∧
      ∀ v, L' v = -(Ring.inverse (T z₀) * holPart (fderiv ℝ T z₀) v * S₁) *
        (1 + G (frameM S₁ T z₀ z₀)) := by
  obtain ⟨L', hL, hL'⟩ := hasFDerivAt_frameL0 S₁ T z₀ z₀
  have hM := hasFDerivAt_frameM S₁ T hT hsa hu
  have hY : HasFDerivAt (fun z => 1 + G (frameM S₁ T z₀ z))
      ((fderiv ℝ G (frameM S₁ T z₀ z₀)).comp (0 : ComplexModel N →L[ℝ] Op N)) z₀ :=
    (hG.hasFDerivAt.comp z₀ hM).const_add 1
  have h := hL.mul' hY
  have hfun : frame G S₁ T z₀ = frameL0 S₁ T z₀ * fun z => 1 + G (frameM S₁ T z₀ z) := by
    funext z; rfl
  refine ⟨_, hfun ▸ h, fun v => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_apply, smul_eq_mul, mul_zero,
    zero_add, op_smul_eq_mul, hL']

/-- **The centre condition**: the derivative of `z ↦ Λ(z₀, z)` at `z₀` is complex linear. -/
theorem fderiv_frame_I {z₀ : ComplexModel N} (hT : DifferentiableAt ℝ T z₀)
    (hsa : ∀ᶠ z in 𝓝 z₀, star (T z) = T z) (hu : IsUnit (T z₀))
    (hG : DifferentiableAt ℝ G (frameM S₁ T z₀ z₀)) (v : ComplexModel N) :
    fderiv ℝ (frame G S₁ T z₀) z₀ (Complex.I • v) =
      Complex.I • fderiv ℝ (frame G S₁ T z₀) z₀ v := by
  obtain ⟨L', hL, hL'⟩ := hasFDerivAt_frame_center G S₁ T hT hsa hu hG
  rw [hL.fderiv, hL', hL', holPart_I]
  exact neg_mul_I_smul_alg (R := Op N) _ _ _ _

/-- `M` is self-adjoint when `T(z)` is. -/
theorem star_frameM {z₀ z : ComplexModel N} (hTz : star (T z) = T z) :
    star (frameM S₁ T z₀ z) = frameM S₁ T z₀ z := by
  unfold frameM
  rw [star_mul, star_mul, star_star, hTz, mul_assoc]

/-- **Normalization**: `Λ(z₀, z)† T(z) Λ(z₀, z) = 1`. -/
theorem frame_normalizing {𝒱 : Set (Op N)}
    (hGn : ∀ M ∈ 𝒱, star M = M → star (1 + G M) * M * (1 + G M) = 1) {z₀ z : ComplexModel N}
    (hM : frameM S₁ T z₀ z ∈ 𝒱) (hTz : star (T z) = T z) :
    star (frame G S₁ T z₀ z) * T z * frame G S₁ T z₀ z = 1 := by
  unfold frame
  rw [star_conj_mul]
  exact hGn _ hM (star_frameM S₁ T hTz)

/-! ### Smoothness of the frame in `(z₀, z)` -/

/-- Pairs `(z₀, z)` of points of `U` with `T(z₀)` invertible. -/
def frameBase (T : ComplexModel N → Op N) (U : Set (ComplexModel N)) :
    Set (ComplexModel N × ComplexModel N) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ IsUnit (T p.1)}

/-- The domain of the frame: `M(z₀, z) ∈ 𝒱` in addition. -/
def frameDom (𝒱 : Set (Op N)) (U : Set (ComplexModel N)) : Set (ComplexModel N × ComplexModel N) :=
  frameBase T U ∩ (fun p => frameM S₁ T p.1 p.2) ⁻¹' 𝒱

variable {S₁ T}

theorem isOpen_frameBase {U : Set (ComplexModel N)} (hU : IsOpen U) (hT : ContDiffOn ℝ ∞ T U) :
    IsOpen (frameBase T U) := by
  have h1 : IsOpen (U ∩ T ⁻¹' {x : Op N | IsUnit x}) :=
    hT.continuousOn.isOpen_inter_preimage hU Units.isOpen
  have h2 : IsOpen ((Prod.fst ⁻¹' (U ∩ T ⁻¹' {x : Op N | IsUnit x})) ∩
      (Prod.snd ⁻¹' U) : Set (ComplexModel N × ComplexModel N)) :=
    (h1.preimage continuous_fst).inter (hU.preimage continuous_snd)
  convert h2 using 1
  ext p
  simp only [frameBase, mem_setOf_eq, mem_inter_iff, mem_preimage]
  tauto

theorem contDiffOn_frameL0 {U : Set (ComplexModel N)} (hU : IsOpen U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => frameL0 S₁ T p.1 p.2)
      (frameBase T U) := by
  have hD : ContDiffOn ℝ ∞ (fun z => fderiv ℝ T z) U := hT.fderiv_of_isOpen hU (by simp)
  have hDp : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => fderiv ℝ T p.1)
      (frameBase T U) := hD.comp contDiffOn_fst fun p hp => hp.1
  have hv : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => p.2 - p.1)
      (frameBase T U) := contDiffOn_snd.sub contDiffOn_fst
  have hIv : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N =>
      Complex.I • (p.2 - p.1)) (frameBase T U) := hv.const_smul Complex.I
  have hh : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N =>
      holPart (fderiv ℝ T p.1) (p.2 - p.1)) (frameBase T U) := by
    have e : (fun p : ComplexModel N × ComplexModel N => holPart (fderiv ℝ T p.1) (p.2 - p.1)) =
        fun p => (2 : ℂ)⁻¹ • (fderiv ℝ T p.1 (p.2 - p.1) -
          Complex.I • fderiv ℝ T p.1 (Complex.I • (p.2 - p.1))) :=
      funext fun p => holPart_apply _ _
    rw [e]
    exact ((hDp.clm_apply hv).sub ((hDp.clm_apply hIv).const_smul Complex.I)).const_smul _
  have hTi : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => Ring.inverse (T p.1))
      (frameBase T U) := by
    intro p hp
    have h1 : ContDiffAt ℝ ∞ Ring.inverse (T p.1) := by
      have := contDiffAt_ringInverse ℝ (n := ∞) hp.2.2.unit
      rwa [IsUnit.unit_spec] at this
    have h2 : ContDiffAt ℝ ∞ (fun p : ComplexModel N × ComplexModel N => T p.1) p :=
      (hT.contDiffAt (hU.mem_nhds hp.1)).comp p contDiffAt_fst
    exact (h1.comp p h2).contDiffWithinAt
  exact contDiffOn_const.sub ((hTi.mul hh).mul contDiffOn_const)

theorem contDiffOn_frameM {U : Set (ComplexModel N)} (hU : IsOpen U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => frameM S₁ T p.1 p.2)
      (frameBase T U) := by
  have hL := contDiffOn_frameL0 (S₁ := S₁) hU hT
  have hTp : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => T p.2)
      (frameBase T U) := hT.comp contDiffOn_snd fun p hp => hp.2.1
  exact ((contDiff_star_op.comp_contDiffOn hL).mul hTp).mul hL

theorem isOpen_frameDom {𝒱 : Set (Op N)} (h𝒱 : IsOpen 𝒱) {U : Set (ComplexModel N)}
    (hU : IsOpen U) (hT : ContDiffOn ℝ ∞ T U) : IsOpen (frameDom S₁ T 𝒱 U) :=
  (contDiffOn_frameM (S₁ := S₁) hU hT).continuousOn.isOpen_inter_preimage
    (isOpen_frameBase hU hT) h𝒱

/-- **Smoothness of the frame** `(z₀, z) ↦ Λ(z₀, z)` on its domain. -/
theorem contDiffOn_frame {𝒱 : Set (Op N)} (hG : ContDiffOn ℝ ∞ G 𝒱) {U : Set (ComplexModel N)}
    (hU : IsOpen U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => frame G S₁ T p.1 p.2)
      (frameDom S₁ T 𝒱 U) := by
  have hL := (contDiffOn_frameL0 (S₁ := S₁) hU hT).mono
    (inter_subset_left : frameDom S₁ T 𝒱 U ⊆ frameBase T U)
  have hM := (contDiffOn_frameM (S₁ := S₁) hU hT).mono
    (inter_subset_left : frameDom S₁ T 𝒱 U ⊆ frameBase T U)
  have hGM : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => G (frameM S₁ T p.1 p.2))
      (frameDom S₁ T 𝒱 U) := hG.comp hM fun p hp => hp.2
  exact hL.mul (contDiffOn_const.add hGM)

end SGPT.NPP.DN9
