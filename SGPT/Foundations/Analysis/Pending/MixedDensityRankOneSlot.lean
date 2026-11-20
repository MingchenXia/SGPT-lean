import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
import SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
import SGPT.Foundations.Analysis.LeviForm

set_option autoImplicit false

/-!
# Mixed densities with one slot `|τ|²`: the smooth slicing identity

Toward Xia, SGPT, proof of Proposition 4.3.3, Step 1 (`xia-sgpt:page-0171`, (2.11) and
Proposition 2.2.1 (6)): on `ℂⁿ⁺¹ = ℂⁿ × ℂ` (`FiniteGeodesicMaximality.stripModelEquiv`), the mixed
Monge--Ampère density of `n` functions `F₁, …, Fₙ` together with `|τ|²` (the squared modulus of
the last coordinate) is `1/π` times the mixed density, on the fibre `ℂⁿ × {τ}`, of the restrictions
`Fᵢ(·, τ)`. In terms of currents: `ddᶜF₁ ∧ ⋯ ∧ ddᶜFₙ ∧ ddᶜ|τ|²` is the fibre measure
`ddᶜ_x F₁ ∧ ⋯ ∧ ddᶜ_x Fₙ` integrated against Lebesgue measure in `τ`.

* `mixedCoefficient_eq_of_last_eq_lastUnit` — **linear algebra**: if the last slot is the
  rank-one matrix `E = e_last e_lastᵀ` (`lastUnit`), the mixed coefficient is the mixed coefficient
  of the top-left `n × n` blocks of the other slots. Only permutations fixing the last row
  contribute, and the Laplace expansion along that row leaves the minor.
* `complexHessian_lastNormSq` — the complex Hessian of `|τ|²` is `E`.
* `complexHessian_fibre` — the top-left block of the complex Hessian of `F` at `(y, τ)` is the
  complex Hessian of `y ↦ F(y, τ)`.
* `mixedDensity_eq_fibre_div_pi` — the slicing identity for `C²` functions.
-/

open Set Matrix
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FiniteGeodesicMaximality

noncomputable section

variable {n : ℕ}

/-! ### Linear algebra -/

/-- The rank-one matrix `E_{last, last}`. -/
def lastUnit (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun j k => if j = Fin.last n ∧ k = Fin.last n then 1 else 0

/-- A permutation of `Fin n`, extended to `Fin (n + 1)` by fixing the last element. -/
def extendLast (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.ofSubtype ((finSuccAboveEquiv (Fin.last n)).permCongr σ)

theorem extendLast_castSucc (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    extendLast σ j.castSucc = (σ j).castSucc := by
  have hj : j.castSucc ≠ Fin.last n := Fin.castSucc_ne_last j
  rw [extendLast, Equiv.Perm.ofSubtype_apply_of_mem (p := fun x => x ≠ Fin.last n) _ hj]
  have h1 : (⟨j.castSucc, hj⟩ : { x : Fin (n + 1) // x ≠ Fin.last n }) =
      finSuccAboveEquiv (Fin.last n) j :=
    Subtype.ext (by simp [finSuccAboveEquiv_apply, Fin.succAbove_last])
  rw [h1, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  simp [finSuccAboveEquiv_apply, Fin.succAbove_last]

theorem extendLast_last (σ : Equiv.Perm (Fin n)) : extendLast σ (Fin.last n) = Fin.last n := by
  rw [extendLast, Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun x => x ≠ Fin.last n) _
    (by simp)]

theorem extendLast_injective : Function.Injective (extendLast (n := n)) := by
  intro σ τ h
  ext j
  have := congrArg (fun π : Equiv.Perm (Fin (n + 1)) => π j.castSucc) h
  simp only [extendLast_castSucc] at this
  exact congrArg Fin.val (Fin.castSucc_injective n this)

theorem sign_extendLast (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (extendLast σ) = Equiv.Perm.sign σ := by
  rw [extendLast, Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]

theorem exists_extendLast_eq {π : Equiv.Perm (Fin (n + 1))} (hπ : π (Fin.last n) = Fin.last n) :
    ∃ σ : Equiv.Perm (Fin n), extendLast σ = π := by
  have hne : ∀ x, x ≠ Fin.last n → π x ≠ Fin.last n := fun x hx h =>
    hx (π.injective (h.trans hπ.symm))
  let πs : Equiv.Perm { x : Fin (n + 1) // x ≠ Fin.last n } :=
    π.subtypePerm fun x => ⟨fun hx h => hx (by rw [h, hπ]), fun hx => hne x hx⟩
  refine ⟨(finSuccAboveEquiv (Fin.last n)).symm.permCongr πs, ?_⟩
  ext x
  by_cases hx : x = Fin.last n
  · subst hx
    rw [extendLast_last, hπ]
  · rw [extendLast, Equiv.Perm.ofSubtype_apply_of_mem (p := fun x => x ≠ Fin.last n) _ hx]
    simp [Equiv.permCongr_apply, πs]

/-- **The mixed coefficient with a rank-one last slot.** If the last slot is `E_{last, last}`, the
mixed coefficient is the mixed coefficient of the top-left `n × n` blocks of the other slots. -/
theorem mixedCoefficient_eq_of_last_eq_lastUnit (H : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hH : H (Fin.last n) = lastUnit n) :
    mixedCoefficient H =
      mixedCoefficient (fun i : Fin n => (H i.castSucc).submatrix Fin.castSucc Fin.castSucc) := by
  unfold mixedCoefficient
  symm
  refine Fintype.sum_of_injective extendLast extendLast_injective _ _ ?_ ?_
  · -- permutations moving the last row see a zero row
    intro π hπ
    have hmove : π (Fin.last n) ≠ Fin.last n := fun h =>
      hπ (by obtain ⟨σ, hσ⟩ := exists_extendLast_eq h; exact ⟨σ, hσ⟩)
    obtain ⟨j₀, hj₀π⟩ : ∃ j, π j = Fin.last n := ⟨π.symm (Fin.last n), by simp⟩
    have hj₀ : j₀ ≠ Fin.last n := fun h => hmove (by rw [← h, hj₀π, h])
    apply Matrix.det_eq_zero_of_row_eq_zero j₀
    intro k
    simp [hj₀π, hH, lastUnit, hj₀]
  · -- permutations fixing the last row: Laplace expansion along it
    intro σ
    rw [Matrix.det_succ_row (fun j k => H (extendLast σ j) j k) (Fin.last n)]
    rw [Finset.sum_eq_single (Fin.last n)]
    · have hrow : H (extendLast σ (Fin.last n)) (Fin.last n) (Fin.last n) = 1 := by
        rw [extendLast_last, hH]
        simp [lastUnit]
      simp only [hrow, Fin.succAbove_last, mul_one]
      rw [show ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 by
        rw [← two_mul, pow_mul]; simp]
      rw [one_mul]
      congr 1
      ext j k
      show H (σ j).castSucc j.castSucc k.castSucc =
        H (extendLast σ j.castSucc) j.castSucc k.castSucc
      rw [extendLast_castSucc]
    · intro k _ hk
      have : H (extendLast σ (Fin.last n)) (Fin.last n) k = 0 := by
        rw [extendLast_last, hH]
        simp [lastUnit, hk]
      simp [this]
    · simp

/-! ### The model `ℂⁿ⁺¹ = ℂⁿ × ℂ` in coordinates -/

theorem stripModelEquiv_symm_apply_castSucc (y : ComplexModel n) (τ : ℂ) (j : Fin n) :
    (stripModelEquiv n).symm (y, τ) j.castSucc = y j := by
  simp [stripModelEquiv, Pending.ProductComplexManifold.prodModelEquiv,
    EuclideanSpace.finAddEquivProd]

theorem stripModelEquiv_symm_apply_last (y : ComplexModel n) (τ : ℂ) :
    (stripModelEquiv n).symm (y, τ) (Fin.last n) = τ := by
  simp [stripModelEquiv, Pending.ProductComplexManifold.prodModelEquiv,
    EuclideanSpace.finAddEquivProd]

theorem stripModelEquiv_symm_coordinateVector (j : Fin n) :
    (stripModelEquiv n).symm (coordinateVector j, 0) = coordinateVector j.castSucc := by
  ext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · rw [stripModelEquiv_symm_apply_last]
    simp [coordinateVector, (Fin.castSucc_ne_last j).symm]
  · rw [stripModelEquiv_symm_apply_castSucc]
    simp [coordinateVector, Fin.castSucc_inj]

/-! ### The complex Hessian of `|τ|²` -/

/-- `|τ|²` on `ℂⁿ⁺¹`: the squared modulus of the last coordinate. -/
def lastNormSq (n : ℕ) : ComplexModel (n + 1) → ℝ := fun q => ‖q (Fin.last n)‖ ^ 2

/-- The last coordinate, as a real continuous linear map. -/
def lastCoordinate (n : ℕ) : ComplexModel (n + 1) →L[ℝ] ℂ :=
  (EuclideanSpace.proj (Fin.last n) : ComplexModel (n + 1) →L[ℂ] ℂ).restrictScalars ℝ

@[simp] theorem lastCoordinate_apply (q : ComplexModel (n + 1)) :
    lastCoordinate n q = q (Fin.last n) := rfl

theorem realHessian_lastNormSq (q a b : ComplexModel (n + 1)) :
    realHessian (lastNormSq n) q a b = 2 * inner ℝ (a (Fin.last n)) (b (Fin.last n)) := by
  have h := realHessian_comp_affine (contDiff_norm_sq ℝ : ContDiff ℝ 2 fun x : ℂ => ‖x‖ ^ 2)
    (lastCoordinate n) 0 q a b
  have hfun : (fun y : ComplexModel (n + 1) => ‖(0 : ℂ) + lastCoordinate n y‖ ^ 2) =
      lastNormSq n := by
    funext y
    simp [lastNormSq]
  rw [hfun] at h
  rw [h, realHessian_norm_sq]
  rfl

theorem complexHessian_lastNormSq (q : ComplexModel (n + 1)) :
    complexHessian (lastNormSq n) q = lastUnit n := by
  ext j k
  simp only [complexHessian, realHessian_lastNormSq, lastUnit]
  by_cases hj : j = Fin.last n <;> by_cases hk : k = Fin.last n
  · subst hj hk
    simp [coordinateVector]
    norm_num
  · simp [coordinateVector, hk, Ne.symm hk]
  · simp [coordinateVector, hj, Ne.symm hj]
  · simp [coordinateVector, hj, Ne.symm hj]

/-! ### The complex Hessian on a fibre -/

/-- The real linear inclusion of the fibre `ℂⁿ × {0}` into `ℂⁿ⁺¹`. -/
def fibreInclusion (n : ℕ) : ComplexModel n →L[ℝ] ComplexModel (n + 1) :=
  (((stripModelEquiv n).symm : ComplexModel n × ℂ →L[ℂ] ComplexModel (n + 1)).comp
    (ContinuousLinearMap.inl ℂ (ComplexModel n) ℂ)).restrictScalars ℝ

@[simp] theorem fibreInclusion_apply (y : ComplexModel n) :
    fibreInclusion n y = (stripModelEquiv n).symm (y, 0) := rfl

theorem fibreInclusion_smul (c : ℂ) (y : ComplexModel n) :
    fibreInclusion n (c • y) = c • fibreInclusion n y := by
  simp only [fibreInclusion_apply]
  rw [← map_smul]
  simp

theorem stripModelEquiv_symm_eq_add (y : ComplexModel n) (τ : ℂ) :
    (stripModelEquiv n).symm (y, τ) = (stripModelEquiv n).symm (0, τ) + fibreInclusion n y := by
  rw [fibreInclusion_apply, ← map_add]
  simp

/-- **The complex Hessian of the restriction to a fibre** is the top-left block of the complex
Hessian. -/
theorem complexHessian_fibre {F : ComplexModel (n + 1) → ℝ} (hF : ContDiff ℝ 2 F)
    (y : ComplexModel n) (τ : ℂ) :
    complexHessian (fun y' => F ((stripModelEquiv n).symm (y', τ))) y =
      (complexHessian F ((stripModelEquiv n).symm (y, τ))).submatrix Fin.castSucc Fin.castSucc := by
  have hfun : (fun y' => F ((stripModelEquiv n).symm (y', τ))) =
      fun y' => F ((stripModelEquiv n).symm (0, τ) + fibreInclusion n y') := by
    funext y'
    rw [stripModelEquiv_symm_eq_add]
  have hR : ∀ a b : ComplexModel n,
      realHessian (fun y' => F ((stripModelEquiv n).symm (y', τ))) y a b =
        realHessian F ((stripModelEquiv n).symm (y, τ)) (fibreInclusion n a)
          (fibreInclusion n b) := by
    intro a b
    rw [hfun, realHessian_comp_affine hF, ← stripModelEquiv_symm_eq_add]
  have hv : ∀ j : Fin n, fibreInclusion n (coordinateVector j) = coordinateVector j.castSucc :=
    fun j => by rw [fibreInclusion_apply, stripModelEquiv_symm_coordinateVector]
  have hIv : ∀ j : Fin n, fibreInclusion n (Complex.I • coordinateVector j) =
      Complex.I • coordinateVector j.castSucc := fun j => by
    rw [fibreInclusion_smul, hv]
  ext j k
  simp only [complexHessian, Matrix.submatrix_apply, hR, hv, hIv]

/-! ### The slicing identity -/

/-- **The smooth slicing identity.** If the last slot is `|τ|²` and the other slots are `C²`, the
mixed density on `ℂⁿ⁺¹` at `(y, τ)` is `1/π` times the mixed density at `y` of the restrictions to
the fibre `ℂⁿ × {τ}`. -/
theorem mixedDensity_eq_fibre_div_pi (u : Fin (n + 1) → ComplexModel (n + 1) → ℝ)
    (hu : ∀ i : Fin n, ContDiff ℝ 2 (u i.castSucc)) (hlast : u (Fin.last n) = lastNormSq n)
    (y : ComplexModel n) (τ : ℂ) :
    mixedDensity u ((stripModelEquiv n).symm (y, τ)) =
      mixedDensity (fun i : Fin n => fun y' => u i.castSucc ((stripModelEquiv n).symm (y', τ)))
        y / Real.pi := by
  unfold mixedDensity
  rw [mixedCoefficient_eq_of_last_eq_lastUnit _ (by rw [hlast, complexHessian_lastNormSq])]
  have hblock : (fun i : Fin n =>
      (complexHessian (u i.castSucc) ((stripModelEquiv n).symm (y, τ))).submatrix Fin.castSucc
        Fin.castSucc) =
      fun i : Fin n => complexHessian
        (fun y' => u i.castSucc ((stripModelEquiv n).symm (y', τ))) y := by
    funext i
    rw [complexHessian_fibre (hu i)]
  rw [hblock, pow_succ, div_div]

/-- The slicing identity at an arbitrary point `q` of `ℂⁿ⁺¹`, with `(y, τ) = stripModelEquiv q`. -/
theorem mixedDensity_eq_fibre_div_pi' (u : Fin (n + 1) → ComplexModel (n + 1) → ℝ)
    (hu : ∀ i : Fin n, ContDiff ℝ 2 (u i.castSucc)) (hlast : u (Fin.last n) = lastNormSq n)
    (q : ComplexModel (n + 1)) :
    mixedDensity u q =
      mixedDensity (fun i : Fin n => fun y' =>
        u i.castSucc ((stripModelEquiv n).symm (y', (stripModelEquiv n q).2)))
        (stripModelEquiv n q).1 / Real.pi := by
  have h := mixedDensity_eq_fibre_div_pi u hu hlast (stripModelEquiv n q).1 (stripModelEquiv n q).2
  rwa [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at h

end

end SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot
