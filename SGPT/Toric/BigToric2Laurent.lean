import SGPT.Toric.MonomialProjectiveOrbit
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Laurent expansions of holomorphic functions on the complex torus

Infrastructure for source `chapter_toric_big.tex`, proof of `prop:baseloc`: the identification
`H⁰(X, O(D)) = ⊕_{m ∈ M ∩ P_D} ℂ χ^m` (`CLS11`, Proposition 4.3.3) rests on the Laurent
expansion of a holomorphic function on the torus `T(ℂ) = (ℂ^*)^n`.  We develop the part of it
that is needed, using the Fourier series of the compact torus `T_c = ℝ^n / ℤ^n` (Mathlib's
`UnitAddTorus`) and one-variable Cauchy integrals.

For a continuous function `g` on `T(ℂ)` its `m`-th Laurent coefficient (at radius one) is the
Fourier coefficient `mFourierCoeff (g ∘ e) m`, `e(t) = (e^{2π i t_k})_k`.

## Main results

* `circleIntegral_mul_zpow_eq`: the circle integral of `F(z) z^{-p-1}` over `|z| = ρ` is
  `2π i ρ^{-p}` times the `p`-th Fourier coefficient of `φ ↦ F(ρ e^{2π i φ})`;
* `fourierCoeff_mul_zpow_eq_zero`, `fourierCoeff_scale`: the one-variable facts (vanishing of
  negative-index coefficients of `H(s) s^q`, `H` entire, and radius independence);
* `mFourierCoeff_eq_integral_fourierCoeff`: averaging a Fourier coefficient on the torus along a
  one-parameter subgroup `φ ↦ (u_k φ)_k` (translation invariance of Haar measure and Fubini);
* `laurentCoeff_eq_zero_of_slice`, `laurentCoeff_scale`: vanishing of the Laurent coefficient
  `m` when the slices `s ↦ g(b λ_u(s))` are of the form `H(s) s^q`, `⟨m, u⟩ < q`, and the
  scaling law of the coefficients along cocharacters;
* `eq_sum_laurentCoeff`: a continuous function on `T(ℂ)` holomorphic along the coordinate
  slices whose Laurent coefficients vanish off a finite set `S` is the Laurent polynomial
  `∑_{m ∈ S} c_m χ^m`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open MeasureTheory Complex Set intervalIntegral UnitAddTorus
open scoped Real BigOperators

/-! ### One-variable facts -/

theorem toCircle_coe_real (x : ℝ) :
    ((AddCircle.toCircle (x : UnitAddCircle) : Circle) : ℂ) = exp (2 * π * x * I) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]; push_cast; ring_nf

theorem fourierCoeff_unit_eq (f : UnitAddCircle → ℂ) (p : ℤ) :
    fourierCoeff f p = ∫ x in (0:ℝ)..1, exp (-(2 * π * p * x * I)) * f x := by
  rw [fourierCoeff_eq_intervalIntegral f p 0]
  simp only [one_div, inv_one, one_smul, zero_add, smul_eq_mul]
  refine integral_congr fun x _ => ?_
  rw [fourier_coe_apply]; congr 1; push_cast; ring_nf

/-- The circle integral of `F(z) z^{-p-1}` over `|z| = ρ` is `2π i ρ^{-p}` times the `p`-th
Fourier coefficient of `φ ↦ F(ρ e^{2π i φ})`. -/
theorem circleIntegral_mul_zpow_eq (F : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (p : ℤ) :
    (∮ z in C(0, ρ), F z * z ^ (-p - 1)) =
      (2 * π * I) * ((ρ : ℂ) ^ (-p) *
        fourierCoeff (fun x : UnitAddCircle => F (ρ * AddCircle.toCircle x)) p) := by
  rw [fourierCoeff_unit_eq]
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun θ : ℝ => deriv (circleMap 0 ρ) θ • (F (circleMap 0 ρ θ) * circleMap 0 ρ θ ^ (-p - 1)))
    (a := 0) (b := 1) h2π
  simp only [mul_zero, mul_one] at hsub
  rw [eq_inv_smul_iff₀ (by exact_mod_cast h2π)] at hsub
  unfold circleIntegral
  rw [← hsub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  rw [← intervalIntegral.integral_smul]
  refine integral_congr fun x _ => ?_
  simp only [deriv_circleMap, circleMap, zero_add, smul_eq_mul, toCircle_coe_real]
  set w := exp (2 * π * x * I) with hw
  have hw0 : w ≠ 0 := exp_ne_zero _
  rw [show ((2 * π * x : ℝ) : ℂ) = (2 * π * x : ℂ) by push_cast; ring]
  rw [← hw]
  have hexp : exp (-(2 * π * p * x * I)) = w ^ (-p) := by
    rw [hw, ← exp_int_mul]; congr 1; push_cast; ring
  rw [hexp, mul_zpow, zpow_sub₀ hρ0, zpow_sub₀ hw0, zpow_one, zpow_one]
  rw [Complex.real_smul]
  field_simp
  push_cast
  ring

/-- If `H` is entire and `p < q`, the `p`-th Fourier coefficient of `H(s) s^q` on the unit
circle vanishes (Cauchy's theorem for `H(z) z^{q-p-1}`). -/
theorem fourierCoeff_mul_zpow_eq_zero {H : ℂ → ℂ} (hH : Differentiable ℂ H) {p q : ℤ}
    (hpq : p < q) :
    fourierCoeff (fun x : UnitAddCircle =>
      H (AddCircle.toCircle x) * (AddCircle.toCircle x : ℂ) ^ q) p = 0 := by
  have h := circleIntegral_mul_zpow_eq (fun z => H z * z ^ q) one_pos p
  simp only [Complex.ofReal_one, one_mul, one_zpow] at h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, q + (-p - 1) = N :=
    ⟨(q + (-p - 1)).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hzero : (∮ z in C(0, 1), H z * z ^ q * z ^ (-p - 1)) = 0 := by
    rw [circleIntegral.integral_congr zero_le_one (g := fun z => H z * z ^ N)]
    · exact circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
        (hH.continuous.mul (continuous_pow N)).continuousOn
        (fun z _ => (hH z).mul (differentiableAt_pow N))
    · intro z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hz
      simp only
      rw [mul_assoc, ← zpow_add₀ hz0, hN, zpow_natCast]
  rw [hzero] at h
  have h2 : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  exact (mul_eq_zero.mp h.symm).resolve_left h2

/-- Radius independence of Laurent coefficients: for `G` holomorphic on `ℂ^*`, the `p`-th
Fourier coefficient of `φ ↦ G(ρ e^{2π i φ})` is `ρ^p` times that of `φ ↦ G(e^{2π i φ})`. -/
theorem fourierCoeff_scale {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {0}ᶜ) {ρ : ℝ} (hρ : 0 < ρ)
    (p : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => G (ρ * AddCircle.toCircle x)) p =
      (ρ : ℂ) ^ p * fourierCoeff (fun x : UnitAddCircle => G (AddCircle.toCircle x)) p := by
  have hρ' := circleIntegral_mul_zpow_eq G hρ p
  have h1 := circleIntegral_mul_zpow_eq G one_pos p
  simp only [Complex.ofReal_one, one_mul, one_zpow] at h1
  have hF : DifferentiableOn ℂ (fun z => G z * z ^ (-p - 1)) {0}ᶜ :=
    hG.mul fun z hz => (differentiableAt_zpow.mpr (Or.inl hz)).differentiableWithinAt
  have hFat : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ (fun z => G z * z ^ (-p - 1)) z :=
    fun z hz => hF.differentiableAt (isOpen_compl_singleton.mem_nhds hz)
  have hann : ∀ {r R : ℝ}, 0 < r → r ≤ R →
      (∮ z in C(0, R), G z * z ^ (-p - 1)) = ∮ z in C(0, r), G z * z ^ (-p - 1) := by
    intro r R hr hrR
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR countable_empty
      ?_ ?_
    · intro z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hz
        linarith
      exact (hFat z hz0).continuousAt.continuousWithinAt
    · intro z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hz
        linarith
      exact hFat z hz0
  have heq : (∮ z in C(0, ρ), G z * z ^ (-p - 1)) = ∮ z in C(0, 1), G z * z ^ (-p - 1) := by
    rcases le_total ρ 1 with h | h
    · exact (hann hρ h).symm
    · exact hann one_pos h
  rw [hρ', h1] at heq
  have h2 : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have h3 := mul_left_cancel₀ h2 heq
  rw [← h3, ← mul_assoc, ← zpow_add₀ hρ0, add_neg_cancel, zpow_zero, one_mul]

/-! ### Averaging along one-parameter subgroups of the compact torus -/

variable {n : ℕ}

/-- The Haar probability measure on the compact torus `ℝ^n / ℤ^n` (the measure of
`UnitAddTorus.mFourierCoeff`). -/
abbrev torusHaar (n : ℕ) : Measure (UnitAddTorus (Fin n)) :=
  Measure.pi fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle)

/-- The one-parameter subgroup `φ ↦ (u_k φ)_k` of the compact torus. -/
def torusShift (u : Fin n → ℤ) (φ : UnitAddCircle) : UnitAddTorus (Fin n) := fun k => u k • φ

theorem continuous_torusShift (u : Fin n → ℤ) : Continuous (torusShift u) :=
  continuous_pi fun k => continuous_zsmul (u k)

theorem mFourier_add_apply (m : Fin n → ℤ) (s t : UnitAddTorus (Fin n)) :
    mFourier m (s + t) = mFourier m s * mFourier m t := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem toCircle_sum {ι : Type*} (s : Finset ι) (f : ι → UnitAddCircle) :
    ((AddCircle.toCircle (∑ i ∈ s, f i) : Circle) : ℂ) =
      ∏ i ∈ s, (AddCircle.toCircle (f i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddCircle.toCircle_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, AddCircle.toCircle_add, Circle.coe_mul, ih, Finset.prod_insert ha]

theorem mFourier_torusShift (m u : Fin n → ℤ) (φ : UnitAddCircle) :
    mFourier m (torusShift u φ) = fourier (∑ k, m k * u k) φ := by
  simp only [mFourier, ContinuousMap.coe_mk, torusShift, fourier_apply]
  rw [Finset.sum_smul, toCircle_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [smul_smul]

/-- Averaging a Fourier coefficient on the torus along the one-parameter subgroup
`φ ↦ (u_k φ)_k`: `ĥ(m) = ∫_t e^{-2π i ⟨m, t⟩} (φ ↦ h(t + φ u))^(⟨m, u⟩) dt`. -/
theorem mFourierCoeff_eq_integral_fourierCoeff {h : UnitAddTorus (Fin n) → ℂ}
    (hh : Continuous h) (m u : Fin n → ℤ) :
    mFourierCoeff h m = ∫ t, mFourier (-m) t *
      fourierCoeff (fun φ => h (t + torusShift u φ)) (∑ k, m k * u k) ∂torusHaar n := by
  set p := ∑ k, m k * u k
  have hstep : ∀ φ : UnitAddCircle, mFourierCoeff h m =
      ∫ t, mFourier (-m) t * (fourier (-p) φ * h (t + torusShift u φ)) ∂torusHaar n := by
    intro φ
    change ∫ t, mFourier (-m) t • h t ∂torusHaar n = _
    rw [← integral_add_right_eq_self (μ := torusHaar n) _ (torusShift u φ)]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [smul_eq_mul, mFourier_add_apply, mFourier_torusShift]
    have : ∑ k, (-m) k * u k = -p := by
      simp only [p, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [this]; ring
  have hint : mFourierCoeff h m = ∫ φ, ∫ t, mFourier (-m) t *
      (fourier (-p) φ * h (t + torusShift u φ))
      ∂torusHaar n ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    rw [integral_congr_ae (ae_of_all _ fun φ => (hstep φ).symm)]
    simp
  have hcont : Continuous (Function.uncurry fun (φ : UnitAddCircle) (t : UnitAddTorus (Fin n)) =>
      mFourier (-m) t * (fourier (-p) φ * h (t + torusShift u φ))) := by
    apply Continuous.mul ((mFourier (-m)).continuous.comp continuous_snd)
    apply Continuous.mul ((fourier (-p)).continuous.comp continuous_fst)
    exact hh.comp (continuous_snd.add ((continuous_torusShift u).comp continuous_fst))
  rw [hint, integral_integral_swap]
  · refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [fourierCoeff, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul]
  · exact integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact isCompact_univ)

/-! ### The multiplicative torus -/

/-- The point `e(t) = (e^{2π i t_k})_k` of the compact torus `T_c ⊆ T(ℂ)`. -/
def compactTorusPoint (t : UnitAddTorus (Fin n)) : Fin n → ℂˣ :=
  fun k => Circle.toUnits (AddCircle.toCircle (t k))

/-- The cocharacter `λ_u : ℂ^* → T(ℂ)`, `λ_u(s) = (s^{u_k})_k`, of `u ∈ N = ℤ^n`. -/
def torusCocharacter (u : Fin n → ℤ) (s : ℂˣ) : Fin n → ℂˣ := fun k => s ^ u k

/-- The positive real point `(e^{x_k})_k` of `T(ℂ)`. -/
def expTorusPoint (x : Fin n → ℝ) : Fin n → ℂˣ :=
  fun k => Units.mk0 ((Real.exp (x k) : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos (x k)).ne')

@[simp] theorem compactTorusPoint_apply (t : UnitAddTorus (Fin n)) (k : Fin n) :
    ((compactTorusPoint t k : ℂˣ) : ℂ) = AddCircle.toCircle (t k) := rfl

@[simp] theorem torusCocharacter_apply (u : Fin n → ℤ) (s : ℂˣ) (k : Fin n) :
    torusCocharacter u s k = s ^ u k := rfl

@[simp] theorem expTorusPoint_apply (x : Fin n → ℝ) (k : Fin n) :
    ((expTorusPoint x k : ℂˣ) : ℂ) = ((Real.exp (x k) : ℝ) : ℂ) := rfl

theorem continuous_compactTorusPoint : Continuous (compactTorusPoint (n := n)) := by
  refine continuous_pi fun k => Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp (continuous_apply k)
  · have hc : Continuous fun t : UnitAddTorus (Fin n) =>
        ((AddCircle.toCircle (t k) : Circle) : ℂ) :=
      (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp (continuous_apply k)
    have := hc.inv₀ (fun t => Circle.coe_ne_zero _)
    simp only [compactTorusPoint, Units.val_inv_eq_inv_val,
      Circle.toUnits_apply, Units.val_mk0]
    exact this

theorem prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G] (s : G) (f : ι → ℤ)
    (S : Finset ι) : ∏ i ∈ S, s ^ f i = s ^ ∑ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem torusCocharacter_mul (u : Fin n → ℤ) (s s' : ℂˣ) :
    torusCocharacter u (s * s') = torusCocharacter u s * torusCocharacter u s' := by
  funext k; simp [torusCocharacter, mul_zpow]

theorem compactTorusPoint_add_torusShift (t : UnitAddTorus (Fin n)) (u : Fin n → ℤ)
    (φ : UnitAddCircle) :
    compactTorusPoint (t + torusShift u φ) =
      compactTorusPoint t * torusCocharacter u (Circle.toUnits (AddCircle.toCircle φ)) := by
  funext k
  apply Units.ext
  simp only [compactTorusPoint, Pi.add_apply, torusShift, AddCircle.toCircle_add, Pi.mul_apply,
    Units.val_mul, torusCocharacter, Units.val_zpow_eq_zpow_val]
  rw [map_mul, Units.val_mul]
  congr 1
  rw [AddCircle.toCircle_zsmul]
  simp

theorem latticeCharacter_torusCocharacter (m u : Fin n → ℤ) (s : ℂˣ) :
    latticeCharacter m (torusCocharacter u s) = s ^ (∑ k, m k * u k) := by
  simp only [latticeCharacter, MonoidHom.coe_mk, OneHom.coe_mk, torusCocharacter, ← zpow_mul]
  rw [← prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun k _ => by rw [mul_comm]

theorem mFourier_eq_latticeCharacter (m : Fin n → ℤ) (t : UnitAddTorus (Fin n)) :
    mFourier m t = (latticeCharacter m (compactTorusPoint t) : ℂ) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_apply, latticeCharacter, MonoidHom.coe_mk,
    OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val, compactTorusPoint_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [AddCircle.toCircle_zsmul]
  simp

/-- Polar decomposition `a = e(t) e^{x}` of a point of `T(ℂ)`. -/
theorem exists_compactTorusPoint_mul_expTorusPoint (a : Fin n → ℂˣ) :
    ∃ t x, compactTorusPoint t * expTorusPoint x = a := by
  refine ⟨fun k => ((arg (a k : ℂ) / (2 * π) : ℝ) : UnitAddCircle),
    fun k => Real.log ‖(a k : ℂ)‖, ?_⟩
  funext k
  apply Units.ext
  simp only [Pi.mul_apply, Units.val_mul, compactTorusPoint_apply, expTorusPoint_apply,
    toCircle_coe_real]
  have hpos : 0 < ‖(a k : ℂ)‖ := norm_pos_iff.mpr (a k).ne_zero
  rw [Real.exp_log hpos]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  have : (2 * π * ((arg (a k : ℂ) / (2 * π) : ℝ) : ℂ) * I) = (arg (a k : ℂ) : ℂ) * I := by
    push_cast; field_simp
  rw [this, mul_comm]
  exact norm_mul_exp_arg_mul_I (a k : ℂ)

/-! ### Laurent coefficients -/

/-- Source `prop:baseloc` (proof): the slice hypothesis gives the vanishing of a Laurent
coefficient.  If for every `b ∈ T(ℂ)` the slice `s ↦ g(b λ_u(s))` is `H(s) s^q` with `H`
entire and `⟨m, u⟩ < q`, then the `m`-th Laurent coefficient of `g` vanishes. -/
theorem laurentCoeff_eq_zero_of_slice {g : (Fin n → ℂˣ) → ℂ} (hg : Continuous g)
    {m u : Fin n → ℤ} {q : ℤ} (hq : ∑ k, m k * u k < q)
    (hslice : ∀ b : Fin n → ℂˣ, ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ s : ℂˣ, g (b * torusCocharacter u s) = H s * (s : ℂ) ^ q) :
    mFourierCoeff (fun t => g (compactTorusPoint t)) m = 0 := by
  rw [mFourierCoeff_eq_integral_fourierCoeff (h := fun t => g (compactTorusPoint t))
    (hg.comp continuous_compactTorusPoint) m u]
  have hzero : ∀ t, fourierCoeff (fun φ => g (compactTorusPoint (t + torusShift u φ)))
      (∑ k, m k * u k) = 0 := by
    intro t
    obtain ⟨H, hH, hgH⟩ := hslice (compactTorusPoint t)
    have hfun : (fun φ => g (compactTorusPoint (t + torusShift u φ))) = fun φ : UnitAddCircle =>
        H (AddCircle.toCircle φ) * (AddCircle.toCircle φ : ℂ) ^ q := by
      funext φ
      rw [compactTorusPoint_add_torusShift, hgH]
      rfl
    rw [hfun]
    exact fourierCoeff_mul_zpow_eq_zero hH hq
  simp [hzero]

/-- Scaling law of Laurent coefficients along a cocharacter: if the slices
`s ↦ g(b λ_u(s))` are holomorphic on `ℂ^*`, then the coefficients of `g(· r λ_u(ρ))` are
`ρ^{⟨m, u⟩}` times those of `g(· r)` (`ρ > 0`). -/
theorem laurentCoeff_scale {g : (Fin n → ℂˣ) → ℂ} (hg : Continuous g) (m u : Fin n → ℤ)
    (hslice : ∀ b : Fin n → ℂˣ, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {0}ᶜ ∧
      ∀ s : ℂˣ, g (b * torusCocharacter u s) = G s)
    (r : Fin n → ℂˣ) {ρ : ℝ} (hρ : 0 < ρ) :
    mFourierCoeff (fun t => g (compactTorusPoint t * (r * torusCocharacter u
        (Units.mk0 (ρ : ℂ) (by exact_mod_cast hρ.ne'))))) m =
      (ρ : ℂ) ^ (∑ k, m k * u k) * mFourierCoeff (fun t => g (compactTorusPoint t * r)) m := by
  set ρu : ℂˣ := Units.mk0 (ρ : ℂ) (by exact_mod_cast hρ.ne')
  have hc1 : Continuous fun t => g (compactTorusPoint t * (r * torusCocharacter u ρu)) :=
    hg.comp (continuous_compactTorusPoint.mul continuous_const)
  have hc0 : Continuous fun t => g (compactTorusPoint t * r) :=
    hg.comp (continuous_compactTorusPoint.mul continuous_const)
  rw [mFourierCoeff_eq_integral_fourierCoeff hc1 m u, mFourierCoeff_eq_integral_fourierCoeff hc0 m u,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  obtain ⟨G, hG, hgG⟩ := hslice (compactTorusPoint t * r)
  have h1 : (fun φ => g (compactTorusPoint (t + torusShift u φ) * (r * torusCocharacter u ρu))) =
      fun φ : UnitAddCircle => G (ρ * AddCircle.toCircle φ) := by
    funext φ
    rw [compactTorusPoint_add_torusShift]
    have : compactTorusPoint t * torusCocharacter u (Circle.toUnits (AddCircle.toCircle φ)) *
        (r * torusCocharacter u ρu) = (compactTorusPoint t * r) *
          torusCocharacter u (ρu * Circle.toUnits (AddCircle.toCircle φ)) := by
      rw [torusCocharacter_mul]
      simp only [mul_comm, mul_left_comm]
    rw [this, hgG]
    rfl
  have h0 : (fun φ => g (compactTorusPoint (t + torusShift u φ) * r)) =
      fun φ : UnitAddCircle => G (AddCircle.toCircle φ) := by
    funext φ
    rw [compactTorusPoint_add_torusShift]
    have : compactTorusPoint t * torusCocharacter u (Circle.toUnits (AddCircle.toCircle φ)) * r =
        (compactTorusPoint t * r) * torusCocharacter u (Circle.toUnits (AddCircle.toCircle φ)) := by
      simp only [mul_comm, mul_left_comm]
    rw [this, hgG]
    rfl
  simp only
  rw [h1, h0, fourierCoeff_scale hG hρ]
  ring

/-- The scaling law at a positive real point: the Laurent coefficients of `g(· e^x)` are
`χ^m(e^x)` times those of `g`. -/
theorem laurentCoeff_expTorusPoint {g : (Fin n → ℂˣ) → ℂ} (hg : Continuous g)
    (hslice : ∀ (k : Fin n) (b : Fin n → ℂˣ), ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {0}ᶜ ∧
      ∀ s : ℂˣ, g (b * torusCocharacter (Pi.single k 1) s) = G s)
    (m : Fin n → ℤ) (x : Fin n → ℝ) :
    mFourierCoeff (fun t => g (compactTorusPoint t * expTorusPoint x)) m =
      (latticeCharacter m (expTorusPoint x) : ℂ) *
        mFourierCoeff (fun t => g (compactTorusPoint t)) m := by
  classical
  -- `x_S`: the coordinates of `x` in `S`, zero elsewhere
  have key : ∀ S : Finset (Fin n),
      mFourierCoeff (fun t => g (compactTorusPoint t *
        expTorusPoint (fun k => if k ∈ S then x k else 0))) m =
      (latticeCharacter m (expTorusPoint (fun k => if k ∈ S then x k else 0)) : ℂ) *
        mFourierCoeff (fun t => g (compactTorusPoint t)) m := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h1 : expTorusPoint (n := n) (fun k => if k ∈ (∅ : Finset (Fin n)) then x k else 0) = 1 := by
        funext k; apply Units.ext; simp
      rw [h1]; simp
    | insert a S ha ih =>
      have hρ : 0 < Real.exp (x a) := Real.exp_pos _
      have hsplit : expTorusPoint (fun k => if k ∈ insert a S then x k else 0) =
          expTorusPoint (fun k => if k ∈ S then x k else 0) *
            torusCocharacter (Pi.single a 1)
              (Units.mk0 ((Real.exp (x a) : ℝ) : ℂ) (by exact_mod_cast hρ.ne')) := by
        funext k
        apply Units.ext
        by_cases hk : k = a
        · subst hk
          simp [ha]
        · simp [Finset.mem_insert, hk]
      rw [hsplit, laurentCoeff_scale hg m (Pi.single a 1) (hslice a) _ hρ, ih, map_mul,
        latticeCharacter_torusCocharacter]
      have hsum : ∑ k, m k * (Pi.single a (1 : ℤ) : Fin n → ℤ) k = m a := by
        simp [Pi.single_apply]
      rw [hsum]
      push_cast
      simp only [Units.val_mk0]
      ring
  have hx : (fun k => if k ∈ (Finset.univ : Finset (Fin n)) then x k else 0) = x := by
    funext k; simp
  simpa only [hx] using key Finset.univ

/-- Source `prop:baseloc` (proof): the Laurent expansion.  Let `g` be continuous on `T(ℂ)`,
holomorphic along the coordinate slices, and suppose that every Laurent coefficient
of every translate `g(· r)` outside the finite set `S` vanishes.  Then
`g = ∑_{m ∈ S} c_m χ^m` on `T(ℂ)`, with `c_m` the Laurent coefficients of `g`. -/
theorem eq_sum_laurentCoeff {g : (Fin n → ℂˣ) → ℂ} (hg : Continuous g)
    (hslice : ∀ (k : Fin n) (b : Fin n → ℂˣ), ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {0}ᶜ ∧
      ∀ s : ℂˣ, g (b * torusCocharacter (Pi.single k 1) s) = G s)
    (S : Finset (Fin n → ℤ))
    (hS : ∀ m ∉ S, mFourierCoeff (fun t => g (compactTorusPoint t)) m = 0)
    (a : Fin n → ℂˣ) :
    g a = ∑ m ∈ S, mFourierCoeff (fun t => g (compactTorusPoint t)) m *
      (latticeCharacter m a : ℂ) := by
  obtain ⟨t, x, rfl⟩ := exists_compactTorusPoint_mul_expTorusPoint a
  let f : C(UnitAddTorus (Fin n), ℂ) :=
    ⟨fun t => g (compactTorusPoint t * expTorusPoint x),
      hg.comp (continuous_compactTorusPoint.mul continuous_const)⟩
  have hcoeff : ∀ m, mFourierCoeff f m = (latticeCharacter m (expTorusPoint x) : ℂ) *
      mFourierCoeff (fun t => g (compactTorusPoint t)) m :=
    fun m => laurentCoeff_expTorusPoint hg hslice m x
  have hsupp : ∀ m ∉ S, mFourierCoeff f m = 0 := by
    intro m hm
    rw [hcoeff, hS m hm, mul_zero]
  have hsum : Summable (mFourierCoeff f) := summable_of_ne_finset_zero hsupp
  have h := hasSum_mFourier_series_apply_of_summable hsum t
  have h' := h.unique (hasSum_sum_of_ne_finset_zero (s := S) fun m hm => by
    rw [hsupp m hm, zero_smul])
  change g (compactTorusPoint t * expTorusPoint x) = _
  change f t = _
  rw [h']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hcoeff, smul_eq_mul, mFourier_eq_latticeCharacter, map_mul, Units.val_mul]
  ring

end SGPT.Toric
