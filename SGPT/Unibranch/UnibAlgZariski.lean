import SGPT.Unibranch.UnibAlgPowerSeries
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Analysis.Complex.Basic

/-!
# Normality survives the base change `ℂ[w] → ℂ⟦w⟧` (Zariski)

Let `R'` be a Noetherian integrally closed domain which is an algebra over `P₀ = ℂ[w]`, and
`D = ℂ⟦w⟧ ⊗_{P₀} R'`. Assume that the fibres `ℂ⟦w⟧ ⊗_{P₀} R'/𝔮` are reduced for every prime `𝔮`.
Then for every nonzero `δ ∈ R'`, an element `b ∈ D` with `b² = δ b` is divisible by `δ`
(`dvd_of_sq_eq_mul`). This is the "Zariski normality" step of the excellence argument: for
every associated prime `𝔮` of `R'/δ` the localization `R'_𝔮` has a principal maximal ideal
(`exists_uniformizer`, normality), so `δ = u πᵉ` there; dividing `b` by `π` one step at a time
uses only that `D/𝔮D` is reduced; prime avoidance and the flatness of `ℂ⟦w⟧` glue the local
statements (`flat_transfer`).

Lane UNIB-ALG, step U3 (e) of `claude-serre-gaga.tex`; blueprint `claude-unib-alg.tex`.
-/

set_option autoImplicit false

open TensorProduct

namespace SGPT.Unibranch.UnibAlg

noncomputable section

/-! ### Associated primes of `R' / δ` in a normal domain -/

section Uniformizer

variable {R' : Type*} [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']

/-- **Associated primes of a principal ideal in a normal domain are "principal at `𝔮`".** If
`𝔮` is an associated prime of `R' / (δ)`, there are `π ∈ 𝔮` and `σ ∉ 𝔮` with `σ 𝔮 ⊆ π R'`. -/
theorem exists_uniformizer {δ : R'} (hδ : δ ≠ 0) {q : Ideal R'}
    (hq : q ∈ associatedPrimes R' (R' ⧸ Ideal.span {δ})) :
    ∃ π ∈ q, ∃ σ ∉ q, ∀ m ∈ q, ∃ t : R', σ * m = π * t := by
  classical
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hq
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmem : ∀ r : R', r ∈ q ↔ ∃ t, r * b₀ = δ * t := by
    intro r
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk,
      ← Submodule.Quotient.mk_smul, smul_eq_mul, Ideal.Quotient.mk_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht, mul_comm]⟩
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht, mul_comm]⟩
  choose! tt htt using fun r (hr : r ∈ q) => (hmem r).mp hr
  by_cases hcase : ∃ r ∈ q, tt r ∉ q
  · obtain ⟨r, hr, hrt⟩ := hcase
    refine ⟨r, hr, tt r, hrt, fun m hm => ⟨tt m, ?_⟩⟩
    -- `m · t_r = r · t_m`, after cancelling `δ`
    apply mul_left_cancel₀ hδ
    calc δ * (tt r * m) = r * b₀ * m := by rw [htt r hr]; ring
      _ = r * (m * b₀) := by ring
      _ = δ * (r * tt m) := by rw [htt m hm]; ring
  · push Not at hcase
    exfalso
    -- `b₀ / δ` maps `q` into itself, hence is integral, hence lies in `R'`
    set K := FractionRing R'
    set z : K := algebraMap R' K b₀ / algebraMap R' K δ
    have hδK : algebraMap R' K δ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R' K)).mpr hδ
    set N : Submodule R' K := Submodule.map (Algebra.linearMap R' K) q
    have hN0 : N ≠ ⊥ := by
      intro h
      have hδq : δ ∈ q := (hmem δ).mpr ⟨b₀, rfl⟩
      have : algebraMap R' K δ ∈ N := Submodule.mem_map_of_mem hδq
      rw [h, Submodule.mem_bot] at this
      exact hδK this
    have hNfg : N.FG := (IsNoetherian.noetherian q).map _
    have hz : IsIntegral R' z := by
      refine isIntegral_of_smul_mem_submodule N hN0 hNfg z fun n hn => ?_
      obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hn
      have : z • (Algebra.linearMap R' K m) = Algebra.linearMap R' K (tt m) := by
        simp only [Algebra.linearMap_apply, smul_eq_mul, z]
        rw [div_mul_eq_mul_div, div_eq_iff hδK, ← map_mul, ← map_mul, mul_comm b₀,
          htt m hm, mul_comm]
      rw [this]
      exact Submodule.mem_map_of_mem (hcase m hm)
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hz
    have hb₀ : b₀ = δ * y := by
      apply IsFractionRing.injective R' K
      rw [map_mul, hy, mul_div_cancel₀ _ hδK]
    have h1 : (1 : R') ∈ q := (hmem 1).mpr ⟨y, by rw [one_mul, hb₀]⟩
    exact hprime.ne_top ((Ideal.eq_top_iff_one q).mpr h1)

omit [IsIntegrallyClosed R'] in
/-- In the situation of `exists_uniformizer`, `δ = w πᵉ / s` with `s, w ∉ 𝔮`. -/
theorem exists_pow_uniformizer {δ : R'} (hδ : δ ≠ 0) {q : Ideal R'} [q.IsPrime]
    {π σ : R'} (hπ : π ∈ q) (hσ : σ ∉ q) (hσq : ∀ m ∈ q, ∃ t : R', σ * m = π * t) :
    ∃ e : ℕ, ∃ s ∉ q, ∃ w ∉ q, s * δ = w * π ^ e := by
  classical
  set Rq := Localization.AtPrime q
  have hmax : IsLocalRing.maximalIdeal Rq = Ideal.span {algebraMap R' Rq π} := by
    apply le_antisymm
    · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q Rq, Ideal.map_le_iff_le_comap]
      intro m hm
      obtain ⟨t, ht⟩ := hσq m hm
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      have hσu : IsUnit (algebraMap R' Rq σ) :=
        IsLocalization.map_units Rq (⟨σ, hσ⟩ : q.primeCompl)
      refine ⟨hσu.unit⁻¹ * algebraMap R' Rq t, ?_⟩
      rw [mul_assoc, ← map_mul, mul_comm t, ← ht, map_mul, ← mul_assoc, IsUnit.val_inv_mul,
        one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        ← IsLocalization.AtPrime.map_eq_maximalIdeal q Rq]
      exact Ideal.mem_map_of_mem _ hπ
  have hδ' : Ideal.span {algebraMap R' Rq δ} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (IsLocalization.injective Rq q.primeCompl_le_nonZeroDivisors)).mpr hδ
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_of_principal Rq ⟨⟨_, hmax⟩⟩ _ hδ'
  rw [hmax, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at he
  obtain ⟨u, hu⟩ := he
  -- `δ = π^e u⁻¹`; clear denominators
  obtain ⟨⟨w, s⟩, hws⟩ := IsLocalization.mk'_surjective q.primeCompl (↑u⁻¹ : Rq)
  simp only at hws
  have hwq : w ∉ q := by
    intro hw
    have : IsUnit (IsLocalization.mk' Rq w s) := by rw [hws]; exact Units.isUnit _
    rw [IsLocalization.mk'_eq_mul_mk'_one] at this
    have hwu : IsUnit (algebraMap R' Rq w) := isUnit_of_mul_isUnit_left this
    have : algebraMap R' Rq w ∈ IsLocalRing.maximalIdeal Rq := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q Rq]
      exact Ideal.mem_map_of_mem _ hw
    exact (IsLocalRing.mem_maximalIdeal _).mp this hwu
  refine ⟨e, s, s.2, w, hwq, ?_⟩
  apply IsLocalization.injective Rq q.primeCompl_le_nonZeroDivisors
  have h1 : algebraMap R' Rq δ = algebraMap R' Rq π ^ e * ↑u⁻¹ := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [map_mul, map_mul, map_pow, h1, ← hws]
  have h2 := IsLocalization.mk'_spec Rq w s
  rw [← h2]
  ring

end Uniformizer

/-! ### The base change `D = ℂ⟦w⟧ ⊗_{P₀} R'` -/

section Tensor

variable {d : ℕ} {R' : Type*} [CommRing R'] [Algebra (MvPolynomial (Fin d) ℂ) R']

local notation "P₀" => MvPolynomial (Fin d) ℂ
local notation "T₀" => MvPowerSeries (Fin d) ℂ

/-- `r ↦ 1 ⊗ r`. -/
abbrev ιR : R' →ₐ[MvPolynomial (Fin d) ℂ] MvPowerSeries (Fin d) ℂ ⊗[MvPolynomial (Fin d) ℂ] R' :=
  Algebra.TensorProduct.includeRight

theorem lTensor_mulLeft (r : R') (x : T₀ ⊗[P₀] R') :
    (LinearMap.mulLeft P₀ r).lTensor T₀ x = ιR r * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t a => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, mul_add]

theorem mul_left_injective_tensor [IsDomain R'] {r : R'} (hr : r ≠ 0) :
    Function.Injective (fun x : T₀ ⊗[P₀] R' => ιR r * x) := by
  have : Function.Injective ((LinearMap.mulLeft P₀ r).lTensor T₀) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (mul_right_injective₀ hr)
  intro x y hxy
  apply this
  simpa only [lTensor_mulLeft] using hxy

/-- **Flat transfer.** If `s` is regular modulo `δ` on `R'`, it is regular modulo `δ` on
`D = ℂ⟦w⟧ ⊗ R'`. -/
theorem flat_transfer [IsDomain R'] {s δ : R'} (hδ : δ ≠ 0)
    (hs : ∀ r : R', s * r ∈ Ideal.span {δ} → r ∈ Ideal.span {δ}) {x c : T₀ ⊗[P₀] R'}
    (h : ιR s * x = ιR δ * c) : ∃ y, x = ιR δ * y := by
  set f₁ : R' →ₗ[P₀] R' × R' := (LinearMap.mulLeft P₀ δ).prod (LinearMap.mulLeft P₀ s)
  set f₂ : R' × R' →ₗ[P₀] R' := (LinearMap.mulLeft P₀ s).coprod (-LinearMap.mulLeft P₀ δ)
  have hex : Function.Exact f₁ f₂ := by
    rintro ⟨a, b⟩
    constructor
    · intro hab
      have hab' : s * a - δ * b = 0 := by simpa [f₂, sub_eq_add_neg] using hab
      have h1 : s * a ∈ Ideal.span {δ} := Ideal.mem_span_singleton'.mpr ⟨b, by
        rw [mul_comm]; linear_combination -hab'⟩
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hs a h1)
      refine ⟨r, ?_⟩
      simp only [f₁, LinearMap.prod_apply]
      refine Prod.ext ?_ ?_
      · change δ * r = a
        rw [← hr, mul_comm]
      · change s * r = b
        apply mul_left_cancel₀ hδ
        linear_combination hab' + s * hr
    · rintro ⟨r, hr⟩
      rw [← hr]
      change s * (δ * r) + -(δ * (s * r)) = 0
      ring
  have hexT := Module.Flat.lTensor_exact T₀ hex
  set e := TensorProduct.prodRight P₀ P₀ T₀ R' R'
  have h1 : ∀ η, e (f₁.lTensor T₀ η) = (ιR δ * η, ιR s * η) := by
    intro η
    induction η using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]; rfl
    | tmul t a =>
      simp [e, f₁, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add, mul_add]; rfl
  have h2 : ∀ ξ, f₂.lTensor T₀ ξ = ιR s * (e ξ).1 - ιR δ * (e ξ).2 := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => simp
    | tmul t a =>
      obtain ⟨a₁, a₂⟩ := a
      simp [e, f₂, Algebra.TensorProduct.tmul_mul_tmul, sub_eq_add_neg, tmul_add,
        tmul_neg]
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add, Prod.fst_add, Prod.snd_add]
      ring
  have hzero : f₂.lTensor T₀ (e.symm (x, c)) = 0 := by
    rw [h2, LinearEquiv.apply_symm_apply, h, sub_self]
  obtain ⟨η, hη⟩ := (hexT _).mp hzero
  refine ⟨η, ?_⟩
  have := congrArg e hη
  rw [h1, LinearEquiv.apply_symm_apply] at this
  exact (Prod.mk.inj this).1.symm

/-- Multiplication by `σ` maps `𝔮 D` into `π D` when `σ 𝔮 ⊆ π R'`. -/
theorem mul_mem_of_mem_map {q : Ideal R'} {π σ : R'} (hσq : ∀ m ∈ q, ∃ t : R', σ * m = π * t)
    {z : T₀ ⊗[P₀] R'} (hz : z ∈ q.map (ιR (d := d))) : ∃ c, ιR σ * z = ιR π * c := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, hm, rfl⟩ := hz
    obtain ⟨t, ht⟩ := hσq m hm
    exact ⟨ιR t, by rw [← map_mul, ht, map_mul]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, hc₁⟩ := hx
    obtain ⟨c₂, hc₂⟩ := hy
    exact ⟨c₁ + c₂, by rw [mul_add, hc₁, hc₂, mul_add]⟩
  | smul a x _ hx =>
    obtain ⟨c₁, hc₁⟩ := hx
    exact ⟨a * c₁, by rw [smul_eq_mul, mul_left_comm, hc₁, mul_left_comm]⟩

/-- **Local step.** At an associated prime `𝔮` of `R' / δ`, an element `b` with `b² = δ b` is
divisible by `δ` after multiplication by an element outside `𝔮`. -/
theorem local_step [IsDomain R'] {q : Ideal R'} [q.IsPrime]
    (hfib : ∀ z : T₀ ⊗[P₀] R', z * z ∈ q.map (ιR (d := d)) → z ∈ q.map (ιR (d := d)))
    {δ π σ : R'} (hπq : π ∈ q) (hπ0 : π ≠ 0) (hσ : σ ∉ q)
    (hσq : ∀ m ∈ q, ∃ t : R', σ * m = π * t)
    {e : ℕ} {s w : R'} (hs : s ∉ q) (hw : w ∉ q) (hswe : s * δ = w * π ^ e)
    {b : T₀ ⊗[P₀] R'} (hb : b * b = ιR δ * b) :
    ∃ u ∉ q, ∃ c, ιR u * b = ιR δ * c := by
  have hstep : ∀ k ≤ e, ∃ u ∉ q, ∃ c, ιR u * b = ιR (π ^ k) * c := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, fun h => (Ideal.IsPrime.ne_top ‹_›)
        ((Ideal.eq_top_iff_one q).mpr h), b, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu, c, hc⟩ := ih (by omega)
      have hπk : π ^ k ≠ 0 := pow_ne_zero _ hπ0
      -- `π^k c² = u δ c`
      have e1 : ιR (π ^ k) * (c * c) = ιR (u * δ) * c := by
        apply mul_left_injective_tensor hπk
        simp only
        calc ιR (π ^ k) * (ιR (π ^ k) * (c * c)) = (ιR u * b) * (ιR u * b) := by
              rw [hc]; ring
          _ = ιR u * ιR u * (b * b) := by ring
          _ = ιR u * ιR u * (ιR δ * b) := by rw [hb]
          _ = ιR u * ιR δ * (ιR u * b) := by ring
          _ = ιR (π ^ k) * (ιR (u * δ) * c) := by rw [hc, map_mul]; ring
      -- `s c² = u w π^(e-k) c`
      have e2 : ιR s * (c * c) = ιR (u * w * π ^ (e - k)) * c := by
        apply mul_left_injective_tensor hπk
        simp only
        calc ιR (π ^ k) * (ιR s * (c * c)) = ιR s * (ιR (π ^ k) * (c * c)) := by ring
          _ = ιR s * (ιR (u * δ) * c) := by rw [e1]
          _ = ιR (u * (s * δ)) * c := by rw [map_mul, map_mul, map_mul]; ring
          _ = ιR (u * (w * π ^ e)) * c := by rw [hswe]
          _ = ιR (π ^ k) * (ιR (u * w * π ^ (e - k)) * c) := by
              have hpow : π ^ k * (u * w * π ^ (e - k)) = u * (w * π ^ e) := by
                rw [show u * (w * π ^ e) = u * w * (π ^ k * π ^ (e - k)) by
                  rw [← pow_add, Nat.add_sub_cancel' (by omega)]; ring]
                ring
              rw [← hpow, map_mul, mul_assoc]
      set z := ιR s * c
      have hz2 : z * z ∈ q.map (ιR (d := d)) := by
        obtain ⟨j, hj⟩ : ∃ j, e - k = j + 1 := ⟨e - k - 1, by omega⟩
        have : z * z = ιR π * (ιR (s * u * w * π ^ j) * c) := by
          calc z * z = ιR s * (ιR s * (c * c)) := by simp only [z]; ring
            _ = ιR s * (ιR (u * w * π ^ (e - k)) * c) := by rw [e2]
            _ = ιR π * (ιR (s * u * w * π ^ j) * c) := by
                rw [hj, pow_succ]
                simp only [map_mul, map_pow]
                ring
        rw [this]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπq)
      obtain ⟨c', hc'⟩ := mul_mem_of_mem_map hσq (hfib z hz2)
      refine ⟨σ * s * u, ?_, c', ?_⟩
      · exact fun h => by
          rcases (Ideal.IsPrime.mem_or_mem ‹_› h) with h1 | h1
          · rcases (Ideal.IsPrime.mem_or_mem ‹_› h1) with h2 | h2
            · exact hσ h2
            · exact hs h2
          · exact hu h1
      · calc ιR (σ * s * u) * b = ιR σ * ιR s * (ιR u * b) := by simp only [map_mul]; ring
          _ = ιR (π ^ k) * (ιR σ * z) := by rw [hc]; simp only [z]; ring
          _ = ιR (π ^ (k + 1)) * c' := by rw [hc', pow_succ, map_mul]; ring
  obtain ⟨u, hu, c, hc⟩ := hstep e le_rfl
  refine ⟨w * u, fun h => ?_, ιR s * c, ?_⟩
  · rcases (Ideal.IsPrime.mem_or_mem ‹_› h) with h1 | h1
    · exact hw h1
    · exact hu h1
  · calc ιR (w * u) * b = ιR w * (ιR u * b) := by rw [map_mul, mul_assoc]
      _ = ιR (w * π ^ e) * c := by rw [hc, map_mul]; ring
      _ = ιR (s * δ) * c := by rw [hswe]
      _ = ιR δ * (ιR s * c) := by rw [map_mul]; ring

/-- **Zariski normality, idempotent form.** Let `R'` be a Noetherian integrally closed domain
over `ℂ[w]` whose fibres `D / 𝔮 D` are reduced. If `δ ≠ 0` and `b² = δ b` in
`D = ℂ⟦w⟧ ⊗ R'`, then `δ ∣ b`. -/
theorem dvd_of_sq_eq_mul [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    (hfib : ∀ (q : Ideal R'), q.IsPrime →
      ∀ z : T₀ ⊗[P₀] R', z * z ∈ q.map (ιR (d := d)) → z ∈ q.map (ιR (d := d)))
    {δ : R'} (hδ : δ ≠ 0) {b : T₀ ⊗[P₀] R'} (hb : b * b = ιR δ * b) :
    ∃ c, b = ιR δ * c := by
  classical
  set Ass := associatedPrimes R' (R' ⧸ Ideal.span {δ})
  have hfin : Ass.Finite := associatedPrimes.finite R' _
  have hδq : ∀ q ∈ Ass, δ ∈ q := by
    intro q hq
    apply (AssociatedPrimes.mem_iff.mp hq).annihilator_le
    rw [Submodule.mem_annihilator]
    intro x _
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hloc : ∀ q ∈ Ass, ∃ u ∉ q, ∃ c, ιR u * b = ιR δ * c := by
    intro q hq
    have hqp : q.IsPrime := (AssociatedPrimes.mem_iff.mp hq).isPrime
    obtain ⟨π, hπq, σ, hσ, hσq⟩ := exists_uniformizer hδ hq
    have hπ0 : π ≠ 0 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hσq δ (hδq q hq)
      rw [zero_mul, mul_eq_zero] at ht
      rcases ht with h | h
      · exact hσ (h ▸ q.zero_mem)
      · exact hδ h
    obtain ⟨e, s, hs, w, hw, hswe⟩ := exists_pow_uniformizer hδ hπq hσ hσq
    exact local_step (hfib q hqp) hπq hπ0 hσ hσq hs hw hswe hb
  choose! u hu c hc using hloc
  set 𝔰 : Ideal R' := Ideal.span (u '' Ass)
  have hall : ∀ x ∈ 𝔰, ∃ c', ιR x * b = ιR δ * c' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨c q, hc q hq⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c₁, hc₁⟩ := hx
      obtain ⟨c₂, hc₂⟩ := hy
      exact ⟨c₁ + c₂, by rw [map_add, add_mul, hc₁, hc₂, mul_add]⟩
    | smul a x _ hx =>
      obtain ⟨c₁, hc₁⟩ := hx
      exact ⟨ιR a * c₁, by rw [smul_eq_mul, map_mul, mul_assoc, hc₁, mul_left_comm]⟩
  -- prime avoidance
  have hnot : ¬ ((𝔰 : Set R') ⊆ ⋃ q ∈ (hfin.toFinset : Set (Ideal R')), (q : Set R')) := by
    intro hsub
    obtain ⟨q, hq, hle⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun q hq _ _ => (AssociatedPrimes.mem_iff.mp (hfin.mem_toFinset.mp hq)).isPrime)).mp
      (by simpa using hsub)
    have hq' := hfin.mem_toFinset.mp hq
    exact hu q hq' (hle (Ideal.subset_span ⟨q, hq', rfl⟩))
  obtain ⟨s, hs𝔰, hsnot⟩ := Set.not_subset.mp hnot
  have hreg : IsSMulRegular (R' ⧸ Ideal.span {δ}) s := by
    have : s ∉ ⋃ p ∈ associatedPrimes R' (R' ⧸ Ideal.span {δ}), (p : Set R') := by
      simpa [hfin.coe_toFinset] using hsnot
    rw [biUnion_associatedPrimes_eq_compl_regular] at this
    simpa using this
  have hs' : ∀ r : R', s * r ∈ Ideal.span {δ} → r ∈ Ideal.span {δ} := by
    intro r hr
    have : s • (Ideal.Quotient.mk (Ideal.span {δ}) r) = s • 0 := by
      rw [smul_zero, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hreg this)
  obtain ⟨c', hc'⟩ := hall s hs𝔰
  exact flat_transfer hδ hs' hc'

end Tensor

end

end SGPT.Unibranch.UnibAlg
