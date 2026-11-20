import SGPT.Unibranch.UnibAlgFibre
import SGPT.Unibranch.GAGA2Normalization

/-!
# Unibranch points have formally irreducible completions (EGA IV 18.9.1, U3)

Let `R` be a domain, finite and torsion-free over `P₀ = ℂ[w]`, presented as a quotient of
`ℂ[z]` (`BridgeData`), and let `R'` be a Noetherian integrally closed domain, finite and
torsion-free over `R` (the normalization). If exactly one maximal ideal of `R'` lies over the
maximal ideal of the point `c`, then the formal completion `B = ℂ⟦z - c⟧ / I` is a domain
(`BridgeData.isDomain_B`). The proof:

* `B` is the localization of `S = ℂ⟦w⟧ ⊗ R` at `M_c` (`UnibAlgBridge`), and `S ⊆ D = ℂ⟦w⟧ ⊗ R'`
  by flatness;
* `D` embeds into `K₀[X] / (f_K)` (`UnibAlgPrimitive`), whose idempotents give, through the
  splitting lemma and Zariski normality (`dvd_of_sq_eq_mul`, with reduced fibres from
  `UnibAlgFibre`), idempotents of `D` separating any two zero divisors;
* `D` has a single maximal ideal over `M_c` (unibranch hypothesis and residue fields `ℂ`), so
  such an idempotent is trivial near `M_c`.

Lane UNIB-ALG, step U3 of `claude-serre-gaga.tex`; blueprint `claude-unib-alg.tex`.
-/

set_option autoImplicit false

open MvPowerSeries TensorProduct

namespace SGPT.Unibranch.UnibAlg

noncomputable section

variable {n d : ℕ}

local notation "P₀" => MvPolynomial (Fin d) ℂ
local notation "T₀" => MvPowerSeries (Fin d) ℂ

namespace BridgeData

variable {R R' : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
  [Algebra (MvPolynomial (Fin d) ℂ) R] [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) R]
  [Module.Finite (MvPolynomial (Fin d) ℂ) R] [FaithfulSMul (MvPolynomial (Fin d) ℂ) R]
  [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [Algebra ℂ R']
  [Algebra R R'] [Algebra (MvPolynomial (Fin d) ℂ) R'] [IsScalarTower (MvPolynomial (Fin d) ℂ) R R']
  [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) R'] [Module.Finite R R'] [FaithfulSMul R R']
  (D : BridgeData n d R)

/-- The inclusion `S = ℂ⟦w⟧ ⊗ R → D = ℂ⟦w⟧ ⊗ R'`. -/
def incl : T₀ ⊗[P₀] R →ₐ[P₀] T₀ ⊗[P₀] R' :=
  Algebra.TensorProduct.map (AlgHom.id P₀ T₀) (IsScalarTower.toAlgHom P₀ R R')

omit [IsDomain R] [IsScalarTower ℂ P₀ R] [Module.Finite P₀ R] [FaithfulSMul P₀ R] [IsDomain R']
  [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsScalarTower ℂ P₀ R'] [Module.Finite R R']
  [Algebra ℂ R] [Algebra ℂ R'] [FaithfulSMul R R'] in
theorem incl_tmul (t : T₀) (r : R) :
    incl (R := R) (R' := R') (t ⊗ₜ r) = t ⊗ₜ algebraMap R R' r := rfl

omit [IsDomain R] [Algebra ℂ R] [IsScalarTower ℂ P₀ R] [Module.Finite P₀ R] [FaithfulSMul P₀ R]
  [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [Algebra ℂ R']
  [IsScalarTower ℂ P₀ R'] [Module.Finite R R'] in
theorem incl_injective : Function.Injective (incl (d := d) (R := R) (R' := R')) := by
  have h : Function.Injective ((IsScalarTower.toAlgHom P₀ R R').toLinearMap.lTensor T₀) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R R')
  convert h using 1
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t r => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable [Module.Finite (MvPolynomial (Fin d) ℂ) R'] [FaithfulSMul (MvPolynomial (Fin d) ℂ) R']

omit [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [FaithfulSMul P₀ R'] in
/-- The fibres of `D = ℂ⟦w⟧ ⊗ R'` are reduced. -/
theorem fib_R' (q : Ideal R') (hq : q.IsPrime) (z : T₀ ⊗[P₀] R')
    (hz : z * z ∈ q.map (ιR (d := d))) : z ∈ q.map (ιR (d := d)) := by
  have : IsDomain (R' ⧸ q) := (Ideal.Quotient.isDomain_iff_prime q).mpr hq
  have : Module.Finite P₀ (R' ⧸ q) :=
    Module.Finite.of_surjective ((Ideal.Quotient.mkₐ P₀ q).toLinearMap)
      Ideal.Quotient.mk_surjective
  have := isReduced_tensor_of_finite (d := d) (R₁ := R' ⧸ q)
  set e := Algebra.TensorProduct.tensorQuotientEquiv (R := P₀) P₀ R' T₀ q
  have h1 : e.symm (Ideal.Quotient.mk (q.map (ιR (d := d))) z) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨2, ?_⟩
    rw [← map_pow, pow_two, ← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem] at h1
  exact h1

omit [FaithfulSMul P₀ R'] in
/-- Zariski normality for `R'`. -/
theorem dvd_of_sq_eq_mul_R' {δ : R'} (hδ : δ ≠ 0) {b : T₀ ⊗[P₀] R'}
    (hb : b * b = ιR δ * b) : ∃ c, b = ιR δ * c :=
  dvd_of_sq_eq_mul (fun q hq z hz => fib_R' q hq z hz) hδ hb

omit [IsDomain R] [Module.Finite P₀ R] [FaithfulSMul P₀ R] in
theorem χ_one_tmul (r : R) : D.χ ((1 : T₀) ⊗ₜ r) = D.evR r := by
  rw [χ_tmul, map_one, one_mul]

omit [IsDomain R] [Module.Finite P₀ R] [FaithfulSMul P₀ R] in
theorem χ_surjective : Function.Surjective D.χ := fun z =>
  ⟨(C z : T₀) ⊗ₜ (1 : R), by rw [χ_tmul, constantCoeff_C, map_one, mul_one]⟩

omit [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [Module.Finite P₀ R']
  [FaithfulSMul P₀ R'] in
theorem ιR_algebraMap_ℂ (z : ℂ) :
    (ιR (d := d) (algebraMap ℂ R' z)) = algebraMap ℂ (T₀ ⊗[P₀] R') z := by
  rw [IsScalarTower.algebraMap_apply ℂ P₀ R', algebraMap_tensor_eq]
  change (1 : T₀) ⊗ₜ[P₀] algebraMap P₀ R' (algebraMap ℂ P₀ z) = _
  rw [one_tmul_algebraMap, MvPolynomial.algebraMap_eq, MvPolynomial.coe_C]

omit [Module.Finite R R'] [FaithfulSMul R R'] [IsDomain R] [Module.Finite P₀ R]
  [FaithfulSMul P₀ R] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
  [FaithfulSMul P₀ R'] in
/-- **One maximal ideal over `M_c`.** -/
theorem max_eq (huni : ∀ 𝔫₁ 𝔫₂ : Ideal R', 𝔫₁.IsMaximal → 𝔫₂.IsMaximal →
      D.mR ≤ 𝔫₁.comap (algebraMap R R') → D.mR ≤ 𝔫₂.comap (algebraMap R R') → 𝔫₁ = 𝔫₂)
    (𝔐₁ 𝔐₂ : Ideal (T₀ ⊗[P₀] R')) [𝔐₁.IsMaximal] [𝔐₂.IsMaximal]
    (h₁ : 𝔐₁.comap (incl (R := R) (R' := R')) = RingHom.ker D.χ)
    (h₂ : 𝔐₂.comap (incl (R := R) (R' := R')) = RingHom.ker D.χ) : 𝔐₁ = 𝔐₂ := by
  obtain ⟨χ₁, hk₁, hC₁, hT₁⟩ := exists_residue (R₁ := R') 𝔐₁
  obtain ⟨χ₂, hk₂, hC₂, hT₂⟩ := exists_residue (R₁ := R') 𝔐₂
  -- the induced points of `R'`
  have hsurj : ∀ χ : T₀ ⊗[P₀] R' →+* ℂ, (∀ z : ℂ, χ (algebraMap ℂ _ z) = z) →
      Function.Surjective (χ.comp (ιR (d := d)).toRingHom) := fun χ hχ z =>
    ⟨algebraMap ℂ R' z, by simp only [RingHom.comp_apply]; erw [ιR_algebraMap_ℂ]; exact hχ z⟩
  have hmR : ∀ (χ : T₀ ⊗[P₀] R' →+* ℂ) (𝔐 : Ideal (T₀ ⊗[P₀] R')),
      RingHom.ker χ = 𝔐 → 𝔐.comap (incl (R := R) (R' := R')) = RingHom.ker D.χ →
      D.mR ≤ (RingHom.ker (χ.comp (ιR (d := d)).toRingHom)).comap (algebraMap R R') := by
    intro χ 𝔐 hk h r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
    have : (1 : T₀) ⊗ₜ[P₀] r ∈ 𝔐.comap (incl (R := R) (R' := R')) := by
      rw [h, RingHom.mem_ker, χ_one_tmul]
      exact hr
    rw [Ideal.mem_comap, ← hk, RingHom.mem_ker] at this
    exact this
  have hn := huni _ _ (RingHom.ker_isMaximal_of_surjective _ (hsurj χ₁ hC₁))
    (RingHom.ker_isMaximal_of_surjective _ (hsurj χ₂ hC₂)) (hmR χ₁ 𝔐₁ hk₁ h₁) (hmR χ₂ 𝔐₂ hk₂ h₂)
  have hR' : ∀ r' : R', χ₁ (ιR r') = χ₂ (ιR r') := by
    intro r'
    have hmem : r' - algebraMap ℂ R' (χ₁ (ιR r')) ∈
        RingHom.ker (χ₁.comp (ιR (d := d)).toRingHom) := by
      simp only [RingHom.mem_ker, RingHom.comp_apply, map_sub]
      erw [ιR_algebraMap_ℂ, hC₁, sub_self]
    rw [hn] at hmem
    simp only [RingHom.mem_ker, RingHom.comp_apply, map_sub] at hmem
    erw [ιR_algebraMap_ℂ, hC₂] at hmem
    exact (sub_eq_zero.mp hmem).symm
  have hχ : ∀ x, χ₁ x = χ₂ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t r' =>
      have : t ⊗ₜ[P₀] r' = (t ⊗ₜ[P₀] (1 : R')) * ((1 : T₀) ⊗ₜ[P₀] r') := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, map_mul, hT₁, hT₂]
      congr 1
      exact hR' r'
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [← hk₁, ← hk₂]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, hχ]

omit [IsDomain R] [Module.Finite P₀ R] [FaithfulSMul P₀ R] in
theorem χ_ker_isMaximal : (RingHom.ker D.χ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ D.χ_surjective

omit [IsDomain R] [Module.Finite P₀ R] [FaithfulSMul P₀ R] [IsDomain R'] [IsNoetherianRing R']
  [IsIntegrallyClosed R'] [Algebra ℂ R'] [IsScalarTower ℂ P₀ R'] [Module.Finite R R']
  [FaithfulSMul R R'] [FaithfulSMul P₀ R'] in
/-- A maximal ideal of `D` over `M_c` containing `1 - η`, unless `η` is killed near `M_c`. -/
theorem exists_max_over {η : T₀ ⊗[P₀] R'} (hη : η * η = η)
    (h : ∀ v : T₀ ⊗[P₀] R, D.χ v ≠ 0 → incl v * η ≠ 0) :
    ∃ 𝔐 : Ideal (T₀ ⊗[P₀] R'), 𝔐.IsMaximal ∧ 1 - η ∈ 𝔐 ∧
      𝔐.comap (incl (R := R) (R' := R')) = RingHom.ker D.χ := by
  let : Algebra (T₀ ⊗[P₀] R) (T₀ ⊗[P₀] R') := (incl (R := R) (R' := R')).toRingHom.toAlgebra
  have : Module.Finite T₀ (T₀ ⊗[P₀] R') := Module.Finite.base_change P₀ T₀ R'
  have : Algebra.IsIntegral (T₀ ⊗[P₀] R) (T₀ ⊗[P₀] R') := by
    constructor
    intro x
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := T₀) x
    refine ⟨p.map (algebraMap T₀ (T₀ ⊗[P₀] R)), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (T₀ ⊗[P₀] R) (T₀ ⊗[P₀] R')).comp (algebraMap T₀ (T₀ ⊗[P₀] R)) =
        algebraMap T₀ (T₀ ⊗[P₀] R') := by
      ext t
      simp only [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      change incl (R := R) (R' := R') (t ⊗ₜ[P₀] (1 : R)) = _
      rw [incl_tmul, map_one]
    rw [hcomp]
    exact hp
  have := D.χ_ker_isMaximal
  have hle : (Ideal.span {1 - η}).comap (algebraMap (T₀ ⊗[P₀] R) (T₀ ⊗[P₀] R')) ≤
      RingHom.ker D.χ := by
    intro v hv
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hv
    obtain ⟨w, hw⟩ := hv
    by_contra hχ
    apply h v hχ
    have : incl (R := R) (R' := R') v = algebraMap (T₀ ⊗[P₀] R) (T₀ ⊗[P₀] R') v := rfl
    rw [this, ← hw, mul_assoc, sub_mul, one_mul, hη, sub_self, mul_zero]
  obtain ⟨Q, hQI, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ _ hle
  refine ⟨Q, ?_, hQI (Ideal.subset_span rfl), hQc⟩
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q (hQc ▸ D.χ_ker_isMaximal)

omit [IsDomain R] [Module.Finite P₀ R] [FaithfulSMul P₀ R] [Module.Finite R R']
  [FaithfulSMul R R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
  [FaithfulSMul P₀ R'] in
/-- **Idempotents of `D` are trivial near `M_c`** (one point of `R'` over `c`). -/
theorem exists_kill (huni : ∀ 𝔫₁ 𝔫₂ : Ideal R', 𝔫₁.IsMaximal → 𝔫₂.IsMaximal →
      D.mR ≤ 𝔫₁.comap (algebraMap R R') → D.mR ≤ 𝔫₂.comap (algebraMap R R') → 𝔫₁ = 𝔫₂)
    {ε : T₀ ⊗[P₀] R'} (hε : ε * ε = ε) :
    ∃ v : T₀ ⊗[P₀] R, D.χ v ≠ 0 ∧ (incl v * ε = 0 ∨ incl v * (1 - ε) = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨𝔐₁, h𝔐₁, hm₁, hc₁⟩ := D.exists_max_over hε fun v hv => (hcon v hv).1
  obtain ⟨𝔐₂, h𝔐₂, hm₂, hc₂⟩ := D.exists_max_over (η := 1 - ε)
    (by rw [sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]) fun v hv => (hcon v hv).2
  have := D.max_eq huni 𝔐₁ 𝔐₂ hc₁ hc₂
  rw [this] at hm₁
  have h1 : (1 : T₀ ⊗[P₀] R') ∈ 𝔐₂ := by
    have := Ideal.add_mem _ hm₁ hm₂
    rwa [sub_sub_cancel, sub_add_cancel] at this
  exact h𝔐₂.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

omit [IsDomain R] [FaithfulSMul P₀ R] [Module.Finite R R'] in
/-- **The formal completion of a unibranch point is a domain.** -/
theorem isDomain_B (huni : ∀ 𝔫₁ 𝔫₂ : Ideal R', 𝔫₁.IsMaximal → 𝔫₂.IsMaximal →
      D.mR ≤ 𝔫₁.comap (algebraMap R R') → D.mR ≤ 𝔫₂.comap (algebraMap R R') → 𝔫₁ = 𝔫₂) :
    IsDomain D.B := by
  have : IsIntegrallyClosed T₀ := isIntegrallyClosed
  have := D.nontrivial_B
  obtain ⟨Θ⟩ := exists_primData (d := d) R'
  set δR : R' := algebraMap P₀ R' Θ.δ'
  have hδR : δR ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective P₀ R')).mpr
    Θ.δ'_ne_zero
  have hΦδ : Θ.Φ (ιR δR) = AdjoinRoot.of Θ.fK (ιK Θ.δ') := by
    change Θ.Φ ((1 : T₀) ⊗ₜ[P₀] algebraMap P₀ R' Θ.δ') = _
    rw [PrimData.Φ_tmul, map_one, one_mul, Θ.compat]
    rfl
  suffices hmain : ∀ x₁ x₂ : D.B, x₁ * x₂ = 0 → x₁ = 0 ∨ x₂ = 0 by
    have : NoZeroDivisors D.B := ⟨fun {a b} hab => hmain a b hab⟩
    exact NoZeroDivisors.to_isDomain _
  intro x₁ x₂ hx
  obtain ⟨s₁, rfl⟩ := D.bridgeMap_surjective x₁
  obtain ⟨s₂, rfl⟩ := D.bridgeMap_surjective x₂
  rw [← map_mul] at hx
  obtain ⟨u, hu, hus⟩ := D.bridgeMap_eq_zero hx
  set a := incl (R := R) (R' := R') (u * s₁)
  set b := incl (R := R) (R' := R') s₂
  have hab : a * b = 0 := by
    simp only [a, b, ← map_mul]
    rw [mul_assoc, hus, map_zero]
  obtain ⟨e, he1, he2, he3⟩ := Θ.exists_split (Θ.Φ a)
  rw [← hΦδ] at he1 he2
  have he : e * e = ιR δR * e := Θ.Φ_injective (by rw [map_mul, map_mul, he1])
  obtain ⟨ε, rfl⟩ := dvd_of_sq_eq_mul_R' hδR he
  have hcancel := mul_left_injective_tensor (d := d) hδR
  have hε : ε * ε = ε := by
    apply hcancel
    apply hcancel
    simp only
    calc ιR δR * (ιR δR * (ε * ε)) = ιR δR * ε * (ιR δR * ε) := by ring
      _ = ιR δR * (ιR δR * ε) := he
  have ha : a * (1 - ε) = 0 := by
    apply hcancel
    simp only [mul_zero]
    have : Θ.Φ (a * (ιR δR - ιR δR * ε)) = 0 := by rw [map_mul, map_sub]; exact he2
    rw [map_eq_zero_iff _ Θ.Φ_injective] at this
    calc ιR δR * (a * (1 - ε)) = a * (ιR δR - ιR δR * ε) := by ring
      _ = 0 := this
  have hb : b * ε = 0 := by
    apply hcancel
    simp only [mul_zero]
    have : Θ.Φ (b * (ιR δR * ε)) = 0 := by
      rw [map_mul]
      exact he3 _ (by rw [← map_mul, hab, map_zero])
    rw [map_eq_zero_iff _ Θ.Φ_injective] at this
    calc ιR δR * (b * ε) = b * (ιR δR * ε) := by ring
      _ = 0 := this
  obtain ⟨v, hv, hkill | hkill⟩ := D.exists_kill huni hε
  · left
    have h0 : incl (R := R) (R' := R') (v * u * s₁) = 0 := by
      calc incl (R := R) (R' := R') (v * u * s₁) = incl v * a := by
            simp only [a, map_mul]; ring
        _ = incl v * a * ε + incl v * (a * (1 - ε)) := by ring
        _ = 0 := by rw [mul_right_comm, hkill, zero_mul, ha, mul_zero, add_zero]
    have h1 := congrArg D.bridgeMap (incl_injective (R := R) (R' := R') (h0.trans (map_zero _).symm))
    rw [map_mul, map_mul, map_zero] at h1
    have hv' := D.isUnit_bridgeMap hv
    have hu' := D.isUnit_bridgeMap hu
    rwa [(hv'.mul hu').mul_right_eq_zero] at h1
  · right
    have h0 : incl (R := R) (R' := R') (v * s₂) = 0 := by
      calc incl (R := R) (R' := R') (v * s₂) = incl v * b := by simp only [b, map_mul]
        _ = incl v * (b * ε) + b * (incl v * (1 - ε)) := by ring
        _ = 0 := by rw [hb, hkill, mul_zero, mul_zero, add_zero]
    have h1 := congrArg D.bridgeMap (incl_injective (R := R) (R' := R') (h0.trans (map_zero _).symm))
    rw [map_mul, map_zero] at h1
    exact (D.isUnit_bridgeMap hv).mul_right_eq_zero.mp h1

end BridgeData

/-! ### The prime case -/

section Prime

open SGPT.Unibranch

/-- A Noether normalization of a finitely generated domain whose generators vanish at a given
`ℂ`-point. -/
theorem exists_noether_at {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] (ev : R →ₐ[ℂ] ℂ) :
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] R), Function.Injective g ∧
      g.toRingHom.Finite ∧ ∀ i, ev (g (MvPolynomial.X i)) = 0 := by
  obtain ⟨d, g₀, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ R
  set c₀ : Fin d → ℂ := fun i => ev (g₀ (MvPolynomial.X i))
  refine ⟨d, g₀.comp (transl (-c₀)), ?_, ?_, ?_⟩
  · exact hinj.comp (Function.LeftInverse.injective (g := transl c₀) (transl_transl_neg c₀))
  · exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ fun q =>
      ⟨transl c₀ q, transl_neg_transl c₀ q⟩)
  · intro i
    simp only [AlgHom.comp_apply, transl_X, map_add, Pi.neg_apply, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes, map_neg, Algebra.algebraMap_self, RingHom.id_apply, c₀]
    ring

variable {n : ℕ}

/-- The maximal ideal of `ℂ[z] / p` at `c`. -/
abbrev ptIdeal (p : Ideal (MvPolynomial (Fin n) ℂ)) (c : Fin n → ℂ)
    (hc : ∀ q ∈ p, MvPolynomial.eval c q = 0) : Ideal (MvPolynomial (Fin n) ℂ ⧸ p) :=
  RingHom.ker (Ideal.Quotient.lift p (MvPolynomial.eval c) hc)

/-- **U3, prime case.** Let `p ⊆ ℂ[z]` be prime and `c ∈ V(p)`. If exactly one maximal ideal of
the normalization of `ℂ[z]/p` lies over the point `c`, then `p · ℂ⟦z - c⟧` is prime: the
completion of the local ring at `c` is a domain. -/
theorem isPrime_map_fpm (p : Ideal (MvPolynomial (Fin n) ℂ)) [hp : p.IsPrime] (c : Fin n → ℂ)
    (hc : ∀ q ∈ p, MvPolynomial.eval c q = 0)
    (huni : ∀ 𝔫₁ 𝔫₂ : Ideal (integralClosure (MvPolynomial (Fin n) ℂ ⧸ p)
        (FractionRing (MvPolynomial (Fin n) ℂ ⧸ p))), 𝔫₁.IsMaximal → 𝔫₂.IsMaximal →
      ptIdeal p c hc ≤ 𝔫₁.comap (algebraMap _ _) → ptIdeal p c hc ≤ 𝔫₂.comap (algebraMap _ _) →
      𝔫₁ = 𝔫₂) :
    (p.map (fpm c)).IsPrime := by
  classical
  set R := MvPolynomial (Fin n) ℂ ⧸ p
  set K := FractionRing R
  set R' := integralClosure R K
  set ev : R →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ p (MvPolynomial.aeval c) (fun q hq => by
    rw [MvPolynomial.aeval_eq_eval]; exact hc q hq)
  have hev : ∀ q, ev (Ideal.Quotient.mk p q) = MvPolynomial.eval c q := fun q => by
    change MvPolynomial.aeval c q = _
    exact congrFun (MvPolynomial.aeval_eq_eval c) q
  obtain ⟨d, g, hinj, hfin, hg0⟩ := exists_noether_at ev
  let : Algebra (MvPolynomial (Fin d) ℂ) R := g.toRingHom.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) R :=
    IsScalarTower.of_algebraMap_eq fun z => (g.commutes z).symm
  have : Module.Finite (MvPolynomial (Fin d) ℂ) R := hfin
  have : FaithfulSMul (MvPolynomial (Fin d) ℂ) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  -- the normalization
  have : Module.Finite R R' := finite_integralClosure_of_finiteType ℂ R
  have : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have : IsIntegrallyClosed R' := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    intro a b h
    have := congrArg (fun x : R' => (x : K)) h
    exact IsFractionRing.injective R K this)
  let : Algebra (MvPolynomial (Fin d) ℂ) R' :=
    ((algebraMap R R').comp (algebraMap (MvPolynomial (Fin d) ℂ) R)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) ℂ) R R' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) R' := IsScalarTower.of_algebraMap_eq fun z => by
    apply Subtype.ext
    change algebraMap ℂ K z = algebraMap R K (algebraMap (MvPolynomial (Fin d) ℂ) R
      (algebraMap ℂ _ z))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have : Module.Finite (MvPolynomial (Fin d) ℂ) R' := Module.Finite.trans R R'
  have : FaithfulSMul (MvPolynomial (Fin d) ℂ) R' :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin d) ℂ) R R']
      exact (FaithfulSMul.algebraMap_injective R R').comp hinj)
  -- the bridge data
  choose y hy using fun i => Ideal.Quotient.mk_surjective (I := p)
    (algebraMap (MvPolynomial (Fin d) ℂ) R (MvPolynomial.X i))
  let D : BridgeData n d R :=
    { φ := Ideal.Quotient.mkₐ ℂ p
      surj := Ideal.Quotient.mk_surjective
      c := c
      hc := fun q hq => hc q (Ideal.Quotient.eq_zero_iff_mem.mp hq)
      y := y
      hy := hy
      hy0 := fun i => by rw [← hev, hy]; exact hg0 i }
  have hmR : D.mR = ptIdeal p c hc := by
    ext r
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp only [BridgeData.mR, RingHom.mem_ker]
    exact Iff.of_eq (congrArg (· = (0 : ℂ)) (D.evR_φ q))
  have hdom : IsDomain D.B := D.isDomain_B (by rw [hmR]; exact huni)
  have hIT : D.IT = p.map (fpm c) := by
    simp only [BridgeData.IT, D]
    erw [Ideal.Quotient.mkₐ_ker ℂ p]
  rw [← hIT]
  exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom

end Prime

end

end SGPT.Unibranch.UnibAlg
