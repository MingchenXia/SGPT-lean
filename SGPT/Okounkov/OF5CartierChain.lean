import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Height
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Local defining equations of a flag of subvarieties smooth at a point

Source: chapter *The theory of Okounkov bodies*, `def:admfl` and the definition of `ν_{Y•}`:
*an admissible flag is a flag of subvarieties `X = Y₀ ⊇ Y₁ ⊇ ⋯ ⊇ Yₙ` such that `Yᵢ` is
irreducible of codimension `i` and is smooth at the point `Yₙ`* … *after localizing around `Yₙ`,
choose a local defining equation `tᵢ` of `Yᵢ` in `Yᵢ₋₁`*.

The existence of the local defining equations is the statement that, near the point `Yₙ`, every
`Yᵢ₊₁` is a Cartier divisor in `Yᵢ`. We prove it in commutative algebra, from smoothness alone:

* `exists_span_eq_ker_of_formallySmooth` (one step): let `A → B` be a surjection of local rings,
  `A` Noetherian, both formally smooth over `k`, with `Ω_{A/k}` finite free. Then `Ω_{B/k}` is
  finite free and `rank Ω_{A/k} = c + rank Ω_{B/k}`, where `c = dim κ ⊗ I/I²` (`I` the kernel,
  `κ` the residue field of `B`): the conormal sequence `I/I² → B ⊗ Ω_A → Ω_B → 0` stays exact
  and injective after `κ ⊗ -` by smoothness of `B`
  (`Algebra.FormallySmooth.iff_injective_lTensor_residueField`). Moreover `c = 0` forces `I = 0`
  and `c = 1` forces `I` to be principal (Nakayama).
* `exists_localEquations` (the chain): if `R` is local Noetherian and formally smooth over `k`
  with `Ω_{R/k}` free of rank at most `n`, and `P 0 ⊊ P 1 ⊊ ⋯ ⊊ P n` are primes with every
  `R ⧸ P i` formally smooth over `k`, then the `n` conormal ranks `cᵢ ≥ 1` add up to at most
  `n`, so each `cᵢ = 1` and `P (i+1) = P i + (tᵢ)` for some `tᵢ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace SGPT.Okounkov.OF5

open TensorProduct KaehlerDifferential Module IsLocalRing

section Step

variable {k : Type*} [CommRing k] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- **One step of the flag**: the conormal rank `c` of a surjection `A → B` of formally smooth
local algebras drops the rank of the differentials by `c`; `c = 0` only for an isomorphism and
`c = 1` gives a principal kernel. -/
theorem exists_span_eq_ker_of_formallySmooth (h : Function.Surjective (algebraMap A B))
    [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth k B]
    [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] :
    Module.Free B Ω[B⁄k] ∧ Module.Finite B Ω[B⁄k] ∧
      ∃ c : ℕ, finrank A Ω[A⁄k] = c + finrank B Ω[B⁄k] ∧
        (c = 0 → RingHom.ker (algebraMap A B) = ⊥) ∧
        (c = 1 → ∃ t : A, RingHom.ker (algebraMap A B) = Ideal.span {t}) := by
  classical
  let P : Algebra.Extension k B :=
    { Ring := A, σ := Function.surjInv h, algebraMap_σ := Function.surjInv_eq h }
  let κ := ResidueField B
  have : Algebra.FormallySmooth k P.Ring := inferInstanceAs (Algebra.FormallySmooth k A)
  have : Module.Free P.Ring Ω[P.Ring⁄k] := inferInstanceAs (Module.Free A Ω[A⁄k])
  have : Module.Finite P.Ring Ω[P.Ring⁄k] := inferInstanceAs (Module.Finite A Ω[A⁄k])
  have hfg : P.ker.FG := (IsNoetherian.noetherian (R := A) (M := A) _)
  have hinj : Function.Injective (P.cotangentComplex.lTensor κ) :=
    (Algebra.FormallySmooth.iff_injective_lTensor_residueField P hfg).mp inferInstance
  -- finiteness and freeness
  have : Module.Finite B P.CotangentSpace := inferInstanceAs (Module.Finite B (B ⊗[A] Ω[A⁄k]))
  have : Module.Free B P.CotangentSpace := inferInstanceAs (Module.Free B (B ⊗[A] Ω[A⁄k]))
  have hΩfin : Module.Finite B Ω[B⁄k] := Module.Finite.of_surjective _ P.toKaehler_surjective
  have hΩfree : Module.Free B Ω[B⁄k] := Module.free_of_flat_of_isLocalRing
  have : Module.Finite A P.ker := Module.Finite.of_fg hfg
  have : Module.Finite A P.Cotangent :=
    Module.Finite.of_surjective _ Algebra.Extension.Cotangent.mk_surjective
  have hCfin : Module.Finite B P.Cotangent := Module.Finite.of_restrictScalars_finite A B _
  refine ⟨hΩfree, hΩfin, finrank κ (κ ⊗[B] P.Cotangent), ?_, ?_, ?_⟩
  · -- the rank identity
    have hex : Function.Exact (P.cotangentComplex.lTensor κ) (P.toKaehler.lTensor κ) :=
      lTensor_exact κ P.exact_cotangentComplex_toKaehler P.toKaehler_surjective
    have hsurj : Function.Surjective (P.toKaehler.lTensor κ) :=
      LinearMap.lTensor_surjective κ P.toKaehler_surjective
    let φ : κ ⊗[B] P.Cotangent →ₗ[κ] κ ⊗[B] P.CotangentSpace := P.cotangentComplex.baseChange κ
    let ψ : κ ⊗[B] P.CotangentSpace →ₗ[κ] κ ⊗[B] Ω[B⁄k] := P.toKaehler.baseChange κ
    have hφ : (φ : _ → _) = P.cotangentComplex.lTensor κ := LinearMap.baseChange_eq_ltensor _
    have hψ : (ψ : _ → _) = P.toKaehler.lTensor κ := LinearMap.baseChange_eq_ltensor _
    have hφinj : Function.Injective φ := by rw [hφ]; exact hinj
    have hψsurj : Function.Surjective ψ := by rw [hψ]; exact hsurj
    have hφψ : LinearMap.ker ψ = LinearMap.range φ := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.mem_range]
      have := hex x
      rw [← hφ, ← hψ] at this
      exact this
    have hV : finrank κ (κ ⊗[B] P.CotangentSpace) = finrank A Ω[A⁄k] := by
      rw [Module.finrank_baseChange]
      exact Module.finrank_baseChange
    have hW : finrank κ (κ ⊗[B] Ω[B⁄k]) = finrank B Ω[B⁄k] := Module.finrank_baseChange
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.range_eq_top.mpr hψsurj, finrank_top, hφψ, LinearMap.finrank_range_of_inj hφinj,
      hV, hW] at hrn
    omega
  · -- `c = 0`: the kernel vanishes
    intro hc
    have hsub : Subsingleton (κ ⊗[B] P.Cotangent) := Module.finrank_zero_iff.mp hc
    have hsubC : Subsingleton P.Cotangent := IsLocalRing.subsingleton_tensorProduct.mp hsub
    have hle : P.ker ≤ P.ker • P.ker := by
      intro x hx
      have h0 : Algebra.Extension.Cotangent.mk (⟨x, hx⟩ : P.ker) = 0 := Subsingleton.elim _ _
      rw [Algebra.Extension.Cotangent.mk_eq_zero_iff] at h0
      rwa [Ideal.smul_eq_mul, ← sq]
    have hne : P.ker ≠ ⊤ := by
      intro htop
      have h1 : (1 : A) ∈ P.ker := htop ▸ Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1
    exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot P.ker P.ker hfg hle
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact le_maximalIdeal hne)
  · -- `c = 1`: the kernel is principal
    intro hc
    -- a pure tensor `1 ⊗ x` spans `κ ⊗ I/I²`
    obtain ⟨x, hx⟩ : ∃ x : P.Cotangent, (1 : κ) ⊗ₜ[B] x ≠ 0 := by
      by_contra hall
      push Not at hall
      have : Subsingleton (κ ⊗[B] P.Cotangent) := by
        refine subsingleton_of_forall_eq 0 fun w => ?_
        induction w using TensorProduct.induction_on with
        | zero => rfl
        | tmul c y =>
          rw [← mul_one c, ← smul_eq_mul, ← smul_tmul', hall, smul_zero]
        | add u w hu hw => rw [hu, hw, add_zero]
      rw [Module.finrank_zero_of_subsingleton] at hc
      exact zero_ne_one hc
    have hspan := (finrank_eq_one_iff_of_nonzero' _ hx).mp hc
    have htop : Submodule.span B {x} = ⊤ := by
      rw [← IsLocalRing.map_tensorProduct_mk_eq_top, Submodule.map_span, Set.image_singleton,
        eq_top_iff]
      intro w _
      obtain ⟨c, rfl⟩ := hspan w
      obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective c
      rw [Submodule.mem_span_singleton]
      refine ⟨b, ?_⟩
      rw [TensorProduct.mk_apply, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
    obtain ⟨⟨t, ht⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    refine ⟨t, le_antisymm ?_ ?_⟩
    · -- Nakayama: `I ≤ (t) + I²`
      have hle : P.ker ≤ Ideal.span {t} ⊔ P.ker • P.ker := by
        intro y hy
        have hy' : Algebra.Extension.Cotangent.mk (⟨y, hy⟩ : P.ker) ∈ Submodule.span B
            {Algebra.Extension.Cotangent.mk (⟨t, ht⟩ : P.ker)} := htop ▸ Submodule.mem_top
        obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy'
        obtain ⟨a, rfl⟩ := h b
        rw [algebraMap_smul, ← LinearMap.map_smul, Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem]
          at hb
        rw [Submodule.mem_sup]
        refine ⟨a * t, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩, y - a * t, ?_, by ring⟩
        rw [Ideal.smul_eq_mul, ← sq, ← neg_mem_iff]
        simpa using hb
      have hne : P.ker ≠ ⊤ := by
        intro htop'
        have h1 : (1 : A) ∈ P.ker := htop' ▸ Submodule.mem_top
        rw [RingHom.mem_ker, map_one] at h1
        exact one_ne_zero h1
      exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact le_maximalIdeal hne) hle
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact ht

end Step

section Chain

variable {k : Type*} [CommRing k] {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Algebra k R]

omit [IsNoetherianRing R] in
/-- A quotient of a local ring by a prime ideal is local. -/
theorem quotient_isLocalRing (I : Ideal R) [I.IsPrime] : IsLocalRing (R ⧸ I) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

attribute [local instance] quotient_isLocalRing

/-- The algebra structure `R ⧸ I → R ⧸ J` for `I ≤ J`. -/
abbrev quotientQuotientAlgebra {I J : Ideal R} (h : I ≤ J) : Algebra (R ⧸ I) (R ⧸ J) :=
  (Ideal.Quotient.factor h).toAlgebra

/-- **Local defining equations of a flag smooth at a point.** Let `R` be a local Noetherian ring,
formally smooth over `k`, with `Ω_{R/k}` finite free of rank at most `n`, and let
`P 0 ⊊ P 1 ⊊ ⋯ ⊊ P n` be prime ideals with every `R ⧸ P i` formally smooth over `k`. Then every
`P (i+1)` is `P i + (t)` for some `t`. -/
theorem exists_localEquations (n : ℕ) (P : ℕ → Ideal R) [∀ i, (P i).IsPrime]
    (hmono : ∀ i < n, P i < P (i + 1))
    (hsm : ∀ i ≤ n, Algebra.FormallySmooth k (R ⧸ P i))
    [Algebra.FormallySmooth k R] [Module.Free R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    (hrank : finrank R Ω[R⁄k] ≤ n) :
    ∀ i < n, ∃ t : R, P (i + 1) = P i ⊔ Ideal.span {t} := by
  classical
  -- the step lemma for `R ⧸ P i → R ⧸ P (i+1)`
  have hstep : ∀ i < n, ∀ (_ : Module.Free (R ⧸ P i) Ω[(R ⧸ P i)⁄k])
      (_ : Module.Finite (R ⧸ P i) Ω[(R ⧸ P i)⁄k]),
      Module.Free (R ⧸ P (i + 1)) Ω[(R ⧸ P (i + 1))⁄k] ∧
        Module.Finite (R ⧸ P (i + 1)) Ω[(R ⧸ P (i + 1))⁄k] ∧
        ∃ c : ℕ, finrank (R ⧸ P i) Ω[(R ⧸ P i)⁄k] =
            c + finrank (R ⧸ P (i + 1)) Ω[(R ⧸ P (i + 1))⁄k] ∧ 1 ≤ c ∧
          (c = 1 → ∃ t : R, P (i + 1) = P i ⊔ Ideal.span {t}) := by
    intro i hi _ _
    let := quotientQuotientAlgebra (hmono i hi).le
    have : IsScalarTower k (R ⧸ P i) (R ⧸ P (i + 1)) :=
      IsScalarTower.of_algebraMap_eq fun x => rfl
    have := hsm i hi.le
    have := hsm (i + 1) hi
    have hsurj : Function.Surjective (algebraMap (R ⧸ P i) (R ⧸ P (i + 1))) :=
      Ideal.Quotient.factor_surjective (hmono i hi).le
    -- the kernel is the image of `P (i+1)`
    have hker : ∀ a : R, Ideal.Quotient.mk (P i) a ∈ RingHom.ker (algebraMap (R ⧸ P i)
        (R ⧸ P (i + 1))) ↔ a ∈ P (i + 1) := by
      intro a
      rw [RingHom.mem_ker]
      change Ideal.Quotient.factor (hmono i hi).le (Ideal.Quotient.mk (P i) a) = 0 ↔ _
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨hfree, hfin, c, hc, hc0, hc1⟩ :=
      exists_span_eq_ker_of_formallySmooth (k := k) hsurj
    refine ⟨hfree, hfin, c, hc, ?_, ?_⟩
    · -- the inclusion is strict
      by_contra hlt
      have h0 := hc0 (by omega)
      obtain ⟨a, ha, hna⟩ := SetLike.exists_of_lt (hmono i hi)
      apply hna
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0, hker]
      exact ha
    · intro h1
      obtain ⟨t, ht⟩ := hc1 h1
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
      refine ⟨t, le_antisymm ?_ (sup_le (hmono i hi).le ?_)⟩
      · intro a ha
        have hmem : Ideal.Quotient.mk (P i) a ∈ Ideal.span {Ideal.Quotient.mk (P i) t} := by
          rw [← ht, hker]
          exact ha
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
        rw [Submodule.mem_sup]
        refine ⟨a - d * t, ?_, d * t, Ideal.mem_span_singleton'.mpr ⟨d, rfl⟩, by ring⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, sub_self]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← hker, ht]
        exact Ideal.mem_span_singleton_self _
  -- the base step `R → R ⧸ P 0`
  have hbase : Module.Free (R ⧸ P 0) Ω[(R ⧸ P 0)⁄k] ∧ Module.Finite (R ⧸ P 0) Ω[(R ⧸ P 0)⁄k] ∧
      finrank (R ⧸ P 0) Ω[(R ⧸ P 0)⁄k] ≤ finrank R Ω[R⁄k] := by
    have := hsm 0 (Nat.zero_le n)
    obtain ⟨hfree, hfin, c, hc, -, -⟩ :=
      exists_span_eq_ker_of_formallySmooth (k := k) (A := R) (B := R ⧸ P 0)
        Ideal.Quotient.mk_surjective
    exact ⟨hfree, hfin, by omega⟩
  -- induction along the chain: the ranks and the conormal ranks
  have hind : ∀ i ≤ n, Module.Free (R ⧸ P i) Ω[(R ⧸ P i)⁄k] ∧
      Module.Finite (R ⧸ P i) Ω[(R ⧸ P i)⁄k] ∧
      i + finrank (R ⧸ P i) Ω[(R ⧸ P i)⁄k] ≤ finrank (R ⧸ P 0) Ω[(R ⧸ P 0)⁄k] ∧
      (∀ j < i, ∃ c : ℕ, finrank (R ⧸ P j) Ω[(R ⧸ P j)⁄k] =
          c + finrank (R ⧸ P (j + 1)) Ω[(R ⧸ P (j + 1))⁄k] ∧ 1 ≤ c ∧
        (c = 1 → ∃ t : R, P (j + 1) = P j ⊔ Ideal.span {t})) := by
    intro i hi
    induction i with
    | zero => exact ⟨hbase.1, hbase.2.1, by omega, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ i ih =>
      obtain ⟨hfree, hfin, hle, hprev⟩ := ih (by omega)
      obtain ⟨hfree', hfin', c, hc, hc1, hct⟩ := hstep i (by omega) hfree hfin
      refine ⟨hfree', hfin', by omega, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hprev j hj
      · exact ⟨c, hc, hc1, hct⟩
  obtain ⟨-, -, -, hall⟩ := hind n le_rfl
  intro i hi
  obtain ⟨c, hc, hc1, hct⟩ := hall i hi
  apply hct
  -- if `cᵢ ≥ 2`, the total rank drop exceeds `n`
  by_contra hne
  have hc2 : 2 ≤ c := by omega
  -- the drop before `i` is at least `i`, after `i+1` at least `n - i - 1`
  have hbefore : ∀ j ≤ i, j + finrank (R ⧸ P j) Ω[(R ⧸ P j)⁄k] ≤
      finrank (R ⧸ P 0) Ω[(R ⧸ P 0)⁄k] := fun j hj => ((hind j (by omega)).2.2.1)
  have hafter : ∀ j, i + 1 + j ≤ n → j + finrank (R ⧸ P (i + 1 + j)) Ω[(R ⧸ P (i + 1 + j))⁄k] ≤
      finrank (R ⧸ P (i + 1)) Ω[(R ⧸ P (i + 1))⁄k] := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨d, hd, hd1, -⟩ := hall (i + 1 + j) (by omega)
      have := ih (by omega)
      rw [show i + 1 + (j + 1) = i + 1 + j + 1 by ring]
      omega
  have h1 := hbefore i le_rfl
  have h2 := hafter (n - (i + 1)) (by omega)
  have h3 := hbase.2.2
  omega

end Chain

end SGPT.Okounkov.OF5
