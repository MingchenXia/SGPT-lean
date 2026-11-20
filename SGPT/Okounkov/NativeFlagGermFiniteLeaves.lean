import SGPT.Okounkov.NativeFlagGermFractionLeaves
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- The actual complex algebra on the LOCAL original meromorphic-germ
field, through the literal original constant-germ and fraction injections. -/
@[instance_reducible]
def originalFlagGermFractionComplexAlgebra {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F) :
    Algebra ℂ (FractionRing (NativeHolGerm n F.carrier x.1)) :=
  ((algebraMap (NativeHolGerm n F.carrier x.1)
    (FractionRing (NativeHolGerm n F.carrier x.1))).comp NativeHolGerm.constHom).toAlgebra

section LinearAlgebra

variable {C E W D : Type*} [Field C] [Field E] [Algebra C E]
  [AddCommGroup W] [Module C W]
  [LinearOrderedAddCommMonoidWithTop D] [Nontrivial D]

omit [Nontrivial D] in
private theorem scalar_value (v : AddValuation E D) (ι : W →ₗ[C] E)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0)
    (c : C) (hc : c ≠ 0) (s : W) : v (ι (c • s)) = v (ι s) := by
  rw [map_smul, Algebra.smul_def, v.map_mul, htrivial c hc, zero_add]

omit [Nontrivial D] in
private theorem unique_min_sum {I : Type*} [DecidableEq I]
    (v : AddValuation E D) (s : Finset I) (f : I → E) {i : I}
    (hi : i ∈ s) (hfinite : v (f i) ≠ ⊤)
    (hmin : ∀ j ∈ s, j ≠ i → v (f i) < v (f j)) :
    v (∑ j ∈ s, f j) = v (f i) := by
  have hrest : v (f i) < v (∑ j ∈ s.erase i, f j) := by
    apply v.map_lt_sum' (lt_top_iff_ne_top.mpr hfinite)
    intro j hj
    exact hmin j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1
  rw [← Finset.sum_erase_add s f hi, add_comm]
  exact v.map_add_eq_of_lt_left hrest

private theorem independent_of_distinct_values {I : Type*}
    (v : AddValuation E D) (ι : W →ₗ[C] E) (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0)
    (u : I → W) (hu : ∀ i, u i ≠ 0)
    (hvalue : Function.Injective (fun i => v (ι (u i)))) : LinearIndependent C u := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter (fun j => g j ≠ 0)
  have hti : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image t (fun j => v (ι (u j))) ⟨i, hti⟩
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hsumt : ∑ l ∈ t, g l • u l = 0 := by
    change ∑ l ∈ s.filter (fun l => g l ≠ 0), g l • u l = 0
    rw [Finset.sum_filter]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro l _hl
    split_ifs with h
    · rfl
    · simp only [not_not] at h
      simp [h]
  have hjfinite : v (ι (g j • u j)) ≠ ⊤ := by
    rw [scalar_value v ι htrivial _ hgj]
    rw [v.ne_top_iff]
    intro hz
    exact hu j (hι (hz.trans (map_zero _).symm))
  have hsmall : ∀ l ∈ t, l ≠ j → v (ι (g j • u j)) < v (ι (g l • u l)) := by
    intro l hl hlj
    have hgl : g l ≠ 0 := (Finset.mem_filter.mp hl).2
    rw [scalar_value v ι htrivial _ hgj, scalar_value v ι htrivial _ hgl]
    exact lt_of_le_of_ne (hjmin l hl) (fun heq => hlj (hvalue heq.symm))
  have hval := unique_min_sum v t (fun l => ι (g l • u l)) hj hjfinite hsmall
  rw [← map_sum, hsumt, map_zero, v.map_zero] at hval
  exact hjfinite hval.symm

private def nonzeroValues (v : AddValuation E D) (ι : W →ₗ[C] E) : Set D :=
  {a | ∃ s : W, s ≠ 0 ∧ v (ι s) = a}

private def valueRepresentative (v : AddValuation E D) (ι : W →ₗ[C] E)
    (a : nonzeroValues v ι) : W := Classical.choose a.property

omit [Nontrivial D] in
private theorem valueRepresentative_spec (v : AddValuation E D) (ι : W →ₗ[C] E)
    (a : nonzeroValues v ι) :
    valueRepresentative v ι a ≠ 0 ∧ v (ι (valueRepresentative v ι a)) = a.1 :=
  Classical.choose_spec a.property

private theorem representatives_independent (v : AddValuation E D) (ι : W →ₗ[C] E)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0) :
    LinearIndependent C (valueRepresentative v ι) := by
  apply independent_of_distinct_values v ι hι htrivial
  · intro a
    exact (valueRepresentative_spec v ι a).1
  · intro a b hab
    change v (ι (valueRepresentative v ι a)) = v (ι (valueRepresentative v ι b)) at hab
    rw [(valueRepresentative_spec v ι a).2, (valueRepresentative_spec v ι b).2] at hab
    exact Subtype.ext hab

private theorem values_finite [FiniteDimensional C W]
    (v : AddValuation E D) (ι : W →ₗ[C] E) (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0) :
    (nonzeroValues v ι).Finite := by
  let : Finite (nonzeroValues v ι) := (representatives_independent v ι hι htrivial).finite
  exact Set.finite_def.mpr ⟨Fintype.ofFinite (nonzeroValues v ι)⟩

omit [Nontrivial D] in
private theorem span_of_complete_values {I : Type*} [Fintype I]
    (v : AddValuation E D) (ι : W →ₗ[C] E) (u : I → W) (hu : ∀ i, u i ≠ 0)
    (hcomplete : ∀ s : W, s ≠ 0 → ∃ i, v (ι s) = v (ι (u i)))
    (hcancel : ∀ s t : W, s ≠ 0 → t ≠ 0 → v (ι s) = v (ι t) →
      ∃ c : C, c ≠ 0 ∧ v (ι s) < v (ι (s + c • t))) :
    Submodule.span C (Set.range u) = ⊤ := by
  classical
  let S := Submodule.span C (Set.range u)
  let upper (s : W) := Finset.univ.filter (fun i => v (ι s) < v (ι (u i)))
  let count (s : W) := (upper s).card
  have hmem : ∀ N : ℕ, ∀ s : W, count s = N → s ∈ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro s hN
        by_cases hs : s = 0
        · simpa only [hs] using S.zero_mem
        obtain ⟨i, hi⟩ := hcomplete s hs
        obtain ⟨c, _hc, hinc⟩ := hcancel s (u i) hs (hu i) hi
        let t := s + c • u i
        have hui : u i ∈ S := Submodule.subset_span (Set.mem_range_self i)
        have ht : t ∈ S := by
          by_cases htzero : t = 0
          · simpa only [htzero] using S.zero_mem
          obtain ⟨j, hj⟩ := hcomplete t htzero
          have hsub : upper t ⊆ upper s := by
            intro k hk
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              hinc.trans (Finset.mem_filter.mp hk).2⟩
          have hne : upper t ≠ upper s := by
            intro heq
            have hjmem : j ∈ upper s :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc.trans_eq hj⟩
            have hjt : j ∈ upper t := heq.symm ▸ hjmem
            have hbad := (Finset.mem_filter.mp hjt).2
            exact (lt_irrefl _ ) (hbad.trans_eq hj.symm)
          have hlt : count t < N :=
            (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)).trans_eq hN
          exact ih (count t) hlt t rfl
        have hsub := S.sub_mem ht (S.smul_mem c hui)
        simpa only [t, add_sub_cancel_right] using hsub
  apply top_unique
  intro s _hs
  exact hmem (count s) s rfl

private theorem values_card_eq_finrank [FiniteDimensional C W]
    (v : AddValuation E D) (ι : W →ₗ[C] E) (hι : Function.Injective ι)
    (htrivial : ∀ c : C, c ≠ 0 → v (algebraMap C E c) = 0)
    (hcancel : ∀ s t : W, s ≠ 0 → t ≠ 0 → v (ι s) = v (ι t) →
      ∃ c : C, c ≠ 0 ∧ v (ι s) < v (ι (s + c • t))) :
    Nat.card (nonzeroValues v ι) = Module.finrank C W := by
  classical
  let : Fintype (nonzeroValues v ι) := (values_finite v ι hι htrivial).fintype
  have hcomplete : ∀ s : W, s ≠ 0 → ∃ a : nonzeroValues v ι,
      v (ι s) = v (ι (valueRepresentative v ι a)) := by
    intro s hs
    let a : nonzeroValues v ι := ⟨v (ι s), s, hs, rfl⟩
    exact ⟨a, (valueRepresentative_spec v ι a).2.symm⟩
  have hspan := span_of_complete_values v ι (valueRepresentative v ι)
    (fun a => (valueRepresentative_spec v ι a).1) hcomplete hcancel
  let b := Module.Basis.mk (representatives_independent v ι hι htrivial) hspan.ge
  simpa only [Nat.card_eq_fintype_card] using (Module.finrank_eq_card_basis b).symm

end LinearAlgebra

section OriginalValues

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)

local instance complexAlgebra : Algebra ℂ (FractionRing (NativeHolGerm n F.carrier x.1)) :=
  originalFlagGermFractionComplexAlgebra F x

theorem originalFlagGermFractionValuation_scalar (c : ℂ) (hc : c ≠ 0) :
    originalFlagGermFractionValuation F x
      (algebraMap ℂ (FractionRing (NativeHolGerm n F.carrier x.1)) c) = 0 := by
  change originalFlagGermFractionValuation F x
    (algebraMap (NativeHolGerm n F.carrier x.1)
      (FractionRing (NativeHolGerm n F.carrier x.1)) (NativeHolGerm.constHom c)) = 0
  rw [originalFlagGermFractionValuation_algebraMap, originalFlagGermValuation_const F x c hc]

/-- The genuine nonzero value set of an actual complex subspace of the
original local fraction field; no values or representatives are supplied. -/
def originalFlagGermFractionValues
    (V : Submodule ℂ (FractionRing (NativeHolGerm n F.carrier x.1))) :
    Set (WithTop (Lex (Fin n → ℤ))) :=
  nonzeroValues (originalFlagGermFractionValuation F x) V.subtype

theorem originalFlagGermFractionValues_finite
    (V : Submodule ℂ (FractionRing (NativeHolGerm n F.carrier x.1))) [FiniteDimensional ℂ V] :
    (originalFlagGermFractionValues F x V).Finite :=
  values_finite (originalFlagGermFractionValuation F x) V.subtype Subtype.val_injective
    (originalFlagGermFractionValuation_scalar F x)

/-- Actual scalar cancellation makes the actual distinct-value
representatives span, so the genuine finite value count is the dimension.
Neither a basis nor a leaf/count certificate is an input. -/
theorem originalFlagGermFractionValues_card_eq_finrank
    (V : Submodule ℂ (FractionRing (NativeHolGerm n F.carrier x.1))) [FiniteDimensional ℂ V] :
    Nat.card (originalFlagGermFractionValues F x V) = Module.finrank ℂ V := by
  apply values_card_eq_finrank (originalFlagGermFractionValuation F x) V.subtype
    Subtype.val_injective (originalFlagGermFractionValuation_scalar F x)
  intro s t hs ht hvalue
  have hsfield : (s : FractionRing (NativeHolGerm n F.carrier x.1)) ≠ 0 := by
    intro hz
    exact hs (Subtype.ext hz)
  have htfield : (t : FractionRing (NativeHolGerm n F.carrier x.1)) ≠ 0 := by
    intro hz
    exact ht (Subtype.ext hz)
  obtain ⟨c, hc, hcancel⟩ := exists_originalFlagGermFraction_scalar_cancel F x s t hsfield htfield hvalue
  refine ⟨c, hc, ?_⟩
  rw [map_add, map_smul, Algebra.smul_def]
  change originalFlagGermFractionValuation F x s < originalFlagGermFractionValuation F x
    ((s : FractionRing (NativeHolGerm n F.carrier x.1)) +
      algebraMap (NativeHolGerm n F.carrier x.1)
        (FractionRing (NativeHolGerm n F.carrier x.1)) (NativeHolGerm.constHom c) * t)
  exact hcancel

end OriginalValues

end SGPT.Okounkov
