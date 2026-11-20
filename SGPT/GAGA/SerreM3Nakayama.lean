import SGPT.GAGA.SerreM3Global

/-!
# Serre's theorems on `ℙᴺ`, part 12: Nakayama's lemma for germ modules

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), milestone M4.2.

`generation_nakayama`: let `I ⊆ M` be coherent at `x`, `h` holomorphic with `h(x) = 0`, and
`σ_k` members of `M_x`. If every member of `M_x` is `∑ c_k σ_k` modulo `I_x + h M_x`, then every
member of `M_x` is `∑ c_k σ_k` modulo `I_x`. This is Nakayama's lemma for the finitely generated
module of germs `M_x` over the local ring `𝒪_x` (Mathlib `le_of_le_smul_of_le_jacobson_bot`,
TN's local ring of holomorphic germs).

Blueprint: `claude-serre-m34.tex`, node `claude-serre-m34:nakayama`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.Foundations.Analysis.Pending.OkaGermBridge
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

variable {n : ℕ} {ι μ : Type} [Fintype ι] [Fintype μ]

/-- Germs of `w + h b'`. -/
theorem germTuple_add_mul {x : EuclideanSpace ℂ (Fin n)} {w b : ι → EuclideanSpace ℂ (Fin n) → ℂ}
    {h : EuclideanSpace ℂ (Fin n) → ℂ} (hw : HolTupleAt w x) (hb : HolTupleAt b x)
    (hh : HolAt h x) :
    germTuple x (fun j z => w j z + h z * b j z) = germTuple x w + germAt x h • germTuple x b := by
  funext j
  simp only [germTuple, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [germAt_add (hw j) (hh.mul (hb j)), germAt_mul hh (hb j)]

/-- **Nakayama's lemma for germ modules.** -/
theorem generation_nakayama {M I : GermModule (EuclideanSpace ℂ (Fin n)) ι}
    {x : EuclideanSpace ℂ (Fin n)} (hM : M.CoherentAt x) (hI : I.CoherentAt x)
    {h : EuclideanSpace ℂ (Fin n) → ℂ} (hh : HolAt h x) (hx : h x = 0)
    {σ : μ → ι → EuclideanSpace ℂ (Fin n) → ℂ} (hσ : ∀ k, M.mem x (σ k))
    (H : ∀ a, M.mem x a → ∃ (c : μ → EuclideanSpace ℂ (Fin n) → ℂ)
      (b b' : ι → EuclideanSpace ℂ (Fin n) → ℂ), (∀ k, HolAt (c k) x) ∧ I.mem x b ∧
        M.mem x b' ∧ ∀ j, a j =ᶠ[𝓝 x] fun z => ∑ k, c k z * σ k j z + b j z + h z * b' j z) :
    ∀ a, M.mem x a → ∃ c : μ → EuclideanSpace ℂ (Fin n) → ℂ, (∀ k, HolAt (c k) x) ∧
      I.mem x (fun j z => a j z - ∑ k, c k z * σ k j z) := by
  classical
  obtain ⟨μM, _, τM, hτM, hMmem⟩ := hM.mem_iff
  obtain ⟨μI, _, τI, hτI, hImem⟩ := hI.mem_iff
  have hσhol : ∀ k j, HolAt (σ k j) x := fun k => hM.holTupleAt_of_mem (hσ k)
  have hcomb : ∀ (k : μ ⊕ μI) j, HolAt (Sum.elim σ τI k j) x := by
    rintro (k | k) j
    · exact hσhol k j
    · exact hτI k j
  set S := germSpan x τM with hSdef
  set T := germSpan x (Sum.elim σ τI) with hTdef
  set J : Ideal (HolGerm (EuclideanSpace ℂ (Fin n))) := Ideal.span {germAt x h} with hJdef
  have hMgerm : ∀ a, M.mem x a ↔ HolTupleAt a x ∧ germTuple x a ∈ S := fun a =>
    (hMmem a).trans (isCombinationAt_iff_germTuple_mem hτM)
  -- every generator of `M_x` lies in `T + J • S`
  have hST : S ≤ T ⊔ J • S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, rfl⟩
    have hl : M.mem x (τM l) := (hMmem _).2 (isCombinationAt_gen τM x l)
    obtain ⟨c, b, b', hc, hb, hb', heq⟩ := H _ hl
    have hbhol : HolTupleAt b x := hI.holTupleAt_of_mem hb
    have hb'hol : HolTupleAt b' x := hM.holTupleAt_of_mem hb'
    set w : ι → EuclideanSpace ℂ (Fin n) → ℂ := fun j z => ∑ k, c k z * σ k j z + b j z
      with hwdef
    have hwhol : HolTupleAt w x := fun j =>
      (HolAt.fintype_sum fun k => (hc k).mul (hσhol k j)).add (hbhol j)
    have hwT : germTuple x w ∈ T := by
      refine ((isCombinationAt_iff_germTuple_mem hcomb).1 ?_).2
      refine GermModule.isCombinationAt_sumElim_iff.2 ⟨fun j z => ∑ k, c k z * σ k j z, b,
        ⟨c, hc, fun j => EventuallyEq.rfl⟩, (hImem b).1 hb, fun j => EventuallyEq.rfl⟩
    have hgerm : germTuple x (τM l) = germTuple x w + germAt x h • germTuple x b' := by
      rw [← germTuple_add_mul hwhol hb'hol hh]
      funext j
      exact (germAt_eq_germAt_iff (hτM l j) ((hwhol j).add (hh.mul (hb'hol j)))).2 (heq j)
    show germTuple x (τM l) ∈ T ⊔ J • S
    rw [hgerm]
    exact Submodule.add_mem_sup hwT (Submodule.smul_mem_smul (Ideal.subset_span rfl)
      ((hMgerm b').1 hb').2)
  -- Nakayama
  have hJ : J ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hJdef, Ideal.span_le,
      Set.singleton_subset_iff]
    have := (germAt_mem_maximalIdeal_pow_iff hh 1).2 fun k hk => by
      obtain rfl : k = 0 := by omega
      ext v
      simp [hx]
    simpa using this
  have hSle : S ≤ T :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (Submodule.fg_span (Set.finite_range _)) hJ hST
  intro a ha
  obtain ⟨hahol, haS⟩ := (hMgerm a).1 ha
  have hca := (isCombinationAt_iff_germTuple_mem hcomb).2 ⟨hahol, hSle haS⟩
  obtain ⟨b, e, ⟨c, hc, hcb⟩, he, hbe⟩ := GermModule.isCombinationAt_sumElim_iff.1 hca
  refine ⟨c, hc, hI.congr_mem ((hImem e).2 he) fun j => ?_⟩
  filter_upwards [hbe j, hcb j] with z hz1 hz2
  rw [hz1, hz2]
  ring

end SGPT.GAGA.PN
