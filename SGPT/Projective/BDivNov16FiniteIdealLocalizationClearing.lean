import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Finiteness.Defs

/-! Blueprint first: BDivNov16FiniteIdealLocalizationClearing.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.BDivNov16

theorem finiteIdeal_exists_uniform_localization_denominator
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I J : Ideal R) (hI : I.FG)
    (hIJ : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) :
    ∃ t ∈ M, ∀ x ∈ I, t * x ∈ J := by
  classical
  obtain ⟨s,hs⟩ := hI
  have hf : ∀ (v : Finset R), (∀ x ∈ v, x ∈ I) →
      ∃ t ∈ M, ∀ x ∈ v, t * x ∈ J := by
    intro v
    induction v using Finset.induction_on with
    | empty => exact fun _ => ⟨1,M.one_mem,by simp⟩
    | @insert x v hx ih =>
      intro hmem
      obtain ⟨u,hu,hux⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J x).mp
        (hIJ (Ideal.mem_map_of_mem _ (hmem x (Finset.mem_insert_self x v))))
      obtain ⟨t,ht,htv⟩ := ih (fun z hz => hmem z (Finset.mem_insert_of_mem hz))
      refine ⟨u*t,M.mul_mem hu ht,?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa [mul_assoc,mul_comm,mul_left_comm] using J.mul_mem_left t hux
      · simpa [mul_assoc] using J.mul_mem_left u (htv z hz)
  obtain ⟨t,ht,hts⟩ := hf s (fun x hx => hs ▸ Ideal.subset_span hx)
  refine ⟨t,ht,?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem z hz => exact hts z hz
  | zero => simp
  | add z w _ _ hz hw => simpa [mul_add] using J.add_mem hz hw
  | smul r z _ hz => simpa [smul_eq_mul,mul_assoc,mul_left_comm] using J.mul_mem_left r hz
end SGPT.Projective.BDivNov16
