import SGPT.GAGA.SerreM3Lift

/-!
# Serre's theorems on `ℙᴺ`, part 11: global sections of `𝒮_d` are global tuples

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), milestone M4.2.

`exists_global_lift`: let `M ⊇ I_{L_d} 𝒪^ι` be coherent (`d ≤ N`) and `m ≥ -d`. Every
`0`-cocycle of `(M/I_{L_d})(m)` for the closed cover `K(ρ)` (sections `g_i` of `M(m)` near
`K_i(ρ)` agreeing modulo `I_{L_d}` on overlaps) is, modulo `I_{L_d}`, one global tuple `P`,
holomorphic and homogeneous of degree `m` on `ℂ^{N+1} ∖ 0`, with germs in `M`. This is the
surjectivity `Ȟ⁰(𝒪(m)^ι) → Ȟ⁰(𝒪_{L_d}(m)^ι)` (`cechHMap_free_OL_surjective`) together with the
gluing of `0`-cocycles of `𝒪^ι(m)` (`cechAug_free_surjective`, lane SERRE-PN).

Blueprint: `claude-serre-m34.tex`, node `claude-serre-m34:lift`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A homogeneous section over the whole cone `ℂ^{N+1} ∖ 0` is homogeneous on it. -/
theorem isHomOn_puncture_of_isHomSection {P : GermModule (ConeSpace N) ι} {m : ℤ} {ρ : ℝ}
    {a : ι → ConeSpace N → ℂ} (ha : IsHomSection P m (coverSet ρ ∅) a) :
    IsHomOn (puncture (ConeSpace N)) m a := by
  obtain ⟨U, hKU, hU, -⟩ := ha
  rw [coverSet_empty] at hKU
  have hUeq : U = puncture (ConeSpace N) := Set.Subset.antisymm hU.subset hKU
  exact hUeq ▸ hU

/-- **Global lifts of `0`-cocycles of subsheaves of `𝒪_{L_d}^ι`.** -/
theorem exists_global_lift {ρ : ℝ} (hρ : 1 ≤ ρ) {d : ℕ} (hd : d ≤ N)
    {M : GermModule (ConeSpace N) ι} (hM : M.IsCoherentOn (puncture (ConeSpace N)))
    (hIM : (Idm d ι).LeOn M (puncture (ConeSpace N))) {m : ℤ} (hm : -(d : ℤ) ≤ m)
    (g : Fin (N + 1) → ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection M m (coverSet ρ {i}) (g i))
    (hcoc : ∀ i k, IsHomSection (Idm d ι) m (coverSet ρ {i, k}) (g k - g i)) :
    ∃ P : ι → ConeSpace N → ℂ, IsHomOn (puncture (ConeSpace N)) m P ∧
      (∀ y : ConeSpace N, y ≠ 0 → M.mem y P) ∧
      ∀ i, IsHomSection (Idm d ι) m (coverSet ρ {i}) (P - g i) := by
  classical
  have hg' : ∀ i, IsHomSection (OL (N := N) d ι).M m (coverSet ρ {i}) (g i) := fun i =>
    (hg i).le (GermModule.LeOn.top hM)
  set z := zeroCocycle (F := OL (N := N) d ι) g hg' hcoc with hzdef
  obtain ⟨y, hy⟩ := cechHMap_free_OL_surjective (ι := ι) hρ (N - d) d (by omega) m hm
    (cechClass _ 0 z)
  obtain ⟨w, rfl⟩ := cechClass_surjective _ 0 y
  obtain ⟨gb, rfl⟩ := cechAug_free_surjective (N := N) (ι := ι) hρ m w
  induction gb using Submodule.Quotient.induction_on with
  | _ a =>
  obtain ⟨P, hP⟩ : ∃ P : ι → ConeSpace N → ℂ, P = a.1 := ⟨_, rfl⟩
  have hy' := (cechHMap_cechClass (coverHom' (toOL (N := N) (ι := ι) d) isHomMatrix_idMatrix
    (add_zero m) ρ) 0 _).symm.trans hy
  have hz := cechClass_injective_zero _ hy'
  have hcomp : ∀ i, IsHomSection (Idm d ι) m (coverSet ρ {i}) (P - g i) := by
    intro i
    have hi := congrArg (fun t : LinearMap.ker (cechDq (coverSystem (OL (N := N) d ι) m ρ) 0) =>
      t.1.1 {i}) hz
    have h2 := (sectionMk_eq_iff (OL (N := N) d ι) ⟨matLin (idMatrix ι) a.1, _⟩ ⟨g i, hg' i⟩).1
      (hi.trans (zeroCocycle_singleton (F := OL (N := N) d ι) g hg' hcoc i))
    change IsHomSection (Idm d ι) m (coverSet ρ {i}) (matLin (idMatrix ι) a.1 - g i) at h2
    have h3 : matLin (idMatrix ι) a.1 = P := (matLin_idMatrix_one a.1).trans hP.symm
    rw [h3] at h2
    exact h2
  refine ⟨P, hP ▸ isHomOn_puncture_of_isHomSection a.2, fun y hy0 => ?_, hcomp⟩
  obtain ⟨i, hyi⟩ := exists_mem_coverSet hρ hy0
  obtain ⟨U, hKU, hU, hUM⟩ := hg i
  obtain ⟨V, hKV, hV, hVI⟩ := hcomp i
  have h1 := hUM y (hKU hyi)
  have h2 := hIM y hy0 _ (hVI y (hKV hyi))
  exact (hM y hy0).congr_mem ((hM y hy0).add_mem h2 h1) fun j =>
    Eventually.of_forall fun x => by simp

end SGPT.GAGA.PN
