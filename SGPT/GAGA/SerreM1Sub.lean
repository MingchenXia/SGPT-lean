import SGPT.GAGA.SerreM1Finite
import SGPT.GAGA.PN2Cohomology

/-!
# Serre's theorems on `ℙᴺ`, part 5: `dim Ȟ¹(ℙᴺ, M(n)) < ∞` for `M ⊆ 𝒪^ι`

Infrastructure towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145).

For a `ℂ*`-invariant coherent submodule `M ⊆ 𝒪^ι` on `ℂ^{N+1} ∖ 0` (a coherent subsheaf of
`𝒪_{ℙᴺ}^ι`), `subSq M` is the subquotient `M/0`. The inclusion `M → 𝒪^ι` (identity matrix) and
its cokernel give a short exact sequence `0 → M → 𝒪^ι → 𝒪^ι/M → 0` of invariant subquotients
(`shortExact_inclFree`). By the long exact sequence of lane SERRE-PN (`coverSystem_les`, with
Theorem B of SERRE-CORE3), `Ȟ⁰(𝒪^ι/M (n)) → Ȟ¹(M(n)) → Ȟ¹(𝒪^ι(n))` is exact; the outer terms are
finite-dimensional (`finiteDimensional_cechH_zero`, SERRE-PN2's `finiteDimensional_cechH_free`),
hence so is `Ȟ¹(M(n))` (`finiteDimensional_cechH_one_subSq`). This is the finiteness used by
Serre's proof of Theorem A (the restriction maps `Ȟ¹(M(m-1)) → Ȟ¹(M(m))` eventually become
bijective).

Blueprint: `claude-serre-m34.tex`, node `claude-serre-m34:finite-H1-sub`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-- An exact sequence `A → B → C` of vector spaces with `A`, `C` finite-dimensional has `B`
finite-dimensional. -/
theorem finiteDimensional_of_exact {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A]
    [FiniteDimensional ℂ C] {f : A →ₗ[ℂ] B} {g : B →ₗ[ℂ] C} (h : Function.Exact f g) :
    FiniteDimensional ℂ B := by
  have hker : LinearMap.ker g = LinearMap.range f := (LinearMap.exact_iff.1 h)
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, hker, LinearMap.range_eq_map]
  exact (Module.Finite.fg_top).map f

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_matApply_idMatrix {P : GermModule (ConeSpace N) ι} {y : ConeSpace N}
    {a : ι → ConeSpace N → ℂ} : P.mem y (matApply (idMatrix ι) a) ↔ P.mem y a := by
  rw [matApply_idMatrix]

/-- The identity matrix is homogeneous of degree `0`. -/
theorem isHomMatrix_idMatrix :
    IsHomMatrix (idMatrix ι : ι → ι → ConeSpace N → ℂ) 0 :=
  ⟨fun x _ i j => holAt_idMatrix x i j, fun _ _ _ _ i j => by simp [idMatrix]⟩

/-- The invariant coherent submodule `M ⊆ 𝒪^ι` as the subquotient `M/0`. -/
def subSq (M : GermModule (ConeSpace N) ι) (hM : M.IsCoherentOn (puncture (ConeSpace N))) :
    Subquotient (ConeSpace N) (puncture (ConeSpace N)) where
  ι := ι
  M := M
  N := GermModule.bot _ ι
  coherent_M := hM
  coherent_N := GermModule.bot_isCoherentOn _
  le := GermModule.bot_le hM

theorem subSq_isInvariant {M : GermModule (ConeSpace N) ι}
    (hM : M.IsCoherentOn (puncture (ConeSpace N))) (hMi : IsConeInvariant M) :
    IsInvariantSubquotient (subSq M hM) :=
  ⟨hMi, isConeInvariant_bot⟩

/-- The inclusion `M → 𝒪^ι`. -/
def inclFree (M : GermModule (ConeSpace N) ι) (hM : M.IsCoherentOn (puncture (ConeSpace N))) :
    Subquotient.Hom (subSq M hM) (freeSubquotient (ConeSpace N) ι) where
  A := idMatrix ι
  holAt x _ := holAt_idMatrix x
  map_M y hy _ ha := mem_matApply_idMatrix.2 ((hM y hy).holTupleAt_of_mem ha)
  map_N _ _ _ ha := mem_matApply_idMatrix.2 ha

theorem inclFree_injective (M : GermModule (ConeSpace N) ι)
    (hM : M.IsCoherentOn (puncture (ConeSpace N))) :
    Subquotient.Injective (inclFree M hM) := by
  intro y hy a
  change (M.mem y a ∧ HolTupleAt a y ∧ (GermModule.bot _ ι).mem y (matApply (idMatrix ι) a)) ↔
    (GermModule.bot _ ι).mem y a
  refine ⟨fun h => mem_matApply_idMatrix.1 h.2.2, fun h => ⟨GermModule.bot_le hM y hy a h,
    (GermModule.bot_isCoherentOn _ y hy).holTupleAt_of_mem h, mem_matApply_idMatrix.2 h⟩⟩

/-- **`0 → M → 𝒪^ι → 𝒪^ι/M → 0`** (with the cokernel `𝒪^ι/(0 + M)`). -/
theorem shortExact_inclFree (M : GermModule (ConeSpace N) ι)
    (hM : M.IsCoherentOn (puncture (ConeSpace N))) :
    Subquotient.ShortExact (inclFree M hM) (Subquotient.cokerπ (inclFree M hM)) :=
  ⟨inclFree_injective M hM, Subquotient.exact_cokerπ _, Subquotient.surjective_cokerπ _⟩

/-- **`dim Ȟ¹(ℙᴺ, M(n)) < ∞`** for every `ℂ*`-invariant coherent submodule `M ⊆ 𝒪^ι` on
`ℂ^{N+1} ∖ 0`, every `n` and every `ρ ≥ 1` (Čech cohomology of the closed cover `K(ρ)`). -/
theorem finiteDimensional_cechH_one_subSq {M : GermModule (ConeSpace N) ι}
    (hM : M.IsCoherentOn (puncture (ConeSpace N))) (hMi : IsConeInvariant M) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (n : ℤ) : FiniteDimensional ℂ (cechH (coverSystem (subSq M hM) n ρ) 1) := by
  have hFi := subSq_isInvariant hM hMi
  have hGi : IsInvariantSubquotient (freeSubquotient (ConeSpace N) ι) :=
    freeSubquotient_isInvariant
  have hφ : IsHomMatrix (inclFree M hM).A 0 := isHomMatrix_idMatrix
  have hψ : IsHomMatrix (Subquotient.cokerπ (inclFree M hM)).A 0 := isHomMatrix_idMatrix
  have hHi := isInvariant_coker hFi hGi hφ
  have hles := coverSystem_les (Laurent.sectionsDecompose_coverSet_all ρ) hFi hGi hHi hφ hψ
    (shortExact_inclFree M hM) n 0
  have h1 : FiniteDimensional ℂ (cechH (coverSystem (Subquotient.coker (inclFree M hM))
      (n + 0 + 0) ρ) 0) := finiteDimensional_cechH_zero hHi hρ
  have h2 : FiniteDimensional ℂ (cechH (coverSystem (freeSubquotient (ConeSpace N) ι)
      (n + 0) ρ) (0 + 1)) := finiteDimensional_cechH_free hρ (n + 0) le_rfl
  exact finiteDimensional_of_exact hles.2.2.2

end SGPT.GAGA.PN
