import SGPT.GAGA.SerreM2Linear

/-!
# Serre's theorems on `ℙᴺ`, part 7: cohomology of `𝒪_{L_d}(m)` and finiteness

Milestone M4.1 of `blueprint/src/claude-serre-core.tex`, towards source `lma:GAGA`
(`chapter_NApotential.tex`, lines 1143--1145).

* `OL d ι = 𝒪^ι / I_{L_d} 𝒪^ι` (the free `𝒪_{L_d}`-module of rank `ι`, pushed forward to `ℙᴺ`).
* **Koszul**: the hyperplane sequences `0 → 𝒪_{L_{d+1}}(m-1) → 𝒪_{L_{d+1}}(m) → 𝒪_{L_d}(m) → 0`
  (`shortExact_hyperplane` with `M = 𝒪^ι`) and SERRE-PN2's computation of `Ȟ^q(ℙᴺ, 𝒪(m))` give,
  by descending induction on `d < N`: `Ȟ^q(K(ρ), 𝒪_{L_d}(m)^ι) = 0` for `q ≥ 1`, `m ≥ -d`
  (`cechH_OL_subsingleton`), and `Ȟ^q` is finite-dimensional for `q ≥ 1` and all `m`
  (`finiteDimensional_cechH_OL`).
* **Finiteness of `Ȟ¹`** for every invariant subsheaf `M/I_{L_d}` of `𝒪_{L_d}^ι`, `d < N`
  (`finiteDimensional_cechH_one_Sd`); for `d = N` this is `finiteDimensional_cechH_one_subSq`.

Blueprint: `claude-serre-m34.tex`, nodes `claude-serre-m34:OL-cohomology`,
`claude-serre-m34:finite-H1-Sd`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-- An exact sequence `A → B → C` with `A`, `C` subsingletons has `B` a subsingleton. -/
theorem subsingleton_of_exact {A B C : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] [Subsingleton A] [Subsingleton C]
    {f : A →ₗ[ℂ] B} {g : B →ₗ[ℂ] C} (h : Function.Exact f g) :
    Subsingleton B := by
  refine ⟨fun b b' => ?_⟩
  have hb : ∀ x : B, x = 0 := fun x => by
    obtain ⟨a, ha⟩ := (h x).1 (Subsingleton.elim _ _)
    rw [← ha, Subsingleton.elim a 0, map_zero]
  rw [hb b, hb b']

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `𝒪_{L_d}^ι = 𝒪^ι / I_{L_d} 𝒪^ι`. -/
def OL (d : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    Subquotient (ConeSpace N) (puncture (ConeSpace N)) :=
  mkSq (GermModule.top _ ι) (Idm d ι) (GermModule.top_isCoherentOn _)
    (Idm_isCoherentOn_puncture d) (GermModule.LeOn.top (Idm_isCoherentOn_puncture d))

theorem OL_isInvariant (d : ℕ) : IsInvariantSubquotient (OL (N := N) d ι) :=
  ⟨isConeInvariant_top, isConeInvariant_Idm d⟩

theorem top_eqOn_comap_scal (e : Fin (N + 1)) :
    (GermModule.top (ConeSpace N) ι).EqOn ((GermModule.top _ ι).comap (scalMat ι e))
      (puncture (ConeSpace N)) := by
  intro y _ a
  constructor
  · intro ha
    exact ⟨ha, HolTupleAt.matApply (fun i j => (isHomMatrix_scalMat e).holAt y
      (by assumption) i j) ha⟩
  · exact fun h => h.1

theorem top_eqOn_sup (I' : GermModule (ConeSpace N) ι)
    (hI'c : I'.IsCoherentOn (puncture (ConeSpace N))) :
    (GermModule.top (ConeSpace N) ι).EqOn ((GermModule.top _ ι).sup I')
      (puncture (ConeSpace N)) := by
  intro y hy a
  constructor
  · intro ha
    exact GermModule.le_sup_left hI'c y hy a ha
  · intro ha
    exact GermModule.sup_le (GermModule.top_isCoherentOn _) (GermModule.LeOn.refl _ _)
      (GermModule.LeOn.top hI'c) y hy a ha

/-- **One Koszul step.** Let `I` be stalkwise equal to `I_{L_{d+1}} 𝒪^ι` (`d + 1 ≤ N`). From the
hyperplane sequence `0 → (𝒪^ι/I)(m-1) → (𝒪^ι/I)(m) → 𝒪_{L_d}^ι(m) → 0`: if `Ȟ^q((𝒪^ι/I)(m)) = 0`
for `q ≥ 1`, `m ≥ -(d+1)`, then `Ȟ^q(𝒪_{L_d}(m)^ι) = 0` for `q ≥ 1`, `m ≥ -d`; and if all
`Ȟ^q((𝒪^ι/I)(m))`, `q ≥ 1`, are finite-dimensional, so are the `Ȟ^q(𝒪_{L_d}(m)^ι)`. -/
theorem OL_step {d : ℕ} (hd : d + 1 < N + 1) {I : GermModule (ConeSpace N) ι}
    (hIc : I.IsCoherentOn (puncture (ConeSpace N)))
    (hI : I.EqOn (Idm (d + 1) ι) (puncture (ConeSpace N))) (hIi : IsConeInvariant I)
    {ρ : ℝ} :
    ((∀ q, 1 ≤ q → ∀ m : ℤ, -((d : ℤ) + 1) ≤ m →
        Subsingleton (cechH (coverSystem (mkSq (GermModule.top _ ι) I
          (GermModule.top_isCoherentOn _) hIc (GermModule.LeOn.top hIc)) m ρ) q)) →
      ∀ q, 1 ≤ q → ∀ m : ℤ, -(d : ℤ) ≤ m →
        Subsingleton (cechH (coverSystem (OL (N := N) d ι) m ρ) q)) ∧
    ((∀ q, 1 ≤ q → ∀ m : ℤ,
        FiniteDimensional ℂ (cechH (coverSystem (mkSq (GermModule.top _ ι) I
          (GermModule.top_isCoherentOn _) hIc (GermModule.LeOn.top hIc)) m ρ) q)) →
      ∀ q, 1 ≤ q → ∀ m : ℤ, FiniteDimensional ℂ (cechH (coverSystem (OL (N := N) d ι) m ρ) q)) := by
  have hI' : (Idm d ι).EqOn (Idm (d + 1 - 1) ι) (puncture (ConeSpace N)) := by
    rw [Nat.add_sub_cancel]
    exact fun _ _ _ => Iff.rfl
  obtain ⟨φ, ψ, hφA, hψA, hex⟩ := shortExact_hyperplane (M := GermModule.top _ ι)
    (M' := GermModule.top _ ι) (M'' := GermModule.top _ ι) (I := I) (I' := Idm d ι) hd
    (by omega) (GermModule.top_isCoherentOn _) (GermModule.top_isCoherentOn _)
    (GermModule.top_isCoherentOn _) hIc (Idm_isCoherentOn_puncture d) hI hI'
    (GermModule.LeOn.top (Idm_isCoherentOn_puncture _)) (top_eqOn_comap_scal _)
    (top_eqOn_sup _ (Idm_isCoherentOn_puncture d)) (GermModule.LeOn.top hIc)
    (GermModule.LeOn.top hIc) (GermModule.LeOn.top (Idm_isCoherentOn_puncture d))
  have hφ : IsHomMatrix φ.A 1 := hφA ▸ isHomMatrix_scalMat _
  have hψ : IsHomMatrix ψ.A 0 := hψA ▸ isHomMatrix_idMatrix
  have hFi : IsInvariantSubquotient (mkSq (GermModule.top (ConeSpace N) ι) I
      (GermModule.top_isCoherentOn _) hIc (GermModule.LeOn.top hIc)) :=
    ⟨isConeInvariant_top, hIi⟩
  have hles := fun n q => coverSystem_les (Laurent.sectionsDecompose_coverSet_all ρ) hFi hFi
    (OL_isInvariant d) hφ hψ hex n q
  have hdeg : ∀ m : ℤ, m - 1 + 1 + 0 = m := fun m => by ring
  refine ⟨fun hyp q hq m hm => ?_, fun hyp q hq m => ?_⟩
  · have h1 := hyp q hq (m - 1 + 1) (by omega)
    have h2 := hyp (q + 1) (by omega) (m - 1) (by omega)
    have h := subsingleton_of_exact (hles (m - 1) q).2.2.1
    rw [hdeg] at h
    exact h
  · have h1 := hyp q hq (m - 1 + 1)
    have h2 := hyp (q + 1) (by omega) (m - 1)
    have h := finiteDimensional_of_exact (hles (m - 1) q).2.2.1
    rw [hdeg] at h
    exact h

/-- The cohomology of `𝒪_{L_d}(m)^ι`, `d < N`, by descending induction. -/
theorem OL_cohomology {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∀ k d : ℕ, d + k + 1 = N →
      (∀ q, 1 ≤ q → ∀ m : ℤ, -(d : ℤ) ≤ m →
        Subsingleton (cechH (coverSystem (OL (N := N) d ι) m ρ) q)) ∧
      (∀ q, 1 ≤ q → ∀ m : ℤ, FiniteDimensional ℂ (cechH (coverSystem (OL (N := N) d ι) m ρ) q)) := by
  intro k
  induction k with
  | zero =>
      intro d hdk
      have hd : d + 1 < N + 1 := by omega
      have hIeq : (GermModule.bot (ConeSpace N) ι).EqOn (Idm (d + 1) ι) (puncture _) := by
        have h := Idm_top_eqOn (N := N) (ι := ι) (puncture (ConeSpace N))
        rw [show d + 1 = N by omega]
        exact fun y hy a => (h y hy a).symm
      obtain ⟨hv, hf⟩ := OL_step (ι := ι) (ρ := ρ) hd (GermModule.bot_isCoherentOn _) hIeq
        isConeInvariant_bot
      refine ⟨hv fun q hq m hm => ?_, hf fun q hq m => ?_⟩
      · exact cechH_free_subsingleton (ι := ι) hρ m hq (Or.inr (by omega))
      · exact finiteDimensional_cechH_free (ι := ι) hρ m hq
  | succ k ih =>
      intro d hdk
      have hd : d + 1 < N + 1 := by omega
      obtain ⟨hv', hf'⟩ := ih (d + 1) (by omega)
      obtain ⟨hv, hf⟩ := OL_step (ι := ι) (ρ := ρ) hd (Idm_isCoherentOn_puncture (d + 1))
        (fun _ _ _ => Iff.rfl) (isConeInvariant_Idm (d + 1))
      refine ⟨hv fun q hq m hm => hv' q hq m (by push_cast at hm ⊢; omega), hf fun q hq m =>
        hf' q hq m⟩

/-- **`Ȟ^q(ℙᴺ, 𝒪_{L_d}(m)^ι) = 0` for `q ≥ 1` and `m ≥ -d`** (`d < N`, closed cover `K(ρ)`,
`ρ ≥ 1`). -/
theorem cechH_OL_subsingleton {ρ : ℝ} (hρ : 1 ≤ ρ) {d : ℕ} (hd : d < N) {q : ℕ} (hq : 1 ≤ q)
    {m : ℤ} (hm : -(d : ℤ) ≤ m) : Subsingleton (cechH (coverSystem (OL (N := N) d ι) m ρ) q) :=
  (OL_cohomology (ι := ι) hρ (N - d - 1) d (by omega)).1 q hq m hm

/-- **`Ȟ^q(ℙᴺ, 𝒪_{L_d}(m)^ι)` is finite-dimensional** for `q ≥ 1` and all `m` (`d < N`). -/
theorem finiteDimensional_cechH_OL {ρ : ℝ} (hρ : 1 ≤ ρ) {d : ℕ} (hd : d < N) {q : ℕ}
    (hq : 1 ≤ q) (m : ℤ) : FiniteDimensional ℂ (cechH (coverSystem (OL (N := N) d ι) m ρ) q) :=
  (OL_cohomology (ι := ι) hρ (N - d - 1) d (by omega)).2 q hq m

/-! ### Finiteness of `Ȟ¹` for subsheaves of `𝒪_{L_d}^ι` -/

/-- The subsheaf `M/I_{L_d}` of `𝒪_{L_d}^ι` (`I_{L_d} 𝒪^ι ⊆ M`). -/
def Sd (d : ℕ) (M : GermModule (ConeSpace N) ι) (hM : M.IsCoherentOn (puncture (ConeSpace N)))
    (hIM : (Idm d ι).LeOn M (puncture (ConeSpace N))) :
    Subquotient (ConeSpace N) (puncture (ConeSpace N)) :=
  mkSq M (Idm d ι) hM (Idm_isCoherentOn_puncture d) hIM

/-- The inclusion `M/I_{L_d} → 𝒪_{L_d}^ι`. -/
def inclOL (d : ℕ) (M : GermModule (ConeSpace N) ι)
    (hM : M.IsCoherentOn (puncture (ConeSpace N)))
    (hIM : (Idm d ι).LeOn M (puncture (ConeSpace N))) :
    Subquotient.Hom (Sd d M hM hIM) (OL d ι) where
  A := idMatrix ι
  holAt x _ := holAt_idMatrix x
  map_M y hy _ ha := mem_matApply_idMatrix.2 ((hM y hy).holTupleAt_of_mem ha)
  map_N _ _ _ ha := mem_matApply_idMatrix.2 ha

theorem inclOL_injective (d : ℕ) (M : GermModule (ConeSpace N) ι)
    (hM : M.IsCoherentOn (puncture (ConeSpace N)))
    (hIM : (Idm d ι).LeOn M (puncture (ConeSpace N))) :
    Subquotient.Injective (inclOL d M hM hIM) := by
  intro y hy a
  change (M.mem y a ∧ HolTupleAt a y ∧ (Idm d ι).mem y (matApply (idMatrix ι) a)) ↔
    (Idm d ι).mem y a
  refine ⟨fun h => mem_matApply_idMatrix.1 h.2.2, fun h => ⟨hIM y hy a h,
    (Idm_isCoherentOn_puncture d y hy).holTupleAt_of_mem h, mem_matApply_idMatrix.2 h⟩⟩

/-- **`dim Ȟ¹(ℙᴺ, (M/I_{L_d})(n)) < ∞`** for every `ℂ*`-invariant coherent `M ⊇ I_{L_d} 𝒪^ι`
(`d < N`), every `n` and `ρ ≥ 1`. -/
theorem finiteDimensional_cechH_one_Sd {d : ℕ} (hd : d < N) {M : GermModule (ConeSpace N) ι}
    (hM : M.IsCoherentOn (puncture (ConeSpace N))) (hMi : IsConeInvariant M)
    (hIM : (Idm d ι).LeOn M (puncture (ConeSpace N))) {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) :
    FiniteDimensional ℂ (cechH (coverSystem (Sd d M hM hIM) n ρ) 1) := by
  have hFi : IsInvariantSubquotient (Sd d M hM hIM) := ⟨hMi, isConeInvariant_Idm d⟩
  have hφ : IsHomMatrix (inclOL d M hM hIM).A 0 := isHomMatrix_idMatrix
  have hψ : IsHomMatrix (Subquotient.cokerπ (inclOL d M hM hIM)).A 0 := isHomMatrix_idMatrix
  have hHi := isInvariant_coker hFi (OL_isInvariant d) hφ
  have hex : Subquotient.ShortExact (inclOL d M hM hIM) (Subquotient.cokerπ _) :=
    ⟨inclOL_injective d M hM hIM, Subquotient.exact_cokerπ _, Subquotient.surjective_cokerπ _⟩
  have hles := coverSystem_les (Laurent.sectionsDecompose_coverSet_all ρ) hFi (OL_isInvariant d)
    hHi hφ hψ hex n 0
  have h1 : FiniteDimensional ℂ (cechH (coverSystem (Subquotient.coker (inclOL d M hM hIM))
      (n + 0 + 0) ρ) 0) := finiteDimensional_cechH_zero hHi hρ
  have h2 : FiniteDimensional ℂ (cechH (coverSystem (OL (N := N) d ι) (n + 0) ρ) (0 + 1)) :=
    finiteDimensional_cechH_OL hρ hd le_rfl (n + 0)
  exact finiteDimensional_of_exact hles.2.2.2

end SGPT.GAGA.PN
