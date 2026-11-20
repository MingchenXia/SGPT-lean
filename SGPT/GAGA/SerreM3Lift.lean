import SGPT.GAGA.SerreM3Maps

/-!
# Serre's theorems on `ℙᴺ`, part 10: degree casts and global lifts

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), milestone M4.2.

* `cechHMap_coverHom'_comp`: maps on Čech cohomology induced by homogeneous matrices compose
  as the matrices do; `cechHMap_id_bijective`: the identity induces bijections between twists
  of equal degree written differently (degree casts).
* `cechH_OL_subsingleton'`: `Ȟ^q(𝒪_{L_d}(m)^ι) = 0` for `q ≥ 1`, `m ≥ -d`, now also for `d = N`.
* `cechHMap_free_OL_surjective`: `Ȟ⁰(𝒪(m)^ι) → Ȟ⁰(𝒪_{L_d}(m)^ι)` is onto for `m ≥ -d`
  (Koszul sequences).
* `exists_global_lift`: every `0`-cocycle of a subsheaf `M/I_{L_d}` of `𝒪_{L_d}^ι` in degree
  `m ≥ 0` is represented, modulo `I_{L_d}`, by one global tuple, holomorphic and homogeneous of
  degree `m` on `ℂ^{N+1} ∖ 0`, with germs in `M`.

Blueprint: `claude-serre-m34.tex`, nodes `claude-serre-m34:maps`, `claude-serre-m34:lift`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

variable {N : ℕ}

section General

variable {F G H : Subquotient (ConeSpace N) (puncture (ConeSpace N))}

/-- Induced maps compose as their matrices do. -/
theorem cechHMap_coverHom'_comp (φ : Subquotient.Hom F G) (ψ : Subquotient.Hom G H)
    (χ : Subquotient.Hom F H) {d e f : ℤ} (hφ : IsHomMatrix φ.A d) (hψ : IsHomMatrix ψ.A e)
    (hχ : IsHomMatrix χ.A f) {n n' n'' : ℤ} (h₁ : n + d = n') (h₂ : n' + e = n'')
    (h₃ : n + f = n'') {ρ : ℝ} (hA : ∀ a, matApply χ.A a = matApply ψ.A (matApply φ.A a))
    (q : ℕ) (x : cechH (coverSystem F n ρ) q) :
    (cechHMap (coverHom' χ hχ h₃ ρ) q).hom x =
      (cechHMap (coverHom' ψ hψ h₂ ρ) q).hom ((cechHMap (coverHom' φ hφ h₁ ρ) q).hom x) :=
  cechHMap_apply_of_app (fun s y => by
    induction y using Submodule.Quotient.induction_on with
    | _ a =>
    change sectionMk H _ = sectionMk H _
    congr 1
    exact Subtype.ext (hA a.1)) q x

theorem matLin_idMatrix' {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ConeSpace N → ℂ) :
    matLin (idMatrix ι) (matLin (idMatrix ι) a) = a := by
  simp only [matLin_apply, matApply_idMatrix]

theorem matApply_idMatrix_idMatrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ConeSpace N → ℂ) :
    matApply (idMatrix ι) a = matApply (idMatrix ι) (matApply (idMatrix ι) a) := by
  simp only [matApply_idMatrix]

theorem matLin_idMatrix_one {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ConeSpace N → ℂ) :
    matLin (idMatrix ι) a = a := by
  simp only [matLin_apply, matApply_idMatrix]

/-- **Degree casts**: the identity induces a bijection `Ȟ^q(F(a)) → Ȟ^q(F(b))` for `a = b`. -/
theorem cechHMap_id_bijective (F : Subquotient (ConeSpace N) (puncture (ConeSpace N)))
    {a b : ℤ} (h : a + 0 = b) (ρ : ℝ) (q : ℕ) :
    Function.Bijective (cechHMap (coverHom' (Subquotient.Hom.id F) isHomMatrix_idMatrix h ρ)
      q).hom := by
  refine cechHMap_bijective_of_inverse (β := coverHom' (Subquotient.Hom.id F)
    isHomMatrix_idMatrix (show b + 0 = a by omega) ρ) (fun s x => ?_) (fun s x => ?_) q
  · induction x using Submodule.Quotient.induction_on with
    | _ a =>
    change sectionMk _ _ = sectionMk _ _
    congr 1
    exact Subtype.ext (matLin_idMatrix' _)
  · induction x using Submodule.Quotient.induction_on with
    | _ a =>
    change sectionMk _ _ = sectionMk _ _
    congr 1
    exact Subtype.ext (matLin_idMatrix' _)

end General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `𝒪^ι = 𝒪^ι/0`, written as `mkSq`. -/
def freeSq (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    Subquotient (ConeSpace N) (puncture (ConeSpace N)) :=
  mkSq (GermModule.top _ ι) (GermModule.bot _ ι) (GermModule.top_isCoherentOn _)
    (GermModule.bot_isCoherentOn _) (GermModule.bot_le (GermModule.top_isCoherentOn _))

/-- The identity `𝒪^ι → 𝒪_{L_d}^ι`. -/
def toOL (d : ℕ) : Subquotient.Hom (freeSq N ι) (OL d ι) :=
  idHomSq (GermModule.LeOn.refl _ _) (GermModule.bot_le (Idm_isCoherentOn_puncture d))

theorem Idm_N_eqOn_bot : (GermModule.bot (ConeSpace N) ι).EqOn (Idm N ι)
    (puncture (ConeSpace N)) := fun y hy a => ((Idm_top_eqOn (N := N) (ι := ι) _) y hy a).symm

/-- `Ȟ^q(𝒪_{L_d}(m)^ι) = 0` for `q ≥ 1`, `m ≥ -d`, `d ≤ N`. -/
theorem cechH_OL_subsingleton' {ρ : ℝ} (hρ : 1 ≤ ρ) {d : ℕ} (hd : d ≤ N) {q : ℕ} (hq : 1 ≤ q)
    {m : ℤ} (hm : -(d : ℤ) ≤ m) : Subsingleton (cechH (coverSystem (OL (N := N) d ι) m ρ) q) := by
  rcases lt_or_eq_of_le hd with hd | hdN
  · exact cechH_OL_subsingleton hρ hd hq hm
  · rw [hdN] at hm ⊢
    have hb := cechHMap_bijective_of_eqOn (M := GermModule.top _ ι) (I := GermModule.bot _ ι)
      (M' := GermModule.top _ ι) (I' := Idm N ι) (hM := GermModule.top_isCoherentOn _)
      (hI := GermModule.bot_isCoherentOn _) (hle := GermModule.bot_le (GermModule.top_isCoherentOn _))
      (hM' := GermModule.top_isCoherentOn _) (hI' := Idm_isCoherentOn_puncture N)
      (hle' := GermModule.LeOn.top (Idm_isCoherentOn_puncture N)) (fun _ _ _ => Iff.rfl)
      Idm_N_eqOn_bot m ρ q
    exact @Function.Surjective.subsingleton _ _ _
      (cechH_free_subsingleton (ι := ι) hρ m hq (Or.inr hm)) hb.2

/-- **`Ȟ⁰(𝒪(m)^ι) → Ȟ⁰(𝒪_{L_d}(m)^ι)` is onto** for `m ≥ -d` (closed cover `K(ρ)`, `ρ ≥ 1`). -/
theorem cechHMap_free_OL_surjective {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∀ k d : ℕ, d + k = N → ∀ m : ℤ, -(d : ℤ) ≤ m →
      Function.Surjective (cechHMap (coverHom' (toOL (N := N) (ι := ι) d) isHomMatrix_idMatrix
        (add_zero m) ρ) 0).hom := by
  intro k
  induction k with
  | zero =>
      intro d hdk m _
      have hdN : d = N := by omega
      rw [hdN]
      exact (cechHMap_bijective_of_eqOn (M := GermModule.top _ ι) (I := GermModule.bot _ ι)
        (M' := GermModule.top _ ι) (I' := Idm N ι) (hM := GermModule.top_isCoherentOn _)
        (hI := GermModule.bot_isCoherentOn _)
        (hle := GermModule.bot_le (GermModule.top_isCoherentOn _))
        (hM' := GermModule.top_isCoherentOn _) (hI' := Idm_isCoherentOn_puncture N)
        (hle' := GermModule.LeOn.top (Idm_isCoherentOn_puncture N)) (fun _ _ _ => Iff.rfl)
        Idm_N_eqOn_bot m ρ 0).2
  | succ k ih =>
      intro d hdk m hm
      have hd : d + 1 < N + 1 := by omega
      have hI' : (Idm d ι).EqOn (Idm (d + 1 - 1) ι) (puncture (ConeSpace N)) := by
        rw [Nat.add_sub_cancel]
        exact fun _ _ _ => Iff.rfl
      obtain ⟨φ, ψ, hφA, hψA, hex⟩ := shortExact_hyperplane (M := GermModule.top _ ι)
        (M' := GermModule.top _ ι) (M'' := GermModule.top _ ι) (I := Idm (d + 1) ι)
        (I' := Idm d ι) hd (by omega) (GermModule.top_isCoherentOn _)
        (GermModule.top_isCoherentOn _) (GermModule.top_isCoherentOn _)
        (Idm_isCoherentOn_puncture _) (Idm_isCoherentOn_puncture d) (fun _ _ _ => Iff.rfl) hI'
        (GermModule.LeOn.top (Idm_isCoherentOn_puncture _)) (top_eqOn_comap_scal _)
        (top_eqOn_sup _ (Idm_isCoherentOn_puncture d))
        (GermModule.LeOn.top (Idm_isCoherentOn_puncture _))
        (GermModule.LeOn.top (Idm_isCoherentOn_puncture _))
        (GermModule.LeOn.top (Idm_isCoherentOn_puncture d))
      have hφ : IsHomMatrix φ.A 1 := hφA ▸ isHomMatrix_scalMat _
      have hψ : IsHomMatrix ψ.A 0 := hψA ▸ isHomMatrix_idMatrix
      have hles := coverSystem_les (Laurent.sectionsDecompose_coverSet_all ρ)
        (OL_isInvariant (d + 1)) (OL_isInvariant (d + 1)) (OL_isInvariant d) hφ hψ hex (m - 1) 0
      have hsub : Subsingleton (cechH (coverSystem (OL (N := N) (d + 1) ι) (m - 1) ρ) (0 + 1)) :=
        cechH_OL_subsingleton' hρ (by omega) le_rfl (by push_cast; omega)
      -- `ψ` is onto on `Ȟ⁰`
      have hψs : Function.Surjective (cechHMap (coverHom ψ hψ (m - 1 + 1) ρ) 0).hom := by
        intro x
        exact (hles.2.2.1 x).1 (Subsingleton.elim _ _)
      intro x
      -- cast `x` to degree `m - 1 + 1 + 0`
      set c₁ := coverHom' (Subquotient.Hom.id (OL (N := N) d ι)) isHomMatrix_idMatrix
        (show m + 0 = m - 1 + 1 + 0 by ring) ρ
      obtain ⟨x₂, hx₂⟩ := hψs ((cechHMap c₁ 0).hom x)
      -- cast `x₂` to degree `m`
      set c₂ := coverHom' (Subquotient.Hom.id (OL (N := N) (d + 1) ι)) isHomMatrix_idMatrix
        (show m - 1 + 1 + 0 = m by ring) ρ
      obtain ⟨y, hy⟩ := ih (d + 1) (by omega) m (by push_cast; omega) ((cechHMap c₂ 0).hom x₂)
      refine ⟨y, (cechHMap_id_bijective (OL (N := N) d ι)
        (show m + 0 = m - 1 + 1 + 0 by ring) ρ 0).1 ?_⟩
      change (cechHMap c₁ 0).hom _ = (cechHMap c₁ 0).hom x
      rw [← hx₂]
      -- both sides are induced by the identity matrix `𝒪^ι(m) → 𝒪_{L_d}^ι(m-1+1+0)`
      have hc₂ : (cechHMap (coverHom' (Subquotient.Hom.id (OL (N := N) (d + 1) ι))
          isHomMatrix_idMatrix (show m + 0 = m - 1 + 1 by ring) ρ) 0).hom
            ((cechHMap c₂ 0).hom x₂) = x₂ := by
        have e := cechHMap_coverHom'_comp (Subquotient.Hom.id (OL (N := N) (d + 1) ι))
          (Subquotient.Hom.id (OL (N := N) (d + 1) ι)) (Subquotient.Hom.id (OL (N := N) (d + 1) ι))
          isHomMatrix_idMatrix isHomMatrix_idMatrix isHomMatrix_idMatrix
          (show m - 1 + 1 + 0 = m by ring) (show m + 0 = m - 1 + 1 by ring)
          (show m - 1 + 1 + 0 = m - 1 + 1 by ring) (ρ := ρ)
          (fun a => matApply_idMatrix_idMatrix a) 0 x₂
        refine e.symm.trans (cechHMap_apply_of_app_id (fun s z => ?_) 0 x₂)
        induction z using Submodule.Quotient.induction_on with
        | _ a =>
        change sectionMk _ _ = sectionMk _ _
        congr 1
        exact Subtype.ext (matLin_idMatrix_one _)
      rw [← hc₂, ← hy]
      have e1 := cechHMap_coverHom'_comp (toOL (N := N) (ι := ι) d)
        (Subquotient.Hom.id (OL (N := N) d ι)) (toOL (N := N) (ι := ι) d) isHomMatrix_idMatrix
        isHomMatrix_idMatrix isHomMatrix_idMatrix (add_zero m)
        (show m + 0 = m - 1 + 1 + 0 by ring) (show m + 0 = m - 1 + 1 + 0 by ring) (ρ := ρ)
        (fun a => matApply_idMatrix_idMatrix a) 0 y
      have e2 := cechHMap_coverHom'_comp (toOL (N := N) (ι := ι) (d + 1))
        (Subquotient.Hom.id (OL (N := N) (d + 1) ι)) (toOL (N := N) (ι := ι) (d + 1))
        isHomMatrix_idMatrix isHomMatrix_idMatrix isHomMatrix_idMatrix (add_zero m)
        (show m + 0 = m - 1 + 1 by ring) (show m + 0 = m - 1 + 1 by ring) (ρ := ρ)
        (fun a => matApply_idMatrix_idMatrix a) 0 y
      have e3 := cechHMap_coverHom'_comp (toOL (N := N) (ι := ι) (d + 1)) ψ
        (toOL (N := N) (ι := ι) d) isHomMatrix_idMatrix hψ isHomMatrix_idMatrix
        (show m + 0 = m - 1 + 1 by ring) rfl (show m + 0 = m - 1 + 1 + 0 by ring) (ρ := ρ)
        (fun a => by rw [hψA]; exact matApply_idMatrix_idMatrix a) 0 y
      exact e1.symm.trans (e3.trans (congrArg (cechHMap (coverHom ψ hψ (m - 1 + 1) ρ) 0).hom e2))

end SGPT.GAGA.PN
