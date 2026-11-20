import SGPT.GAGA.SerreM2Gen

/-!
# Serre's theorems on `ℙᴺ`, part 9: induced maps, composites, transfer, lifting

Infrastructure for Serre's Theorem A (milestone M4.2 of `blueprint/src/claude-serre-core.tex`),
towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145).

* `CechSystem.Hom.comp` and `cechHMap_apply_of_app`: the map on Čech cohomology induced by a
  componentwise composite is the composite.
* `coverHom'`: the morphism of Čech coefficient systems induced by a homogeneous morphism of
  subquotients of degree `d`, with an arbitrary target degree `n' = n + d`; composites of such
  maps are again of this form (`coverHom'_comp_app`), so no casts between degrees are needed.
* `cechHMap_bijective_of_eqOn`: subquotients with stalkwise equal numerators and denominators
  have isomorphic Čech cohomology.
* `exists_global_lift`: for `m ≥ 0`, every `0`-cocycle of a subsheaf `M/I_{L_d}` of
  `𝒪_{L_d}^ι` (`d < N`) is represented by a global tuple, holomorphic and homogeneous of degree
  `m` on `ℂ^{N+1} ∖ 0`, with germs in `M` (`Ȟ⁰(𝒪(m)) → Ȟ⁰(𝒪_{L_d}(m))` is onto by the Koszul
  sequences).

Blueprint: `claude-serre-m34.tex`, nodes `claude-serre-m34:maps`, `claude-serre-m34:lift`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-! ### Composites of morphisms of coefficient systems -/

section CechComp

universe u v

variable {k : Type u} [Ring k] {I : Type} [LinearOrder I]
variable {Γ₁ Γ₂ Γ₃ : CechSystem.{u, v} k I}

/-- The composite of two morphisms of coefficient systems. -/
def CechSystem.Hom.comp (ψ : CechSystem.Hom Γ₂ Γ₃) (φ : CechSystem.Hom Γ₁ Γ₂) :
    CechSystem.Hom Γ₁ Γ₃ where
  app s := (ψ.app s).comp (φ.app s)
  naturality h x := by
    simp only [LinearMap.comp_apply]
    rw [φ.naturality, ψ.naturality]

/-- If `γ` is componentwise `ψ ∘ φ`, the induced map on cohomology is the composite. -/
theorem cechHMap_apply_of_app {φ : CechSystem.Hom Γ₁ Γ₂} {ψ : CechSystem.Hom Γ₂ Γ₃}
    {γ : CechSystem.Hom Γ₁ Γ₃} (h : ∀ s x, γ.app s x = ψ.app s (φ.app s x)) (q : ℕ)
    (x : cechH Γ₁ q) :
    (cechHMap γ q).hom x = (cechHMap ψ q).hom ((cechHMap φ q).hom x) := by
  obtain ⟨z, rfl⟩ := cechClass_surjective Γ₁ q x
  rw [cechHMap_cechClass, cechHMap_cechClass, cechHMap_cechClass]
  congr 1
  exact Subtype.ext (Subtype.ext (funext fun s => h s _))

/-- If `γ` acts componentwise as the identity, so does the induced map on cohomology. -/
theorem cechHMap_apply_of_app_id {γ : CechSystem.Hom Γ₁ Γ₁} (h : ∀ s x, γ.app s x = x)
    (q : ℕ) (x : cechH Γ₁ q) : (cechHMap γ q).hom x = x := by
  obtain ⟨z, rfl⟩ := cechClass_surjective Γ₁ q x
  rw [cechHMap_cechClass]
  congr 1
  exact Subtype.ext (Subtype.ext (funext fun s => h s _))

/-- Componentwise inverse morphisms induce inverse maps on cohomology. -/
theorem cechHMap_bijective_of_inverse {α : CechSystem.Hom Γ₁ Γ₂} {β : CechSystem.Hom Γ₂ Γ₁}
    (hβα : ∀ s x, β.app s (α.app s x) = x) (hαβ : ∀ s y, α.app s (β.app s y) = y) (q : ℕ) :
    Function.Bijective (cechHMap α q).hom := by
  have h1 : ∀ x, (cechHMap β q).hom ((cechHMap α q).hom x) = x := fun x => by
    rw [← cechHMap_apply_of_app (γ := β.comp α) (fun s x => rfl)]
    exact cechHMap_apply_of_app_id (fun s x => hβα s x) q x
  have h2 : ∀ y, (cechHMap α q).hom ((cechHMap β q).hom y) = y := fun y => by
    rw [← cechHMap_apply_of_app (γ := α.comp β) (fun s x => rfl)]
    exact cechHMap_apply_of_app_id (fun s x => hαβ s x) q y
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end CechComp

variable {N : ℕ}

/-! ### Induced maps with an arbitrary target degree -/

section Induced

variable {F G H : Subquotient (ConeSpace N) (puncture (ConeSpace N))}

/-- A product of homogeneous matrices is homogeneous. -/
theorem IsHomMatrix.matMul {κ ι μ : Type} [Fintype κ] [Fintype ι] [Fintype μ]
    {B : κ → ι → ConeSpace N → ℂ} {A : ι → μ → ConeSpace N → ℂ} {d e : ℤ}
    (hB : IsHomMatrix B e) (hA : IsHomMatrix A d) :
    IsHomMatrix (GermModule.matMul B A) (d + e) := by
  refine ⟨fun x hx i k => HolAt.fintype_sum fun j => (hB.holAt x hx i j).mul (hA.holAt x hx j k),
    fun z hz c hc i k => ?_⟩
  simp only [GermModule.matMul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hB.hom z hz c hc i j, hA.hom z hz c hc j k, zpow_add₀ hc]
  ring

/-- `sectionMap` with an arbitrary target degree `n' = n + d`. -/
def sectionMap' (φ : Subquotient.Hom F G) {d : ℤ} (hφ : IsHomMatrix φ.A d) {n n' : ℤ}
    (h : n + d = n') (K : Set (ConeSpace N)) (hK : K ⊆ puncture (ConeSpace N)) :
    sectionModule F n K hK →ₗ[ℂ] sectionModule G n' K hK :=
  Submodule.mapQ _ _
    (((matLin φ.A).comp (secM F n K hK).subtype).codRestrict (secM G n' K hK)
      fun a => h ▸ IsHomSection.matApply a.2 hφ fun y hy b hb => φ.map_M y hy b hb)
    (fun _ ha => h ▸ IsHomSection.matApply ha hφ fun y hy b hb => φ.map_N y hy b hb)

theorem sectionMap'_mk (φ : Subquotient.Hom F G) {d : ℤ} (hφ : IsHomMatrix φ.A d) {n n' : ℤ}
    (h : n + d = n') (K : Set (ConeSpace N)) (hK : K ⊆ puncture (ConeSpace N))
    (a : secM F n K hK) :
    sectionMap' φ hφ h K hK (sectionMk F a) = sectionMk G ⟨matApply φ.A a.1,
      h ▸ IsHomSection.matApply a.2 hφ fun y hy b hb => φ.map_M y hy b hb⟩ :=
  rfl

/-- The morphism of Čech coefficient systems `F(n) → G(n')`, `n' = n + d`, induced by a
homogeneous morphism of degree `d`. -/
def coverHom' (φ : Subquotient.Hom F G) {d : ℤ} (hφ : IsHomMatrix φ.A d) {n n' : ℤ}
    (h : n + d = n') (ρ : ℝ) : CechSystem.Hom (coverSystem F n ρ) (coverSystem G n' ρ) where
  app s := sectionMap' φ hφ h _ (coverSet_subset ρ s)
  naturality _ x := by
    induction x using Submodule.Quotient.induction_on with
    | _ a => rfl

theorem coverHom_eq_coverHom' (φ : Subquotient.Hom F G) {d : ℤ} (hφ : IsHomMatrix φ.A d)
    (n : ℤ) (ρ : ℝ) : coverHom φ hφ n ρ = coverHom' φ hφ rfl ρ :=
  rfl

/-- Composites of induced maps. -/
theorem coverHom'_comp_app (φ : Subquotient.Hom F G) (ψ : Subquotient.Hom G H) {d e : ℤ}
    (hφ : IsHomMatrix φ.A d) (hψ : IsHomMatrix ψ.A e) {n n' n'' : ℤ} (h₁ : n + d = n')
    (h₂ : n' + e = n'') (h₃ : n + (d + e) = n'') (ρ : ℝ) (s : Finset (Fin (N + 1)))
    (x : (coverSystem F n ρ).obj s) :
    (coverHom' (ψ.comp φ) (hψ.matMul hφ) h₃ ρ).app s x =
      (coverHom' ψ hψ h₂ ρ).app s ((coverHom' φ hφ h₁ ρ).app s x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
  change sectionMk H _ = sectionMk H _
  congr 1
  exact Subtype.ext (matApply_matApply ψ.A φ.A a.1).symm

/-- Two induced maps whose matrices act equally on tuples agree. -/
theorem coverHom'_app_congr (φ ψ : Subquotient.Hom F G) {d e : ℤ} (hφ : IsHomMatrix φ.A d)
    (hψ : IsHomMatrix ψ.A e) {n n' : ℤ} (h₁ : n + d = n') (h₂ : n + e = n') (ρ : ℝ)
    (hA : ∀ a, matApply φ.A a = matApply ψ.A a) (s : Finset (Fin (N + 1)))
    (x : (coverSystem F n ρ).obj s) :
    (coverHom' φ hφ h₁ ρ).app s x = (coverHom' ψ hψ h₂ ρ).app s x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
  change sectionMk G _ = sectionMk G _
  congr 1
  exact Subtype.ext (hA a.1)

end Induced

/-! ### Stalkwise equal subquotients -/

section Transfer

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem matLin_idMatrix_idMatrix (a : ι → ConeSpace N → ℂ) :
    matLin (idMatrix ι) (matLin (idMatrix ι) a) = a := by
  simp only [matLin_apply, matApply_idMatrix]

/-- The identity matrix as a morphism `M/I → M'/I'` when `M ⊆ M'`, `I ⊆ I'`. -/
def idHomSq {M I M' I' : GermModule (ConeSpace N) ι}
    {hM : M.IsCoherentOn (puncture (ConeSpace N))} {hI : I.IsCoherentOn (puncture (ConeSpace N))}
    {hle : I.LeOn M (puncture (ConeSpace N))}
    {hM' : M'.IsCoherentOn (puncture (ConeSpace N))}
    {hI' : I'.IsCoherentOn (puncture (ConeSpace N))} {hle' : I'.LeOn M' (puncture (ConeSpace N))}
    (h1 : M.LeOn M' (puncture (ConeSpace N))) (h2 : I.LeOn I' (puncture (ConeSpace N))) :
    Subquotient.Hom (mkSq M I hM hI hle) (mkSq M' I' hM' hI' hle') where
  A := idMatrix ι
  holAt x _ := holAt_idMatrix x
  map_M y hy _ ha := mem_matApply_idMatrix.2 (h1 y hy _ ha)
  map_N y hy _ ha := mem_matApply_idMatrix.2 (h2 y hy _ ha)

/-- **Transfer**: if `M, M'` and `I, I'` are stalkwise equal on `ℂ^{N+1} ∖ 0`, the identity
induces bijections `Ȟ^q(K(ρ), (M/I)(n)) → Ȟ^q(K(ρ), (M'/I')(n))`. -/
theorem cechHMap_bijective_of_eqOn {M I M' I' : GermModule (ConeSpace N) ι}
    {hM : M.IsCoherentOn (puncture (ConeSpace N))} {hI : I.IsCoherentOn (puncture (ConeSpace N))}
    {hle : I.LeOn M (puncture (ConeSpace N))}
    {hM' : M'.IsCoherentOn (puncture (ConeSpace N))}
    {hI' : I'.IsCoherentOn (puncture (ConeSpace N))} {hle' : I'.LeOn M' (puncture (ConeSpace N))}
    (h1 : M.EqOn M' (puncture (ConeSpace N))) (h2 : I.EqOn I' (puncture (ConeSpace N)))
    (n : ℤ) (ρ : ℝ) (q : ℕ) :
    Function.Bijective (cechHMap (coverHom' (idHomSq (hM := hM) (hI := hI) (hle := hle)
      (hM' := hM') (hI' := hI') (hle' := hle') h1.le h2.le) isHomMatrix_idMatrix
      (add_zero n) ρ) q).hom := by
  refine cechHMap_bijective_of_inverse (β := coverHom' (idHomSq (hM := hM') (hI := hI')
    (hle := hle') (hM' := hM) (hI' := hI) (hle' := hle) h1.symm.le h2.symm.le)
    isHomMatrix_idMatrix (add_zero n) ρ) (fun s x => ?_) (fun s x => ?_) q
  · induction x using Submodule.Quotient.induction_on with
    | _ a =>
    change sectionMk _ _ = sectionMk _ _
    congr 1
    exact Subtype.ext (matLin_idMatrix_idMatrix _)
  · induction x using Submodule.Quotient.induction_on with
    | _ a =>
    change sectionMk _ _ = sectionMk _ _
    congr 1
    exact Subtype.ext (matLin_idMatrix_idMatrix _)

end Transfer

end SGPT.GAGA.PN
