import SGPT.Checks.Comparison.BJProjEuler
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionMixedEulerDifferences
import SGPT.Foundations.Envelope.AlgGeom.SchemeLineProjectionFormula
import SGPT.Foundations.Envelope.AlgGeom.SchemeInvertibleTensorQuasicoherent
import SGPT.Foundations.Envelope.AlgGeom.SchemeCommonAffineLineFrames

/-!
# The projection formula for mixed Euler differences (lane BJ-PROJ, R3 step 3)

Let `g : Y ⟶ X` be a morphism of separated quasi-compact `k`-schemes, `U` a finite affine open
cover of `X`, `L₁, …, L_r` invertible sheaves on `X` that are trivial on every member of `U`, and
`M` a quasi-coherent sheaf on `Y` without higher cohomology on the inverse images of the finite
intersections of `U`. Then

  `Δ_{g^*L₁} ⋯ Δ_{g^*L_r} χ(Y, M) = Δ_{L₁} ⋯ Δ_{L_r} χ(X, g_* M)`
  (`mixedEulerDifference_pullback_of_acyclic`).

The proof is an induction on the list: `M ⊗ g^*L` is again acyclic on the inverse images (it is
isomorphic to `M` there), `χ(Y, ·) = χ(X, g_* ·)` on such sheaves (`BJProjEuler`), and
`g_*(M ⊗ g^*L) ≅ g_*M ⊗ L` (SGPT.Foundations.Envelope's projection formula for invertible sheaves).

We also prove that finitely many invertible sheaves on a quasi-compact scheme admit a common
finite affine trivializing cover (`exists_finite_affine_trivializing_cover`).

Blueprint: `claude-bj-proj.tex` (`claude-bj-proj:mixed-pushforward`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace

universe u

namespace SGPT.NAPotential.BJProj

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion
  SGPT.Foundations.Envelope.SchemeCoherentEulerCharacteristic

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Cohomology and isomorphisms -/

/-- Vanishing of a cohomology group is invariant under isomorphisms of sheaves of modules. -/
theorem subsingleton_H_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (hM : Subsingleton (CategoryTheory.Sheaf.H M.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H N.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := hM
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩

/-! ### Twisting by a pulled-back invertible sheaf that is trivial on the base -/

section twist

variable {X Y : Scheme.{u}}

/-- If `L` is trivial on the open `U` of `X` and `V ≤ g⁻¹ U`, then `M ⊗ g^*L` and `M` have
isomorphic restrictions to `V`. -/
def restrictTensorPullbackIso (g : Y ⟶ X) (L : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ unitObj U.toScheme) (V : Y.Opens)
    (hV : V ≤ g ⁻¹ᵁ U) (M : Y.Modules) :
    (M ⊗ (Scheme.Modules.pullback g).obj L).restrict V.ι ≅ M.restrict V.ι :=
  have hrange : Set.range (V.ι ≫ g) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hV y.2
  SchemeInvertibleTensorQuasicoherent.restrictTensorIsoOfFrame M
    ((Scheme.Modules.pullback g).obj L) V
    (restrictIsoOfPullbackIso ((Scheme.Modules.pullback g).obj L) V
      ((Scheme.Modules.pullbackComp V.ι g).app L ≪≫
        pullbackCompositeTrivialization (IsOpenImmersion.lift U.ι (V.ι ≫ g) hrange) U.ι
          (V.ι ≫ g) (IsOpenImmersion.lift_fac U.ι (V.ι ≫ g) hrange) L e))

end twist

/-! ### Common trivializing covers -/

section cover

/-- Finitely many invertible sheaves on a quasi-compact scheme are trivial on the members of a
common finite affine open cover. -/
theorem exists_finite_affine_trivializing_cover {X : Scheme.{u}} [CompactSpace X]
    (ls : List X.Modules) (hls : ∀ L ∈ ls, IsInvertible L) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens), IsOpenCover U ∧
      (∀ i, IsAffineOpen (U i)) ∧
      ∀ L ∈ ls, ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L ≅ unitObj (U i).toScheme) := by
  classical
  -- around every point, a common trivializing affine open
  have hpt : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∀ L ∈ ls, Nonempty ((Scheme.Modules.pullback V.1.ι).obj L ≅ unitObj V.1.toScheme) := by
    intro x
    induction ls with
    | nil =>
      obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact ⟨⟨V, hV⟩, hxV, fun L hL => absurd hL (by simp)⟩
    | cons L ls ih =>
      obtain ⟨V, hxV, hV⟩ := ih (fun K hK => hls K (by simp [hK]))
      obtain ⟨W, hxW, hWV, eL, -⟩ := SchemeCommonAffineLineFrames.exists_in_open L (unitObj X)
        (hls L (by simp)) isInvertible_unit x V.1 hxV
      refine ⟨W, hxW, ?_⟩
      intro K hK
      rcases List.mem_cons.mp hK with rfl | hK
      · exact eL
      · obtain ⟨eK⟩ := hV K hK
        exact ⟨pullbackCompositeTrivialization (X.homOfLE hWV) V.1.ι W.1.ι
          (X.homOfLE_ι hWV) K eK⟩
  choose V hxV hV using hpt
  have hc : (Set.univ : Set X) ⊆ ⋃ x : X, ((V x).1 : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((V x).1 : Set X)) (fun x => (V x).1.isOpen) hc
  refine ⟨a, inferInstance, fun x => (V x.1).1, ?_, fun x => (V x.1).2, fun L hL x => hV x.1 L hL⟩
  change (⨆ x : a, (V x.1).1) = ⊤
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (ha (Set.mem_univ x))
  obtain ⟨hya, hxy⟩ := Set.mem_iUnion.mp hy
  exact Opens.mem_iSup.mpr ⟨⟨y, hya⟩, hxy⟩

end cover

/-! ### The projection formula for mixed Euler differences -/

section mixed

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **Projection formula for mixed Euler differences.** For a morphism `g : Y ⟶ X` of separated
quasi-compact `k`-schemes, invertible sheaves `L₁, …, L_r` on `X` trivial on the members of a
finite affine open cover `U` of `X`, and a quasi-coherent `M` on `Y` that is acyclic on the inverse
images of the finite intersections of `U`:
`Δ_{g^*L₁} ⋯ Δ_{g^*L_r} χ(Y, M) = Δ_{L₁} ⋯ Δ_{L_r} χ(X, g_* M)`. -/
theorem mixedEulerDifference_pullback_of_acyclic [CompactSpace X] [CompactSpace Y]
    [X.IsSeparated] [Y.IsSeparated] (g : Y ⟶ X) [QuasiCompact g] (f : X ⟶ Spec (.of k))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) (ls : List X.Modules) :
    (∀ L ∈ ls, IsInvertible L) →
    (∀ L ∈ ls, ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L ≅ unitObj (U i).toScheme)) →
    ∀ (M : Y.Modules) [M.IsQuasicoherent],
    (∀ (a : ℕ) (i : Fin (a + 1) → ι) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict (g ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l))).ι).sheaf (q + 1))) →
    mixedEulerDifference (g ≫ f) (ls.map (Scheme.Modules.pullback g).obj) M =
      mixedEulerDifference f ls ((Scheme.Modules.pushforward g).obj M) := by
  induction ls with
  | nil =>
    intro _ _ M _ hacyc
    exact eulerCharacteristic_pushforward_of_acyclic g f M U hU hUa hacyc
  | cons L ls ih =>
    intro hls htriv M _ hacyc
    have hL : IsInvertible L := hls L (by simp)
    have ht : ∀ K ∈ ls, IsInvertible K := fun K hK => hls K (by simp [hK])
    have htt : ∀ K ∈ ls, ∀ i,
        Nonempty ((Scheme.Modules.pullback (U i).ι).obj K ≅ unitObj (U i).toScheme) :=
      fun K hK => htriv K (by simp [hK])
    let K := (Scheme.Modules.pullback g).obj L
    have hK : IsInvertible K := hL.pullback g
    let : (M ⊗ K).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M K hK
    have hacyc' : ∀ (a : ℕ) (i : Fin (a + 1) → ι) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
        ((M ⊗ K).restrict (g ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l))).ι).sheaf (q + 1)) := by
      intro a i q
      obtain ⟨e⟩ := htriv L (by simp) (i 0)
      have hle : g ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l)) ≤ g ⁻¹ᵁ U (i 0) := by
        intro y hy
        exact leOfHom (Limits.Pi.π (fun l : Fin (a + 1) => U (i l)) 0) hy
      exact subsingleton_H_of_iso (restrictTensorPullbackIso g L (U (i 0)) e _ hle M).symm
        (q + 1) (hacyc a i q)
    let e : (Scheme.Modules.pushforward g).obj M ⊗ L ≅
        (Scheme.Modules.pushforward g).obj (M ⊗ K) :=
      SchemeLineProjectionFormula.lineProjectionFormulaObj g L hL M
    change mixedEulerDifference (g ≫ f) (ls.map (Scheme.Modules.pullback g).obj) (M ⊗ K) -
        mixedEulerDifference (g ≫ f) (ls.map (Scheme.Modules.pullback g).obj) M =
      mixedEulerDifference f ls ((Scheme.Modules.pushforward g).obj M ⊗ L) -
        mixedEulerDifference f ls ((Scheme.Modules.pushforward g).obj M)
    rw [mixedEulerDifference_eq_of_iso f ls e, ih ht htt (M ⊗ K) hacyc', ih ht htt M hacyc]

end mixed

end SGPT.NAPotential.BJProj
