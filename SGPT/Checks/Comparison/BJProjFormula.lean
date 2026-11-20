import SGPT.Checks.Comparison.BJProjRelative
import SGPT.Checks.Comparison.BJProjRank
import SGPT.Checks.Comparison.BJIntersectCut
import SGPT.Checks.Comparison.BJIntersectPullbackVanishing
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalAmpleConeGeneration
import SGPT.Foundations.Envelope.AlgGeom.SchemeInvertibleTensorFiniteType

/-!
# The projection formula for intersection numbers (lane BJ-PROJ, R3)

Let `X` be an integral projective scheme over a field `k` with `dim X ≤ d`, `π : Y ⟶ X` a morphism
from a projective `k`-scheme with `dim Y ≤ d`, and `A` an ample invertible sheaf on `Y`. For
invertible `L₁, …, L_d` on `X` and coherent `G` on `Y`,

  `(π^*L₁ ⋯ π^*L_d · G)_Y = rk(π_*(G ⊗ A^m)) · (L₁ ⋯ L_d)_X`   for `m ≫ 0`

(`mixedEulerDifference_pullback_eq_genericRank_mul`). Proof: replacing `G` by `G ⊗ A^m` does not
change the left side (`Δ_{A^m}` of a top intersection number vanishes); for `m ≫ 0` the sheaf
`G ⊗ A^m` is acyclic on the inverse images of a finite affine cover of `X` trivializing the `Lᵢ`
(relative Serre vanishing, `BJProjRelative`), so the left side is
`(L₁ ⋯ L_d · π_*(G ⊗ A^m))_X` (`BJProjPullback`), which is `rk · (L₁ ⋯ L_d)_X` by the rank
formula on the integral `X` (`BJProjRank`), `π_*(G ⊗ A^m)` being coherent.

The rank does not depend on the classes: there is one `e = rk π_*(A^m)` with

  `(π^*θ₁ ⋯ π^*θ_d)_Y = e · (θ₁ ⋯ θ_d)_X`   for all `θᵢ ∈ Pic(X)_ℚ`

(`exists_interFormQ_pullback_eq`), and `e > 0` when `π` is surjective and `Y` integral
(`exists_interFormQ_pullback_eq_of_surjective`). For a generically finite `π` of degree `e` between
integral schemes of the same dimension this is the projection formula of
[Debarre, Prop. 1.10]; for `dim π(Y) < d` it recovers (with `e = 0`) the vanishing of
`BJIntersectPullbackVanishing`. If `π` is an isomorphism over a nonempty open subset of `X`, then
`e = 1` (`interFormQ_pullback_eq_of_isIso_restrict`, birational invariance), and signs of
intersection numbers descend along surjections (`interFormQ_nonpos_of_pullback_nonpos`).

Blueprint: `claude-bj-proj.tex` (`claude-bj-proj:projection`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJProj

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion SGPT.Foundations.Envelope.SchemeLineAmpleness
open SGPT.NAPotential.BJIntersect

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

section formula

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
  (pX : X ⟶ Spec (.of k)) [IsProjective pX] [CompactSpace Y] [Y.IsSeparated] (π : Y ⟶ X)
  [IsProjective (π ≫ pX)]

omit [CompactSpace X] [X.IsSeparated] in
include pX in
/-- A projective scheme over a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_isProjective : IsLocallyNoetherian X := by
  let hp := ProjectiveFactorizationRingIso.of_isProjective pX
  let : IsProper pX := hp.isProper
  exact LocallyOfFiniteType.isLocallyNoetherian pX

omit [CompactSpace X] [CompactSpace Y] [Y.IsSeparated] [IsProjective (π ≫ pX)] in
/-- One twist makes `G ⊗ A^m` acyclic on the inverse images of all finite intersections of a
finite affine cover. -/
theorem exists_uniform_preimage_cohomology_bound (A : Y.Modules) (hA : IsAmple (π ≫ pX) A)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hUa : ∀ i, IsAffineOpen (U i)) (G : Y.Modules)
    [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ (a : ℕ) (i : Fin (a + 1) → ι) (q : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H
        ((CanonicalGeometry.bundleTensorPower A m ⊗ G).restrict
          (π ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l))).ι).sheaf (q + 1)) := by
  classical
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isProjective pX
  let S : Set X.Opens := Set.range (fun T : Set ι => ⨅ j ∈ T, U j) ∩ {O | IsAffineOpen O}
  have hS : S.Finite := (Set.finite_range _).inter_of_left _
  have hmem : ∀ (a : ℕ) (i : Fin (a + 1) → ι), (∏ᶜ fun l : Fin (a + 1) => U (i l)) ∈ S :=
    fun a i => ⟨⟨Set.range i, by
      rw [TopologicalSpace.Opens.piObj_eq_iInf]
      exact iInf_range⟩,
      IsAffineOpen.cechIntersection U hUa a i⟩
  have hbound : ∀ O ∈ S, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ, Subsingleton
      (CategoryTheory.Sheaf.H ((CanonicalGeometry.bundleTensorPower A m ⊗ G).restrict
        (π ⁻¹ᵁ O).ι).sheaf (q + 1)) :=
    fun O hO => exists_preimage_cohomology_bound pX π A hA hO.2 G
  choose! N hN using hbound
  refine ⟨hS.toFinset.sup N, fun m hm a i q => ?_⟩
  exact hN _ (hmem a i) m
    (le_trans (Finset.le_sup ((Set.Finite.mem_toFinset _).mpr (hmem a i))) hm) q

variable [IsIntegral X]

/-- **The projection formula with the generic rank.** -/
theorem mixedEulerDifference_pullback_eq_genericRank_mul (d : ℕ)
    (hX : topologicalKrullDim X ≤ d) (hY : topologicalKrullDim Y ≤ d) (A : Y.Modules)
    (hA : IsAmple (π ≫ pX) A) (ls : List X.Modules) (hlen : ls.length = d)
    (hls : ∀ L ∈ ls, IsInvertible L) (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      mixedEulerDifference (π ≫ pX) (ls.map (Scheme.Modules.pullback π).obj) G =
        (genericRank ((Scheme.Modules.pushforward π).obj
          (G ⊗ CanonicalGeometry.bundleTensorPower A m)) : ℤ) *
          mixedEulerDifference pX ls (unitObj X) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isProjective pX
  obtain ⟨ι, hι, U, hU, hUa, htriv⟩ := exists_finite_affine_trivializing_cover ls hls
  obtain ⟨N, hN⟩ := exists_uniform_preimage_cohomology_bound pX π A hA U hUa G
  refine ⟨N, fun m hm => ?_⟩
  let Am := CanonicalGeometry.bundleTensorPower A m
  have hAm : IsInvertible Am := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 m
  let F := G ⊗ Am
  let : F.IsQuasicoherent := SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight G Am hAm
  let : F.IsFiniteType := SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight G Am hAm
  have hpls : ∀ K ∈ ls.map (Scheme.Modules.pullback π).obj, IsInvertible K := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hK
    exact (hls L hL).pullback π
  -- twisting by `A^m` does not change the top intersection number
  have h1 : mixedEulerDifference (π ≫ pX) (ls.map (Scheme.Modules.pullback π).obj) G =
      mixedEulerDifference (π ≫ pX) (ls.map (Scheme.Modules.pullback π).obj) F := by
    have hz := mixedEulerDifference_eq_zero_of_dimension_le d (π ≫ pX) hY
      (Am :: ls.map (Scheme.Modules.pullback π).obj) (by simp [hlen])
      (by
        intro K hK
        rcases List.mem_cons.mp hK with rfl | hK
        · exact hAm
        · exact hpls K hK) G
    change mixedEulerDifference (π ≫ pX) _ (G ⊗ Am) -
      mixedEulerDifference (π ≫ pX) _ G = 0 at hz
    exact (sub_eq_zero.mp hz).symm
  -- acyclicity on the inverse images of the cover
  have hacyc : ∀ (a : ℕ) (i : Fin (a + 1) → ι) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (F.restrict (π ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l))).ι).sheaf (q + 1)) := by
    intro a i q
    exact subsingleton_H_of_iso ((restrictFunctor _).mapIso (β_ Am G)) (q + 1) (hN m hm a i q)
  have h2 := mixedEulerDifference_pullback_of_acyclic π pX U hU hUa ls hls htriv F hacyc
  let : ((Scheme.Modules.pushforward π).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact π F
  let : ((Scheme.Modules.pushforward π).obj F).IsFiniteType :=
    isFiniteType_pushforward pX π A hA F
  have h3 := mixedEulerDifference_eq_genericRank_mul pX d hX ls hlen hls
    ((Scheme.Modules.pushforward π).obj F)
  rw [h1, h2, h3]

/-- The intersection numbers of pulled-back Picard classes, in terms of the generic rank. -/
theorem interNum_pullback_eq_genericRank_mul (d : ℕ) (hX : topologicalKrullDim X ≤ d)
    (hY : topologicalKrullDim Y ≤ d) (A : Y.Modules) (hA : IsAmple (π ≫ pX) A)
    (s : Multiset (Additive X.Pic)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      interNum (π ≫ pX) d (unitObj Y) (s.map (picPullbackAdd π)) =
        (genericRank ((Scheme.Modules.pushforward π).obj
          (unitObj Y ⊗ CanonicalGeometry.bundleTensorPower A m)) : ℤ) *
          interNum pX d (unitObj X) s := by
  by_cases hs : Multiset.card s = d
  · obtain ⟨l, rfl⟩ : ∃ l : List (Additive X.Pic), (l : Multiset _) = s :=
      ⟨s.toList, Multiset.coe_toList s⟩
    have hl : l.length = d := by simpa using hs
    obtain ⟨N, hN⟩ := mixedEulerDifference_pullback_eq_genericRank_mul pX π d hX hY A hA
      (l.map fun a => picRep a.toMul) (by simp [hl])
      (by
        intro K hK
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hK
        exact picRep_isInvertible _) (unitObj Y)
    refine ⟨N, fun m hm => ?_⟩
    rw [Multiset.map_coe, interNum_coe (π ≫ pX) d _ _ (by simpa using hl),
      interNum_coe pX d _ _ hl]
    unfold interList
    rw [List.map_map]
    have hcongr := mixedEulerDifference_congr (π ≫ pX)
      (ls := l.map ((fun a => picRep a.toMul) ∘ picPullbackAdd π))
      (ms := (l.map fun a => picRep a.toMul).map (Scheme.Modules.pullback π).obj)
      (by
        rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.forall₂_same.mpr fun a _ => ?_
        exact picRep_picPullback π a.toMul) (unitObj Y)
    rw [hcongr]
    exact hN m hm
  · refine ⟨0, fun m _ => ?_⟩
    rw [interNum_of_card_ne (π ≫ pX) d _ _ (by simpa using hs),
      interNum_of_card_ne pX d _ _ hs, mul_zero]

/-- One rank for all classes: for every `M₀` there is `m ≥ M₀` such that, with
`e = rk π_*(A^m)`, `(π^*a₁ ⋯ π^*a_d)_Y = e · (a₁ ⋯ a_d)_X` for all Picard classes. -/
theorem exists_interNum_pullback_eq (d : ℕ) (hX : topologicalKrullDim X ≤ d)
    (hY : topologicalKrullDim Y ≤ d) (A : Y.Modules) (hA : IsAmple (π ≫ pX) A) (M₀ : ℕ) :
    ∃ m : ℕ, M₀ ≤ m ∧ ∀ s : Multiset (Additive X.Pic),
      interNum (π ≫ pX) d (unitObj Y) (s.map (picPullbackAdd π)) =
        (genericRank ((Scheme.Modules.pushforward π).obj
          (unitObj Y ⊗ CanonicalGeometry.bundleTensorPower A m)) : ℤ) *
          interNum pX d (unitObj X) s := by
  have key := interNum_pullback_eq_genericRank_mul pX π d hX hY A hA
  by_cases h : ∃ s₀ : Multiset (Additive X.Pic), interNum pX d (unitObj X) s₀ ≠ 0
  · obtain ⟨s₀, hs₀⟩ := h
    obtain ⟨N₀, hN₀⟩ := key s₀
    refine ⟨max M₀ N₀, le_max_left _ _, fun s => ?_⟩
    obtain ⟨N, hN⟩ := key s
    let m' := max (max M₀ N₀) N
    have e1 := hN₀ m' (le_trans (le_max_right _ _) (le_max_left _ _))
    have e2 := hN₀ (max M₀ N₀) (le_max_right _ _)
    have hr : (genericRank ((Scheme.Modules.pushforward π).obj
          (unitObj Y ⊗ CanonicalGeometry.bundleTensorPower A m')) : ℤ) =
        genericRank ((Scheme.Modules.pushforward π).obj
          (unitObj Y ⊗ CanonicalGeometry.bundleTensorPower A (max M₀ N₀))) :=
      mul_right_cancel₀ hs₀ (e1.symm.trans e2)
    rw [hN m' (le_max_right _ _), hr]
  · push Not at h
    refine ⟨M₀, le_rfl, fun s => ?_⟩
    obtain ⟨N, hN⟩ := key s
    rw [hN (max N M₀) (le_max_left _ _), h s, mul_zero, mul_zero]

/-- **The projection formula** on `ℚ`-line bundles: for `m` as in `exists_interNum_pullback_eq`
and `e = rk π_*(A^m)`, `(π^*θ₁ ⋯ π^*θ_d)_Y = e · (θ₁ ⋯ θ_d)_X` for all `θᵢ ∈ Pic(X)_ℚ`. -/
theorem exists_interFormQ_pullback_eq (d : ℕ) (hX : topologicalKrullDim X ≤ d)
    (hY : topologicalKrullDim Y ≤ d) (A : Y.Modules) (hA : IsAmple (π ≫ pX) A) (M₀ : ℕ) :
    ∃ m : ℕ, M₀ ≤ m ∧ ∀ s : Multiset (PicQ X),
      interFormQ (π ≫ pX) d hY (unitObj Y) (s.map (picPullbackQ π)) =
        (genericRank ((Scheme.Modules.pushforward π).obj
          (unitObj Y ⊗ CanonicalGeometry.bundleTensorPower A m)) : ℚ) *
          interFormQ pX d hX (unitObj X) s := by
  obtain ⟨m, hm, H⟩ := exists_interNum_pullback_eq pX π d hX hY A hA M₀
  refine ⟨m, hm, ?_⟩
  let e : ℚ := genericRank ((Scheme.Modules.pushforward π).obj
    (unitObj Y ⊗ CanonicalGeometry.bundleTensorPower A m))
  let Φ := interFormQ pX d hX (unitObj X)
  let Ψ : MultisetForm ℚ (PicQ X) :=
    ⟨fun s => e * Φ s, fun x y s => by rw [Φ.map_add, mul_add],
      fun c x s => by rw [Φ.map_smul]; ring⟩
  have key := MultisetForm.ext_tmul ((interFormQ (π ≫ pX) d hY (unitObj Y)).comp (picPullbackQ π))
    Ψ (by
      intro u
      rw [MultisetForm.comp_apply, Multiset.map_map]
      have h3 : ((picPullbackQ π) ∘ fun a : Additive X.Pic => (1 : ℚ) ⊗ₜ[ℤ] a) =
          (fun a => (1 : ℚ) ⊗ₜ[ℤ] a) ∘ picPullbackAdd π := rfl
      rw [h3, ← Multiset.map_map, interFormQ_tmul]
      change _ = e * Φ _
      rw [interFormQ_tmul, H u]
      push_cast
      rfl)
  intro s
  exact key s

end formula

/-! ### Positivity of the rank for surjective morphisms -/

section positivity

/-- A nonzero section of an invertible sheaf over the inverse image of an open `U ⊆ X` has a
nonzero germ at the generic point of `X` in the direct image, when `π` is surjective and `Y`
integral. -/
theorem genericBundleFiber_pushforward_nontrivial {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) (hπ : Function.Surjective π) (F : Y.Modules) (hF : IsInvertible F)
    (s : Γ(F, π ⁻¹ᵁ ⊤)) (hs : s ≠ 0) :
    Nontrivial (CanonicalGeometry.genericBundleFiber ((Scheme.Modules.pushforward π).obj F)) := by
  let P := (Scheme.Modules.pushforward π).obj F
  let s' : Γ(P, ⊤) := s
  refine ⟨⟨P.presheaf.germ ⊤ (genericPoint X) trivial s', 0, fun h => hs ?_⟩⟩
  have h' : P.presheaf.germ ⊤ (genericPoint X) trivial s' =
      P.presheaf.germ ⊤ (genericPoint X) trivial 0 := h.trans (map_zero _).symm
  obtain ⟨V, hηV, i, j, hij⟩ := P.presheaf.germ_eq _ _ _ _ _ h'
  have hle : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ ⊤ := fun y _ => trivial
  have hne : Nonempty (π ⁻¹ᵁ V) := by
    obtain ⟨y, hy⟩ := hπ (genericPoint X)
    exact ⟨⟨y, show π y ∈ V by rw [hy]; exact hηV⟩⟩
  have hij' : F.presheaf.map (homOfLE hle).op s = F.presheaf.map (homOfLE hle).op 0 := by
    have e1 : P.presheaf.map i.op s' = F.presheaf.map (homOfLE hle).op s := rfl
    have e2 : P.presheaf.map j.op 0 = F.presheaf.map (homOfLE hle).op 0 := rfl
    rw [← e1, ← e2]
    exact hij
  exact (CanonicalGeometry.invertibleLineAtlas F hF).restriction_injective (homOfLE hle) hij'

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
  (pX : X ⟶ Spec (.of k)) [IsProjective pX] [CompactSpace Y] [Y.IsSeparated] (π : Y ⟶ X)
  [IsProjective (π ≫ pX)] [IsIntegral X]

/-- **The projection formula for surjective morphisms of integral projective schemes.** If
`π : Y ⟶ X` is a surjective morphism of integral projective `k`-schemes with `dim X, dim Y ≤ d`,
there is a positive integer `e` with `(π^*θ₁ ⋯ π^*θ_d)_Y = e · (θ₁ ⋯ θ_d)_X` for all
`θᵢ ∈ Pic(X)_ℚ`. (For `π` generically finite, `e` is the degree `[K(Y) : K(X)]`; this
identification is not needed for the sign arguments below.) -/
theorem exists_interFormQ_pullback_eq_of_surjective [IsIntegral Y] (d : ℕ)
    (hX : topologicalKrullDim X ≤ d) (hY : topologicalKrullDim Y ≤ d)
    (hπ : Function.Surjective π) :
    ∃ e : ℕ, 0 < e ∧ ∀ s : Multiset (PicQ X),
      interFormQ (π ≫ pX) d hY (unitObj Y) (s.map (picPullbackQ π)) =
        (e : ℚ) * interFormQ pX d hX (unitObj X) s := by
  obtain ⟨A, hA⟩ := NativeRealNumericalClasses.exists_geometric_ample_line (π ≫ pX)
  obtain ⟨N₁, hN₁⟩ :=
    SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections (π ≫ pX) A hA
  obtain ⟨m, hm, H⟩ := exists_interFormQ_pullback_eq pX π d hX hY A hA N₁
  refine ⟨_, ?_, H⟩
  let Am := CanonicalGeometry.bundleTensorPower A m
  have hAm : IsInvertible Am := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 m
  obtain ⟨Gs, -⟩ := hN₁ m hm
  obtain ⟨s, hs⟩ := exists_section_not_mem_support Am hAm Gs (genericPoint Y)
  have hσ := SchemeGlobalPullbackCartierRatio.pullbackSection_ne_zero (𝟙 Y) Am hAm
    (SchemeModuleGlobalSections.sectionHom Am s) (genericPoint Y) hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hσ
    have h0 : SchemeModuleGlobalSections.sectionHom Am 0 = 0 := by
      apply SheafOfModules.hom_ext
      ext W : 2
      apply LinearMap.ext
      intro a
      have h : ((SchemeModuleGlobalSections.sectionHom Am 0).val.app W).hom a =
          (show Γ(Y, W.unop) from a) •
            Am.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op (0 : Γ(Am, ⊤)) := rfl
      rw [h, map_zero, smul_zero]
      rfl
    rw [h0, SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_zero, comp_zero]
  -- the direct image and its generic stalk
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isProjective pX
  let F := unitObj Y ⊗ Am
  let : F.IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight _ Am hAm
  let : F.IsFiniteType := SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight _ Am hAm
  let P := (Scheme.Modules.pushforward π).obj F
  let : P.IsQuasicoherent := isQuasicoherent_pushforward_of_quasiCompact π F
  let : P.IsFiniteType := isFiniteType_pushforward pX π A hA F
  let : Module.Finite X.functionField (CanonicalGeometry.genericBundleFiber P) :=
    genericFiber_finite pX P
  have hne : Nonempty (π ⁻¹ᵁ ⊤) := ⟨⟨genericPoint Y, trivial⟩⟩
  have ht : Am.presheaf.map (homOfLE (le_top : π ⁻¹ᵁ ⊤ ≤ ⊤)).op s ≠ 0 := by
    intro h0
    apply hs0
    exact (CanonicalGeometry.invertibleLineAtlas Am hAm).restriction_injective
      (homOfLE (le_top : π ⁻¹ᵁ ⊤ ≤ ⊤)) (h0.trans (map_zero _).symm)
  have hnt := genericBundleFiber_pushforward_nontrivial π hπ Am hAm _ ht
  let e : unitObj Y ⊗ Am ≅ Am :=
    ((SGPT.Support.ModularCurves.monoidalUnitObjIso Y).symm ⊗ᵢ Iso.refl Am) ≪≫ λ_ Am
  let E := stalkLinearEquiv ((Scheme.Modules.pushforward π).mapIso e) (genericPoint X)
  have : Nontrivial (CanonicalGeometry.genericBundleFiber P) := E.toEquiv.nontrivial
  exact Module.finrank_pos

/-- **Signs descend along surjections** (step (d) of the reduction of the Hodge-type
inequality): for a surjective morphism `π : Y ⟶ X` of integral projective `k`-schemes with
`dim X, dim Y ≤ d`, if `(π^*θ₁ ⋯ π^*θ_d)_Y ≤ 0` then `(θ₁ ⋯ θ_d)_X ≤ 0`. -/
theorem interFormQ_nonpos_of_pullback_nonpos [IsIntegral Y] (d : ℕ)
    (hX : topologicalKrullDim X ≤ d) (hY : topologicalKrullDim Y ≤ d)
    (hπ : Function.Surjective π) (s : Multiset (PicQ X))
    (h : interFormQ (π ≫ pX) d hY (unitObj Y) (s.map (picPullbackQ π)) ≤ 0) :
    interFormQ pX d hX (unitObj X) s ≤ 0 := by
  obtain ⟨e, he, H⟩ := exists_interFormQ_pullback_eq_of_surjective pX π d hX hY hπ
  rw [H s] at h
  by_contra hx
  push Not at hx
  have : (0 : ℚ) < (e : ℚ) * interFormQ pX d hX (unitObj X) s :=
    mul_pos (by exact_mod_cast he) hx
  linarith

/-- Signs descend along surjections: nonnegativity version. -/
theorem interFormQ_nonneg_of_pullback_nonneg [IsIntegral Y] (d : ℕ)
    (hX : topologicalKrullDim X ≤ d) (hY : topologicalKrullDim Y ≤ d)
    (hπ : Function.Surjective π) (s : Multiset (PicQ X))
    (h : 0 ≤ interFormQ (π ≫ pX) d hY (unitObj Y) (s.map (picPullbackQ π))) :
    0 ≤ interFormQ pX d hX (unitObj X) s := by
  obtain ⟨e, he, H⟩ := exists_interFormQ_pullback_eq_of_surjective pX π d hX hY hπ
  rw [H s] at h
  by_contra hx
  push Not at hx
  have : (e : ℚ) * interFormQ pX d hX (unitObj X) s < 0 :=
    mul_neg_of_pos_of_neg (by exact_mod_cast he) hx
  linarith

end positivity

/-! ### Birational morphisms -/

section birational

/-- If `π` is an isomorphism over a nonempty open `V` of the integral `X`, the direct image of an
invertible sheaf has generic rank one. -/
theorem genericRank_pushforward_eq_one {X Y : Scheme.{u}} [IsIntegral X] (π : Y ⟶ X)
    (V : X.Opens) [Nonempty V] [IsIso (π ∣_ V)] (F : Y.Modules) (hF : IsInvertible F) :
    genericRank ((Scheme.Modules.pushforward π).obj F) = 1 := by
  let P := (Scheme.Modules.pushforward π).obj F
  let ι := (π ⁻¹ᵁ V).ι
  have hG : IsInvertible (F.restrict ι) :=
    (hF.pullback ι).of_iso ((restrictFunctorIsoPullback ι).app F)
  have hG' : IsInvertible ((Scheme.Modules.pushforward (π ∣_ V)).obj (F.restrict ι)) :=
    (hG.pullback (inv (π ∣_ V))).of_iso ((pushforwardIsoPullbackInv (π ∣_ V)).app _)
  have hQ : IsInvertible (P.restrict V.ι) :=
    hG'.of_iso (restrictPushforwardIsoOfIsPullbackApp π (π ∣_ V) ι V.ι
      (isPullback_morphismRestrict π V) F)
  have hη : genericPoint X ∈ V := CanonicalGeometry.genericPoint_mem_nonempty_open V
  obtain ⟨ι', U, hU, htriv⟩ := hQ
  obtain ⟨i, hi⟩ : ∃ i, (⟨genericPoint X, hη⟩ : V.toScheme) ∈ U i := by
    have : (⟨genericPoint X, hη⟩ : V.toScheme) ∈ ⨆ i, U i := by rw [hU]; trivial
    exact Opens.mem_iSup.mp this
  obtain ⟨t⟩ := htriv i
  let W : X.Opens := V.ι ''ᵁ U i
  have hηW : genericPoint X ∈ W := ⟨⟨genericPoint X, hη⟩, hi, rfl⟩
  have : Nonempty W := ⟨⟨genericPoint X, hηW⟩⟩
  let t' : (Scheme.Modules.pullback ((U i).ι ≫ V.ι)).obj P ≅ unitObj (U i).toScheme :=
    ((Scheme.Modules.pullbackComp (U i).ι V.ι).app P).symm ≪≫
      (Scheme.Modules.pullback (U i).ι).mapIso ((restrictFunctorIsoPullback V.ι).app P).symm ≪≫ t
  let tW : (Scheme.Modules.pullback W.ι).obj P ≅ unitObj W.toScheme :=
    pullbackCompositeTrivialization (V.ι.isoImage (U i)).inv ((U i).ι ≫ V.ι) W.ι
      (Scheme.Hom.isoImage_inv_ι V.ι (U i)) P t'
  let e := overTrivializationOfRestrictIso P W (restrictIsoOfPullbackIso P W tW)
  exact (CanonicalGeometry.genericBundleFiber_finite_free_rank_one e).2.2

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
  (pX : X ⟶ Spec (.of k)) [IsProjective pX] [CompactSpace Y] [Y.IsSeparated] (π : Y ⟶ X)
  [IsProjective (π ≫ pX)] [IsIntegral X]

/-- **Birational invariance of intersection numbers.** If `π : Y ⟶ X` is an isomorphism over a
nonempty open subset of the integral projective `X`, and `dim X, dim Y ≤ d`, then
`(π^*θ₁ ⋯ π^*θ_d)_Y = (θ₁ ⋯ θ_d)_X` for all `θᵢ ∈ Pic(X)_ℚ`. -/
theorem interFormQ_pullback_eq_of_isIso_restrict (d : ℕ) (hX : topologicalKrullDim X ≤ d)
    (hY : topologicalKrullDim Y ≤ d) (V : X.Opens) [Nonempty V] [IsIso (π ∣_ V)]
    (s : Multiset (PicQ X)) :
    interFormQ (π ≫ pX) d hY (unitObj Y) (s.map (picPullbackQ π)) =
      interFormQ pX d hX (unitObj X) s := by
  obtain ⟨A, hA⟩ := NativeRealNumericalClasses.exists_geometric_ample_line (π ≫ pX)
  obtain ⟨m, -, H⟩ := exists_interFormQ_pullback_eq pX π d hX hY A hA 0
  let Am := CanonicalGeometry.bundleTensorPower A m
  have hAm : IsInvertible Am := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 m
  have hF : IsInvertible (unitObj Y ⊗ Am) :=
    (isInvertible_unit.tensorObj hAm).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso _ Am)
  rw [H s, genericRank_pushforward_eq_one π V _ hF, Nat.cast_one, one_mul]

end birational

end SGPT.NAPotential.BJProj
