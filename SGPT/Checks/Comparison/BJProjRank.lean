import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionMixedEulerDifferences
import SGPT.Foundations.Envelope.AlgGeom.SchemeModuleStalkLinearity
import SGPT.Foundations.Envelope.AlgGeom.Canonical.GenericLineSections
import SGPT.Foundations.Envelope.AlgGeom.Canonical.InvertibleLineAtlas
import SGPT.Foundations.Envelope.AlgGeom.SchemePointClosureIntegral
import SGPT.Support.Alterations.Regular

/-!
# Intersection numbers against a coherent sheaf and its generic rank (lane BJ-PROJ, R3 step 4)

Let `X` be an integral projective scheme over a field `k` with `dim X ≤ d`, let `L₁, …, L_d` be
invertible sheaves and `G` a coherent sheaf. Then

  `(L₁ ⋯ L_d · G) = rk(G) · (L₁ ⋯ L_d · 𝒪_X)`   (`mixedEulerDifference_eq_genericRank_mul`),

where `rk(G) = dim_{K(X)} G_η` is the dimension of the stalk of `G` at the generic point over the
function field (`genericRank`); this dimension is finite (`genericFiber_finite`).

Proof: a prime filtration of `G` (SGPT.Foundations.Envelope) has successive quotients `i_* T` with `T`
invertible on an integral closed subscheme `i : Z ⟶ X`. If `Z ≠ X` the quotient has zero generic
stalk and, since `dim Z < d`, vanishing intersection number; if `Z = X` the quotient is invertible
on `X`, has one-dimensional generic stalk, and its intersection number is that of `𝒪_X`. Both
sides are additive in short exact sequences (the stalk at the generic point is exact,
`rank_genericFiber_shortExact`).

Blueprint: `claude-bj-proj.tex` (`claude-bj-proj:rank`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Opposite

universe u

namespace SGPT.NAPotential.BJProj

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion
  SGPT.Foundations.Envelope.SchemeModuleStalkLinearity

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Stalks of sheaves of modules -/

section stalks

variable {X : Scheme.{u}}

/-- The stalk maps of a composition. -/
theorem stalkMapLinear_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (x : X) :
    stalkMapLinear (f ≫ g) x = (stalkMapLinear g x).comp (stalkMapLinear f x) := by
  apply LinearMap.ext
  intro m
  simp only [stalkMapLinear_apply, LinearMap.comp_apply, Functor.map_comp]
  rfl

/-- The stalk map of the identity. -/
theorem stalkMapLinear_id (M : X.Modules) (x : X) :
    stalkMapLinear (𝟙 M) x = LinearMap.id := by
  apply LinearMap.ext
  intro m
  rw [stalkMapLinear_apply, CategoryTheory.Functor.map_id]
  rfl

/-- An isomorphism of sheaves of modules induces linear equivalences of the stalks. -/
def stalkLinearEquiv {M N : X.Modules} (e : M ≅ N) (x : X) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  LinearEquiv.ofLinearMap (stalkMapLinear e.hom x) (stalkMapLinear e.inv x)
    (by rw [← stalkMapLinear_comp, e.inv_hom_id, stalkMapLinear_id])
    (by rw [← stalkMapLinear_comp, e.hom_inv_id, stalkMapLinear_id])

/-- The stalks of a zero object are trivial. -/
theorem stalk_subsingleton_of_isZero (M : X.Modules) (hM : IsZero M) (x : X) :
    Subsingleton (M.presheaf.stalk x) := by
  have hid : (𝟙 M : M ⟶ M) = 0 := (IsZero.iff_id_eq_zero M).mp hM
  have hz (m : M.presheaf.stalk x) : m = 0 := by
    obtain ⟨U, hxU, s, hs⟩ := M.presheaf.exists_germ_eq m
    have hs0 : s = 0 := by
      have h := congrArg (fun v : M ⟶ M => v.val.app (op U) s) hid
      exact h
    exact hs.symm.trans ((congrArg (M.presheaf.germ U x hxU) hs0).trans
      (M.presheaf.germ U x hxU).hom.map_zero)
  exact ⟨fun m n => (hz m).trans (hz n).symm⟩

/-- The value of a stalk map on a germ. -/
theorem stalkMapLinear_germ {M N : X.Modules} (f : M ⟶ N) (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(M, U)) :
    stalkMapLinear f x (M.presheaf.germ U x hx s) =
      N.presheaf.germ U x hx ((f.val.app (op U)).hom s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ((Scheme.Modules.toPresheaf X).map f) s

/-- A monomorphism of sheaves of modules is injective on sections. -/
theorem app_injective_of_mono {M N : X.Modules} (f : M ⟶ N) [Mono f] (U : X.Opens) :
    Function.Injective (f.val.app (op U)).hom :=
  PresheafOfModules.injective_of_mono ((Scheme.Modules.toPresheafOfModules X).map f) (op U)

/-- A short exact sequence of sheaves of modules is exact in the middle on sections. -/
theorem app_exact_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact) (U : X.Opens)
    (s : Γ(S.X₂, U)) (hs : (S.g.val.app (op U)).hom s = 0) :
    ∃ t : Γ(S.X₁, U), (S.f.val.app (op U)).hom t = s := by
  have := hS.mono_f
  have h1 : (S.map (Scheme.Modules.toPresheafOfModules X)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
  have hm : Mono (S.map (Scheme.Modules.toPresheafOfModules X)).f := by
    change Mono ((Scheme.Modules.toPresheafOfModules X).map S.f)
    infer_instance
  have h2 : ((S.map (Scheme.Modules.toPresheafOfModules X)).map
      (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op U))).Exact :=
    h1.map_of_mono_of_preservesKernel _ hm inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).mp h2 s hs

/-- Restriction commutes with morphisms of sheaves of modules. -/
theorem app_restrict {M N : X.Modules} (f : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    (f.val.app (op V)).hom (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op ((f.val.app (op U)).hom s) := by
  exact PresheafOfModules.naturality_apply f.val (homOfLE h).op s

/-- The stalk of a monomorphism is injective. -/
theorem stalkMapLinear_injective_of_mono {M N : X.Modules} (f : M ⟶ N) [Mono f] (x : X) :
    Function.Injective (stalkMapLinear f x) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  obtain ⟨U, hxU, s, rfl⟩ := M.presheaf.exists_germ_eq m
  rw [stalkMapLinear_germ] at hm
  have hm' : N.presheaf.germ U x hxU ((f.val.app (op U)).hom s) =
      N.presheaf.germ U x hxU 0 := hm.trans (map_zero _).symm
  obtain ⟨V, hxV, a, b, h⟩ := N.presheaf.germ_eq _ _ _ _ _ hm'
  cases Subsingleton.elim a b
  have hVU : V ≤ U := a.le
  have h0 : (f.val.app (op V)).hom (M.presheaf.map (homOfLE hVU).op s) = 0 := by
    rw [app_restrict]
    rw [show homOfLE hVU = a from Subsingleton.elim _ _]
    exact h.trans (map_zero _)
  have hs : M.presheaf.map (homOfLE hVU).op s = 0 :=
    app_injective_of_mono f V (h0.trans (map_zero _).symm)
  calc M.presheaf.germ U x hxU s
      = M.presheaf.germ V x hxV (M.presheaf.map (homOfLE hVU).op s) :=
        (M.presheaf.germ_res_apply (homOfLE hVU) x hxV s).symm
    _ = 0 := by rw [hs, map_zero]

/-- The stalk of an epimorphism of quasi-coherent sheaves is surjective. -/
theorem stalkMapLinear_surjective_of_epi {M N : X.Modules} (f : M ⟶ N) [Epi f]
    [M.IsQuasicoherent] [N.IsQuasicoherent] (x : X) :
    Function.Surjective (stalkMapLinear f x) := by
  intro n
  obtain ⟨U, hxU, s, rfl⟩ := N.presheaf.exists_germ_eq n
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  obtain ⟨t, ht⟩ := Scheme.Modules.isQuasicoherent_app_surjective_of_epi V hV f
    (N.presheaf.map (homOfLE hVU).op s)
  refine ⟨M.presheaf.germ V x hxV t, ?_⟩
  exact (stalkMapLinear_germ f x V hxV t).trans
    ((congrArg (N.presheaf.germ V x hxV) ht).trans
      (N.presheaf.germ_res_apply (homOfLE hVU) x hxV s))

/-- The stalks of a short exact sequence of sheaves of modules are exact in the middle. -/
theorem stalkMapLinear_exact (S : ShortComplex X.Modules) (hS : S.ShortExact) (x : X) :
    LinearMap.ker (stalkMapLinear S.g x) = LinearMap.range (stalkMapLinear S.f x) := by
  apply le_antisymm
  · intro m hm
    rw [LinearMap.mem_ker] at hm
    obtain ⟨U, hxU, s, rfl⟩ := S.X₂.presheaf.exists_germ_eq m
    rw [stalkMapLinear_germ] at hm
    have hm' : S.X₃.presheaf.germ U x hxU ((S.g.val.app (op U)).hom s) =
        S.X₃.presheaf.germ U x hxU 0 := hm.trans (map_zero _).symm
    obtain ⟨V, hxV, a, b, h⟩ := S.X₃.presheaf.germ_eq _ _ _ _ _ hm'
    cases Subsingleton.elim a b
    have hVU : V ≤ U := a.le
    have h0 : (S.g.val.app (op V)).hom (S.X₂.presheaf.map (homOfLE hVU).op s) = 0 := by
      rw [app_restrict]
      rw [show homOfLE hVU = a from Subsingleton.elim _ _]
      exact h.trans (map_zero _)
    obtain ⟨t, ht⟩ := app_exact_of_shortExact S hS V _ h0
    refine ⟨S.X₁.presheaf.germ V x hxV t, ?_⟩
    exact (stalkMapLinear_germ S.f x V hxV t).trans
      ((congrArg (S.X₂.presheaf.germ V x hxV) ht).trans
        (S.X₂.presheaf.germ_res_apply (homOfLE hVU) x hxV s))
  · rintro _ ⟨m, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← stalkMapLinear_comp, S.zero]
    obtain ⟨U, hxU, s, rfl⟩ := S.X₁.presheaf.exists_germ_eq m
    rw [stalkMapLinear_germ]
    exact map_zero _

end stalks

/-! ### The generic rank -/

section rank

variable {X : Scheme.{u}} [IsIntegral X]

/-- **The generic rank** of a sheaf of modules on an integral scheme: the dimension over the
function field of its stalk at the generic point. -/
def genericRank (G : X.Modules) : ℕ :=
  Module.finrank X.functionField (CanonicalGeometry.genericBundleFiber G)

/-- The rank of the generic stalk is additive in short exact sequences of quasi-coherent
sheaves. -/
theorem rank_genericFiber_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    Module.rank X.functionField (CanonicalGeometry.genericBundleFiber S.X₂) =
      Module.rank X.functionField (CanonicalGeometry.genericBundleFiber S.X₁) +
        Module.rank X.functionField (CanonicalGeometry.genericBundleFiber S.X₃) := by
  have := hS.mono_f
  have := hS.epi_g
  let f : CanonicalGeometry.genericBundleFiber S.X₁ →ₗ[X.functionField]
      CanonicalGeometry.genericBundleFiber S.X₂ := stalkMapLinear S.f (genericPoint X)
  let g : CanonicalGeometry.genericBundleFiber S.X₂ →ₗ[X.functionField]
      CanonicalGeometry.genericBundleFiber S.X₃ := stalkMapLinear S.g (genericPoint X)
  have hf : Function.Injective f := stalkMapLinear_injective_of_mono S.f (genericPoint X)
  have hg : Function.Surjective g := stalkMapLinear_surjective_of_epi S.g (genericPoint X)
  have hfg : LinearMap.ker g = LinearMap.range f := stalkMapLinear_exact S hS (genericPoint X)
  have h := LinearMap.rank_range_add_rank_ker g
  rw [rank_range_of_surjective g hg, hfg, rank_range_of_injective f hf] at h
  rw [← h, add_comm]

/-- Isomorphic sheaves have generic stalks of the same rank. -/
theorem rank_genericFiber_of_iso {M N : X.Modules} (e : M ≅ N) :
    Module.rank X.functionField (CanonicalGeometry.genericBundleFiber M) =
      Module.rank X.functionField (CanonicalGeometry.genericBundleFiber N) := by
  let E : CanonicalGeometry.genericBundleFiber M ≃ₗ[X.functionField]
      CanonicalGeometry.genericBundleFiber N := stalkLinearEquiv e (genericPoint X)
  exact E.rank_eq

/-- An invertible sheaf has generic rank one. -/
theorem rank_genericFiber_of_isInvertible (T : X.Modules) (hT : IsInvertible T) :
    Module.rank X.functionField (CanonicalGeometry.genericBundleFiber T) = 1 := by
  obtain ⟨U, hU, ⟨e⟩⟩ := (CanonicalGeometry.invertibleLineAtlas T hT).exists_generic_frame
  let : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  obtain ⟨hfin, hfree, hrank⟩ := CanonicalGeometry.genericBundleFiber_finite_free_rank_one e
  rw [← Module.finrank_eq_rank, hrank]
  simp

end rank

/-! ### Push-forwards from closed subschemes -/

section pushforward

variable {X Z : Scheme.{u}}

/-- Sections of a sheaf of modules over the empty open set vanish. -/
theorem section_eq_zero_of_eq_bot (T : Z.Modules) (W : Z.Opens) (hW : W = ⊥) (s : Γ(T, W)) :
    s = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext (F := T.val.presheaf) T.isSheaf
  intro x hx
  rw [hW] at hx
  exact (hx : x ∈ (⊥ : Z.Opens)).elim

/-- The stalk of a push-forward at a point outside the closed image vanishes. -/
theorem stalk_pushforward_subsingleton (i : Z ⟶ X) (hi : IsClosed (Set.range i)) (T : Z.Modules)
    (x : X) (hx : x ∉ Set.range i) :
    Subsingleton (((Scheme.Modules.pushforward i).obj T).presheaf.stalk x) := by
  let N := (Scheme.Modules.pushforward i).obj T
  let W : X.Opens := ⟨(Set.range i)ᶜ, hi.isOpen_compl⟩
  have hz (m : N.presheaf.stalk x) : m = 0 := by
    obtain ⟨U, hxU, s, hs⟩ := N.presheaf.exists_germ_eq m
    let V : X.Opens := U ⊓ W
    have hxV : x ∈ V := ⟨hxU, hx⟩
    have hVU : V ≤ U := inf_le_left
    have hbot : i ⁻¹ᵁ V = ⊥ := by
      ext z
      simp only [Scheme.Hom.mem_preimage, Opens.coe_bot, Set.mem_empty_iff_false, iff_false,
        SetLike.mem_coe]
      intro hz
      exact hz.2 ⟨z, rfl⟩
    have hs0 : N.presheaf.map (homOfLE hVU).op s = 0 :=
      section_eq_zero_of_eq_bot T (i ⁻¹ᵁ V) hbot _
    calc m = N.presheaf.germ U x hxU s := hs.symm
      _ = N.presheaf.germ V x hxV (N.presheaf.map (homOfLE hVU).op s) :=
        (N.presheaf.germ_res_apply (homOfLE hVU) x hxV s).symm
      _ = 0 := by rw [hs0, map_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Push-forward along an isomorphism is the pull-back along its inverse. -/
def pushforwardIsoPullbackInv (i : Z ⟶ X) [IsIso i] :
    Scheme.Modules.pushforward i ≅ Scheme.Modules.pullback (inv i) :=
  let E : Z.Modules ≌ X.Modules := CategoryTheory.Equivalence.mk
    (Scheme.Modules.pushforward i) (Scheme.Modules.pushforward (inv i))
    ((Scheme.Modules.pushforwardId Z).symm ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id i).symm ≪≫
      (Scheme.Modules.pushforwardComp i (inv i)).symm)
    (Scheme.Modules.pushforwardComp (inv i) i ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id i) ≪≫ Scheme.Modules.pushforwardId X)
  E.toAdjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction (inv i))

/-- The push-forward of an invertible sheaf along an isomorphism is invertible. -/
theorem isInvertible_pushforward_of_isIso (i : Z ⟶ X) [IsIso i] (T : Z.Modules)
    (hT : IsInvertible T) : IsInvertible ((Scheme.Modules.pushforward i).obj T) :=
  (hT.pullback (inv i)).of_iso ((pushforwardIsoPullbackInv i).app T)

end pushforward

/-! ### The rank formula -/

section formula

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
  (p : X ⟶ Spec (.of k)) [IsProjective p]

private theorem isProjective_closedComp {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  refine ⟨E, hE, hEF, i ≫ j, inferInstance, ?_⟩
  exact (Category.assoc i j E.projectiveBundleπ).trans
    (congrArg (fun q => i ≫ q) hjp)

/-- The rank formula along a prime filtration. -/
private theorem rank_and_mixedEuler_of_filtration
    {n : ℕ} {G : X.Modules} (hfil : ActualCoherentPrimeFiltration n G) :
    ∃ r : ℕ, Module.rank X.functionField (CanonicalGeometry.genericBundleFiber G) = r ∧
      ∀ (d : ℕ), topologicalKrullDim X ≤ d → ∀ ls : List X.Modules, ls.length = d →
        (∀ L ∈ ls, IsInvertible L) →
        mixedEulerDifference p ls G = r * mixedEulerDifference p ls (unitObj X) := by
  induction hfil with
  | zero M hM =>
    refine ⟨0, ?_, ?_⟩
    · have h : Subsingleton (CanonicalGeometry.genericBundleFiber M) :=
        stalk_subsingleton_of_isZero M hM (genericPoint X)
      simp
    · intro d hdim ls hlen hls
      rw [mixedEulerDifference_eq_zero_of_isZero p ls hls M hM]
      simp
  | iso e _ ih =>
    obtain ⟨r, hr, hm⟩ := ih
    exact ⟨r, (rank_genericFiber_of_iso e).symm.trans hr, fun d hdim ls hlen hls =>
      (mixedEulerDifference_eq_of_iso p ls e).symm.trans (hm d hdim ls hlen hls)⟩
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e _ ih =>
    obtain ⟨r, hr, hm⟩ := ih
    let : S.X₁.IsQuasicoherent := hQ₁
    let : S.X₂.IsQuasicoherent := hQ₂
    let : S.X₃.IsQuasicoherent := hQ₃
    let : S.X₁.IsFiniteType := hF₁
    let : S.X₂.IsFiniteType := hF₂
    let : S.X₃.IsFiniteType := hF₃
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
    let Z := I.subscheme
    let i : Z ⟶ X := I.subschemeι
    have hrank := rank_genericFiber_shortExact S hS
    have hrange : Set.range i = closure ({eta} : Set X) := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    by_cases heta : genericPoint X ∈ closure ({eta} : Set X)
    · -- the quotient is invertible on `X`
      have hsurj : Function.Surjective i := by
        rw [← Set.range_eq_univ, hrange]
        apply Set.eq_univ_of_univ_subset
        rw [← (genericPoint_spec X).def]
        exact closure_minimal (Set.singleton_subset_iff.mpr heta) isClosed_closure
      let : Surjective i := ⟨hsurj⟩
      let : IsIso i := isIso_of_isClosedImmersion_of_surjective i
      have hinv : IsInvertible S.X₃ := (isInvertible_pushforward_of_isIso i T hT).of_iso e
      refine ⟨r + 1, ?_, ?_⟩
      · rw [hrank, hr, rank_genericFiber_of_isInvertible S.X₃ hinv]
        simp
      · intro d hdim ls hlen hls
        rw [mixedEulerDifference_add p ls hls S hS, hm d hdim ls hlen hls,
          mixedEulerDifference_eq_unit_of_dimension_le p d hdim ls hlen hls S.X₃ hinv]
        push_cast
        ring
    · -- the quotient is supported on a proper closed subset
      have hstalk : Subsingleton (CanonicalGeometry.genericBundleFiber S.X₃) := by
        have h1 := stalk_pushforward_subsingleton i (hrange ▸ isClosed_closure) T
          (genericPoint X) (hrange ▸ heta)
        exact (stalkLinearEquiv e (genericPoint X)).toEquiv.subsingleton
      refine ⟨r, ?_, ?_⟩
      · rw [hrank, hr]
        have : Module.rank X.functionField (CanonicalGeometry.genericBundleFiber S.X₃) = 0 :=
          rank_subsingleton' _ _
        rw [this, add_zero]
      · intro d hdim ls hlen hls
        have hzero : mixedEulerDifference p ls S.X₃ = 0 := by
          let : IsIntegral Z := SchemePointClosureIntegral.isIntegral_pointClosure eta
          let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
          let : Z.IsSeparated := ⟨by
            have h : IsSeparated (i ≫ terminal.from X) := inferInstance
            simpa only [terminal.comp_from] using h⟩
          let : IsProjective (i ≫ p) := isProjective_closedComp i p
          let : T.IsQuasicoherent := hT.isQuasicoherent
          let : T.IsFinitePresentation := hT.isFinitePresentation
          let : T.IsFiniteType :=
            SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := Z.ringCatSheaf) T
          have hInv : ∀ K ∈ ls.map (Scheme.Modules.pullback i).obj, IsInvertible K := by
            intro K hK
            obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hK
            exact (hls L hL).pullback i
          rw [mixedEulerDifference_eq_of_iso p ls e,
            mixedEulerDifference_pushforward p i ls hls T]
          rcases d with _ | d'
          · exfalso
            have := SGPT.Support.Alterations.subsingleton_of_topologicalKrullDim_le_zero X
              (by simpa using hdim)
            exact heta (Subsingleton.elim eta (genericPoint X) ▸ subset_closure rfl)
          · have hne : I.support ≠ ⊤ := by
              intro htop
              apply heta
              have : genericPoint X ∈ (I.support : Set X) := by rw [htop]; trivial
              rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
              exact this
            have hdimZ : topologicalKrullDim Z ≤ d' :=
              properClosed_dimension_drop I.support hne d' hdim
            exact mixedEulerDifference_eq_zero_of_dimension_le d' (i ≫ p) hdimZ _
              (by simpa using hlen) hInv T
        rw [mixedEulerDifference_add p ls hls S hS, hm d hdim ls hlen hls, hzero, add_zero]

include p in
/-- The generic stalk of a coherent sheaf on an integral projective scheme is finite-dimensional
over the function field. -/
theorem genericFiber_finite (G : X.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    Module.Finite X.functionField (CanonicalGeometry.genericBundleFiber G) := by
  obtain ⟨n, hfil⟩ := exists_finite_coherent_primeFiltration p G
  obtain ⟨r, hr, -⟩ := rank_and_mixedEuler_of_filtration p hfil
  exact Module.finite_of_rank_eq_nat hr

/-- **Intersection numbers against a coherent sheaf.** On an integral projective scheme `X` of
dimension `≤ d`, for invertible `L₁, …, L_d` and coherent `G`:
`(L₁ ⋯ L_d · G) = rk(G) · (L₁ ⋯ L_d · 𝒪_X)`. -/
theorem mixedEulerDifference_eq_genericRank_mul (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (ls : List X.Modules) (hlen : ls.length = d) (hls : ∀ L ∈ ls, IsInvertible L)
    (G : X.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    mixedEulerDifference p ls G = (genericRank G : ℤ) * mixedEulerDifference p ls (unitObj X) := by
  obtain ⟨n, hfil⟩ := exists_finite_coherent_primeFiltration p G
  obtain ⟨r, hr, hm⟩ := rank_and_mixedEuler_of_filtration p hfil
  rw [hm d hdim ls hlen hls, genericRank, Module.finrank_eq_of_rank_eq hr]

end formula

end SGPT.NAPotential.BJProj
