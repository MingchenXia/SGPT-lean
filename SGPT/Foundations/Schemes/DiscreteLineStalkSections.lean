import SGPT.Foundations.Schemes.DiscreteSingletonStalkGeometry

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The original atlas frame gives its TRUE coefficient map on the actual
singleton open, without a supplied trivialization. -/
def LineBundleAtlas.discreteSingletonCoefficientEquiv {X : Scheme.{u}} [DiscreteTopology X]
    {M : X.Modules} (a : LineBundleAtlas M) (x : X) :
    Γ(M, discreteSingletonOpen X x) ≃ₗ[Γ(X, discreteSingletonOpen X x)]
      Γ(X, discreteSingletonOpen X x) := by
  let j := (a.covers x).choose
  have hx : x ∈ a.opens j := (a.covers x).choose_spec
  have h : discreteSingletonOpen X x ≤ a.opens j := by
    intro y hy
    have hyx : y = x := hy
    simpa only [hyx] using hx
  exact (a.frame j).coefficients (homOfLE h)

/-- The literal singleton coefficient/germ map preserves ORIGINAL global
base scalars and the actual structural base scalars on every actual stalk. -/
def LineBundleAtlas.discreteGlobalStalkCoefficientLinear {X : Scheme.{u}} [DiscreteTopology X]
    {M : X.Modules} (a : LineBundleAtlas M) {K : Type u} [CommRing K]
    (c : K →+* Γ(X, ⊤)) :
    letI : ∀ x : X, Algebra K (X.presheaf.stalk x) := fun x ↦ schemeStalkGlobalConstantsAlgebra c x
    actualSchemeModuleBaseGlobalSections M c →ₗ[K] (∀ x : X, X.presheaf.stalk x) := by
  letI : ∀ x : X, Algebra K (X.presheaf.stalk x) := fun x ↦ schemeStalkGlobalConstantsAlgebra c x
  exact {
    toFun := fun s x ↦ X.presheaf.germ (discreteSingletonOpen X x) x (Set.mem_singleton x)
      (a.discreteSingletonCoefficientEquiv x
        (M.val.map (discreteSingletonOpen X x).leTop.op s))
    map_add' := by
      intro s t
      funext x
      simp only [Pi.add_apply, map_add]
    map_smul' := by
      intro k s
      funext x
      let U := discreteSingletonOpen X x
      let e := a.discreteSingletonCoefficientEquiv x
      change X.presheaf.germ U x (Set.mem_singleton x)
        (e (M.val.map U.leTop.op (c k • (show Γ(M, ⊤) from s)))) =
          X.presheaf.Γgerm x (c k) *
            X.presheaf.germ U x (Set.mem_singleton x) (e (M.val.map U.leTop.op s))
      rw [PresheafOfModules.map_smul]
      rw [e.map_smul]
      change X.presheaf.germ U x (Set.mem_singleton x)
        (X.presheaf.map U.leTop.op (c k) * e (M.val.map U.leTop.op s)) = _
      rw [(X.presheaf.germ U x (Set.mem_singleton x)).hom.map_mul]
      rw [X.presheaf.Γgerm_res_apply x (Set.mem_singleton x)] }


/-- Actual singleton sheaf gluing and actual frame/germ inverses give
bijectivity, including an empty or infinite discrete scheme. -/
theorem LineBundleAtlas.discreteGlobalStalkCoefficientLinear_bijective
    {X : Scheme.{u}} [DiscreteTopology X] {M : X.Modules} (a : LineBundleAtlas M)
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) :
    letI : ∀ x : X, Algebra K (X.presheaf.stalk x) := fun x ↦ schemeStalkGlobalConstantsAlgebra c x
    Function.Bijective (a.discreteGlobalStalkCoefficientLinear c) := by
  classical
  let : ∀ x : X, Algebra K (X.presheaf.stalk x) := fun x ↦ schemeStalkGlobalConstantsAlgebra c x
  let S := discreteSingletonOpen X
  let G (x : X) := (discreteSingletonGermIso X x).commRingCatIsoToRingEquiv
  constructor
  · intro s t h
    apply (bundleGlobalToCech_bijective M S (discreteSingletonOpens_covers X)).injective
    apply Subtype.ext
    funext x
    apply (a.discreteSingletonCoefficientEquiv x).injective
    apply (G x).injective
    exact congrFun h x
  · intro z
    let l (x : X) : Γ(M, S x) :=
      (a.discreteSingletonCoefficientEquiv x).symm ((G x).symm (z x))
    have hl : ∀ x y,
        M.val.map (homOfLE (show S x ⊓ S y ≤ S x from inf_le_left)).op (l x) =
          M.val.map (homOfLE (show S x ⊓ S y ≤ S y from inf_le_right)).op (l y) := by
      intro x y
      by_cases hxy : x = y
      · subst y
        congr 1
      · have hV : S x ⊓ S y = ⊥ := by
          apply bot_unique
          intro t ht
          have htx : t = x := ht.1
          have hty : t = y := ht.2
          exact (hxy (htx.symm.trans hty)).elim
        let : Subsingleton Γ(X, S x ⊓ S y) := CommRingCat.subsingleton_of_isTerminal
          (TopCat.Sheaf.isTerminalOfEqEmpty X.sheaf hV)
        let : Subsingleton Γ(M, S x ⊓ S y) :=
          Module.subsingleton Γ(X, S x ⊓ S y) Γ(M, S x ⊓ S y)
        exact @Subsingleton.elim Γ(M, S x ⊓ S y) inferInstance _ _
    obtain ⟨s, hs⟩ := (bundleGlobalToCech_bijective M S
      (discreteSingletonOpens_covers X)).surjective ⟨l, hl⟩
    refine ⟨s, ?_⟩
    funext x
    have hx := congrArg (fun w : bundleCechSections M S ↦ w.val x) hs
    change M.val.map (S x).leTop.op s = l x at hx
    change G x (a.discreteSingletonCoefficientEquiv x
      (M.val.map (S x).leTop.op s)) = z x
    rw [hx]
    dsimp only [l]
    rw [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- A genuine ORIGINAL-base linear equivalence from actual global line
sections to the product of SAME actual scheme stalk rings. -/
def LineBundleAtlas.discreteGlobalStalkCoefficientEquiv
    {X : Scheme.{u}} [DiscreteTopology X] {M : X.Modules} (a : LineBundleAtlas M)
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) :
    letI : ∀ x : X, Algebra K (X.presheaf.stalk x) := fun x ↦ schemeStalkGlobalConstantsAlgebra c x
    actualSchemeModuleBaseGlobalSections M c ≃ₗ[K] (∀ x : X, X.presheaf.stalk x) := by
  letI : ∀ x : X, Algebra K (X.presheaf.stalk x) := fun x ↦ schemeStalkGlobalConstantsAlgebra c x
  exact LinearEquiv.ofBijective (a.discreteGlobalStalkCoefficientLinear c)
    (a.discreteGlobalStalkCoefficientLinear_bijective c)



end
end SGPT.Foundations.Schemes
