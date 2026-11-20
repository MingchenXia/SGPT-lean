import SGPT.TestCurve.GeomLinSection

/-!
# Linearizations as isomorphisms of sheaves of modules

Lane GEOM-LIN. `GeomLinearization` records an isomorphism `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` by its matrix
coefficients in the pulled-back frames (`IsCechIso`). Here the isomorphism is an actual
isomorphism of sheaves of modules on `𝔾_m × 𝓧`:

* `FramedPullback b g`: a model of the pull-back `g^* M` of a line bundle with atlas
  `(U_i, e_i)`: a sheaf of modules with frames `g^* e_i` over `g⁻¹(U_i)` whose transition functions
  are the pull-backs `g^♯ τ_{ii'}` (this characterizes `g^* M` up to a unique frame-preserving
  isomorphism; it is the encoding of `𝓛|_{𝓧 ∖ 𝓧₀} ≅ q^* L`);
* `FramedPullback.isoCoeff`: the matrix coefficients `Φ(g^* e_i) = φ_{ij} h^* e_j` of an
  isomorphism `Φ : P ≅ P'` of sheaves of modules; they are units (`isUnit_isoCoeff`) and satisfy
  the compatibility `IsCechIso` (`isCechIso_isoUnits`);
* `SheafLinearization T`: a `𝔾_m`-action with an isomorphism of sheaves of modules
  `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` (between framed models), the cocycle condition and the compatibility with
  the identification over `𝔾_m`; it gives a `GeomLinearization` (`toGeomLinearization`), hence
  the `𝔾_m`-representation on sections (`toSectionLinearization`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GeomLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin

section Framed

variable {Y Z : Scheme.{0}} {M : Y.Modules} (b : LineBundleAtlas M)

/-- **A model of the pull-back `g^* M`** of a line bundle `M` with atlas `(U_i, e_i)` along
`g : Z ⟶ Y`: a sheaf of modules on `Z` with frames over `g⁻¹(U_i)` (the frames `g^* e_i`) whose
transition functions are `g^♯ τ_{ii'}`. -/
structure FramedPullback (g : Z ⟶ Y) where
  /-- The sheaf `g^* M`. -/
  sheaf : Z.Modules
  /-- The frame `g^* e_i` over `g⁻¹(U_i)`. -/
  frame : ∀ i : b.I, LocalBundleFrame sheaf (g ⁻¹ᵁ b.opens i)
  /-- The transition functions are the pull-backs `g^♯ τ_{ii'}`. -/
  transition : ∀ i i' : b.I,
    transitionFun (frame i) (frame i') (homOfLE (g.preimage_mono inf_le_left))
        (homOfLE (g.preimage_mono inf_le_right)) =
      g.app (b.opens i ⊓ b.opens i') (atlasTransition b i i')

/-- Restriction of sections of a sheaf of modules. -/
abbrev sres {N : Z.Modules} {U V : Z.Opens} (k : V ⟶ U) (s : bundleSections N U) :
    bundleSections N V :=
  N.val.map k.op s

theorem sres_smul {N : Z.Modules} {U V : Z.Opens} (k : V ⟶ U) (r : Γ(Z, U))
    (s : bundleSections N U) : sres k (r • s) = Z.presheaf.map k.op r • sres k s :=
  PresheafOfModules.map_smul N.val k.op r s

namespace FramedPullback

variable {b} {g : Z ⟶ Y} (P : FramedPullback b g)

theorem smap_smap {N : Z.Modules} {U V W : Z.Opens} (k1 : W ⟶ V) (k2 : V ⟶ U)
    (s : bundleSections N U) : sres k1 (sres k2 s) = sres (k1 ≫ k2) s :=
  (PresheafOfModules.map_comp_apply _ k2.op k1.op s).symm

/-- The frame section `g^* e_i`. -/
def sec (i : b.I) : bundleSections P.sheaf (g ⁻¹ᵁ b.opens i) :=
  ((P.frame i).coefficients (𝟙 _)).symm 1

theorem coeff_res_sec (i : b.I) {W : Z.Opens} (k : W ⟶ g ⁻¹ᵁ b.opens i) :
    (P.frame i).coefficients k (P.sheaf.val.map k.op (P.sec i)) = 1 := by
  have h := (P.frame i).coefficients_restrict (𝟙 _) k (P.sec i)
  rw [Category.comp_id] at h
  rw [h, sec, LinearEquiv.apply_symm_apply, map_one]

/-- A section over `W ⊆ g⁻¹(U_i)` is its coefficient times the frame. -/
theorem eq_smul_sec (i : b.I) {W : Z.Opens} (k : W ⟶ g ⁻¹ᵁ b.opens i)
    (s : bundleSections P.sheaf W) :
    s = (P.frame i).coefficients k s • P.sheaf.val.map k.op (P.sec i) := by
  apply ((P.frame i).coefficients k).injective
  rw [LinearEquiv.map_smul, coeff_res_sec, smul_eq_mul, mul_one]

/-- `g^* e_i = g^♯(τ_{ii'}) g^* e_{i'}` on every `W ⊆ g⁻¹(U_i ∩ U_{i'})`. -/
theorem res_sec_transition (i i' : b.I) {W : Z.Opens}
    (k : W ⟶ g ⁻¹ᵁ (b.opens i ⊓ b.opens i')) :
    sres (k ≫ homOfLE (g.preimage_mono inf_le_left)) (P.sec i) =
      Z.presheaf.map k.op (g.app _ (atlasTransition b i i')) •
        sres (k ≫ homOfLE (g.preimage_mono inf_le_right)) (P.sec i') := by
  apply ((P.frame i').coefficients (k ≫ homOfLE (g.preimage_mono inf_le_right))).injective
  rw [LinearEquiv.map_smul, coeff_res_sec, smul_eq_mul, mul_one,
    localBundleFrameTransition_coefficients (P.frame i) (P.frame i')
      (k ≫ homOfLE (g.preimage_mono inf_le_left)) (k ≫ homOfLE (g.preimage_mono inf_le_right)),
    coeff_res_sec, mul_one, localBundleFrameTransition_restrict]
  rw [← P.transition i i']
  rfl

end FramedPullback

/-! ### Isomorphisms of framed pull-backs -/

namespace FramedPullback

variable {b} {g h : Z ⟶ Y} (P : FramedPullback b g) (P' : FramedPullback b h)
  (Φ : P.sheaf ≅ P'.sheaf)

/-- **The matrix coefficients of `Φ : g^* M ≅ h^* M`**: `Φ(g^* e_i) = φ_{ij} h^* e_j` on
`g⁻¹(U_i) ∩ h⁻¹(U_j)`. -/
def isoCoeff (i j : b.I) : Γ(Z, cechOpen b g h i j) :=
  (P'.frame j).coefficients (homOfLE inf_le_right)
    (Φ.hom.val.app (op _) (sres (homOfLE (inf_le_left :
      cechOpen b g h i j ≤ _)) (P.sec i)))

theorem iso_app_res_sec (i j : b.I) :
    Φ.hom.val.app (op _) (sres (homOfLE (inf_le_left :
      cechOpen b g h i j ≤ _)) (P.sec i)) =
    isoCoeff P P' Φ i j • sres (homOfLE (inf_le_right :
      cechOpen b g h i j ≤ _)) (P'.sec j) :=
  P'.eq_smul_sec j _ _

theorem hom_inv_app {W : Z.Opens} (x : bundleSections P'.sheaf W) :
    Φ.hom.val.app (op W) (Φ.inv.val.app (op W) x) = x := by
  have h := congrArg (fun φ : P'.sheaf ⟶ P'.sheaf => φ.val.app (op W) x) Φ.inv_hom_id
  exact h

theorem hom_app_smul {W : Z.Opens} (r : Γ(Z, W)) (x : bundleSections P.sheaf W) :
    Φ.hom.val.app (op W) (r • x) = r • Φ.hom.val.app (op W) x :=
  (Φ.hom.val.app (op W)).hom.map_smul r x

theorem hom_app_res {V W : Z.Opens} (k : W ⟶ V) (x : bundleSections P.sheaf V) :
    Φ.hom.val.app (op W) (sres k x) = sres k (Φ.hom.val.app (op V) x) :=
  PresheafOfModules.naturality_apply Φ.hom.val k.op x

/-- The matrix coefficients of an isomorphism are units. -/
theorem isUnit_isoCoeff (i j : b.I) : IsUnit (isoCoeff P P' Φ i j) := by
  let W := cechOpen b g h i j
  have h1 := P.eq_smul_sec i (homOfLE (inf_le_left : W ≤ _))
    (Φ.inv.val.app (op W) (sres (homOfLE (inf_le_right : W ≤ _)) (P'.sec j)))
  have h2 := congrArg (Φ.hom.val.app (op W)) h1
  rw [hom_inv_app, hom_app_smul, iso_app_res_sec, smul_smul] at h2
  have h3 := congrArg ((P'.frame j).coefficients (homOfLE (inf_le_right : W ≤ _))) h2
  rw [coeff_res_sec, LinearEquiv.map_smul, coeff_res_sec, smul_eq_mul, mul_one] at h3
  exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact h3.symm⟩

/-- The matrix coefficients as units. -/
def isoUnits (i j : b.I) : (Γ(Z, cechOpen b g h i j))ˣ := (isUnit_isoCoeff P P' Φ i j).unit

/-- **An isomorphism of framed pull-backs is a Čech isomorphism.** -/
theorem isCechIso_isoUnits : IsCechIso b g h (isoUnits P P' Φ) := by
  intro i i' j j'
  let W := cechOverlap b g h i i' j j'
  let kL : W ⟶ cechOpen b g h i j := homOfLE (cechOverlap_le_left b g h i i' j j')
  let kR : W ⟶ cechOpen b g h i' j' := homOfLE (cechOverlap_le_right b g h i i' j j')
  let kg : W ⟶ g ⁻¹ᵁ (b.opens i ⊓ b.opens i') := homOfLE inf_le_left
  let kh : W ⟶ h ⁻¹ᵁ (b.opens j ⊓ b.opens j') := homOfLE inf_le_right
  -- `Φ(g^* e_i)` restricted to `W`, computed in two ways
  have e1 := congrArg (sres kL) (iso_app_res_sec P P' Φ i j)
  rw [← hom_app_res, smap_smap, sres_smul, smap_smap] at e1
  have e2 := congrArg (sres kR) (iso_app_res_sec P P' Φ i' j')
  rw [← hom_app_res, smap_smap, sres_smul, smap_smap] at e2
  have tg := P.res_sec_transition i i' kg
  have th := P'.res_sec_transition j j' kh
  have hL : (kL ≫ homOfLE (inf_le_left : cechOpen b g h i j ≤ _)) =
      kg ≫ homOfLE (g.preimage_mono inf_le_left) := rfl
  have hR : (kR ≫ homOfLE (inf_le_left : cechOpen b g h i' j' ≤ _)) =
      kg ≫ homOfLE (g.preimage_mono inf_le_right) := rfl
  have hL' : (kL ≫ homOfLE (inf_le_right : cechOpen b g h i j ≤ _)) =
      kh ≫ homOfLE (h.preimage_mono inf_le_left) := rfl
  have hR' : (kR ≫ homOfLE (inf_le_right : cechOpen b g h i' j' ≤ _)) =
      kh ≫ homOfLE (h.preimage_mono inf_le_right) := rfl
  rw [hL, tg, hom_app_smul, ← hR, e2, hL', th, smul_smul, smul_smul] at e1
  have e3 := congrArg ((P'.frame j').coefficients (kh ≫ homOfLE (h.preimage_mono inf_le_right)))
    e1
  rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ← hR', coeff_res_sec, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at e3
  change g.appLE _ W inf_le_left (atlasTransition b i i') *
      Z.presheaf.map kR.op (isoCoeff P P' Φ i' j') =
    Z.presheaf.map kL.op (isoCoeff P P' Φ i j) *
      h.appLE _ W inf_le_right (atlasTransition b j j')
  have hg : g.appLE _ W inf_le_left (atlasTransition b i i') =
      Z.presheaf.map kg.op (g.app _ (atlasTransition b i i')) := rfl
  have hh : h.appLE _ W inf_le_right (atlasTransition b j j') =
      Z.presheaf.map kh.op (h.app _ (atlasTransition b j j')) := rfl
  rw [hg, hh]
  exact e3

end FramedPullback

end Framed

/-! ### Linearizations as sheaf isomorphisms -/

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

/-- **A `𝔾_m`-linearization of `𝓛` as an isomorphism of sheaves of modules**
([BHJ17, Def. 2.2], [MFK, Def. 1.6]): a `𝔾_m`-action `σ`, models `σ^* 𝓛`, `pr₂^* 𝓛` of the
pulled-back line bundles (sheaves of modules on `𝔾_m × 𝓧` with the pulled-back frames), an
isomorphism of sheaves of modules `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛`, the cocycle condition and the
compatibility `Φ(σ^* ε_j) = pr₂^* ε_j` with the identification over `𝔾_m`. -/
structure SheafLinearization (T : TestConfiguration f a) where
  /-- The `𝔾_m`-action. -/
  action : GmAction T
  /-- The sheaf `σ^* 𝓛`. -/
  src : FramedPullback T.extAtlas action.smulMap
  /-- The sheaf `pr₂^* 𝓛`. -/
  tgt : FramedPullback T.extAtlas (gmProj T)
  /-- The isomorphism `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛`. -/
  iso : src.sheaf ≅ tgt.sheaf
  /-- The cocycle condition. -/
  cocycle : action.IsCocycle (FramedPullback.isoUnits src tgt iso)
  /-- `Φ(σ^* ε_j) = pr₂^* ε_j`. -/
  frame_eq : ∀ k : a.I, FramedPullback.isoUnits src tgt iso (.inr k) (.inr k) = 1

namespace SheafLinearization

variable {T : TestConfiguration f a} (Λ : SheafLinearization T)

/-- A sheaf-theoretic linearization is a (Čech) `GeomLinearization`. -/
def toGeomLinearization : GeomLinearization T where
  action := Λ.action
  phi := FramedPullback.isoUnits Λ.src Λ.tgt Λ.iso
  isCechIso := FramedPullback.isCechIso_isoUnits Λ.src Λ.tgt Λ.iso
  cocycle := Λ.cocycle
  phi_frame := Λ.frame_eq

/-- **A sheaf-theoretic `𝔾_m`-linearization induces the `𝔾_m`-representation on the sections**
(`X` integral projective). -/
def toSectionLinearization [IsIntegral X] (E : ClosedProjectiveEmbedding f) :
    SectionLinearization T :=
  Λ.toGeomLinearization.toSectionLinearization E

end SheafLinearization

/-- A test configuration whose linearization is given as an isomorphism of sheaves of modules
is a geometrically linearized test configuration. -/
def GeomLinearizedTestConfiguration.ofSheaf (T : TestConfiguration f a)
    (Λ : SheafLinearization T) : GeomLinearizedTestConfiguration f a :=
  ⟨T, Λ.toGeomLinearization⟩

end SGPT.TestCurve.GeomLin
