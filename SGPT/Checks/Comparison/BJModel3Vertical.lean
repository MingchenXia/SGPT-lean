import SGPT.Checks.Comparison.BJModel3Normal
import SGPT.Checks.Comparison.BJModel2GaussCentral
import SGPT.Checks.Comparison.BJProjNef
import SGPT.Foundations.Envelope.AlgGeom.NormalizationCartierModulePullback
import SGPT.Foundations.Envelope.AlgGeom.CartierInvertibleSheaves
import SGPT.Foundations.Envelope.Berkovich.SchemeNormalizationDominantLift

/-!
# Vertical `ℚ`-Cartier divisors, their PL functions and relative nefness (lane BJ-MODEL3, R4)

Source: [BJ22] (`references/bj22-trivval`), §2.2 (`φ_D(v) = σ(v)(D)` for a vertical `ℚ`-Cartier
divisor `D` on a test configuration, Theorem `thm:VCarPL`: `PL(X) = {φ_D}`), §3.1 (`φ_D` is
`ω`-psh iff `ω + D` is relatively nef); the book's `eq:Gext` and `def:NApotential:L878`. Towards
`thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-model3.tex`.

On the blow-up model `𝒳 = flagModel p 𝔠 c` of a flag ideal:

* `VertCartier p 𝔠 c`: vertical effective Cartier divisors `E`, i.e. invertible ideal sheaves
  `J = 𝒪(-E)` whose zero locus lies in the central fibre `𝒳₀ = π⁻¹(X × {0})`;
* `VDiv p 𝔠 c`: vertical `ℚ`-Cartier divisors, the `ℚ`-vector space with basis the `VertCartier`;
* `VDiv.fn`: the PL function `φ_D`, `φ_E(v) = σ(v)(E) = σ(v)(J)` (Gauss point of the model,
  BJ-MODEL2) extended linearly;
* `VDiv.cls`: the class of `𝒪(D)` in `Pic(𝒳)_ℚ` (`𝒪(E) = J⁻¹`, so `cls E = -[J]`), using the
  invertible sheaf `J.toModules` of the invertible ideal sheaf `J` (SGPT.Foundations.Envelope);
* `flagVert`, `centralVert`: the divisors `(t^b 𝔞) · 𝒪_𝒳` and `𝒳₀ = 𝓘 · 𝒪_𝒳` on a dominating
  model, with `φ = b - φ_𝔞` and `φ = 1`; `flagDiv = b 𝒳₀ - E_{t^b 𝔞}` has `φ_{flagDiv} = φ_𝔞`
  ([BJ22, §2.1]: `𝔞 · 𝒪_𝒳 = 𝒪_𝒳(D)` and `φ_𝔞 = φ_D`);
* `VDiv.pullback`: pull-back along a domination map of models; `φ` is invariant and the class
  is the pulled-back class; domination maps are dominant and lift uniquely to the normalized
  models (`existsUnique_normModel_lift`);
* `mem_representable_of_mem_plSubmodule`: **every PL function is `φ_D`** for a vertical
  `ℚ`-Cartier divisor on some model ([BJ22, `thm:VCarPL`], inclusion `PL ⊆ {φ_D}`);
* `relNefCone`: the cone of `ℚ`-classes nef on a set (spanned by the classes of invertible
  sheaves nef on it, BJ-INTERSECT's `IsNefOn`), stable under pull-back;
* `IsOmegaPshPL`: `φ` is an `ω`-psh PL function: `φ = φ_D` on a model with `π^*ω + D` nef on
  the central fibre ([BJ22, §3.1]); stable under midpoints (common models).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.Foundations.Envelope SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJModel SGPT.NAPotential.BJIntersect FlagIdealBound

/-! ### Pull-back of `ℚ`-line bundles -/

section picPullback

universe u

/-- Pull-back of additive Picard classes along a composite. -/
theorem picPullbackAdd_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Additive Z.Pic) :
    picPullbackAdd (g ≫ h) a = picPullbackAdd g (picPullbackAdd h a) := by
  obtain ⟨b, rfl⟩ : ∃ b : Z.Pic, Additive.ofMul b = a := ⟨a.toMul, rfl⟩
  rw [← lineClass_picRep b]
  change Additive.ofMul (CurvePicardDegrees.picPullback (g ≫ h)
      (CurvePicardDegrees.lineClass (picRep b) (picRep_isInvertible b))) =
    Additive.ofMul (CurvePicardDegrees.picPullback g (CurvePicardDegrees.picPullback h
      (CurvePicardDegrees.lineClass (picRep b) (picRep_isInvertible b))))
  rw [CurvePicardDegrees.picPullback_lineClass, CurvePicardDegrees.picPullback_lineClass,
    CurvePicardDegrees.picPullback_lineClass]
  apply congrArg Additive.ofMul
  apply Units.ext
  rw [CurvePicardDegrees.lineClass_val, CurvePicardDegrees.lineClass_val]
  exact congr_toSkeleton_of_iso ((Scheme.Modules.pullbackComp g h).app _).symm

/-- Pull-back of `ℚ`-line bundles along a composite. -/
theorem picPullbackQ_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (θ : PicQ Z) :
    picPullbackQ (g ≫ h) θ = picPullbackQ g (picPullbackQ h θ) := by
  induction θ using TensorProduct.induction_on with
  | zero => simp
  | tmul q a =>
    simp only [picPullbackQ, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
    rw [picPullbackAdd_comp]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The class of a pulled-back invertible sheaf is the pulled-back class. -/
theorem picPullbackQ_picQ {X Y : Scheme.{u}} (f : X ⟶ Y) (L : {L : Y.Modules // Scheme.Modules.IsInvertible L}) :
    picPullbackQ f (picQ L) = picQ ⟨(Scheme.Modules.pullback f).obj L.1, L.2.pullback f⟩ := by
  simp only [picQ, picPullbackQ, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
  congr 1
  exact congrArg Additive.ofMul (CurvePicardDegrees.picPullback_lineClass f L.1 L.2)

/-- Isomorphic invertible sheaves have the same `ℚ`-class. -/
theorem picQ_eq_of_iso {X : Scheme.{u}} {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hM : Scheme.Modules.IsInvertible M) (e : L ≅ M) : picQ ⟨L, hL⟩ = picQ ⟨M, hM⟩ := by
  simp only [picQ]
  rw [lineCls_eq_of_iso hL hM e]

end picPullback

/-! ### The relatively nef cone -/

section nefCone

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}} [CompactSpace Y]

/-- **The cone of `ℚ`-classes nef on `W`**: the convex cone of `Pic(Y)_ℚ` spanned by the classes
of the invertible sheaves nef on `W` (nonnegative degree on every closed integral curve of `Y`
inside `W`; BJ-INTERSECT's `IsNefOn`). A class lies in it iff a positive multiple is the class of
an invertible sheaf nef on `W`. For `W` the central fibre of a test configuration this is
relative nefness over `𝔸¹` ([BJ22, §3.1]). -/
def relNefCone (q : Y ⟶ Spec (.of k)) (W : Set Y) : PointedCone ℚ (PicQ Y) :=
  PointedCone.hull ℚ
    {θ | ∃ N : {N : Y.Modules // Scheme.Modules.IsInvertible N}, IsNefOn q N.1 W ∧ θ = picQ N}

theorem picQ_mem_relNefCone (q : Y ⟶ Spec (.of k)) {W : Set Y}
    (N : {N : Y.Modules // Scheme.Modules.IsInvertible N})
    (hN : IsNefOn q N.1 W) : picQ N ∈ relNefCone q W :=
  Submodule.subset_span ⟨N, hN, rfl⟩

theorem relNefCone_mono (q : Y ⟶ Spec (.of k)) {W W' : Set Y} (hW : W' ⊆ W) :
    relNefCone q W ≤ relNefCone q W' :=
  Submodule.span_le.mpr fun _ ⟨N, hN, hθ⟩ => Submodule.subset_span ⟨N, hN.mono hW, hθ⟩

/-- **Pull-backs of relatively nef classes are relatively nef** (BJ-PROJ's
`IsNefOn.pullback_morphism`). -/
theorem picPullbackQ_mem_relNefCone {Y' : Scheme.{u}} [CompactSpace Y'] (q : Y ⟶ Spec (.of k))
    [IsProjective q] (f : Y' ⟶ Y) [IsProjective (f ≫ q)] {W : Set Y} {θ : PicQ Y}
    (hθ : θ ∈ relNefCone q W) : picPullbackQ f θ ∈ relNefCone (f ≫ q) (f ⁻¹' W) := by
  induction hθ using Submodule.span_induction with
  | mem θ hθ =>
    obtain ⟨N, hN, rfl⟩ := hθ
    rw [picPullbackQ_picQ]
    exact picQ_mem_relNefCone _ _ (IsNefOn.pullback_morphism f N.2 hN)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [show c • x = (c : ℚ) • x from rfl, map_smul]
    exact Submodule.smul_mem _ c hx

end nefCone

/-! ### Vertical divisors on the blow-up models -/

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **The central fibre** `𝒳₀ = π⁻¹(X × {0})` of the blow-up model. -/
def centralFibre (𝔠 : FlagIdeal X) (c : ℤ) : Set (flagModel p 𝔠 c) :=
  flagModelπ p 𝔠 c ⁻¹' ((centralIdeal p).support : Set (productLine p))

/-- **Vertical effective Cartier divisors** on the model: invertible ideal sheaves `J = 𝒪(-E)`
whose zero locus lies in the central fibre. -/
structure VertCartier (𝔠 : FlagIdeal X) (c : ℤ) where
  /-- The ideal sheaf `𝒪(-E)`. -/
  ideal : (flagModel p 𝔠 c).IdealSheafData
  isInvertible : ideal.IsInvertible
  support_subset : (ideal.support : Set (flagModel p 𝔠 c)) ⊆ centralFibre p 𝔠 c

/-- **Vertical `ℚ`-Cartier divisors** on the model: formal `ℚ`-combinations of vertical effective
Cartier divisors. -/
abbrev VDiv (𝔠 : FlagIdeal X) (c : ℤ) := VertCartier p 𝔠 c →₀ ℚ

variable {p}

namespace VertCartier

variable {𝔠 : FlagIdeal X} {c : ℤ}

/-- The invertible sheaf `J = 𝒪(-E)` of a vertical effective Cartier divisor. -/
def line (E : VertCartier p 𝔠 c) :
    {L : (flagModel p 𝔠 c).Modules // Scheme.Modules.IsInvertible L} :=
  ⟨E.ideal.toModules, E.isInvertible.isInvertibleModule_toModules⟩

/-- **The PL function of a vertical effective Cartier divisor**: `φ_E(v) = σ(v)(E)`, the value of
the Gauss extension `σ(v)` ([BJ22, §2.2]; `eq:Gext`) on the ideal `𝒪(-E)`. -/
def fn (E : VertCartier p 𝔠 c) (v : BerkovichPoint p) : ℝ :=
  ((gaussModelPoint v 𝔠 c).idealVal E.ideal).toReal

end VertCartier

namespace VDiv

variable {𝔠 : FlagIdeal X} {c : ℤ}

/-- **The PL function `φ_D` of a vertical `ℚ`-Cartier divisor** ([BJ22, §2.2]):
`φ_{∑ qᵢ Eᵢ} = ∑ qᵢ σ(·)(Eᵢ)`. -/
def fn : VDiv p 𝔠 c →ₗ[ℚ] (BerkovichPoint p → ℝ) :=
  Finsupp.linearCombination ℚ VertCartier.fn

/-- **The class of `𝒪(D)`** in `Pic(𝒳)_ℚ`: `cls E = [𝒪(E)] = -[𝒪(-E)]`. -/
def cls : VDiv p 𝔠 c →ₗ[ℚ] PicQ (flagModel p 𝔠 c) :=
  Finsupp.linearCombination ℚ fun E => -picQ E.line

omit [IsIntegral X] in
@[simp] theorem fn_single (E : VertCartier p 𝔠 c) (q : ℚ) :
    fn (Finsupp.single E q) = q • E.fn := by
  simp [fn]

omit [IsProjective p] [IsIntegral X] in
@[simp] theorem cls_single (E : VertCartier p 𝔠 c) (q : ℚ) :
    cls (Finsupp.single E q) = q • -picQ E.line := by
  simp [cls]

end VDiv

/-! ### The divisors of flag ideals and of the central fibre -/

section flag

variable {𝔠 : FlagIdeal X} {c : ℤ} {𝔞 : FlagIdeal X} {b : ℤ}

omit [IsProjective p] [IsIntegral X] in
/-- The zero locus of `(t^b 𝔞) · 𝒪` lies in the central fibre. -/
theorem support_comap_flagSheaf_subset (𝔞 : FlagIdeal X) (b : ℤ) :
    (((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔠 c)).support : Set (flagModel p 𝔠 c)) ⊆
      centralFibre p 𝔠 c := by
  rw [Scheme.IdealSheafData.support_comap]
  intro x hx
  exact support_flagSheaf_le p 𝔞 b hx

/-- **The vertical Cartier divisor `E_{t^b 𝔞} = (t^b 𝔞) · 𝒪`** on a model dominating the model of
`(𝔞, b)` ([BJ22, §2.1]). -/
def flagVert (h : Dominates p 𝔠 c 𝔞 b) : VertCartier p 𝔠 c where
  ideal := (flagSheaf p 𝔞 b).comap (flagModelπ p 𝔠 c)
  isInvertible := h.1
  support_subset := support_comap_flagSheaf_subset 𝔞 b

omit [IsIntegral X] in
/-- **`φ_{E_{t^b 𝔞}} = b - φ_𝔞`** ([BJ22, §2.1], BJ-MODEL2's
`phi_eq_sub_idealVal_gaussModelPoint_of_model`). -/
theorem fn_flagVert (h : Dominates p 𝔠 c 𝔞 b) (hb : IsWeightBound 𝔞 b) (v : BerkovichPoint p) :
    (flagVert h).fn v = b - 𝔞.phi v := by
  have := phi_eq_sub_idealVal_gaussModelPoint_of_model v 𝔠 c 𝔞 hb
  simp only [VertCartier.fn, flagVert]
  linarith

omit [IsProjective p] [IsIntegral X] in
/-- The pair `(t^0, 1)`: its ideal `t^1 (t^0) = 𝓘` is the ideal of the central fibre. -/
theorem flagSheaf_monomial_zero_one : flagSheaf p (FlagIdeal.monomial X 0) 1 = centralIdeal p := by
  rw [flagSheaf_monomial p (show (0 : ℤ) ≤ 1 by norm_num)]
  simp

/-- **The central fibre `𝒳₀ = 𝓘 · 𝒪`** as a vertical Cartier divisor on a model on which it is
invertible (a model dominating the model of `((t^0), 1)`). -/
abbrev centralVert (h : Dominates p 𝔠 c (FlagIdeal.monomial X 0) 1) : VertCartier p 𝔠 c :=
  flagVert h

omit [IsIntegral X] in
/-- **`φ_{𝒳₀} = 1`** (`σ(v)(t) = 1`, `eq:Gext`). -/
theorem fn_centralVert (h : Dominates p 𝔠 c (FlagIdeal.monomial X 0) 1) (v : BerkovichPoint p) :
    (centralVert h).fn v = 1 := by
  rw [fn_flagVert h (isWeightBound_monomial 0 |>.mono (by norm_num)) v, FlagIdeal.phi_monomial]
  norm_num

/-- **The vertical `ℚ`-Cartier divisor `D_𝔞 = b 𝒳₀ - E_{t^b 𝔞}` of a flag ideal**, with
`𝔞 · 𝒪_𝒳 = 𝒪_𝒳(D_𝔞)` ([BJ22, §2.1]). -/
def flagDiv (h0 : Dominates p 𝔠 c (FlagIdeal.monomial X 0) 1) (h : Dominates p 𝔠 c 𝔞 b) :
    VDiv p 𝔠 c :=
  Finsupp.single (centralVert h0) (b : ℚ) - Finsupp.single (flagVert h) 1

omit [IsIntegral X] in
/-- **`φ_{D_𝔞} = φ_𝔞`** ([BJ22, §2.1]). -/
theorem fn_flagDiv (h0 : Dominates p 𝔠 c (FlagIdeal.monomial X 0) 1) (h : Dominates p 𝔠 c 𝔞 b)
    (hb : IsWeightBound 𝔞 b) : VDiv.fn (flagDiv h0 h) = 𝔞.phi := by
  funext v
  simp only [flagDiv, map_sub, VDiv.fn_single, Pi.sub_apply, Pi.smul_apply, one_smul,
    fn_centralVert h0 v, fn_flagVert h hb v]
  rw [Rat.smul_def, Rat.cast_intCast]
  ring

omit [IsIntegral X] in
/-- `φ_{c 𝒳₀} = c`: constants are PL functions of vertical divisors. -/
theorem fn_single_centralVert (h0 : Dominates p 𝔠 c (FlagIdeal.monomial X 0) 1) (q : ℚ) :
    VDiv.fn (Finsupp.single (centralVert h0) q) = fun _ => (q : ℝ) := by
  funext v
  simp [fn_centralVert h0 v, Rat.smul_def]

end flag

/-! ### Domination maps -/

section domination

variable {𝔠 𝔠' : FlagIdeal X} {c c' : ℤ}

/-- **Domination maps are dominant**: a morphism `g : 𝒳_{𝔠'} ⟶ 𝒳_𝔠` over `X × ℙ¹` maps the generic
point to the generic point (both blow-downs are isomorphisms over the dense open complement of the
cosupport of `t^c 𝔠`). -/
theorem isDominant_of_comp_eq (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') : IsDominant g := by
  let := productLine_isIntegral_of_isProjective p
  let W : (productLine p).Opens := (flagSheaf p 𝔠 c).support.compl
  let π := flagModelπ p 𝔠 c
  let : IsIso (π ∣_ W) := flagModelπ_isIso_restrict p 𝔠 c
  have hW : Nonempty W := by
    by_contra hne
    apply support_flagSheaf_ne_top p 𝔠 c
    ext z
    simp only [TopologicalSpace.Closeds.coe_top, Set.mem_univ, iff_true]
    by_contra hz
    exact hne ⟨⟨z, hz⟩⟩
  obtain ⟨h1, -⟩ := flagModelπ_genericPoint p 𝔠 c
  obtain ⟨h1', -⟩ := flagModelπ_genericPoint p 𝔠' c'
  have hηW : genericPoint (productLine p) ∈ W :=
    ((genericPoint_spec (productLine p)).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have hgη : g (genericPoint (flagModel p 𝔠' c')) = genericPoint (flagModel p 𝔠 c) := by
    have hx : π (g (genericPoint (flagModel p 𝔠' c'))) = genericPoint (productLine p) := by
      rw [← Scheme.Hom.comp_apply, hg, h1']
    have hm1 : g (genericPoint (flagModel p 𝔠' c')) ∈ π ⁻¹ᵁ W := by
      change π _ ∈ W; rw [hx]; exact hηW
    have hm2 : genericPoint (flagModel p 𝔠 c) ∈ π ⁻¹ᵁ W := by
      change π _ ∈ W; rw [h1]; exact hηW
    have hinj : Function.Injective (π ∣_ W) :=
      (ConcreteCategory.bijective_of_isIso ((π ∣_ W).base)).1
    have := @hinj ⟨_, hm1⟩ ⟨_, hm2⟩ (by
      apply Subtype.ext
      rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      rw [hx, h1])
    exact congrArg Subtype.val this
  constructor
  rw [DenseRange, Dense]
  intro x
  have hcl : x ∈ closure ({genericPoint (flagModel p 𝔠 c)} : Set (flagModel p 𝔠 c)) := by
    rw [(genericPoint_spec (flagModel p 𝔠 c)).def]; trivial
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range.mpr ⟨_, hgη⟩)) hcl

/-- **Pull-back of a vertical effective Cartier divisor** along a domination map. -/
def VertCartier.pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (E : VertCartier p 𝔠 c) :
    VertCartier p 𝔠' c' where
  ideal := E.ideal.comap g
  isInvertible := by
    let := isDominant_of_comp_eq g hg
    exact E.isInvertible.comap_of_dominant_integral g
  support_subset := by
    rw [Scheme.IdealSheafData.support_comap]
    intro x hx
    have := E.support_subset hx
    show flagModelπ p 𝔠' c' x ∈ ((centralIdeal p).support : Set (productLine p))
    rw [← hg, Scheme.Hom.comp_apply]
    exact this

/-- `φ` is invariant under pull-back (BJ-MODEL2's `idealVal_gaussModelPoint_comap_map`). -/
theorem VertCartier.fn_pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (E : VertCartier p 𝔠 c) :
    (E.pullback g hg).fn = E.fn := by
  funext v
  simp only [VertCartier.fn, VertCartier.pullback]
  rw [idealVal_gaussModelPoint_comap_map v g hg]

/-- The class of the pulled-back divisor is the pulled-back class: `(J · 𝒪_{𝒳'}) ≅ g^* J` for
invertible `J` along the dominant `g` (SGPT.Foundations.Envelope's Cartier module comparison). -/
theorem VertCartier.picQ_line_pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (E : VertCartier p 𝔠 c) :
    picQ (E.pullback g hg).line = picPullbackQ g (picQ E.line) := by
  let := isDominant_of_comp_eq g hg
  have hiso : IsIso (E.ideal.toModulesComapPullbackMap g) :=
    E.isInvertible.toModulesComapPullbackMap_isIso_of_dominant_integral g
  rw [picPullbackQ_picQ]
  exact (picQ_eq_of_iso _ _ (asIso (E.ideal.toModulesComapPullbackMap g))).symm

/-- **Pull-back of vertical `ℚ`-Cartier divisors** along a domination map. -/
def VDiv.pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') : VDiv p 𝔠 c →ₗ[ℚ] VDiv p 𝔠' c' :=
  Finsupp.lmapDomain ℚ ℚ (VertCartier.pullback g hg)

theorem VDiv.fn_pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (D : VDiv p 𝔠 c) :
    VDiv.fn (VDiv.pullback g hg D) = VDiv.fn D := by
  simp only [VDiv.pullback, VDiv.fn, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain]
  rw [show VertCartier.fn ∘ VertCartier.pullback g hg = VertCartier.fn from
    funext fun E => VertCartier.fn_pullback g hg E]

theorem VDiv.cls_pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (D : VDiv p 𝔠 c) :
    VDiv.cls (VDiv.pullback g hg D) = picPullbackQ g (VDiv.cls D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => simp only [map_add, hD, hD']
  | single E q =>
    simp only [VDiv.pullback, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      VDiv.cls_single, map_smul, map_neg, VertCartier.picQ_line_pullback]

/-- **Domination maps lift uniquely to the normalized models** (the normalized model is normal
and the composite `normModel ⟶ flagModel ⟶ flagModel` is dominant). -/
theorem existsUnique_normModel_lift (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') :
    ∃! g' : normModel p 𝔠' c' ⟶ normModel p 𝔠 c,
      g' ≫ normModelν p 𝔠 c = normModelν p 𝔠' c' ≫ g := by
  have : IsDominant (normModelν p 𝔠' c') := ⟨(normModelν_surjective p 𝔠' c').denseRange⟩
  have := isDominant_of_comp_eq g hg
  exact IntegralSchemeNormalization.existsUnique_dominant_normalization_lift _
    (normModel_stalk_isIntegrallyClosed p 𝔠' c')

/-- Dominating the model of `((t^0), 1)` is preserved by domination maps. -/
theorem Dominates.of_comp {𝔞 : FlagIdeal X} {b : ℤ} (h : Dominates p 𝔠 c 𝔞 b)
    (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') : Dominates p 𝔠' c' 𝔞 b := by
  refine ⟨?_, ?_⟩
  · let := isDominant_of_comp_eq g hg
    have h' := h.1.comap_of_dominant_integral g
    rwa [← Scheme.IdealSheafData.comap_comp, hg] at h'
  · obtain ⟨g₀, hg₀⟩ := h.2
    exact ⟨g ≫ g₀, by rw [Category.assoc, hg₀, hg]⟩

end domination

/-! ### Every PL function is the function of a vertical divisor -/

section representation

variable (p)

/-- A function is **representable on a model** if it is `φ_D` for a vertical `ℚ`-Cartier
divisor `D` on a blow-up model on which the central fibre is Cartier. -/
def IsRepresentable (φ : BerkovichPoint p → ℝ) : Prop :=
  ∃ (𝔠 : FlagIdeal X) (c : ℤ), Dominates p 𝔠 c (FlagIdeal.monomial X 0) 1 ∧
    ∃ D : VDiv p 𝔠 c, VDiv.fn D = φ

omit [IsProjective p] [IsIntegral X] in
/-- Two models with Cartier central fibre are dominated by a third one (their product). -/
theorem exists_common_dominating {𝔠 𝔠' : FlagIdeal X} {c c' : ℤ}
    (hc : IsWeightBound 𝔠 c) (hc' : IsWeightBound 𝔠' c') :
    ∃ (g : flagModel p (𝔠 * 𝔠') (c + c') ⟶ flagModel p 𝔠 c)
      (g' : flagModel p (𝔠 * 𝔠') (c + c') ⟶ flagModel p 𝔠' c'),
      g ≫ flagModelπ p 𝔠 c = flagModelπ p (𝔠 * 𝔠') (c + c') ∧
      g' ≫ flagModelπ p 𝔠' c' = flagModelπ p (𝔠 * 𝔠') (c + c') :=
  ⟨flagModelMulLeft p hc hc', flagModelMulRight p hc hc', flagModelMap_π _ _,
    flagModelMap_π _ _⟩

/-- Models with Cartier central fibre and a weight bound. -/
def IsGoodModel (𝔠 : FlagIdeal X) (c : ℤ) : Prop :=
  IsWeightBound 𝔠 c ∧ Dominates p 𝔠 c (FlagIdeal.monomial X 0) 1

omit [IsProjective p] [IsIntegral X] in
/-- The model of `𝔞 · (t^0)` with bound `b + 1` dominates the model of `(𝔞, b)` and has Cartier
central fibre. -/
theorem isGoodModel_mul_monomial {𝔞 : FlagIdeal X} {b : ℤ} (hb : IsWeightBound 𝔞 b) :
    IsGoodModel p (𝔞 * FlagIdeal.monomial X 0) (b + 1) ∧
      Dominates p (𝔞 * FlagIdeal.monomial X 0) (b + 1) 𝔞 b := by
  have h0 : IsWeightBound (FlagIdeal.monomial X 0) 1 := (isWeightBound_monomial 0).mono (by norm_num)
  exact ⟨⟨hb.mul h0, dominates_of_flagSheaf_eq_mul p
      ((flagSheaf_mul p hb h0).trans (mul_comm _ _))⟩,
    dominates_of_flagSheaf_eq_mul p (flagSheaf_mul p hb h0)⟩

variable {p} in
/-- A function representable on a good model is representable on every good model dominating
it. -/
theorem exists_vdiv_of_dominates {𝔠 𝔠' : FlagIdeal X} {c c' : ℤ}
    (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (D : VDiv p 𝔠 c) :
    ∃ D' : VDiv p 𝔠' c', VDiv.fn D' = VDiv.fn D :=
  ⟨VDiv.pullback g hg D, VDiv.fn_pullback g hg D⟩

/-- The representable functions on good models form a `ℚ`-submodule. -/
def representableSubmodule : Submodule ℚ (BerkovichPoint p → ℝ) where
  carrier := {φ | ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c ∧
    ∃ D : VDiv p 𝔠 c, VDiv.fn D = φ}
  zero_mem' := by
    obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound (FlagIdeal.monomial X 0)
    obtain ⟨hgood, -⟩ := isGoodModel_mul_monomial p hb
    exact ⟨_, _, hgood, 0, map_zero _⟩
  add_mem' := by
    rintro φ ψ ⟨𝔠, c, ⟨hc, h0⟩, D, rfl⟩ ⟨𝔠', c', ⟨hc', h0'⟩, D', rfl⟩
    obtain ⟨g, g', hg, hg'⟩ := exists_common_dominating p hc hc'
    refine ⟨𝔠 * 𝔠', c + c', ⟨hc.mul hc', h0.of_comp g hg⟩,
      VDiv.pullback g hg D + VDiv.pullback g' hg' D', ?_⟩
    rw [map_add, VDiv.fn_pullback, VDiv.fn_pullback]
  smul_mem' := by
    rintro q φ ⟨𝔠, c, hgood, D, rfl⟩
    exact ⟨𝔠, c, hgood, q • D, map_smul _ _ _⟩

/-- **Every PL function is the function of a vertical `ℚ`-Cartier divisor on a model**
([BJ22, `thm:VCarPL`], the inclusion `PL(X) ⊆ {φ_D}`): `φ_𝔞 = φ_{D_𝔞}` on the model of
`𝔞 · (t^0)`, and the representable functions form a `ℚ`-submodule (common models). -/
theorem plSubmodule_le_representableSubmodule : plSubmodule p ≤ representableSubmodule p := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨𝔞, rfl⟩
  obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound 𝔞
  obtain ⟨hgood, hdom⟩ := isGoodModel_mul_monomial p hb
  exact ⟨_, _, hgood, flagDiv hgood.2 hdom, fn_flagDiv hgood.2 hdom hb⟩

end representation

/-! ### `ω`-psh PL functions -/

section psh

/-- The pull-back `π^*ω` of a `ℚ`-class of `X` to the model. -/
def omegaPullback (𝔠 : FlagIdeal X) (c : ℤ) : PicQ X →ₗ[ℚ] PicQ (flagModel p 𝔠 c) :=
  picPullbackQ (flagModelπ p 𝔠 c ≫ productFst p)

omit [IsProjective p] [IsIntegral X] in
theorem omegaPullback_comp {𝔠 𝔠' : FlagIdeal X} {c c' : ℤ}
    (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (ω : PicQ X) :
    picPullbackQ g (omegaPullback 𝔠 c ω) = omegaPullback 𝔠' c' ω := by
  rw [omegaPullback, omegaPullback, ← picPullbackQ_comp, ← Category.assoc, hg]

/-- **`ω`-psh PL functions** ([BJ22, §3.1]): `φ` is `φ_D` for a vertical `ℚ`-Cartier divisor `D`
on a good model on which `π^*ω + D` is nef on the central fibre. -/
def IsOmegaPshPL (ω : PicQ X) (φ : BerkovichPoint p → ℝ) : Prop :=
  ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c ∧ ∃ D : VDiv p 𝔠 c, VDiv.fn D = φ ∧
    omegaPullback 𝔠 c ω + VDiv.cls D ∈ relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c)

/-- `ω`-psh PL functions are PL in the sense of representable. -/
theorem IsOmegaPshPL.mem_representable {ω : PicQ X} {φ : BerkovichPoint p → ℝ}
    (h : IsOmegaPshPL ω φ) : φ ∈ representableSubmodule p := by
  obtain ⟨𝔠, c, hgood, D, hD, -⟩ := h
  exact ⟨𝔠, c, hgood, D, hD⟩

omit [IsIntegral X] in
/-- Relative nefness on the central fibre transfers along domination maps. -/
theorem mem_relNefCone_pullback {𝔠 𝔠' : FlagIdeal X} {c c' : ℤ}
    (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') {θ : PicQ (flagModel p 𝔠 c)}
    (hθ : θ ∈ relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c)) :
    picPullbackQ g θ ∈ relNefCone (flagModelStructure p 𝔠' c') (centralFibre p 𝔠' c') := by
  have hgp : g ≫ flagModelStructure p 𝔠 c = flagModelStructure p 𝔠' c' := by
    rw [flagModelStructure, ← Category.assoc, hg]
  have : IsProjective (g ≫ flagModelStructure p 𝔠 c) := by rw [hgp]; infer_instance
  have h := picPullbackQ_mem_relNefCone (flagModelStructure p 𝔠 c) g hθ
  have hW : g ⁻¹' centralFibre p 𝔠 c = centralFibre p 𝔠' c' := by
    ext x
    simp only [centralFibre, Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, hg]
  rw [hW] at h
  convert h using 2
  exact hgp.symm

/-- **Midpoints of `ω`-psh PL functions are `ω`-psh** (common models; the relatively nef cone is
convex). -/
theorem IsOmegaPshPL.midpoint {ω : PicQ X} {φ ψ : BerkovichPoint p → ℝ} (hφ : IsOmegaPshPL ω φ)
    (hψ : IsOmegaPshPL ω ψ) : IsOmegaPshPL ω ((1 / 2 : ℚ) • (φ + ψ)) := by
  obtain ⟨𝔠, c, ⟨hc, h0⟩, D, rfl, hD⟩ := hφ
  obtain ⟨𝔠', c', ⟨hc', h0'⟩, D', rfl, hD'⟩ := hψ
  obtain ⟨g, g', hg, hg'⟩ := exists_common_dominating p hc hc'
  refine ⟨𝔠 * 𝔠', c + c', ⟨hc.mul hc', h0.of_comp g hg⟩,
    (1 / 2 : ℚ) • (VDiv.pullback g hg D + VDiv.pullback g' hg' D'), ?_, ?_⟩
  · rw [map_smul, map_add, VDiv.fn_pullback, VDiv.fn_pullback]
  · have e1 := mem_relNefCone_pullback g hg hD
    have e2 := mem_relNefCone_pullback g' hg' hD'
    rw [map_add, omegaPullback_comp g hg, ← VDiv.cls_pullback g hg] at e1
    rw [map_add, omegaPullback_comp g' hg', ← VDiv.cls_pullback g' hg'] at e2
    have key : omegaPullback (𝔠 * 𝔠') (c + c') ω +
        VDiv.cls ((1 / 2 : ℚ) • (VDiv.pullback g hg D + VDiv.pullback g' hg' D')) =
        (1 / 2 : ℚ) • ((omegaPullback (𝔠 * 𝔠') (c + c') ω + VDiv.cls (VDiv.pullback g hg D)) +
          (omegaPullback (𝔠 * 𝔠') (c + c') ω + VDiv.cls (VDiv.pullback g' hg' D'))) := by
      rw [map_smul, map_add]
      module
    rw [key]
    exact Submodule.smul_mem _ (⟨1 / 2, by norm_num⟩ : {r : ℚ // 0 ≤ r}) (add_mem e1 e2)

end psh

end SGPT.NAPotential.BJ
