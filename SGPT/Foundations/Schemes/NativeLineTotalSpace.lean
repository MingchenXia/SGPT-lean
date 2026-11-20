import SGPT.Foundations.Schemes.LineBundleSectionRing
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Native total spaces of dual line sheaves

The local objects are the native relative affine lines. Their coordinate changes
are constructed from literal regular functions using the Γ–Spec polynomial
adjunction. The multipliers are derived from the actual sheaf frames.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native affine line over an arbitrary actual scheme. -/
abbrev nativeAffineLine (U : Scheme.{u}) : Scheme.{u} :=
  AffineSpace PUnit.{u + 1} U

/-- Its literal native pullback projection. -/
abbrev nativeAffineLineProjection (U : Scheme.{u}) : nativeAffineLine U ⟶ U :=
  nativeAffineLine U ↘ U

/-- The actual regular coordinate of the relative affine line. -/
def nativeAffineLineCoordinate (U : Scheme.{u}) : Γ(nativeAffineLine U, ⊤) :=
  AffineSpace.coord U PUnit.unit

/-- Scaling is produced by the native universal polynomial morphism. -/
def nativeAffineLineScale (U : Scheme.{u}) (r : Γ(U, ⊤)) :
    nativeAffineLine U ⟶ nativeAffineLine U :=
  AffineSpace.homOfVector (nativeAffineLineProjection U)
    (fun _ ↦ (nativeAffineLineProjection U).appTop r * nativeAffineLineCoordinate U)

@[reassoc (attr := simp)]
theorem nativeAffineLineScale_projection (U : Scheme.{u}) (r : Γ(U, ⊤)) :
    nativeAffineLineScale U r ≫ nativeAffineLineProjection U =
      nativeAffineLineProjection U :=
  AffineSpace.homOfVector_over _ _

@[simp]
theorem nativeAffineLineScale_coordinate (U : Scheme.{u}) (r : Γ(U, ⊤)) :
    (nativeAffineLineScale U r).appTop (nativeAffineLineCoordinate U) =
      (nativeAffineLineProjection U).appTop r * nativeAffineLineCoordinate U :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- Actual maps to the native affine line are determined by their base map and
their pullback of the actual coordinate. -/
theorem nativeAffineLine_hom_ext {T U : Scheme.{u}}
    {f g : T ⟶ nativeAffineLine U}
    (hp : f ≫ nativeAffineLineProjection U = g ≫ nativeAffineLineProjection U)
    (ht : f.appTop (nativeAffineLineCoordinate U) =
      g.appTop (nativeAffineLineCoordinate U)) : f = g := by
  apply AffineSpace.hom_ext hp
  intro i
  cases i
  exact ht

@[simp]
theorem nativeAffineLineScale_one (U : Scheme.{u}) :
    nativeAffineLineScale U 1 = 𝟙 (nativeAffineLine U) := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp

/-- Composition of the literal scheme maps multiplies the actual regular
scalars, on every base scheme without an affineness hypothesis. -/
theorem nativeAffineLineScale_comp (U : Scheme.{u}) (r s : Γ(U, ⊤)) :
    nativeAffineLineScale U r ≫ nativeAffineLineScale U s =
      nativeAffineLineScale U (r * s) := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      nativeAffineLineScale_coordinate, map_mul]
    have hr : (nativeAffineLineScale U r).appTop
        ((nativeAffineLineProjection U).appTop s) =
        (nativeAffineLineProjection U).appTop s := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      simp
    rw [hr]
    ring

/-- A literal global unit gives a genuine native scheme automorphism. -/
def nativeAffineLineScaleIso (U : Scheme.{u}) (r : Γ(U, ⊤)ˣ) :
    nativeAffineLine U ≅ nativeAffineLine U where
  hom := nativeAffineLineScale U r
  inv := nativeAffineLineScale U (↑r⁻¹ : Γ(U, ⊤))
  hom_inv_id := by rw [nativeAffineLineScale_comp]; simp
  inv_hom_id := by rw [nativeAffineLineScale_comp]; simp

/-- The actual affine-line map under change of the base scheme. -/
abbrev nativeAffineLineMap {U V : Scheme.{u}} (f : U ⟶ V) :
    nativeAffineLine U ⟶ nativeAffineLine V :=
  AffineSpace.map PUnit.{u + 1} f

@[reassoc (attr := simp)]
theorem nativeAffineLineMap_projection {U V : Scheme.{u}} (f : U ⟶ V) :
    nativeAffineLineMap f ≫ nativeAffineLineProjection V =
      nativeAffineLineProjection U ≫ f :=
  AffineSpace.map_over _

@[simp]
theorem nativeAffineLineMap_coordinate {U V : Scheme.{u}} (f : U ⟶ V) :
    (nativeAffineLineMap f).appTop (nativeAffineLineCoordinate V) =
      nativeAffineLineCoordinate U :=
  AffineSpace.map_appTop_coord _ _

/-- Scaling by a regular function commutes with literal pullback to any base. -/
theorem nativeAffineLineScale_naturality {U V : Scheme.{u}} (f : U ⟶ V)
    (r : Γ(V, ⊤)) :
    nativeAffineLineScale U (f.appTop r) ≫ nativeAffineLineMap f =
      nativeAffineLineMap f ≫ nativeAffineLineScale V r := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      nativeAffineLineMap_coordinate, nativeAffineLineScale_coordinate, map_mul]
    have hr : (nativeAffineLineMap f).appTop
        ((nativeAffineLineProjection V).appTop r) =
        (nativeAffineLineProjection U).appTop (f.appTop r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        nativeAffineLineMap_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [hr]

/-- The relative affine-line square is a genuine native pullback square. -/
theorem nativeAffineLineMap_isPullback {U V : Scheme.{u}} (f : U ⟶ V) :
    IsPullback (nativeAffineLineMap f) (nativeAffineLineProjection U)
      (nativeAffineLineProjection V) f :=
  AffineSpace.isPullback_map f

/-- Native affine-line maps along open subschemes are actual open immersions. -/
instance nativeAffineLineMap_isOpenImmersion {U V : Scheme.{u}} (f : U ⟶ V)
    [IsOpenImmersion f] : IsOpenImmersion (nativeAffineLineMap f) := by
  exact MorphismProperty.of_isPullback (nativeAffineLineMap_isPullback f).flip
    (inferInstance : IsOpenImmersion f)

/-- Its open image is the literal pullback of the base open image. -/
theorem nativeAffineLineMap_opensRange {U V : Scheme.{u}} (f : U ⟶ V)
    [IsOpenImmersion f] :
    (nativeAffineLineMap f).opensRange =
      nativeAffineLineProjection V ⁻¹ᵁ f.opensRange := by
  let e := (nativeAffineLineMap_isPullback f).isoPullback
  calc
    (nativeAffineLineMap f).opensRange =
        (e.hom ≫ pullback.fst (nativeAffineLineProjection V) f).opensRange := by
      simp only [e, IsPullback.isoPullback_hom_fst]
    _ = (pullback.fst (nativeAffineLineProjection V) f).opensRange :=
      Scheme.Hom.opensRange_comp_of_isIso _ _
    _ = _ := Scheme.Hom.opensRange_pullbackFst _ _

variable {X : Scheme.{u}}

/-- Passing between functions on an open and global functions on its actual
open subscheme commutes with literal restriction. -/
theorem nativeOpenSections_restrict {U V : X.Opens} (h : U ≤ V) (r : Γ(X, V)) :
    (X.homOfLE h).appTop (V.topIso.inv r) =
      U.topIso.inv (X.presheaf.map (homOfLE h).op r) := by
  have hn := X.restrictFunctorΓ.inv.naturality (homOfLE h).op
  exact (congrArg (fun (q : Γ(X, V) ⟶ Γ(U.toScheme, ⊤)) ↦ q r) hn).symm

/-- The literal global unit on the actual overlap, derived from two genuine
sheaf frames rather than supplied as coordinate-change data. -/
def nativeFrameTransitionUnit {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V)
    (i : W ⟶ U) (j : W ⟶ V) : Γ(W.toScheme, ⊤)ˣ :=
  Units.map W.topIso.inv.hom.toMonoidHom (localBundleFrameTransition e f i j)

@[simp]
theorem nativeFrameTransitionUnit_self {L : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame L U) (i : W ⟶ U) :
    nativeFrameTransitionUnit e e i i = 1 := by
  simp [nativeFrameTransitionUnit, localBundleFrameTransition]

/-- The actual global transition units satisfy the actual frame cocycle. -/
theorem nativeFrameTransitionUnit_cocycle {L : X.Modules} {U V Z W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (g : LocalBundleFrame L Z)
    (i : W ⟶ U) (j : W ⟶ V) (k : W ⟶ Z) :
    nativeFrameTransitionUnit e g i k =
      nativeFrameTransitionUnit f g j k * nativeFrameTransitionUnit e f i j := by
  exact (congrArg (Units.map W.topIso.inv.hom.toMonoidHom)
    (localBundleFrameTransition_cocycle e f g i j k)).trans
      ((Units.map W.topIso.inv.hom.toMonoidHom).map_mul _ _)

/-- The derived global overlap units restrict by the actual native base map. -/
theorem nativeFrameTransitionUnit_restrict {L : X.Modules} {U V W Z : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V)
    (i : W ⟶ U) (j : W ⟶ V) (h : Z ≤ W) :
    nativeFrameTransitionUnit e f (homOfLE h ≫ i) (homOfLE h ≫ j) =
      Units.map (X.homOfLE h).appTop.hom.toMonoidHom
        (nativeFrameTransitionUnit e f i j) := by
  apply Units.ext
  simp only [nativeFrameTransitionUnit, Units.coe_map, localBundleFrameTransition_restrict]
  change Z.topIso.inv (X.presheaf.map (homOfLE h).op
      (localBundleFrameTransition e f i j).val) =
    (X.homOfLE h).appTop (W.topIso.inv (localBundleFrameTransition e f i j).val)
  exact (nativeOpenSections_restrict h _).symm

/-- Framed actual smaller opens in a genuine line-sheaf atlas. Morphisms are
literal inclusions of their underlying opens, independently of their frame. -/
abbrev NativeFramedOpen {L : X.Modules} (a : LineBundleAtlas L) :=
  InducedCategory X.Opens
    (fun c : Σ i : a.I, {W : X.Opens // W ≤ a.opens i} ↦ c.2.1)

instance nativeFramedOpen_isThin {L : X.Modules} (a : LineBundleAtlas L) :
    Quiver.IsThin (NativeFramedOpen a) :=
  fun _ _ ↦ ⟨fun f g ↦ InducedCategory.hom_ext (Subsingleton.elim f.hom g.hom)⟩

/-- The inverse transition unit is the genuine dual-line fiber-coordinate
multiplier on a smaller actual open. -/
def nativeFramedMultiplier {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) : Γ(c.2.1.toScheme, ⊤)ˣ :=
  (nativeFrameTransitionUnit (a.frame c.1) (a.frame d.1)
    (homOfLE c.2.2) (homOfLE (h.hom.le.trans d.2.2)))⁻¹

@[simp]
theorem nativeFramedMultiplier_id {L : X.Modules} (a : LineBundleAtlas L)
    (c : NativeFramedOpen a) : nativeFramedMultiplier a (𝟙 c) = 1 := by
  simp [nativeFramedMultiplier]

/-- The literal fiber-coordinate multipliers obey composition after actual
restriction to the source open. -/
theorem nativeFramedMultiplier_comp {L : X.Modules} (a : LineBundleAtlas L)
    {c d e : NativeFramedOpen a} (f : c ⟶ d) (g : d ⟶ e) :
    nativeFramedMultiplier a (f ≫ g) = nativeFramedMultiplier a f *
      Units.map (X.homOfLE f.hom.le).appTop.hom.toMonoidHom
        (nativeFramedMultiplier a g) := by
  have hr := nativeFrameTransitionUnit_restrict (a.frame d.1) (a.frame e.1)
    (homOfLE d.2.2) (homOfLE (g.hom.le.trans e.2.2)) f.hom.le
  have hc := nativeFrameTransitionUnit_cocycle (a.frame c.1) (a.frame d.1)
    (a.frame e.1) (homOfLE c.2.2) (homOfLE (f.hom.le.trans d.2.2))
      (homOfLE ((f.hom.le.trans g.hom.le).trans e.2.2))
  dsimp only [nativeFramedMultiplier]
  rw [map_inv, ← hr]
  rw [hc, mul_inv_rev]
  congr 3

/-- The literal dual-line chart map is inverse scaling followed by the native
affine-line map for the actual open inclusion. -/
def nativeFramedMap {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    nativeAffineLine c.2.1.toScheme ⟶ nativeAffineLine d.2.1.toScheme :=
  nativeAffineLineScale c.2.1.toScheme (↑(nativeFramedMultiplier a h)) ≫
    nativeAffineLineMap (X.homOfLE h.hom.le)

@[reassoc (attr := simp)]
theorem nativeFramedMap_projection {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    nativeFramedMap a h ≫ nativeAffineLineProjection d.2.1.toScheme =
      nativeAffineLineProjection c.2.1.toScheme ≫ X.homOfLE h.hom.le := by
  simp [nativeFramedMap]

@[simp]
theorem nativeFramedMap_coordinate {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    (nativeFramedMap a h).appTop (nativeAffineLineCoordinate d.2.1.toScheme) =
      (nativeAffineLineProjection c.2.1.toScheme).appTop (↑(nativeFramedMultiplier a h)) *
        nativeAffineLineCoordinate c.2.1.toScheme := by
  simp [nativeFramedMap]

@[simp]
theorem nativeFramedMap_id {L : X.Modules} (a : LineBundleAtlas L)
    (c : NativeFramedOpen a) : nativeFramedMap a (𝟙 c) = 𝟙 _ := by
  simp [nativeFramedMap]

/-- The actual scheme maps compose by the derived frame cocycle. -/
theorem nativeFramedMap_comp {L : X.Modules} (a : LineBundleAtlas L)
    {c d e : NativeFramedOpen a} (f : c ⟶ d) (g : d ⟶ e) :
    nativeFramedMap a f ≫ nativeFramedMap a g = nativeFramedMap a (f ≫ g) := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      nativeFramedMap_coordinate, map_mul]
    have hr : (nativeFramedMap a f).appTop
        ((nativeAffineLineProjection d.2.1.toScheme).appTop
          (↑(nativeFramedMultiplier a g))) =
        (nativeAffineLineProjection c.2.1.toScheme).appTop
          ((X.homOfLE f.hom.le).appTop (↑(nativeFramedMultiplier a g))) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        nativeFramedMap_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [hr, nativeFramedMultiplier_comp]
    simp only [Units.val_mul, Units.coe_map, map_mul]
    let A := (nativeAffineLineProjection c.2.1.toScheme).appTop
      (↑(nativeFramedMultiplier a f))
    let B := (nativeAffineLineProjection c.2.1.toScheme).appTop
      ((X.homOfLE f.hom.le).appTop (↑(nativeFramedMultiplier a g)))
    let T := nativeAffineLineCoordinate c.2.1.toScheme
    change B * (A * T) = (A * B) * T
    ring

/-- The actual open-chart diagram whose maps use the genuine dual-frame
transitions. Its objects and maps are native schemes and native morphisms. -/
def nativeDualLineDiagram {L : X.Modules} (a : LineBundleAtlas L) :
    NativeFramedOpen a ⥤ Scheme.{u} where
  obj c := nativeAffineLine c.2.1.toScheme
  map h := nativeFramedMap a h
  map_id c := nativeFramedMap_id a c
  map_comp f g := (nativeFramedMap_comp a f g).symm

/-- Each actual transition-and-inclusion chart map is an open immersion. -/
instance nativeFramedMap_isOpenImmersion {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) : IsOpenImmersion (nativeFramedMap a h) := by
  change IsOpenImmersion
    ((nativeAffineLineScaleIso c.2.1.toScheme (nativeFramedMultiplier a h)).hom ≫
      nativeAffineLineMap (X.homOfLE h.hom.le))
  infer_instance

instance nativeDualLineDiagram_map_isOpenImmersion {L : X.Modules}
    (a : LineBundleAtlas L) {c d : NativeFramedOpen a} (h : c ⟶ d) :
    IsOpenImmersion ((nativeDualLineDiagram a).map h) :=
  nativeFramedMap_isOpenImmersion a h

/-- The image of a framed chart inclusion is exactly the inverse image of its
actual smaller base open. -/
theorem nativeFramedMap_opensRange {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    (nativeFramedMap a h).opensRange =
      nativeAffineLineProjection d.2.1.toScheme ⁻¹ᵁ d.2.1.ι ⁻¹ᵁ c.2.1 := by
  calc
    (nativeFramedMap a h).opensRange =
        (nativeAffineLineMap (X.homOfLE h.hom.le)).opensRange :=
      Scheme.Hom.opensRange_comp_of_isIso
        (nativeAffineLineScaleIso c.2.1.toScheme (nativeFramedMultiplier a h)).hom _
    _ = _ := by rw [nativeAffineLineMap_opensRange, Scheme.opensRange_homOfLE]

/-- A point lifts through a framed chart inclusion precisely when its actual
base point lies in the smaller open. -/
theorem nativeFramedMap_mem_range {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) (x : nativeAffineLine d.2.1.toScheme) :
    x ∈ Set.range (nativeFramedMap a h) ↔
      (nativeAffineLineProjection d.2.1.toScheme x).1 ∈ c.2.1 := by
  change x ∈ (nativeFramedMap a h).opensRange ↔ _
  rw [nativeFramedMap_opensRange]
  rfl

@[reassoc (attr := simp)]
theorem nativeFramedMap_base {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    nativeFramedMap a h ≫ nativeAffineLineProjection d.2.1.toScheme ≫ d.2.1.ι =
      nativeAffineLineProjection c.2.1.toScheme ≫ c.2.1.ι := by
  rw [nativeFramedMap_projection_assoc, Scheme.homOfLE_ι]

/-- Actual intersections of the base opens supply all common point lifts.
Thus the genuine inverse-transition scheme diagram is locally directed. -/
instance nativeDualLineDiagram_isLocallyDirected {L : X.Modules}
    (a : LineBundleAtlas L) : (nativeDualLineDiagram a ⋙ Scheme.forget).IsLocallyDirected where
  cond := by
    intro i j k fi fj xi xj heq
    change nativeAffineLine i.2.1.toScheme at xi
    change nativeAffineLine j.2.1.toScheme at xj
    change nativeFramedMap a fi xi = nativeFramedMap a fj xj at heq
    have hb : (nativeAffineLineProjection i.2.1.toScheme xi).1 =
        (nativeAffineLineProjection j.2.1.toScheme xj).1 := by
      have hh := congrArg
        (fun y ↦ k.2.1.ι (nativeAffineLineProjection k.2.1.toScheme y)) heq
      change (nativeFramedMap a fi ≫ nativeAffineLineProjection k.2.1.toScheme ≫ k.2.1.ι) xi =
        (nativeFramedMap a fj ≫ nativeAffineLineProjection k.2.1.toScheme ≫ k.2.1.ι) xj at hh
      rw [nativeFramedMap_base, nativeFramedMap_base] at hh
      exact hh
    let l : NativeFramedOpen a :=
      ⟨i.1, ⟨i.2.1 ⊓ j.2.1, inf_le_left.trans i.2.2⟩⟩
    let fli : l ⟶ i := InducedCategory.homMk (homOfLE inf_le_left)
    let flj : l ⟶ j := InducedCategory.homMk (homOfLE inf_le_right)
    have hxj : (nativeAffineLineProjection i.2.1.toScheme xi).1 ∈ j.2.1 := by
      rw [hb]
      exact (nativeAffineLineProjection j.2.1.toScheme xj).2
    have hx : xi ∈ Set.range (nativeFramedMap a fli) :=
      (nativeFramedMap_mem_range a fli xi).mpr
        ⟨(nativeAffineLineProjection i.2.1.toScheme xi).2, hxj⟩
    obtain ⟨x, hx⟩ := hx
    refine ⟨l, fli, flj, x, hx, ?_⟩
    change nativeFramedMap a flj x = xj
    apply (nativeFramedMap a fj).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, nativeFramedMap_comp,
      Subsingleton.elim (flj ≫ fj) (fli ≫ fi), ← nativeFramedMap_comp,
      Scheme.Hom.comp_apply, hx, heq]

/-- The literal native scheme obtained by gluing the actual dual-line charts. -/
def nativeDualLineTotalSpace {L : X.Modules} (a : LineBundleAtlas L) : Scheme.{u} :=
  colimit (nativeDualLineDiagram a)

/-- The actual compatible chart projections to the original scheme. -/
def nativeDualLineProjectionCocone {L : X.Modules} (a : LineBundleAtlas L) :
    Cocone (nativeDualLineDiagram a) where
  pt := X
  ι :=
    { app := fun c ↦ nativeAffineLineProjection c.2.1.toScheme ≫ c.2.1.ι
      naturality := fun c d h ↦ by
        change nativeFramedMap a h ≫ nativeAffineLineProjection d.2.1.toScheme ≫ d.2.1.ι =
          (nativeAffineLineProjection c.2.1.toScheme ≫ c.2.1.ι) ≫ 𝟙 X
        rw [Category.comp_id]
        exact nativeFramedMap_base a h }

/-- The literal scheme morphism descending the actual chart projections. -/
def nativeDualLineProjection {L : X.Modules} (a : LineBundleAtlas L) :
    nativeDualLineTotalSpace a ⟶ X :=
  colimit.desc (nativeDualLineDiagram a) (nativeDualLineProjectionCocone a)

@[reassoc (attr := simp)]
theorem nativeDualLineProjection_on_open {L : X.Modules} (a : LineBundleAtlas L)
    (c : NativeFramedOpen a) :
    colimit.ι (nativeDualLineDiagram a) c ≫ nativeDualLineProjection a =
      nativeAffineLineProjection c.2.1.toScheme ≫ c.2.1.ι :=
  colimit.ι_desc _ _

/-- The actual affine-line chart for an original atlas open. -/
def nativeDualLineChart {L : X.Modules} (a : LineBundleAtlas L) (i : a.I) :
    nativeAffineLine (a.opens i).toScheme ⟶ nativeDualLineTotalSpace a :=
  colimit.ι (nativeDualLineDiagram a) ⟨i, ⟨a.opens i, le_rfl⟩⟩

instance nativeDualLineChart_isOpenImmersion {L : X.Modules}
    (a : LineBundleAtlas L) (i : a.I) : IsOpenImmersion (nativeDualLineChart a i) :=
  inferInstanceAs (IsOpenImmersion
    (colimit.ι (nativeDualLineDiagram a) ⟨i, ⟨a.opens i, le_rfl⟩⟩))

@[reassoc (attr := simp)]
theorem nativeDualLineChart_projection {L : X.Modules} (a : LineBundleAtlas L) (i : a.I) :
    nativeDualLineChart a i ≫ nativeDualLineProjection a =
      nativeAffineLineProjection (a.opens i).toScheme ≫ (a.opens i).ι :=
  nativeDualLineProjection_on_open a _

/-- The original atlas charts jointly cover the actual glued total space. -/
theorem nativeDualLineChart_jointly_surjective {L : X.Modules}
    (a : LineBundleAtlas L) (x : nativeDualLineTotalSpace a) :
    ∃ (i : a.I) (y : nativeAffineLine (a.opens i).toScheme), nativeDualLineChart a i y = x := by
  obtain ⟨c, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (nativeDualLineDiagram a) x
  change nativeAffineLine c.2.1.toScheme at y
  let d : NativeFramedOpen a := ⟨c.1, ⟨a.opens c.1, le_rfl⟩⟩
  let h : c ⟶ d := InducedCategory.homMk (homOfLE c.2.2)
  refine ⟨c.1, nativeFramedMap a h y, ?_⟩
  change colimit.ι (nativeDualLineDiagram a) d (nativeFramedMap a h y) = x
  change (nativeFramedMap a h ≫ colimit.ι (nativeDualLineDiagram a) d) y = x
  exact (congrArg (fun q ↦ q y) (colimit.w (nativeDualLineDiagram a) h)).trans hy

/-- On an affine base the same native affine line is the literal spectrum of
the one-variable polynomial algebra. -/
def nativeAffineLineSpecIso (R : CommRingCat.{u}) :
    nativeAffineLine (Spec R) ≅ Spec (.of (MvPolynomial PUnit.{u + 1} R)) :=
  AffineSpace.SpecIso PUnit.{u + 1} R

/-- Over a complex scheme the native affine line is the actual pullback with
the native complex affine line, not a replacement total-space object. -/
def nativeAffineLineComplexPullbackIso {U : Scheme} (f : U ⟶ Spec (.of ℂ)) :
    nativeAffineLine U ≅
      pullback f (nativeAffineLineProjection (Spec (.of ℂ))) :=
  (nativeAffineLineMap_isPullback f).isoPullback ≪≫ pullbackSymmetry _ _

/-- The literal zero section on an arbitrary actual affine-line base. -/
def nativeAffineLineZero (U : Scheme.{u}) : U ⟶ nativeAffineLine U :=
  AffineSpace.homOfVector (𝟙 U) (fun _ ↦ 0)

@[reassoc (attr := simp)]
theorem nativeAffineLineZero_projection (U : Scheme.{u}) :
    nativeAffineLineZero U ≫ nativeAffineLineProjection U = 𝟙 U :=
  AffineSpace.homOfVector_over _ _

@[simp]
theorem nativeAffineLineZero_coordinate (U : Scheme.{u}) :
    (nativeAffineLineZero U).appTop (nativeAffineLineCoordinate U) = 0 :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- Literal scaling fixes the actual zero section. -/
@[reassoc (attr := simp)]
theorem nativeAffineLineZero_scale (U : Scheme.{u}) (r : Γ(U, ⊤)) :
    nativeAffineLineZero U ≫ nativeAffineLineScale U r = nativeAffineLineZero U := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp

/-- Actual zero sections commute with native change of the base scheme. -/
@[reassoc (attr := simp)]
theorem nativeAffineLineZero_naturality {U V : Scheme.{u}} (f : U ⟶ V) :
    nativeAffineLineZero U ≫ nativeAffineLineMap f = f ≫ nativeAffineLineZero V := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp

/-- The derived inverse-transition maps preserve the actual zero sections. -/
@[reassoc]
theorem nativeFramedZero_naturality {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    nativeAffineLineZero c.2.1.toScheme ≫ nativeFramedMap a h =
      X.homOfLE h.hom.le ≫ nativeAffineLineZero d.2.1.toScheme := by
  simp [nativeFramedMap, ← Category.assoc]

/-- Zero chart maps agree after every actual smaller-open inclusion. -/
theorem nativeDualLineZero_restrict {L : X.Modules} (a : LineBundleAtlas L)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    X.homOfLE h.hom.le ≫ nativeAffineLineZero d.2.1.toScheme ≫
        colimit.ι (nativeDualLineDiagram a) d =
      nativeAffineLineZero c.2.1.toScheme ≫ colimit.ι (nativeDualLineDiagram a) c := by
  rw [← nativeFramedZero_naturality_assoc]
  change nativeAffineLineZero c.2.1.toScheme ≫ (nativeDualLineDiagram a).map h ≫
    colimit.ι (nativeDualLineDiagram a) d = _
  rw [colimit.w]

/-- The genuine base open cover of the supplied sheaf atlas. -/
def nativeLineAtlasBaseCover {L : X.Modules} (a : LineBundleAtlas L) : X.OpenCover where
  I₀ := a.I
  X i := (a.opens i).toScheme
  f i := (a.opens i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := a.covers x
    exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- Literal zero-chart maps agree on genuine native pullback overlaps. -/
theorem nativeDualLineZero_compatible {L : X.Modules} (a : LineBundleAtlas L) (i j : a.I) :
    pullback.fst (a.opens i).ι (a.opens j).ι ≫
        nativeAffineLineZero (a.opens i).toScheme ≫ nativeDualLineChart a i =
      pullback.snd (a.opens i).ι (a.opens j).ι ≫
        nativeAffineLineZero (a.opens j).toScheme ≫ nativeDualLineChart a j := by
  let c : NativeFramedOpen a := ⟨i, ⟨a.opens i ⊓ a.opens j, inf_le_left⟩⟩
  let di : NativeFramedOpen a := ⟨i, ⟨a.opens i, le_rfl⟩⟩
  let dj : NativeFramedOpen a := ⟨j, ⟨a.opens j, le_rfl⟩⟩
  let hi : c ⟶ di := InducedCategory.homMk (homOfLE inf_le_left)
  let hj : c ⟶ dj := InducedCategory.homMk (homOfLE inf_le_right)
  let pb := isPullback_opens_inf (a.opens i) (a.opens j)
  rw [← cancel_epi pb.isoPullback.hom]
  simp only [IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  exact (nativeDualLineZero_restrict a hi).trans (nativeDualLineZero_restrict a hj).symm

/-- The global native zero section, glued on the actual base open cover. -/
def nativeDualLineZero {L : X.Modules} (a : LineBundleAtlas L) :
    X ⟶ nativeDualLineTotalSpace a :=
  (nativeLineAtlasBaseCover a).glueMorphisms
    (fun i ↦ nativeAffineLineZero (a.opens i).toScheme ≫ nativeDualLineChart a i)
    (nativeDualLineZero_compatible a)

@[reassoc (attr := simp)]
theorem nativeDualLineZero_on_chart {L : X.Modules} (a : LineBundleAtlas L) (i : a.I) :
    (a.opens i).ι ≫ nativeDualLineZero a =
      nativeAffineLineZero (a.opens i).toScheme ≫ nativeDualLineChart a i :=
  (nativeLineAtlasBaseCover a).ι_glueMorphisms _ _ i

/-- The actual glued zero section is a section of the actual projection. -/
@[reassoc (attr := simp)]
theorem nativeDualLineZero_projection {L : X.Modules} (a : LineBundleAtlas L) :
    nativeDualLineZero a ≫ nativeDualLineProjection a = 𝟙 X := by
  apply (nativeLineAtlasBaseCover a).hom_ext
  intro i
  change (a.opens i).ι ≫ nativeDualLineZero a ≫ nativeDualLineProjection a =
    (a.opens i).ι ≫ 𝟙 X
  simp

/-- The literal regular coefficient of an actual tensor-power section on a
framed open subscheme, transported only by the native top-open isomorphism. -/
def nativeFramedSectionCoefficient {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n) (c : NativeFramedOpen a) :
    Γ(c.2.1.toScheme, ⊤) :=
  c.2.1.topIso.inv
    (X.presheaf.map (homOfLE c.2.2).op (atlasPowerGlobalCoefficients a n c.1 s))

/-- The actual section coefficients transform by the inverse of the dual-line
fiber multiplier to the tensor-power degree. -/
theorem nativeFramedSectionCoefficient_transition {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    (X.homOfLE h.hom.le).appTop (nativeFramedSectionCoefficient a n s d) =
      (↑((nativeFramedMultiplier a h)⁻¹) : Γ(c.2.1.toScheme, ⊤)) ^ n *
        nativeFramedSectionCoefficient a n s c := by
  unfold nativeFramedSectionCoefficient
  rw [nativeOpenSections_restrict]
  have hmap : X.presheaf.map (homOfLE h.hom.le).op
      (X.presheaf.map (homOfLE d.2.2).op (atlasPowerGlobalCoefficients a n d.1 s)) =
      X.presheaf.map (homOfLE (h.hom.le.trans d.2.2)).op
        (atlasPowerGlobalCoefficients a n d.1 s) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    congr 2
  rw [hmap]
  have ht := LocalBundleFrame.global_coefficients_transition (a.frame c.1) (a.frame d.1)
    (homOfLE c.2.2) (homOfLE (h.hom.le.trans d.2.2)) n s
  change c.2.1.topIso.inv
      (X.sheaf.obj.map (homOfLE (h.hom.le.trans d.2.2)).op
        (atlasPowerGlobalCoefficients a n d.1 s)) = _
  simp only [atlasPowerGlobalCoefficients]
  rw [ht]
  simp only [nativeFramedMultiplier, inv_inv, nativeFrameTransitionUnit,
    Units.coe_map, map_mul, map_pow]
  rfl

/-- A homogeneous actual section evaluates as its actual regular coefficient
times the corresponding power of the actual affine-line coordinate. -/
def nativeFramedHomogeneousFunction {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n) (c : NativeFramedOpen a) :
    Γ(nativeAffineLine c.2.1.toScheme, ⊤) :=
  (nativeAffineLineProjection c.2.1.toScheme).appTop
    (nativeFramedSectionCoefficient a n s c) * nativeAffineLineCoordinate c.2.1.toScheme ^ n

/-- Evaluation of actual tensor-power sections is invariant under the
genuine inverse coordinate changes of the dual-line total space. -/
theorem nativeFramedHomogeneousFunction_compatible {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    (nativeFramedMap a h).appTop (nativeFramedHomogeneousFunction a n s d) =
      nativeFramedHomogeneousFunction a n s c := by
  unfold nativeFramedHomogeneousFunction
  simp only [map_mul, map_pow, nativeFramedMap_coordinate]
  have hp : (nativeFramedMap a h).appTop
      ((nativeAffineLineProjection d.2.1.toScheme).appTop
        (nativeFramedSectionCoefficient a n s d)) =
      (nativeAffineLineProjection c.2.1.toScheme).appTop
        ((X.homOfLE h.hom.le).appTop (nativeFramedSectionCoefficient a n s d)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      nativeFramedMap_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [hp, nativeFramedSectionCoefficient_transition, map_mul, map_pow]
  let p := (nativeAffineLineProjection c.2.1.toScheme).appTop
  let u := nativeFramedMultiplier a h
  let r := nativeFramedSectionCoefficient a n s c
  let t := nativeAffineLineCoordinate c.2.1.toScheme
  change p (↑u⁻¹ : Γ(c.2.1.toScheme, ⊤)) ^ n * p r * (p (↑u) * t) ^ n = p r * t ^ n
  calc
    _ = (p (↑u⁻¹ : Γ(c.2.1.toScheme, ⊤)) * p (↑u)) ^ n * (p r * t ^ n) := by
      rw [mul_pow, mul_pow]
      ring
    _ = _ := by rw [← map_mul]; simp

end

end SGPT.Foundations.Schemes
