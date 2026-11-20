import SGPT.NAPotential.BerkovichIdealValue
import SGPT.NAPotential.GAGAMult2Faithful
import SGPT.Support.Principalization.Scheme.BlowUp.InverseImage

/-!
# Semi-valuations from field-valued points, and values of inverse-image ideals
(lane BJ-MODEL2, step R1(e))

Source: `chapter_NApotential.tex` (`def:NApotential:L878` and the paragraph before it, `eq:va`),
and [BJ22] (`references/bj22-trivval`), §1.1–1.3: a point of `X^An` is a pair `(y, v)` of a
point of `X` and a valuation of `κ(y)` trivial on `ℂ`; for a morphism `h : Y ⟶ Z` the image of a
semi-valuation is its restriction along `κ(h(y)) → κ(y)`, its centre is the image of the centre,
and `v(𝔞 · 𝒪_Y) = (h_* v)(𝔞)` for ideal sheaves `𝔞` on `Z`. Blueprint: `claude-bj-model2.tex`.

* `fieldEmb g : κ(g(pt)) → L` for a field-valued point `g : Spec L ⟶ Y` (Mathlib's
  `Scheme.SpecToEquivOfField`), and `fieldBerkovichPoint g W ∈ Y^An` for a valuation `W` of
  `L` trivial on `ℂ` (when `g` is a `ℂ`-morphism): support `g(pt)`, valuation `W ∘ fieldEmb g`;
* `fieldEmb_comp_specializationMap`: compatibility of these embeddings with specialization maps
  and stalk maps of a morphism `h : Y ⟶ Z`;
* `stalkIdeal_comap`: `(𝔞 · 𝒪_Y)_c = 𝔞_{h(c)} · 𝒪_{Y,c}`;
* `isCenter_of_compat`, `idealVal_comap_of_compat`: if `u ∈ Z^An` restricts the valuation of
  `w ∈ Y^An` along the stalk maps of `h` at the centre `c(w)`, then `h(c(w))` is the centre of
  `u` and `w(𝔞 · 𝒪_Y) = u(𝔞)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology IsLocalRing
open SGPT.NAPotential.Berkovich
open SGPT.NAPotential.Berkovich.BerkovichPoint (specializationMap)
open scoped ENNReal

/-! ### Stalks of inverse-image ideal sheaves -/

/-- `(𝔞 · 𝒪_Y)_c = 𝔞_{h(c)} · 𝒪_{Y,c}`. -/
theorem stalkIdeal_comap {Y Z : Scheme.{0}} (h : Y ⟶ Z) (J : Z.IdealSheafData) (c : Y) :
    stalkIdeal (J.comap h) c = Ideal.map (h.stalkMap c).hom (stalkIdeal J (h c)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show h c ∈ (⊤ : Z.Opens) from trivial) (⊤ : Z.Opens).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hcV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show c ∈ (h ⁻¹ᵁ U : Y.Opens) from hcU) (h ⁻¹ᵁ U).isOpen
  rw [stalkIdeal_eq_map (J.comap h) ⟨V, hV⟩ hcV, stalkIdeal_eq_map J ⟨U, hU⟩ hcU,
    Scheme.IdealSheafData.ideal_comap_of_le J h ⟨U, hU⟩ ⟨V, hV⟩ hVU, Ideal.map_map,
    Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap]
  congr 1
  rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-! ### Field-valued points -/

section fieldPoint

variable {Y : Scheme.{0}} {L : Type} [Field L]

/-- The point of `Y` of a field-valued point `g : Spec L ⟶ Y`. -/
abbrev fieldPt (g : Spec (.of L) ⟶ Y) : Y := g (closedPoint L)

/-- **The residue field embedding `κ(g(pt)) → L`** of a field-valued point (Mathlib's
`Scheme.SpecToEquivOfField`). -/
abbrev fieldEmb (g : Spec (.of L) ⟶ Y) : Y.residueField (fieldPt g) ⟶ .of L :=
  Y.descResidueField (Scheme.stalkClosedPointTo g)

theorem spec_fieldEmb (g : Spec (.of L) ⟶ Y) :
    Spec.map (fieldEmb g) ≫ Y.fromSpecResidueField (fieldPt g) = g :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L Y g

theorem fieldEmb_comp {Z : Scheme.{0}} (g : Spec (.of L) ⟶ Y) (h : Y ⟶ Z) :
    fieldEmb (g ≫ h) = h.residueFieldMap (fieldPt g) ≫ fieldEmb g :=
  Scheme.descResidueField_stalkClosedPointTo_comp h g

/-- **Compatibility of field-valued points with specialization and stalk maps**: for
`g : Spec L ⟶ Y`, `h : Y ⟶ Z` and a specialization `g(pt) ⤳ c`, the map
`𝒪_{Z,h(c)} → κ(h(g(pt))) → L` equals `𝒪_{Z,h(c)} → 𝒪_{Y,c} → κ(g(pt)) → L`. -/
theorem fieldEmb_comp_specializationMap {Z : Scheme.{0}} (g : Spec (.of L) ⟶ Y) (h : Y ⟶ Z)
    {c : Y} (hs : fieldPt g ⤳ c) (s : Z.presheaf.stalk (h c)) :
    (fieldEmb (g ≫ h)).hom ((specializationMap (hs.map h.continuous)).hom s) =
      (fieldEmb g).hom ((specializationMap hs).hom ((h.stalkMap c).hom s)) := by
  rw [fieldEmb_comp]
  change (fieldEmb g).hom ((h.residueFieldMap (fieldPt g)).hom
    ((specializationMap (hs.map h.continuous)).hom s)) = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  unfold specializationMap
  rw [Category.assoc, Scheme.residue_residueFieldMap, ← Category.assoc,
    Scheme.Hom.stalkSpecializes_stalkMap, Category.assoc]

variable [Algebra ℂ L] (fY : Y ⟶ Spec (.of ℂ))

/-- For a `ℂ`-morphism `g : Spec L ⟶ Y`, the residue embedding is a `ℂ`-algebra map. -/
theorem residueComplexHom_fieldEmb (g : Spec (.of L) ⟶ Y)
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) :
    residueComplexHom fY (fieldPt g) ≫ fieldEmb g = CommRingCat.ofHom (algebraMap ℂ L) := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_map_residueComplexHom, ← Category.assoc, spec_fieldEmb, hg]

/-- **The semi-valuation of a field-valued point**: for a `ℂ`-morphism `g : Spec L ⟶ Y` and a
valuation `W` of `L` trivial on `ℂ`, the point of `Y^An` with support `g(pt)` and valuation
`W ∘ (κ(g(pt)) → L)`. -/
def fieldBerkovichPoint (g : Spec (.of L) ⟶ Y)
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (W : SourceRealValuation L) : BerkovichPoint fY where
  support := fieldPt g
  val :=
    letI := residueComplexAlgebra fY (fieldPt g)
    { toFun := fun a => W ((fieldEmb g).hom a)
      eq_top_iff' := fun a => by
        rw [W.eq_top_iff']
        exact map_eq_zero_iff _ (fieldEmb g).hom.injective
      map_mul' := fun a b => by rw [map_mul, W.map_mul']
      min_le_map_add' := fun a b => by rw [map_add]; exact W.min_le_map_add' _ _
      map_complex' := fun c hc => by
        have h := congrArg (fun φ : CommRingCat.of ℂ ⟶ CommRingCat.of L => φ.hom c)
          (residueComplexHom_fieldEmb fY g hg)
        change W ((fieldEmb g).hom ((residueComplexHom fY (fieldPt g)).hom c)) = 0
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        rw [h]
        exact W.map_complex' c hc }

theorem fieldBerkovichPoint_support (g : Spec (.of L) ⟶ Y)
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (W : SourceRealValuation L) : (fieldBerkovichPoint fY g hg W).support = fieldPt g := rfl

theorem fieldBerkovichPoint_valAt (g : Spec (.of L) ⟶ Y)
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (W : SourceRealValuation L) (a : Y.residueField (fieldPt g)) :
    (fieldBerkovichPoint fY g hg W).valAt a = W ((fieldEmb g).hom a) := rfl

end fieldPoint

/-! ### Centres and values of inverse-image ideals -/

section comap

variable {Y Z : Scheme.{0}} {fY : Y ⟶ Spec (.of ℂ)} {fZ : Z ⟶ Spec (.of ℂ)}

/-- If `u` restricts the valuation of `w` along the stalk maps of `h` at a centre `c` of `w`, then
`h(c)` is a centre of `u`. -/
theorem isCenter_of_compat (h : Y ⟶ Z) (w : BerkovichPoint fY) (u : BerkovichPoint fZ) {c : Y}
    (hc : w.IsCenter c) (hu : u.support ⤳ h c)
    (hval : ∀ s : Z.presheaf.stalk (h c), u.valAt ((specializationMap hu).hom s) =
      w.valAt ((specializationMap hc.choose).hom ((h.stalkMap c).hom s))) :
    u.IsCenter (h c) := by
  refine ⟨hu, fun s => ?_, fun s hs => ?_⟩
  · rw [hval]
    exact hc.choose_spec.1 _
  · rw [hval]
    apply hc.choose_spec.2
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    exact fun hu' => hs (isUnit_of_map_unit (h.stalkMap c).hom s hu')

/-- The value of an ideal sheaf computed at any centre. -/
theorem idealVal_eq_of_isCenter [IsProper fZ] (u : BerkovichPoint fZ) {c : Z}
    (hc : u.IsCenter c) (J : Z.IdealSheafData) :
    u.idealVal J = ⨅ g ∈ stalkIdeal J c, toENNReal (u.valAt ((specializationMap hc.choose).hom g)) := by
  obtain rfl := (u.isCenter_iff_eq_center c).mp hc
  rfl

/-- **Values of inverse-image ideals** ([BJ22, §1.1]): if `u ∈ Z^An` restricts the valuation of
`w ∈ Y^An` along the stalk maps of `h : Y ⟶ Z` at the centre `c(w)`, then
`w(𝔞 · 𝒪_Y) = u(𝔞)` for every ideal sheaf `𝔞` on `Z`. -/
theorem idealVal_comap_of_compat [IsProper fY] [IsProper fZ] (h : Y ⟶ Z) (w : BerkovichPoint fY)
    (u : BerkovichPoint fZ) (hu : u.support ⤳ h w.center)
    (hval : ∀ s : Z.presheaf.stalk (h w.center), u.valAt ((specializationMap hu).hom s) =
      w.valAt ((specializationMap w.support_specializes_center).hom ((h.stalkMap w.center).hom s)))
    (J : Z.IdealSheafData) : w.idealVal (J.comap h) = u.idealVal J := by
  have hcen : u.IsCenter (h w.center) := isCenter_of_compat h w u w.isCenter_center hu hval
  rw [idealVal_eq_of_isCenter u hcen, BerkovichPoint.idealVal, stalkIdeal_comap, Ideal.map,
    BerkovichPoint.iInf_span_eq]
  apply le_antisymm
  · refine le_iInf₂ fun s hs => ?_
    refine (iInf₂_le ((h.stalkMap w.center).hom s) ⟨s, hs, rfl⟩).trans (le_of_eq ?_)
    unfold BerkovichPoint.centerValENN BerkovichPoint.centerVal
    rw [hval]
  · refine le_iInf₂ fun t ht => ?_
    obtain ⟨s, hs, rfl⟩ := ht
    refine (iInf₂_le s hs).trans (le_of_eq ?_)
    unfold BerkovichPoint.centerValENN BerkovichPoint.centerVal
    rw [hval]

/-- Under the compatibility of `idealVal_comap_of_compat`, the centre of `u` is the image of the
centre of `w`. -/
theorem center_eq_of_compat [IsProper fY] [IsProper fZ] (h : Y ⟶ Z) (w : BerkovichPoint fY)
    (u : BerkovichPoint fZ) (hu : u.support ⤳ h w.center)
    (hval : ∀ s : Z.presheaf.stalk (h w.center), u.valAt ((specializationMap hu).hom s) =
      w.valAt ((specializationMap w.support_specializes_center).hom ((h.stalkMap w.center).hom s))) :
    u.center = h w.center :=
  ((u.isCenter_iff_eq_center _).mp (isCenter_of_compat h w u w.isCenter_center hu hval)).symm

end comap

/-! ### Images of semi-valuations of field-valued points -/

section fieldComap

variable {Y Z : Scheme.{0}} {fY : Y ⟶ Spec (.of ℂ)} {fZ : Z ⟶ Spec (.of ℂ)}
variable {L : Type} [Field L] [Algebra ℂ L]

theorem comp_structure_eq {g : Spec (.of L) ⟶ Y}
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) (h : Y ⟶ Z) (hh : h ≫ fZ = fY) :
    (g ≫ h) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  rw [Category.assoc, hh, hg]

/-- **The semi-valuation of `g ≫ h` is the image of the semi-valuation of `g`**, in the sense of
values of ideal sheaves: `w(𝔞 · 𝒪_Y) = (h_* w)(𝔞)`. -/
theorem idealVal_comap_fieldBerkovichPoint [IsProper fY] [IsProper fZ] (h : Y ⟶ Z)
    (hh : h ≫ fZ = fY) (g : Spec (.of L) ⟶ Y)
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) (W : SourceRealValuation L)
    (J : Z.IdealSheafData) :
    (fieldBerkovichPoint fY g hg W).idealVal (J.comap h) =
      (fieldBerkovichPoint fZ (g ≫ h) (comp_structure_eq hg h hh) W).idealVal J := by
  let w := fieldBerkovichPoint fY g hg W
  have hs : fieldPt g ⤳ w.center := w.support_specializes_center
  apply idealVal_comap_of_compat h w _ (hs.map h.continuous)
  intro s
  exact congrArg W.toFun (fieldEmb_comp_specializationMap g h hs s)

/-- Field-valued points of the same morphism give the same semi-valuation. -/
theorem fieldBerkovichPoint_congr {g g' : Spec (.of L) ⟶ Y} (e : g = g')
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hg' : g' ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) (W : SourceRealValuation L) :
    fieldBerkovichPoint fY g hg W = fieldBerkovichPoint fY g' hg' W := by
  subst e
  rfl

/-- Two semi-valuations with the same values on the stalk at the centre of the first have the same
values on ideal sheaves. -/
theorem idealVal_eq_of_valAt_eq [IsProper fY] (w v : BerkovichPoint fY)
    (hv : v.support ⤳ w.center)
    (hval : ∀ s : Y.presheaf.stalk w.center, v.valAt ((specializationMap hv).hom s) =
      w.valAt ((specializationMap w.support_specializes_center).hom s))
    (J : Y.IdealSheafData) : w.idealVal J = v.idealVal J := by
  have hc : v.IsCenter w.center := by
    refine ⟨hv, fun s => ?_, fun s hs => ?_⟩
    · rw [hval]
      exact w.centerVal_nonneg s
    · rw [hval]
      exact w.centerVal_pos hs
  rw [idealVal_eq_of_isCenter v hc J, BerkovichPoint.idealVal]
  refine iInf_congr fun s => iInf_congr fun _ => ?_
  unfold BerkovichPoint.centerValENN BerkovichPoint.centerVal
  rw [hval]

/-- The value of an ideal sheaf at a semi-valuation is determined by the support and the valuation:
if `g = Spec ψ ≫ (Spec κ(y) → Y)` and `W ∘ ψ` is the valuation of `v` (support `y`), then the
semi-valuation of `g` and `v` have the same values on ideal sheaves. -/
theorem idealVal_fieldBerkovichPoint_fromSpecResidueField [IsProper fY] (v : BerkovichPoint fY)
    (ψ : Y.residueField v.support ⟶ .of L) (W : SourceRealValuation L)
    (hg : (Spec.map ψ ≫ Y.fromSpecResidueField v.support) ≫ fY =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hW : ∀ a, W (ψ.hom a) = v.valAt a) (J : Y.IdealSheafData) :
    (fieldBerkovichPoint fY (Spec.map ψ ≫ Y.fromSpecResidueField v.support) hg W).idealVal J =
      v.idealVal J := by
  let g := Spec.map ψ ≫ Y.fromSpecResidueField v.support
  let w := fieldBerkovichPoint fY g hg W
  -- the field-valued point `g` corresponds to `(v.support, ψ)`
  have hσ : (Scheme.SpecToEquivOfField L Y) g = ⟨v.support, ψ⟩ :=
    (Scheme.SpecToEquivOfField L Y).apply_symm_apply ⟨v.support, ψ⟩
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hσ
  have key : ∀ (x : Y) (e : x = v.support) (η : Y.residueField x ⟶ .of L)
      (_ : η = (Y.residueFieldCongr e).hom ≫ ψ) {c : Y} (hx : x ⤳ c) (hv : v.support ⤳ c)
      (s : Y.presheaf.stalk c), W (η.hom ((specializationMap hx).hom s)) =
        v.valAt ((specializationMap hv).hom s) := by
    intro x e η hη c hx hv s
    subst e hη
    rw [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp]
    exact hW _
  have e' : fieldPt g = v.support := e
  have hv : v.support ⤳ w.center := e' ▸ w.support_specializes_center
  refine idealVal_eq_of_valAt_eq w v hv (fun s => ?_) J
  exact (key (fieldPt g) e' (fieldEmb g) he w.support_specializes_center hv s).symm

end fieldComap

end SGPT.NAPotential.BJ
