import SGPT.Unibranch.UnibAnSpace
import SGPT.Unibranch.HironakaG10GenGluing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology SGPT.Foundations.Analysis.FirstPass
open SGPT.Unibranch SGPT.Foundations.Schemes

namespace SGPT.Unibranch.UnibAn

noncomputable section

/-- The complex-point map of a scheme morphism is given in embedded charts by
polynomial fractions on a principal open around the chosen source point. -/
theorem exists_local_morphism_coords
    {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X)
    (e : EmbeddedChart (ρ ≫ f)) (e' : EmbeddedChart f) (c : polynomialZeroSet e.ideal)
    (hc : ρ (e.map (Spec.map (CommRingCat.ofHom (pointEval c)) default)) ∈ Set.range e'.map) :
    ∃ (r : MvPolynomial (Fin e.dim) ℂ) (p : Fin e'.dim → MvPolynomial (Fin e.dim) ℂ)
      (m : Fin e'.dim → ℕ), polyEval r (c.val : ComplexModel e.dim) ≠ 0 ∧
      ∀ c' : polynomialZeroSet e.ideal, polyEval r (c'.val : ComplexModel e.dim) ≠ 0 →
        ∃ d' : polynomialZeroSet e'.ideal,
          complexCoordinates (d'.val : ComplexModel e'.dim) =
            (fun k => polyEval (p k) (c'.val : ComplexModel e.dim) /
              polyEval r (c'.val : ComplexModel e.dim) ^ m k) ∧
          chartPoint e' d' = schemeComplexPointMap (ρ ≫ f) f ρ rfl (chartPoint e c') := by
  classical
  have hP : Spec.map (CommRingCat.ofHom (pointEval c)) default ∈
      (e.map ≫ ρ) ⁻¹' Set.range e'.map := by
    simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hc
  have hopen : IsOpen ((e.map ≫ ρ) ⁻¹' Set.range e'.map) :=
    e'.map.isOpenEmbedding.isOpen_range.preimage (e.map ≫ ρ).continuous
  obtain ⟨_, ⟨r₀, rfl⟩, hPr, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens
      (R := MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal)).exists_subset_of_mem_open hP hopen
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r₀
  have hcr : polyEval r (c.val : ComplexModel e.dim) ≠ 0 := by
    have h1 : Ideal.Quotient.mk e.ideal r ∉
        (Spec.map (CommRingCat.ofHom (pointEval c)) default).asIdeal :=
      (PrimeSpectrum.mem_basicOpen _ _).mp hPr
    rw [spec_pointEval_asIdeal, RingHom.mem_ker, pointEval_mk] at h1
    exact h1
  let L := Localization.Away (Ideal.Quotient.mk e.ideal r)
  let ι : coordRing e.ideal ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap _ L)
  have hrange : Set.range (Spec.map ι ≫ e.map ≫ ρ) ⊆ Set.range e'.map := by
    rintro _ ⟨s, rfl⟩
    have hs : Spec.map ι s ∈ (PrimeSpectrum.basicOpen (Ideal.Quotient.mk e.ideal r) :
        Set (PrimeSpectrum (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal))) := by
      rw [← PrimeSpectrum.localization_away_comap_range L]
      exact ⟨s, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hsub hs
  let Λ := IsOpenImmersion.lift e'.map (Spec.map ι ≫ e.map ≫ ρ) hrange
  have hΛ : Λ ≫ e'.map = Spec.map ι ≫ e.map ≫ ρ := IsOpenImmersion.lift_fac _ _ _
  let ψ : coordRing e'.ideal ⟶ CommRingCat.of L := Spec.preimage Λ
  have hψ : Spec.map ψ = Λ := Spec.map_preimage Λ
  have hψC : CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal)) ≫ ψ =
      CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal)) ≫ ι := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← e'.isOver, ← e.isOver, hψ]
    calc
      Λ ≫ e'.map ≫ f = (Λ ≫ e'.map) ≫ f := (Category.assoc _ _ _).symm
      _ = (Spec.map ι ≫ e.map ≫ ρ) ≫ f := by rw [hΛ]
      _ = Spec.map ι ≫ e.map ≫ ρ ≫ f := by simp only [Category.assoc]
  have hsurj : ∀ k : Fin e'.dim, ∃ (j : ℕ) (a : MvPolynomial (Fin e.dim) ℂ),
      ψ.hom (Ideal.Quotient.mk e'.ideal (MvPolynomial.X k)) *
          algebraMap _ L (Ideal.Quotient.mk e.ideal r) ^ j =
        algebraMap _ L (Ideal.Quotient.mk e.ideal a) := by
    intro k
    obtain ⟨j, a, ha⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk e.ideal r)
      (ψ.hom (Ideal.Quotient.mk e'.ideal (MvPolynomial.X k)))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨j, a, ha⟩
  choose m p hp using hsurj
  refine ⟨r, p, m, hcr, ?_⟩
  intro c' hc'
  have hunit : IsUnit (pointEval c' (Ideal.Quotient.mk e.ideal r)) := by
    rw [pointEval_mk]
    exact isUnit_iff_ne_zero.mpr hc'
  let χ : L →+* ℂ := IsLocalization.Away.lift (Ideal.Quotient.mk e.ideal r) hunit
  have hχ : ∀ a, χ (algebraMap _ L a) = pointEval c' a :=
    IsLocalization.Away.lift_eq (Ideal.Quotient.mk e.ideal r) hunit
  let μ : (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal) →+* ℂ := χ.comp ψ.hom
  have hμ : μ.comp (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal)) = RingHom.id ℂ := by
    apply RingHom.ext
    intro a
    have h1 : ψ.hom (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal) a) =
        algebraMap _ L (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal) a) :=
      congrArg (fun g => g.hom a) hψC
    have h2 : pointEval c' (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal) a) = a :=
      congrArg (fun g : ℂ →+* ℂ => g a) (pointEval_comp_algebraMap c')
    change χ (ψ.hom (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal) a)) = a
    rw [h1, hχ, h2]
  refine ⟨ofEval μ hμ, ?_, ?_⟩
  · funext k
    simp only [ofEval, complexCoordinates_ofCoords]
    have hk := congrArg χ (hp k)
    rw [map_mul, map_pow, hχ, hχ, pointEval_mk, pointEval_mk] at hk
    rw [eq_div_iff (pow_ne_zero _ hc')]
    exact hk
  · apply Subtype.ext
    change (chartPoint e' (ofEval μ hμ)).val = (chartPoint e c').val ≫ ρ
    rw [chartPoint_val, chartPoint_val, pointEval_ofEval]
    have h1 : CommRingCat.ofHom μ = ψ ≫ CommRingCat.ofHom χ := rfl
    have h2 : CommRingCat.ofHom (pointEval c') = ι ≫ CommRingCat.ofHom χ :=
      CommRingCat.hom_ext (RingHom.ext fun a => (hχ a).symm)
    simp only [h1, h2, Spec.map_comp, Category.assoc, hψ, hΛ]

open TopologicalSpace SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
open scoped Manifold ContDiff

set_option maxHeartbeats 1000000 in
/-- A scheme morphism induces a morphism of the glued reduced analytic spaces,
with its literal map on complex points. -/
theorem exists_analytification_morphism
    {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [IsSeparated (ρ ≫ f)] [QuasiCompact (ρ ≫ f)] [LocallyOfFiniteType (ρ ≫ f)] :
    ∃ F : analytification (ρ ≫ f) ⟶ analytification f, ∀ y : analytificationLRS (ρ ≫ f),
      pointMap f (F.hom.left.base y) = schemeComplexPointMap (ρ ≫ f) f ρ rfl (pointMap (ρ ≫ f) y) := by
  classical
  let pointEquiv := Equiv.ofBijective (pointMap f) ⟨pointMap_injective, pointMap_surjective⟩
  let φ : analytificationLRS (ρ ≫ f) → analytificationLRS f := fun y =>
    pointEquiv.symm (schemeComplexPointMap (ρ ≫ f) f ρ rfl (pointMap (ρ ≫ f) y))
  have hφ (y : analytificationLRS (ρ ≫ f)) :
      pointMap f (φ y) = schemeComplexPointMap (ρ ≫ f) f ρ rfl (pointMap (ρ ≫ f) y) :=
    pointEquiv.apply_symm_apply _
  suffices h : ∃ F : analytification (ρ ≫ f) ⟶ analytification f,
      ∀ y : analytificationLRS (ρ ≫ f), F.hom.left.base y = φ y by
    obtain ⟨F, hF⟩ := h
    exact ⟨F, fun y => (congrArg (pointMap f) (hF y)).trans (hφ y)⟩
  refine HironakaG10GenGluing.exists_hom_of_local
    (A := analytification (ρ ≫ f)) (B := analytification f) φ ?_
  intro y
  obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective y
  obtain ⟨e', d, hd⟩ := exists_chartPoint_eq
    (schemeComplexPointMap (ρ ≫ f) f ρ rfl (chartPoint e c))
  have hc : ρ (e.map (Spec.map (CommRingCat.ofHom (pointEval c)) default)) ∈ Set.range e'.map := by
    refine ⟨Spec.map (CommRingCat.ofHom (pointEval d)) default, ?_⟩
    have h := congrArg (schemeComplexPointImage f) hd
    change schemeComplexPointImage f (chartPoint e' d) =
      ((chartPoint e c).val ≫ ρ) default at h
    rw [chartPoint_image, Scheme.Hom.comp_apply] at h
    exact h.trans (congrArg (fun x : Y => ρ x) (chartPoint_image e c))
  obtain ⟨r, p, m, hr, hcoords⟩ := exists_local_morphism_coords f ρ e e' c hc
  let U : Opens (Amb e) := ⟨{z | polyEval r (z : ComplexModel e.dim) ≠ 0},
    (isOpen_ne_fun (contDiff_polyEval r).continuous continuous_const).preimage continuous_subtype_val⟩
  let S : Set U := (Subtype.val : U → Amb e) ⁻¹' polynomialZeroSet e.ideal
  let I : actualSubspaceLocallyRingedSpace S ⟶ chartModel e :=
    actualOpenSubspaceMap (polynomialZeroSet e.ideal) U
  let k := I ≫ chartEmbedding e
  have hk : LocallyRingedSpace.IsOpenImmersion k := by
    unfold k I
    infer_instance
  let g : U → Amb e' := fun u => ⟨fracMap r p m (u.val : ComplexModel e.dim), Set.mem_univ _⟩
  have hg : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff (⊤ : Opens (ComplexModel e'.dim)) _).mp
    intro u
    change ContMDiffAt 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞
      (fun z : U => fracMap r p m (z.val : ComplexModel e.dim)) u
    have hAmbient : ContMDiffAt 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞
        (fracMap r p m) (u.val : ComplexModel e.dim) :=
      (contDiffAt_fracMap r p m u.property).contMDiffAt
    have hChart : ContMDiffAt 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞
        (fun z : Amb e => fracMap r p m (z : ComplexModel e.dim)) u.val :=
      contMDiffAt_subtype_iff.mpr hAmbient
    exact contMDiffAt_subtype_iff.mpr hChart
  have hg_point (z : S) :
      ∃ d' : polynomialZeroSet e'.ideal, g z.val = d'.val ∧
        chartPoint e' d' = schemeComplexPointMap (ρ ≫ f) f ρ rfl
          (chartPoint e (I.base z)) := by
    obtain ⟨d', hcoord, hpt⟩ := hcoords (I.base z) z.val.property
    refine ⟨d', eq_of_complexCoordinates_eq ?_, hpt⟩
    change complexCoordinates (fracMap r p m (z.val.val : ComplexModel e.dim)) = _
    rw [complexCoordinates_fracMap]
    exact hcoord.symm
  have hgS : Set.MapsTo g S (polynomialZeroSet e'.ideal) := by
    intro u hu
    obtain ⟨d', heq, _⟩ := hg_point ⟨u, hu⟩
    change g u = d'.val at heq
    rw [heq]
    exact d'.property
  let G : actualSubspaceLocallyRingedSpace S ⟶ chartModel e' := actualSubspaceMap hg hgS
  refine ⟨_, k, G ≫ chartEmbedding e', hk, ⟨⟨⟨c.val, hr⟩, c.property⟩, rfl⟩, ?_, ?_⟩
  · change (G ≫ chartEmbedding e') ≫ structureMap f = k ≫ structureMap (ρ ≫ f)
    simp only [k, Category.assoc, chartEmbedding_structureMap]
    exact (actualSubspaceMap_point hg hgS).trans
      (actualSubspaceMap_point (f := (Subtype.val : U → Amb e)) contMDiff_subtype_val
        (fun _ hz => hz)).symm
  · intro z
    apply pointMap_injective
    change pointMap f ((G ≫ chartEmbedding e').base z) = pointMap f (φ (k.base z))
    obtain ⟨d', heq, hpt⟩ := hg_point z
    have he : G.base z = d' := Subtype.ext heq
    rw [comp_base_apply, he, pointMap_chartEmbedding, hφ]
    unfold k
    rw [comp_base_apply, pointMap_chartEmbedding]
    exact hpt


end

end SGPT.Unibranch.UnibAn
