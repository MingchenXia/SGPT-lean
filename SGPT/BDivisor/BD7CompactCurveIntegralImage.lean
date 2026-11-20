import SGPT.BDivisor.BD7CompactCurveAlgebraicImage
import SGPT.Okounkov.OF14Integral
import SGPT.Projective.BDivOriginalIdealStalk
import SGPT.Okounkov.OF12SmoothProjectiveBirationalModel
import SGPT.Okounkov.SchemeNativeAnalyticSubset
import SGPT.Foundations.Analysis.Pending.AnalyticImageDimension
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.BDivisor.GM
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

local instance curveTopology {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance curveCharts {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g d
local instance curveManifold {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

private theorem curve_stalkIdeal_radical {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) :
    I.radical.stalkIdeal x = (I.stalkIdeal x).radical := by
  obtain ⟨U, hx⟩ := SGPT.NAPotential.Berkovich.exists_affineOpen_mem x
  rw [I.radical.stalkIdeal_eq_affine x U hx, I.stalkIdeal_eq_affine x U hx]
  change Ideal.map _ (I.ideal U).radical = (Ideal.map _ (I.ideal U)).radical
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.map_radical (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) _

private theorem reduced_vanishingIdeal_subscheme {X : Scheme.{0}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hs : I.support = Z := Closeds.ext (by
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  have hr : I.radical = I := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, hs]
  refine @isReduced_of_isReduced_stalk I.subscheme ?_
  intro z
  have hq : IsReduced (X.presheaf.stalk (I.subschemeι z) ⧸ I.stalkIdeal (I.subschemeι z)) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← Ideal.radical_eq_iff, ← curve_stalkIdeal_radical, hr]
  let e := (Ideal.quotEquivOfEq (I.ker_stalkMap_subschemeι z).symm).trans
    (((I.subschemeι.stalkMap z).hom).quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective z))
  exact isReduced_of_injective e.symm e.symm.injective

/-- The reduced, integral closed scheme whose complex points are exactly the given image. -/
theorem exists_integralProjective_image_of_compactCurve_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [CompactSpace T] [ConnectedSpace T] (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g) :
    ∃ I : X.IdealSheafData, IsIntegral I.subscheme ∧
      Nonempty (ClosedProjectiveEmbedding (I.subschemeι ≫ f)) ∧
      range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) = range g := by
  obtain ⟨Z, hZ, htrace⟩ := exists_closedAlgebraicTrace_eq_image_of_compactCurve_bd7 f E n g hg
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : Closeds X)
  let c := I.subschemeι ≫ f
  let j := schemeComplexPointMap c f I.subschemeι rfl
  have himage : range j = range g := by
    rw [htrace]
    change range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) = _
    rw [closedImmersionComplexPointMap_range]
    ext q
    change schemeComplexPointImage f q ∈ range I.subschemeι ↔ schemeComplexPointImage f q ∈ Z
    rw [I.range_subschemeι]
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal] <;> rfl
  have hpoint (q : SchemeComplexPoint c) :
      schemeComplexPointImage f (j q) = I.subschemeι (schemeComplexPointImage c q) := by
    simp only [j, schemeComplexPointImage, schemeComplexPointMap, Scheme.Hom.comp_apply]
  have hfact (x : T) : schemeComplexPointImage f (g x) ∈ range I.subschemeι := by
    have hx : g x ∈ range j := by
      rw [himage]
      exact mem_range_self x
    obtain ⟨q, hq⟩ := hx
    exact ⟨schemeComplexPointImage c q, (hpoint q).symm.trans (congrArg (schemeComplexPointImage f) hq)⟩
  let : IsClosedImmersion E.map := E.closedImmersion
  let : IsProper f := E.isProper
  let : LocallyOfFiniteType c := inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ f))
  let : Nonempty I.subscheme := ⟨Classical.choose (hfact (Classical.choice (inferInstance : Nonempty T)))⟩
  have hfull (F : Set I.subscheme) (hF : IsClosed F)
      (h : univ = g ⁻¹' schemeNativeAlgebraicTrace f (I.subschemeι '' F)) : univ ⊆ F := by
    have hrange : range (schemeComplexPointImage c) ⊆ F := by
      rintro _ ⟨q, rfl⟩
      have hq : j q ∈ range g := by
        rw [← himage]
        exact mem_range_self q
      obtain ⟨x, hx⟩ := hq
      have hxF : x ∈ g ⁻¹' schemeNativeAlgebraicTrace f (I.subschemeι '' F) :=
        h ▸ mem_univ x
      change schemeComplexPointImage f (g x) ∈ I.subschemeι '' F at hxF
      rw [hx, hpoint] at hxF
      obtain ⟨v, hv, he⟩ := hxF
      exact I.subschemeι.isClosedEmbedding.injective he ▸ hv
    rw [← (OF14.dense_range_schemeComplexPointImage c).closure_eq]
    exact closure_minimal hrange hF
  have hpre : IsPreirreducible (univ : Set I.subscheme) := by
    apply isPreirreducible_iff_isClosed_union_isClosed.mpr
    intro F G hF hG hcover
    let A := g ⁻¹' schemeNativeAlgebraicTrace f (I.subschemeι '' F)
    let B := g ⁻¹' schemeNativeAlgebraicTrace f (I.subschemeι '' G)
    have hA : IsComplexAnalyticSubset (n := 1) A :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg
        (schemeNativeAlgebraicTrace_isComplexAnalyticSubset f n _ (I.subschemeι.isClosedMap F hF))
    have hB : IsComplexAnalyticSubset (n := 1) B :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg
        (schemeNativeAlgebraicTrace_isComplexAnalyticSubset f n _ (I.subschemeι.isClosedMap G hG))
    have hAB : (univ : Set T) = A ∪ B := by
      apply eq_of_subset_of_subset _ (subset_univ _)
      intro x _
      obtain ⟨z, hz⟩ := hfact x
      rcases hcover (mem_univ z) with h | h
      · exact Or.inl ⟨z, h, hz⟩
      · exact Or.inr ⟨z, h, hz⟩
    rcases (isComplexAnalyticallyIrreducible_univ_of_connectedSpace (n := 1) (M := T)).eq_left_or_eq_right
        hA hB (subset_univ _) (subset_univ _) hAB with h | h
    · exact Or.inl (hfull F hF h)
    · exact Or.inr (hfull G hG h)
  let : PreirreducibleSpace I.subscheme := ⟨hpre⟩
  let : IrreducibleSpace I.subscheme := { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  let : IsReduced I.subscheme := reduced_vanishingIdeal_subscheme ⟨Z, hZ⟩
  refine ⟨I, isIntegral_of_irreducibleSpace_of_isReduced _, ⟨?_⟩, himage⟩
  exact {
    ambientDimension := E.ambientDimension
    map := I.subschemeι ≫ E.map
    closedImmersion := inferInstance
    over_base := by rw [Category.assoc, E.over_base] }

/-- Every regular local dimension of the ambient compact curve image is at most one. -/
theorem dimLE_projectivePoint_image_of_compactCurve_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g) :
    AnalyticDimensionBasics.DimLE (n := E.ambientDimension) (range (projectivePoint f E n ∘ g)) 1 := by
  let F := projectivePoint f E n ∘ g
  have hF := (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding
    (isHolomorphicEmbedding_projectivePoint f E n)).comp hg
  have hdim : AnalyticDimensionBasics.DimLE (n := 1) (univ : Set T) 1 :=
    fun _ _ hx => hx.1
  have h := AnalyticImageDimension.dimLE_image (a := 1) (b := 0) (T := univ)
    hF isComplexAnalyticSubset_univ hdim (fun x hx => AnalyticDimensionBasics.locDimGE_zero
      (isComplexAnalyticSubset_univ.inter
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hF
          (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (F x))))
      ⟨hx, by simp [F]⟩)
  simpa only [image_univ, Nat.sub_zero] using h

/-- A nonconstant compact curve map has ambient regular dimension exactly one. -/
theorem regularAtDim_projectivePoint_image_eq_one_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [CompactSpace T] [ConnectedSpace T] (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hnc : ∃ x y, g x ≠ g y) {z : ComplexProjectiveSpace E.ambientDimension} {k : ℕ}
    (hz : RegularAtDim (n := E.ambientDimension) (range (projectivePoint f E n ∘ g)) z k) :
    k = 1 := by
  let F := projectivePoint f E n ∘ g
  have hEmbed := isHolomorphicEmbedding_projectivePoint f E n
  have hF := (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hEmbed).comp hg
  have hle := dimLE_projectivePoint_image_of_compactCurve_bd7 f E n g hg z k hz
  suffices hne : k ≠ 0 by omega
  rintro rfl
  have hproper : AnalyticDimensionBasics.ProperOn F univ := by
    intro K hK
    rw [univ_inter]
    exact (hK.isClosed.preimage hF.continuous).isCompact
  have hA : IsComplexAnalyticSubset (n := E.ambientDimension) (range F) := by
    simpa only [image_univ] using ProperMappingTheorem.isComplexAnalyticSubset_image
      hF (isComplexAnalyticSubset_univ (n := 1) (M := T)) hproper
  have hisol := AnalyticDimensionBasics.not_accPt_of_locDimLE_zero hA hz.2.1
    (AnalyticDimensionBasics.locDimLE_of_regularAtDim hz)
  rw [accPt_iff_nhds] at hisol
  push Not at hisol
  obtain ⟨U, hU, hsingle⟩ := hisol
  obtain ⟨W, hWU, hW, hzW⟩ := mem_nhds_iff.mp hU
  have hpre : F ⁻¹' W = F ⁻¹' {z} := by
    ext x
    exact ⟨fun hx => hsingle (F x) ⟨hWU hx, mem_range_self x⟩,
      fun hx => by
        change F x ∈ W
        simpa only [mem_singleton_iff.mp hx] using hzW⟩
  have hop : IsOpen (F ⁻¹' {z}) := hpre ▸ hW.preimage hF.continuous
  have hcl : IsClosed (F ⁻¹' {z}) := isClosed_singleton.preimage hF.continuous
  have hnon : (F ⁻¹' {z}).Nonempty := by
    obtain ⟨x, hx⟩ := hz.2.1
    exact ⟨x, mem_singleton_iff.mpr hx⟩
  have hall := IsClopen.eq_univ ⟨hcl, hop⟩ hnon
  obtain ⟨x, y, hxy⟩ := hnc
  have heq (t : T) : F t = z := by
    have ht : t ∈ F ⁻¹' {z} := by rw [hall]; exact mem_univ t
    exact mem_singleton_iff.mp ht
  exact hxy (hEmbed.injective ((heq x).trans (heq y).symm))

/-- The image of a nonconstant compact connected curve map is an integral projective curve,
with a proper smooth projective birational curve over the image. -/
theorem exists_smoothProjectiveCurve_over_image_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [CompactSpace T] [ConnectedSpace T] (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hnc : ∃ x y, g x ≠ g y) :
    ∃ (I : X.IdealSheafData) (_ : IsIntegral I.subscheme)
      (_ : ClosedProjectiveEmbedding (I.subschemeι ≫ f)),
      range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) = range g ∧
      letI := schemeFunctionFieldAlgebra (I.subschemeι ≫ f)
      Algebra.trdeg ℂ I.subscheme.functionField = 1 ∧
      ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ I.subscheme) (_ : IsProper ρ)
        (_ : SmoothOfRelativeDimension 1 (ρ ≫ (I.subschemeι ≫ f)))
        (_ : ClosedProjectiveEmbedding (ρ ≫ (I.subschemeι ≫ f))),
        IsIso (ρ.stalkMap (genericPoint Y)) ∧
        ∃ U : I.subscheme.Opens, (U : Set I.subscheme).Nonempty ∧
          Function.Bijective
            (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ (I.subschemeι ≫ f)))
              (U.ι ≫ (I.subschemeι ≫ f)) (ρ ∣_ U) rfl) := by
  obtain ⟨I, hI, _, himage⟩ := exists_integralProjective_image_of_compactCurve_bd7 f E n g hg
  let := hI
  let c := I.subschemeι ≫ f
  let j := schemeComplexPointMap c f I.subschemeι rfl
  let : IsClosedImmersion E.map := E.closedImmersion
  let EI : ClosedProjectiveEmbedding c := {
    ambientDimension := E.ambientDimension
    map := I.subschemeι ≫ E.map
    closedImmersion := inferInstance
    over_base := by rw [Category.assoc, E.over_base] }
  have hcomp (q : SchemeComplexPoint c) :
      ambientPoint EI q = projectivePoint f E n (j q) := by
    rw [← ambientPoint_eq_projectivePoint E n]
    unfold ambientPoint
    apply congrArg (originalProjectiveHomeomorph E.ambientDimension)
    apply Subtype.ext
    simp only [EI, j, schemeComplexPointMap, Category.assoc]
  have hrange : range (ambientPoint EI) = range (projectivePoint f E n ∘ g) := by
    change range j = range g at himage
    rw [show ambientPoint EI = projectivePoint f E n ∘ j from funext hcomp]
    rw [range_comp, range_comp, himage]
  obtain ⟨V, M, tM, cM, mM, σ, _hσ, hS, Y, hY, s, hs, EY, ρ, hρ, hrest⟩ :=
    OF12.exists_projective_model_of_embedded_resolution EI
  let := tM
  let := cM
  let := mM
  let := hY
  subst s
  let := hs
  let := EY.isSeparated
  let := EY.quasiCompact
  let : TopologicalSpace (SchemeComplexPoint (ρ ≫ c)) := schemeAnalyticPointTopology _
  let : ChartedSpace (ComplexModel V.dim) (SchemeComplexPoint (ρ ≫ c)) :=
    schemeAnalyticTNChartedSpace (ρ ≫ c) V.dim
  let := SubmanifoldChartedSpace.chartedSpace V.dim_le hS.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace V.dim_le hS.2.2
  obtain ⟨hV, hiso, e, he⟩ := hrest
  have hdim : V.dim = 1 := by
    obtain ⟨z, hz⟩ := V.regularLocus_nonempty
    change RegularAtDim V.carrier z V.dim at hz
    rw [hV, hrange] at hz
    exact regularAtDim_projectivePoint_image_eq_one_bd7 f E n g hg hnc hz
  obtain ⟨U, hU, hbij⟩ :=
    OF12.exists_nonempty_open_complexPoint_bijective_of_embedded_projection EI ρ
      e.toHomeomorph.toEquiv hV hiso he
  let : IsProper (ρ ≫ c) := EY.isProper
  let : IsProper ρ := IsProper.of_comp ρ c
  let : Nonempty U := hU.to_subtype
  let := EI.isSeparated
  let := EI.locallyOfFiniteType
  let := schemeFunctionFieldAlgebra c
  obtain ⟨hbirational, eField, hfield⟩ :=
    OF12.birationalData_of_restrict_complexPoint_bijective c ρ U hbij
  have htrdeg := OF12.functionField_trdeg_of_stalkCompatible_smooth_model c ρ eField hfield V.dim
  exact ⟨I, hI, EI, himage, (by simpa only [hdim, Nat.cast_one] using htrdeg),
    Y, hY, ρ, inferInstance, hdim ▸ hs, EY, hbirational, U, hU, hbij⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
