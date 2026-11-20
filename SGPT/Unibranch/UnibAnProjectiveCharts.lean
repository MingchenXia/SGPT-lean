import SGPT.Unibranch.UnibAnClosedAffineChart
import SGPT.Foundations.Schemes.NativeProjectiveFano
import SGPT.Foundations.Schemes.ProjectiveAnalyticRatioCharts

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Unibranch SGPT.Foundations.Schemes

namespace SGPT.Unibranch.UnibAn

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pull back an embedded affine chart through a closed immersion, retaining
a quotient presentation in exactly the same ambient coordinates. -/
theorem exists_closedAffinePresentation
    {X Y : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (ρ : Y ⟶ X) [IsClosedImmersion ρ]
    (e : EmbeddedChart f) :
    ∃ (J : Ideal (MvPolynomial (Fin e.dim) ℂ)) (hIJ : e.ideal ≤ J)
      (u : Spec (coordRing J) ⟶ Y),
      IsOpenImmersion u ∧
      Set.range u = ρ ⁻¹' Set.range e.map ∧
      u ≫ ρ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ)) ≫ e.map := by
  let d := bweChart e
  let c := closedImmersionAffineSourceChart ρ d
  let l : Spec c.ring ⟶ Spec (coordRing e.ideal) := closedImmersionAffineChartMap ρ d
  let : IsClosedImmersion l := closedImmersionAffineChartMap_isClosedImmersion ρ d
  let τ : coordRing e.ideal ⟶ c.ring := Spec.preimage l
  let φ : MvPolynomial (Fin e.dim) ℂ →+* c.ring :=
    τ.hom.comp (Ideal.Quotient.mk e.ideal)
  have hφ : Function.Surjective φ :=
    (affineClosedImmersion_preimage_surjective l).comp Ideal.Quotient.mk_surjective
  let J := RingHom.ker φ
  have hIJ : e.ideal ≤ J := by
    intro p hp
    change τ.hom (Ideal.Quotient.mk e.ideal p) = 0
    exact (congrArg τ.hom ((Ideal.Quotient.eq_zero_iff_mem).mpr hp)).trans (map_zero τ.hom)
  let E := RingHom.quotientKerEquivOfSurjective hφ
  let a : c.ring ≅ coordRing J := E.symm.toCommRingCatIso
  have hfactor : CommRingCat.ofHom (Ideal.Quotient.factor hIJ) ≫ a.inv = τ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun (w : MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal) => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
    change E (Ideal.Quotient.factor hIJ (Ideal.Quotient.mk e.ideal p)) =
      τ.hom (Ideal.Quotient.mk e.ideal p)
    rw [Ideal.Quotient.factor_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    rfl
  let factor : coordRing e.ideal ⟶ coordRing J :=
    CommRingCat.ofHom (Ideal.Quotient.factor hIJ)
  have hcomp : τ ≫ a.hom = factor := calc
    τ ≫ a.hom = (factor ≫ a.inv) ≫ a.hom :=
      congrArg (fun k : coordRing e.ideal ⟶ c.ring => k ≫ a.hom) hfactor.symm
    _ = factor := by rw [Category.assoc, a.inv_hom_id, Category.comp_id]
  have hmap : Spec.map a.hom ≫ l = Spec.map factor := calc
    Spec.map a.hom ≫ l = Spec.map a.hom ≫ Spec.map τ :=
      congrArg (fun k : Spec c.ring ⟶ Spec (coordRing e.ideal) => Spec.map a.hom ≫ k)
        (Spec.map_preimage l).symm
    _ = Spec.map (τ ≫ a.hom) := by rw [Spec.map_comp]
    _ = Spec.map factor := congrArg Spec.map hcomp
  let u := Spec.map a.hom ≫ c.map
  have hu : IsOpenImmersion u := by unfold u; infer_instance
  refine ⟨J, hIJ, u, hu, ?_, ?_⟩
  · change Set.range (Spec.map a.hom ≫ c.map) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso (Spec.map a.hom).base).2.range_eq, Set.image_univ]
    exact closedImmersionAffineSourceChart_range ρ d
  · change (Spec.map a.hom ≫ c.map) ≫ ρ = Spec.map factor ≫ e.map
    have hfac : c.map ≫ ρ = l ≫ e.map := closedImmersionAffineChartMap_fac ρ d
    calc
      (Spec.map a.hom ≫ c.map) ≫ ρ = Spec.map a.hom ≫ (c.map ≫ ρ) :=
        Category.assoc _ _ _
      _ = Spec.map a.hom ≫ (l ≫ e.map) := congrArg (fun k => Spec.map a.hom ≫ k) hfac
      _ = (Spec.map a.hom ≫ l) ≫ e.map := (Category.assoc _ _ _).symm
      _ = Spec.map factor ≫ e.map := congrArg (fun k => k ≫ e.map) hmap

/-- The usual affine projective chart, presented in the native polynomial
coordinates with zero defining ideal. -/
def projectiveAmbientChart (N : ℕ) (i : Fin (N + 1)) :
    EmbeddedChart (polynomialProjStructureMap ℂ N) := by
  let P := MvPolynomial (Fin N) ℂ
  let E : polynomialProjCoordinateRing ℂ N i ≃+* P ⧸ (⊥ : Ideal P) :=
    (polynomialProjCoordinateEquiv ℂ N i).toRingEquiv.trans (RingEquiv.quotientBot P).symm
  let a : CommRingCat.of (polynomialProjCoordinateRing ℂ N i) ≅
      coordRing (⊥ : Ideal P) := E.toCommRingCatIso
  refine ⟨N, ⊥, Spec.map a.hom ≫ polynomialProjCoordinateImmersion ℂ N i, inferInstance, ?_⟩
  rw [Category.assoc, polynomialProjCoordinateImmersion_structure, affineStructuralMap, affineBaseRingMap,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  refine RingHom.ext fun b => ?_
  change Ideal.Quotient.mk (⊥ : Ideal P)
      (polynomialProjCoordinateEquiv ℂ N i (algebraMap ℂ _ b)) =
    algebraMap ℂ (P ⧸ (⊥ : Ideal P)) b
  rw [AlgEquiv.commutes]; rfl

theorem polynomialZeroSet_bot (N : ℕ) :
    polynomialZeroSet (⊥ : Ideal (MvPolynomial (Fin N) ℂ)) = Set.univ := by
  ext y
  refine ⟨fun _ => Set.mem_univ _, fun _ p hp => ?_⟩
  have hp0 : p = 0 := hp
  simp [hp0]

/-- Every fixed embedded chart hits precisely the complex points over its
original algebraic range. -/
theorem chartPoint_range {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (e : EmbeddedChart f) :
    Set.range (chartPoint e) = schemeComplexPointImage f ⁻¹' Set.range e.map := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom (pointEval z)) default, (chartPoint_image e z).symm⟩
  · intro hp
    let q := schemeComplexPointLift f e.map p hp
    refine ⟨ofSpecPoint e q, ?_⟩
    rw [chartPoint_eq_map, chartSpecPoint_ofSpecPoint]
    apply Subtype.ext
    exact schemeComplexPointLift_fac f e.map p hp

/-- The explicit quotient-zero projective chart has exactly the algebraic range
of the usual projective coordinate immersion. -/
theorem projectiveAmbientChart_range (N : ℕ) (i : Fin (N + 1)) :
    Set.range (projectiveAmbientChart N i).map =
      Set.range (polynomialProjCoordinateImmersion ℂ N i) := by
  unfold projectiveAmbientChart
  dsimp only
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso (Spec.map _).base).2.range_eq, Set.image_univ]

theorem projectiveAmbientChart_complexPoint_range (N : ℕ) (i : Fin (N + 1)) :
    Set.range (chartPoint (projectiveAmbientChart N i)) =
      (polynomialProjRatioChart N i).source := by
  rw [chartPoint_range, projectiveAmbientChart_range]
  ext p
  exact (polynomialProjRatioChart_mem_source N i p).symm

/-- The full closed source chart retains the original map to the standard
ambient projective chart and covers its entire complex-point preimage. -/
theorem exists_projectiveSourceChart {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) (i : Fin (E.ambientDimension + 1)) :
    ∃ (J : Ideal (MvPolynomial (Fin E.ambientDimension) ℂ)) (u : Spec (coordRing J) ⟶ X)
      (hu : IsOpenImmersion u)
      (hover : u ≫ f = Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (MvPolynomial (Fin E.ambientDimension) ℂ ⧸ J)))),
      let e : EmbeddedChart f := ⟨E.ambientDimension, J, u, hu, hover⟩
      u ≫ E.map = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (bot_le : ⊥ ≤ J))) ≫
          (projectiveAmbientChart E.ambientDimension i).map ∧
      Set.range (chartPoint e) = (schemeComplexPointMap f _ E.map E.over_base) ⁻¹'
        (polynomialProjRatioChart E.ambientDimension i).source := by
  let d := projectiveAmbientChart E.ambientDimension i
  obtain ⟨J, hJ, u, hu, hrange, hfac⟩ := exists_closedAffinePresentation E.map d
  have hfac' : u ≫ E.map = Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.factor (bot_le : ⊥ ≤ J))) ≫ d.map := hfac
  have hover : u ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin E.ambientDimension) ℂ ⧸ J))) := by
    let factor : coordRing d.ideal ⟶ coordRing J :=
      CommRingCat.ofHom (Ideal.Quotient.factor hJ)
    let base : CommRingCat.of ℂ ⟶ coordRing d.ideal :=
      CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin d.dim) ℂ ⧸ d.ideal))
    have hbase : base ≫ factor = CommRingCat.ofHom
        (algebraMap ℂ (MvPolynomial (Fin E.ambientDimension) ℂ ⧸ J)) := by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun b => ?_
      exact (Ideal.Quotient.factorₐ ℂ hJ).commutes b
    calc
      u ≫ f = u ≫ (E.map ≫ polynomialProjStructureMap ℂ E.ambientDimension) :=
        congrArg (fun k : X ⟶ Spec (.of ℂ) => u ≫ k) E.over_base.symm
      _ = (u ≫ E.map) ≫ polynomialProjStructureMap ℂ E.ambientDimension :=
        (Category.assoc _ _ _).symm
      _ = (Spec.map factor ≫ d.map) ≫ polynomialProjStructureMap ℂ E.ambientDimension :=
        congrArg (fun k => k ≫ polynomialProjStructureMap ℂ E.ambientDimension) hfac
      _ = Spec.map factor ≫ Spec.map base :=
        (Category.assoc _ _ _).trans (congrArg (fun k => Spec.map factor ≫ k) d.isOver)
      _ = Spec.map (base ≫ factor) := by rw [Spec.map_comp]
      _ = _ := congrArg Spec.map hbase
  refine ⟨J, u, hu, hover, hfac', ?_⟩
  rw [chartPoint_range]
  change schemeComplexPointImage f ⁻¹' Set.range u = _
  rw [hrange]
  rw [show Set.range d.map = Set.range (polynomialProjCoordinateImmersion ℂ E.ambientDimension i)
    from projectiveAmbientChart_range _ _]
  ext p
  let q := schemeComplexPointMap f _ E.map E.over_base p
  change E.map (schemeComplexPointImage f p) ∈
    Set.range (polynomialProjCoordinateImmersion ℂ E.ambientDimension i) ↔
    q ∈ (polynomialProjRatioChart E.ambientDimension i).source
  have hq : schemeComplexPointImage (polynomialProjStructureMap ℂ E.ambientDimension) q =
      E.map (schemeComplexPointImage f p) :=
    Scheme.Hom.comp_apply p.val E.map default
  rw [← hq]
  exact (polynomialProjRatioChart_mem_source E.ambientDimension i q).symm


/-- The chosen source chart retains the literal quotient map to its fixed
projective ambient chart together with its entire complex-point image. -/
structure ProjectiveSourceChartData {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) (i : Fin (E.ambientDimension + 1)) where
  ideal : Ideal (MvPolynomial (Fin E.ambientDimension) ℂ)
  map : Spec (coordRing ideal) ⟶ X
  isOpenImmersion : IsOpenImmersion map
  over_base : map ≫ f = Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (MvPolynomial (Fin E.ambientDimension) ℂ ⧸ ideal)))
  factor : map ≫ E.map =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (bot_le : ⊥ ≤ ideal))) ≫
      (projectiveAmbientChart E.ambientDimension i).map
  complexPoint_range : Set.range (chartPoint
      (⟨E.ambientDimension, ideal, map, isOpenImmersion, over_base⟩ : EmbeddedChart f)) =
    (schemeComplexPointMap f _ E.map E.over_base) ⁻¹' (polynomialProjRatioChart E.ambientDimension i).source

def projectiveSourceChartData {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) (i : Fin (E.ambientDimension + 1)) :
    ProjectiveSourceChartData f E i := by
  classical
  apply Classical.choice
  obtain ⟨J, u, hu, hover, hfac, hrange⟩ := exists_projectiveSourceChart f E i
  exact ⟨⟨J, u, hu, hover, hfac, hrange⟩⟩

def projectiveSourceChart {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) (i : Fin (E.ambientDimension + 1)) : EmbeddedChart f :=
  let C := projectiveSourceChartData f E i
  ⟨E.ambientDimension, C.ideal, C.map, C.isOpenImmersion, C.over_base⟩

/-- The finite standard source chart family covers every point of the glued
analytic scheme using the actual chart embeddings. -/
theorem projectiveSourceChart_covers {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) (x : analytificationLRS f) :
    ∃ (i : Fin (E.ambientDimension + 1))
      (z : polynomialZeroSet (projectiveSourceChart f E i).ideal),
      (chartEmbedding (projectiveSourceChart f E i)).base z = x := by
  obtain ⟨i, hi⟩ := polynomialProjRatioChart_sources_cover E.ambientDimension
    (schemeComplexPointMap f _ E.map E.over_base (pointMap f x))
  let e := projectiveSourceChart f E i
  have hrange : Set.range (chartPoint e) =
      (schemeComplexPointMap f _ E.map E.over_base) ⁻¹' (polynomialProjRatioChart E.ambientDimension i).source :=
    (projectiveSourceChartData f E i).complexPoint_range
  have hx : pointMap f x ∈ Set.range (chartPoint e) := hrange.symm ▸ hi
  obtain ⟨z, hz⟩ := hx
  refine ⟨i, z, pointMap_injective ?_⟩
  exact (pointMap_chartEmbedding e z).trans hz


end

end SGPT.Unibranch.UnibAn
