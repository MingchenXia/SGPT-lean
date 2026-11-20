import SGPT.BDivisor.BD7CompactCurveNormalizationLift
import SGPT.BDivisor.BD7CompactCurveIntegralImage
import SGPT.BDivisor.BD7NormalizationGoodOpenLift
import SGPT.PSH.BookMultiplierConvention
import SGPT.Okounkov.SchemeAnalyticMorphism

set_option autoImplicit false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Metric
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

/-- Glue the good-open lift and its pointwise puncture extensions. Each chosen
puncture neighborhood contains just one exceptional point, so the two defining
cases of the global map agree there with the same local holomorphic map. -/
theorem exists_holomorphic_lift_of_isolated_extensions_bd7
    {T Y Z : Type*} [TopologicalSpace T] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 1) T] [ChartedSpace (ComplexModel 1) Y]
    [IsComplexManifold 1 T] [IsComplexManifold 1 Y]
    {B : Set T} (hB : IsClosed B) {π : Y → Z} {G : T → Z} {u : T → Y}
    (hu : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ u Bᶜ)
    (huπ : EqOn (π ∘ u) G Bᶜ)
    (hlocal : ∀ x ∈ B, ∃ (W : Set T) (v : T → Y), IsOpen W ∧ x ∈ W ∧
      W ∩ B ⊆ {x} ∧ ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ v W ∧
      EqOn v u (W \ B) ∧ EqOn (π ∘ v) G W) :
    ∃ L : T → Y, ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ L ∧
      EqOn L u Bᶜ ∧ π ∘ L = G := by
  classical
  have hlocal' (x : B) := hlocal x.val x.property
  choose W v hW hxW hWsingle hv hvu hvπ using hlocal'
  let L (x : T) : Y := if h : x ∈ B then v ⟨x, h⟩ x else u x
  have hegood : EqOn L u Bᶜ := fun x hx => dif_neg hx
  have he (x : B) : EqOn L (v x) (W x) := by
    intro y hy
    by_cases hyB : y ∈ B
    · have hyx : y = x.val := mem_singleton_iff.mp (hWsingle x ⟨hy, hyB⟩)
      subst y
      exact dif_pos x.property
    · exact (hegood hyB).trans (hvu x ⟨hy, hyB⟩).symm
  refine ⟨L, contMDiff_of_locally_contMDiffOn ?_, hegood, funext ?_⟩
  · intro x
    by_cases hx : x ∈ B
    · exact ⟨W ⟨x, hx⟩, hW ⟨x, hx⟩, hxW ⟨x, hx⟩, (hv ⟨x, hx⟩).congr (he ⟨x, hx⟩)⟩
    · exact ⟨Bᶜ, hB.isOpen_compl, hx, hu.congr hegood⟩
  · intro x
    by_cases hx : x ∈ B
    · exact (congrArg π (he ⟨x, hx⟩ (hxW ⟨x, hx⟩))).trans (hvπ ⟨x, hx⟩ (hxW ⟨x, hx⟩))
    · exact (congrArg π (hegood hx)).trans (huπ hx)

private def curveScalarChart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] (x : M) : OpenPartialHomeomorph M ℂ :=
  (chartAt (ComplexModel 1) x).transHomeomorph SGPT.PSH.MultiplierConvention.lineCoord.toHomeomorph

private theorem curveScalarChart_holomorphic {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M] (x : M) :
    ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞ (curveScalarChart x)
      (curveScalarChart x).source := by
  let k := SGPT.PSH.MultiplierConvention.lineCoord
  have hchart : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞
      (chartAt (ComplexModel 1) x) (chartAt (ComplexModel 1) x).source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
  change ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞
    (k ∘ chartAt (ComplexModel 1) x) (chartAt (ComplexModel 1) x).source
  have hk : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞ k := k.contDiff.contMDiff
  exact hk.comp_contMDiffOn hchart

private theorem curveScalarChart_symm_holomorphic {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M] (x : M) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ComplexModel 1) ∞ (curveScalarChart x).symm
      (curveScalarChart x).target := by
  let k := SGPT.PSH.MultiplierConvention.lineCoord
  have hchart : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞
      (chartAt (ComplexModel 1) x).symm (chartAt (ComplexModel 1) x).target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
  change ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ComplexModel 1) ∞
    ((chartAt (ComplexModel 1) x).symm ∘ k.symm) (k.symm ⁻¹' (chartAt (ComplexModel 1) x).target)
  have hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ComplexModel 1) ∞ k.symm := k.symm.contDiff.contMDiff
  exact hchart.comp hk.contMDiffOn (fun _ h => h)

/-- Extend an exact good-open inverse on curves using finite fibers of the actual
projection. No lift across the exceptional trace is an input. -/
theorem exists_holomorphic_lift_of_finite_closed_curveProjection_bd7
    {T Y Z : Type*} [TopologicalSpace T] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    [ChartedSpace (ComplexModel 1) T] [ChartedSpace (ComplexModel 1) Y]
    [IsComplexManifold 1 T] [IsComplexManifold 1 Y]
    (π : Y → Z) (hπ : Continuous π) (hπclosed : IsClosedMap π)
    (hfinite : ∀ z : Z, (π ⁻¹' {z}).Finite)
    (G : T → Z) (hG : Continuous G) {B : Set T} (hBc : IsClosed B) (hBd : IsDiscrete B)
    (u : T → Y) (hu : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ u Bᶜ)
    (huπ : EqOn (π ∘ u) G Bᶜ) :
    ∃ L : T → Y, ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ L ∧
      EqOn L u Bᶜ ∧ π ∘ L = G := by
  apply exists_holomorphic_lift_of_isolated_extensions_bd7 hBc hu huπ
  intro x hx
  have hdisc := isDiscrete_iff_forall_mem_exists_isOpen.mp hBd
  obtain ⟨V, hV, hVB⟩ := hdisc x hx
  have hxV : x ∈ V := ((Set.ext_iff.mp hVB x).mpr (mem_singleton x)).1
  let d := curveScalarChart x
  let a := d x
  let s : ℂ → T := fun z => d.symm (z + a)
  let t : T → ℂ := fun y => d y - a
  have hxs : x ∈ d.source := mem_chart_source _ x
  have hat : a ∈ d.target := d.map_source hxs
  have hs0 : s 0 = x := by simpa [s, a] using d.left_inv hxs
  have hshift : ContinuousAt (fun z : ℂ => z + a) 0 :=
    (continuous_id.add continuous_const).continuousAt
  have h0t : (0 : ℂ) + a ∈ d.target := by simpa using hat
  have hscont : ContinuousAt s 0 :=
    (d.continuousAt_symm h0t).comp_of_eq hshift rfl
  have htnear : ∀ᶠ z : ℂ in 𝓝 0, z + a ∈ d.target :=
    hshift (d.open_target.mem_nhds h0t)
  have hsnear : ∀ᶠ z : ℂ in 𝓝 0, s z ∈ V :=
    hscont (hV.mem_nhds (hs0.symm ▸ hxV))
  obtain ⟨r, hr, hnear'⟩ := Metric.eventually_nhds_iff_ball.mp (htnear.and hsnear)
  have hshiftH : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (fun z : ℂ => z + a) := by
    exact ((contDiff_id.add contDiff_const : ContDiff ℂ ∞ (fun z : ℂ => z + a))).contMDiff
  have hcomp : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ComplexModel 1) ∞ s (ball 0 r) :=
    (curveScalarChart_symm_holomorphic x).comp hshiftH.contMDiffOn (fun z hz => (hnear' z hz).1)
  have hgood : MapsTo s (ball 0 r \ {0}) Bᶜ := by
    intro z hz hzb
    have heq := mem_singleton_iff.mp ((Set.ext_iff.mp hVB (s z)).mp ⟨(hnear' z hz.1).2, hzb⟩)
    have hz0 : z + a = a := by
      calc
        z + a = d (s z) := (d.right_inv (hnear' z hz.1).1).symm
        _ = a := congrArg d heq
    exact hz.2 (add_right_cancel (hz0.trans (zero_add a).symm))
  let S := π ⁻¹' {G (s 0)}
  let e : S → OpenPartialHomeomorph Y ℂ := fun y => curveScalarChart y.val
  obtain ⟨W, R, hW, hdisj, hcover, hsrc, hcoord, htgt⟩ :=
    exists_separated_bounded_charts_of_finite_bd7 (hfinite _) e
      (fun y => mem_chart_source _ y.val)
  have hU := hu.comp (hcomp.mono sdiff_subset) hgood
  have hdiff (i : S) :
      DifferentiableOn ℂ (e i ∘ (u ∘ s)) ((ball 0 r \ {0}) ∩ (u ∘ s) ⁻¹' W i) :=
    ((curveScalarChart_holomorphic i.val).comp (hU.mono inter_subset_left)
      (fun _ h => hsrc i h.2)).contDiffOn.differentiableOn (by simp)
  obtain ⟨δ, i, v, hδ, hδr, hv, hvt, hfix, hproj⟩ :=
    exists_chart_lift_across_puncture_bd7 hπ hπclosed (hG.continuousAt.comp hscont) hr
      hU.continuousOn (fun z hz => huπ (hgood hz)) W hW hdisj hcover e
      (fun y => e y y.val) R hsrc hcoord htgt hdiff
  let D := V ∩ (d.source ∩ d ⁻¹' (fun w : ℂ => w - a) ⁻¹' ball 0 δ)
  have hDo : IsOpen D := hV.inter (d.isOpen_inter_preimage (isOpen_ball.preimage
    (continuous_id.sub continuous_const)))
  have ht0 : t x = 0 := sub_self a
  have hxD : x ∈ D := ⟨hxV, hxs, ht0.symm ▸ mem_ball_self hδ⟩
  have hst (y : T) (hy : y ∈ D) : s (t y) = y := by
    change d.symm ((d y - a) + a) = y
    rw [sub_add_cancel]
    exact d.left_inv hy.2.1
  have htneq (y : T) (hy : y ∈ D) (hne : y ≠ x) : t y ≠ 0 := by
    intro h
    exact hne ((hst y hy).symm.trans (h ▸ hs0))
  have hth : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞ t D :=
    ((curveScalarChart_holomorphic x).mono fun _ h => h.2.1).sub contMDiffOn_const
  let L := (e i).symm ∘ v ∘ t
  have hvh : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ v (ball 0 δ) :=
    (hv.contDiffOn isOpen_ball).contMDiffOn
  have hL : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ L D :=
    (curveScalarChart_symm_holomorphic i.val).comp (hvh.comp hth (fun _ h => h.2.2))
      (fun _ h => hvt h.2.2)
  refine ⟨D, L, hDo, hxD, fun _ h => (Set.ext_iff.mp hVB _).mp ⟨h.1.1, h.2⟩, hL, ?_, ?_⟩
  · intro y hy
    have hne : y ≠ x := fun h => hy.2 (h.symm ▸ hx)
    exact (hfix ⟨hy.1.2.2, htneq y hy.1 hne⟩).trans (congrArg u (hst y hy.1))
  · intro y hy
    exact (hproj hy.2.2).trans (congrArg G (hst y hy))


section Projective

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.GAGA.H0S
open TopologicalSpace

local instance curvePointTopology {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance curvePointCharts {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance curvePointManifold {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

private theorem curveGlobal_points_holomorphic
    {Y X : Scheme.{0}} {fY : Y ⟶ Spec (.of ℂ)} {fX : X ⟶ Spec (.of ℂ)}
    (ρ : Y ⟶ X) (hρ : ρ ≫ fX = fY) (d n : ℕ)
    [SmoothOfRelativeDimension d fY] [SmoothOfRelativeDimension n fX] :
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (schemeComplexPointMap fY fX ρ hρ) := by
  cases hρ
  exact schemeComplexPointMap_contMDiff fX ρ d n ∞

/-- Every nonconstant holomorphic map from a compact connected curve to the smooth
projective target factors through the smooth projective normalization of its exact image. -/
theorem exists_holomorphic_lift_to_normalization_of_compactCurve_bd7
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [CompactSpace T] [ConnectedSpace T] (g : T → SchemeComplexPoint f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hnc : ∃ x y, g x ≠ g y) :
    ∃ (I : X.IdealSheafData) (_ : IsIntegral I.subscheme)
      (_ : ClosedProjectiveEmbedding (I.subschemeι ≫ f)),
      (letI := schemeFunctionFieldAlgebra (I.subschemeι ≫ f)
       Algebra.trdeg ℂ I.subscheme.functionField = 1) ∧
      range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) = range g ∧
      ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ I.subscheme) (_ : IsFinite ρ)
        (_ : SmoothOfRelativeDimension 1 (ρ ≫ (I.subschemeι ≫ f)))
        (_ : ClosedProjectiveEmbedding (ρ ≫ (I.subschemeι ≫ f))),
        (∃ j : originalNormalizationScheme I.subscheme ≅ Y,
          j.hom ≫ ρ = originalNormalizationMap I.subscheme) ∧
        ∃ L : T → SchemeComplexPoint (ρ ≫ (I.subschemeι ≫ f)),
          ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ L ∧
          ∀ x, schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl
            (schemeComplexPointMap (ρ ≫ (I.subschemeι ≫ f)) (I.subschemeι ≫ f) ρ rfl (L x)) =
              g x := by
  classical
  obtain ⟨I, hI, EI, himage, hdim, _⟩ := exists_smoothProjectiveCurve_over_image_bd7 f E n g hg hnc
  let := hI
  let c := I.subschemeι ≫ f
  let := EI.isSeparated
  let := EI.quasiCompact
  let := EI.locallyOfFiniteType
  obtain ⟨Y, hY, ρ, hρ, hsm, EY, hnorm, U, hU, hIso⟩ :=
    exists_canonical_smoothProjective_normalization_curve_bd7 c EI hdim
  let := hY
  let := hρ
  let := hsm
  let := hIso
  let := EY.isSeparated
  let := EY.quasiCompact
  let := EY.locallyOfFiniteType
  let : CompactSpace (SchemeComplexPoint (ρ ≫ c)) := EY.analyticCompact
  let j := schemeComplexPointMap c f I.subschemeι rfl
  have hjinj : Function.Injective j := by
    intro p q h
    apply Subtype.ext
    exact (cancel_mono I.subschemeι).mp (congrArg Subtype.val h)
  have hq' (x : T) : ∃ q : SchemeComplexPoint c, j q = g x := by
    have hx : g x ∈ range j := by rw [himage]; exact mem_range_self x
    exact hx
  choose q hq using hq'
  let B : Set T := g ⁻¹' schemeNativeAlgebraicTrace f (I.subschemeι '' (U : Set I.subscheme)ᶜ)
  have hB (x : T) : x ∈ B ↔ schemeComplexPointImage c (q x) ∉ U := by
    change schemeComplexPointImage f (g x) ∈ I.subschemeι '' (U : Set I.subscheme)ᶜ ↔ _
    rw [← hq x]
    simp only [j, schemeComplexPointImage, schemeComplexPointMap, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨z, hz, he⟩
      exact I.subschemeι.isClosedEmbedding.injective he ▸ hz
    · exact fun hz => ⟨_, hz, rfl⟩
  have hBan : IsComplexAnalyticSubset (n := 1) B :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg
      (schemeNativeAlgebraicTrace_isComplexAnalyticSubset f n _
        (I.subschemeι.isClosedMap _ U.isOpen.isClosed_compl))
  have hBproper : B ≠ univ := by
    intro he
    obtain ⟨_, hp, ⟨p, rfl⟩⟩ :=
      (dense_iff_inter_open.mp (OF14.dense_range_schemeComplexPointImage c)) U U.isOpen hU
    have hjp : j p ∈ range g := by rw [← himage]; exact mem_range_self p
    obtain ⟨x, hx⟩ := hjp
    have hqx : q x = p := hjinj ((hq x).trans hx)
    exact (hB x).mp (he ▸ mem_univ x) (hqx.symm ▸ hp)
  let A : Opens T := ⟨Bᶜ, hBan.isClosed.isOpen_compl⟩
  -- The image embedding may be taken to be the one induced from the original
  -- target embedding. Rebuild it here so that projective coordinates are literal.
  let : IsClosedImmersion E.map := E.closedImmersion
  let EI' : ClosedProjectiveEmbedding c := {
    ambientDimension := E.ambientDimension
    map := I.subschemeι ≫ E.map
    closedImmersion := inferInstance
    over_base := by rw [Category.assoc, E.over_base] }
  let b' := polynomialProjStructureMap ℂ E.ambientDimension
  let P : A → SchemeComplexPoint b' :=
    fun x => schemeComplexPointMap f b' E.map E.over_base (g x.val)
  have hP : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel E.ambientDimension) ∞ P := by
    have hEP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel E.ambientDimension) ∞
        (schemeComplexPointMap f b' E.map E.over_base) := by
      exact curveGlobal_points_holomorphic E.map E.over_base n E.ambientDimension
    exact hEP.comp (hg.comp contMDiff_subtype_val)
  obtain ⟨uA, huA, huAρ⟩ := SGPT.BDivisor.BD7.exists_holomorphic_lift_of_projective_goodOpen_bd7
    c ρ EI' U P hP (fun x => q x.val) (fun x => by
      apply Subtype.ext
      have heq := congrArg Subtype.val (hq x.val)
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ E.map) heq))
    (fun x => by
      by_contra h
      exact x.property ((hB x.val).mpr h))
  have hA : (A : Set T).Nonempty := by
    by_contra h
    apply hBproper
    exact eq_univ_of_forall fun x => by
      by_contra hx
      exact h ⟨x, hx⟩
  obtain ⟨x0, hx0⟩ := hA
  let u : T → SchemeComplexPoint (ρ ≫ c) :=
    Subtype.val.extend uA (fun _ => uA ⟨x0, hx0⟩)
  have huu (x : A) : u x.val = uA x := Subtype.val_injective.extend_apply _ _ _
  have hu : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ u Bᶜ := by
    have he : (fun x : A => u x.val) = uA := funext huu
    have h : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞
        (fun x : A => u x.val) := he.symm ▸ huA
    intro x hx
    exact ((contMDiffAt_subtype_iff (U := A)).mp (h.contMDiffAt (x := ⟨x, hx⟩))).contMDiffWithinAt
  let p : SchemeComplexPoint (ρ ≫ c) → SchemeComplexPoint f :=
    j ∘ schemeComplexPointMap (ρ ≫ c) c ρ rfl
  have hp : Continuous p := by
    have hover : (ρ ≫ I.subschemeι) ≫ f = ρ ≫ c := Category.assoc _ _ _
    have heq : p = schemeComplexPointMap (ρ ≫ c) f (ρ ≫ I.subschemeι) hover := by
      funext w
      apply Subtype.ext
      exact Category.assoc _ _ _
    rw [heq]
    exact (curveGlobal_points_holomorphic (ρ ≫ I.subschemeι) hover 1 n).continuous
  have hfinite (z : SchemeComplexPoint f) : (p ⁻¹' {z}).Finite := by
    have hfin := ((ρ ≫ I.subschemeι).finite_preimage_singleton (schemeComplexPointImage f z)).preimage
      (schemeComplexPointImage_injective (ρ ≫ c)).injOn
    apply hfin.subset
    intro w hw
    have heq := congrArg (schemeComplexPointImage f) (mem_singleton_iff.mp hw)
    simpa only [p, j, schemeComplexPointImage, schemeComplexPointMap,
      Function.comp_apply, Scheme.Hom.comp_apply, mem_preimage, mem_singleton_iff] using heq
  obtain ⟨L, hL, _, hfac⟩ := exists_holomorphic_lift_of_finite_closed_curveProjection_bd7
    p hp hp.isClosedMap hfinite g hg.continuous hBan.isClosed
    (isDiscrete_proper_analyticSubset_curve_bd7 hBan hBproper) u hu (fun x hx => by
      change j (schemeComplexPointMap (ρ ≫ c) c ρ rfl (u x)) = g x
      rw [huu ⟨x, hx⟩, huAρ ⟨x, hx⟩, hq])
  exact ⟨I, hI, EI, hdim, himage, Y, hY, ρ, hρ, hsm, EY, hnorm, L, hL, congrFun hfac⟩

end Projective

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
