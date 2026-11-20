import SGPT.Unibranch.OriginalFiniteIdealGraphDensity
import SGPT.Unibranch.EmbeddedIdealBlowupGlobalUniversal
import SGPT.Unibranch.EmbeddedIdealBlowupGlobalCartier
import SGPT.Unibranch.EmbeddedIdealBlowupOriginalObject
import SGPT.Unibranch.RIsoAModification
import SGPT.Foundations.Analysis.Pending.HironakaProductZeroPlaneBlowup

/-!
# Graph charts of an ideal blowup

Lane KS3 (towards Kähler preservation under blowups, `def:unibranch:L212`).  Let `p : Y → X` be
the blowup of a complex space `X` along a coherent ideal `B ⊆ 𝒪_X` of finite type
(`IsIdealBlowup p B b`).  Near every point of every local embedding `e : V ↪ Ω ⊆ ℂ^N` of `X`,
finitely many generators `G = (G_1, …, G_r)` of `B` give the graph `Γ ⊆ O × ℂ^r` of
`G|_{V ∩ O}`, and the blowup of `O × ℂ^r` along the zero plane `O × {0}` restricts to the blowup
of `Γ ≅ V ∩ O` along `B` (`G11`, `OriginalFiniteIdealGraphChart`).  This file packages these
*graph charts* and shows that the strict transform of every graph chart is an open piece of `Y`:

* `GraphChart B b e`: generators on an open `O` of the ambient domain of `e`, with the ideal
  identity, generic nonvanishing (density) and `r > 0`;
* `exists_graphChart`: graph charts exist at every carrier point of every local embedding;
* `exists_localOpenImmersion`: for a family of graph charts covering `X` and blowups of the
  ambient products along their zero planes, each strict transform `Γ'` maps by an open
  immersion `L` onto `p⁻¹(chart image)` with `p ∘ L = chart ∘ π|_{Γ'}`.

The proof glues the strict transforms (`EmbeddedIdealBlowupOriginalObject`, generic), uses the
universal property of the glued object (`EmbeddedIdealBlowupGlobalUniversal`,
`EmbeddedIdealBlowupGlobalCartier`) and the uniqueness of ideal blowups
(`RIsoAModification.isIdealBlowup_exists_unique_iso`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.KS3GraphBlowup

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk HironakaFiniteSectionProductGraph
  SourceReducedComplexSpace OriginalFiniteIdealGraphChart OriginalFiniteIdealGraphDensity
  HironakaActualAnalyticSubspaceOpenRestriction
  SmoothCentreModification

open scoped ProductComplexManifold

variable {X : SourceReducedComplexSpace}

/-- The graph of `G` over the carrier points of `O`. -/
abbrev graph (e : LocalEmbedding X) (O : Opens e.ambient) {r : ℕ} (G : O → ComplexModel r) :
    Set (O × ComplexModel r) :=
  productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G

/-- The zero plane `O × {0}`. -/
abbrev zeroPlane (T : Type) (r : ℕ) : Set (T × ComplexModel r) :=
  {q : T × ComplexModel r | q.2 = 0}

variable (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

/-- **A graph chart** of the ideal `B` on a local embedding `e`: holomorphic generators
`G : O → ℂ^r` on an open subset `O` of the ambient domain, whose graph `Γ` is analytic, such that
the ideal of the zero plane restricted to `Γ` is the pull-back of `B`, with `Γ` the closure of
its points off the zero plane and `r > 0`. -/
structure GraphChart (e : LocalEmbedding X) where
  O : Opens e.ambient
  r : ℕ
  G : O → ComplexModel r
  hG : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel r) ∞ G
  hΓ : IsComplexAnalyticSubset (n := e.dim + r) (graph e O G)
  hJ : ∀ z : graph e O G,
    Ideal.map ((actualSubspaceInclusion (n := e.dim + r) (graph e O G)).stalkMap z).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim + r) (zeroPlane O r))
          z.val) =
      nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z
  hr : 0 < r
  hd : graph e O G ⊆ closure (graph e O G \ zeroPlane O r)
  hJS : ∀ y : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier),
    Ideal.map (((productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG).hom ≫
      actualSubspaceInclusion (n := e.dim + r) (graph e O G)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim + r) (zeroPlane O r))
        (((productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG).hom ≫
          actualSubspaceInclusion (n := e.dim + r) (graph e O G)).base y)) =
      nativePulledIdealStalkIdeal (actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ e.map) B b y

namespace GraphChart

variable {B b} {e : LocalEmbedding X} (g : GraphChart B b e)

/-- The graph chart as a morphism of complex spaces. -/
abbrev chart : ofClosedAnalytic (graph e g.O g.G) g.hΓ ⟶ X :=
  chartGraphMorphism e g.O g.G g.hG g.hΓ

instance chart_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion g.chart.hom.left :=
  chartGraphMap_isOpenImmersion e g.O g.G g.hG

/-- A graph point is off the zero plane exactly when the ideal is the unit ideal at its image. -/
theorem ne_zero_iff (z : graph e g.O g.G) :
    z.val.2 ≠ 0 ↔
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((chartGraphMap e g.O g.G g.hG).base z)) = ⊤ := by
  have hC : IsClosed (zeroPlane g.O g.r) := isClosed_singleton.preimage continuous_snd
  calc
    _ ↔ actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim + g.r)
        (zeroPlane g.O g.r)) z.val = ⊤ :=
      (actualWholeVanishing_eq_top_iff _ hC z.val).symm
    _ ↔ Ideal.map ((actualSubspaceInclusion (n := e.dim + g.r) (graph e g.O g.G)).stalkMap z).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim + g.r)
          (zeroPlane g.O g.r)) z.val) = ⊤ := by
      constructor
      · intro h
        rw [h, Ideal.map_top]
      · intro h
        by_contra hI
        have hlt := (Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans_lt
          (IsLocalRing.map_maximalIdeal_lt_top
            ((actualSubspaceInclusion (n := e.dim + g.r) (graph e g.O g.G)).stalkMap z).hom)
        exact hlt.ne h
    _ ↔ nativePulledIdealStalkIdeal (chartGraphMap e g.O g.G g.hG) B b z = ⊤ :=
      iff_of_eq (congrArg (fun I => I = ⊤) (g.hJ z))
    _ ↔ _ := nativePulledIdealStalkIdeal_eq_top_iff (chartGraphMap e g.O g.G g.hG) B b z

end GraphChart

/-- **Graph charts exist** at every carrier point of every local embedding. -/
theorem exists_graphChart [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left |
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (e : LocalEmbedding X) (w : e.carrier) :
    ∃ (g : GraphChart B b e) (hw : w.val ∈ g.O),
      ((⟨w.val, hw⟩ : g.O), g.G ⟨w.val, hw⟩) ∈ graph e g.O g.G := by
  obtain ⟨O, hwO, r, G, hG, hΓ, hJS, hJ, -⟩ := exists_graph_chart_on_embedding B b e w
  -- density, as in `OriginalFiniteIdealGraphDensity`
  let Γ := graph e O G
  have hC : IsClosed (zeroPlane O r) := isClosed_singleton.preimage continuous_snd
  have hiff (z : Γ) : z.val.2 ≠ 0 ↔
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((chartGraphMap e O G hG).base z)) = ⊤ := by
    calc
      _ ↔ actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim + r)
          (zeroPlane O r)) z.val = ⊤ :=
        (actualWholeVanishing_eq_top_iff _ hC z.val).symm
      _ ↔ Ideal.map ((actualSubspaceInclusion (n := e.dim + r) Γ).stalkMap z).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim + r)
            (zeroPlane O r)) z.val) = ⊤ := by
        constructor
        · intro h
          rw [h, Ideal.map_top]
        · intro h
          by_contra hI
          have hlt := (Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans_lt
            (IsLocalRing.map_maximalIdeal_lt_top
              ((actualSubspaceInclusion (n := e.dim + r) Γ).stalkMap z).hom)
          exact hlt.ne h
      _ ↔ nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z = ⊤ :=
        iff_of_eq (congrArg (fun I => I = ⊤) (hJ z))
      _ ↔ _ := nativePulledIdealStalkIdeal_eq_top_iff (chartGraphMap e O G hG) B b z
  have hd0 := hDense.preimage (chartGraphMap_isOpenImmersion e O G hG).base_open.isOpenMap
  have hset : {z : Γ | LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((chartGraphMap e O G hG).base z)) = ⊤} = {z : Γ | z.val.2 ≠ 0} :=
    Set.ext fun z => (hiff z).symm
  change Dense {z : Γ | LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
    ((chartGraphMap e O G hG).base z)) = ⊤} at hd0
  rw [hset] at hd0
  have himage : (Subtype.val : Γ → O × ComplexModel r) '' {z : Γ | z.val.2 ≠ 0} =
      Γ \ zeroPlane O r := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hq, hq0⟩
      exact ⟨⟨q, hq⟩, hq0, rfl⟩
  have hd : Γ ⊆ closure (Γ \ zeroPlane O r) := by
    intro q hq
    have hqcl : (⟨q, hq⟩ : Γ) ∈ closure {z : Γ | z.val.2 ≠ 0} := by
      rw [hd0.closure_eq]
      trivial
    have ha := mem_closure_image continuous_subtype_val.continuousAt hqcl
    rw [himage] at ha
    exact ha
  have hwΓ : ((⟨w.val, hwO⟩ : O), G ⟨w.val, hwO⟩) ∈ Γ := ⟨w.property, rfl⟩
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    have hsub : Subsingleton (ComplexModel r) := hr0.symm ▸ inferInstance
    have he : Γ \ zeroPlane O r = ∅ := by
      ext q
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
        not_not]
      exact fun _ => @Subsingleton.elim (ComplexModel r) hsub q.2 0
    have hc := hd hwΓ
    rw [he, closure_empty] at hc
    exact hc
  exact ⟨⟨O, r, G, hG, hΓ, hJ, hr, hd, hJS⟩, hwO, hwΓ⟩

/-! ### Local open immersions into the blowup -/

/-- A blowup of the ambient product of a graph chart along its zero plane. -/
structure ZeroPlaneBlowup {e : LocalEmbedding X} (g : GraphChart B b e) where
  space : Type
  [top : TopologicalSpace space]
  [charted : ChartedSpace (ComplexModel (e.dim + g.r)) space]
  [complex : IsComplexManifold (e.dim + g.r) space]
  proj : space → g.O × ComplexModel g.r
  isBlowup : IsBlowupAlong (e.dim + g.r) (zeroPlane g.O g.r) proj

attribute [instance] ZeroPlaneBlowup.top ZeroPlaneBlowup.charted ZeroPlaneBlowup.complex

theorem nonempty_zeroPlaneBlowup {e : LocalEmbedding X} (g : GraphChart B b e) :
    Nonempty (ZeroPlaneBlowup B b g) := by
  obtain ⟨Z, tZ, aZ, cZ, π, hπ⟩ :=
    HironakaProductZeroPlaneBlowup.exists_product_zero_plane_blowup
      (n := e.dim) (M := g.O) g.hr
  exact ⟨@ZeroPlaneBlowup.mk _ B b e g Z tZ aZ cZ π hπ⟩

/-- A covering family of graph charts with zero-plane blowups. -/
structure GraphFamily where
  /-- the local embedding at each point -/
  emb : X.obj.left → LocalEmbedding X
  /-- the graph chart at each point -/
  chart : ∀ x, GraphChart B b (emb x)
  /-- the blowup of the ambient product -/
  blowup : ∀ x, ZeroPlaneBlowup B b (chart x)
  /-- a graph point over `x` -/
  point : ∀ x, graph (emb x) (chart x).O (chart x).G
  point_over : ∀ x, (chartGraphMap (emb x) (chart x).O (chart x).G (chart x).hG).base (point x) = x

namespace GraphFamily

variable {B b} (F : GraphFamily B b)

/-- The strict transform as a complex space. -/
abbrev localSpace (x : X.obj.left) : SourceReducedComplexSpace :=
  EmbeddedIdealBlowupOverlap.localSpace (n := fun x => (F.emb x).dim + (F.chart x).r)
    (M := fun x => (F.chart x).O × ComplexModel (F.chart x).r)
    (Y := fun x => (F.blowup x).space)
    (C := fun x => zeroPlane (F.chart x).O (F.chart x).r)
    (W := fun x => graph (F.emb x) (F.chart x).O (F.chart x).G)
    (π := fun x => (F.blowup x).proj)
    (fun x => (F.chart x).hΓ) (fun x => (F.blowup x).isBlowup) x

end GraphFamily

/-- Graph families exist (choice of a graph chart at every point of every given family of local
embeddings). -/
theorem nonempty_graphFamily [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left |
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (emb : X.obj.left → LocalEmbedding X) (hemb : ∀ x, x ∈ range (emb x).toPoint) :
    ∃ F : GraphFamily B b, F.emb = emb := by
  choose w hw using hemb
  choose g hgw hgΓ using fun x => exists_graphChart B b hDense (emb x) (w x)
  refine ⟨{ emb := emb
            chart := g
            blowup := fun x => Classical.choice (nonempty_zeroPlaneBlowup B b (g x))
            point := fun x => ⟨_, hgΓ x⟩
            point_over := fun x => ?_ }, rfl⟩
  rw [chartGraphMap_base]
  exact hw x

/-- **The strict transforms of a graph family are open pieces of the ideal blowup.** -/
theorem exists_localOpenImmersion {Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsIdealBlowup p B b) (F : GraphFamily B b) (x : X.obj.left) :
    ∃ L : F.localSpace x ⟶ Y,
      L ≫ p = EmbeddedBlowup.strictTransformMorphism (F.blowup x).isBlowup (F.chart x).hΓ ≫
        (F.chart x).chart ∧
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
      range L.hom.left.base = p.hom.left.base ⁻¹' range (F.chart x).chart.hom.left.base := by
  classical
  let hW := fun x => (F.chart x).hΓ
  let hπ := fun x => (F.blowup x).isBlowup
  let J := fun x => (F.chart x).chart
  have hJopen : ∀ x, LocallyRingedSpace.IsOpenImmersion (J x).hom.left :=
    fun x => (F.chart x).chart_isOpenImmersion
  have hd := fun x => (F.chart x).hd
  have hJ := fun x => (F.chart x).hJ
  have hcover : ∀ x : X.obj.left, ∃ (i : X.obj.left)
      (w : graph (F.emb i) (F.chart i).O (F.chart i).G), (J i).hom.left.base w = x :=
    fun x => ⟨x, F.point x, F.point_over x⟩
  let S := EmbeddedIdealBlowupOriginalObject.sourceObject hW hπ J B b hd hJ hcover
  let q := EmbeddedIdealBlowupOriginalObject.projectionMorphism hW hπ J B b hd hJ hcover
  have hq : IsIdealBlowup q B b := by
    refine ⟨EmbeddedIdealBlowupGlobalCartier.projection_ideal_exists_locallyFreeData hW hπ J B b
      hd hJ, ?_⟩
    intro A G hG
    obtain ⟨c, hc, huniq⟩ := hG
    let : c.IsLocallyFreeData := hc
    let : ∀ t, Unique (c.generators t).I := fun t => Classical.choice (huniq t)
    exact EmbeddedIdealBlowupGlobalUniversal.exists_unique_lift_of_locallyFreeData hW hπ J B b hd hJ
      hcover A G c
  obtain ⟨β, hβ, -⟩ := RIsoAModification.isIdealBlowup_exists_unique_iso hq hp
  let L := EmbeddedIdealBlowupOriginalObject.localMorphism hW hπ J B b hd hJ hcover x ≫ β.hom
  have hβopen : LocallyRingedSpace.IsOpenImmersion β.hom.hom.left := by
    have : IsIso β.hom.hom.left := by
      change IsIso (isoLeft β).hom
      infer_instance
    infer_instance
  refine ⟨L, ?_, ?_, ?_⟩
  · change (EmbeddedIdealBlowupOriginalObject.localMorphism hW hπ J B b hd hJ hcover x ≫ β.hom) ≫ p = _
    rw [Category.assoc, hβ]
    exact EmbeddedIdealBlowupOriginalObject.localMorphism_projection hW hπ J B b hd hJ hcover x
  · change LocallyRingedSpace.IsOpenImmersion
      ((EmbeddedIdealBlowupOriginalObject.localMorphism hW hπ J B b hd hJ hcover x).hom.left ≫
        β.hom.hom.left)
    infer_instance
  · have hrange := EmbeddedIdealBlowupObjectGluing.preimage_chart_range hW hπ J B b hd hJ x
    have hpb : ∀ s, p.hom.left.base (β.hom.hom.left.base s) = q.hom.left.base s := by
      intro s
      exact congrArg (fun k : S ⟶ X => k.hom.left.base s) hβ
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      show p.hom.left.base (β.hom.hom.left.base
        ((EmbeddedIdealBlowupOriginalObject.localMorphism hW hπ J B b hd hJ hcover x).hom.left.base
          s)) ∈ range (F.chart x).chart.hom.left.base
      rw [hpb]
      have : (EmbeddedIdealBlowupOriginalObject.localMorphism hW hπ J B b hd hJ hcover x).hom.left.base
          s ∈ range (EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ x).base :=
        ⟨s, rfl⟩
      rw [← hrange] at this
      exact this
    · intro hy
      let s := β.inv.hom.left.base y
      have hsy : β.hom.hom.left.base s = y := by
        change (β.inv ≫ β.hom).hom.left.base y = y
        rw [β.inv_hom_id]
        rfl
      have hs : s ∈ (EmbeddedIdealBlowupObjectGluing.projection hW hπ J B b hd hJ).base ⁻¹'
          range (J x).hom.left.base := by
        show q.hom.left.base s ∈ range (J x).hom.left.base
        rw [← hpb, hsy]
        exact hy
      rw [hrange] at hs
      obtain ⟨t, ht⟩ := hs
      refine ⟨t, ?_⟩
      change β.hom.hom.left.base
        ((EmbeddedIdealBlowupObjectGluing.inclusion hW hπ J B b hd hJ x).base t) = y
      rw [ht, hsy]

end SGPT.Unibranch.KS3GraphBlowup
