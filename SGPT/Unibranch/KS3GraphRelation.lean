import SGPT.Unibranch.KS3GraphBlowup
import SGPT.Foundations.Analysis.Pending.HironakaSingularSubspaceBlowupCartierRatios
import SGPT.Foundations.Analysis.Pending.HironakaG10ChowRatioGeneration
import SGPT.Foundations.Analysis.Pending.HironakaIntrinsicReducedCentreOpenPullback
import SGPT.Foundations.Analysis.Pending.HironakaIntrinsicReducedCentreIdealModel
import SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates

/-!
# Generators of the reduced ideal in a graph chart

Lane KS3 (towards Kähler preservation under blowups, `def:unibranch:L212`).  Let `C ⊆ X` be an
analytic subset of a complex space and `g` a graph chart of the reduced ideal `𝓘_C` on a local
embedding `e` (`KS3GraphBlowup.GraphChart`), with generators `G = (G_1, …, G_r)` on an open
`O` of the ambient domain.  The ideal identity of `g` says that the germs of the `G_l` generate
the ideal of germs vanishing on `C`.  In function terms:

* `exists_relation`: every holomorphic function `f` near a carrier point which vanishes on the
  carrier points over `C` is, on the carrier, a holomorphic combination `f = Σ a_l G_l`.

This is the only place where the ideal-theoretic content of the blowup enters the Kähler
construction: it relates the generators of two overlapping graph charts.

Ingredients: the model description of the reduced ideal
(`HironakaIntrinsicReducedCentreIdealModel.intrinsicReducedCentreStalkInclusion_range_model`),
its compatibility with open immersions
(`HironakaIntrinsicReducedCentreOpenPullback.openImmersion_pulled_stalkIdeal_eq`), a Hadamard
lemma for the zero plane of `O × ℂ^r` (`exists_eq_sum_zeroPlane`, from
`BlowupFlatCoordinates.exists_eq_sum_flatCoord`) and the germ calculus of
`HironakaSingularSubspaceBlowupCartierRatios`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.KS3GraphRelation

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk HironakaFiniteSectionProductGraph
  HironakaSingularSubspaceBlowupCartier HironakaSingularSubspaceBlowupCartierRatios
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback HironakaActualAnalyticSubspaceOpenRestriction
  SourceReducedComplexSpace OriginalFiniteIdealGraphChart KS3GraphBlowup ProductComplexManifold
  HironakaHolomorphicJetRankLoci

open scoped ProductComplexManifold

/-! ### Germ calculus -/

section Germs

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem germ_mul (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x (fun z => f z * g z) (hf.mul hg) =
      actualOriginalFunctionGerm x f hf * actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_mul, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

theorem germ_add (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hfg : HolomorphicAt n (fun z => f z + g z) x) :
    actualOriginalFunctionGerm x (fun z => f z + g z) hfg =
      actualOriginalFunctionGerm x f hf + actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_add, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

omit [IsComplexManifold n M] in
theorem holomorphicAt_sum {ι : Type} (s : Finset ι) (f : ι → M → ℂ) (x : M)
    (hf : ∀ i ∈ s, HolomorphicAt n (f i) x) :
    HolomorphicAt n (fun z => ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact holomorphicAt_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    exact (h1.and h2).mono fun _ h => h.1.add h.2

theorem germ_sum {ι : Type} (s : Finset ι) (f : ι → M → ℂ) (x : M)
    (hf : ∀ i, HolomorphicAt n (f i) x) :
    actualOriginalFunctionGerm x (fun z => ∑ i ∈ s, f i z) (holomorphicAt_sum s f x fun i _ => hf i) =
      ∑ i ∈ s, actualOriginalFunctionGerm x (f i) (hf i) := by
  classical
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_sum, actualOriginalFunctionGerm_chart]
  simp only [actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_sum _ _ _

theorem germ_congr (x : M) {f g : M → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (h : f =ᶠ[𝓝 x] g) : actualOriginalFunctionGerm x f hf = actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original x f g hf hg h

theorem exists_quotient_rep (C : Set M) (x : C)
    (r : ((actualSubspaceLocallyRingedSpace (n := n) C).presheaf.stalk x).carrier) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f x.val),
      ((actualSubspaceInclusion (n := n) C).stalkMap x)
        (actualOriginalFunctionGerm x.val f hf) = r := by
  obtain ⟨a, ha⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C x r
  obtain ⟨U, hxU, s, hs⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq a
  let f := sectionExtension U s
  have hf : HolomorphicAt n f x.val := sectionExtension_holomorphicAt U s x.val hxU
  have hg : actualOriginalFunctionGerm x.val f hf = a :=
    (actualOriginalFunctionGerm_eq_section U x.val hxU s f hf Filter.EventuallyEq.rfl).trans hs
  exact ⟨f, hf, (congrArg ((actualSubspaceInclusion (n := n) C).stalkMap x) hg).trans ha⟩

end Germs

/-! ### Hadamard lemma for the zero plane of a product -/

section ZeroPlane

variable {n r : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem holomorphicAt_snd_coord (l : Fin r) (q₀ : M × ComplexModel r) :
    HolomorphicAt (n + r) (fun q : M × ComplexModel r => q.2 l) q₀ := by
  refine Eventually.of_forall fun q => ?_
  have h1 : ContMDiff 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel r) ∞
      (fun q : M × ComplexModel r => q.2) := ProductComplexManifold.contMDiff_snd
  have h2 : ContMDiff 𝓘(ℂ, ComplexModel r) 𝓘(ℂ, ℂ) ∞ (fun v : ComplexModel r => v l) :=
    (EuclideanSpace.proj l : ComplexModel r →L[ℂ] ℂ).contMDiff
  exact ((h2.comp h1) q).mdifferentiableAt (by simp)

/-- **Hadamard's lemma for the zero plane** `M × {0} ⊆ M × ℂ^r`: a holomorphic germ vanishing on
the zero plane is a holomorphic combination of the fibre coordinates. -/
theorem exists_eq_sum_zeroPlane (q₀ : M × ComplexModel r) {g : M × ComplexModel r → ℂ}
    (hg : (vanishingIdeal (n := n + r) {q : M × ComplexModel r | q.2 = 0}).mem q₀ g) :
    ∃ b : Fin r → M × ComplexModel r → ℂ, (∀ l, HolomorphicAt (n + r) (b l) q₀) ∧
      g =ᶠ[𝓝 q₀] fun q => ∑ l, q.2 l * b l q := by
  classical
  by_cases h0 : q₀.2 = 0
  · -- flat chart of the zero plane at `q₀ = (p, 0)`
    obtain ⟨p, w⟩ := q₀
    simp only at h0
    subst h0
    let c := complexChartAt (n := n + r) ((p, 0) : M × ComplexModel r)
    let a := chartAt (ComplexModel n) p
    have hc (q : M × ComplexModel r) : c.val q = prodModelEquiv n r (a q.1, q.2) := by
      change prodModelEquiv n r (a q.1, (chartAt (ComplexModel r) (0 : ComplexModel r)) q.2) = _
      rw [chartAt_self_eq]
      rfl
    let Φ : LocalHolomorphicEquivAt (n := n + r)
        (chartAt (ComplexModel (n + r)) ((p, 0) : M × ComplexModel r) (p, 0)) :=
      { source := c.val.target
        target := (fun q : ComplexModel (n + r) => q + c.val (p, 0)) ⁻¹' c.val.target
        isOpen_source := c.val.open_target
        isOpen_target := c.val.open_target.preimage (continuous_id.add continuous_const)
        center_mem_source := c.val.map_source (mem_complexChartAt_source _)
        toFun := fun q => q - c.val (p, 0)
        invFun := fun q => q + c.val (p, 0)
        toFun_holomorphic := (differentiable_id.sub_const _).differentiableOn
        invFun_holomorphic := (differentiable_id.add_const _).differentiableOn
        mapsTo_toFun := fun q hq => by
          change (q - c.val (p, 0)) + c.val (p, 0) ∈ c.val.target
          simpa only [sub_add_cancel] using hq
        mapsTo_invFun := fun _ hq => hq
        left_inv := fun q _ => sub_add_cancel q _
        right_inv := fun q _ => add_sub_cancel_right q _ }
    have hflat : ∀ {y : M × ComplexModel r},
        y ∈ (chartAt (ComplexModel (n + r)) ((p, 0) : M × ComplexModel r)).source →
        chartAt (ComplexModel (n + r)) ((p, 0) : M × ComplexModel r) y ∈ Φ.source →
          (y ∈ {q : M × ComplexModel r | q.2 = 0} ↔
            Φ.toFun (chartAt (ComplexModel (n + r)) ((p, 0) : M × ComplexModel r) y) ∈
              complexCoordinatePlane (n + r) n) := by
      intro q _hq _hq'
      change q.2 = 0 ↔ c.val q - c.val (p, 0) ∈ complexCoordinatePlane (n + r) n
      rw [hc q, hc (p, 0), ← map_sub]
      change q.2 = 0 ↔ prodModelEquiv n r (a q.1 - a p, q.2 - 0) ∈ complexCoordinatePlane (n + r) n
      rw [sub_zero, prodModelEquiv_mem_complexCoordinatePlane_iff]
    have hy : ((p, 0) : M × ComplexModel r) ∈ BlowupFlatCoordinates.flatDomain Φ :=
      BlowupFlatCoordinates.mem_flatDomain_self Φ
    obtain ⟨b', hb'0, hb'h, hb'eq⟩ :=
      BlowupFlatCoordinates.exists_eq_sum_flatCoord Φ (Subset.rfl) hflat hy hg
    refine ⟨fun l => b' (Fin.natAdd n l), fun l => hb'h _, ?_⟩
    filter_upwards [hb'eq] with q hq
    rw [hq]
    have hcoord (i : Fin (n + r)) :
        BlowupFlatCoordinates.flatCoord Φ i q =
          prodModelEquiv n r (a q.1 - a p, q.2) i := by
      change (c.val q - c.val (p, 0)) i = _
      rw [hc q, hc (p, 0), ← map_sub]
      simp only [Prod.mk_sub_mk, sub_zero]
    rw [Fin.sum_univ_add]
    have hleft : ∑ i : Fin n, b' (Fin.castAdd r i) q *
        BlowupFlatCoordinates.flatCoord Φ (Fin.castAdd r i) q = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hb'0 (Fin.castAdd r i) (by simp)]
      simp
    rw [hleft, zero_add]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcoord, mul_comm]
    congr 1
    simp [prodModelEquiv]
  · obtain ⟨l₀, hl₀⟩ : ∃ l, q₀.2 l ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by ext l; simpa using h l)
    have hs := holomorphicAt_snd_coord (n := n) l₀ q₀
    have hinv := BlowupFlatCoordinates.HolomorphicAt.inv hs hl₀
    refine ⟨fun l q => if l = l₀ then g q * (q.2 l₀)⁻¹ else 0, fun l => ?_, ?_⟩
    · by_cases hl : l = l₀
      · simp only [hl, if_true]
        exact hg.1.mul hinv
      · simp only [hl, if_false]
        exact holomorphicAt_const 0
    · have hne : ∀ᶠ q in 𝓝 q₀, q.2 l₀ ≠ 0 :=
        hs.continuousAt.eventually (isOpen_ne.mem_nhds hl₀)
      filter_upwards [hne] with q hq
      rw [Finset.sum_eq_single l₀]
      · simp only [if_true]
        field_simp
      · intro l _ hl
        simp [hl]
      · simp

end ZeroPlane

/-! ### Relations in a graph chart -/

section Relation

variable {X : SourceReducedComplexSpace} (Cset : Set X.obj.left)

/-- The reduced ideal of `C` and its inclusion. -/
abbrev idealB : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf) :=
  intrinsicReducedCentreIdealModule X.obj.left Cset

abbrev idealb : idealB Cset ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf) :=
  intrinsicReducedCentreIdealInclusion X.obj.left Cset

variable {Cset} {e : LocalEmbedding X} (g : GraphChart (idealB Cset) (idealb Cset) e)

/-- The generators are holomorphic. -/
theorem holomorphicAt_gen (l : Fin g.r) (u : g.O) :
    HolomorphicAt e.dim (fun v : g.O => g.G v l) u := by
  refine Eventually.of_forall fun v => ?_
  have h2 : ContMDiff 𝓘(ℂ, ComplexModel g.r) 𝓘(ℂ, ℂ) ∞ (fun w : ComplexModel g.r => w l) :=
    (EuclideanSpace.proj l : ComplexModel g.r →L[ℂ] ℂ).contMDiff
  exact ((h2.comp g.hG) v).mdifferentiableAt (by simp)

set_option maxHeartbeats 1000000 in
/-- **Relations in a graph chart.**  A holomorphic function on the chart domain which vanishes
on the carrier points over `C` is, near every carrier point, a holomorphic combination of the
generators along the carrier. -/
theorem exists_relation (y : ((Subtype.val : g.O → e.ambient) ⁻¹' e.carrier))
    (f : g.O → ℂ) (hf : HolomorphicAt e.dim f y.val)
    (hf0 : ∀ᶠ u in 𝓝 y.val, ∀ h : u.val ∈ e.carrier, e.toPoint ⟨u.val, h⟩ ∈ Cset → f u = 0) :
    ∃ a : Fin g.r → g.O → ℂ, (∀ l, HolomorphicAt e.dim (a l) y.val) ∧
      ∀ᶠ u in 𝓝 y.val, u.val ∈ e.carrier → f u = ∑ l, a l u * g.G u l := by
  classical
  let S : Set g.O := (Subtype.val : g.O → e.ambient) ⁻¹' e.carrier
  let T : Set g.O := {u | ∃ h : u.val ∈ e.carrier, e.toPoint ⟨u.val, h⟩ ∈ Cset}
  have hTS : T ⊆ S := fun u hu => hu.1
  let inclS := (actualSubspaceInclusion (n := e.dim) S).stalkMap y
  -- `f` lies in the vanishing ideal of `T`
  have h1 : (vanishingIdeal (n := e.dim) T).mem y.val f :=
    ⟨hf, hf0.mono fun u hu hT => hu hT.1 hT.2⟩
  have h2 := (actualOriginalGerm_mem_vanishingIdeal_iff T y.val f hf).mpr h1
  have h3 : inclS (actualOriginalFunctionGerm y.val f hf) ∈
      Ideal.map inclS.hom (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim) T) y.val) :=
    Ideal.mem_map_of_mem _ h2
  rw [← intrinsicReducedCentreStalkInclusion_range_model hTS y] at h3
  -- the reduced ideal of `C` pulled back along the chart
  let jS : actualSubspaceLocallyRingedSpace (n := e.dim) S ⟶ X.obj.left :=
    actualOpenSubspaceMap (n := e.dim) e.carrier g.O ≫ e.map
  have hjS : LocallyRingedSpace.IsOpenImmersion jS := by
    let := e.isOpenImmersion
    infer_instance
  have hset : jS.base ⁻¹' Cset = (Subtype.val : S → g.O) ⁻¹' T := by
    ext u
    constructor
    · intro hu
      exact ⟨u.property, hu⟩
    · rintro ⟨_, hu⟩
      exact hu
  have h4 : inclS (actualOriginalFunctionGerm y.val f hf) ∈
      nativePulledIdealStalkIdeal jS (idealB Cset) (idealb Cset) y := by
    rw [openImmersion_pulled_stalkIdeal_eq jS Cset y, hset]
    exact h3
  rw [← g.hJS y] at h4
  -- the graph map pulls the ideal of the zero plane into the span of the generators
  let J : Ideal ((actualSubspaceLocallyRingedSpace (n := e.dim) S).presheaf.stalk y).carrier :=
    Ideal.span (Set.range fun l : Fin g.r =>
      inclS (actualOriginalFunctionGerm y.val (fun v : g.O => g.G v l) (holomorphicAt_gen g l y.val)))
  let φ : g.O → g.O × ComplexModel g.r := fun o => (o, g.G o)
  have hφ : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel (e.dim + g.r)) ∞ φ :=
    contMDiff_prodMk contMDiff_id g.hG
  have hφC : ∀ x ∈ S, φ x ∈ graph e g.O g.G := fun x hx => ⟨hx, rfl⟩
  have hstalk : ∀ (ψ : g.O × ComplexModel g.r → ℂ) (hψ : HolomorphicAt (e.dim + g.r) ψ (φ y.val)),
      (((productGraphIso S g.G g.hG).hom ≫
        actualSubspaceInclusion (n := e.dim + g.r) (graph e g.O g.G)).stalkMap y)
          (actualOriginalFunctionGerm (φ y.val) ψ hψ) =
        inclS (actualOriginalFunctionGerm y.val (ψ ∘ φ)
          (hψ.comp_contMDiff (Eventually.of_forall fun _ => hφ.contMDiffAt))) := by
    intro ψ hψ
    have hsq := ConcreteCategory.congr_hom
      (actualSubspaceRingedMap_stalk_square hφ hφC y) (actualOriginalFunctionGerm (φ y.val) ψ hψ)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hsq
    have hpull := HironakaG10ChowRatioGeneration.stalkMap_originalGerm hφ y.val ψ hψ
    rw [LocallyRingedSpace.stalkMap_comp, ConcreteCategory.comp_apply]
    refine hsq.trans ?_
    change inclS ((ChartedSpace.locallyRingedSpaceMap φ hφ).stalkMap y.val
      (actualOriginalFunctionGerm (φ y.val) ψ hψ)) = _
    rw [hpull]
  have hle : Ideal.map (((productGraphIso S g.G g.hG).hom ≫
      actualSubspaceInclusion (n := e.dim + g.r) (graph e g.O g.G)).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim + g.r) (zeroPlane g.O g.r))
          (φ y.val)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    unfold actualWholeSheafStalkIdeal
    rw [Ideal.span_le]
    rintro _ ⟨ψ, hψ, hψ0, rfl⟩
    obtain ⟨bψ, hbψ, hbψeq⟩ := exists_eq_sum_zeroPlane (n := e.dim) (φ y.val) hψ0
    change (((productGraphIso S g.G g.hG).hom ≫
      actualSubspaceInclusion (n := e.dim + g.r) (graph e g.O g.G)).stalkMap y)
        (actualOriginalFunctionGerm (φ y.val) ψ hψ) ∈ J
    rw [hstalk]
    have hcomp : ψ ∘ φ =ᶠ[𝓝 y.val] fun v => ∑ l, g.G v l * (bψ l ∘ φ) v := by
      have ht : Tendsto φ (𝓝 y.val) (𝓝 (φ y.val)) := hφ.continuous.continuousAt.tendsto
      exact ht.eventually hbψeq
    have hbφ : ∀ l, HolomorphicAt e.dim (bψ l ∘ φ) y.val := fun l =>
      (hbψ l).comp_contMDiff (Eventually.of_forall fun _ => hφ.contMDiffAt)
    have hterm : ∀ l : Fin g.r,
        HolomorphicAt e.dim (fun v => g.G v l * (bψ l ∘ φ) v) y.val :=
      fun l => (holomorphicAt_gen g l y.val).mul (hbφ l)
    rw [germ_congr y.val _ (holomorphicAt_sum Finset.univ _ y.val fun l _ => hterm l) hcomp,
      germ_sum Finset.univ _ y.val hterm, map_sum]
    apply Ideal.sum_mem
    intro l _
    rw [germ_mul y.val _ _ (holomorphicAt_gen g l y.val) (hbφ l), map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have h5 := hle h4
  -- coefficients
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp h5
  choose a ha hac using fun l => exists_quotient_rep S y (c l)
  refine ⟨a, ha, ?_⟩
  have hterm : ∀ l : Fin g.r,
      HolomorphicAt e.dim (fun v => a l v * g.G v l) y.val :=
    fun l => (ha l).mul (holomorphicAt_gen g l y.val)
  have hgerm : inclS (actualOriginalFunctionGerm y.val (fun v => ∑ l, a l v * g.G v l)
      (holomorphicAt_sum Finset.univ _ y.val fun l _ => hterm l)) =
      inclS (actualOriginalFunctionGerm y.val f hf) := by
    rw [germ_sum Finset.univ _ y.val hterm, map_sum, ← hc]
    apply Finset.sum_congr rfl
    intro l _
    have hac' : inclS (actualOriginalFunctionGerm y.val (a l) (ha l)) = c l := hac l
    rw [germ_mul y.val _ _ (ha l) (holomorphicAt_gen g l y.val), map_mul, hac']
  have hev := (actual_quotient_germ_eq_iff S y _ f _ hf).mp hgerm
  exact hev.mono fun u hu huS => (hu huS).symm

end Relation

end SGPT.Unibranch.KS3GraphRelation
