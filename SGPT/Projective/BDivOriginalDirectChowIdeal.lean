import SGPT.Foundations.Schemes.LineSectionZeroSubscheme
import SGPT.Projective.BDivOriginalIdealStalk
import SGPT.GAGA.ChowBlImage
import SGPT.NAPotential.FSPosSections
import SGPT.Projective.NativeVanishingStalkRadical
import SGPT.Projective.OriginalComplexPointClosedFactor
import SGPT.Okounkov.SchemeNativeAnalyticSubset
import SGPT.Okounkov.FlagValuationSchemeChowFunctions
import SGPT.Okounkov.SchemeNativeStalkFlatness
import SGPT.PSH.BookRestrictionIdeal

/-! The original projective homogeneous sections cut out the reduced
algebraic model of the analytic set and produce its actual vanishing stalks. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MvPolynomial
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S SGPT.GAGA.ChowBl
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.IdealRestriction
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

local instance chowStalkTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance chowStalkCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance chowStalkManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

section Original
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {μ : Type} [Fintype μ]
    (P : μ → MvPolynomial (Fin (E.ambientDimension+1)) ℂ)
    (C : Set (SchemeComplexPoint f))
    (hgen : (coneIdeal ((projectivePoint f E n) '' C)).GeneratedOn
      (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace E.ambientDimension))
      (fun k => SGPT.GAGA.PN.polyTuple (P k)))
    (p : SchemeComplexPoint f) (i : Fin (E.ambientDimension+1))
    (hp : schemeComplexPointImage f p ∈ coordOpen E i)
include hgen

/-- The FULL native graph vanishing ideal is the extension of the literal
ORIGINAL coefficient stalk span, via the ACTUAL original stalk map. -/
theorem directChow_vanishingStalk_eq_coefficientSpan_map :
    stalkIdeal (vanishingIdeal (n := n) C) p =
      (Ideal.span (range fun k => X.presheaf.germ (coordOpen E i)
        (schemeComplexPointImage f p) hp (polyCoef E i (P k)))).map (schemeNativeStalkGerm f n p) := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let e : μ ≃ Fin (Fintype.card μ) := Fintype.equivFin μ
  let Q := fun j => P (e.symm j)
  have hgenQ : (coneIdeal ((projectivePoint f E n) '' C)).GeneratedOn
      (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace E.ambientDimension))
      (fun j => SGPT.GAGA.PN.polyTuple (Q j)) := by
    apply hgen.of_generators
    · exact fun j b => hgen.1 (e.symm j) b
    · exact fun y hy j => hgen.gen_mem hy (e.symm j)
    · intro y hy j
      have hh := SGPT.GAGA.Core.isCombinationAt_gen (fun a => SGPT.GAGA.PN.polyTuple (Q a)) y (e j)
      simpa only [Q, e.symm_apply_apply] using hh
  have hΨ := isHolomorphicEmbedding_projectivePoint f E n
  have hpi : projectivePoint f E n p ∈ (affineChart i).source :=
    (projectivePoint_mem_source_iff f E n i p).mpr hp
  have hs := stalkIdeal_eq_span (vanishingIdeal (n := n) C)
    (fun k => genFun (projectivePoint f E n) i (Q k))
    (fun k => holomorphicAt_genFun hΨ hpi (Q k))
    (fun g => vanishingIdeal_mem_iff_isInSpanAt_genFun hΨ hgenQ hpi g)
  rw [hs, Ideal.map_span, ← range_comp]
  apply congrArg Ideal.span
  ext γ
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨e.symm j,schemeNativeStalkGerm_polyCoef f E n i (P (e.symm j)) p hp⟩
  · rintro ⟨k,rfl⟩
    refine ⟨e k,?_⟩
    simpa only [Q,e.symm_apply_apply,Function.comp_apply] using
      (schemeNativeStalkGerm_polyCoef f E n i (P k) p hp).symm


end Original

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

namespace SGPT.Projective.BDivNov16
open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes TopologicalSpace IsLocalRing
open scoped Topology Manifold ContDiff
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult
open SGPT.PSH.IdealRestriction
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
    [SmoothOfRelativeDimension (m+1) f] [IsSeparated f] [QuasiCompact f]
local instance analyticIntegralTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance analyticIntegralCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance analyticIntegralManifold : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)
open SGPT.NAPotential.FSPos SGPT.GAGA.ChowBl SGPT.Projective.ComplexProjectiveSpace

private theorem analyticRegular_nativeVanishingStalk_eval_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (C : Set M) (p : M) (hp : p ∈ C)
    (γ : NativeHolGerm n M p) (hγ : γ ∈ stalkIdeal (vanishingIdeal (n := n) C) p) :
    NativeHolGerm.eval γ=0 := by
  obtain ⟨g,hg,rfl⟩ := NativeHolGerm.exists_eq_mk γ
  have hcomb := isInSpanAt_of_mk_mem_spanGerms hg hγ
  obtain ⟨_,N,s,a,hs,_ha,heq⟩ := hcomb
  have hzero : ∀ᶠ y in 𝓝 p,y∈C → g y=0 := by
    filter_upwards [heq,eventually_all.mpr (fun i => (hs i).2)] with y hy hs' hyC
    rw [hy]
    exact Finset.sum_eq_zero fun i _ => by rw [hs' i hyC,mul_zero]
  rw [NativeHolGerm.eval_mk]
  exact hzero.self_of_nhds hp


private theorem directChow_stalkIdeal_radical {Y : Scheme.{0}}
    (D : Y.IdealSheafData) (x : Y) :
    D.radical.stalkIdeal x = (D.stalkIdeal x).radical := by
  obtain ⟨U, hx⟩ := SGPT.NAPotential.Berkovich.exists_affineOpen_mem x
  rw [D.radical.stalkIdeal_eq_affine x U hx, D.stalkIdeal_eq_affine x U hx]
  change Ideal.map _ (D.ideal U).radical = (Ideal.map _ (D.ideal U)).radical
  let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨x, hx⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.map_radical (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Y.presheaf.stalk x) _

private theorem directChow_mem_support_iff {Y : Scheme.{0}}
    (D : Y.IdealSheafData) (x : Y) :
    x ∈ D.support ↔ D.stalkIdeal x ≤ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
  obtain ⟨U, hx⟩ := SGPT.NAPotential.Berkovich.exists_affineOpen_mem x
  rw [D.mem_support_iff_of_mem hx, Scheme.mem_zeroLocus_iff, D.stalkIdeal_eq_affine x U hx,
    Ideal.map_le_iff_le_comap]
  constructor
  · intro h r hr
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => h r hr ((Scheme.mem_basicOpen Y r x hx).mpr hu)
  · intro h r hr hx'
    have hmem := h hr
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    exact hmem ((Scheme.mem_basicOpen Y r x hx).mp hx')

/-- Direct homogeneous equations on the original scheme. The original
sections of the hyperplane power give the complete native vanishing stalks. -/
theorem exists_original_reduced_analytic_ideal_direct
    (EX : ClosedProjectiveEmbedding f) (C : Set (SchemeComplexPoint f))
    (hC : IsComplexAnalyticSubset (n := m+1) C) :
    ∃ I : X.IdealSheafData,I.radical=I ∧ IsReduced I.subscheme ∧
      Set.range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl)=C ∧
      Function.Injective (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) ∧
      (∀ z : I.subscheme,Function.Surjective (I.subschemeι.stalkMap z).hom ∧
        RingHom.ker (I.subschemeι.stalkMap z).hom=I.stalkIdeal (I.subschemeι z)) ∧
      ∀ p : SchemeComplexPoint f,
        Ideal.map (schemeNativeStalkGerm f (m+1) p)
          (I.stalkIdeal (schemeComplexPointImage f p)) =
            stalkIdeal (vanishingIdeal (n := m+1) C) p := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := EX.analyticCompact
  obtain ⟨d, hd⟩ := chow_image (isHolomorphicEmbedding_projectivePoint f EX (m+1)) hC
  obtain ⟨μ, hμ, P, hP, hgen, _⟩ := hd d le_rfl
  let := hμ
  let a := (hyperplaneAtlas EX).tensorPower d
  let K (j : μ) := sectionZeroIdealSheaf a (polySection EX (P j) (hP j))
  let D : X.IdealSheafData := ⨆ j, K j
  have hD (p : SchemeComplexPoint f) :
      (D.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f (m+1) p) =
        stalkIdeal (vanishingIdeal (n := m+1) C) p := by
    let i := frameIndex f EX p
    let x := schemeComplexPointImage f p
    have hx : x ∈ coordOpen EX i := mem_coordOpen_frameIndex f EX p
    let U : X.affineOpens := ⟨coordOpen EX i, isAffineOpen_coordOpen EX i⟩
    have hK (j : μ) : (K j).stalkIdeal x =
        Ideal.span {X.presheaf.germ (coordOpen EX i) x hx (polyCoef EX i (P j))} := by
      rw [(K j).stalkIdeal_eq_affine x U hx]
      have hz : (K j).ideal U =
          Ideal.span {algCoef ((hyperplaneAtlas EX).frame i) d
            (polySection EX (P j) (hP j))} :=
        sectionZeroIdeal_eq_span_frame (polySection EX (P j) (hP j))
          (a.frame i) (𝟙 (a.opens i))
      rw [hz, Ideal.map_span, Set.image_singleton, algCoef_polySection]
    rw [directChow_vanishingStalk_eq_coefficientSpan_map f (m+1) EX P C hgen p i hx]
    apply congrArg (Ideal.map (schemeNativeStalkGerm f (m+1) p))
    have hsum : D.stalkIdeal x = ⨆ j, (K j).stalkIdeal x := by
      rw [D.stalkIdeal_eq_affine x U hx]
      simp only [D, Scheme.IdealSheafData.ideal_iSup, iSup_apply, Ideal.map_iSup,
        fun j => (K j).stalkIdeal_eq_affine x U hx]
    rw [hsum]
    simp only [hK, ← Ideal.span_iUnion]
    apply congrArg Ideal.span
    ext r
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_range]
    exact exists_congr fun j => eq_comm
  let I := D.radical
  have hrad : I.radical = I := by
    change D.radical.radical = D.radical
    apply Scheme.IdealSheafData.ext
    funext U
    exact Ideal.radical_idem (D.ideal U)
  have hfull (p : SchemeComplexPoint f) :
      (I.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f (m+1) p) =
        stalkIdeal (vanishingIdeal (n := m+1) C) p := by
    let φ := schemeNativeStalkGerm f (m+1) p
    let J := stalkIdeal (vanishingIdeal (n := m+1) C) p
    have hJ : J.IsRadical := nativeVanishingStalk_isRadical C p
    have hmap : (D.stalkIdeal (schemeComplexPointImage f p)).map φ = J := hD p
    change (D.radical.stalkIdeal _).map φ = J
    rw [directChow_stalkIdeal_radical]
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hr
      have hk' : (φ r)^k ∈ J := by
        rw [← map_pow, ← hmap]
        exact Ideal.mem_map_of_mem φ hk
      have hr' : φ r ∈ J.radical := Ideal.mem_radical_iff.mpr ⟨k, hk'⟩
      change φ r ∈ J
      simpa only [Ideal.radical_eq_iff.mpr hJ] using hr'
    · rw [← hmap]
      exact Ideal.map_mono Ideal.le_radical
  have hred : IsReduced I.subscheme := by
    refine @isReduced_of_isReduced_stalk I.subscheme ?_
    intro z
    have hq : IsReduced (X.presheaf.stalk (I.subschemeι z) ⧸
        I.stalkIdeal (I.subschemeι z)) := by
      rw [← Ideal.isRadical_iff_quotient_reduced, ← Ideal.radical_eq_iff,
        ← directChow_stalkIdeal_radical, hrad]
    let e := (Ideal.quotEquivOfEq (I.ker_stalkMap_subschemeι z).symm).trans
      (((I.subschemeι.stalkMap z).hom).quotientKerEquivOfSurjective
        (I.subschemeι.stalkMap_surjective z))
    exact isReduced_of_injective e.symm e.symm.injective
  have htrace (p : SchemeComplexPoint f) :
      schemeComplexPointImage f p ∈ I.support ↔ p ∈ C := by
    let J := stalkIdeal (vanishingIdeal (n := m+1) C) p
    let A := I.stalkIdeal (schemeComplexPointImage f p)
    have hmap : A.map (schemeNativeStalkGerm f (m+1) p) = J := hfull p
    have htop : A = ⊤ ↔ J = ⊤ := by
      constructor
      · intro h
        rw [← hmap, h, Ideal.map_top]
      · intro h
        apply (Ideal.eq_top_iff_one _).mpr
        apply (mem_ideal_iff_schemeNativeStalkGerm f (m+1) p A 1).mpr
        change _ ∈ A.map (schemeNativeStalkGerm f (m+1) p)
        rw [hmap, h]
        simp
    rw [directChow_mem_support_iff]
    constructor
    · intro h
      by_contra hp
      have hnot : A ≠ ⊤ := by
        intro ha
        change A ≤ IsLocalRing.maximalIdeal _ at h
        rw [ha] at h
        exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h)
      apply hnot
      apply htop.mpr
      have hhol : HolomorphicAt (m+1) (fun _ : SchemeComplexPoint f => (1 : ℂ)) p :=
        Filter.Eventually.of_forall fun _ => mdifferentiableAt_const
      have hout : ∀ᶠ y in 𝓝 p, y ∈ Cᶜ := hC.isClosed.isOpen_compl.mem_nhds hp
      have hmem : (vanishingIdeal (n := m+1) C).mem p (fun _ => 1) :=
        ⟨hhol, hout.mono fun _ hn hy => False.elim (hn hy)⟩
      apply (Ideal.eq_top_iff_one _).mpr
      change NativeHolGerm.mk _ hhol ∈ J
      exact mk_mem_stalkIdeal hhol hmem
    · intro hp
      apply IsLocalRing.le_maximalIdeal
      intro h
      have ht := htop.mp h
      have hmem : (1 : NativeHolGerm (m+1) (SchemeComplexPoint f) p) ∈ J := by
        rw [ht]
        simp
      have he := analyticRegular_nativeVanishingStalk_eval_zero C p hp _ hmem
      exact one_ne_zero ((map_one NativeHolGerm.eval).symm.trans he)
  refine ⟨I,hrad,hred,?_,?_,?_,hfull⟩
  · rw [closedImmersionComplexPointMap_range]
    ext p
    rw [I.range_subschemeι]
    exact htrace p
  · intro p q hpq
    apply Subtype.ext
    apply (cancel_mono I.subschemeι).mp
    exact congrArg Subtype.val hpq
  · intro z
    exact ⟨I.subschemeι.stalkMap_surjective z,I.ker_stalkMap_subschemeι z⟩

theorem exists_original_integral_ideal_of_native_irreducible_direct
    (EX : ClosedProjectiveEmbedding f) (C : Set (SchemeComplexPoint f))
    (hC : IsComplexAnalyticallyIrreducible (n := m+1) C) :
    ∃ I : X.IdealSheafData,I.radical=I ∧ IsReduced I.subscheme ∧ IsIntegral I.subscheme ∧
      Set.range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl)=C ∧
      Function.Injective (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) ∧
      (∀ z : I.subscheme,Function.Surjective (I.subschemeι.stalkMap z).hom ∧
        RingHom.ker (I.subschemeι.stalkMap z).hom=I.stalkIdeal (I.subschemeι z)) ∧
      ∀ p : SchemeComplexPoint f,
        Ideal.map (schemeNativeStalkGerm f (m+1) p)
          (I.stalkIdeal (schemeComplexPointImage f p)) =
            stalkIdeal (vanishingIdeal (n := m+1) C) p := by
  let : IsProper f := EX.isProper
  let : LocallyOfFiniteType f := inferInstance
  obtain ⟨I,hrad,hred,himage,hinj,hstalk,hfull⟩ :=
    exists_original_reduced_analytic_ideal_direct f m EX C hC.analytic
  obtain ⟨p,hp⟩ := hC.nonempty
  obtain ⟨q,_hq⟩ : p∈Set.range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) := by
    rwa [himage]
  let : Nonempty I.subscheme := ⟨schemeComplexPointImage (I.subschemeι ≫ f) q⟩
  have hsupp : {p : SchemeComplexPoint f | schemeComplexPointImage f p∈I.support}=C := by
    ext p
    change schemeComplexPointImage f p∈I.support ↔ p∈C
    rw [←himage,closedImmersionComplexPointMap_range]
    exact (Set.ext_iff.mp I.range_subschemeι _).symm
  let : LocallyOfFiniteType (I.subschemeι ≫ f) := inferInstance
  have full_of_trace (F : Set I.subscheme) (hF : IsClosed F)
      (hEq : C={p : SchemeComplexPoint f | schemeComplexPointImage f p∈I.subschemeι '' F}) :
      (Set.univ : Set I.subscheme)⊆F := by
    have hclosed : IsClosed (I.subschemeι '' F) := I.subschemeι.isClosedMap F hF
    let J := Scheme.IdealSheafData.vanishingIdeal (⟨I.subschemeι '' F,hclosed⟩ : Closeds X)
    have hpoints : ∀ q : SchemeComplexPoint (I.subschemeι ≫ f),
        I.subschemeι (schemeComplexPointImage (I.subschemeι ≫ f) q)∈Set.range J.subschemeι := by
      intro q
      let p := schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl q
      have hp : p∈C := himage ▸ (show p∈Set.range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) from ⟨q,rfl⟩)
      rw [hEq] at hp
      rw [J.range_subschemeι]
      change I.subschemeι (schemeComplexPointImage (I.subschemeι ≫ f) q)∈I.subschemeι '' F
      exact hp
    have hrange := originalRangeSubset_of_complexPoints I.subschemeι f J.subschemeι hpoints
    intro z _hz
    have hz := hrange ⟨z,rfl⟩
    rw [J.range_subschemeι] at hz
    change I.subschemeι z∈I.subschemeι '' F at hz
    obtain ⟨w,hw,hwe⟩ := hz
    exact I.subschemeι.isClosedEmbedding.injective hwe ▸ hw
  have hpre : IsPreirreducible (Set.univ : Set I.subscheme) := by
    apply isPreirreducible_iff_isClosed_union_isClosed.mpr
    intro F G hF hG hcover
    let B := {p : SchemeComplexPoint f | schemeComplexPointImage f p∈I.subschemeι '' F}
    let D := {p : SchemeComplexPoint f | schemeComplexPointImage f p∈I.subschemeι '' G}
    have hB := schemeNativeAlgebraicTrace_isComplexAnalyticSubset f (m+1) (I.subschemeι '' F) (I.subschemeι.isClosedMap F hF)
    have hD := schemeNativeAlgebraicTrace_isComplexAnalyticSubset f (m+1) (I.subschemeι '' G) (I.subschemeι.isClosedMap G hG)
    have subC (A : Set I.subscheme) :
        {p : SchemeComplexPoint f | schemeComplexPointImage f p∈I.subschemeι '' A}⊆C := by
      intro p hp
      have hpI : schemeComplexPointImage f p∈I.support := by
        change schemeComplexPointImage f p ∈ (I.support : Set X)
        rw [←I.range_subschemeι]
        obtain ⟨z,_hz,hzp⟩ := hp
        exact ⟨z,hzp⟩
      exact (Set.ext_iff.mp hsupp p).mp hpI
    have hEq : C=B∪D := by
      ext p
      constructor
      · intro hp
        have hpI : schemeComplexPointImage f p∈I.support := (Set.ext_iff.mp hsupp p).mpr hp
        change schemeComplexPointImage f p ∈ (I.support : Set X) at hpI
        rw [←I.range_subschemeι] at hpI
        obtain ⟨z,hz⟩ := hpI
        rcases hcover (Set.mem_univ z) with hzf|hzg
        · exact Or.inl ⟨z,hzf,hz⟩
        · exact Or.inr ⟨z,hzg,hz⟩
      · exact fun h => h.elim (fun hp => subC F hp) (fun hp => subC G hp)
    rcases hC.eq_left_or_eq_right hB hD (subC F) (subC G) hEq with he|he
    · exact Or.inl (full_of_trace F hF he)
    · exact Or.inr (full_of_trace G hG he)
  let : PreirreducibleSpace I.subscheme := ⟨hpre⟩
  let : IrreducibleSpace I.subscheme := { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  let : IsReduced I.subscheme := hred
  have hi : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  exact ⟨I,hrad,hred,hi,himage,hinj,hstalk,hfull⟩
end SGPT.Projective.BDivNov16
