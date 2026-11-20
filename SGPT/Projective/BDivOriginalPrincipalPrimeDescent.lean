import SGPT.Projective.BDivOriginalIdealStalk
import SGPT.Okounkov.SchemeNativeStalkFlatness
import SGPT.Projective.BDivNov16NativePrincipalGermSpan

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory IsLocalRing Set Filter SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.GAGAMult SGPT.PSH.IdealRestriction
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves InvertibleIdealQuotient
open scoped Topology Manifold

namespace SGPT.Projective.BDivNov16

noncomputable section

/-- If extension of an ideal is nonzero principal in a local domain, one
original element already generates the extension. No flatness premise is
needed for this direction. -/
theorem exists_original_generator_of_principal_map
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B] [IsDomain B]
    (φ : A →+* B) (I : Ideal A) (b : B) (hb : b ≠ 0)
    (hmap : I.map φ = Ideal.span {b}) :
    ∃ a ∈ I, φ a ≠ 0 ∧ I.map φ = Ideal.span {φ a} := by
  classical
  have hnot : ∃ a ∈ I, φ a ∉ Ideal.span {b} * maximalIdeal B := by
    by_contra h
    push_neg at h
    have hle : I.map φ ≤ Ideal.span {b} * maximalIdeal B :=
      Ideal.map_le_iff_le_comap.mpr fun a ha => h a ha
    have hm : b ∈ Ideal.span {b} * maximalIdeal B :=
      hle (hmap.symm ▸ Ideal.mem_span_singleton_self b)
    obtain ⟨t, ht, hbt⟩ := Ideal.mem_span_singleton_mul.mp hm
    have h1 : b * (1 - t) = b * 0 := by rw [mul_sub, mul_one, hbt, sub_self, mul_zero]
    have ht1 : t = 1 := (sub_eq_zero.mp (mul_left_cancel₀ hb h1)).symm
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr (ht1 ▸ ht))
  obtain ⟨a, ha, haq⟩ := hnot
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hmap ▸ Ideal.mem_map_of_mem φ ha)
  have hu : IsUnit t := by
    by_contra h
    exact haq (Ideal.mem_span_singleton_mul.mpr
      ⟨t, (IsLocalRing.mem_maximalIdeal t).mpr h, by rw [← ht, mul_comm]⟩)
  refine ⟨a, ha, ?_, ?_⟩
  · rw [← ht]
    exact mul_ne_zero hu.ne_zero hb
  · rw [hmap, ← ht, Ideal.span_singleton_mul_left_unit hu]

section Native

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m+1) f] [IsSeparated f] [QuasiCompact f]

local instance primeDescentTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance primeDescentCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m+1)
local instance primeDescentManifold : IsComplexManifold (m+1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m+1)

/-- The exact analytic ideal extension chooses an ORIGINAL affine equation
whose germ generates the entire original algebraic ideal stalk. -/
theorem exists_affine_generator_of_native_principal_stalk
    (D : X.IdealSheafData) (p : SchemeComplexPoint f) (U : X.affineOpens)
    (hp : schemeComplexPointImage f p ∈ U.1)
    (b : NativeHolGerm (m+1) (SchemeComplexPoint f) p) (hb : b ≠ 0)
    (hprincipal : Ideal.map (schemeNativeStalkGerm f (m+1) p)
      (D.stalkIdeal (schemeComplexPointImage f p)) = Ideal.span {b}) :
    ∃ a ∈ D.ideal U,
      let r := (X.presheaf.germ U.1 (schemeComplexPointImage f p) hp).hom a
      r ≠ 0 ∧ D.stalkIdeal (schemeComplexPointImage f p) = Ideal.span {r} := by
  let ψ := (X.presheaf.germ U.1 (schemeComplexPointImage f p) hp).hom
  let φ := schemeNativeStalkGerm f (m+1) p
  have hmap : (D.ideal U).map (φ.comp ψ) = Ideal.span {b} := by
    rw [← Ideal.map_map]
    change Ideal.map φ ((D.ideal U).map ψ) = _
    rw [← D.stalkIdeal_eq_affine (schemeComplexPointImage f p) U hp]
    exact hprincipal
  obtain ⟨a, ha, hne, hgen⟩ :=
    exists_original_generator_of_principal_map (φ.comp ψ) (D.ideal U) b hb hmap
  let r := ψ a
  have hr : r ≠ 0 := by
    intro h
    apply hne
    change φ r = 0
    rw [h, map_zero]
  refine ⟨a, ha, hr, ?_⟩
  have hmapEq : (D.stalkIdeal (schemeComplexPointImage f p)).map φ =
      (Ideal.span {r}).map φ := by
    rw [D.stalkIdeal_eq_affine (schemeComplexPointImage f p) U hp, Ideal.map_map, Ideal.map_span,
      Set.image_singleton]
    exact hgen
  ext a
  rw [mem_ideal_iff_schemeNativeStalkGerm f (m+1) p
      (D.stalkIdeal (schemeComplexPointImage f p)) a,
    mem_ideal_iff_schemeNativeStalkGerm f (m+1) p (Ideal.span {r}) a, hmapEq]

end Native

end

end SGPT.Projective.BDivNov16
