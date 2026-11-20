import SGPT.Projective.BDivOriginalPrincipalPrimeDescent
import SGPT.Projective.BDivCartierIdealModulePrereqs
import SGPT.Projective.BDivNov16OriginalIdealStalkDenominator
import SGPT.Okounkov.SchemeGenericPointComplexSurjectivity

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Okounkov SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves InvertibleIdealQuotient
open scoped Topology Manifold

namespace SGPT.Projective.BDivNov16

noncomputable section

/-- A nonzero affine equation generating an original ideal stalk generates the
same whole ideal after shrinking to a principal algebraic open. -/
theorem exists_regular_affine_generator_of_stalk_generator
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    (a : Γ(X,U)) (ha : a ∈ D.ideal U)
    (hne : X.presheaf.germ U.1 x hx a ≠ 0)
    (hgen : D.stalkIdeal x = Ideal.span {X.presheaf.germ U.1 x hx a}) :
    ∃ (V : X.affineOpens) (_ : x ∈ V.1) (s : Γ(X,V)),
      s ∈ nonZeroDivisors Γ(X,V) ∧ D.ideal V = Ideal.span {s} := by
  let g : Fin 1 → Γ(X,U) := fun _ => a
  have hsingle : Ideal.span (Set.range fun i => X.presheaf.germ U.1 x hx (g i)) =
      D.stalkIdeal x := by simpa only [g, Set.range_const] using hgen.symm
  obtain ⟨t, hxt, ht⟩ := originalIdeal_exists_common_denominator_of_stalk_generators D x U hx g hsingle
  let V : X.affineOpens := ⟨X.basicOpen t, U.2.basicOpen t⟩
  let j : (V : X.Opens) ⟶ (U : X.Opens) := homOfLE (X.basicOpen_le t)
  let ρ := (X.presheaf.map j.op).hom
  let : Nonempty (Spec Γ(X,V)) := ⟨V.2.primeIdealOf ⟨x,hxt⟩⟩
  let : IsOpenImmersion V.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec V.2
  let : IsIntegral (Spec Γ(X,V)) := isIntegral_of_isOpenImmersion V.2.fromSpec
  let : IsDomain Γ(X,V) := (affine_isIntegral_iff Γ(X,V)).mp inferInstance
  have hρt : IsUnit (ρ t) := X.toRingedSpace.isUnit_res_basicOpen t
  obtain ⟨u, hu⟩ := hρt
  have hmap : (D.ideal U).map ρ = D.ideal V := D.map_ideal_basicOpen U t
  have hρa : ρ a ≠ 0 := by
    intro hz
    apply hne
    rw [← X.presheaf.germ_res_apply j x hxt a]
    change X.presheaf.germ V.1 x hxt (ρ a) = 0
    rw [hz, map_zero]
  refine ⟨V, hxt, ρ a, mem_nonZeroDivisors_iff_ne_zero.mpr hρa, ?_⟩
  rw [← hmap]
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    have hmem : t * b ∈ Ideal.span {a} := by simpa only [g, Set.range_const] using ht b hb
    have hr := Ideal.mem_map_of_mem ρ hmem
    rw [Ideal.map_span, Set.image_singleton, map_mul, ← hu] at hr
    have hmul := (Ideal.span {ρ a}).mul_mem_left (↑(u⁻¹) : Γ(X,V)) hr
    change ρ b ∈ Ideal.span {ρ a}
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hmul
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem ρ ha))

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m+1) f] [IsSeparated f] [QuasiCompact f]
  [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType f]

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m+1)
local instance : IsComplexManifold (m+1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m+1)

/-- Exact nonzero principal analytic extensions at all complex points imply
invertibility of the original algebraic ideal on the entire scheme. -/
theorem originalIdeal_isInvertible_of_nativePrincipal
    (D : X.IdealSheafData)
    (hprincipal : ∀ p : SchemeComplexPoint f, ∃ b : NativeHolGerm (m+1) (SchemeComplexPoint f) p,
      b ≠ 0 ∧ Ideal.map (schemeNativeStalkGerm f (m+1) p)
        (D.stalkIdeal (schemeComplexPointImage f p)) = Ideal.span {b}) :
    D.IsInvertible := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let Ugood : X.Opens := ⨆ V : {V : X.affineOpens // ∃ s : Γ(X,V),
    s ∈ nonZeroDivisors Γ(X,V) ∧ D.ideal V = Ideal.span {s}}, V.1.1
  have hgood : closedPoints X ⊆ (Ugood : Set X) := by
    intro x hx
    let p : SchemeComplexPoint f := ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩
    have hpx : schemeComplexPointImage f p = x := pointOfClosedPoint_apply f x hx _
    obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let V : X.affineOpens := ⟨U,hU⟩
    have hpV : schemeComplexPointImage f p ∈ V.1 := hpx.symm ▸ hxU
    obtain ⟨b,hb,hg⟩ := hprincipal p
    obtain ⟨a,ha,hne,hgen⟩ :=
      exists_affine_generator_of_native_principal_stalk f m D p V hpV b hb hg
    obtain ⟨W, hpW, s, hs, hW⟩ :=
      exists_regular_affine_generator_of_stalk_generator D _ V hpV a ha hne hgen
    change x ∈ ((⨆ V : {V : X.affineOpens // ∃ s : Γ(X,V),
      s ∈ nonZeroDivisors Γ(X,V) ∧ D.ideal V = Ideal.span {s}}, V.1.1) : X.Opens)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W,s,hs,hW⟩,hpx ▸ hpW⟩
  have huniv : (Ugood : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hclosed : IsClosed ((Ugood : Set X)ᶜ) := Ugood.2.isClosed_compl
    obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints (Z := (Ugood : Set X)ᶜ)
      ⟨x,hx⟩ ⟨Set.univ, _, isOpen_univ,hclosed,(Set.univ_inter _).symm⟩
    exact hy (hgood hyc)
  intro x
  have hx : x ∈ (Ugood : Set X) := huniv.symm ▸ Set.mem_univ x
  obtain ⟨⟨V,s,hs,hV⟩,hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨V,hxV,s,hs,hV⟩

end

end SGPT.Projective.BDivNov16
