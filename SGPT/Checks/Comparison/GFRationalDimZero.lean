import SGPT.Checks.Comparison.BJModel2Dimension
import SGPT.Checks.Comparison.BJCharge2Divisorial
import SGPT.NAPotential.BerkovichIdealValue
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The ORIGINAL dimension-zero Berkovich space, through its actual residue fields
Blueprint: `gf-rational-hull-dimension-zero.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull.NarrowDimensionZero
open Set AlgebraicGeometry CategoryTheory Order
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ

section Geometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f]
/-- Smooth of relative dimension `0` means étale, and étale morphisms are locally quasi-finite. -/
theorem locallyQuasiFinite_of_dim_zero : LocallyQuasiFinite f := by
  have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h := HasRingHomProperty.appLE (P := @Etale) f ‹_› U V e
  algebraize [(f.appLE U V e).hom]
  have : Algebra.Etale _ _ := h
  change Algebra.QuasiFinite _ _
  infer_instance

include f in
/-- A scheme smooth of relative dimension `0` over `ℂ` is discrete. -/
theorem discreteTopology_of_dim_zero : DiscreteTopology X := by
  have := locallyQuasiFinite_of_dim_zero f
  obtain ⟨y⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have h := f.isDiscrete_preimage_singleton y
  have huniv : f ⁻¹' {y} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv] at h
  exact isDiscrete_univ_iff.mp h

include f in
/-- An integral scheme smooth of relative dimension `0` over `ℂ` has Krull dimension `0`. -/
theorem topologicalKrullDim_eq_zero_of_dim_zero [IsIntegral X] : topologicalKrullDim X = 0 := by
  have := discreteTopology_of_dim_zero f
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

end Geometry

/-- Actual scheme coheight zero identifies the original generic point. -/
theorem genericPoint_eq_of_zero_coheight {X : Scheme.{0}} [IsIntegral X] {c : X}
    (h : coheight c = 0) : c = genericPoint X := by
  rw [Order.coheight_eq_zero] at h
  have h1 : c ≤ genericPoint X := by
    rw [Scheme.le_iff_specializes]
    exact genericPoint_specializes c
  exact (inseparable_iff_specializes_and.mpr
    ⟨Scheme.le_iff_specializes.mp (h h1), genericPoint_specializes c⟩).eq

section Residue
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
local instance narrowZeroProper : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

omit [IsProjective p] in
/-- On a zero-dimensional integral scheme every point is the generic point. -/
theorem eq_genericPoint_of_topologicalKrullDim_eq_zero (hX : topologicalKrullDim X = 0)
    (x : X) : x = genericPoint X := by
  apply genericPoint_eq_of_zero_coheight
  have h1 : (coheight x : WithBot ℕ∞) ≤ Order.krullDim X := Order.coheight_le_krullDim x
  have h2 : Order.krullDim X = topologicalKrullDim X := by
    change Order.krullDim X = Order.krullDim (TopologicalSpace.IrreducibleCloseds X)
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  rw [h2, hX] at h1
  have h3 : coheight x ≤ 0 := by exact_mod_cast h1
  exact nonpos_iff_eq_zero.mp h3

/-- **`κ(η) = ℂ` for a zero-dimensional variety**: the function field has transcendence degree
`0` over the algebraically closed field `ℂ`, so every element of the residue field at the
generic point is a constant. -/
theorem exists_algebraMap_eq_of_dim_zero (hX : topologicalKrullDim X = 0)
    (g : X.residueField (genericPoint X)) :
    letI := residueComplexAlgebra p (genericPoint X)
    ∃ c : ℂ, algebraMap ℂ (X.residueField (genericPoint X)) c = g := by
  let := p.stalkAlgebra (genericPoint X)
  let := residueComplexAlgebra p (genericPoint X)
  obtain ⟨d, htr, hd⟩ := exists_trdeg_eq_and_dim_eq p
  have hd0 : d = 0 := by
    rw [hX] at hd
    exact_mod_cast hd.symm
  subst hd0
  have : Algebra.IsAlgebraic ℂ X.functionField :=
    trdeg_eq_zero_iff.mp (by simpa using htr)
  let e : X.functionField ≃ₐ[ℂ] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective (X.residue (genericPoint X)).hom
        (residue_bijective_of_eq_genericPoint _ rfl) with
      commutes' := fun a => by
        have h := congrArg (fun φ => φ.hom a) (residueComplexHom_eq_stalkAlgebra p (genericPoint X))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h.symm }
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := X.functionField)).2 (e.symm g)
  exact ⟨c, by rw [← e.commutes, hc, AlgEquiv.apply_symm_apply]⟩

/-- **`X^An` is a single point for a zero-dimensional variety**: every semi-valuation is
supported at the generic point, and every valuation of `κ(η) = ℂ` trivial on `ℂ` is trivial. -/
theorem berkovichPoint_subsingleton (hX : topologicalKrullDim X = 0) :
    Subsingleton (BerkovichPoint p) := by
  constructor
  rintro ⟨s, w⟩ ⟨s', w'⟩
  obtain rfl := eq_genericPoint_of_topologicalKrullDim_eq_zero hX s
  obtain rfl := eq_genericPoint_of_topologicalKrullDim_eq_zero hX s'
  congr 1
  let := residueComplexAlgebra p (genericPoint X)
  apply SourceRealValuation.ext
  intro g
  by_cases hg : g = 0
  · subst hg
    rw [(w.eq_top_iff' 0).mpr rfl, (w'.eq_top_iff' 0).mpr rfl]
  · obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_dim_zero p hX g
    have hc : c ≠ 0 := by
      rintro rfl
      exact hg (map_zero _)
    change w.toFun _ = w'.toFun _
    rw [w.map_complex' c hc, w'.map_complex' c hc]

end Residue
/-- The actual original Berkovich space is a singleton in dimension zero, with no psh/model imports. -/
theorem berkovichPoint_subsingleton_of_dim_zero {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f] [IsIntegral X] [IsProjective f] :
    Subsingleton (BerkovichPoint f) :=
  berkovichPoint_subsingleton f (topologicalKrullDim_eq_zero_of_dim_zero f)

end SGPT.NAPotential.BJ.GfIm.RationalHull.NarrowDimensionZero
