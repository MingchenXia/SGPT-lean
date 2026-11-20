import SGPT.Checks.Comparison.DimZeroComparison
import SGPT.Checks.Comparison.BJRelAmpleAppSeq
import SGPT.NAPotential.Homogeneous
import SGPT.NPP.DimensionZero
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# `thm:DXZ` in dimension zero

Source: `chapter_NApotential.tex`, `thm:DXZ`: *the map `eq:analymap`
`PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An`, is an order preserving bijection* (`X` a connected projective
manifold of dimension `n`; `n = 0` is not excluded). Blueprint `claude-dim-zero.tex`, nodes
`claude-dim-zero:point` and `claude-dim-zero:DXZ`.

The workspace proves that the map is well defined, order preserving, order reflecting and
injective in every dimension (`BJ.Exist.naAnalytification`, `DimZero.naAnalytification_le_iff_dim`,
`DimZero.naAnalytification_injective_dim`); surjectivity is open in positive dimension. Here the
whole theorem in dimension zero.

* `locallyQuasiFinite_of_dim_zero`, `discreteTopology_of_dim_zero`,
  `topologicalKrullDim_eq_zero_of_dim_zero`, `berkovichPoint_subsingleton_of_dim_zero`: a scheme
  smooth of relative dimension `0` over `ℂ` is étale, hence locally quasi-finite, hence discrete;
  if it is integral its Krull dimension is `0` and `X^An` is a single point
  (`BJ.berkovichPoint_subsingleton`, lane BJ-RELAMPLE).
* `exists_eq_const_of_isModuleTopologyPSH_of_dim_zero`: every `ψ ∈ PSH(L^An)` is a real constant
  (not identically `-∞`, and `< +∞` as a decreasing limit of GF functions).
* `naAnalytification_surjective_of_dim_zero`, **`source_DXZ_of_dim_zero`**: `thm:DXZ` in dimension
  zero; the preimage of the constant `c` is the translate by `c` of the homogeneous metric `Γ^0`
  of `ex:embedpshintona`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.DimZero

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

/-! ### A scheme smooth of relative dimension zero over `ℂ` -/

section Point

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

/-- **`X^An` is a point** for `X` integral, projective and smooth of relative dimension `0` over
`ℂ`. -/
theorem berkovichPoint_subsingleton_of_dim_zero [IsIntegral X] [IsProjective f] :
    Subsingleton (BerkovichPoint f) :=
  BJ.berkovichPoint_subsingleton f (topologicalKrullDim_eq_zero_of_dim_zero f)

/-- In dimension zero every psh metric on `L^An` is a real constant. -/
theorem exists_eq_const_of_isModuleTopologyPSH_of_dim_zero [IsIntegral X] [IsProjective f]
    {L : RationalPicardSpace X} {ψ : BerkovichPoint f → EReal}
    (h : IsModuleTopologyPSH.{0} f L ψ) : ∃ c : ℝ, ψ = fun _ => (c : EReal) := by
  have := berkovichPoint_subsingleton_of_dim_zero f
  obtain ⟨⟨v, hv⟩, D, -, hD⟩ := (isPSHForNumericalTopology_iff_inf f _ L ψ).mp h
  have htop : ψ v ≠ ⊤ := by rw [hD]; exact D.limit_ne_top f v
  refine ⟨(ψ v).toReal, funext fun w => ?_⟩
  rw [Subsingleton.elim w v, EReal.coe_toReal htop hv]

end Point

/-! ### `thm:DXZ` in dimension zero -/

section DXZ

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance dimZeroDXZProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance dimZeroDXZPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dimZeroDXZPointCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance dimZeroDXZPointManifold : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f 0 E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

/-- The element of `PSH^NA(X, θ)` with cutoff `c` on a point: the translate by `c` of the
homogeneous metric `Γ^0` of `ex:embedpshintona`. -/
theorem component_max_translate_homogeneous_of_dim_zero (c : ℝ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    (((SourceNAPotential.homogeneous (SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0)).translate c).component
      ω).val.max = c := by
  rw [← sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative ω),
    sourceNAPotentialCutoff_translate, sourceNAPotentialCutoff_homogeneous, zero_add]

include hm hθ in
/-- **`thm:DXZ`, surjectivity, in dimension zero.** -/
theorem naAnalytification_surjective_of_dim_zero (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    Function.Surjective (BJ.Exist.naAnalytification (θ := θ) f 0 E b HM hm hθ ω) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨c, rfl⟩ := exists_eq_const_of_isModuleTopologyPSH_of_dim_zero f hψ
  refine ⟨(SourceNAPotential.homogeneous (SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0)).translate c,
    Subtype.ext (funext fun v => ?_)⟩
  rw [BJ.Exist.naAnalytification_apply, NANS.naPotentialAnAt_eq_of_dim_zero,
    component_max_translate_homogeneous_of_dim_zero f]

include hm hθ in
/-- **`thm:DXZ` in dimension zero.** For `X` integral, projective and smooth of relative dimension `0`
over `ℂ` with `X(ℂ)` connected (a point), `L = m⁻¹ [M]`, `θ = c₁(L, h)`: the map `eq:analymap`
`PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An`, is an order preserving (and order reflecting) bijection. -/
theorem source_DXZ_of_dim_zero (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    (∀ Γ Γ' : SourceNAPotential θ, SourceNAPOrder Γ Γ' ↔
      ∀ v, (BJ.Exist.naAnalytification f 0 E b HM hm hθ ω Γ).1 v ≤
        (BJ.Exist.naAnalytification f 0 E b HM hm hθ ω Γ').1 v) ∧
      Function.Bijective (BJ.Exist.naAnalytification (θ := θ) f 0 E b HM hm hθ ω) :=
  ⟨fun _ _ => (naAnalytification_le_iff_dim f 0 E b HM hm hθ ω).symm,
    naAnalytification_injective_dim f 0 E b HM hm hθ ω,
    naAnalytification_surjective_of_dim_zero f E b HM hm hθ ω⟩

end DXZ

end SGPT.NAPotential.DimZero
