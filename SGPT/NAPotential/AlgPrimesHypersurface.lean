import SGPT.NAPotential.AlgPrimesValuation
import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition
import SGPT.Foundations.Analysis.Pending.UnramifiedNormalOrder
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition
import SGPT.Foundations.Analysis.Pending.IrreducibleComponentFilling

/-!
# Realizing an algebraic prime divisor from an analytic hypersurface on a smooth model


`SGPT.NAPotential.AlgPrimes.LocalOrderRealizations` asks, for every algebraic prime divisor `D`
over `X`, for an analytic presentation `p` (a modification `π : Y → X(ℂ)` with a *smooth
connected* hypersurface `E ⊆ Y`) and a point `y₀ ∈ E` at which the analytic orders along `E` of
the pull-backs of the germs of `𝒪_{X,π(y₀)}` are the algebraic orders `ord_D`.

The hypersurface produced by an algebraic construction (the analytification of the closure of
the centre of `ord_D` on a model) is in general singular.  This file removes the smoothness and
connectedness requirements, by the embedded resolution of irreducible analytic subvarieties of
compact complex manifolds (`SGPT.Foundations.Analysis.Pending.EmbeddedResolution.exists_embeddedResolution`,
proved in TN from the canonical resolution invariant and Cartan's coherence theorem; G11a
itself, the resolution of an arbitrary closed analytic subset, comes from the companion
`HironakaAPI3.exists_embeddedResolution_analytic`):

* **`exists_isRealizedBy_of_hypersurface`**: let `ρ : W → X(ℂ)` be an analytic modification (`W` is
  compact, as `X(ℂ)` is), `V ⊆ W` an irreducible analytic hypersurface, `w₀` a regular point of
  `V` with a flattening `Ψ` of `V` at `w₀`.  If the analytic order of `g^an ∘ ρ` along `V` at `w₀`
  is `ord_D(g)` for every nonzero germ `g ∈ 𝒪_{X,ρ(w₀)}`, then `D` is realized by an analytic
  presentation (`PrimeDivisorOver.IsRealizedBy`).  Proof: an embedded resolution `μ : W' → W`
  of `V` is an isomorphism over the regular locus of `V` and makes the strict transform `V'` a
  smooth connected hypersurface; `(W', ρ ∘ μ, V')` is an analytic presentation, and at the point
  `y₀` over `w₀` the orders along `V'` and along `V` agree (`μ` is unramified at `y₀` and
  `V' = μ⁻¹ V` near `y₀`), so the local criterion `isRealizedBy_of_ord_eq_stalkOrd` applies.
* `HypersurfaceRealizations`, `localOrderRealizations_of_hypersurfaceRealizations`,
  `algebraicPrimesRealized_of_hypersurfaceRealizations`: the corresponding form of the algebraic
  half of the dictionary, with a possibly singular hypersurface on a smooth model, and the
  implication to `AlgebraicPrimesRealized`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes

open Set Filter
open scoped Topology ENNReal Manifold ContDiff
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH.CompactPrimeOver SGPT.NAPotential.Berkovich SGPT.NAPotential.TowerAlg
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder BlowupTowers
open AnalyticModificationLocalDiscrepancy RegularLocusComponent IrreducibleComponentFilling

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance algPrimesHypPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimesHypPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPrimesHypPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X]

/-- **Realization from a possibly singular analytic hypersurface on a smooth compact model.**
Let `ρ : W → X(ℂ)` be an analytic modification (`W` is then compact), `V ⊆ W` an
irreducible analytic hypersurface, `w₀ ∈ V` a regular point of `V` and `Ψ` a flattening of `V` at
`w₀`.  If for every nonzero germ `g ∈ 𝒪_{X,ρ(w₀)}` the order of vanishing of `g^an ∘ ρ` along `V`
at `w₀` is `ord_D(g)`, then the algebraic prime divisor `D` is realized by an analytic
presentation, obtained from an embedded resolution of `V`. -/
theorem exists_isRealizedBy_of_hypersurface (E : ClosedProjectiveEmbedding f)
    (D : PrimeDivisorOver X) {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel (m + 1)) W] [IsComplexManifold (m + 1) W]
    {ρ : W → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := m + 1) ρ)
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) W) (hVdim : V.dim = m) {w₀ : W}
    (hw₀ : w₀ ∈ V.carrier) (hw₀reg : w₀ ∉ singularLocus V)
    (Ψ : DivisorFlattening (m := m) V.carrier w₀)
    (hD : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (ρ w₀)), g ≠ 0 →
      (D.ord ((BerkovichPoint.specializationMap
        (ordVal_support_specializes f D (schemeComplexPointImage f (ρ w₀)))).hom g) : ℤ) =
        ((pullbackNormalOrder hρ Ψ (stalkRep m (ρ w₀) g)
          (stalkRep_holomorphicAt (ρ w₀) g)).toNat : ℤ)) :
    ∃ p : PrimePresentation (m + 1) (SchemeComplexPoint f), D.IsRealizedBy m E p := by
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : CompactSpace W :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hρ
  obtain ⟨Wt, tWt, cWt, mWt, μ, hμ, hres⟩ := EmbeddedResolution.exists_embeddedResolution V
  let := tWt
  let := cWt
  let := mWt
  have hμmod : IsAnalyticModification (n := m + 1) μ :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hμ
  -- the point over `w₀`
  have hw₀S : w₀ ∈ (singularLocus V)ᶜ := hw₀reg
  obtain ⟨y₀, hy₀S, hy₀⟩ := hres.1.1.surjOn hw₀S
  have hy₀exc : y₀ ∉ exceptionalLocus (m + 1) μ := fun h =>
    Set.disjoint_left.mp hres.1.2 hy₀S h
  subst hy₀
  set S : Set Wt := strictTransform (m + 1) μ V.carrier with hSdef
  have hS : IsClosedConnectedSubmanifold (m + 1) S V.dim := hres.2
  have hy₀mem : y₀ ∈ S :=
    (RestrictedVolumePullbackLower.mem_strictTransform_iff hμmod.1.continuous V.isClosed_carrier
      hy₀exc).mpr hw₀
  have hreg : RegularAtDim (n := m + 1) S y₀ m := by
    have h := hS.2.2 y₀ hy₀mem
    rwa [hVdim] at h
  obtain ⟨Φ₀⟩ := DivisorFlattening.nonempty_of_regularAtDim hreg
  let p : PrimePresentation (m + 1) (SchemeComplexPoint f) :=
    { model := CMfd.of Wt
      projection := ρ ∘ μ
      modification := AnalyticModificationComposition.isAnalyticModification_comp hρ hμmod
      divisor := S
      divisorDimension := V.dim
      smooth := hS
      codimension_one := by rw [hVdim] }
  -- `S = μ⁻¹ V` near `y₀`
  have hO : IsOpen (exceptionalLocus (m + 1) μ)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hμmod.1
  have hsets : ∀ᶠ y in 𝓝 y₀, y ∈ S ↔ μ y ∈ V.carrier := by
    filter_upwards [hO.mem_nhds hy₀exc] with y hy
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hμmod.1.continuous
      V.isClosed_carrier hy
  refine ⟨p, isRealizedBy_of_ord_eq_stalkOrd (y₀ := y₀) E D p Φ₀ fun g hg => ?_⟩
  have hord : stalkOrd p Φ₀ g = pullbackNormalOrder hρ Ψ (stalkRep m (ρ (μ y₀)) g)
      (stalkRep_holomorphicAt (ρ (μ y₀)) g) := by
    unfold stalkOrd pullbackNormalOrder
    exact UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional hμmod.1 hy₀exc
      Ψ Φ₀ hsets (stalkRep m (ρ (μ y₀)) g ∘ ρ)
      ((stalkRep_holomorphicAt (ρ (μ y₀)) g).comp_contMDiff
        (Eventually.of_forall fun _ => hρ.1.contMDiffAt))
  rw [hord]
  exact hD g hg

/-- **Realization from a regular point of an analytic subset of a smooth compact model.**
Let `ρ : W → X(ℂ)` be an analytic modification of `X(ℂ)`, `T ⊆ W` a closed
analytic subset (neither irreducible nor of pure dimension in general) and `w₀ ∈ T` a point at
which `T` is a smooth hypersurface, with a flattening `Ψ`.  If the order of vanishing along `T` at
`w₀` of `g^an ∘ ρ` is `ord_D(g)` for every nonzero germ `g ∈ 𝒪_{X,ρ(w₀)}`, then `D` is realized
by an analytic presentation.  (The irreducible component of `T` through `w₀`, the closure of the
connected component of the regular locus, is an irreducible hypersurface regular at `w₀` and equal
to `T` near `w₀`; then `exists_isRealizedBy_of_hypersurface`.) -/
theorem exists_isRealizedBy_of_analyticSubset (E : ClosedProjectiveEmbedding f)
    (D : PrimeDivisorOver X) {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel (m + 1)) W] [IsComplexManifold (m + 1) W]
    {ρ : W → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := m + 1) ρ)
    {T : Set W} (hT : IsComplexAnalyticSubset (n := m + 1) T) {w₀ : W}
    (hreg : RegularAtDim (n := m + 1) T w₀ m) (Ψ : DivisorFlattening (m := m) T w₀)
    (hD : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (ρ w₀)), g ≠ 0 →
      (D.ord ((BerkovichPoint.specializationMap
        (ordVal_support_specializes f D (schemeComplexPointImage f (ρ w₀)))).hom g) : ℤ) =
        ((pullbackNormalOrder hρ Ψ (stalkRep m (ρ w₀) g)
          (stalkRep_holomorphicAt (ρ w₀) g)).toNat : ℤ)) :
    ∃ p : PrimePresentation (m + 1) (SchemeComplexPoint f), D.IsRealizedBy m E p := by
  obtain ⟨V, hVdef⟩ : ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) W,
      V = componentSubvariety hT hreg := ⟨_, rfl⟩
  have hVc : V.carrier = closure (component (n := m + 1) T w₀) := by rw [hVdef]; rfl
  have hVdim : V.dim = m := by rw [hVdef]; rfl
  have hVsub : V.carrier ⊆ T := by rw [hVdef]; exact componentSubvariety_subset hT hreg
  have hw₀C : w₀ ∈ component (n := m + 1) T w₀ := mem_component_self hreg
  have hVreg : RegularAtDim (n := m + 1) V.carrier w₀ m := by
    rw [hVc]
    exact regularAtDim_closure_component hreg hw₀C
  have hw₀V : w₀ ∈ V.carrier := by
    rw [hVc]
    exact subset_closure hw₀C
  have hw₀sing : w₀ ∉ singularLocus V := by
    intro h
    apply h.2
    change RegularAtDim (n := m + 1) V.carrier w₀ V.dim
    rw [hVdim]
    exact hVreg
  obtain ⟨Ψ'⟩ := DivisorFlattening.nonempty_of_regularAtDim hVreg
  obtain ⟨O, hO, hw₀O, hTO⟩ := exists_open_inter_subset_component hreg hw₀C
  have hsets : ∀ᶠ z in 𝓝 w₀, z ∈ V.carrier ↔ id z ∈ T := by
    filter_upwards [hO.mem_nhds hw₀O] with z hz
    refine ⟨fun h => hVsub h, fun h => ?_⟩
    rw [hVc]
    exact subset_closure (hTO ⟨h, hz⟩)
  have hid : w₀ ∉ exceptionalLocus (m + 1) (id : W → W) := by
    intro h
    apply h
    rw [mfderiv_id]
    exact Function.bijective_id
  refine exists_isRealizedBy_of_hypersurface E D hρ V hVdim hw₀V hw₀sing Ψ' fun g hg => ?_
  have hF := (stalkRep_holomorphicAt (m := m) (ρ w₀) g).comp_contMDiff
    (Eventually.of_forall fun _ => hρ.1.contMDiffAt)
  have hord : pullbackNormalOrder hρ Ψ' (stalkRep m (ρ w₀) g) (stalkRep_holomorphicAt (ρ w₀) g) =
      pullbackNormalOrder hρ Ψ (stalkRep m (ρ w₀) g) (stalkRep_holomorphicAt (ρ w₀) g) :=
    UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional contMDiff_id hid
      Ψ Ψ' hsets (stalkRep m (ρ w₀) g ∘ ρ) hF
  rw [hord]
  exact hD g hg

variable (m) in
/-- **The algebraic half of the dictionary, with a singular hypersurface on a smooth model**:
for every algebraic prime divisor `D` over `X` there are an analytic modification
`ρ : W → X(ℂ)` (from a complex manifold, necessarily compact), a closed analytic subset `T ⊆ W`
and a point
`w₀ ∈ T` at which `T` is a smooth hypersurface (with a flattening `Ψ`), such that the order of
vanishing along `T` at `w₀` of `g^an ∘ ρ` is `ord_D(g)` for every nonzero germ
`g ∈ 𝒪_{X,ρ(w₀)}`.  (A statement; not proved here.) -/
def HypersurfaceRealizations : Prop :=
  ∀ D : PrimeDivisorOver X, ∃ (W : CMfd.{0} (m + 1))
    (ρ : W → SchemeComplexPoint f) (hρ : IsAnalyticModification (n := m + 1) ρ)
    (T : Set W) (_ : IsComplexAnalyticSubset (n := m + 1) T) (w₀ : W)
    (_ : RegularAtDim (n := m + 1) T w₀ m) (Ψ : DivisorFlattening (m := m) T w₀),
    ∀ g : X.presheaf.stalk (schemeComplexPointImage f (ρ w₀)), g ≠ 0 →
      (D.ord ((BerkovichPoint.specializationMap
        (ordVal_support_specializes f D (schemeComplexPointImage f (ρ w₀)))).hom g) : ℤ) =
        ((pullbackNormalOrder hρ Ψ (stalkRep m (ρ w₀) g)
          (stalkRep_holomorphicAt (ρ w₀) g)).toNat : ℤ)

/-- **`AlgebraicPrimesRealized` reduces to `HypersurfaceRealizations`**: the hypersurface need
be neither smooth, nor irreducible, nor of pure dimension, and the model need not be a blow-up
of `X(ℂ)`; the irreducible component through `w₀` and its embedded resolution do the rest. -/
theorem algebraicPrimesRealized_of_hypersurfaceRealizations (E : ClosedProjectiveEmbedding f)
    (h : HypersurfaceRealizations (f := f) m) : AlgebraicPrimesRealized (f := f) m E := by
  intro D
  obtain ⟨W, ρ, hρ, T, hT, w₀, hreg, Ψ, hD⟩ := h D
  exact exists_isRealizedBy_of_analyticSubset E D hρ hT hreg Ψ hD

end SGPT.NAPotential.AlgPrimes

end
