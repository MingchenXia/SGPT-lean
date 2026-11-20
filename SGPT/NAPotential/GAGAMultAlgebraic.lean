import SGPT.NAPotential.BerkovichAnalytification
import SGPT.NAPotential.GAGAMultSiuGerms
import SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform

/-!
# The two formal halves of GAGA for algebraic models of ideal sheaves

Blueprint `claude-gagamult:alg-halves`.  For the canonical algebraic model
`algebraization I` of an analytic ideal sheaf `I` on `X(ℂ)` (the largest quasi-coherent ideal
sheaf whose sections have their germs in `I`) and the analytification `analytificationIdeal 𝔞`
of an algebraic ideal sheaf (`SGPT/NAPotential/BerkovichAnalytification.lean`):

* `le_algebraization_analytificationIdeal`: `𝔞 ≤ alg(𝔞^an)` for every ideal sheaf `𝔞`;
* `analytificationIdeal_algebraization_le`: `alg(I)^an ⊆ I` for every coherent analytic `I`.

The remaining halves are `alg(𝔞^an) ≤ 𝔞` (faithful flatness of `𝒪_{X,x} → 𝒪^an_{X,x}` plus the
local-global principle on affines) and `I ⊆ alg(I)^an`; for multiplier ideals the latter is the
algebraicity statement `MultiplierIdealAlgebraic` below, which by Siu's uniform global generation
(`siuGlobalGeneration_fixedWeight`) reduces to GAGA for global sections of `𝒪(m)|_X`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open scoped Topology Manifold
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.GAGAMult

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance gagaHalvesPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance gagaHalvesPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- `𝔞 ≤ alg(𝔞^an)`: every algebraic ideal sheaf lies in the algebraic model of its
analytification. -/
theorem le_algebraization_analytificationIdeal (𝔞 : X.IdealSheafData) :
    𝔞 ≤ algebraization f n E (analytificationIdeal f n E 𝔞) := by
  unfold algebraization
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U r hr
  refine Ideal.subset_span fun p hp => ?_
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U r p hp, 1,
    fun _ => schemeOpenRegularFunction f n E U r, fun _ => fun _ => 1,
    fun _ => ⟨U, hp, r, hr, rfl⟩, fun _ => holomorphicAt_const 1, ?_⟩
  exact Eventually.of_forall fun y => by simp

/-- The germ at `p` of the analytic function of an element of `Γ(X, U)` is a ring homomorphism. -/
def regularGermHom (U : X.Opens) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    Γ(X, U) →+* NativeHolGerm n (SchemeComplexPoint f) p :=
  letI := E.isSeparated
  letI := E.quasiCompact
  (schemeNativeStalkGerm f n p).comp (X.presheaf.germ U (schemeComplexPointImage f p) hp).hom

theorem regularGermHom_apply (U : X.Opens) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) (r : Γ(X, U)) :
    regularGermHom f n E U p hp r = NativeHolGerm.mk (schemeOpenRegularFunction f n E U r)
      (schemeOpenRegularFunction_holomorphicAt f n E U r p hp) :=
  (schemeOpenRegularFunction_germ f n E U r p hp).symm

/-- `alg(I)^an ⊆ I` for every coherent analytic ideal sheaf `I`. -/
theorem analytificationIdeal_algebraization_le (I : GermIdeal n (SchemeComplexPoint f))
    (hI : I.IsCoherent) : (analytificationIdeal f n E (algebraization f n E I)).Le I := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  intro p g hg
  have hg' : IsInSpanAt (n := n) (fun s => ∃ (U : X.affineOpens)
      (_ : schemeComplexPointImage f p ∈ (U : X.Opens)) (r : Γ(X, U)),
        r ∈ (algebraization f n E I).ideal U ∧ s = schemeOpenRegularFunction f n E U r) p g := hg
  refine GermIdealTotalTransform.mem_of_isInSpanAt_mem hI ?_
  refine IsInSpanAt.mono ?_ hg'
  rintro _ ⟨U, hp, r, hr, rfl⟩
  -- the regular functions of `span (algebraicSections I U)` have germs in the span of `I_p`
  have hle : Ideal.span (algebraicSections f n E I U) ≤
      Ideal.comap (regularGermHom f n E U p hp) (spanGerms (I.mem p) p) := by
    refine Ideal.span_le.mpr fun t ht => ?_
    rw [SetLike.mem_coe, Ideal.mem_comap, regularGermHom_apply]
    exact mk_mem_spanGerms _ (ht p hp)
  have hmem := hle (algebraization_ideal_le f n E I U hr)
  rw [Ideal.mem_comap, regularGermHom_apply] at hmem
  exact GermIdealTotalTransform.mem_of_isInSpanAt_mem hI
    (isInSpanAt_of_mk_mem_spanGerms _ hmem)

/-- **Algebraicity of multiplier ideals** (the missing half of GAGA for multiplier ideals, the
input of `def:NApotential:L975`): for every quasi-psh `φ` on `X(ℂ)` and `c > 0`, the multiplier
ideal `𝓘(cφ)` is contained in, hence (by `analytificationIdeal_algebraization_le`) equal to, the
analytification of its algebraic model.  Not proved here: by `siuGlobalGeneration_fixedWeight` it reduces
to GAGA for the global holomorphic sections of `𝒪(m)|_{X(ℂ)}`, `m ≫ 0`. -/
def MultiplierIdealAlgebraic : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  letI := schemeAnalyticTN_isComplexManifold f n
  ∀ φ : SchemeComplexPoint f → EReal, IsGlobalQuasiPshPotential (n := n) φ →
    ∀ c : ℝ, 0 < c →
      (multiplierIdeal (n := n) c φ).Le
        (analytificationIdeal f n E (algebraization f n E (multiplierIdeal (n := n) c φ)))

end SGPT.NAPotential.Berkovich
