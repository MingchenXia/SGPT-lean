import SGPT.Projective.OkounkovOriginalBookInfty

/-!
# `rmk:DeltaanaW0`, first sentence, for an arbitrary valuation

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*
(`sec:PoB`), remark `rmk:DeltaanaW0`, first sentence: *if `φ` has analytic singularities and
`θ_φ` is a Kähler current, then `eq:Gamma0Gammaanalytic` holds*, i.e.
`d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0`.

In `sec:PoB` the valuation `ν : ℂ(X)^× → ℤⁿ` is an **arbitrary** rank `n` valuation (author
decision on record), assumed surjective without loss of generality. The existing lane VAL-GEN
result `SGPT.Okounkov.ValGen.dist_inftySemigroup_multiplierConeSubset_eq_zero` proves the claim
for an arbitrary valuation under the hypothesis `Γ_ν(L) ∈ 𝒮'(C)`, i.e. the conclusion of
`prop:Okounbiglbdl` for `ν`. That proposition is now proved for every surjective valuation and
in every dimension (`SGPT.Okounkov.OriginalBook.exists_original_admissibleCone_allDimensions`).
Here we discharge the hypothesis: the statement holds **unconditionally** for every surjective
`ν`, in every dimension `n` (including `n = 0`), in every admissible cone `C ⊇ Γ(L)`
(`d_sg` only depends on the slices), in particular in the cone `C(Δ_ν(L))` over the Okounkov
body of `L` used by the book (`def:Okobd`, `thm:Gammaasg`).

## Setting

`X` an integral smooth projective complex scheme of dimension `n` (structure morphism `f`,
closed projective embedding `E`), `L` a big line bundle with atlas `a` and smooth Hermitian
metric `H`, `θ = c₁(L, H)`, `v : ℂ(X) → ℤⁿ_lex ∪ {∞}` an arbitrary surjective additive
valuation, section values read at a point `c` (the centre `valuationCenter f v` in the
source; every point is allowed), `φ` a `θ`-psh function with analytic singularities whose
current `θ_φ` is a Kähler current.

## Main results

* `SGPT.Okounkov.OF.dist_inftySection_multiplierSection_eq_zero`: for every admissible cone
  `C` containing `Γ_ν(L)`, `d_sg(Γ^∞_ν(θ, φ), Γ_ν(θ, φ)) = 0`;
* `SGPT.Okounkov.OF.dist_inftySection_multiplierSection_ownBody_eq_zero`: the same in the
  cone over the Okounkov body `Δ_ν(L)` (which is compact and convex).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]

local instance ofDeltaTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance ofDeltaCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance ofDeltaManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **Source `rmk:DeltaanaW0`, first sentence (`eq:Gamma0Gammaanalytic`), for an arbitrary
surjective rank `n` valuation, unconditionally and in every dimension.** If `φ` has analytic
singularities and `θ_φ` is a Kähler current, then `d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0` in every
admissible cone `C` containing `Γ(L)`. -/
theorem dist_inftySection_multiplierSection_eq_zero
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (hbig : SGPT.LineBundle.IsBig f L n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hv : Function.Surjective v) (c : X) {C : AdmissibleCone n}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (φ : SchemeComplexPoint f → EReal)
    (hK : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hA : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := n) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    dist (α := ConeSubset C)
      ⟨AlgebraicValuation.inftySectionSet f n E v c a φ,
        fun _ hz => hS (AlgebraicValuation.inftySectionSet_subset a φ hz)⟩
      ⟨AlgebraicValuation.multiplierSectionSet f n E v c a φ,
        fun _ hz => hS (AlgebraicValuation.multiplierSectionSet_subset a φ hz)⟩ = 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  -- `prop:Okounbiglbdl` for `v`: `Γ(L)` generates `ℤⁿ⁺¹` (cone-independent).
  obtain ⟨_, _, hG⟩ :=
    OriginalBook.exists_original_admissibleCone_allDimensions f a n E hbig v hv c
  cases n with
  | succ m =>
    obtain ⟨Y, hY⟩ := SGPT.GAGA.SmoothFlags.smoothFlagsExist X f E m
    exact ValGen.dist_inftySemigroup_multiplierConeSubset_eq_zero f E Y hY a H c v hS hG hK hA
  | zero =>
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
    obtain ⟨Y, hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f 0 E
    have hφ := (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hK).quasiPshPotential
    have heq := (PobDimZero.valuation_inftySectionSet_eq f E Y hY a c v hφ).trans
      (PobDimZero.valuation_multiplierSectionSet_eq f E Y hY a c v hφ).symm
    have key : ∀ S T : ConeSubset C, S.val = T.val → dist S T = 0 := fun S T h => by
      rw [Subtype.ext h, dist_self]
    exact key _ _ heq

/-- **Source `rmk:DeltaanaW0`, first sentence, in the book's cone `C(Δ_ν(L))`.** For an
arbitrary surjective rank `n` valuation `ν`, the Okounkov body `Δ_ν(L)` is compact and convex,
`Γ(L)` lies in the cone over it, and `d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0` there whenever `φ` has
analytic singularities and `θ_φ` is a Kähler current. -/
theorem dist_inftySection_multiplierSection_ownBody_eq_zero
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (hbig : SGPT.LineBundle.IsBig f L n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hv : Function.Surjective v) (c : X)
    (φ : SchemeComplexPoint f → EReal)
    (hK : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hA : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := n) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a))
      (hS : sectionSemigroup v c a ≤
        latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone),
      dist (α := ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv))
        ⟨AlgebraicValuation.inftySectionSet f n E v c a φ,
          fun _ hz => hS (AlgebraicValuation.inftySectionSet_subset a φ hz)⟩
        ⟨AlgebraicValuation.multiplierSectionSet f n E v c a φ,
          fun _ hz => hS (AlgebraicValuation.multiplierSectionSet_subset a φ hz)⟩ = 0 := by
  obtain ⟨hKc, hKv, _, hS, _⟩ :=
    OriginalBook.sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions
      f a n E hbig v hv c
  exact ⟨hKc, hKv, hS,
    dist_inftySection_multiplierSection_eq_zero f n E a H hbig v hv c hS φ hK hA⟩

end SGPT.Okounkov.OF
