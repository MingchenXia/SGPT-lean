import SGPT.Okounkov.ValGen2Atlas
import SGPT.Okounkov.ValGen2Veronese
import SGPT.AlmostSemigroup.ConeIndependence

/-!
# `prop:res` for an arbitrary valuation: `Δ_ν(aθ, aφ) = a Δ_ν(θ, φ)`

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, Section *Basic properties of partial Okounkov bodies*, `prop:res`.

For `a ∈ ℤ_{>0}`, `aθ = c₁(L^a, h₀^a)` and the weight `aφ` of `h^a` define
`Γ(aθ, aφ) = {(ν(s), k) : s ∈ H⁰(X, (L^a)^k ⊗ 𝓘(k aφ))^×}`. By the frame compatibility between
`L^a` and `L` (`SGPT.Okounkov.ValGen2.mem_multiplierSectionSet_tensorPower_iff`, which uses the
multiplier condition through one atlas), `Γ(aθ, aφ)` is the Veronese subset
`{(x, k) : (x, ak) ∈ Γ(θ, φ)}`; by `SGPT.Okounkov.ValGen2.setBody_veroneseSet` the continuous
extension of the Okounkov body map commutes with Veronese subsets. The source instead reduces to
`prop:Okourescaling` through log resolutions (`rmk:DeltaanaW0`); the Veronese argument works
for every valuation and needs no resolution.

## Main results

* `multiplierSectionSet_tensorPower_eq`: `Γ(aθ, aφ) = Γ(θ, φ)^{(a)}`.
* `partialBody_tensorPower_eq_smul`: `Δ_ν(aθ, aφ) = a Δ_ν(θ, φ)` whenever `Γ(θ, φ)` is an almost
  semigroup in an admissible cone `C` (the ambient cone of `Δ_ν(aθ, aφ)` is the Veronese cone
  `C^{(a)}`, which for `C = C(Δ_ν(L))` is `C(a Δ_ν(L)) = C(Δ_ν(L^a))`), and `setBody_of_cone_le`
  (the body does not change when the ambient cone is enlarged).
* **`partialBody_tensorPower_eq_smul_of_mass`** (source `prop:res`): in the setting of
  `SGPT.Okounkov.ValGen` (arbitrary valuation `ν = v`, `Γ(L) ∈ 𝒮'(C)` for `v`), for every
  `φ ∈ PSH(X, θ)` with positive mass, `Δ_ν(aθ, aφ) = a Δ_ν(θ, φ)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
open SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology Pointwise

/-- The Okounkov body of an almost semigroup does not change when the ambient admissible cone is
enlarged. -/
theorem setBody_of_cone_le {n : ℕ} {C D : AdmissibleCone n}
    (hCD : (C.cone : Set ((Fin n → ℝ) × ℝ)) ⊆ D.cone) {S : Set ((Fin n → ℤ) × ℤ)}
    (hsub : S ⊆ (latticePoints C.cone : Set _))
    (hS : (⟨S, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    SGPT.Okounkov.ValGen.setBody D S = SGPT.Okounkov.ValGen.setBody C S := by
  have hsubD : S ⊆ (latticePoints D.cone : Set _) := fun _ hz => hCD (hsub hz)
  have hSD := SGPT.AlmostSemigroup.ConeIndependence.includeSubset_mem_almostSemigroupLocus hCD hS
  rw [SGPT.Okounkov.ValGen.setBody_eq hsub hS, SGPT.Okounkov.ValGen.setBody_eq hsubD hSD]
  exact congrArg (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) =>
    (K : Set (EuclideanSpace ℝ (Fin n))))
    (SGPT.AlmostSemigroup.ConeIndependence.bodyExtension_includeAlmost hCD ⟨⟨S, hsub⟩, hS⟩)

section General

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance valGen2ResTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2ResCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}
  {L : X.Modules}

/-- **`Γ(aθ, aφ) = Γ(θ, φ)^{(a)}`** for the valuation `v` (at a point `c` with `v ≥ 0` there),
every atlas `b` of `L^a`. -/
theorem multiplierSectionSet_tensorPower_eq (hc : IsNonnegAt v c) (a : LineBundleAtlas L)
    {r : ℕ} (hr : 0 < r) (b : LineBundleAtlas (bundleTensorPower L r))
    (φ : SchemeComplexPoint f → EReal) :
    AlgebraicValuation.multiplierSectionSet f n E v c b (fun z => (r : EReal) * φ z) =
      veroneseSet r (AlgebraicValuation.multiplierSectionSet f n E v c a φ) := by
  ext ⟨x, k⟩
  rw [mem_veroneseSet]
  exact mem_multiplierSectionSet_tensorPower_iff f n E v hc a hr b φ x k

/-- **Source `prop:res` for an arbitrary valuation, on almost semigroups**: if `Γ(θ, φ)` is an
almost semigroup in the admissible cone `C`, then `Γ(aθ, aφ)` is one in the Veronese cone
`C^{(a)}` and `Δ_ν(aθ, aφ) = a Δ_ν(θ, φ)`. -/
theorem partialBody_tensorPower_eq_smul (hc : IsNonnegAt v c) (a : LineBundleAtlas L) {r : ℕ}
    (hr : 0 < r) (b : LineBundleAtlas (bundleTensorPower L r)) {C : AdmissibleCone n}
    (φ : SchemeComplexPoint f → EReal)
    (hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆ (latticePoints C.cone : Set _))
    (hΓ : (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    (∃ hsub' : AlgebraicValuation.multiplierSectionSet f n E v c b (fun z => (r : EReal) * φ z) ⊆
        (latticePoints (veroneseCone C hr).cone : Set _),
        (⟨_, hsub'⟩ : ConeSubset (veroneseCone C hr)) ∈ almostSemigroupLocus (veroneseCone C hr)) ∧
      SGPT.Okounkov.ValGen.partialBody f n E v c b (veroneseCone C hr)
          (fun z => (r : EReal) * φ z) =
        (r : ℝ) • SGPT.Okounkov.ValGen.partialBody f n E v c a C φ := by
  have heq := multiplierSectionSet_tensorPower_eq f n E v hc a hr b φ
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact ⟨veroneseSet_subset_latticePoints hr hsub,
      veroneseSubset_mem_almostSemigroupLocus hr hΓ⟩
  · unfold SGPT.Okounkov.ValGen.partialBody
    rw [heq]
    exact setBody_veroneseSet hr hsub hΓ

end General

/-! ### The book's statement in the setting of `SGPT.Okounkov.ValGen` -/

section Book

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance valGen2ResBookTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2ResBookCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance valGen2ResBookManifold :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
  (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))

include Y hY in
/-- **Source `prop:res` for an arbitrary valuation `ν = v`**: under `Γ(L) ∈ 𝒮'(C)` for `v` (source
`prop:Okounbiglbdl`, an explicit hypothesis), for every `φ ∈ PSH(X, θ)` with positive
non-pluripolar mass and every `a ∈ ℤ_{>0}`, `Δ_ν(aθ, aφ) = a Δ_ν(θ, φ)`: the partial Okounkov body
of `L^a` (any atlas `b`) with the weight `aφ` (ambient cone `C^{(a)}`, which for `C = C(Δ_ν(L))`
is `C(Δ_ν(L^a))`) is `a` times that of `(L, φ)`. Both are partial Okounkov bodies of almost
semigroups (source `thm:Gammaasg`). -/
theorem partialBody_tensorPower_eq_smul_of_mass [Nonempty (SchemeComplexPoint f)]
    (hc : IsNonnegAt v c) {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hmass : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) φ hφ)
    {r : ℕ} (hr : 0 < r) (b : LineBundleAtlas (bundleTensorPower L r)) :
    (∃ hsub' : AlgebraicValuation.multiplierSectionSet f (m + 1) E v c b
        (fun z => (r : EReal) * φ z) ⊆ (latticePoints (veroneseCone C hr).cone : Set _),
        (⟨_, hsub'⟩ : ConeSubset (veroneseCone C hr)) ∈ almostSemigroupLocus (veroneseCone C hr)) ∧
      SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c b (veroneseCone C hr)
          (fun z => (r : EReal) * φ z) =
        (r : ℝ) • SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a C φ := by
  have hΓ := SGPT.Okounkov.ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_mass f E Y hY a
    H c v hS hG hφ hmass
  exact partialBody_tensorPower_eq_smul f (m + 1) E v hc a hr b φ
    (SGPT.Okounkov.ValGen.multiplierSectionSet_subset_cone f E a c v hS φ) hΓ

end Book

end SGPT.Okounkov.ValGen2
