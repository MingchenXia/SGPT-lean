import SGPT.Okounkov.ValGenSections
import SGPT.GAGA.OkoCloseBig

/-!
# Okounkov bodies of line bundles for an arbitrary valuation

Lane VAL-GEN, blueprint `claude-val-gen.tex`. Source: chapter *The theory of Okounkov bodies*,
Section *Algebraic partial Okounkov bodies* (`sec:PoB`), for an **arbitrary** valuation
`ν : ℂ(X)^× → ℤⁿ` (values of sections at a point `c`, in the source the centre of `ν`).

Under the conclusion `Γ(L) ∈ 𝒮'(C)` of `prop:Okounbiglbdl` for `ν` (an explicit hypothesis:
`Γ(L)` lies in an admissible cone `C` and generates `ℤⁿ⁺¹`) and on `X` carrying a smooth flag
(used only for the growth bound `h⁰(X, L^m) = O(mⁿ)` behind the one-dimensional leaves):

* `sectionSemigroup_le_coneOver`: `Γ(L)` lies in the cone `C(Δ_ν(L))` over its Okounkov body
  `Δ_ν(L) = Δ(Γ(L))`, which is a convex body (the book's ambient cone of `sec:PoB`);
* **`volume_eq_factorial_mul_okounkovBody`** (source `cor:Okounvol`): `vol L = n! vol Δ_ν(L)`
  (`k⁻ⁿ h⁰(X, L^k) → vol Δ_ν(L)`);
* **`tendsto_hausdorffDist_lineBundleDegreePolytope`** (source `prop:Deltaconvtwisted` for the
  trivial twist `T = 𝒪_X`, which is source `thm:HausOkoun` for `Γ(L)`): `Δ_k(L) → Δ_ν(L)` in the
  Hausdorff metric;
* `multiplierSectionSet_add_bounded_smooth` (source `prop:Okocurrent`, Step 1, for `ν`):
  `Γ(θ, φ) = Γ(θ', φ')` when `φ' = φ + f` for a bounded smooth `f` (change of the smooth reference
  metric `h₀`, `θ' = θ - dd^c f`); hence the partial bodies `Δ_ν(θ, φ) = Δ_ν(θ', φ')` agree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.ValGen

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation SGPT.LineBundle SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov
open scoped Topology ENNReal

/-! ### The cone over the Okounkov body -/

/-- A semigroup in an admissible cone that generates `ℤⁿ⁺¹` lies in the cone `C(Δ(S))` over its
Okounkov body. -/
theorem le_latticePoints_coneOver {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) :
    ∃ (hKc : IsCompact (body S)) (hKv : Convex ℝ (body S)),
      S ≤ latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone := by
  have hne := nonempty_of_generatedGroup_eq_top S hG
  have hKc := isCompact_body C S hS hne
  have hKv := convex_body S
  refine ⟨hKc, hKv, ?_⟩
  obtain ⟨y₀, hy₀⟩ := BodyGeometry.euclideanBody_nonempty C S hS hG
  obtain ⟨y₁, hy₁, -⟩ := hy₀
  intro z hz
  have hzC := hS hz
  have h2 : (0 : ℝ) ≤ (z.2 : ℝ) := C.nonnegativeHeight _ hzC
  change latticeCast n z ∈ (SGPT.GAGA.OkoClose.coneOver (body S) hKc hKv).cone
  refine ⟨h2, ?_⟩
  rcases h2.lt_or_eq with hpos | hzero
  · refine ⟨((z.2 : ℝ))⁻¹ • (fun i => (z.1 i : ℝ)), ?_, ?_⟩
    · have hmem := mem_closedCone_of_mem S hz
      have hsmul := (closedCone S).smul_mem (by positivity : (0 : ℝ) ≤ ((z.2 : ℝ))⁻¹) hmem
      change (((z.2 : ℝ))⁻¹ • (fun i => (z.1 i : ℝ)), (1 : ℝ)) ∈ closedCone S
      convert hsmul using 1
      ext
      · simp [latticeCast]
      · simp [latticeCast, inv_mul_cancel₀ hpos.ne']
    · change (fun i => (z.1 i : ℝ)) = (z.2 : ℝ) • (((z.2 : ℝ))⁻¹ • fun i => (z.1 i : ℝ))
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  · refine ⟨y₁, hy₁, ?_⟩
    have hx : (fun i => (z.1 i : ℝ)) = 0 := by
      apply C.zeroHeight
      have : latticeCast n z = ((fun i => (z.1 i : ℝ)), (0 : ℝ)) := by
        ext
        · simp [latticeCast]
        · simp [latticeCast, ← hzero]
      rw [← this]
      exact hzC
    change (fun i => (z.1 i : ℝ)) = (z.2 : ℝ) • y₁
    rw [hx, ← hzero, zero_smul]

/-! ### `cor:Okounvol` and `prop:Deltaconvtwisted` (`T = 𝒪_X`) for an arbitrary valuation -/

section Volume

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance valGenBodiesTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGenBodiesCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance valGenBodiesManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) {n}
  (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))

include E Y hY in
/-- `k⁻ⁿ h⁰(X, L^k) → vol Δ_ν(L)` for an arbitrary valuation, under `Γ(L) ∈ 𝒮'(C)`. -/
theorem tendsto_normalized_h0_okounkovBody {C : AdmissibleCone n}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤) :
    Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ n * (h0 f L k : ℝ)) atTop
      (𝓝 (MeasureTheory.volume.real (okounkovBody v c a))) := by
  have h := tendsto_source_of_generatedGroup_eq_top C _ hS hG
  refine h.congr fun k => ?_
  rw [ConeSubset.normalizedCardinality, card_sourceSubset_slices, slice_sectionSemigroup_eq,
    card_vectorSet_eq_finrank f E Y hY a c v hS hG k ⊤, finrank_top]
  rfl

include E Y hY in
/-- **Source `cor:Okounvol` for an arbitrary valuation `ν = v`**: under `Γ(L) ∈ 𝒮'(C)` for `v`
(source `prop:Okounbiglbdl`), `vol L = n! vol Δ_ν(L)`, i.e. `vol Δ_ν(L) = vol L / n!` (and the
`limsup` defining `vol L` is a limit). -/
theorem volume_eq_factorial_mul_okounkovBody {C : AdmissibleCone n}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤) :
    SGPT.LineBundle.volume f L n =
      ENNReal.ofReal ((n.factorial : ℝ) * MeasureTheory.volume.real (okounkovBody v c a)) :=
  volume_eq_of_tendsto (tendsto_normalized_h0_okounkovBody f E Y hY a c v hS hG)

/-- The degree polytopes of a semigroup, in Euclidean coordinates, are the degree bodies of
`SGPT.AlmostSemigroup.BodyGeometry`. -/
theorem image_degreePolytope (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (k : ℕ) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm '' degreePolytope n (S : Set ((Fin n → ℤ) × ℤ)) k =
      BodyGeometry.euclideanDegreeBody S k := by
  unfold degreePolytope BodyGeometry.euclideanDegreeBody
  exact LinearMap.image_convexHull (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap _

/-- **Source `prop:Deltaconvtwisted` for the trivial twist `T = 𝒪_X` (`thm:HausOkoun` for
`Γ(L)`), for an arbitrary valuation `ν = v`**: under `Γ(L) ∈ 𝒮'(C)`, `Δ_k(L) → Δ_ν(L)` in the
Hausdorff metric (Euclidean copies). -/
theorem tendsto_hausdorffDist_lineBundleDegreePolytope {C : AdmissibleCone n}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' lineBundleDegreePolytope v c a k)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm '' okounkovBody v c a)) atTop (𝓝 0) := by
  have h := BodyGeometry.tendsto_hausdorffDist_degreeBody C _ hS hG
  refine h.congr fun k => ?_
  rw [lineBundleDegreePolytope, image_degreePolytope]
  rfl

/-- `Δ_ν(L)` is a convex body (compact, convex, with nonempty interior) under `Γ(L) ∈ 𝒮'(C)`. -/
theorem okounkovBody_convexBody {C : AdmissibleCone n}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤) :
    IsCompact (okounkovBody v c a) ∧ Convex ℝ (okounkovBody v c a) ∧
      (interior (okounkovBody v c a)).Nonempty :=
  ⟨isCompact_body C _ hS (nonempty_of_generatedGroup_eq_top _ hG), convex_body _,
    BodyGeometry.interior_body_nonempty C _ hS hG⟩

end Volume

/-! ### `prop:Okocurrent`, Step 1, for an arbitrary valuation -/

section Current

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance valGenCurTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGenCurCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance valGenCurManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {n} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
  {L : X.Modules} (a : LineBundleAtlas L)

/-- **Source `prop:Okocurrent`, Step 1, for an arbitrary valuation**: changing the smooth reference
metric `h₀` of `L` changes the weight `φ` by a bounded smooth function `g`
(`θ' = θ - dd^c g`, `φ' = φ + g`), and `Γ(θ, φ) = Γ(θ', φ')`; consequently the partial bodies
coincide (`partialBody_add_bounded_smooth`). -/
theorem multiplierSectionSet_add_bounded_smooth {φ : SchemeComplexPoint f → EReal}
    {g : SchemeComplexPoint f → ℝ}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hg : letI := E.isSeparated; letI := E.quasiCompact; ChartSmooth (n := n) g)
    {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    AlgebraicValuation.multiplierSectionSet f n E v c a (fun x => φ x + (g x : EReal)) =
      AlgebraicValuation.multiplierSectionSet f n E v c a φ := by
  let := E.isSeparated
  let := E.quasiCompact
  have hI : ∀ k : ℕ, multiplierIdeal (n := n) (k : ℝ) (fun x => φ x + (g x : EReal)) =
      multiplierIdeal (n := n) (k : ℝ) φ := fun k =>
    SGPT.Okounkov.multiplierIdeal_add_bounded_smooth hφ hg hC _
  unfold AlgebraicValuation.multiplierSectionSet IsMultiplierSection
  simp only [hI]

theorem partialBody_add_bounded_smooth {φ : SchemeComplexPoint f → EReal}
    {g : SchemeComplexPoint f → ℝ}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hg : letI := E.isSeparated; letI := E.quasiCompact; ChartSmooth (n := n) g)
    {C : ℝ} (hC : ∀ x, |g x| ≤ C) (K : AdmissibleCone n) :
    partialBody f n E v c a K (fun x => φ x + (g x : EReal)) = partialBody f n E v c a K φ := by
  unfold partialBody
  rw [multiplierSectionSet_add_bounded_smooth f E v c a hφ hg hC]

end Current

end SGPT.Okounkov.ValGen
