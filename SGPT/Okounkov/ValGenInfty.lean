import SGPT.Okounkov.ValGenSections
import SGPT.Okounkov.OkoNSInfty
import SGPT.Okounkov.AlgPOBComparison
import SGPT.GAGA.H0LOkounkov
import SGPT.NAPotential.QwNAConcavity
import SGPT.Okounkov.QwOkoScaling
import SGPT.Okounkov.MultiplierCancellation
import SGPT.Trace.BertiniGeneralTrace
import SGPT.Bergman.Quant3PBMConvergence

/-!
# The semigroups `Γ^∞(θ, φ)` and `Γ(θ, φ)` for an arbitrary valuation

Lane VAL-GEN, blueprint `claude-val-gen.tex`. Source: chapter *The theory of Okounkov bodies*,
Section *Algebraic partial Okounkov bodies* (`sec:PoB`), for an **arbitrary** valuation
`ν : ℂ(X)^× → ℤⁿ`: `prop:GammaepsSp`, the first sentence of `rmk:DeltaanaW0`, and the first step
(analytic singularities, Kähler current) of the proof of `thm:Gammaasg` / `cor:POBvolume`.

## Setting

`X` an integral smooth projective complex scheme of dimension `n = m + 1` carrying a smooth flag
`Y•` (as for the flag-valuation results of lanes OKO-A / DXMAIN / H0-GAGA3 / OKO-NS; the flag is
only used through the valuation-free asymptotic Riemann–Roch formula `thm:DXmain1` and the bound
`h⁰(X, L^m) = O(mⁿ)`), `L` a line bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`,
and an **arbitrary** valuation `v : ℂ(X) → ℤⁿ_lex ∪ {∞}` with section values at a point `c`
(the centre, `SGPT.Okounkov.AlgebraicValuation.valuationCenter`, in the source). The hypothesis
`Γ(L) ∈ 𝒮'(C)` (an admissible cone `C` containing `Γ(L)`, and `Γ(L)` generating `ℤⁿ⁺¹`) is the
conclusion of `prop:Okounbiglbdl` for `v`; it is an explicit hypothesis (for flag valuations it is
proved: `SGPT.GAGA.H0L.exists_sectionSemigroup_mem_fullSemigroupLocus`; for other valuations the
source's proof uses `rmk:Abhyankar`, [CFKLRS17] and a resolution).

## Main results

* `card_slice_multiplierSectionSet`: `#Γ_k(θ, φ) = h⁰(X, L^k ⊗ 𝓘(kφ))` for the valuation `v`
  (one-dimensional leaves, `SGPT.Okounkov.ValGen.card_vectorSet_eq_finrank`);
* `tendsto_normalized_multiplierH0`: `k⁻ⁿ h⁰(X, L^k ⊗ 𝓘(kφ)) → vol θ_φ / n!`
  (`= vol Δ_{Y•}(θ_φ)`, valuation-free);
* `inftySemigroup`: `Γ^∞(θ, φ)` is an additive semigroup;
* `generatedGroup_inftySemigroup_eq_top`: if `θ_φ` is a Kähler current with analytic
  singularities, `Γ^∞(θ, φ)` generates `ℤⁿ⁺¹` (absorbing sections: for every `u ∈ H⁰(X, L^j)`
  there is `σ ∈ H⁰(X, L^N ⊗ 𝓘_∞(Nφ))` with `σ u ∈ H⁰(X, L^{N+j} ⊗ 𝓘_∞((N+j)φ))`);
* **`inftySemigroup_mem_fullSemigroupLocus`** (source `prop:GammaepsSp`):
  `Γ^∞(θ, φ) ∈ 𝒮'(C)` and `k⁻ⁿ #Γ^∞_k(θ, φ) → (1/n!) ∫_X θ_φⁿ`;
* `dist_inftySemigroup_multiplierSectionSet_eq_zero` (source `rmk:DeltaanaW0`, first sentence):
  `d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0`;
* `multiplierSectionSet_mem_almostSemigroupLocus_of_analytic` (source `thm:Gammaasg` in the
  analytic Kähler case): `Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}` with `vol Γ(θ, φ) = vol θ_φ / n!`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.AlgebraicValuation SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov SGPT.IGood.DXMain
open scoped Topology ENNReal

/-! ### Germ lemmas -/

section Germs

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A holomorphic germ lies in `𝓘_∞(0)` (it is locally bounded). -/
theorem mem_inftyIdeal_zero {x : M} {h : M → ℂ} (hh : HolomorphicAt n h x) :
    (SGPT.PSH.inftyIdeal (n := n) (fun _ => (0 : EReal))).mem x h := by
  refine ⟨hh, (‖h x‖ + 1) ^ 2, by positivity, ?_⟩
  have hc : ContinuousAt h x := HolomorphicAt.continuousAt hh
  have hev : ∀ᶠ y in 𝓝 x, ‖h y‖ < ‖h x‖ + 1 := by
    have := (continuous_norm.continuousAt.comp hc).eventually (gt_mem_nhds (lt_add_one ‖h x‖))
    exact this
  filter_upwards [hev] with y hy
  simp only [multiplierDensity, multiplierWeight, mul_zero, neg_zero, EReal.exp_zero, mul_one]
  apply ENNReal.ofReal_le_ofReal
  have h0 : 0 ≤ ‖h y‖ := norm_nonneg _
  nlinarith

/-- **`lma:IandIinf` across levels**: for `ψ` quasi-psh with analytic singularities and `ε > 0`
there is `k₀` such that `𝓘(N q ψ) ⊆ 𝓘_∞(K ψ)` whenever `K ≥ k₀` and `K (1 + ε) ≤ N q`. -/
theorem exists_mem_inftyIdeal_of_mem_multiplierIdeal [CompactSpace M] {ψ : M → EReal}
    (hψq : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (hψan : HasManifoldAnalyticSingularityType (n := n) ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ K : ℕ, k₀ ≤ K → ∀ (N : ℕ) (q : ℝ), 0 < N → 0 < q →
      (K : ℝ) * (1 + ε) ≤ N * q → ∀ (x : M) (g : M → ℂ),
        (multiplierIdeal (n := n) (N : ℝ) (fun y => (q : EReal) * ψ y)).mem x g →
          (SGPT.PSH.inftyIdeal (n := n) (fun y => (K : EReal) * ψ y)).mem x g := by
  have hψan' : (VariableComplexAtlas.ofFixedModel n M).HasRationalAnalyticChartType ψ :=
    fun e z hz => hψan e z hz
  obtain ⟨k₀, hk₀, hI⟩ := SGPT.PSH.MultiplierIdealInf.lma_IandIinf hψan' hε
  refine ⟨k₀, hk₀, fun K hK N q hN hq hKq x g hg => ?_⟩
  have hKpos : (0 : ℝ) < K := by exact_mod_cast lt_of_lt_of_le hk₀ hK
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply hI K hK x g
  refine ⟨hg.1, ?_⟩
  have h1 := (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff hNR hq).mp hg.2
  have hx : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  have h2 := multiplierIntegrableAt_of_exponent_le
    (hψq (complexChartAt (n := n) x) _ ((complexChartAt (n := n) x).val.map_source hx))
    (mul_pos hKpos (by linarith)) hKq h1
  refine (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff one_pos
    (mul_pos hKpos (by linarith))).mpr ?_
  rw [one_mul]
  exact h2

end Germs

/-! ### The scheme setting -/

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance valGenInftyTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGenInftyCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance valGenInftyManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-! ### Valuation-free asymptotics -/

/-- **`thm:DXmain1`, real form** (valuation-free; `X` carries a smooth flag):
`k⁻ⁿ h⁰(X, L^k ⊗ 𝓘(kφ)) → vol Δ_{Y•}(θ_φ) = vol θ_φ / n!` for every `φ ∈ PSH(X, θ)`. -/
theorem tendsto_normalized_multiplierH0 [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ (m + 1) *
        (multiplierH0 f (m + 1) E hφ.1.quasiPlurisubharmonic L k : ℝ)) atTop
      (𝓝 (volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₀, -, hC⟩ := AlgPOB.exists_cubeCone_contains f E Y hY a H
  obtain ⟨hsub, hKC⟩ := hC C₀ le_rfl φ hφ
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  have h := AlgPOB.tendsto_normalizedCardinality_of_fills (cubeCone (n := m + 1) C₀) hKc hKv hKC
    (AlgPOB.multiplierConeSubset f E Y hY a φ hsub)
    (fun η hη => AlgPOB.multiplierConeSubset_upper f E Y hY a H hφ hsub hη)
    (fun ε hε => AlgPOB.multiplierConeSubset_lower f E Y hY a H hφ hsub
      (SGPT.GAGA.H0L.dxMainLowerBound_of_smoothFlag f E Y hY a H hφ) hε)
  refine h.congr fun k => ?_
  exact AlgPOB.normalizedCardinality_multiplierConeSubset f E Y hY a
    hφ.1.quasiPlurisubharmonic hsub k

/-! ### Counting for the valuation `v` -/

variable (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))

/-- The degree-`k` slice of a section value set is the vector set of the sections satisfying the
condition. -/
theorem slice_sectionValueSet_eq (P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop) (k : ℕ)
    (V : Submodule ℂ (SectionSpace f L k)) (hV : ∀ s : SectionSpace f L k, s ∈ V ↔ P k s) :
    slice (AlgebraicValuation.sectionValueSet v c a P) (k : ℤ) = vectorSet f c a v k V := by
  ext x
  constructor
  · rintro ⟨k', s, hs, hP, hz⟩
    have hk : k' = k := by
      have h2 := congrArg Prod.snd hz
      simp only at h2
      exact_mod_cast h2.symm
    subst hk
    exact ⟨s, hs, (hV s).mpr hP, (congrArg Prod.fst hz).symm⟩
  · rintro ⟨s, hs, hsV, rfl⟩
    exact ⟨k, s, hs, (hV s).mp hsV, rfl⟩

include Y hY in
/-- **`#Γ_k(θ, φ) = h⁰(X, L^k ⊗ 𝓘(kφ))` for the valuation `v`** (one-dimensional leaves), under
`Γ(L) ∈ 𝒮'(C)` for `v`. -/
theorem card_slice_multiplierSectionSet {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφq : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ) (k : ℕ) :
    Nat.card (slice (AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ) (k : ℤ)) =
      multiplierH0 f (m + 1) E hφq L k := by
  rw [AlgebraicValuation.multiplierSectionSet, slice_sectionValueSet_eq f a c v _ k
    (multiplierSubmodule f (m + 1) E hφq L k) (fun s => Iff.rfl)]
  exact card_vectorSet_eq_finrank f E Y hY a c v hS hG k _

/-! ### `Γ^∞(θ, φ)` for the valuation `v` -/

/-- Source `def:Okounkov:L500` for the valuation `v`: `Γ^∞(θ, φ)` is an additive semigroup
(`𝓘_∞(kφ) 𝓘_∞(lφ) ⊆ 𝓘_∞((k+l)φ)` and `ν(st) = ν(s) + ν(t)`). -/
def inftySemigroup (φ : SchemeComplexPoint f → EReal) :
    AddSubsemigroup ((Fin (m + 1) → ℤ) × ℤ) where
  carrier := AlgebraicValuation.inftySectionSet f (m + 1) E v c a φ
  add_mem' := by
    rintro z w ⟨k, s, hs, hks, rfl⟩ ⟨l, t, ht, hlt, rfl⟩
    have hu := atlasPowerGlobalMul_ne_zero (v := v) c a k l hs ht
    refine ⟨k + l, atlasPowerGlobalMul a k l s t, hu,
      OkoNS.isInftySection_atlasPowerGlobalMul f E a hks hlt, ?_⟩
    have hv := sectionValue_mul (v := v) c a k l s t
    rw [sectionValue_eq_vector c a (k + l) _ hu, sectionValue_eq_vector c a k s hs,
      sectionValue_eq_vector c a l t ht, ← WithTop.coe_add, ← toLex_add] at hv
    have hv' := toLex.injective (WithTop.coe_injective hv)
    rw [hv']
    ext <;> simp

theorem mem_inftySemigroup {φ : SchemeComplexPoint f → EReal} {z : (Fin (m + 1) → ℤ) × ℤ} :
    z ∈ inftySemigroup f E a c v φ ↔
      z ∈ AlgebraicValuation.inftySectionSet f (m + 1) E v c a φ := Iff.rfl

/-- `𝓘_∞(kφ) ⊆ 𝓘(kφ)` for sections. -/
theorem isMultiplierSection_of_isInftySection {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {k : ℕ} {s : bundlePowerGlobalSections L k}
    (hs : IsInftySection f (m + 1) E φ k s) : IsMultiplierSection f (m + 1) E φ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  refine Or.inr fun U α p hp => ?_
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : ManifoldQuasiPlurisubharmonic (n := m + 1) (fun x => ((k : ℝ) : EReal) * φ x) :=
    (TranscendentalCore.isThetaPshPotential_nonneg_smul hφ hkR.le).1.quasiPlurisubharmonic
  have h1 := OkoNS.inftyIdeal_le_multiplierIdeal' hq p _ (hs U α p hp)
  refine ⟨h1.1, ?_⟩
  have h3 := (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff one_pos hkR).mp h1.2
  rw [one_mul] at h3
  exact h3

/-- `Γ^∞(θ, φ) ⊆ Γ(θ, φ)` for the valuation `v`. -/
theorem inftySectionSet_subset_multiplierSectionSet {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    AlgebraicValuation.inftySectionSet f (m + 1) E v c a φ ⊆
      AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ :=
  AlgebraicValuation.sectionValueSet_mono c a
    (fun _ _ hs => isMultiplierSection_of_isInftySection f E a H hφ hs)

/-- `Γ(θ, φ) ⊆ Γ(L)`, hence `⊆ C`. -/
theorem multiplierSectionSet_subset_cone {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone) (φ : SchemeComplexPoint f → EReal) :
    AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ ⊆
      (latticePoints C.cone : Set _) :=
  fun _ hz => hS (AlgebraicValuation.multiplierSectionSet_subset a φ hz)

/-- `Γ(θ, φ)` for the valuation `v`, as a lattice subset of the cone `C`. -/
def multiplierConeSubset {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone) (φ : SchemeComplexPoint f → EReal) :
    ConeSubset C :=
  ⟨_, multiplierSectionSet_subset_cone f E a c v hS φ⟩

/-- The normalized cardinalities of a lattice subset of the cone. -/
theorem normalizedCardinality_eq_card {C : AdmissibleCone (m + 1)} (S : ConeSubset C) (k : ℕ) :
    S.normalizedCardinality k = (k : ℝ)⁻¹ ^ (m + 1) * (Nat.card (slice S.val (k : ℤ)) : ℝ) := by
  rw [ConeSubset.normalizedCardinality, ConeSubset.slices,
    ← Nat.card_eq_card_finite_toFinset]

include Y hY in
/-- **Counting `Γ(θ, φ)` for the valuation `v`**: under `Γ(L) ∈ 𝒮'(C)` for `v`,
`k⁻ⁿ #Γ_k(θ, φ) → vol θ_φ / n! = vol Δ_{Y•}(θ_φ)` for every `φ ∈ PSH(X, θ)`. -/
theorem tendsto_normalizedCardinality_multiplierSectionSet [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    Tendsto (multiplierConeSubset f E a c v hS φ).normalizedCardinality atTop (𝓝 (volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))) := by
  let := E.isSeparated
  let := E.quasiCompact
  refine (tendsto_normalized_multiplierH0 f E Y hY a H hφ).congr fun k => ?_
  rw [normalizedCardinality_eq_card]
  change _ = (k : ℝ)⁻¹ ^ (m + 1) *
    (Nat.card (slice (AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ) (k : ℤ)) : ℝ)
  rw [card_slice_multiplierSectionSet f E Y hY a c v hS hG hφ.1.quasiPlurisubharmonic k]

/-- `Γ^∞(θ, φ)` lies in the cone. -/
theorem inftySemigroup_le_cone {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    inftySemigroup f E a c v φ ≤ latticePoints C.cone :=
  fun _ hz => multiplierSectionSet_subset_cone f E a c v hS φ
    (inftySectionSet_subset_multiplierSectionSet f E a H c v hφ hz)

/-- Degreewise inclusion of slices gives the inequality of normalized cardinalities. -/
theorem normalizedCardinality_le_of_slice_subset {C : AdmissibleCone (m + 1)} (S T : ConeSubset C)
    {k : ℕ} (h : slice S.val (k : ℤ) ⊆ slice T.val (k : ℤ)) :
    S.normalizedCardinality k ≤ T.normalizedCardinality k := by
  rw [normalizedCardinality_eq_card, normalizedCardinality_eq_card]
  gcongr
  exact Nat.card_mono (T.finite_slice k) h

include Y hY in
/-- **Counting `Γ^∞(θ, φ)` for the valuation `v`**: if `θ_φ` is a Kähler current with analytic
singularities, `k⁻ⁿ #Γ^∞_k(θ, φ) → vol Δ_{Y•}(θ_φ) = vol θ_φ / n!`. Upper bound from
`Γ^∞ ⊆ Γ`; lower bound from `Γ(θ, qφ)_k ⊆ Γ^∞(θ, φ)_k` (`k ≫ 0`, `q > 1`, `lma:IandIinf`) and
`vol θ_{qφ} → vol θ_φ` as `q → 1+`. -/
theorem tendsto_normalizedCardinality_inftySemigroup [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    Tendsto (sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS
        (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ))).normalizedCardinality
      atTop (𝓝 (volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set K := PartialBody.generalPartialBody 𝔽 (H.curvature a) φ with hK
  set U := sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS hφθ)
  have hUT : ∀ k, U.normalizedCardinality k ≤
      (multiplierConeSubset f E a c v hS φ).normalizedCardinality k := fun k =>
    ConeSubset.normalizedCardinality_mono _ _
      (inftySectionSet_subset_multiplierSectionSet f E a H c v hφθ) k
  have hT := tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hφθ
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨q, hq1, hqψ, hqvol⟩ := OkoNS.exists_rat_smul_volume_ge (F := 𝔽) hφ
      (half_pos (sub_pos.mpr hb))
    have hTq := tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hqψ
    have hbq : b < volume.real (PartialBody.generalPartialBody 𝔽 (H.curvature a)
        (fun x => ((q : ℝ) : EReal) * φ x)) := by linarith
    obtain ⟨k₀, -, hincl⟩ := OkoNS.eventually_isInftySection_of_isMultiplierSection f E hφan
      (q := (q : ℝ)) (by exact_mod_cast hq1)
    filter_upwards [(tendsto_order.mp hTq).1 b hbq, eventually_ge_atTop k₀] with k hk hk₀
    refine lt_of_lt_of_le hk (normalizedCardinality_le_of_slice_subset _ _ ?_)
    rintro x ⟨k', s, hs, hP, hz⟩
    have hk' : k' = k := by
      have h2 := congrArg Prod.snd hz
      simp only at h2
      exact_mod_cast h2.symm
    subst hk'
    exact ⟨k', s, hs, hincl k' hk₀ s hP, hz⟩
  · filter_upwards [(tendsto_order.mp hT).2 b hb] with k hk
    exact lt_of_le_of_lt (hUT k) hk

include Y hY in
/-- **Absorbing sections**: if `θ_φ` is a Kähler current with analytic singularities, then for
every section `u ∈ H⁰(X, L^j)` there are `N` and `σ ∈ H⁰(X, L^N ⊗ 𝓘_∞(Nφ)) \ {0}` with
`σ u ∈ H⁰(X, L^{N+j} ⊗ 𝓘_∞((N+j)φ))`. (Take `q > 1` with `qφ ∈ PSH(X, θ)` of positive volume,
`σ ∈ H⁰(X, L^N ⊗ 𝓘(N qφ))` and `lma:IandIinf`.) Valuation-free. -/
theorem exists_absorbing_section [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) {j : ℕ}
    (u : bundlePowerGlobalSections L j) :
    ∃ (N : ℕ) (σ : bundlePowerGlobalSections L N), σ ≠ 0 ∧
      IsInftySection f (m + 1) E φ N σ ∧
      IsInftySection f (m + 1) E φ (N + j) (atlasPowerGlobalMul a N j σ u) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  have hpos : 0 < volume.real (PartialBody.generalPartialBody 𝔽 (H.curvature a) φ) :=
    OkoNS.volume_real_generalPartialBody_pos_of_kahler _ hφ
  obtain ⟨q, hq1, hqψ, hqvol⟩ := OkoNS.exists_rat_smul_volume_ge (F := 𝔽) hφ (half_pos hpos)
  have hqpos : 0 < volume.real (PartialBody.generalPartialBody 𝔽 (H.curvature a)
      (fun x => ((q : ℝ) : EReal) * φ x)) := by linarith
  have hq1R : (1 : ℝ) < q := by exact_mod_cast hq1
  set ε : ℝ := ((q : ℝ) - 1) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨k₀, hk₀, hI⟩ := exists_mem_inftyIdeal_of_mem_multiplierIdeal
    hφθ.1.quasiPlurisubharmonic hφan hεpos
  have hev := (tendsto_order.mp (tendsto_normalized_multiplierH0 f E Y hY a H hqψ)).1 0 hqpos
  obtain ⟨N, hN, hNk₀, hNj, hN1⟩ := (hev.and ((eventually_ge_atTop k₀).and
    ((eventually_ge_atTop ⌈(j : ℝ) * (1 + ε) / ε⌉₊).and (eventually_ge_atTop 1)))).exists
  have hNpos : 0 < N := hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hh0 : 0 < multiplierH0 f (m + 1) E hqψ.1.quasiPlurisubharmonic L N := by
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.mp h0] at hN
    simp at hN
  have := SectionSpace.finiteDimensional f E a N
  obtain ⟨σ', hσ'⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hh0
  set σ : bundlePowerGlobalSections L N := (σ' : SectionSpace f L N) with hσdef
  have hσ0 : σ ≠ 0 := fun h => hσ' (Subtype.ext h)
  have hσmult : IsMultiplierSection f (m + 1) E (fun x => ((q : ℝ) : EReal) * φ x) N σ := σ'.2
  have hσideal := hσmult.resolve_left (by omega)
  -- the level inequalities
  have hNq : ((N : ℕ) : ℝ) * (1 + ε) ≤ (N : ℝ) * q := by
    apply mul_le_mul_of_nonneg_left _ hNR.le
    rw [hε]; linarith
  have hNjq : (((N + j : ℕ)) : ℝ) * (1 + ε) ≤ (N : ℝ) * q := by
    have h1 : (j : ℝ) * (1 + ε) / ε ≤ N :=
      (Nat.le_ceil _).trans (by exact_mod_cast hNj)
    rw [div_le_iff₀ hεpos] at h1
    push_cast
    have : (q : ℝ) = 1 + 2 * ε := by rw [hε]; ring
    rw [this]
    nlinarith
  refine ⟨N, σ, hσ0, fun U α p hp => ?_, fun U α p hp => ?_⟩
  · exact hI N hNk₀ N q hNpos (by linarith) hNq p _ (hσideal U α p hp)
  · have h1 : (SGPT.PSH.inftyIdeal (n := m + 1)
        (fun y => (((N + j : ℕ) : EReal)) * φ y)).mem p
        (sectionFrameCoefficient f (m + 1) E α N σ) :=
      hI (N + j) (le_trans hNk₀ (Nat.le_add_right _ _)) N q hNpos (by linarith) hNjq p _
        (hσideal U α p hp)
    have h2 := mem_inftyIdeal_zero (n := m + 1)
      (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ p hp :
        HolomorphicAt (m + 1) (sectionFrameCoefficient f (m + 1) E α j u) p)
    have h3 := OkoNS.inftyIdeal_mul_mem_add h1 h2
    simp only [add_zero] at h3
    refine (SGPT.PSH.inftyIdeal_mem_congr ?_).mp h3
    have hU : IsOpen (schemeComplexPointImage f ⁻¹' (U : Set X)) :=
      U.isOpen.preimage (schemeComplexPointImage_continuous f)
    filter_upwards [hU.mem_nhds hp] with y hy
    exact (OkoNS.sectionFrameCoefficient_atlasPowerGlobalMul f E a α N j σ u hy).symm

include Y hY in
/-- **`Γ^∞(θ, φ)` generates `ℤⁿ⁺¹`** for the valuation `v` (`θ_φ` a Kähler current with analytic
singularities), as soon as `Γ(L)` does: every `(ν(u), j) ∈ Γ(L)` is the difference
`(ν(σu), N + j) - (ν(σ), N)` of two points of `Γ^∞(θ, φ)` (`exists_absorbing_section`). -/
theorem generatedGroup_inftySemigroup_eq_top [Nonempty (SchemeComplexPoint f)]
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    LatticeSlices.generatedGroup (inftySemigroup f E a c v φ) = ⊤ := by
  rw [eq_top_iff, ← hG]
  unfold LatticeSlices.generatedGroup
  rw [AddSubgroup.closure_le]
  rintro z ⟨j, u, hu, rfl⟩
  obtain ⟨N, σ, hσ0, hσ, hσu⟩ := exists_absorbing_section f E Y hY a H hφ hφan u
  have hσu0 := atlasPowerGlobalMul_ne_zero (v := v) c a N j hσ0 hu
  have h1 : (sectionVector v c a N σ hσ0, (N : ℤ)) ∈ inftySemigroup f E a c v φ :=
    ⟨N, σ, hσ0, hσ, rfl⟩
  have h2 : (sectionVector v c a (N + j) _ hσu0, ((N + j : ℕ) : ℤ)) ∈
      inftySemigroup f E a c v φ := ⟨N + j, _, hσu0, hσu, rfl⟩
  have hv := sectionValue_mul (v := v) c a N j σ u
  rw [sectionValue_eq_vector c a (N + j) _ hσu0, sectionValue_eq_vector c a N σ hσ0,
    sectionValue_eq_vector c a j u hu, ← WithTop.coe_add, ← toLex_add] at hv
  have hv' := toLex.injective (WithTop.coe_injective hv)
  have hz : (sectionVector v c a j u hu, (j : ℤ)) =
      (sectionVector v c a (N + j) _ hσu0, ((N + j : ℕ) : ℤ)) -
        (sectionVector v c a N σ hσ0, (N : ℤ)) := by
    rw [hv']
    ext <;> simp
  rw [hz]
  exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure h2) (AddSubgroup.subset_closure h1)

/-! ### `prop:GammaepsSp`, `rmk:DeltaanaW0` and the analytic case of `thm:Gammaasg` -/

include Y hY in
/-- **Source `prop:GammaepsSp` for an arbitrary valuation `v`**: under `Γ(L) ∈ 𝒮'(C)` for `v`
(source `prop:Okounbiglbdl`), if `φ` has analytic singularities and `θ_φ` is a Kähler current,
then `Γ^∞(θ, φ) ∈ 𝒮'(C)` (a semigroup in `C` generating `ℤⁿ⁺¹`) and
`k⁻ⁿ #Γ^∞_k(θ, φ) → (1/n!) ∫_X θ_φⁿ`, so `vol Γ^∞(θ, φ) = (1/n!) ∫_X θ_φⁿ`. -/
theorem inftySemigroup_mem_fullSemigroupLocus [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS
        (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)) ∈
        fullSemigroupLocus C ∧
      Tendsto (sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ))).normalizedCardinality
        atTop (𝓝 ((DiagonalMass.diagonalPotentialMass (H.curvature a) φ
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal /
            ((m + 1).factorial : ℝ))) ∧
      (sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ))).volume =
        (DiagonalMass.diagonalPotentialMass (H.curvature a) φ
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal /
            ((m + 1).factorial : ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  set K := PartialBody.generalPartialBody
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ with hKdef
  have hmass : volume.real K =
      (DiagonalMass.diagonalPotentialMass (H.curvature a) φ hφθ).toReal /
        ((m + 1).factorial : ℝ) := by
    rw [hKdef, AlgPOB.volume_real_generalPartialBody f E Y hY a H hφθ]
    congr 2
    exact SourceValuativeClosure.iVolume_eq_mass_of_kahler_analytic
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) ⟨hφθ, hφan⟩ hφ
  have hlim := tendsto_normalizedCardinality_inftySemigroup f E Y hY a H c v hS hG hφ hφan
  rw [← hKdef, hmass] at hlim
  exact ⟨sourceSubset_mem_fullSemigroupLocus C _ _
    (generatedGroup_inftySemigroup_eq_top f E Y hY a H c v hG hφ hφan), hlim, hlim.limsup_eq⟩

include Y hY in
/-- **Source `rmk:DeltaanaW0`, first sentence (`eq:Gamma0Gammaanalytic`), for an arbitrary
valuation `v`**: if `φ` has analytic singularities and `θ_φ` is a Kähler current, then
`d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0` (in every admissible cone `C ⊇ Γ(L)`, under `Γ(L) ∈ 𝒮'(C)`). -/
theorem dist_inftySemigroup_multiplierConeSubset_eq_zero [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    dist (sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS
        (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)))
      (multiplierConeSubset f E a c v hS φ) = 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  set U := sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS hφθ)
  set T := multiplierConeSubset f E a c v hS φ
  have hUT : U.val ⊆ T.val := inftySectionSet_subset_multiplierSectionSet f E a H c v hφθ
  have hU := tendsto_normalizedCardinality_inftySemigroup f E Y hY a H c v hS hG hφ hφan
  have hT := tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hφθ
  rw [ConeSubset.dist_eq_distance, ConeSubset.distance_eq_limsup_card]
  have heq : (fun k : ℕ => (k : ℝ)⁻¹ ^ (m + 1) * (((U.slices k).card : ℝ) + (T.slices k).card -
      2 * ((U.slices k ∩ T.slices k).card : ℝ))) =
      fun k => T.normalizedCardinality k - U.normalizedCardinality k := by
    funext k
    rw [Finset.inter_eq_left.mpr (ConeSubset.slices_subset_of_subset U T hUT k),
      ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality]
    ring
  rw [heq]
  have h := hT.sub hU
  rw [sub_self] at h
  exact h.limsup_eq

include Y hY in
/-- **Source `thm:Gammaasg` and `cor:POBvolume` in the analytic Kähler case (Step 1 of the
source's proof), for an arbitrary valuation `v`**: under `Γ(L) ∈ 𝒮'(C)` for `v`, if `φ` has
analytic singularities and `θ_φ` is a Kähler current, then `Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}` with
`vol Γ(θ, φ) = vol θ_φ / n! = (1/n!) ∫_X θ_φⁿ`, and the partial Okounkov body
`Δ_ν(θ, φ) = Δ(Γ(θ, φ))` has volume `vol θ_φ / n!`. -/
theorem multiplierConeSubset_mem_almostSemigroupLocus_of_analytic
    [Nonempty (SchemeComplexPoint f)] {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    multiplierConeSubset f E a c v hS φ ∈ almostSemigroupLocus C ∧
      (multiplierConeSubset f E a c v hS φ).volume =
        (DiagonalMass.diagonalPotentialMass (H.curvature a) φ
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal /
            ((m + 1).factorial : ℝ) ∧
      volume.real (partialBody f (m + 1) E v c a C φ) =
        (DiagonalMass.diagonalPotentialMass (H.curvature a) φ
          (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal /
            ((m + 1).factorial : ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨hfull, hlim, hvol⟩ := inftySemigroup_mem_fullSemigroupLocus f E Y hY a H c v hS hG hφ hφan
  have hd := dist_inftySemigroup_multiplierConeSubset_eq_zero f E Y hY a H c v hS hG hφ hφan
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  set T := multiplierConeSubset f E a c v hS φ
  -- the volume of `Γ(θ, φ)`
  have hvolT : T.volume = (DiagonalMass.diagonalPotentialMass (H.curvature a) φ hφθ).toReal /
      ((m + 1).factorial : ℝ) := by
    rw [← hvol]
    have h := ConeSubset.abs_volume_sub_le_distance
      (sourceSubset C (inftySemigroup f E a c v φ) (inftySemigroup_le_cone f E a H c v hS hφθ)) T
    rw [← ConeSubset.dist_eq_distance, hd] at h
    linarith [abs_nonneg (ConeSubset.volume (sourceSubset C (inftySemigroup f E a c v φ)
      (inftySemigroup_le_cone f E a H c v hS hφθ)) - T.volume), abs_le.mp h]
  have hpos : 0 < T.volume := by
    rw [hvolT, ← hvol]
    exact FullSemigroup.volume_pos ⟨_, hfull⟩
  have hmem : T ∈ almostSemigroupLocus C := by
    refine ⟨Metric.mem_closure_iff.mpr fun ε hε => ⟨_, hfull, ?_⟩, hpos⟩
    rw [dist_comm, hd]
    exact hε
  refine ⟨hmem, hvolT, ?_⟩
  rw [volume_partialBody a φ _ hmem]
  exact hvolT

/-! ### Kähler currents: Step 2 of the proof of `thm:Gammaasg` -/

/-- Nested section sets: if `Γ(θ, φ) ⊆ Γ(θ, ψ)` and both counts converge, the distance is the
difference of the limits. -/
theorem dist_multiplierConeSubset_eq_of_subset {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone) {φ ψ : SchemeComplexPoint f → EReal}
    (hsub : (multiplierConeSubset f E a c v hS φ).val ⊆ (multiplierConeSubset f E a c v hS ψ).val)
    {V W : ℝ} (hV : Tendsto (multiplierConeSubset f E a c v hS φ).normalizedCardinality atTop (𝓝 V))
    (hW : Tendsto (multiplierConeSubset f E a c v hS ψ).normalizedCardinality atTop (𝓝 W)) :
    dist (multiplierConeSubset f E a c v hS φ) (multiplierConeSubset f E a c v hS ψ) = W - V := by
  set S := multiplierConeSubset f E a c v hS φ
  set T := multiplierConeSubset f E a c v hS ψ
  rw [ConeSubset.dist_eq_distance, ConeSubset.distance_eq_limsup_card]
  have heq : (fun k : ℕ => (k : ℝ)⁻¹ ^ (m + 1) * (((S.slices k).card : ℝ) + (T.slices k).card -
      2 * ((S.slices k ∩ T.slices k).card : ℝ))) =
      fun k => T.normalizedCardinality k - S.normalizedCardinality k := by
    funext k
    rw [Finset.inter_eq_left.mpr (ConeSubset.slices_subset_of_subset S T hsub k),
      ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality]
    ring
  rw [heq]
  exact (hW.sub hV).limsup_eq

/-- `φ ≤ ψ` with `ψ` quasi-psh gives `Γ(θ, φ) ⊆ Γ(θ, ψ)` for the valuation `v`. -/
theorem multiplierSectionSet_mono_of_le {φ ψ : SchemeComplexPoint f → EReal}
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) ψ) (hle : φ ≤ ψ) :
    AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ ⊆
      AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a ψ := by
  let := E.isSeparated
  let := E.quasiCompact
  have hI := SGPT.Foundations.Analysis.Pending.iOrderOnManifold_of_le hψ hle
  apply AlgebraicValuation.sectionValueSet_mono c a
  rintro k s (hk | hs)
  · exact Or.inl hk
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · exact Or.inl hk
    · exact Or.inr fun U α p hp =>
        SGPT.Okounkov.multiplierIdeal_le_of_iOrderOnManifold hI (by exact_mod_cast hk) p _
          (hs U α p hp)

include Y hY in
/-- **Source `thm:Gammaasg` and `cor:POBvolume` for Kähler currents (Steps 1–2 of the source's
proof), for an arbitrary valuation `v`**: under `Γ(L) ∈ 𝒮'(C)` for `v`, if `θ_φ` is a Kähler
current (arbitrary singularities), then `Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}` with
`vol Γ(θ, φ) = vol Δ_ν(θ, φ) = vol θ_φ / n!` (`= vol Δ_{Y•}(θ_φ)`). Proof: a quasi-equisingular
approximation `(U_j)` of `φ` by Kähler currents with analytic singularities
(`PartialBody.exists_isKahlerQEA`) has `Γ(θ, φ) ⊆ Γ(θ, U_j)`,
`d_sg(Γ(θ, U_j), Γ(θ, φ)) = vol θ_{U_j}/n! - vol θ_φ/n! → 0` (`Δ_{Y•}(θ_φ) = ⋂_j Δ_{Y•}(θ_{U_j})`,
`lma:Okounkov:L1517`), and `d_sg(Γ^∞(θ, U_j), Γ(θ, U_j)) = 0` with `Γ^∞(θ, U_j) ∈ 𝒮'(C)`. -/
theorem multiplierConeSubset_mem_almostSemigroupLocus_of_kahler
    [Nonempty (SchemeComplexPoint f)] {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ) :
    multiplierConeSubset f E a c v hS φ ∈ almostSemigroupLocus C ∧
      (multiplierConeSubset f E a c v hS φ).volume = volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) ∧
      volume.real (partialBody f (m + 1) E v c a C φ) = volume.real
        (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set θ := H.curvature a with hθ
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨U, hU⟩ := PartialBody.exists_isKahlerQEA hφ
  have hUK : ∀ j, IsKahlerCurrentPotential θ (U j) := fun j => (hU.2 j).2
  have hUθ : ∀ j, IsThetaPshPotential θ.val (U j) := fun j =>
    PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hUK j)
  obtain ⟨-, hUan, hd, -, -⟩ := hU.1
  have hle : ∀ j, φ ≤ U j := fun j x => (hd.1 x).le_of_tendsto (hd.2 x) j
  -- volumes of the transcendental bodies
  set K : ℕ → Set (Fin (m + 1) → ℝ) := fun j => PartialBody.generalPartialBody 𝔽 θ (U j)
    with hKdef
  have hKφ : PartialBody.generalPartialBody 𝔽 θ φ = ⋂ j, K j := by
    rw [PartialBody.generalPartialBody_eq_kahlerPartialBody hφ,
      PartialBody.kahlerPartialBody_eq_kahlerPartialBodyOf hU, PartialBody.kahlerPartialBodyOf]
    exact iInter_congr fun j =>
      (PartialBody.generalPartialBody_eq_analyticPartialBody (hU.2 j).1 (hU.2 j).2).symm
  have hanti : Antitone K := by
    intro i j hij
    simp only [hKdef]
    rw [PartialBody.generalPartialBody_eq_kahlerPartialBody (hUK j),
      PartialBody.generalPartialBody_eq_kahlerPartialBody (hUK i)]
    exact (PartialBody.kahlerPartialBody_subset_of_iOrder (hUK j) (hUK i)
      (SGPT.Foundations.Analysis.Pending.iOrderOnManifold_of_le (hUθ i).1.quasiPlurisubharmonic
        (show U j ≤ U i from fun x => by have h := hd.1 x hij; exact h))).1
  have hKcpt : ∀ j, IsCompact (K j) := fun j =>
    (PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) (hUθ j)).2
  have hvolK : Tendsto (fun j => volume.real (K j)) atTop
      (𝓝 (volume.real (PartialBody.generalPartialBody 𝔽 θ φ))) := by
    have h := tendsto_measure_iInter_atTop (μ := (volume : Measure (Fin (m + 1) → ℝ)))
      (fun j => (hKcpt j).isClosed.measurableSet.nullMeasurableSet) hanti
      ⟨0, (hKcpt 0).measure_lt_top.ne⟩
    rw [← hKφ] at h
    have hfin : volume (PartialBody.generalPartialBody 𝔽 θ φ) ≠ ⊤ :=
      (PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) hφθ).2.measure_lt_top.ne
    exact (ENNReal.tendsto_toReal hfin).comp h
  set V := volume.real (PartialBody.generalPartialBody 𝔽 θ φ) with hVdef
  have hVpos : 0 < V := OkoNS.volume_real_generalPartialBody_pos_of_kahler _ hφ
  -- counts
  have hTφ := tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hφθ
  have hdist : ∀ j, dist (multiplierConeSubset f E a c v hS φ)
      (multiplierConeSubset f E a c v hS (U j)) = volume.real (K j) - V := fun j =>
    dist_multiplierConeSubset_eq_of_subset f E a c v hS
      (multiplierSectionSet_mono_of_le f E a c v (hUθ j).1.quasiPlurisubharmonic (hle j)) hTφ
      (tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG (hUθ j))
  have hvolT : (multiplierConeSubset f E a c v hS φ).volume = V := hTφ.limsup_eq
  have hmem : multiplierConeSubset f E a c v hS φ ∈ almostSemigroupLocus C := by
    refine ⟨Metric.mem_closure_iff.mpr fun ε hε => ?_, ?_⟩
    swap
    · change 0 < (multiplierConeSubset f E a c v hS φ).volume
      rw [hvolT]
      exact hVpos
    obtain ⟨j, hj⟩ := ((tendsto_order.mp hvolK).2 (V + ε) (by linarith)).exists
    obtain ⟨hfull, -, -⟩ := inftySemigroup_mem_fullSemigroupLocus f E Y hY a H c v hS hG
      (hUK j) (hUan j)
    refine ⟨_, hfull, ?_⟩
    have h0 := dist_inftySemigroup_multiplierConeSubset_eq_zero f E Y hY a H c v hS hG
      (hUK j) (hUan j)
    calc dist (multiplierConeSubset f E a c v hS φ) _
        ≤ dist (multiplierConeSubset f E a c v hS φ) (multiplierConeSubset f E a c v hS (U j)) +
            dist (multiplierConeSubset f E a c v hS (U j)) (sourceSubset C
              (inftySemigroup f E a c v (U j)) (inftySemigroup_le_cone f E a H c v hS
                (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hUK j)))) :=
          dist_triangle _ _ _
      _ = volume.real (K j) - V := by rw [hdist j, dist_comm, h0, add_zero]
      _ < ε := by linarith
  refine ⟨hmem, hvolT, ?_⟩
  rw [volume_partialBody a φ _ hmem]
  exact hvolT

/-! ### General potentials: Step 3 of the proof of `thm:Gammaasg` -/

/-- `φ ⪯_𝓘 ψ` gives `Γ(θ, φ) ⊆ Γ(θ, ψ)` for the valuation `v`. -/
theorem multiplierSectionSet_mono_of_iOrder {φ ψ : SchemeComplexPoint f → EReal}
    (hI : letI := E.isSeparated; letI := E.quasiCompact;
      IOrderOnManifold (n := m + 1) φ ψ) :
    AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ ⊆
      AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a ψ := by
  let := E.isSeparated
  let := E.quasiCompact
  apply AlgebraicValuation.sectionValueSet_mono c a
  rintro k s (hk | hs)
  · exact Or.inl hk
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · exact Or.inl hk
    · exact Or.inr fun U α p hp =>
        SGPT.Okounkov.multiplierIdeal_le_of_iOrderOnManifold hI (by exact_mod_cast hk) p _
          (hs U α p hp)

include Y hY in
/-- **Source `thm:Gammaasg`, `def:Okounkov:L687` and `cor:POBvolume` for an arbitrary valuation
`v`** (all three steps of the source's proof): under `Γ(L) ∈ 𝒮'(C)` for `v` (source
`prop:Okounbiglbdl`), for every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0` (equivalently
`vol Δ_{Y•}(θ_φ) > 0`), `Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}`, `vol Γ(θ, φ) = vol θ_φ / n!`, and the partial
Okounkov body `Δ_ν(θ, φ) = Δ(Γ(θ, φ))` (`partialBody`) has volume `vol θ_φ / n!`.
Step 3: replace `φ` by its `𝓘`-envelope `P = P_θ[φ]_𝓘` (same multiplier ideals, positive mass),
take a Kähler current `θ_s`, `s ≤ P` (`lma:kahcurrentposmass`), and the Kähler currents
`χ_t = t s + (1 - t) P ≤ P`: `Γ(θ, χ_t) ⊆ Γ(θ, φ)` and
`vol Δ_{Y•}(θ_{χ_t}) ≥ (1 - t)ⁿ vol Δ_{Y•}(θ_P)` by concavity, so
`d_sg(Γ(θ, χ_t), Γ(θ, φ)) → 0`, while `Γ(θ, χ_t)` are almost semigroups (Step 2). -/
theorem multiplierConeSubset_mem_almostSemigroupLocus
    [Nonempty (SchemeComplexPoint f)] {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) :
    multiplierConeSubset f E a c v hS φ ∈ almostSemigroupLocus C ∧
      (multiplierConeSubset f E a c v hS φ).volume = volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) ∧
      volume.real (partialBody f (m + 1) E v c a C φ) = volume.real
        (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set θ := H.curvature a with hθ
  set V := volume.real (PartialBody.generalPartialBody 𝔽 θ φ) with hVdef
  have hlocal := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  -- the `𝓘`-envelope
  set P := iSingularityEnvelope θ.val φ with hPdef
  have hP : IsThetaPshPotential θ.val P :=
    SGPT.Foundations.Analysis.Pending.iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1
      θ.property.2 hlocal φ hφ
  have hequiv := SGPT.Foundations.Analysis.Pending.iEquivalent_iSingularityEnvelope θ.val
    θ.property.1 θ.property.2 hlocal φ hφ
  have hΓP : AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a P =
      AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ :=
    (multiplierSectionSet_mono_of_iOrder f E a c v hequiv.2).antisymm
      (multiplierSectionSet_mono_of_iOrder f E a c v hequiv.1)
  have hTφ := tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hφ
  have hTP := tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG hP
  have hVP : volume.real (PartialBody.generalPartialBody 𝔽 θ P) = V := by
    have hcongr : multiplierConeSubset f E a c v hS P = multiplierConeSubset f E a c v hS φ :=
      Subtype.ext hΓP
    rw [hcongr] at hTP
    exact tendsto_nhds_unique hTP hTφ
  -- positive mass of the envelope and a Kähler current below it
  have hmass : DiagonalMass.HasPositivePotentialMass θ P hP := by
    have h := AlgPOB.volume_real_generalPartialBody f E Y hY a H hφ
    rw [← hVdef] at h
    have hfac : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hiv : 0 < (iVolume θ hlocal φ hφ).toReal := by
      rw [h] at hpos
      exact (div_pos_iff_of_pos_right hfac).mp hpos
    exact ENNReal.toReal_pos_iff.mp hiv |>.1
  obtain ⟨δ, hδ, s, hs, hsP⟩ := SGPT.Trace.BertiniGeneral.exists_kahlerCurrent_le (Nat.succ_pos m)
    (schemeProjectiveTNKahlerBackground f (m + 1) E) hP hmass
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  have hsK : IsKahlerCurrentPotential θ s :=
    ⟨KahlerBackground.smul hδ ω, by simpa only [KahlerBackground.smul_form] using hs⟩
  have hsθ : IsThetaPshPotential θ.val s :=
    PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hsK
  obtain ⟨y, hy⟩ : (PartialBody.generalPartialBody 𝔽 θ s).Nonempty := by
    have h := OkoNS.volume_real_generalPartialBody_pos_of_kahler 𝔽 hsK
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, measureReal_empty] at h
    exact lt_irrefl _ h
  -- the Kähler currents `χ_t`
  set χ : ℝ → SchemeComplexPoint f → EReal :=
    fun t => ThetaPshConvexCombination.convexComb t s P with hχ
  have hχK : ∀ t : ℝ, 0 < t → t < 1 → IsKahlerCurrentPotential θ (χ t) := by
    intro t ht0 ht1
    have h1 := TranscendentalCore.isThetaPshPotential_nonneg_smul hs ht0.le
    have h2 := TranscendentalCore.isThetaPshPotential_nonneg_smul hP (sub_nonneg.mpr ht1.le)
    have h3 := SGPT.Okounkov.isThetaPshPotential_add_from_positive_sum h1 h2
    refine ⟨KahlerBackground.smul (mul_pos ht0 hδ) ω, ?_⟩
    have hform : t • (θ - δ • ω.form) + (1 - t) • θ =
        θ - (KahlerBackground.smul (mul_pos ht0 hδ) ω).form := by
      rw [KahlerBackground.smul_form]
      module
    rw [hform] at h3
    exact h3
  have hχθ : ∀ t : ℝ, 0 < t → t < 1 → IsThetaPshPotential θ.val (χ t) := fun t ht0 ht1 =>
    PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hχK t ht0 ht1)
  have hχle : ∀ t : ℝ, 0 < t → χ t ≤ P := fun t ht0 =>
    SGPT.Bergman.Quant3.convexComb_le_right hsP
      (fun x => hP.1.quasiPlurisubharmonic.ne_top x) ht0
  have hχsub : ∀ t : ℝ, 0 < t → (multiplierConeSubset f E a c v hS (χ t)).val ⊆
      (multiplierConeSubset f E a c v hS φ).val := fun t ht0 => by
    change AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a (χ t) ⊆
      AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ
    rw [← hΓP]
    exact multiplierSectionSet_mono_of_le f E a c v hP.1.quasiPlurisubharmonic (hχle t ht0)
  -- the volumes of `χ_t`
  have hvolχ : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) ^ (m + 1) * V ≤ volume.real (PartialBody.generalPartialBody 𝔽 θ (χ t)) := by
    intro t ht0 ht1
    have hconc := QwOko.convexComb_generalPartialBody_subset_real (F := 𝔽) hsθ hP ht0 ht1
    have hsub : (fun x => (1 - t) • x + t • y) '' PartialBody.generalPartialBody 𝔽 θ P ⊆
        PartialBody.generalPartialBody 𝔽 θ (χ t) := by
      rintro _ ⟨x, hx, rfl⟩
      apply hconc
      show (1 - t) • x + t • y ∈ _
      rw [add_comm ((1 - t) • x)]
      exact Set.add_mem_add (Set.smul_mem_smul_set hy) (Set.smul_mem_smul_set hx)
    have hcpt := (PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) (hχθ t ht0 ht1)).2
    have hmono := measureReal_mono (μ := (volume : Measure (Fin (m + 1) → ℝ))) hsub
      hcpt.measure_lt_top.ne
    rw [OkoNS.volume_real_affine_image, hVP] at hmono
    have habs : |(1 - t) ^ (m + 1)| = (1 - t) ^ (m + 1) :=
      abs_of_nonneg (pow_nonneg (by linarith) _)
    rw [habs] at hmono
    exact hmono
  have hdist : ∀ t : ℝ, 0 < t → t < 1 → dist (multiplierConeSubset f E a c v hS (χ t))
      (multiplierConeSubset f E a c v hS φ) =
        V - volume.real (PartialBody.generalPartialBody 𝔽 θ (χ t)) := fun t ht0 ht1 =>
    dist_multiplierConeSubset_eq_of_subset f E a c v hS (hχsub t ht0)
      (tendsto_normalizedCardinality_multiplierSectionSet f E Y hY a H c v hS hG (hχθ t ht0 ht1))
      hTφ
  have hvolT : (multiplierConeSubset f E a c v hS φ).volume = V := hTφ.limsup_eq
  have hmem : multiplierConeSubset f E a c v hS φ ∈ almostSemigroupLocus C := by
    refine ⟨Metric.mem_closure_iff.mpr fun ε hε => ?_, ?_⟩
    swap
    · change 0 < (multiplierConeSubset f E a c v hS φ).volume
      rw [hvolT]
      exact hpos
    -- choose `t` with `(1 - (1 - t)^n) V < ε / 2`
    have hcont : Tendsto (fun t : ℝ => (1 - t) ^ (m + 1) * V) (𝓝[>] 0) (𝓝 V) := by
      have : Continuous (fun t : ℝ => (1 - t) ^ (m + 1) * V) := by fun_prop
      have h := this.tendsto 0
      simp only [sub_zero, one_pow, one_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0, ht1⟩ := ((hcont.eventually
      (lt_mem_nhds (show V - ε / 2 < V by linarith))).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
    have hmemχ := (multiplierConeSubset_mem_almostSemigroupLocus_of_kahler f E Y hY a H c v hS hG
      (hχK t ht0 ht1)).1
    obtain ⟨b, hb, hdb⟩ := Metric.mem_closure_iff.mp hmemχ.1 (ε / 2) (half_pos hε)
    refine ⟨b, hb, ?_⟩
    have hle := hvolχ t ht0 ht1
    calc dist (multiplierConeSubset f E a c v hS φ) b
        ≤ dist (multiplierConeSubset f E a c v hS φ) (multiplierConeSubset f E a c v hS (χ t)) +
            dist (multiplierConeSubset f E a c v hS (χ t)) b := dist_triangle _ _ _
      _ < ε := by
        rw [dist_comm, hdist t ht0 ht1]
        linarith
  refine ⟨hmem, hvolT, ?_⟩
  rw [volume_partialBody a φ _ hmem]
  exact hvolT

end SGPT.Okounkov.ValGen
