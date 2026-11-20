import SGPT.Okounkov.ValGen2Suba
import SGPT.Okounkov.ValGen2Res

/-!
# `thm:concOko` for an arbitrary valuation: the analytic Kähler case with rational weights

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, `thm:concOko`: `Δ_ν(θ, tφ + (1-t)ψ) ⊇ tΔ_ν(θ, φ) + (1-t)Δ_ν(θ, ψ)`.

The source treats rational `t = p/N` and potentials with analytic singularities first: for
`s ∈ H⁰(X, L^k ⊗ 𝓘_∞(kφ))`, `r ∈ H⁰(X, L^k ⊗ 𝓘_∞(kψ))`,
`s^{p} r^{q} ∈ H⁰(X, L^{kN} ⊗ 𝓘_∞(kN(tφ + (1-t)ψ)))`, and concludes with `thm:HausOkoun` and
`rmk:DeltaanaW0`. Here this step is proved for an arbitrary valuation with Veronese subsets:
the degreewise sums of the Veronese subsets `Γ^∞(θ, φ)^{(p)}` and `Γ^∞(θ, ψ)^{(q)}` (full
semigroups) lie in `Γ(θ, χ)^{(N)}`, `χ = tφ + (1-t)ψ`, whose body is `N Δ_ν(θ, χ)`
(`SGPT.Okounkov.ValGen2.setBody_veroneseSet`), while their bodies are `p Δ_ν(θ, φ)`, `q Δ_ν(θ, ψ)`.

## Main results

* `ereal_coe_mul_add`, `ereal_convex_weight`: arithmetic of the weights in `EReal`.
* `isInftySection_atlasPowerGlobalMul_of_weights`: products of `𝓘_∞`-sections with different
  weights.
* **`partialBody_convexComb_superset_of_analytic`**: `thm:concOko` for `ν` when `φ, ψ` have
  analytic singularities, `θ_φ, θ_ψ` are Kähler currents and `t = p/(p+q)` is rational.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology Pointwise

/-- `c (x + y) = c x + c y` in `EReal` for a positive real `c`. -/
theorem ereal_coe_mul_add {c : ℝ} (hc : 0 < c) (x y : EReal) :
    (c : EReal) * (x + y) = (c : EReal) * x + (c : EReal) * y := by
  induction x using EReal.rec with
  | bot => rw [EReal.bot_add, EReal.coe_mul_bot_of_pos hc, EReal.bot_add]
  | top =>
    induction y using EReal.rec with
    | bot => rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hc, EReal.add_bot]
    | top => rw [EReal.top_add_top, EReal.coe_mul_top_of_pos hc, EReal.top_add_top]
    | coe y =>
      rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hc, ← EReal.coe_mul, EReal.top_add_coe]
  | coe x =>
    induction y using EReal.rec with
    | bot => rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hc, EReal.add_bot]
    | top =>
      rw [EReal.coe_add_top, EReal.coe_mul_top_of_pos hc, ← EReal.coe_mul, EReal.coe_add_top]
    | coe y =>
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        mul_add]

/-- The weights of a convex combination: with `N = p + q`,
`(Nk) ((p/N) φ + (q/N) ψ) = (pk) φ + (qk) ψ` in `EReal`. -/
theorem ereal_convex_weight {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (k : ℕ) (x y : EReal) :
    ((p * k + q * k : ℕ) : EReal) *
        ((((p : ℝ) / (p + q) : ℝ) : EReal) * x + (((q : ℝ) / (p + q) : ℝ) : EReal) * y) =
      ((p * k : ℕ) : EReal) * x + ((q * k : ℕ) : EReal) * y := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hN : (0 : ℝ) < (p : ℝ) + q := by positivity
  have hpos : (0 : ℝ) < ((p * k + q * k : ℕ) : ℝ) := by
    have : 0 < p * k + q * k := by positivity
    exact_mod_cast this
  have hcast : ((p * k + q * k : ℕ) : EReal) = (((p * k + q * k : ℕ) : ℝ) : EReal) := rfl
  rw [hcast, ereal_coe_mul_add hpos, ← mul_assoc, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul]
  have h1 : ((p * k + q * k : ℕ) : ℝ) * ((p : ℝ) / (p + q)) = ((p * k : ℕ) : ℝ) := by
    push_cast
    field_simp
  have h2 : ((p * k + q * k : ℕ) : ℝ) * ((q : ℝ) / (p + q)) = ((q * k : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [h1, h2]
  rfl

section Analytic

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance valGen2ConcTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2ConcCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance valGen2ConcManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))

/-- Products of `𝓘_∞`-sections of `L` with different weights: `s ∈ H⁰(L^k ⊗ 𝓘_∞(kφ))`,
`t ∈ H⁰(L^l ⊗ 𝓘_∞(lψ))` and `(k + l) χ = kφ + lψ` give `st ∈ H⁰(L^{k+l} ⊗ 𝓘_∞((k+l)χ))`. -/
theorem isInftySection_atlasPowerGlobalMul_of_weights {L : X.Modules} (a : LineBundleAtlas L)
    {φ ψ χ : SchemeComplexPoint f → EReal} {k l : ℕ} {s : bundlePowerGlobalSections L k}
    {t : bundlePowerGlobalSections L l} (hs : IsInftySection f (m + 1) E φ k s)
    (ht : IsInftySection f (m + 1) E ψ l t)
    (hχ : ∀ x, ((k + l : ℕ) : EReal) * χ x = (k : EReal) * φ x + (l : EReal) * ψ x) :
    IsInftySection f (m + 1) E χ (k + l) (atlasPowerGlobalMul a k l s t) := by
  intro U α p hp
  have h := SGPT.Okounkov.OkoNS.inftyIdeal_mul_mem_add (hs U α p hp) (ht U α p hp)
  have hfun : (fun y => (k : EReal) * φ y + (l : EReal) * ψ y) =
      fun y => ((k + l : ℕ) : EReal) * χ y := funext fun y => (hχ y).symm
  rw [hfun] at h
  refine (SGPT.PSH.inftyIdeal_mem_congr ?_).mp h
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' (U : Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hU.mem_nhds hp] with y hy
  exact (SGPT.Okounkov.OkoNS.sectionFrameCoefficient_atlasPowerGlobalMul f E a α k l s t hy).symm

/-- `Γ^∞(θ, φ)^{(p)}` and `Γ^∞(θ, ψ)^{(q)}` add, degreewise, into `Γ^∞(θ, χ)^{(p+q)}`,
`χ = (p/(p+q)) φ + (q/(p+q)) ψ`. -/
theorem veroneseSet_inftySemigroup_add_mem {L : X.Modules} (a : LineBundleAtlas L)
    {φ ψ : SchemeComplexPoint f → EReal} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (x y : Fin (m + 1) → ℤ) (k : ℤ)
    (hx : (x, k) ∈ veroneseSet p (SGPT.Okounkov.ValGen.inftySemigroup f E a c v φ :
      Set ((Fin (m + 1) → ℤ) × ℤ)))
    (hy : (y, k) ∈ veroneseSet q (SGPT.Okounkov.ValGen.inftySemigroup f E a c v ψ :
      Set ((Fin (m + 1) → ℤ) × ℤ))) :
    (x + y, k) ∈ veroneseSet (p + q) (SGPT.Okounkov.ValGen.inftySemigroup f E a c v
      (fun z => (((p : ℝ) / (p + q) : ℝ) : EReal) * φ z +
        (((q : ℝ) / (p + q) : ℝ) : EReal) * ψ z) : Set ((Fin (m + 1) → ℤ) × ℤ)) := by
  obtain ⟨m₁, s, hs, hsI, hz⟩ := hx
  obtain ⟨m₂, t, ht, htI, hz'⟩ := hy
  obtain ⟨hxs, hk₁⟩ := Prod.mk.inj hz
  obtain ⟨hyt, hk₂⟩ := Prod.mk.inj hz'
  simp only at hxs hk₁ hyt hk₂
  have hk0 : 0 ≤ k := by
    have h0 : (0 : ℤ) ≤ (p : ℤ) * k := by rw [hk₁]; exact Int.natCast_nonneg _
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    nlinarith
  lift k to ℕ using hk0
  have hm₁ : m₁ = p * k := by exact_mod_cast hk₁.symm
  have hm₂ : m₂ = q * k := by exact_mod_cast hk₂.symm
  subst hm₁ hm₂ hxs hyt
  have hu := atlasPowerGlobalMul_ne_zero (v := v) c a (p * k) (q * k) hs ht
  refine ⟨p * k + q * k, atlasPowerGlobalMul a (p * k) (q * k) s t, hu,
    isInftySection_atlasPowerGlobalMul_of_weights f E a hsI htI
      (fun z => ereal_convex_weight hp hq k (φ z) (ψ z)), ?_⟩
  have hv := sectionValue_mul (v := v) c a (p * k) (q * k) s t
  rw [sectionValue_eq_vector c a _ _ hu, sectionValue_eq_vector c a _ s hs,
    sectionValue_eq_vector c a _ t ht, ← WithTop.coe_add, ← toLex_add] at hv
  have hv' := toLex.injective (WithTop.coe_injective hv)
  refine Prod.ext ?_ ?_
  · exact hv'.symm
  · push_cast
    ring

/-- The Veronese subset of a full semigroup, as a semigroup. -/
def veroneseSemigroup {C : AdmissibleCone (m + 1)} {r : ℕ} (hr : 0 < r)
    (S : AddSubsemigroup ((Fin (m + 1) → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hfull : sourceSubset C S hS ∈ fullSemigroupLocus C) :
    AddSubsemigroup ((Fin (m + 1) → ℤ) × ℤ) where
  carrier := veroneseSet r (S : Set ((Fin (m + 1) → ℤ) × ℤ))
  add_mem' hx hy := (veroneseSubset_mem_fullSemigroupLocus hr hfull).1 _ hx _ hy

include Y hY in
/-- **Source `thm:concOko` for an arbitrary valuation `ν = v`, analytic Kähler case with rational
weights**: under `Γ(L) ∈ 𝒮'(C)` for `v`, if `φ, ψ` have analytic singularities, `θ_φ, θ_ψ` are
Kähler currents, `p, q ∈ ℤ_{>0}`, `t = p/(p+q)` and `χ = tφ + (1-t)ψ` (psh with positive mass),
then `Δ_ν(θ, χ) ⊇ tΔ_ν(θ, φ) + (1-t)Δ_ν(θ, ψ)`. -/
theorem partialBody_convexComb_superset_of_analytic [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : HasManifoldAnalyticSingularityType (n := m + 1) φ)
    (hψ : IsKahlerCurrentPotential (H.curvature a) ψ)
    (hψan : HasManifoldAnalyticSingularityType (n := m + 1) ψ)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hχ : IsThetaPshPotential (H.curvature a).val (fun z =>
      (((p : ℝ) / (p + q) : ℝ) : EReal) * φ z + (((q : ℝ) / (p + q) : ℝ) : EReal) * ψ z))
    (hmass : letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) _ hχ) :
    ((p : ℝ) / (p + q)) • SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a C φ +
        ((q : ℝ) / (p + q)) • SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a C ψ ⊆
      SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a C (fun z =>
        (((p : ℝ) / (p + q) : ℝ) : EReal) * φ z + (((q : ℝ) / (p + q) : ℝ) : EReal) * ψ z) := by
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set χ : SchemeComplexPoint f → EReal := fun z =>
    (((p : ℝ) / (p + q) : ℝ) : EReal) * φ z + (((q : ℝ) / (p + q) : ℝ) : EReal) * ψ z with hχdef
  have hN : 0 < p + q := by omega
  have hNR : (0 : ℝ) < ((p + q : ℕ) : ℝ) := by exact_mod_cast hN
  set A := SGPT.Okounkov.ValGen.inftySemigroup f E a c v φ with hAdef
  set B := SGPT.Okounkov.ValGen.inftySemigroup f E a c v ψ with hBdef
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hψθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hψ
  have hAC := SGPT.Okounkov.ValGen.inftySemigroup_le_cone f E a H c v hS hφθ
  have hBC := SGPT.Okounkov.ValGen.inftySemigroup_le_cone f E a H c v hS hψθ
  obtain ⟨hfullA, -, -⟩ := SGPT.Okounkov.ValGen.inftySemigroup_mem_fullSemigroupLocus f E Y hY a H
    c v hS hG hφ hφan
  obtain ⟨hfullB, -, -⟩ := SGPT.Okounkov.ValGen.inftySemigroup_mem_fullSemigroupLocus f E Y hY a H
    c v hS hG hψ hψan
  let VA := veroneseSemigroup hp A hAC hfullA
  let VB := veroneseSemigroup hq B hBC hfullB
  have hVAgen : AddSubgroup.closure (VA : Set ((Fin (m + 1) → ℤ) × ℤ)) = ⊤ :=
    (veroneseSubset_mem_fullSemigroupLocus hp hfullA).2
  have hVBgen : AddSubgroup.closure (VB : Set ((Fin (m + 1) → ℤ) × ℤ)) = ⊤ :=
    (veroneseSubset_mem_fullSemigroupLocus hq hfullB).2
  have hdegA : ∀ z ∈ VA, 0 ≤ z.2 := by
    intro z hz
    have h := inftySemigroup_degree_nonneg f E c v a φ _ hz
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    change 0 ≤ (p : ℤ) * z.2 at h
    nlinarith
  have hdegB : ∀ z ∈ VB, 0 ≤ z.2 := by
    intro z hz
    have h := inftySemigroup_degree_nonneg f E c v a ψ _ hz
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    change 0 ≤ (q : ℤ) * z.2 at h
    nlinarith
  have h0A : (0 : (Fin (m + 1) → ℤ) × ℤ) ∈ VA := by
    change ((0 : (Fin (m + 1) → ℤ) × ℤ).1, (p : ℤ) * (0 : (Fin (m + 1) → ℤ) × ℤ).2) ∈ A
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, Prod.mk_zero_zero]
    exact zero_mem_inftySemigroup f E c v a φ
  have h0B : (0 : (Fin (m + 1) → ℤ) × ℤ) ∈ VB := by
    change ((0 : (Fin (m + 1) → ℤ) × ℤ).1, (q : ℤ) * (0 : (Fin (m + 1) → ℤ) × ℤ).2) ∈ B
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, Prod.mk_zero_zero]
    exact zero_mem_inftySemigroup f E c v a ψ
  -- the degreewise sums
  let W : AddSubsemigroup ((Fin (m + 1) → ℤ) × ℤ) :=
    { carrier := {z | ∃ (x y : Fin (m + 1) → ℤ) (k : ℤ), (x, k) ∈ VA ∧ (y, k) ∈ VB ∧
        z = (x + y, k)}
      add_mem' := by
        rintro _ _ ⟨x, y, k, hx, hy, rfl⟩ ⟨x', y', k', hx', hy', rfl⟩
        refine ⟨x + x', y + y', k + k', VA.add_mem hx hx', VB.add_mem hy hy', ?_⟩
        refine Prod.ext ?_ rfl
        change x + y + (x' + y') = x + x' + (y + y')
        abel }
  set Γχ := AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a χ with hΓχ
  have hΓχC := SGPT.Okounkov.ValGen.multiplierSectionSet_subset_cone f E a c v hS χ
  have hΓ := SGPT.Okounkov.ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_mass f E Y hY a
    H c v hS hG hχ hmass
  have hWΓ : (W : Set ((Fin (m + 1) → ℤ) × ℤ)) ⊆ veroneseSet (p + q) Γχ := by
    rintro _ ⟨x, y, k, hx, hy, rfl⟩
    exact SGPT.Okounkov.ValGen.inftySectionSet_subset_multiplierSectionSet f E a H c v hχ
      (veroneseSet_inftySemigroup_add_mem f E c v a hp hq x y k hx hy)
  have hWC : W ≤ latticePoints (veroneseCone C hN).cone := fun z hz =>
    veroneseSet_subset_latticePoints hN hΓχC (hWΓ hz)
  have hWgen : LatticeSlices.generatedGroup W = ⊤ :=
    closure_degreeSum_eq_top VA VB hVAgen hVBgen hdegA hdegB W
      (fun x y k hx hy => ⟨x, y, k, hx, hy, rfl⟩)
  have hWfull := sourceSubset_mem_fullSemigroupLocus (veroneseCone C hN) W hWC hWgen
  -- the Veronese of `Γ(θ, χ)` and its body
  have hΓN := veroneseSubset_mem_almostSemigroupLocus hN hΓ
  have hmono := SGPT.AlmostSemigroup.OkounkovComparison.bodyExtension_mono
    (fullToAlmost (⟨_, hWfull⟩ : FullSemigroup (veroneseCone C hN)))
    ⟨veroneseSubset hN (SGPT.Okounkov.ValGen.multiplierConeSubset f E a c v hS χ), hΓN⟩ hWΓ
  rw [bodyExtension_source] at hmono
  have hset := setBody_veroneseSet hN hΓχC hΓ
  -- `p Δ(A) + q Δ(B) ⊆ (p + q) Δ_ν(θ, χ)`
  have hbodyVA : body VA = (p : ℝ) • body A :=
    SGPT.Okounkov.AlgebraicBody.body_eq_smul_of_veronese A VA hp (fun x k => Iff.rfl)
  have hbodyVB : body VB = (q : ℝ) • body B :=
    SGPT.Okounkov.AlgebraicBody.body_eq_smul_of_veronese B VB hq (fun x k => Iff.rfl)
  have hadd := SGPT.Okounkov.AlgebraicBody.body_add_subset_of_mul VA VB W h0A h0B hdegA hdegB
    (fun x y k hx hy => ⟨x, y, k, hx, hy, rfl⟩)
  rw [hbodyVA, hbodyVB] at hadd
  have hkey : ∀ x ∈ body A, ∀ y ∈ body B,
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ((p : ℝ) • x + (q : ℝ) • y) ∈
        ((p + q : ℕ) : ℝ) • SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a C χ := by
    intro x hx y hy
    have h1 : (p : ℝ) • x + (q : ℝ) • y ∈ body W :=
      hadd ⟨_, Set.smul_mem_smul_set hx, _, Set.smul_mem_smul_set hy, rfl⟩
    have h2 := hmono ⟨_, h1, rfl⟩
    have h3 : (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ((p : ℝ) • x + (q : ℝ) • y) ∈
        SGPT.Okounkov.ValGen.setBody (veroneseCone C hN) (veroneseSet (p + q) Γχ) := by
      rw [SGPT.Okounkov.ValGen.setBody_eq (veroneseSet_subset_latticePoints hN hΓχC) hΓN]
      exact h2
    rw [hset] at h3
    exact h3
  rw [partialBody_eq_euclideanBody_inftySemigroup f E Y hY c v a H hS hG hφ hφan,
    partialBody_eq_euclideanBody_inftySemigroup f E Y hY c v a H hS hG hψ hψan]
  rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, _, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨w, hw, hNw⟩ := Set.mem_smul_set.mp (hkey x hx y hy)
  convert hw using 1
  have hNR' : ((p + q : ℕ) : ℝ) ≠ 0 := hNR.ne'
  have hw' : w = (((p + q : ℕ) : ℝ))⁻¹ •
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ((p : ℝ) • x + (q : ℝ) • y) := by
    rw [← hNw, smul_smul, inv_mul_cancel₀ hNR', one_smul]
  rw [hw', map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul]
  congr 2 <;> push_cast <;> field_simp

end Analytic

end SGPT.Okounkov.ValGen2
