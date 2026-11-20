import SGPT.Okounkov.OkoNSAlgebraic
import SGPT.Foundations.Analysis.FirstPass.AnalyticPoleSet
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.Okounkov.SourceValuativeKahlerQEABarrier

/-!
# The semigroup `Γ^∞(θ, φ)` of an analytic Kähler current

Lane OKO-NS, blueprint `claude-oko-ns.tex`. Source: chapter *The theory of Okounkov bodies*,
`prop:GammaepsSp` and the first sentence of `rmk:DeltaanaW0`.

Setting of `SGPT.Okounkov.OkoNS` (`OkoNSAlgebraic`): `X` integral smooth projective of dimension
`n = m + 1` with a smooth flag `Y•` (flag valuation `ν`), `L` with atlas `a` and smooth metric
`H`, `θ = c₁(L, H)`. Let `φ ∈ PSH(X, θ)` have analytic singularities with `θ_φ` a Kähler current.

* `inftySectionSemigroup`: `Γ^∞(θ, φ) = {(ν(s), k) : s ∈ H⁰(X, L^k ⊗ 𝓘_∞(kφ)) \ {0}}`
  (`def:Okounkov:L500`) is an additive semigroup, since `𝓘_∞(kφ) 𝓘_∞(lφ) ⊆ 𝓘_∞((k+l)φ)`.
* `tendsto_normalizedCardinality_inftySection`: `k⁻ⁿ #Γ^∞_k → vol Δ_{Y•}(θ_φ)`: from above since
  `𝓘_∞(kφ) ⊆ 𝓘(kφ)`, from below since `𝓘(k q φ) ⊆ 𝓘_∞(kφ)` for `q > 1` and `k ≫ 0`
  (`lma:IandIinf`) and `vol Δ_{Y•}(θ + dd^c(qφ)) → vol Δ_{Y•}(θ_φ)` as `q → 1+`
  (the shrinking bounds of `exists_one_sub_smul_bounds`).
* **`prop:GammaepsSp`** (`inftySectionSemigroup_mem_fullSemigroupLocus`): for big `L`,
  `Γ^∞(θ, φ) ∈ 𝒮'(Δ_ν(L))` (a semigroup in the cone over `Δ_ν(L)` generating `ℤⁿ⁺¹`) and
  `vol Γ^∞(θ, φ) = (1/n!) ∫_X θ_φⁿ`.
* **`rmk:DeltaanaW0`**, first sentence (`dist_inftySection_multiplierSection_eq_zero`):
  `d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.OkoNS

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Okounkov SGPT.Okounkov.AlgPOB SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov
open SGPT.Okounkov.TranscendentalCore
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending.DiagonalMass
open scoped Topology ENNReal NNReal Pointwise

/-! ### `𝓘_∞` is multiplicative -/

/-- `k x + l x = (k + l) x` on `EReal` for natural coefficients. -/
theorem ereal_natCast_mul_add (k l : ℕ) (x : EReal) :
    (k : EReal) * x + (l : EReal) * x = ((k + l : ℕ) : EReal) * x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hklR : (0 : ℝ) < ((k + l : ℕ) : ℝ) := by exact_mod_cast Nat.add_pos_left hk l
  change ((k : ℝ) : EReal) * x + ((l : ℝ) : EReal) * x = (((k + l : ℕ) : ℝ) : EReal) * x
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hkR, EReal.coe_mul_bot_of_pos hlR,
      EReal.coe_mul_bot_of_pos hklR, EReal.bot_add]
  | top => rw [EReal.coe_mul_top_of_pos hkR, EReal.coe_mul_top_of_pos hlR,
      EReal.coe_mul_top_of_pos hklR, EReal.top_add_top]
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    push_cast
    ring

theorem logNormSq_mul' (v w : ℂ) : logNormSq (v * w) = logNormSq v + logNormSq w := by
  rw [logNormSq, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg ‖v‖), ENNReal.log_mul_add]
  rfl

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `𝓘_∞(u) · 𝓘_∞(v) ⊆ 𝓘_∞(u + v)`. -/
theorem inftyIdeal_mul_mem_add {u v : M → EReal} {x : M} {g h : M → ℂ}
    (hg : (inftyIdeal (n := n) u).mem x g) (hh : (inftyIdeal (n := n) v).mem x h) :
    (inftyIdeal (n := n) (fun y => u y + v y)).mem x (fun y => g y * h y) := by
  obtain ⟨hgh, C, hC⟩ := mem_inftyIdeal_iff_log_bound.mp hg
  obtain ⟨hhh, D, hD⟩ := mem_inftyIdeal_iff_log_bound.mp hh
  refine mem_inftyIdeal_iff_log_bound.mpr ⟨hgh.mul hhh, C + D, ?_⟩
  filter_upwards [hC, hD] with y hy hy'
  show logNormSq (g y * h y) ≤ u y + v y + ((C + D : ℝ) : EReal)
  rw [logNormSq_mul', EReal.coe_add]
  calc logNormSq (g y) + logNormSq (h y) ≤ (u y + (C : EReal)) + (v y + (D : EReal)) :=
        add_le_add hy hy'
    _ = u y + v y + ((C : EReal) + (D : EReal)) := add_add_add_comm _ _ _ _

/-- **`𝓘_∞(u) ⊆ 𝓘(u)`** (the remark after `def:Iinfty`) for a quasi-psh function `u` (the proof
of `SGPT.Trace.RestVol.inftyIdeal_le_multiplierIdeal`, a module outside the library build). -/
theorem inftyIdeal_le_multiplierIdeal' {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) :
    (SGPT.PSH.inftyIdeal (n := n) u).Le (multiplierIdeal (n := n) 1 u) := by
  intro x g hg
  obtain ⟨hgh, K, hK, hev⟩ := hg
  refine ⟨hgh, ?_⟩
  obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp hgh
  set e := (complexChartAt (n := n) x).val with he
  have hz : e x ∈ e.target := e.map_source (mem_complexChartAt_source x)
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hzO : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hz, ?_⟩
    simpa [e.left_inv (mem_complexChartAt_source x)] using hxU
  have hdon : DifferentiableOn ℂ (fun z => g (e.symm z)) (e.target ∩ e.symm ⁻¹' U) :=
    SGPT.Foundations.Analysis.FirstPass.differentiableOn_comp_chartSymm x
      (fun y hy => (hUsub hy).mdifferentiableWithinAt)
  have hsymm : ContinuousAt e.symm (e x) := e.continuousAt_symm hz
  have hsx : e.symm (e x) = x := e.left_inv (mem_complexChartAt_source x)
  have hev' : ∀ᶠ z in 𝓝 (e x),
      multiplierDensity (chartFunction u (complexChartAt (n := n) x)) 1
        (fun z => g (e.symm z)) z ≤ ENNReal.ofReal K := by
    have := hsymm.eventually (p := fun y => multiplierDensity u 1 g y ≤ ENNReal.ofReal K)
      (by rw [hsx]; exact hev)
    exact this
  have hq : QuasiPlurisubharmonicOn (chartFunction u (complexChartAt (n := n) x)) e.target :=
    hu (complexChartAt (n := n) x)
  have hev2 : ∀ᶠ z in 𝓝 (e x), z ∈ e.target ∩ e.symm ⁻¹' U ∧
      multiplierDensity (chartFunction u (complexChartAt (n := n) x)) 1
        (fun z => g (e.symm z)) z ≤ ENNReal.ofReal K :=
    (Filter.eventually_mem_set.mpr (hO.mem_nhds hzO)).and hev'
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev2
  have hBO : Metric.ball (e x) r ⊆ e.target ∩ e.symm ⁻¹' U := fun z hz => (hball z hz).1
  refine ⟨one_pos, Metric.ball (e x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    hdon.mono hBO, ?_, ?_⟩
  · exact SGPT.Foundations.Analysis.Pending.aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
      Metric.isOpen_ball (fun y hy => hq y (hBO hy).1) one_ne_zero (hdon.mono hBO).continuousOn
  · calc (∫⁻ y in Metric.ball (e x) r,
          multiplierDensity (chartFunction u (complexChartAt (n := n) x)) 1
            (fun z => g (e.symm z)) y)
        ≤ ∫⁻ _y in Metric.ball (e x) r, ENNReal.ofReal K :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun y hy => (hball y hy).2)
      _ = ENNReal.ofReal K * volume (Metric.ball (e x) r) := by
          rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

end Manifold

/-! ### Volumes of affine images -/

theorem volume_real_affine_image {k : ℕ} (K : Set (Fin k → ℝ)) (t : ℝ) (v : Fin k → ℝ) :
    volume.real ((fun x => t • x + v) '' K) = |t ^ k| * volume.real K := by
  have himg : (fun x => t • x + v) '' K = (fun x => x + v) '' (t • K) := by
    rw [← image_smul, image_image]
  rw [measureReal_def, measureReal_def, himg, image_add_right, measure_preimage_add_right,
    Measure.addHaar_smul, Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

theorem volume_real_smul_set {k : ℕ} (K : Set (Fin k → ℝ)) (t : ℝ) :
    volume.real (t • K) = |t ^ k| * volume.real K := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_smul, Module.finrank_fin_fun,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- **Volumes of `Δ_{Y•}(θ + dd^c(qφ))` as `q → 1+`**: if `θ_φ` is a Kähler current, for every
`ε > 0` there is a rational `q > 1` with `qφ ∈ PSH(X, θ)` and
`vol Δ_{Y•}(θ + dd^c(qφ)) ≥ vol Δ_{Y•}(θ_φ) - ε`. -/
theorem exists_rat_smul_volume_ge {m : ℕ} {F : OriginalFlagGeometry (m + 1)}
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 1 < q ∧ IsThetaPshPotential θ.val (fun x => ((q : ℝ) : EReal) * φ x) ∧
      volume.real (PartialBody.generalPartialBody F θ φ) - ε ≤
        volume.real (PartialBody.generalPartialBody F θ (fun x => ((q : ℝ) : EReal) * φ x)) := by
  obtain ⟨c, hcpos, x₀, y₀, -, hbd⟩ := exists_one_sub_smul_bounds (F := F) hφ
  set V := volume.real (PartialBody.generalPartialBody F θ φ) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hmR : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨β, hβ0, hβ⟩ := exists_pos_rat_lt
    (show (0 : ℝ) < min (1 / (2 * (c : ℝ))) (ε / (((m + 1 : ℕ) : ℝ) * c * V + 1)) by positivity)
  have hβR : (0 : ℝ) < β := by exact_mod_cast hβ0
  have hβ1 : (β : ℝ) < 1 / (2 * (c : ℝ)) := hβ.trans_le (min_le_left _ _)
  have hβ2 : (β : ℝ) < ε / (((m + 1 : ℕ) : ℝ) * c * V + 1) := hβ.trans_le (min_le_right _ _)
  have hcβ : (c : ℝ) * β < 1 / 2 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * c)).mp hβ1
    nlinarith
  have hcβQ : (c : ℚ) * β < 1 := by
    have h : (c : ℝ) * β < 1 := by linarith
    exact_mod_cast h
  obtain ⟨hφβ, -, hlow⟩ := hbd β hβ0 hcβQ
  set q : ℚ := (1 - β)⁻¹ with hqdef
  have hβlt1 : (β : ℝ) < 1 := by
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hcpos
    nlinarith
  have hqR : (q : ℝ) = (1 - (β : ℝ))⁻¹ := by rw [hqdef]; push_cast; ring
  have hq1β : (q : ℝ) * (1 - (β : ℝ)) = 1 := by
    rw [hqR]
    exact inv_mul_cancel₀ (by linarith)
  have hq1R : (1 : ℝ) < q := by
    rw [hqR]
    exact (one_lt_inv₀ (by linarith)).mpr (by linarith)
  have hq0 : (0 : ℚ) < q := by
    have h : (0 : ℝ) < q := by linarith
    exact_mod_cast h
  refine ⟨q, by exact_mod_cast hq1R, ?_, ?_⟩
  · have h := isThetaPshPotential_nonneg_smul hφβ (by linarith : (0 : ℝ) ≤ q)
    rwa [smul_smul, hq1β, one_smul] at h
  · have h := SGPT.GAGA.OkoClose.generalPartialBody_rat_smul (F := F) hφβ hq0
    rw [smul_smul, hq1β, one_smul] at h
    rw [h, volume_real_smul_set]
    have hcpt := (PartialBody.convex_isCompact_generalPartialBody (F := F) (by
      have h' := isThetaPshPotential_nonneg_smul hφβ (by linarith : (0 : ℝ) ≤ q)
      rwa [smul_smul, hq1β, one_smul] at h')).2
    have hcpt' := (PartialBody.convex_isCompact_generalPartialBody (F := F) hφβ).2
    -- `vol Δ((1-β)θ; φ) ≥ (1 - cβ)ⁿ vol Δ(θ; φ)`
    have hsub : (fun x => (1 - (c : ℝ) * β) • x + (β : ℝ) • y₀) ''
        PartialBody.generalPartialBody F θ φ ⊆
          PartialBody.generalPartialBody F ((1 - (β : ℝ)) • θ) φ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hlow x hx
    have hA := measureReal_mono (μ := volume) hsub hcpt'.measure_lt_top.ne
    rw [volume_real_affine_image] at hA
    have hpow : 1 + ((m + 1 : ℕ) : ℝ) * (-((c : ℝ) * β)) ≤ (1 + -((c : ℝ) * β)) ^ (m + 1) :=
      one_add_mul_le_pow (by linarith) (m + 1)
    have habs : |(1 - (c : ℝ) * β) ^ (m + 1)| = (1 - (c : ℝ) * β) ^ (m + 1) :=
      abs_of_nonneg (pow_nonneg (by linarith) _)
    rw [habs] at hA
    have hqpow : (1 : ℝ) ≤ |(q : ℝ) ^ (m + 1)| := by
      rw [abs_of_nonneg (pow_nonneg (by linarith) _)]
      exact one_le_pow₀ hq1R.le
    have hAnn : 0 ≤ volume.real (PartialBody.generalPartialBody F ((1 - (β : ℝ)) • θ) φ) :=
      measureReal_nonneg
    have hε' : ((m + 1 : ℕ) : ℝ) * c * β * V ≤ ε := by
      have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * c * V + 1)).mp hβ2
      nlinarith
    have hchain : V - ε ≤ (1 - (c : ℝ) * β) ^ (m + 1) * V := by
      have h3 : (1 + ((m + 1 : ℕ) : ℝ) * (-((c : ℝ) * β))) * V ≤
          (1 + -((c : ℝ) * β)) ^ (m + 1) * V := mul_le_mul_of_nonneg_right hpow hV0
      have h4 : (1 + -((c : ℝ) * β)) = 1 - (c : ℝ) * β := by ring
      rw [h4] at h3
      nlinarith
    calc V - ε ≤ (1 - (c : ℝ) * β) ^ (m + 1) * V := hchain
      _ ≤ volume.real (PartialBody.generalPartialBody F ((1 - (β : ℝ)) • θ) φ) := hA
      _ ≤ |(q : ℝ) ^ (m + 1)| *
          volume.real (PartialBody.generalPartialBody F ((1 - (β : ℝ)) • θ) φ) :=
        le_mul_of_one_le_left hAnn hqpow

/-! ### The algebraic setting -/

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance okoNSInftyTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoNSInftyCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoNSInftyManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- In every frame, the coefficient of a product of sections is the product of coefficients. -/
theorem sectionFrameCoefficient_atlasPowerGlobalMul {L : X.Modules} (a : LineBundleAtlas L)
    {U : X.Opens} (α : LocalBundleFrame L U) (k l : ℕ) (s : bundlePowerGlobalSections L k)
    (t : bundlePowerGlobalSections L l) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) :
    sectionFrameCoefficient f (m + 1) E α (k + l) (atlasPowerGlobalMul a k l s t) p =
      sectionFrameCoefficient f (m + 1) E α k s p * sectionFrameCoefficient f (m + 1) E α l t p := by
  have h := atlasPowerGlobalMul_anyFrame a k l α (𝟙 U) s t
  unfold sectionFrameCoefficient
  rw [show (homOfLE le_top : U ⟶ ⊤) = U.leTop from rfl, h]
  exact schemeOpenRegularFunction_mul f (m + 1) E U _ _ hp

/-- `s ∈ H⁰(L^k ⊗ 𝓘_∞(kφ))`, `t ∈ H⁰(L^l ⊗ 𝓘_∞(lφ))` give `st ∈ H⁰(L^{k+l} ⊗ 𝓘_∞((k+l)φ))`. -/
theorem isInftySection_atlasPowerGlobalMul {L : X.Modules} (a : LineBundleAtlas L)
    {φ : SchemeComplexPoint f → EReal} {k l : ℕ} {s : bundlePowerGlobalSections L k}
    {t : bundlePowerGlobalSections L l} (hs : IsInftySection f (m + 1) E φ k s)
    (ht : IsInftySection f (m + 1) E φ l t) :
    IsInftySection f (m + 1) E φ (k + l) (atlasPowerGlobalMul a k l s t) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro U α p hp
  have h := inftyIdeal_mul_mem_add (hs U α p hp) (ht U α p hp)
  have hfun : (fun y => (k : EReal) * φ y + (l : EReal) * φ y) =
      fun y => ((k + l : ℕ) : EReal) * φ y :=
    funext fun y => ereal_natCast_mul_add k l (φ y)
  rw [hfun] at h
  refine (inftyIdeal_mem_congr ?_).mp h
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' (U : Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hU.mem_nhds hp] with y hy
  exact (sectionFrameCoefficient_atlasPowerGlobalMul f E a α k l s t hy).symm

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **`Γ^∞(θ, φ)` is an additive semigroup** (`def:Okounkov:L500`). -/
def inftySectionSemigroup {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) : AddSubsemigroup ((Fin (m + 1) → ℤ) × ℤ) where
  carrier := inftySectionSet f (m + 1) E Y hY a φ
  add_mem' := by
    let := E.isSeparated
    let := E.quasiCompact
    rintro z w ⟨k, s, hs, hks, rfl⟩ ⟨l, t, ht, hlt, rfl⟩
    let ω := schemeProjectiveTNKahlerBackground f (m + 1) E
    let p := (schemeProjectiveOriginalFlagPoint f (m + 1) E ω Y hY).val
    let u := atlasPowerGlobalMul a k l s t
    have hu : u ≠ 0 := schemePointPowerGlobalMul_ne_zero f (m + 1) p a k l s t hs ht
    have hv := schemeOriginalFlagSectionVector_mul f (m + 1) E ω Y hY a k l s t hs ht
    change schemeFubiniStudySectionVector f (m + 1) E Y hY a (k + l) u hu =
      schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs +
        schemeFubiniStudySectionVector f (m + 1) E Y hY a l t ht at hv
    refine ⟨k + l, u, hu, isInftySection_atlasPowerGlobalMul f E a hks hlt, ?_⟩
    rw [hv]
    ext i <;> simp

theorem mem_inftySectionSemigroup {L : X.Modules} (a : LineBundleAtlas L)
    {φ : SchemeComplexPoint f → EReal} {z : (Fin (m + 1) → ℤ) × ℤ} :
    z ∈ inftySectionSemigroup f E Y hY a φ ↔ z ∈ inftySectionSet f (m + 1) E Y hY a φ :=
  Iff.rfl

/-- `𝓘_∞(kφ) ⊆ 𝓘(kφ)`: `Γ^∞(θ, φ) ⊆ Γ(θ, φ)`. -/
theorem inftySectionSet_subset_multiplierSectionSet {L : X.Modules} (a : LineBundleAtlas L)
    {H : SchemeLineBundleMetric f (m + 1) E L} {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    inftySectionSet f (m + 1) E Y hY a φ ⊆ multiplierSectionSet f (m + 1) E Y hY a φ := by
  let := E.isSeparated
  let := E.quasiCompact
  apply sectionValueSet_mono
  intro k s hs
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  refine Or.inr fun U α p hp => ?_
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : ManifoldQuasiPlurisubharmonic (n := m + 1) (fun x => ((k : ℝ) : EReal) * φ x) :=
    (isThetaPshPotential_nonneg_smul hφ hkR.le).1.quasiPlurisubharmonic
  have h1 := inftyIdeal_le_multiplierIdeal' hq p _ (hs U α p hp)
  refine ⟨h1.1, ?_⟩
  have h3 := (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff one_pos hkR).mp h1.2
  rw [one_mul] at h3
  exact h3

/-- **`lma:IandIinf` for sections**: if `φ` has analytic singularities and `q > 1`, then for
`k ≫ 0` every `s ∈ H⁰(X, L^k ⊗ 𝓘(k qφ))` lies in `H⁰(X, L^k ⊗ 𝓘_∞(kφ))`. -/
theorem eventually_isInftySection_of_isMultiplierSection {φ : SchemeComplexPoint f → EReal}
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) {q : ℝ} (hq : 1 < q) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ {L : X.Modules} (s : bundlePowerGlobalSections L k),
      IsMultiplierSection f (m + 1) E (fun x => (q : EReal) * φ x) k s →
        IsInftySection f (m + 1) E φ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hφan' : (VariableComplexAtlas.ofFixedModel (m + 1) (SchemeComplexPoint f)).HasRationalAnalyticChartType
      φ := fun e z hz => hφan e z hz
  obtain ⟨k₀, hk₀, hI⟩ := SGPT.PSH.MultiplierIdealInf.lma_IandIinf hφan' (ε := q - 1)
    (by linarith)
  have hq1 : (1 : ℝ) + (q - 1) = q := by ring
  refine ⟨k₀, hk₀, fun k hk L s hs => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le hk₀ hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  rcases hs with hk0 | hs
  · omega
  intro U α p hp
  have hmem := hs U α p hp
  have hmem1 : (multiplierIdeal (n := m + 1) 1 fun x =>
      (((k : ℝ) * (1 + (q - 1)) : ℝ) : EReal) * φ x).mem p
        (sectionFrameCoefficient f (m + 1) E α k s) := by
    refine ⟨hmem.1, ?_⟩
    have h := (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff hkR
      (by linarith : (0 : ℝ) < q)).mp hmem.2
    refine (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff one_pos
      (mul_pos hkR (by linarith))).mpr ?_
    rw [one_mul, hq1]
    exact h
  exact hI k hk p _ hmem1

/-! ### Counting -/

/-- Cone-independence of the normalized cardinalities of a semigroup. -/
theorem normalizedCardinality_sourceSubset_congr {n : ℕ} {C C' : AdmissibleCone n}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hS' : S ≤ latticePoints C'.cone) :
    (sourceSubset C S hS).normalizedCardinality = (sourceSubset C' S hS').normalizedCardinality := by
  funext k
  simp only [ConeSubset.normalizedCardinality, card_sourceSubset_slices]

/-- **`Γ^∞(θ, φ)` fills `Δ_{Y•}(θ_φ)`** (counting part of `prop:GammaepsSp`): for an analytic
Kähler current `θ_φ` and every cube cone `C` containing the section sets (`exists_cubeCone_contains`),
`k⁻ⁿ #Γ^∞_k(θ, φ) → vol Δ_{Y•}(θ_φ)`, the upper and lower hypotheses of the filling criterion
hold, and the normalized points of `Γ^∞(θ, φ)` lie in `Δ_{Y•}(θ_φ)`. -/
theorem inftySection_fills [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∃ hU : inftySectionSemigroup f E Y hY a φ ≤ latticePoints (cubeCone (n := m + 1) C).cone,
      (∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
        ∀ x ∈ (sourceSubset (cubeCone (n := m + 1) C) _ hU).slices k,
          ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) - ε ≤
            (sourceSubset (cubeCone (n := m + 1) C) _ hU).normalizedCardinality k) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨C₀, hC₀, hC⟩ := exists_cubeCone_contains f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC' => ?_⟩
  obtain ⟨hsubφ, -⟩ := hC C hC' φ hφθ
  have hincl := inftySectionSet_subset_multiplierSectionSet f E Y hY a hφθ
  have hU : inftySectionSemigroup f E Y hY a φ ≤ latticePoints (cubeCone (n := m + 1) C).cone :=
    fun z hz => hsubφ (hincl hz)
  refine ⟨hU, fun η hη => ?_, fun ε hε => ?_⟩
  · filter_upwards [multiplierConeSubset_upper f E Y hY a H hφθ hsubφ hη] with k hk x hx
    refine hk x ?_
    rw [ConeSubset.mem_slices] at hx ⊢
    exact hincl hx
  · obtain ⟨q, hq1, hqψ, hqvol⟩ := exists_rat_smul_volume_ge
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ (half_pos hε)
    obtain ⟨k₀, -, hlowIncl⟩ := eventually_isInftySection_of_isMultiplierSection f E hφan
      (q := (q : ℝ)) (by exact_mod_cast hq1)
    obtain ⟨hsubψ, -⟩ := hC C hC' _ hqψ
    have hl := multiplierConeSubset_lower f E Y hY a H hqψ hsubψ
      (SGPT.GAGA.H0L.dxMainLowerBound_of_smoothFlag f E Y hY a H hqψ) (half_pos hε)
    filter_upwards [hl, eventually_ge_atTop k₀] with k hk hk0
    have hslices : (multiplierConeSubset f E Y hY a _ hsubψ).slices k ⊆
        (sourceSubset (cubeCone (n := m + 1) C) _ hU).slices k := by
      intro x hx
      rw [ConeSubset.mem_slices] at hx ⊢
      obtain ⟨k', s, hs, hP, hz⟩ := hx
      simp only [Prod.mk.injEq] at hz
      obtain ⟨rfl, hkk⟩ := hz
      have hk' : k' = k := by exact_mod_cast hkk.symm
      subst hk'
      exact ⟨k', s, hs, hlowIncl k' hk0 s hP, rfl⟩
    have hmono : (multiplierConeSubset f E Y hY a _ hsubψ).normalizedCardinality k ≤
        (sourceSubset (cubeCone (n := m + 1) C) _ hU).normalizedCardinality k := by
      unfold ConeSubset.normalizedCardinality
      gcongr
    linarith

/-- The normalized points of `Γ^∞(θ, φ)` lie in `Δ_{Y•}(θ_φ)`, hence `Δ(Γ^∞(θ, φ)) ⊆ Δ_{Y•}(θ_φ)`. -/
theorem body_inftySectionSemigroup_subset [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    body (inftySectionSemigroup f E Y hY a φ) ⊆ PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ := by
  let := E.isSeparated
  let := E.quasiCompact
  set K := PartialBody.generalPartialBody
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ with hKdef
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  obtain ⟨C₀, -, hC⟩ := exists_cubeCone_contains f E Y hY a H
  obtain ⟨hsubφ, -⟩ := hC C₀ le_rfl φ hφ
  have hincl := inftySectionSet_subset_multiplierSectionSet f E Y hY a hφ
  set U := inftySectionSemigroup f E Y hY a φ with hUdef
  have hU : U ≤ latticePoints (cubeCone (n := m + 1) C₀).cone := fun z hz => hsubφ (hincl hz)
  -- multiples stay in `U`
  have hmul : ∀ z ∈ U, ∀ j : ℕ, (j + 1) • z ∈ U := by
    intro z hz j
    induction j with
    | zero => simpa using hz
    | succ j ih =>
      rw [succ_nsmul]
      exact U.add_mem ih hz
  refine AlgebraicDX.body_subset_of_normalized_mem U hKc.isClosed hKv fun z hz => ?_
  obtain ⟨k, s, hs, hks, rfl⟩ := hz
  set v : Fin (m + 1) → ℤ :=
    fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℤ) with hv
  have hzU : (v, (k : ℤ)) ∈ U := ⟨k, s, hs, hks, rfl⟩
  refine ⟨by simp, fun h0 => ?_, fun hpos => ?_⟩
  · -- degree zero: the cone forces `ν(s) = 0`
    have hzc : latticeCast (m + 1) (v, (k : ℤ)) ∈ (cubeCone (n := m + 1) C₀).cone := hU hzU
    have hk0 : (k : ℤ) = 0 := h0
    simp only [latticeCast, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hk0, Int.cast_zero] at hzc
    have h := (cubeCone (n := m + 1) C₀).zeroHeight _ hzc
    funext i
    have hi := congrFun h i
    simp only [Pi.zero_apply, Int.cast_eq_zero] at hi
    exact hi
  · have hpos' : (0 : ℤ) < (k : ℤ) := hpos
    have hkpos : 0 < k := by exact_mod_cast hpos'
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    change (((k : ℤ) : ℝ))⁻¹ • Counting.integerCast v ∈ K
    have hKcl : IsClosed K := hKc.isClosed
    rw [← hKcl.closure_eq, closure_eq_iInter_cthickening]
    refine mem_iInter₂.mpr fun η hη => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.mp (multiplierConeSubset_upper f E Y hY a H hφ hsubφ hη)
    have hj := hincl (hmul _ hzU N)
    have hsmul : (N + 1) • (v, (k : ℤ)) = ((N + 1) • v, (((N + 1) * k : ℕ) : ℤ)) := by
      refine Prod.ext ?_ ?_
      · rfl
      · show (N + 1) • (k : ℤ) = (((N + 1) * k : ℕ) : ℤ)
        rw [nsmul_eq_mul]
        push_cast
        ring
    rw [hsmul] at hj
    have hNk : N ≤ (N + 1) * k := by nlinarith
    have h := hN _ hNk ((N + 1) • v) (by rw [ConeSubset.mem_slices]; exact hj)
    have hcast : ((((N + 1) * k : ℕ) : ℝ))⁻¹ • Counting.integerCast ((N + 1) • v) =
        (((k : ℤ) : ℝ))⁻¹ • Counting.integerCast v := by
      funext i
      have hvi : ((N + 1) • v) i = ((N + 1 : ℕ) : ℤ) * v i := by
        rw [Pi.smul_apply, nsmul_eq_mul]
      have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
      rw [Pi.smul_apply, Pi.smul_apply]
      simp only [Counting.integerCast]
      rw [hvi, smul_eq_mul, smul_eq_mul]
      push_cast
      field_simp
    rwa [hcast] at h

/-- **Source `prop:GammaepsSp`** (flag valuations): let `L` be big, and let `φ ∈ PSH(X, θ)` have
analytic singularities with `θ_φ` a Kähler current. Then `Γ^∞(θ, φ) ∈ 𝒮'(Δ_ν(L))`: it is an
additive semigroup contained in the cone over the convex body `Δ_ν(L)` and generating `ℤⁿ⁺¹`
(the full semigroup locus of that cone); moreover `k⁻ⁿ #Γ^∞_k(θ, φ) → (1/n!) ∫_X θ_φⁿ`, so
`vol Γ^∞(θ, φ) = (1/n!) ∫_X θ_φⁿ` (non-pluripolar mass `diagonalPotentialMass`). -/
theorem inftySectionSemigroup_mem_fullSemigroupLocus [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hbig : IsBig f L (m + 1)) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hKc : IsCompact (lineBundleOkounkovBody f (m + 1) E Y hY a))
      (hKv : Convex ℝ (lineBundleOkounkovBody f (m + 1) E Y hY a))
      (hS : inftySectionSemigroup f E Y hY a φ ≤
        latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone),
      sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) _ hS ∈
          fullSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ∧
        Tendsto (sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) _ hS).normalizedCardinality
          atTop (𝓝 ((diagonalPotentialMass (H.curvature a) φ
            (PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ)).toReal /
              ((m + 1).factorial : ℝ))) ∧
        (sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) _ hS).volume =
          (diagonalPotentialMass (H.curvature a) φ
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
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφθ
  have hvol : 0 < volume.real K := volume_real_generalPartialBody_pos_of_kahler _ hφ
  -- counting in a cube cone
  obtain ⟨C₀, -, hC⟩ := inftySection_fills f E Y hY a H hφ hφan
  obtain ⟨C₁, -, hC1⟩ := exists_cubeCone_contains f E Y hY a H
  obtain ⟨hU, hup, hlow⟩ := hC (max C₀ C₁) (le_max_left _ _)
  obtain ⟨-, hKC⟩ := hC1 (max C₀ C₁) (le_max_right _ _) φ hφθ
  have hlim := tendsto_normalizedCardinality_of_fills (cubeCone (n := m + 1) (max C₀ C₁)) hKc hKv
    hKC _ hup hlow
  have hG := Intersection.generatedGroup_eq_top_of_full_count_limit
    (cubeCone (n := m + 1) (max C₀ C₁)) _ hU hKc
    (body_inftySectionSemigroup_subset f E Y hY a H hφθ) hvol hlim
  -- the cone over `Δ_ν(L)`
  obtain ⟨hLc, hLv, hcone⟩ :=
    SGPT.GAGA.OkoClose.multiplierConeSubset_mem_almostSemigroupLocus_coneOver f E Y hY a H hbig
  obtain ⟨hsubO, -⟩ := hcone φ hφθ hvol
  have hincl := inftySectionSet_subset_multiplierSectionSet f E Y hY a hφθ
  have hS : inftySectionSemigroup f E Y hY a φ ≤
      latticePoints (SGPT.GAGA.OkoClose.coneOver _ hLc hLv).cone :=
    fun z hz => hsubO (hincl hz)
  -- the volume
  have hmass : volume.real K =
      (diagonalPotentialMass (H.curvature a) φ hφθ).toReal / ((m + 1).factorial : ℝ) := by
    rw [hKdef, volume_real_generalPartialBody f E Y hY a H hφθ]
    congr 2
    exact SourceValuativeClosure.iVolume_eq_mass_of_kahler_analytic
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) ⟨hφθ, hφan⟩ hφ
  have hlim' : Tendsto (sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hLc hLv) _ hS).normalizedCardinality
      atTop (𝓝 (volume.real K)) := by
    rw [normalizedCardinality_sourceSubset_congr _ hS hU]
    exact hlim
  rw [hmass] at hlim'
  exact ⟨hLc, hLv, hS, sourceSubset_mem_fullSemigroupLocus _ _ hS hG, hlim', hlim'.limsup_eq⟩

/-- **Source `rmk:DeltaanaW0`, first sentence** (`eq:Gamma0Gammaanalytic`, flag valuations): if
`φ` has analytic singularities and `θ_φ` is a Kähler current, then
`d_sg(Γ^∞(θ, φ), Γ(θ, φ)) = 0` (in every large cube cone containing both). -/
theorem dist_inftySection_multiplierSection_eq_zero [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : letI := E.isSeparated; letI := E.quasiCompact;
      HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∃ (hU : inftySectionSemigroup f E Y hY a φ ≤ latticePoints (cubeCone (n := m + 1) C).cone)
        (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
          (latticePoints (cubeCone (n := m + 1) C).cone : Set _)),
        dist (sourceSubset (cubeCone (n := m + 1) C) _ hU)
          (multiplierConeSubset f E Y hY a φ hsub) = 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφθ
  obtain ⟨C₀, hC₀, hC⟩ := inftySection_fills f E Y hY a H hφ hφan
  obtain ⟨C₁, -, hC1⟩ := exists_cubeCone_contains f E Y hY a H
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀, fun C hC' => ?_⟩
  obtain ⟨hU, hup, hlow⟩ := hC C (le_of_max_le_left hC')
  obtain ⟨hsub, hKC⟩ := hC1 C (le_of_max_le_right hC') φ hφθ
  refine ⟨hU, hsub, ?_⟩
  have h1 := dist_eq_zero_of_fills (cubeCone (n := m + 1) C) hKc hKv hKC _ hup hlow
  have h2 := dist_eq_zero_of_fills (cubeCone (n := m + 1) C) hKc hKv hKC
    (multiplierConeSubset f E Y hY a φ hsub) (fun η hη => multiplierConeSubset_upper f E Y hY a H hφθ hsub hη)
    (fun ε hε => multiplierConeSubset_lower f E Y hY a H hφθ hsub
      (SGPT.GAGA.H0L.dxMainLowerBound_of_smoothFlag f E Y hY a H hφθ) hε)
  refine le_antisymm ((dist_triangle _ (sourceSubset (cubeCone (n := m + 1) C) _
    (bodyLatticeSemigroup_le (cubeCone (n := m + 1) C) hKv hKC)) _).trans ?_) dist_nonneg
  rw [h1, dist_comm, h2, add_zero]

end SGPT.Okounkov.OkoNS
