import SGPT.Checks.Comparison.BJExistGrid
import SGPT.Checks.Comparison.BJExistPackage
import SGPT.Checks.Comparison.BJExistComponents

/-!
# `cor:testcurvegivepshme`, existence: `Γ^An` is a psh metric

Source: `chapter_NApotential.tex`, `cor:testcurvegivepshme` (*The algebraic setting*): for
`Γ ∈ PSH^NA(X, θ)`, the function `Γ^An` of `def:Gammaana` admits a (unique) extension to
`PSH(L^An)`. Here the existence part: the formula `eq:psiandef` evaluated at every point of `X^An`,
`Γ^An(v) = sup_{τ < Γ_max} (Γ^{θ+ω}_τ{}^{An}(v) + τ)` (`naPotentialAnAt`), lies in `PSH(L^An)`
(`def:BJpshmetric`, `IsModuleTopologyPSH`).

## Formal setting

As in `SGPT.Checks.Comparison.BJAsmVarphian` (`lma:varphian`): `X` is an integral scheme, projective and
smooth of relative dimension `n` over `ℂ`, with a closed projective embedding `E`; `X(ℂ)` carries a
Borel measurable structure and is compact and connected (the standing hypotheses of
`SourceNAPotential`). `L = m⁻¹ [M]` for an algebraic line bundle `M` with atlas `b` and smooth metric
`h_M`, and the closed `(1,1)`-form `θ` of the non-Archimedean potential is `c₁(L, h) =
m⁻¹ c₁(M, h_M)` (equal coefficients in every chart). `Γ : SourceNAPotential θ` and `ω` is any Kähler
index.

## Proof

The book combines `prop:PhiinducePSH` (positive mass: complexification and Siu's theorem on
`X × Δ`) with `prop:BJdecseqstab` (decreasing stability, `[BJ22, (PSH2)]`, proved for unibranch
`X` by Fang–Han–Xia). Neither is used here. Instead, with `H = 𝒪_X(1)` and its Fubini–Study form
`ω_FS`, `q = 2^a` and `ε_a = (2 m q)⁻¹`:

1. The component `Γ^{θ + ε_a ω_FS}` has slices `Γ^{(a)}_t ∈ PSH(X, θ + ε_a ω_FS)` and a limit
   `Γ^{(a)}_{-∞} = usc sup_t Γ^{(a)}_t` in the same class; `m q Γ^{(a)}_t` lies in
   `PSH(X, c₁(𝒪_X(1) ⊗ M^{⊗ q}) - ½ ω_FS)` (`isThetaPshPotential_componentTwist`).
2. Siu's uniform global generation (`exists_sections_algebraization_eq`, threshold `k₀(a)`
   independent of the potential) and GAGA give, at the common level `J_a = m q K_a`
   (`K_a = 2^{Σ_{i ≤ a} k₀(i)}`), finitely many sections of `(𝒪_X(1) ⊗ M^{⊗ q})^{⊗ K_a}` whose zero
   ideals generate `alg 𝓘(J_a Γ^{(a)}_t)` for **every** grid slice and for the limit.
3. Corresponding slices (and the limits) of different components have the same multiplier ideals
   (`𝓘`-projections), so all these ideals are those of the fixed component `Γ^{θ+ω}`.
4. The upper dyadic grid maximum
   `D_a = max (-J_a⁻¹ v(𝓘(J_a Γ_{-∞})) - a, max_{-a ≤ k/2^a < Γ_max} (-J_a⁻¹ v(𝓘(J_a Γ_{k/2^a})) + (k+1)/2^a))`
   is a rational GF function of class `(m q)⁻¹ [𝒪_X(1) ⊗ M^{⊗ q}] = L + (m 2^a)⁻¹ H`
   (`exists_package_of_weighted_families`). Subadditivity of multiplier ideals along the
   multiplicative chain `J_a | J_{a+1}` and the monotonicity of the slices make `D_a` decrease,
   and `inf_a D_a = Γ^An` (`SGPT.Checks.Comparison.BJExistGrid`).
5. `isModuleTopologyPSH_of_antitone_seq` concludes; `Γ^An(v_triv) = Γ_max ≠ -∞`.

## Main results

* `siuThreshold`, `siuPower`, `siuLevel`: the common Siu levels `k₀(a)`, `K_a`, `J_a`.
* `gridSlice`, `gridTail`: the approximants `-J_a⁻¹ v(𝓘(J_a Γ_t))`, `-J_a⁻¹ v(𝓘(J_a Γ_{-∞}))`;
  `antitone_gridApprox_component`, `iInf_gridApprox_component`: their grid maxima decrease to
  `Γ^An`.
* `exists_gridPackage`: the grid maximum at level `a` is a rational GF function of class
  `L + (m 2^a)⁻¹ H`.
* `naPotentialAnAt_isModuleTopologyPSH`: **existence clause of `cor:testcurvegivepshme`**.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.Exist

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult SGPT.NAPotential.FSPos
open SGPT.NAPotential.Berkovich.BJSections
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance existCurveProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance existCurvePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance existCurvePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance existCurvePointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- `-J⁻¹ v(𝓘(Jφ))`. -/
def approxVal (φ : SchemeComplexPoint f → EReal) (J : ℕ) (v : BerkovichPoint f) : EReal :=
  -(((v.multiplierIdealVal n E φ J / J : ℝ≥0∞)) : EReal)

theorem approxVal_nonpos (φ : SchemeComplexPoint f → EReal) (J : ℕ) (v : BerkovichPoint f) :
    approxVal f n E φ J v ≤ 0 := by
  unfold approxVal
  rw [EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

/-- `φ^An(v) ≤ -J⁻¹ v(𝓘(Jφ))` (Fekete). -/
theorem potentialAn_le_approxVal {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm n (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    {J : ℕ} (hJ : 0 < J) (v : BerkovichPoint f) :
    potentialAn n E φ v ≤ approxVal f n E φ J v := by
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  unfold potentialAn approxVal
  rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff,
    BerkovichPoint.potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E hA hφ v]
  exact le_iSup₂_of_le J hJ le_rfl

/-- `φ ≤ ψ ⟹ -J⁻¹ v(𝓘(Jφ)) ≤ -J⁻¹ v(𝓘(Jψ))`. -/
theorem approxVal_mono {φ ψ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm n (SchemeComplexPoint f) 2} (hψ : IsThetaPshPotential θ ψ)
    (hle : ∀ x, φ x ≤ ψ x) {J : ℕ} (hJ : 0 < J) (v : BerkovichPoint f) :
    approxVal f n E φ J v ≤ approxVal f n E ψ J v := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  unfold approxVal
  rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine ENNReal.div_le_div_right ?_ _
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  exact v.idealVal_antitone (algebraization_mono f n E (multiplierIdeal_mono hψ.1 hle hJ'))

/-- Along a multiplicative chain, `-J⁻¹ v(𝓘(Jφ))` decreases. -/
theorem approxVal_mul_le {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm n (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    {J : ℕ} (hJ : 0 < J) {t : ℕ} (ht : 0 < t) (v : BerkovichPoint f) :
    approxVal f n E φ (t * J) v ≤ approxVal f n E φ J v := by
  unfold approxVal
  rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  exact multiplierIdealVal_div_le f n E hφ v hJ t ht

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-! ### The common Siu levels -/

section Levels

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)

/-- Siu's threshold for `𝒪_X(1) ⊗ M^{⊗ 2^a}` with the margin `½ ω_FS` (it does not depend on the
potential). -/
def siuThreshold (a : ℕ) : ℕ :=
  Classical.choose (exists_sections_algebraization_eq f n E (twistAtlas f E b (2 ^ a))
    (twistMetric f n E b HM (2 ^ a)) (fsBackground f n E) (one_half_pos : (0 : ℝ) < 1 / 2))

theorem siuThreshold_spec (a : ℕ) :
    ∀ k : ℕ, siuThreshold f n E b HM a ≤ k → ∀ ψ : SchemeComplexPoint f → EReal,
      IsThetaPshPotential ((twistMetric f n E b HM (2 ^ a)).curvature (twistAtlas f E b (2 ^ a)) -
        ((1 : ℝ) / 2) • (fsBackground f n E).form).val ψ →
      ∃ (ι : Type) (_ : Fintype ι) (σ : ι → bundlePowerGlobalSections
          (bundleTensor (hyperplaneBundle E) (bundleTensorPower M (2 ^ a))) k),
        algebraization f n E (multiplierIdeal (n := n) (k : ℝ) ψ) =
          ⨆ i, sectionZeroIdealSheaf ((twistAtlas f E b (2 ^ a)).tensorPower k) (σ i) :=
  Classical.choose_spec (exists_sections_algebraization_eq f n E (twistAtlas f E b (2 ^ a))
    (twistMetric f n E b HM (2 ^ a)) (fsBackground f n E) (one_half_pos : (0 : ℝ) < 1 / 2))

/-- `K_a = 2^{Σ_{i ≤ a} k₀(i)}`. -/
def siuPower (a : ℕ) : ℕ := 2 ^ ∑ i ∈ Finset.range (a + 1), siuThreshold f n E b HM i

/-- The common level `J_a = m 2^a K_a`. -/
def siuLevel (m a : ℕ) : ℕ := m * 2 ^ a * siuPower f n E b HM a

theorem siuThreshold_le_siuPower (a : ℕ) : siuThreshold f n E b HM a ≤ siuPower f n E b HM a :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le (siuThreshold f n E b HM i))
    (Finset.self_mem_range_succ a)).trans (Nat.lt_two_pow_self).le

theorem siuPower_pos (a : ℕ) : 0 < siuPower f n E b HM a := Nat.two_pow_pos _

theorem siuLevel_pos {m : ℕ} (hm : 0 < m) (a : ℕ) : 0 < siuLevel f n E b HM m a :=
  Nat.mul_pos (Nat.mul_pos hm (Nat.two_pow_pos a)) (siuPower_pos f n E b HM a)

theorem siuLevel_succ (m a : ℕ) : siuLevel f n E b HM m (a + 1) =
    (2 * 2 ^ siuThreshold f n E b HM (a + 1)) * siuLevel f n E b HM m a := by
  simp only [siuLevel, siuPower, Finset.sum_range_succ (fun i => siuThreshold f n E b HM i) (a + 1),
    pow_add, pow_succ]
  ring

theorem siuLevel_strictMono {m : ℕ} (hm : 0 < m) : StrictMono (siuLevel f n E b HM m) := by
  refine strictMono_nat_of_lt_succ fun a => ?_
  rw [siuLevel_succ]
  have : 2 ≤ 2 * 2 ^ siuThreshold f n E b HM (a + 1) := by
    have := Nat.two_pow_pos (siuThreshold f n E b HM (a + 1)); omega
  have := siuLevel_pos f n E b HM hm a
  nlinarith

end Levels

/-! ### The grid approximants of `Γ^An` -/

section Grid

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- `t ↦ -J_a⁻¹ v(𝓘(J_a Γ^{θ+ω}_t))` for `t < Γ_max` (and `-∞` otherwise). -/
def gridSlice (J : ℕ → ℕ) (Γ : SourceNAPotential θ) (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (v : BerkovichPoint f) (a : ℕ) (t : ℝ) : EReal :=
  if h : t < (Γ.component ω).val.max then
    approxVal f n E ((Γ.component ω).val.potential ⟨t, h⟩) (J a) v else ⊥

/-- `-J_a⁻¹ v(𝓘(J_a Γ^{θ+ω}_{-∞}))` for the limit `Γ_{-∞} = usc sup_t Γ_t`. -/
def gridTail (J : ℕ → ℕ) (Γ : SourceNAPotential θ) (ω : SourceKahlerForm n (SchemeComplexPoint f))
    (v : BerkovichPoint f) (a : ℕ) : EReal :=
  approxVal f n E (sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata) (J a) v

theorem component_potential_le_limit (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (τ : Iio (Γ.component ω).val.max)
    (x : SchemeComplexPoint f) :
    (Γ.component ω).val.potential τ x ≤
      sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata x :=
  (le_iSup (fun j => (Γ.component ω).val.potential j x) τ).trans
    (SGPT.Foundations.Analysis.FirstPass.le_uscRegularization
      (fun y => ⨆ j, (Γ.component ω).val.potential j y) x)

variable {J : ℕ → ℕ} (hJpos : ∀ a, 0 < J a) (hJsucc : ∀ a, ∃ t, 0 < t ∧ J (a + 1) = t * J a)

include hJpos hJsucc in
/-- The grid approximants decrease. -/
theorem antitone_gridApprox_component (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    Antitone (gridApprox (gridSlice f n E J Γ ω v) (gridTail f n E J Γ ω v)
      (Γ.component ω).val.max) := by
  have hP := fun τ => (Γ.component ω).val.native_thetaPSH τ
  have hPlim := (isThetaPSH_iff_nativeThetaPotential _ _).mp (Γ.component ω).val.limit_thetaPSH
  refine antitone_gridApprox (fun a t ht => ?_) (fun a s t hst ht => ?_) (fun a t ht => ?_)
    (fun a => ?_)
  · simp only [gridSlice, gridTail, dif_pos ht]
    exact approxVal_mono f n E hPlim (component_potential_le_limit f n Γ ω _) (hJpos a) v
  · simp only [gridSlice, dif_pos ht, dif_pos (hst.trans_lt ht)]
    exact approxVal_mono f n E (hP _) (fun x => (Γ.component ω).val.antitone x hst) (hJpos a) v
  · simp only [gridSlice, dif_pos ht]
    obtain ⟨c, hc, hJ⟩ := hJsucc a
    rw [hJ]
    exact approxVal_mul_le f n E (hP _) (hJpos a) hc v
  · simp only [gridTail]
    obtain ⟨c, hc, hJ⟩ := hJsucc a
    rw [hJ]
    exact approxVal_mul_le f n E hPlim (hJpos a) hc v

include hJpos in
/-- The grid approximants converge to `Γ^An` (`eq:psiandef`). -/
theorem iInf_gridApprox_component (hJmono : StrictMono J) (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    ⨅ a, gridApprox (gridSlice f n E J Γ ω v) (gridTail f n E J Γ ω v)
      (Γ.component ω).val.max a = naPotentialAnAt n E Γ ω v := by
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  have hP := fun τ => (Γ.component ω).val.native_thetaPSH τ
  have hPlim := (isThetaPSH_iff_nativeThetaPotential _ _).mp (Γ.component ω).val.limit_thetaPSH
  let A : ℝ → EReal := fun t => if h : t < (Γ.component ω).val.max then
    potentialAn n E ((Γ.component ω).val.potential ⟨t, h⟩) v else ⊥
  rw [iInf_gridApprox (F := gridSlice f n E J Γ ω v) (Flim := gridTail f n E J Γ ω v)
    (A := A) (fun a t ht => ?_) (fun a t ht => ?_) (fun a s t hst ht => ?_)
    (fun t ht => ?_) (fun a t ht => ?_) (fun a => approxVal_nonpos f n E _ _ v)]
  · unfold naPotentialAnAt
    refine iSup_congr fun τ => ?_
    simp only [A]
    rw [dif_pos (show (τ : ℝ) < (Γ.component ω).val.max from τ.2)]
  · simp only [A, gridSlice, dif_pos ht]
    exact potentialAn_le_approxVal f n E (hP _) (hJpos a) v
  · simp only [gridSlice, gridTail, dif_pos ht]
    exact approxVal_mono f n E hPlim (component_potential_le_limit f n Γ ω _) (hJpos a) v
  · simp only [gridSlice, dif_pos ht, dif_pos (hst.trans_lt ht)]
    exact approxVal_mono f n E (hP _) (fun x => (Γ.component ω).val.antitone x hst) (hJpos a) v
  · simp only [gridSlice, A, dif_pos ht]
    have h := (BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic n E hA
      (hP ⟨t, ht⟩) v).comp hJmono.tendsto_atTop
    exact ((continuous_neg.comp continuous_coe_ennreal_ereal).tendsto _).comp h
  · simp only [gridSlice, dif_pos ht]
    exact approxVal_nonpos f n E _ _ v

end Grid

/-! ### The grid approximants are rational GF functions of class `L + (m 2^a)⁻¹ H` -/

section Package

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **The level-`a` package.** For `Γ ∈ PSH^NA(X, θ)` and every `a`, the upper grid maximum
`D_a` (`gridApprox`) of `Γ^An` at the common Siu level `J_a` is a rational GF function of class
`L + (m 2^a)⁻¹ H`. -/
theorem exists_gridPackage (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (a : ℕ) :
    ∃ D : RationalGFPackage X, D.picardClass = (m : ℚ)⁻¹ • rationalPicardClass b +
        (1 / ((m * 2 ^ a : ℕ) : ℚ)) • rationalPicardClass (hyperplaneAtlas E) ∧
      ∀ v : BerkovichPoint f, D.eval f v =
        gridApprox (gridSlice f n E (siuLevel f n E b HM m) Γ ω v)
          (gridTail f n E (siuLevel f n E b HM m) Γ ω v) (Γ.component ω).val.max a := by
  classical
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  let T : ℝ := (Γ.component ω).val.max
  let Plim : SchemeComplexPoint f → EReal :=
    sourceTestCurveLimit (Γ.component ω).val.toSourceTestCurvePredata
  have hPlim := (isThetaPSH_iff_nativeThetaPotential _ _).mp (Γ.component ω).val.limit_thetaPSH
  let K := siuPower f n E b HM a
  let J := siuLevel f n E b HM m a
  have hKpos : 0 < K := siuPower_pos f n E b HM a
  have hJpos : 0 < J := siuLevel_pos f n E b HM hm a
  -- the Kähler index `(2 m 2^a)⁻¹ ω_FS`
  let ωa : SourceKahlerForm n (SchemeComplexPoint f) :=
    scaledFSIndex f n E (twistScale_pos hm (Nat.two_pow_pos a))
  have hmax : (Γ.component ωa).val.max = T := Γ.component_max_eq _ _
  -- Siu sections at level `a` for every potential in the class of the component at `ωa`
  have hsiu : ∀ φ : SchemeComplexPoint f → EReal,
      (ofFixedModel n (SchemeComplexPoint f)).IsThetaPSH (sourceNAComponentBackground θ ωa) φ →
      ∃ (ι : Type) (_ : Fintype ι) (σ : ι → bundlePowerGlobalSections
          (bundleTensor (hyperplaneBundle E) (bundleTensorPower M (2 ^ a))) K),
        algebraization f n E (multiplierIdeal (n := n) ((J : ℕ) : ℝ) φ) =
          ⨆ i, sectionZeroIdealSheaf ((twistAtlas f E b (2 ^ a)).tensorPower K) (σ i) := by
    intro φ hφ
    obtain ⟨ι, hι, σ, hσ⟩ := siuThreshold_spec f n E b HM a K
      (siuThreshold_le_siuPower f n E b HM a) _
      (isThetaPshPotential_componentTwist f n E b HM hm (Nat.two_pow_pos a) hθ hφ)
    refine ⟨ι, hι, σ, ?_⟩
    rw [← hσ, multiplierIdeal_coe_mul (by exact_mod_cast hKpos)
      (by exact_mod_cast Nat.mul_pos hm (Nat.two_pow_pos a))]
    congr 2
    simp only [J, K, siuLevel]
    push_cast
    ring
  -- the reference potentials of the families
  let refPot : Option (gridIndex T a) → SchemeComplexPoint f → EReal := fun g =>
    Option.elim g Plim fun k => (Γ.component ω).val.potential
      ⟨((k : ℤ) : ℝ) / 2 ^ a, (mem_gridIndex.mp k.2).2⟩
  have hfam : ∀ g : Option (gridIndex T a), ∃ (ι : Type) (_ : Fintype ι)
      (σ : ι → bundlePowerGlobalSections
          (bundleTensor (hyperplaneBundle E) (bundleTensorPower M (2 ^ a))) K),
      ∀ v : BerkovichPoint f, v.idealVal
          (⨆ i, sectionZeroIdealSheaf ((twistAtlas f E b (2 ^ a)).tensorPower K) (σ i)) =
        v.multiplierIdealVal n E (refPot g) J := by
    intro g
    have hJR : (0 : ℝ) < ((J : ℕ) : ℝ) := by exact_mod_cast hJpos
    cases g with
    | none =>
      obtain ⟨ι, hι, σ, hσ⟩ := hsiu _ (Γ.component ωa).val.limit_thetaPSH
      refine ⟨ι, hι, σ, fun v => ?_⟩
      rw [← hσ, multiplierIdeal_component_limit_eq f n Γ ω ωa hJR]
      rfl
    | some k =>
      have hk := (mem_gridIndex.mp k.2).2
      have hk' : ((k : ℤ) : ℝ) / 2 ^ a < (Γ.component ωa).val.max := by rw [hmax]; exact hk
      obtain ⟨ι, hι, σ, hσ⟩ := hsiu _ ((Γ.component ωa).val.thetaPSH ⟨_, hk'⟩)
      refine ⟨ι, hι, σ, fun v => ?_⟩
      rw [← hσ, multiplierIdeal_component_potential_eq f n Γ ω ωa _ hk hk' hJR]
      rfl
  choose ι hι σ hσ using hfam
  -- the weights: `(k+1)/2^a` on the grid, `-a` on the tail
  let w : Option (gridIndex T a) → ℚ := fun g =>
    Option.elim g (-(a : ℚ)) fun k => (((k : ℤ) : ℚ) + 1) / 2 ^ a
  -- nondegeneracy of the tail family at `v_triv`
  have h₀ : (BerkovichPoint.trivial f).idealVal (⨆ i, sectionZeroIdealSheaf
      ((twistAtlas f E b (2 ^ a)).tensorPower K) (σ none i)) ≠ ⊤ := by
    rw [hσ none]
    change (BerkovichPoint.trivial f).multiplierIdealVal n E Plim J ≠ ⊤
    have htriv : potentialAn n E Plim (BerkovichPoint.trivial f) = 0 :=
      Berkovich.potentialAn_trivial hA hPlim
    have hle := potentialAn_le_approxVal f n E hPlim hJpos (BerkovichPoint.trivial f)
    rw [htriv] at hle
    have h0 : (BerkovichPoint.trivial f).multiplierIdealVal n E Plim J / (J : ℝ≥0∞) = 0 := by
      have h1 : (((BerkovichPoint.trivial f).multiplierIdealVal n E Plim J /
          (J : ℝ≥0∞) : ℝ≥0∞) : EReal) ≤ 0 := by
        have := EReal.neg_le_neg_iff.mpr hle
        simpa [approxVal] using this
      exact le_antisymm (by exact_mod_cast h1) bot_le
    rw [ENNReal.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rw [h0]; exact ENNReal.zero_ne_top
    · exact absurd h0 (ENNReal.natCast_ne_top _)
  let := hι
  obtain ⟨D, hD, hDv⟩ := exists_package_of_weighted_families f (twistAtlas f E b (2 ^ a))
    hKpos hJpos σ w (BerkovichPoint.trivial f) none h₀
  refine ⟨D, ?_, fun v => ?_⟩
  · -- the class `(K/J) [𝒪_X(1) ⊗ M^{⊗ 2^a}] = L + (m 2^a)⁻¹ H`
    rw [hD]
    unfold twistAtlas
    rw [Assembly.rationalPicardClass_pairwiseTensor,
      rationalPicardClass_atlas_independent (b.tensorPower (2 ^ a)) (powerAtlas b (2 ^ a)),
      rationalPicardClass_power, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, add_comm]
    have hKq : ((siuPower f n E b HM a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hKpos.ne'
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    congr 2
    · simp only [J, K, siuLevel]
      push_cast
      field_simp
    · simp only [J, K, siuLevel]
      push_cast
      field_simp
  · -- the package is the upper grid maximum
    rw [hDv v, iSup_option]
    unfold gridApprox
    congr 1
    · rw [hσ none v]
      change approxVal f n E Plim J v + (((-(a : ℚ) : ℚ) : ℝ) : EReal) = _
      push_cast
      rfl
    · refine iSup_congr fun k => ?_
      have hk := (mem_gridIndex.mp k.2).2
      rw [hσ (some k) v]
      change approxVal f n E ((Γ.component ω).val.potential _) J v +
        (((((k : ℤ) : ℚ) + 1) / 2 ^ a : ℚ) : ℝ) =
          gridSlice f n E (siuLevel f n E b HM m) Γ ω v a (((k : ℤ) : ℝ) / 2 ^ a) + _
      simp only [gridSlice]
      rw [dif_pos (show ((k : ℤ) : ℝ) / 2 ^ a < (Γ.component ω).val.max from hk)]
      push_cast
      rfl

include hm hθ in
/-- **`cor:testcurvegivepshme`, existence**: for a connected projective manifold `X`, a
`ℚ`-line bundle `L = m⁻¹ [M]` with the Hermitian metric `h_M^{1/m}`, `θ = c₁(L, h) =
m⁻¹ c₁(M, h_M)` and `Γ ∈ PSH^NA(X, θ)`, the analytification
`Γ^An(v) = sup_{τ < Γ_max} (Γ^{θ+ω}_τ{}^{An}(v) + τ)` (at any Kähler index `ω`, every `v ∈ X^An`)
lies in `PSH(L^An)`. -/
theorem naPotentialAnAt_isModuleTopologyPSH (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b) (naPotentialAnAt n E Γ ω) := by
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  choose D hDcls hDev using exists_gridPackage f n E b HM hm hθ Γ ω
  let J := siuLevel f n E b HM m
  have hJpos : ∀ a, 0 < J a := siuLevel_pos f n E b HM hm
  have hJsucc : ∀ a, ∃ t, 0 < t ∧ J (a + 1) = t * J a := fun a =>
    ⟨_, Nat.mul_pos two_pos (Nat.two_pow_pos _), siuLevel_succ f n E b HM m a⟩
  have hε : Tendsto (fun a => ((1 / ((m * 2 ^ a : ℕ) : ℚ) : ℚ) : ℝ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun a : ℕ => ((m : ℝ) * 2 ^ a)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop
        (by exact_mod_cast hm)
    refine (tendsto_inv_atTop_zero.comp h2).congr fun a => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hinf : ∀ v, ⨅ a, (D a).eval f v = naPotentialAnAt n E Γ ω v := by
    intro v
    simp only [hDev]
    exact iInf_gridApprox_component f n E hJpos (siuLevel_strictMono f n E b HM hm) Γ ω v
  have hanti : ∀ v, Antitone fun a => (D a).eval f v := by
    intro v
    simp only [hDev]
    exact antitone_gridApprox_component f n E hJpos hJsucc Γ ω v
  -- `Γ^An(v_triv) ≠ -∞`
  have hne : ∃ v, (⨅ a, (D a).eval f v) ≠ ⊥ := by
    refine ⟨BerkovichPoint.trivial f, ?_⟩
    rw [hinf]
    have hτ : (Γ.component ω).val.max - 1 < (Γ.component ω).val.max := by linarith
    have hle := le_naPotentialAnAt n E Γ ω (BerkovichPoint.trivial f) ⟨_, hτ⟩
    rw [Berkovich.potentialAn_trivial hA ((Γ.component ω).val.native_thetaPSH ⟨_, hτ⟩),
      zero_add] at hle
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
  have h := isModuleTopologyPSH_of_antitone_seq.{u} f D hε hDcls hanti hne
  have hfun : (fun v => ⨅ a, (D a).eval f v) = naPotentialAnAt n E Γ ω := funext hinf
  rwa [hfun] at h

end Package

end SGPT.NAPotential.BJ.Exist
