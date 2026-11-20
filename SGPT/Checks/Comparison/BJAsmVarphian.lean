import SGPT.Checks.Comparison.BJAsmSectionGF
import SGPT.Checks.Comparison.BJAsmSiu
import SGPT.IGood.DXMainTensorMetric
import SGPT.NAPotential.FSPosKahler
import SGPT.NAPotential.DivDictTrivial
import SGPT.NAPotential.GAGAMult2Limit
import SGPT.GAGA.H0SSchemeGAGA

/-!
# `lma:varphian`: analytifications of quasi-plurisubharmonic functions are psh metrics

Source: `chapter_NApotential.tex`, `lma:varphian` (*The algebraic setting*). Let `X` be a connected
projective manifold, `L` a `ℚ`-line bundle on `X` with a Hermitian metric `h`, `θ = c₁(L, h)` and
`φ ∈ PSH(X, θ)`. Then `φ^An ∈ PSH(L^An)`.

## Formal setting

`X` is an integral scheme, projective and smooth of relative dimension `n` over `ℂ`, with a closed
projective embedding `E` (so `X(ℂ)` is a connected projective manifold). A `ℚ`-line bundle with a
Hermitian metric is `L = m⁻¹ [M]` for an algebraic line bundle `M` with a smooth metric `h_M`
(`SchemeLineBundleMetric`), `h = h_M^{1/m}` and `θ = m⁻¹ c₁(M, h_M)`. `φ^An` is
`SGPT.NAPotential.Berkovich.potentialAn` (`def:NApotential:L975`) and `PSH(L^An)` is the recalled
`def:BJpshmetric` (`SGPT.NAPotential.BJ.Printed.IsModuleTopologyPSH`).

## Proof

As in the book, with the ample line bundle `H = 𝒪_X(1)` (Fubini–Study metric). The book takes a
power `H^b` with `b` independent of `k` (Siu); the workspace's Siu theorem has its curvature margin
in the line bundle, so we use `M_q = 𝒪_X(1) ⊗ M^{⊗ q}`, `q = 2^a`, whose curvature is
`ω_FS + q c₁(M, h_M)`, and `ψ = m q φ ∈ PSH(X, c₁(M_q) - ω_FS)`. For `k = 2^{c(a)} ≥ k₀(a)`,
`alg 𝓘(kψ) = alg 𝓘(J_a φ)` (`J_a = m q k`) is the sum of the zero ideals of finitely many sections
of `M_q^{⊗ k}` (`exists_sections_algebraization_eq`), so `v ↦ -J_a⁻¹ v(𝓘(J_a φ))` is a rational GF
function of class `(k/J_a)[M_q] = m⁻¹[M] + (m q)⁻¹[H] = L + (m q)⁻¹ H`
(`exists_package_of_sections`). Along `a` these functions decrease (subadditivity of multiplier
ideals) to `φ^An` (Fekete), they are finite at `v_triv`, and
`isModuleTopologyPSH_of_antitone_seq` concludes.

## Main results

* `potentialAn_isModuleTopologyPSH`: **`lma:varphian`**.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.Assembly

open Set Filter Bundle MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult SGPT.NAPotential.FSPos
open SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

/-- `𝓘(c · (dφ)) = 𝓘((cd) φ)`. -/
theorem multiplierIdeal_coe_mul {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (φ : Y → EReal) :
    multiplierIdeal (n := n) c (fun y => (d : EReal) * φ y) = multiplierIdeal (n := n) (c * d) φ := by
  have hw : ∀ t : EReal, multiplierWeight c ((d : EReal) * t) = multiplierWeight (c * d) t := by
    intro t; unfold multiplierWeight; rw [← mul_assoc, ← EReal.coe_mul]
  have hdens : ∀ (e : ComplexChart n Y) (g : ComplexModel n → ℂ),
      multiplierDensity (chartFunction (fun y => (d : EReal) * φ y) e) c g =
        multiplierDensity (chartFunction φ e) (c * d) g := by
    intro e g; funext z
    simp only [multiplierDensity, chartFunction, hw]
  ext y g
  simp only [multiplierIdeal, MultiplierIntegrableAt, WeightedL2On, hdens, hc, mul_pos hc hd,
    true_and]

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance asmVarphianPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance asmVarphianPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

section Twist

variable [IsSeparated f] [QuasiCompact f]

local instance asmVarphianPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)

/-- The atlas of `𝒪_X(1) ⊗ M^{⊗ q}` by tensor frames. -/
def twistAtlas (q : ℕ) :
    LineBundleAtlas (bundleTensor (hyperplaneBundle E) (bundleTensorPower M q)) :=
  pairwiseTensorAtlas (hyperplaneAtlas E) (b.tensorPower q)

/-- The product metric `h_FS ⊗ h_M^q` on `𝒪_X(1) ⊗ M^{⊗ q}`. -/
def twistMetric (q : ℕ) :
    SchemeLineBundleMetric f n E (bundleTensor (hyperplaneBundle E) (bundleTensorPower M q)) :=
  (fubiniStudyMetric f E n).tensorProduct (HM.tensorPower b q) (hyperplaneAtlas E)
    (b.tensorPower q)

/-- The Kähler background `ω_FS = c₁(𝒪_X(1), h_FS)`. -/
def fsBackground : KahlerBackground n (SchemeComplexPoint f) :=
  ⟨(fubiniStudyMetric f E n).curvature (hyperplaneAtlas E), fubiniStudy_isKahler f E n⟩

/-- `φ ∈ PSH(X, m⁻¹ c₁(M, h_M))` gives `m q φ ∈ PSH(X, c₁(𝒪_X(1) ⊗ M^q) - ω_FS)`. -/
theorem isThetaPshPotential_twist {m : ℕ} (hm : 0 < m) (q : ℕ) {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (((m : ℝ)⁻¹) • HM.curvature b).val φ) :
    IsThetaPshPotential ((twistMetric f n E b HM q).curvature (twistAtlas f E b q) -
      (1 : ℝ) • (fsBackground f n E).form).val (fun y => (((m * q : ℕ) : ℝ) : EReal) * φ y) := by
  have h0 := TranscendentalCore.isThetaPshPotential_nonneg_smul hφ
    (Nat.cast_nonneg (α := ℝ) (m * q))
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hgeq : ((((m * q : ℕ) : ℝ)) • (((m : ℝ)⁻¹) • HM.curvature b)).val.GeometricallyEq
      ((twistMetric f n E b HM q).curvature (twistAtlas f E b q) -
        (1 : ℝ) • (fsBackground f n E).form).val := by
    intro e u hu
    have h1 := (fubiniStudyMetric f E n).curvature_tensorProduct (HM.tensorPower b q)
      (hyperplaneAtlas E) (b.tensorPower q) (twistAtlas f E b q) e hu
    have h2 := HM.curvature_tensorPower b q e hu
    change ((((m * q : ℕ) : ℝ)) • (((m : ℝ)⁻¹) • HM.curvature b)).val.coeff e u =
      ((twistMetric f n E b HM q).curvature (twistAtlas f E b q) -
        (1 : ℝ) • (fsBackground f n E).form).val.coeff e u
    rw [SGPT.PSH.GlobalL2.coeff_sub_smul]
    change _ = (((fubiniStudyMetric f E n).tensorProduct (HM.tensorPower b q) (hyperplaneAtlas E)
      (b.tensorPower q)).curvature (twistAtlas f E b q)).val.coeff e u -
      (1 : ℝ) • ((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.coeff e u
    rw [h1, ClosedRealOneOneForm.coeff_add, h2, ClosedRealOneOneForm.coeff_smul,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_smul, one_smul,
      add_sub_cancel_left, smul_smul]
    congr 1
    push_cast
    field_simp
  exact (hgeq.thetaPshPotential_iff _).mp h0

end Twist

/-! ### Superadditivity along multiples -/

section Assembly

variable [IsProjective f] [IsIntegral X]

local instance asmVarphianProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance asmVarphianPointManifold' : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- `t · v(𝓘(jφ)) ≤ v(𝓘(tjφ))` for `t ≥ 1`, `j ≥ 1`. -/
theorem natCast_mul_multiplierIdealVal_le {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm n (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) {j : ℕ} (hj : 0 < j) (t : ℕ) (ht : 0 < t) :
    (t : ℝ≥0∞) * v.multiplierIdealVal n E φ j ≤ v.multiplierIdealVal n E φ (t * j) := by
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  induction t with
  | zero => exact absurd ht (lt_irrefl 0)
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with h0 | htp
    · subst h0; simp
    · calc ((t + 1 : ℕ) : ℝ≥0∞) * v.multiplierIdealVal n E φ j
          = (t : ℝ≥0∞) * v.multiplierIdealVal n E φ j + v.multiplierIdealVal n E φ j := by
            push_cast; ring
        _ ≤ v.multiplierIdealVal n E φ (t * j) + v.multiplierIdealVal n E φ j :=
            add_le_add (ih htp) le_rfl
        _ ≤ v.multiplierIdealVal n E φ (t * j + j) :=
            BerkovichPoint.multiplierIdealVal_superadditive_pos n E hA hφ v _ _
              (Nat.mul_pos htp hj) hj
        _ = v.multiplierIdealVal n E φ ((t + 1) * j) := by rw [Nat.succ_mul]

/-- `j⁻¹ v(𝓘(jφ)) ≤ (tj)⁻¹ v(𝓘(tjφ))` for `t ≥ 1`, `j ≥ 1`. -/
theorem multiplierIdealVal_div_le {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm n (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) {j : ℕ} (hj : 0 < j) (t : ℕ) (ht : 0 < t) :
    v.multiplierIdealVal n E φ j / j ≤ v.multiplierIdealVal n E φ (t * j) / ((t * j : ℕ) : ℝ≥0∞) := by
  have ht0 : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  rw [← ENNReal.mul_div_mul_left (v.multiplierIdealVal n E φ j) (j : ℝ≥0∞) ht0
    (ENNReal.natCast_ne_top t), Nat.cast_mul]
  exact ENNReal.div_le_div_right (natCast_mul_multiplierIdealVal_le f n E hφ v hj t ht) _

include E in
/-- An integral scheme of finite type over `ℂ` has a complex point. -/
theorem nonempty_schemeComplexPoint : Nonempty (SchemeComplexPoint f) := by
  have := E.locallyOfFiniteType
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
  obtain ⟨P, hP⟩ := Ideal.exists_maximal Γ(X, U)
  obtain ⟨p, -⟩ := exists_schemeComplexPoint_fromSpec f hU P hP
  exact ⟨p⟩

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)]

/-- **`lma:varphian`**, with the measurable structure and compactness of `X(ℂ)` as instances. -/
theorem potentialAn_isModuleTopologyPSH_aux {M : X.Modules} (b : LineBundleAtlas M)
    (HM : SchemeLineBundleMetric f n E M) {m : ℕ} (hm : 0 < m) {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (((m : ℝ)⁻¹) • HM.curvature b).val φ) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b) (potentialAn n E φ) := by
  classical
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint f E
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  -- Siu thresholds for the bundles `𝒪_X(1) ⊗ M^{⊗ 2^a}`
  choose k₀ hk₀ using fun a : ℕ => exists_sections_algebraization_eq f n E
    (twistAtlas f E b (2 ^ a)) (twistMetric f n E b HM (2 ^ a)) (fsBackground f n E) one_pos
  let c : ℕ → ℕ := fun a => ∑ i ∈ Finset.range (a + 1), k₀ i
  let K : ℕ → ℕ := fun a => 2 ^ c a
  let J : ℕ → ℕ := fun a => m * 2 ^ a * K a
  have hK : ∀ a, k₀ a ≤ K a := fun a =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le (k₀ i))
      (Finset.self_mem_range_succ a)).trans (Nat.lt_two_pow_self).le
  have hKpos : ∀ a, 0 < K a := fun a => Nat.two_pow_pos _
  have hJpos : ∀ a, 0 < J a := fun a => Nat.mul_pos (Nat.mul_pos hm (Nat.two_pow_pos a)) (hKpos a)
  have hJsucc : ∀ a, J (a + 1) = (2 * 2 ^ k₀ (a + 1)) * J a := by
    intro a
    simp only [J, K, c, Finset.sum_range_succ (fun i => k₀ i) (a + 1), pow_add, pow_succ]
    ring
  -- the multiplier ideals of `m 2^a φ` at level `K a` are those of `φ` at level `J a`
  have hI : ∀ a, multiplierIdeal (n := n) ((K a : ℕ) : ℝ)
      (fun y => (((m * 2 ^ a : ℕ) : ℝ) : EReal) * φ y) =
        multiplierIdeal (n := n) ((J a : ℕ) : ℝ) φ := by
    intro a
    rw [multiplierIdeal_coe_mul (by exact_mod_cast hKpos a)
      (by exact_mod_cast Nat.mul_pos hm (Nat.two_pow_pos a))]
    congr 1
    simp only [J]
    push_cast
    ring
  -- sections at level `a`
  choose ι hι σ hσ using fun a : ℕ => hk₀ a (K a) (hK a) _
    (isThetaPshPotential_twist f n E b HM hm (2 ^ a) hφ)
  -- `φ^An(v_triv) = 0`
  have htriv : potentialAn n E φ (BerkovichPoint.trivial f) = 0 :=
    Berkovich.potentialAn_trivial hA hφ
  have hP0 : (BerkovichPoint.trivial f).potentialVal n E φ = 0 := by
    have h := htriv
    unfold potentialAn at h
    have h' : (((BerkovichPoint.trivial f).potentialVal n E φ : ℝ≥0∞) : EReal) = 0 := by
      have := congrArg (fun x : EReal => -x) h
      simpa using this
    exact_mod_cast h'
  have hval0 : ∀ a, (BerkovichPoint.trivial f).multiplierIdealVal n E φ (J a) ≠ ⊤ := by
    intro a
    have hle : (BerkovichPoint.trivial f).multiplierIdealVal n E φ (J a) / (J a : ℝ≥0∞) ≤ 0 := by
      rw [← hP0, BerkovichPoint.potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E hA hφ]
      exact le_iSup₂_of_le (J a) (hJpos a) le_rfl
    have h0 := le_antisymm hle (by positivity)
    rw [ENNReal.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rw [h0]; exact ENNReal.zero_ne_top
    · exact absurd h0 (ENNReal.natCast_ne_top _)
  -- the packages
  have hpkg : ∀ a, ∃ D : RationalGFPackage X,
      D.picardClass = ((K a : ℚ) / (J a : ℚ)) • rationalPicardClass (twistAtlas f E b (2 ^ a)) ∧
      ∀ v : BerkovichPoint f, D.eval f v =
        -(((v.multiplierIdealVal n E φ (J a) / (J a : ℝ≥0∞) : ℝ≥0∞)) : EReal) := by
    intro a
    let := hι a
    have h₀ : (BerkovichPoint.trivial f).idealVal
        (⨆ i, sectionZeroIdealSheaf ((twistAtlas f E b (2 ^ a)).tensorPower (K a)) (σ a i)) ≠ ⊤ := by
      rw [← hσ a, hI a]
      exact hval0 a
    obtain ⟨D, hD, hDv⟩ := exists_package_of_sections f (twistAtlas f E b (2 ^ a)) (hKpos a)
      (hJpos a) (σ a) (BerkovichPoint.trivial f) h₀
    refine ⟨D, hD, fun v => ?_⟩
    rw [hDv v, ← hσ a, hI a]
    rfl
  choose D hDcls hDev using hpkg
  -- the classes `L + ε_a H`
  let ε : ℕ → ℚ := fun a => 1 / ((m * 2 ^ a : ℕ) : ℚ)
  have hcls : ∀ a, (D a).picardClass = (m : ℚ)⁻¹ • rationalPicardClass b +
      ε a • rationalPicardClass (hyperplaneAtlas E) := by
    intro a
    rw [hDcls a]
    unfold twistAtlas
    rw [Assembly.rationalPicardClass_pairwiseTensor,
      rationalPicardClass_atlas_independent (b.tensorPower (2 ^ a)) (powerAtlas b (2 ^ a)),
      rationalPicardClass_power, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, add_comm]
    have hKq : (K a : ℚ) ≠ 0 := by exact_mod_cast (hKpos a).ne'
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    congr 2
    · simp only [J]
      push_cast
      field_simp
    · simp only [J, ε]
      push_cast
      field_simp
  have hε : Tendsto (fun a => (ε a : ℝ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun a : ℕ => ((m : ℝ) * 2 ^ a)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop
        (by exact_mod_cast hm)
    refine (tendsto_inv_atTop_zero.comp h2).congr fun a => ?_
    simp only [ε, Function.comp_apply]
    push_cast
    ring
  -- monotonicity and the limit
  have hmono : ∀ v : BerkovichPoint f,
      Monotone fun a => v.multiplierIdealVal n E φ (J a) / (J a : ℝ≥0∞) := by
    intro v
    refine monotone_nat_of_le_succ fun a => ?_
    have h := multiplierIdealVal_div_le f n E hφ v (hJpos a) (2 * 2 ^ k₀ (a + 1))
      (Nat.mul_pos two_pos (Nat.two_pow_pos _))
    rwa [← hJsucc a] at h
  have hanti : ∀ v, Antitone fun a => (D a).eval f v := by
    intro v a a' haa'
    simp only [hDev]
    exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmono v haa'))
  have hJmono : StrictMono J := by
    refine strictMono_nat_of_lt_succ fun a => ?_
    rw [hJsucc a]
    have : 2 ≤ 2 * 2 ^ k₀ (a + 1) := by
      have := Nat.two_pow_pos (k₀ (a + 1)); omega
    have := hJpos a
    nlinarith
  have hinf : ∀ v, ⨅ a, (D a).eval f v = potentialAn n E φ v := by
    intro v
    have hlim : Tendsto (fun a => v.multiplierIdealVal n E φ (J a) / (J a : ℝ≥0∞)) atTop
        (𝓝 (v.potentialVal n E φ)) :=
      (BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic n E hA hφ v).comp
        hJmono.tendsto_atTop
    have hlim' : Tendsto (fun a => (D a).eval f v) atTop (𝓝 (potentialAn n E φ v)) := by
      simp only [hDev]
      exact ((continuous_neg.comp continuous_coe_ennreal_ereal).tendsto _).comp hlim
    exact tendsto_nhds_unique (tendsto_atTop_iInf (hanti v)) hlim'
  have h := isModuleTopologyPSH_of_antitone_seq.{u} f D hε hcls hanti
    ⟨BerkovichPoint.trivial f, by rw [hinf, htriv]; exact EReal.zero_ne_bot⟩
  have hfun : (fun v => ⨅ a, (D a).eval f v) = potentialAn n E φ := funext hinf
  rwa [hfun] at h

end Assembly

section Statement

variable [IsProjective f] [IsIntegral X]

local instance asmVarphianProper' : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance asmVarphianPointManifold'' : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **`lma:varphian`**: for a connected projective manifold `X` (an integral scheme, projective and
smooth over `ℂ`, with a closed projective embedding `E`), a `ℚ`-line bundle `L = m⁻¹ [M]` with the
Hermitian metric `h_M^{1/m}` (`M` an algebraic line bundle with atlas `b` and smooth metric `h_M`)
and `θ = c₁(L, h) = m⁻¹ c₁(M, h_M)`, every `φ ∈ PSH(X, θ)` has `φ^An ∈ PSH(L^An)`. -/
theorem potentialAn_isModuleTopologyPSH {M : X.Modules} (b : LineBundleAtlas M)
    (HM : SchemeLineBundleMetric f n E M) {m : ℕ} (hm : 0 < m) {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (((m : ℝ)⁻¹) • HM.curvature b).val φ) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b) (potentialAn n E φ) := by
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact potentialAn_isModuleTopologyPSH_aux f n E b HM hm hφ

end Statement

end SGPT.NAPotential.BJ.Assembly
