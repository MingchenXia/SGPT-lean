import SGPT.NAPotential.GAGAMult2Algebraic
import SGPT.Foundations.Analysis.Pending.MultiplierSubadditivity
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

/-!
# The limit defining `φ^An`, from the algebraicity of multiplier ideals

Blueprint `claude-gagamult2:limit`.  Source `def:NApotential:L975`: *by `thm:multipsubadd` and
Fekete's lemma the limit `v(φ) = lim_k k⁻¹ v(𝓘(kφ))` exists, and
`φ^An(v) = inf_k -2^{-k} v(𝓘(2^k φ))` (`eq:varphiAnalt`).*

* `mul_analytificationIdeal_le`: `𝔞^an · 𝔟^an ⊆ (𝔞𝔟)^an` for algebraic ideal sheaves.
* `analytificationIdeal_algebraization_eq`: under `MultiplierIdealAlgebraic`,
  `alg(𝓘(cφ))^an = 𝓘(cφ)`.
* `algebraization_multiplierIdeal_add_le_mul`: under `MultiplierIdealAlgebraic`, the algebraic
  models are submultiplicative, `alg 𝓘((c₁+c₂)φ) ≤ alg 𝓘(c₁φ) · alg 𝓘(c₂φ)` for `c₁, c₂ > 0`
  (the analytic subadditivity `thm:multipsubadd`, transported by `analytificationIdeal_le_iff`).
* `superadditive_pos_tendsto_iSup`: Fekete's lemma in `[0, ∞]` for sequences superadditive on
  the positive integers.
* **`tendsto_potentialVal_of_multiplierIdealAlgebraic`**,
  **`potentialVal_eq_iSup_dyadic_of_multiplierIdealAlgebraic`**: for `φ ∈ PSH(X, θ)` and
  `v ∈ X^An`, `k⁻¹ v(𝓘(kφ)) → v(φ) = sup_{k ≥ 1} k⁻¹ v(𝓘(kφ)) = sup_j 2^{-j} v(𝓘(2^j φ))`, under
  `MultiplierIdealAlgebraic` (which `multiplierIdealAlgebraic_of_positive` derives from a
  positively curved algebraic line bundle and GAGA for its sections).

Note: the earlier hypothesis `AlgebraizedSubmultiplicative` (all `k, l ∈ ℕ`) is never satisfied
when `X(ℂ) ≠ ∅`, since `𝓘(0 · φ)` is the zero ideal sheaf in the workspace convention
(`multiplierIdeal` requires `c > 0`); the results here use positive indices only.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open scoped Topology Manifold ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.GAGAMult

/-! ### Fekete's lemma on the positive integers -/

/-- Fekete's lemma in `[0, ∞]` for a sequence superadditive on the positive integers. -/
theorem superadditive_pos_tendsto_iSup {a : ℕ → ℝ≥0∞}
    (h : ∀ k l, 0 < k → 0 < l → a k + a l ≤ a (k + l)) :
    Tendsto (fun k : ℕ => a k / k) atTop (𝓝 (⨆ k : ℕ, ⨆ (_ : 0 < k), a k / k)) := by
  classical
  let a' : ℕ → ℝ≥0∞ := fun k => if k = 0 then 0 else a k
  have h' : ∀ k l, a' k + a' l ≤ a' (k + l) := by
    intro k l
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [a']
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [a']
    simp only [a', hk.ne', hl.ne', (Nat.add_pos_left hk l).ne', if_false]
    exact h k l hk hl
  have hlim := superadditive_tendsto_iSup h'
  have hsup : (⨆ k : ℕ, ⨆ (_ : 0 < k), a' k / k) = ⨆ k : ℕ, ⨆ (_ : 0 < k), a k / k := by
    refine iSup_congr fun k => iSup_congr fun hk => ?_
    simp only [a', hk.ne', if_false]
  rw [hsup] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  simp only [a', hk.ne', if_false]

/-- The dyadic form of Fekete's lemma, for sequences superadditive on the positive integers. -/
theorem superadditive_pos_iSup_eq_iSup_dyadic {a : ℕ → ℝ≥0∞}
    (h : ∀ k l, 0 < k → 0 < l → a k + a l ≤ a (k + l)) :
    (⨆ k : ℕ, ⨆ (_ : 0 < k), a k / k) = ⨆ j : ℕ, a (2 ^ j) / (2 ^ j : ℕ) := by
  have h1 := (superadditive_pos_tendsto_iSup h).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
  have hmono : Monotone (fun j : ℕ => a (2 ^ j) / (2 ^ j : ℕ)) := by
    apply monotone_nat_of_le_succ
    intro j
    have hpos : 0 < 2 ^ j := by positivity
    have h2 : (2 : ℝ≥0∞) * a (2 ^ j) ≤ a (2 ^ (j + 1)) := by
      have := h (2 ^ j) (2 ^ j) hpos hpos
      rw [two_mul]
      calc a (2 ^ j) + a (2 ^ j) ≤ a (2 ^ j + 2 ^ j) := this
        _ = a (2 ^ (j + 1)) := by rw [pow_succ, mul_two]
    have hne : ((2 ^ j : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
    calc a (2 ^ j) / (2 ^ j : ℕ) = (2 * a (2 ^ j)) / (2 ^ (j + 1) : ℕ) := by
          rw [pow_succ, Nat.cast_mul, mul_comm ((2 ^ j : ℕ) : ℝ≥0∞), Nat.cast_ofNat,
            ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
      _ ≤ a (2 ^ (j + 1)) / (2 ^ (j + 1) : ℕ) := ENNReal.div_le_div_right h2 _
  exact tendsto_nhds_unique h1 (tendsto_atTop_iSup hmono)

/-! ### Products of analytifications -/

section Products

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A function in the span of holomorphic generators has its germ in the span of their germs. -/
theorem mk_mem_spanGerms_of_isInSpanAt {S : (M → ℂ) → Prop} {x : M} {g : M → ℂ}
    (hS : ∀ s, S s → HolomorphicAt n s x) (h : IsInSpanAt (n := n) S x g) :
    NativeHolGerm.mk g h.1 ∈ spanGerms S x := by
  obtain ⟨hg, N, s, c, hSs, hc, heq⟩ := h
  have hs : ∀ i, HolomorphicAt n (s i) x := fun i => hS _ (hSs i)
  have hsum : HolomorphicAt n (fun y => ∑ i, c i y * s i y) x :=
    HolomorphicAt.sum _ fun i _ => (hc i).mul (hs i)
  rw [show NativeHolGerm.mk g hg = NativeHolGerm.mk _ hsum from
    NativeHolGerm.mk_eq_mk_iff.mpr heq, SGPT.PSH.IdealRestriction.mk_sum_mul c s hc hs hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (mk_mem_spanGerms (hs i) (hSs i))

end Products

/-! ### Monotonicity of multiplier ideals -/

section Monotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem multiplierWeight_antitone {c : ℝ} (hc : 0 < c) {a b : EReal} (hab : a ≤ b) :
    multiplierWeight c b ≤ multiplierWeight c a := by
  unfold multiplierWeight
  rw [EReal.exp_le_exp_iff, EReal.neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left hab (by exact_mod_cast hc.le)

/-- **Monotonicity of multiplier ideals**: `φ ≤ ψ` with `ψ` quasi-psh gives `𝓘(cφ) ⊆ 𝓘(cψ)`. -/
theorem multiplierIdeal_mono {θ : SmoothRealForm n M 2} {φ ψ : M → EReal}
    (hψ : ThetaPlurisubharmonic θ ψ) (hle : ∀ x, φ x ≤ ψ x) {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := n) c φ).Le (multiplierIdeal (n := n) c ψ) := by
  rintro x g ⟨hg, -, U, hU, hxU, hdiff, -, hint⟩
  refine ⟨hg, hc, U ∩ (complexChartAt (n := n) x).val.target,
    hU.inter (complexChartAt (n := n) x).val.open_target,
    ⟨hxU, (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)⟩,
    hdiff.mono inter_subset_left, ?_, ?_⟩
  · have husc := SGPT.Okounkov.TranscendentalL2.upperSemicontinuousOn_chartFunction_of_thetaPlurisubharmonicOn
      (Ω := univ) (fun e z hz _ => hψ e z hz) (complexChartAt (n := n) x)
    have hO : IsOpen (U ∩ (complexChartAt (n := n) x).val.target) :=
      hU.inter (complexChartAt (n := n) x).val.open_target
    have hw := DemaillyApproximation.aemeasurable_multiplierWeight_restrict hO
      (husc.mono fun z hz => ⟨hz.2, mem_univ _⟩) hc.ne'
    have hf : AEMeasurable (fun z => ENNReal.ofReal
        (‖g ((complexChartAt (n := n) x).val.symm z)‖ ^ 2))
        (MeasureTheory.volume.restrict (U ∩ (complexChartAt (n := n) x).val.target)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((hdiff.mono inter_subset_left).continuousOn.aestronglyMeasurable
          hO.measurableSet).norm.aemeasurable.pow_const 2)
    exact hf.mul hw
  · refine lt_of_le_of_lt ?_ hint
    refine (MeasureTheory.setLIntegral_mono' (hU.inter
      (complexChartAt (n := n) x).val.open_target).measurableSet fun z _ => ?_).trans
      (MeasureTheory.lintegral_mono_set inter_subset_left)
    exact mul_le_mul_of_nonneg_left (multiplierWeight_antitone hc (hle _)) zero_le

end Monotone

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance gagaLimitPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance gagaLimitPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- The generators of `𝔞^an` at `x`: analytic functions of the sections of `𝔞` over affine
neighbourhoods of `x`. -/
def AnGen (𝔞 : X.IdealSheafData) (x : SchemeComplexPoint f) (s : SchemeComplexPoint f → ℂ) :
    Prop :=
  ∃ (U : X.affineOpens) (_ : schemeComplexPointImage f x ∈ (U : X.Opens)) (r : Γ(X, U)),
    r ∈ 𝔞.ideal U ∧ s = schemeOpenRegularFunction f n E U r

theorem analytificationIdeal_mem_iff (𝔞 : X.IdealSheafData) (x : SchemeComplexPoint f)
    (g : SchemeComplexPoint f → ℂ) :
    (analytificationIdeal f n E 𝔞).mem x g ↔ IsInSpanAt (n := n) (AnGen f n E 𝔞 x) x g :=
  Iff.rfl

section Manifold

variable [IsSeparated f] [QuasiCompact f]

local instance gagaLimitPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

theorem holomorphicAt_of_anGen {𝔞 : X.IdealSheafData} {x : SchemeComplexPoint f}
    {s : SchemeComplexPoint f → ℂ} (h : AnGen f n E 𝔞 x s) : HolomorphicAt n s x := by
  obtain ⟨U, hU, r, -, rfl⟩ := h
  exact schemeOpenRegularFunction_holomorphicAt f n E U r x hU

/-- The product of two generators of `𝔞^an`, `𝔟^an` has its germ in the span of the generators
of `(𝔞𝔟)^an`. -/
theorem mk_mul_mem_spanGerms {𝔞 𝔟 : X.IdealSheafData} {x : SchemeComplexPoint f}
    {s t : SchemeComplexPoint f → ℂ} (hs : AnGen f n E 𝔞 x s) (ht : AnGen f n E 𝔟 x t) :
    NativeHolGerm.mk (s * t) ((holomorphicAt_of_anGen f n E hs).mul
      (holomorphicAt_of_anGen f n E ht)) ∈ spanGerms (AnGen f n E (𝔞 * 𝔟) x) x := by
  obtain ⟨U, hU, r, hr, rfl⟩ := hs
  obtain ⟨V, hV, r', hr', rfl⟩ := ht
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_inter hU hV) ((U : X.Opens).isOpen.inter (V : X.Opens).isOpen)
  let W' : X.affineOpens := ⟨W, hW⟩
  have hWU : W' ≤ U := fun y hy => (hWUV hy).1
  have hWV : W' ≤ V := fun y hy => (hWUV hy).2
  have hWU' : (W' : X.Opens) ≤ (U : X.Opens) := hWU
  have hWV' : (W' : X.Opens) ≤ (V : X.Opens) := hWV
  let ρ := X.presheaf.map (homOfLE hWU').op
  let ρ' := X.presheaf.map (homOfLE hWV').op
  have hprod : ρ r * ρ' r' ∈ (𝔞 * 𝔟).ideal W' := by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    exact Ideal.mul_mem_mul (𝔞.ideal_le_comap_ideal hWU hr) (𝔟.ideal_le_comap_ideal hWV hr')
  have hgen : AnGen f n E (𝔞 * 𝔟) x (schemeOpenRegularFunction f n E W' (ρ r * ρ' r')) :=
    ⟨W', hxW, _, hprod, rfl⟩
  have heq : NativeHolGerm.mk (schemeOpenRegularFunction f n E U r *
      schemeOpenRegularFunction f n E V r') ((holomorphicAt_of_anGen f n E ⟨U, hU, r, hr, rfl⟩).mul
        (holomorphicAt_of_anGen f n E ⟨V, hV, r', hr', rfl⟩)) =
      NativeHolGerm.mk _ (holomorphicAt_of_anGen f n E hgen) := by
    apply NativeHolGerm.mk_eq_mk_iff.mpr
    have hO : IsOpen (schemeComplexPointImage f ⁻¹' ((W' : X.Opens) : Set X)) :=
      (W' : X.Opens).isOpen.preimage (schemeComplexPointImage_continuous f)
    filter_upwards [hO.mem_nhds hxW] with y hy
    rw [schemeOpenRegularFunction_mul f n E W' _ _ hy]
    simp only [Pi.mul_apply]
    rw [schemeOpenRegularFunction_restrict f n E W' U hWU r hy,
      schemeOpenRegularFunction_restrict f n E W' V hWV r' hy]
  rw [heq]
  exact mk_mem_spanGerms _ hgen

/-- `𝔞^an · 𝔟^an ⊆ (𝔞𝔟)^an`. -/
theorem mul_analytificationIdeal_le (𝔞 𝔟 : X.IdealSheafData) :
    ((analytificationIdeal f n E 𝔞).mul (analytificationIdeal f n E 𝔟)).Le
      (analytificationIdeal f n E (𝔞 * 𝔟)) := by
  intro x g hg
  -- germs of `𝔞^an` and `𝔟^an` lie in the spans of the germs of their generators
  have hspan : ∀ a b, (analytificationIdeal f n E 𝔞).mem x a →
      (analytificationIdeal f n E 𝔟).mem x b → ∀ (hab : HolomorphicAt n (a * b) x),
      NativeHolGerm.mk (a * b) hab ∈ spanGerms (AnGen f n E (𝔞 * 𝔟) x) x := by
    intro a b ha hb hab
    have ha' := mk_mem_spanGerms_of_isInSpanAt (fun s hs => holomorphicAt_of_anGen f n E hs) ha
    have hb' := mk_mem_spanGerms_of_isInSpanAt (fun s hs => holomorphicAt_of_anGen f n E hs) hb
    have hmul : NativeHolGerm.mk (a * b) hab =
        NativeHolGerm.mk a ha.1 * NativeHolGerm.mk b hb.1 := by
      apply Subtype.ext; rfl
    rw [hmul]
    refine (Ideal.mul_le.mpr fun u hu w hw => ?_) (Ideal.mul_mem_mul ha' hb')
    -- products of generators
    refine Submodule.span_induction (p := fun u _ => u * w ∈ spanGerms (AnGen f n E (𝔞 * 𝔟) x) x)
      ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨s, hs, hS, rfl⟩
      refine Submodule.span_induction
        (p := fun w _ => NativeHolGerm.mk s hs * w ∈ spanGerms (AnGen f n E (𝔞 * 𝔟) x) x)
        ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨t, ht, hT, rfl⟩
        have := mk_mul_mem_spanGerms f n E hS hT
        convert this using 1
        apply Subtype.ext; rfl
      · simp
      · intro w₁ w₂ _ _ h₁ h₂; rw [mul_add]; exact Ideal.add_mem _ h₁ h₂
      · intro c w _ h; rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ h
    · simp
    · intro u₁ u₂ _ _ h₁ h₂; rw [add_mul]; exact Ideal.add_mem _ h₁ h₂
    · intro c u _ h; rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ h
  have hg' := mk_mem_spanGerms_of_isInSpanAt (n := n) (S := fun s => ∃ a b,
      (analytificationIdeal f n E 𝔞).mem x a ∧ (analytificationIdeal f n E 𝔟).mem x b ∧
        s = a * b) (fun s hs => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hs
      exact ha.1.mul hb.1) hg
  have hle : spanGerms (n := n) (fun s => ∃ a b,
      (analytificationIdeal f n E 𝔞).mem x a ∧ (analytificationIdeal f n E 𝔟).mem x b ∧
        s = a * b) x ≤ spanGerms (n := n) (AnGen f n E (𝔞 * 𝔟) x) x := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨s, hs, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    exact hspan a b ha hb hs
  exact isInSpanAt_of_mk_mem_spanGerms hg.1 (hle hg')

end Manifold

/-! ### Consequences of the algebraicity of multiplier ideals -/

/-- Under `MultiplierIdealAlgebraic`: `alg(𝓘(cφ))^an = 𝓘(cφ)` for quasi-psh `φ`, `c > 0`. -/
theorem analytificationIdeal_algebraization_eq (hA : MultiplierIdealAlgebraic f n E)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsGlobalQuasiPshPotential (n := n) φ)
    {c : ℝ} (hc : 0 < c) :
    analytificationIdeal f n E (algebraization f n E (multiplierIdeal (n := n) c φ)) =
      multiplierIdeal (n := n) c φ := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  have h1 := analytificationIdeal_algebraization_le f n E (multiplierIdeal (n := n) c φ)
    (SGPT.Bergman.MultiplierSectionsDraft.multiplierIdeal_isCoherent_genuine hφ hc)
  have h2 := hA φ hφ c hc
  ext x g
  exact ⟨h1 x g, h2 x g⟩

/-- **Submultiplicativity of the algebraic models** (the algebraic form of `thm:multipsubadd`),
under `MultiplierIdealAlgebraic`: `alg 𝓘((c₁+c₂)φ) ≤ alg 𝓘(c₁φ) · alg 𝓘(c₂φ)`. -/
theorem algebraization_multiplierIdeal_add_le_mul (hA : MultiplierIdealAlgebraic f n E)
    {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    algebraization f n E (multiplierIdeal (n := n) (c₁ + c₂) φ) ≤
      algebraization f n E (multiplierIdeal (n := n) c₁ φ) *
        algebraization f n E (multiplierIdeal (n := n) c₂ φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  have hq : IsGlobalQuasiPshPotential (n := n) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  rw [← analytificationIdeal_le_iff f n E,
    analytificationIdeal_algebraization_eq f n E hA hq (add_pos hc₁ hc₂)]
  -- the analytic subadditivity
  have hsub : (multiplierIdeal (n := n) (c₁ + c₂) φ).Le
      ((multiplierIdeal (n := n) c₁ φ).mul (multiplierIdeal (n := n) c₂ φ)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      intro x g hg
      have hg1 := (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
        hq (add_pos hc₁ hc₂) x g).mp hg
      refine ⟨hg1, 1, fun _ => g, fun _ _ => 1, fun _ => ?_,
        fun _ => holomorphicAt_const 1, Eventually.of_forall fun _ => by simp⟩
      refine ⟨g, fun _ => 1,
        (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
          hq hc₁ x g).mpr hg1,
        (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
          hq hc₂ x _).mpr (holomorphicAt_const 1), ?_⟩
      funext y; simp
    · exact MultiplierSubadditivity.multiplierIdeal_add_le_mul hn hφ.1 hc₁ hc₂
  intro x g hg
  have h1 := hsub x g hg
  rw [← analytificationIdeal_algebraization_eq f n E hA hq hc₁,
    ← analytificationIdeal_algebraization_eq f n E hA hq hc₂] at h1
  exact mul_analytificationIdeal_le f n E _ _ x g h1

variable {f} [IsProper f]

namespace BerkovichPoint

/-- The sequence `k ↦ v(𝓘(kφ))` is superadditive on the positive integers, under
`MultiplierIdealAlgebraic`. -/
theorem multiplierIdealVal_superadditive_pos (hA : MultiplierIdealAlgebraic f n E)
    {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    v.multiplierIdealVal n E φ k + v.multiplierIdealVal n E φ l ≤
      v.multiplierIdealVal n E φ (k + l) := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  unfold multiplierIdealVal
  rw [← v.idealVal_mul]
  apply v.idealVal_antitone
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have h := algebraization_multiplierIdeal_add_le_mul f n E hA hφ hk' hl'
  rwa [← Nat.cast_add] at h

/-- **`def:NApotential:L975`, existence of the limit**: under `MultiplierIdealAlgebraic`, for
`φ ∈ PSH(X, θ)` and `v ∈ X^An`, `k⁻¹ v(𝓘(kφ)) → v(φ) = sup_{k ≥ 1} k⁻¹ v(𝓘(kφ))`. -/
theorem tendsto_potentialVal_of_multiplierIdealAlgebraic (hA : MultiplierIdealAlgebraic f n E)
    {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => v.multiplierIdealVal n E φ k / k) atTop (𝓝 (v.potentialVal n E φ)) := by
  have h := superadditive_pos_tendsto_iSup (v.multiplierIdealVal_superadditive_pos n E hA hφ)
  rwa [potentialVal, h.limUnder_eq]

theorem potentialVal_eq_iSup_of_multiplierIdealAlgebraic (hA : MultiplierIdealAlgebraic f n E)
    {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ k : ℕ, ⨆ (_ : 0 < k), v.multiplierIdealVal n E φ k / k :=
  (superadditive_pos_tendsto_iSup (v.multiplierIdealVal_superadditive_pos n E hA hφ)).limUnder_eq

/-- **`eq:varphiAnalt`** under `MultiplierIdealAlgebraic`:
`v(φ) = sup_j 2^{-j} v(𝓘(2^j φ))`, i.e. `φ^An(v) = inf_j -2^{-j} v(𝓘(2^j φ))`. -/
theorem potentialVal_eq_iSup_dyadic_of_multiplierIdealAlgebraic
    (hA : MultiplierIdealAlgebraic f n E) {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ j : ℕ, v.multiplierIdealVal n E φ (2 ^ j) / (2 ^ j : ℕ) := by
  rw [potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E hA hφ v,
    superadditive_pos_iSup_eq_iSup_dyadic (v.multiplierIdealVal_superadditive_pos n E hA hφ)]

/-- **Monotonicity of `φ ↦ φ^An`** under `MultiplierIdealAlgebraic`: if `φ ≤ ψ` are quasi-psh
(`φ ∈ PSH(X, θ)`, `ψ ∈ PSH(X, θ')`), then `v(ψ) ≤ v(φ)` for every `v ∈ X^An`. -/
theorem potentialVal_antitone_of_multiplierIdealAlgebraic (hA : MultiplierIdealAlgebraic f n E)
    {φ ψ : SchemeComplexPoint f → EReal}
    {θ θ' : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ' ψ)
    (hle : ∀ x, φ x ≤ ψ x) (v : BerkovichPoint f) :
    v.potentialVal n E ψ ≤ v.potentialVal n E φ := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  rw [potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E hA hψ v,
    potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E hA hφ v]
  refine iSup₂_mono fun k hk => ENNReal.div_le_div_right ?_ _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact v.idealVal_antitone (algebraization_mono f n E
    (multiplierIdeal_mono hψ.1 hle hk'))

/-- `φ ≤ ψ ⟹ φ^An ≤ ψ^An` under `MultiplierIdealAlgebraic`. -/
theorem potentialAn_mono_of_multiplierIdealAlgebraic (hA : MultiplierIdealAlgebraic f n E)
    {φ ψ : SchemeComplexPoint f → EReal}
    {θ θ' : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ' ψ)
    (hle : ∀ x, φ x ≤ ψ x) (v : BerkovichPoint f) :
    potentialAn n E φ v ≤ potentialAn n E ψ v := by
  unfold potentialAn
  rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  exact potentialVal_antitone_of_multiplierIdealAlgebraic n E hA hφ hψ hle v

end BerkovichPoint

end SGPT.NAPotential.Berkovich
