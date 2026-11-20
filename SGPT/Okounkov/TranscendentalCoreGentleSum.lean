import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Okounkov.TranscendentalCoreCommonModel
import SGPT.Okounkov.TranscendentalCoreDivisorGenerators
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Okounkov.FlagLelong

/-!
# Sums of potentials with gentle analytic singularities

Source: blueprint node `tok:gentle-sum` (implicit in DRWNXZ Proposition 3.3, "Point (2) is also
clear"): if `T ∈ 𝒢(ξ)`, `S ∈ 𝒢(ξ')` and `a, b ∈ ℚ_{≥ 0}` with `(a, b) ≠ (0, 0)`, then
`aT + bS ∈ 𝒢(aξ + bξ')`; if moreover `T` is a Kähler current and `a > 0`, then
`aT + bS ∈ Ω(aξ + bξ')`.

Let `φ`, `ψ` be gentle of types `(c, 𝓘)`, `(c', 𝓙)` and write `ac = u/N`, `bc' = u'/N`. Then
`aφ + bψ` has analytic singularities of type `(1/N, 𝓘^u 𝓙^{u'})` and
`e^{N(aφ + bψ)} = (e^{φ/c})^u (e^{ψ/c'})^{u'}` is smooth. If `f : Y → X`, `f' : Y' → X` are the
resolutions of `φ` and `ψ`, with `f^*φ = c log|g|² + h` and `f'^*ψ = c' log|g'|² + h'`, a compact
Kähler common model `ℓ : Z → Y`, `ℓ' : Z → Y'` (`exists_kahler_compact_smooth_common_model`)
gives `(f ∘ ℓ)^*(aφ + bψ) = (1/N) log|(g ∘ ℓ)^u (g' ∘ ℓ')^{u'}|² + a h ∘ ℓ + b h' ∘ ℓ'`, a local
equation of the effective divisor `u ℓ^*D + u' ℓ'^*D'` with a smooth remainder.

The case `a = b = 0` is the zero current, which is gentle on a Kähler manifold
(`hasGentleAnalyticSingularitiesOfType_zero`, resolved by the identity).

## Main results

* `hasGentleAnalyticSingularitiesOfType_pos_rat_smul`: `aφ` is gentle of type `(ac, 𝓘)`.
* `exists_hasGentleAnalyticSingularitiesOfType_add_smul`: `aφ + bψ` is gentle (`a, b > 0`).
* `add_smul_mem_gentleCurrents`, `add_smul_mem_gentleCurrents_of_kahler`,
  `add_smul_mem_gentleKahlerCurrents`: blueprint `tok:gentle-sum`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Foundations.Analysis.Pending.IdealWeightPowers
open SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

universe u

/-! ### Extended-real arithmetic -/

/-- `exp (k x) = (exp x)^k` in `EReal`. -/
theorem ereal_exp_nat_mul (k : ℕ) (x : EReal) :
    EReal.exp (((k : ℝ) : EReal) * x) = EReal.exp x ^ k := by
  rw [← ereal_nsmul_eq_mul]
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, EReal.exp_add, ih, pow_succ]

/-- `log (A^k B^l) = k log A + l log B` for `A, B ≥ 0`. -/
theorem log_ofReal_pow_mul_pow {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (k l : ℕ) :
    ENNReal.log (ENNReal.ofReal (A ^ k * B ^ l)) =
      ((k : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal A) +
        ((l : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal B) := by
  rw [ENNReal.ofReal_mul (pow_nonneg hA k), ENNReal.ofReal_pow hA, ENNReal.ofReal_pow hB,
    ENNReal.log_mul_add, ENNReal.log_pow, ENNReal.log_pow, EReal.coe_natCast, EReal.coe_natCast]

/-- `log |x^k y^l|² = k log |x|² + l log |y|²`. -/
theorem log_norm_sq_pow_mul_pow (x y : ℂ) (k l : ℕ) :
    ENNReal.log (ENNReal.ofReal (‖x ^ k * y ^ l‖ ^ 2)) =
      ((k : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖x‖ ^ 2)) +
        ((l : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖y‖ ^ 2)) := by
  have h : ‖x ^ k * y ^ l‖ ^ 2 = (‖x‖ ^ 2) ^ k * (‖y‖ ^ 2) ^ l := by
    rw [norm_mul, norm_pow, norm_pow]
    ring
  rw [h]
  exact log_ofReal_pow_mul_pow (sq_nonneg _) (sq_nonneg _) k l

/-- `r (c L + h) = (r c) L + r h` for `r ≥ 0`. -/
theorem ereal_mul_add_coe {r : ℝ} (hr : 0 ≤ r) (c : ℝ) (L : EReal) (h : ℝ) :
    (r : EReal) * ((c : EReal) * L + (h : EReal)) = ((r * c : ℝ) : EReal) * L +
      ((r * h : ℝ) : EReal) := by
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hr) (EReal.coe_ne_top _),
    ← _root_.mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul]

/-! ### Local holomorphic coordinates -/

/-- The translation `w ↦ w - p` as a local holomorphic equivalence at `p`, on an open set. -/
def translationEquivAt {n : ℕ} (S : Set (ComplexModel n)) (hS : IsOpen S)
    (p : ComplexModel n) (hp : p ∈ S) : LocalHolomorphicEquivAt (n := n) p where
  source := S
  target := (fun w => w + p) ⁻¹' S
  isOpen_source := hS
  isOpen_target := hS.preimage (continuous_id.add continuous_const)
  center_mem_source := hp
  toFun := fun w => w - p
  invFun := fun w => w + p
  toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
  mapsTo_toFun := fun w hw => by simpa [mem_preimage] using hw
  mapsTo_invFun := fun w hw => hw
  left_inv := fun w _ => sub_add_cancel w p
  right_inv := fun w _ => add_sub_cancel_right w p

section Manifold

variable {n : ℕ}

/-- A function smooth in the charts of `Y` over an open set `N` stays smooth in the charts of
`Z` after composition with a holomorphic map `ℓ : Z → Y`, over `ℓ⁻¹ N`. -/
theorem contDiffOn_comp_holomorphic {Y Z : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {ℓ : Z → Y}
    (hℓ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ) {N : Set Y}
    (hN : IsOpen N) {H : Y → ℝ}
    (hH : ∀ e : ComplexChart n Y,
      ContDiffOn ℝ ∞ (fun z => H (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' N))
    (χ : ComplexChart n Z) :
    ContDiffOn ℝ ∞ (fun z => H (ℓ (χ.val.symm z))) (χ.val.target ∩ χ.val.symm ⁻¹' (ℓ ⁻¹' N)) := by
  intro z hz
  set d := complexChartAt (n := n) (ℓ (χ.val.symm z))
  have hzD : z ∈ coordinateDomain ℓ χ d := ⟨hz.1, mem_complexChartAt_source _⟩
  have hG := coordinateMap_contDiffAt_real hℓ χ d hzD
  have hGz : coordinateMap ℓ χ d z ∈ d.val.target ∩ d.val.symm ⁻¹' N := by
    refine ⟨coordinateMap_mem_target hzD, ?_⟩
    change d.val.symm (d.val (ℓ (χ.val.symm z))) ∈ N
    rw [d.val.left_inv hzD.2]
    exact hz.2
  have hopen : IsOpen (d.val.target ∩ d.val.symm ⁻¹' N) :=
    d.val.isOpen_inter_preimage_symm hN
  have hHd := (hH d).contDiffAt (hopen.mem_nhds hGz)
  refine ((hHd.comp z hG).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(coordinateDomain_isOpen hℓ χ d).mem_nhds hzD] with w hw
  change H (ℓ (χ.val.symm w)) = H (d.val.symm (d.val (ℓ (χ.val.symm w))))
  rw [d.val.left_inv hw.2]

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] in
/-- The local resolution data of `def:analy-sing` (`HasGentleAnalyticSingularitiesOfType`, last
clause) at a point `y` of the resolution, read in a chart `χ` at `y`, give, on an open
neighbourhood `N` of `y`, a local equation `g` of the divisor and a remainder `H` smooth in every
chart with `v ∘ f = c log |g|² + H` on `N`. -/
theorem exists_local_resolution_presentation {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X}
    {D : EffectiveDivisor n Y} {v : X → EReal} {c : ℚ} {y : Y} (χ : ComplexChart n Y)
    (hyχ : y ∈ χ.val.source) {V : Set Y}
    {g : Y → ℂ} (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g V)
    (hnon : ∀ W : Set Y, IsOpen W → W ⊆ V → W.Nonempty → ∃ t ∈ W, g t ≠ 0)
    (hgen : ∀ t ∈ V, ∀ a : Y → ℂ, D.ideal.mem t a ↔ IsInSpanAt (n := n) (· = g) t a)
    (Φ : LocalHolomorphicEquivAt (n := n) (χ.val y))
    (hΦ0 : Φ.toFun (χ.val y) = 0)
    {h : ComplexModel n → ℝ} {r : ℝ} (hr : 0 < r) (hh : ContDiffOn ℝ ∞ h (ball 0 r))
    (heq : ∀ z ∈ ball (0 : ComplexModel n) r,
      χ.val.symm (Φ.invFun z) ∈ V ∧
      v (f (χ.val.symm (Φ.invFun z))) =
        ((c : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal
          (‖g (χ.val.symm (Φ.invFun z))‖ ^ 2)) + (h z : EReal)) :
    ∃ N : Set Y, IsOpen N ∧ y ∈ N ∧ IsLocalEquationOn D.ideal N g ∧ ∃ H : Y → ℝ,
      (∀ e : ComplexChart n Y,
        ContDiffOn ℝ ∞ (fun z => H (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' N)) ∧
      ∀ q ∈ N, v (f q) = ((c : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖g q‖ ^ 2)) +
        (H q : EReal) := by
  have hΦcont : ContinuousOn Φ.toFun Φ.source := Φ.toFun_holomorphic.continuousOn
  have hO : IsOpen (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r) :=
    hΦcont.isOpen_inter_preimage Φ.isOpen_source isOpen_ball
  have hNopen : IsOpen (χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r)) :=
    χ.val.continuousOn.isOpen_inter_preimage χ.val.open_source hO
  have hball0 : Φ.toFun (χ.val y) ∈ ball (0 : ComplexModel n) r := by
    rw [hΦ0]
    exact mem_ball_self hr
  have hyN : y ∈ χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r) :=
    ⟨hyχ, Φ.center_mem_source, hball0⟩
  have hback : ∀ q ∈ χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r),
      χ.val.symm (Φ.invFun (Φ.toFun (χ.val q))) = q := by
    intro q hq
    rw [Φ.left_inv _ hq.2.1, χ.val.left_inv hq.1]
  have hNV : χ.val.source ∩ χ.val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r) ⊆ V := by
    intro q hq
    have := (heq _ hq.2.2).1
    rwa [hback q hq] at this
  refine ⟨_, hNopen, hyN, (show IsLocalEquationOn D.ideal V g from ⟨hg, hnon, hgen⟩).mono hNV,
    fun q => h (Φ.toFun (χ.val q)), ?_, ?_⟩
  · intro e z hz
    have hzsrc : z ∈ (chartTransition e χ).source := by
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage]
      exact ⟨hz.1, hz.2.1⟩
    have h1 := chartTransition_contDiffAt_real e χ hzsrc
    have h2 : ContDiffAt ℝ ∞ Φ.toFun (χ.val (e.val.symm z)) :=
      (contDiffOn_real_of_differentiableOn_complex Φ.toFun_holomorphic
        Φ.isOpen_source).contDiffAt (Φ.isOpen_source.mem_nhds hz.2.2.1)
    have h3 : ContDiffAt ℝ ∞ h (Φ.toFun (χ.val (e.val.symm z))) :=
      hh.contDiffAt (isOpen_ball.mem_nhds hz.2.2.2)
    exact (h3.comp z (h2.comp z h1)).contDiffWithinAt
  · intro q hq
    have := (heq _ hq.2.2).2
    rwa [hback q hq] at this

/-- **Positive rational multiples of gentle potentials** are gentle: `aφ` has type `(ac, 𝓘)`. -/
theorem hasGentleAnalyticSingularitiesOfType_pos_rat_smul {φ : X → EReal} {c : ℚ}
    {𝔞 : GermIdeal n X} (hφ : HasGentleAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    {a : ℚ} (ha : 0 < a)
    (hq : IsGlobalQuasiPshPotential (n := n) (fun x => ((a : ℝ) : EReal) * φ x)) :
    HasGentleAnalyticSingularitiesOfType (n := n) (fun x => ((a : ℝ) : EReal) * φ x)
      (a * c) 𝔞 := by
  obtain ⟨-, htype, hexp, hsmooth, Y, iT, iC, iM, f, D, hf, hK, hloc⟩ := hφ
  have hc : (0 : ℝ) < c := by exact_mod_cast htype.1
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hcoef : ∀ x, (((((a * c : ℚ) : ℝ))⁻¹ : ℝ) : EReal) * (((a : ℝ) : EReal) * φ x) =
      ((((c : ℝ))⁻¹ : ℝ) : EReal) * φ x := by
    intro x
    rw [← _root_.mul_assoc, ← EReal.coe_mul]
    congr 2
    push_cast
    field_simp
  refine ⟨hq, hasAnalyticSingularitiesOfType_pos_rat_smul htype ha, fun x => ?_, ?_,
    Y, iT, iC, iM, f, D, hf, hK, fun y => ?_⟩
  · rw [hcoef]
    exact hexp x
  · simp only [hcoef]
    exact hsmooth
  · obtain ⟨V, hV, hyV, s, hs, hsne, hsD, Φ, hΦsrc, hΦ0, h, r, hr, hball, hh, heq⟩ := hloc y
    refine ⟨V, hV, hyV, s, hs, hsne, hsD, Φ, hΦsrc, hΦ0, fun z => a * h z, r, hr, hball,
      hh.const_smul (a : ℝ), fun z hz => ⟨(heq z hz).1, ?_⟩⟩
    change ((a : ℝ) : EReal) * φ (f _) = _
    rw [(heq z hz).2, ereal_mul_add_coe haR.le, Rat.cast_mul]


/-- The zero divisor `𝒪(-0) = 𝒪`, with local equation `1`. -/
def zeroEffectiveDivisor : EffectiveDivisor n X where
  ideal := unitIdeal n X
  isInvertible := fun x => ⟨univ, isOpen_univ, mem_univ x, fun _ => 1,
    (mdifferentiable_const (I := 𝓘(ℂ, ComplexModel n)) (I' := 𝓘(ℂ, ℂ))
      (c := (1 : ℂ))).mdifferentiableOn,
    fun _ _ _ ⟨y, hy⟩ => ⟨y, hy, one_ne_zero⟩, fun y _ g => by
      rw [mem_unitIdeal_iff]
      have hpred : (fun s : X → ℂ => s ∈ range (fun _ : Fin 1 => (1 : X → ℂ))) =
          (fun s => s = fun _ => 1) := by
        funext s
        apply propext
        constructor
        · rintro ⟨_, rfl⟩
          rfl
        · rintro rfl
          exact ⟨0, rfl⟩
      rw [hpred]⟩

/-- **The zero potential is gentle** on a Kähler manifold: it has type `(1, 𝒪_X)`, and the
identity resolves it with the zero divisor. -/
theorem hasGentleAnalyticSingularitiesOfType_zero (hK : Nonempty (KahlerBackground n X)) :
    HasGentleAnalyticSingularitiesOfType (n := n) (fun _ : X => (0 : EReal)) 1
      (unitIdeal n X) := by
  have hzero : IsThetaPshPotential (0 : ClosedRealOneOneForm n X).val
      (fun _ : X => (0 : EReal)) :=
    (Pending.LocalPotentials.isThetaPshPotential_zero_iff 0).mpr (by intro e z hz w; simp)
  have hexp : ∀ x : X, EReal.exp (((((1 : ℚ) : ℝ))⁻¹ : ℝ) * ((fun _ : X => (0 : EReal)) x)) =
      1 := by
    intro x
    simp
  refine ⟨hzero.quasiPshPotential, hasAnalyticSingularitiesOfType_unitIdeal one_pos,
    fun x => by rw [hexp x]; exact ENNReal.one_ne_top, ?_, X, inferInstance, inferInstance,
    inferInstance, id, zeroEffectiveDivisor (n := n) (X := X),
    SGPT.Okounkov.isAnalyticModification_identity, hK,
    fun y => ?_⟩
  · have hfun : (fun x : X => (EReal.exp (((((1 : ℚ) : ℝ))⁻¹ : ℝ) *
        ((fun _ : X => (0 : EReal)) x))).toReal) = fun _ => 1 := by
      funext x
      rw [hexp x, ENNReal.toReal_one]
    rw [hfun]
    exact fun e => contDiffOn_const
  · have hχy : (complexChartAt (n := n) y).val y ∈ (complexChartAt (n := n) y).val.target :=
      (complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y)
    set Φ := translationEquivAt (complexChartAt (n := n) y).val.target
      (complexChartAt (n := n) y).val.open_target _ hχy
    have h0 : (0 : ComplexModel n) ∈ Φ.target := by
      change (0 : ComplexModel n) + (complexChartAt (n := n) y).val y ∈
        (complexChartAt (n := n) y).val.target
      rw [zero_add]
      exact hχy
    obtain ⟨r, hr, hrΦ⟩ := Metric.isOpen_iff.mp Φ.isOpen_target 0 h0
    refine ⟨univ, isOpen_univ, mem_univ y, fun _ => 1,
      (mdifferentiable_const (I := 𝓘(ℂ, ComplexModel n)) (I' := 𝓘(ℂ, ℂ))
        (c := (1 : ℂ))).mdifferentiableOn,
      fun _ _ _ ⟨t, ht⟩ => ⟨t, ht, one_ne_zero⟩, ?_,
      Φ, subset_rfl, sub_self _, fun _ => 0, r, hr, hrΦ, contDiffOn_const,
      fun z _ => ⟨mem_univ _, by simp⟩⟩
    intro t _ a
    rw [show (zeroEffectiveDivisor (n := n) (X := X)).ideal = unitIdeal n X from rfl,
      mem_unitIdeal_iff]
    have hpred : (fun s : X → ℂ => s ∈ range (fun _ : Fin 1 => (1 : X → ℂ))) =
        (fun s => s = fun _ => 1) := by
      funext s
      apply propext
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, rfl⟩
    rw [hpred]

variable [ConnectedSpace X] [CompactSpace X]

/-- **Sums of gentle potentials** (blueprint `tok:gentle-sum`): for `a, b ∈ ℚ_{>0}`,
`aφ + bψ` has gentle analytic singularities whenever `φ` and `ψ` do (and `aφ + bψ` is
quasi-psh). -/
theorem exists_hasGentleAnalyticSingularitiesOfType_add_smul {φ ψ : X → EReal} {c c' : ℚ}
    {𝔞 𝔟 : GermIdeal n X} (hφ : HasGentleAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hψ : HasGentleAnalyticSingularitiesOfType (n := n) ψ c' 𝔟) {a b : ℚ} (ha : 0 < a)
    (hb : 0 < b)
    (hq : IsGlobalQuasiPshPotential (n := n)
      (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x)) :
    ∃ (c'' : ℚ) (𝔠 : GermIdeal n X), HasGentleAnalyticSingularitiesOfType (n := n)
      (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) c'' 𝔠 := by
  obtain ⟨-, htype, hexp, hsmooth, Y₀, iT₀, iC₀, iM₀, f₀, D₀, hf₀, hK₀, hloc₀⟩ := hφ
  obtain ⟨-, htype', hexp', hsmooth', Y₁, iT₁, iC₁, iM₁, f₁, D₁, hf₁, hK₁, hloc₁⟩ := hψ
  have hc : (0 : ℚ) < c := htype.1
  have hc' : (0 : ℚ) < c' := htype'.1
  obtain ⟨N, u, u', hN, hu, hu', hac, hbc⟩ :=
    exists_common_denominator (mul_pos ha hc) (mul_pos hb hc')
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu.ne'
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu'.ne'
  -- real forms of the coefficient identities
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hc'R : (0 : ℝ) < c' := by exact_mod_cast hc'
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hacR : (a : ℝ) * (c : ℝ) = ((k.succ : ℕ) : ℝ) / N := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hac
    push_cast at this ⊢
    exact this
  have hbcR : (b : ℝ) * (c' : ℝ) = ((k'.succ : ℕ) : ℝ) / N := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hbc
    push_cast at this ⊢
    exact this
  -- the type `(1/N, 𝓘^u 𝓙^{u'})`
  have htypeφ := hasAnalyticSingularitiesOfType_pos_rat_smul htype ha
  rw [hac] at htypeφ
  have htypeψ := hasAnalyticSingularitiesOfType_pos_rat_smul htype' hb
  rw [hbc] at htypeψ
  have htypeΨ := hasAnalyticSingularitiesOfType_mul
    (hasAnalyticSingularitiesOfType_rescale hu hN htypeφ)
    (hasAnalyticSingularitiesOfType_rescale hu' hN htypeψ)
  -- the exponential
  have hNinv : (((((N : ℚ)⁻¹ : ℚ) : ℝ))⁻¹ : ℝ) = N := by push_cast; exact inv_inv _
  have hexp_eq : ∀ x, EReal.exp ((((((N : ℚ)⁻¹ : ℚ) : ℝ))⁻¹ : ℝ) *
        (((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x)) =
      EReal.exp ((((c : ℝ))⁻¹ : ℝ) * φ x) ^ k.succ *
        EReal.exp ((((c' : ℝ))⁻¹ : ℝ) * ψ x) ^ k'.succ := by
    intro x
    rw [hNinv, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hNR.le)
      (EReal.coe_ne_top _), ← _root_.mul_assoc, ← _root_.mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul,
      EReal.exp_add]
    have h1 : (N : ℝ) * a = ((k.succ : ℕ) : ℝ) * (c : ℝ)⁻¹ := by
      have h := hacR
      rw [eq_div_iff hNR.ne'] at h
      field_simp
      linarith [h]
    have h2 : (N : ℝ) * b = ((k'.succ : ℕ) : ℝ) * (c' : ℝ)⁻¹ := by
      have h := hbcR
      rw [eq_div_iff hNR.ne'] at h
      field_simp
      linarith [h]
    rw [h1, h2, EReal.coe_mul, EReal.coe_mul, _root_.mul_assoc, _root_.mul_assoc, ereal_exp_nat_mul,
      ereal_exp_nat_mul]
  refine ⟨(N : ℚ)⁻¹, (idealPow 𝔞 k.succ).mul (idealPow 𝔟 k'.succ), hq, htypeΨ, ?_, ?_, ?_⟩
  · intro x
    rw [hexp_eq]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (hexp x)) (ENNReal.pow_ne_top (hexp' x))
  · have hfun : (fun x => (EReal.exp ((((((N : ℚ)⁻¹ : ℚ) : ℝ))⁻¹ : ℝ) *
          (((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x))).toReal) =
        fun x => (EReal.exp ((((c : ℝ))⁻¹ : ℝ) * φ x)).toReal ^ k.succ *
          (EReal.exp ((((c' : ℝ))⁻¹ : ℝ) * ψ x)).toReal ^ k'.succ := by
      funext x
      rw [hexp_eq, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
    rw [hfun]
    exact fun e => ((hsmooth e).pow _).mul ((hsmooth' e).pow _)
  -- the resolution: a Kähler common model
  obtain ⟨Z, iTZ, iCZ, iMZ, _iConnZ, _iCompZ, ℓ₀, ℓ₁, hℓ₀, hℓ₁, hF, hover, hKZ⟩ :=
    exists_kahler_compact_smooth_common_model hf₀ hf₁ hK₀ hK₁
  have hint₀ := interior_exceptionalLocus_eq_empty_of_isAnalyticModification hℓ₀
  have hint₁ := interior_exceptionalLocus_eq_empty_of_isAnalyticModification hℓ₁
  set E₀ := EffectiveDivisor.totalTransform hℓ₀.1 hint₀ D₀
  set E₁ := EffectiveDivisor.totalTransform hℓ₁.1 hint₁ D₁
  refine ⟨Z, iTZ, iCZ, iMZ, f₀ ∘ ℓ₀,
    EffectiveDivisor.add (divisorSuccNsmul E₀ k) (divisorSuccNsmul E₁ k'), hF, hKZ,
    fun z => ?_⟩
  -- local data on `Y₀` and `Y₁`
  obtain ⟨V₀, -, -, s₀, hs₀, hsne₀, hsD₀, Φ₀, -, hΦ0₀, h₀, r₀, hr₀, -, hh₀, heq₀⟩ :=
    hloc₀ (ℓ₀ z)
  obtain ⟨N₀, hN₀, hzN₀, hloceq₀, H₀, hH₀, hpres₀⟩ := exists_local_resolution_presentation
    _ (mem_complexChartAt_source _) hs₀ hsne₀ hsD₀ Φ₀ hΦ0₀ hr₀ hh₀ heq₀
  obtain ⟨V₁, -, -, s₁, hs₁, hsne₁, hsD₁, Φ₁, -, hΦ0₁, h₁, r₁, hr₁, -, hh₁, heq₁⟩ :=
    hloc₁ (ℓ₁ z)
  obtain ⟨N₁, hN₁, hzN₁, hloceq₁, H₁, hH₁, hpres₁⟩ := exists_local_resolution_presentation
    _ (mem_complexChartAt_source _) hs₁ hsne₁ hsD₁ Φ₁ hΦ0₁ hr₁ hh₁ heq₁
  -- the local equation on `Z`
  set V : Set Z := ℓ₀ ⁻¹' N₀ ∩ ℓ₁ ⁻¹' N₁
  have hVopen : IsOpen V := (hN₀.preimage hℓ₀.1.continuous).inter (hN₁.preimage hℓ₁.1.continuous)
  have hzV : z ∈ V := ⟨hzN₀, hzN₁⟩
  have hE₀ : IsLocalEquationOn E₀.ideal V (fun w => s₀ (ℓ₀ w)) :=
    (IsLocalEquationOn.pullback hℓ₀.1 hint₀ hN₀ hloceq₀).mono inter_subset_left
  have hE₁ : IsLocalEquationOn E₁.ideal V (fun w => s₁ (ℓ₁ w)) :=
    (IsLocalEquationOn.pullback hℓ₁.1 hint₁ hN₁ hloceq₁).mono inter_subset_right
  have hEq := (IsLocalEquationOn.succNsmul hVopen hE₀ k).mul
    (divisorSuccNsmul E₀ k).isInvertible (divisorSuccNsmul E₁ k').isInvertible hVopen
    (IsLocalEquationOn.succNsmul hVopen hE₁ k')
  obtain ⟨hGhol, hGnon, hGgen⟩ := hEq
  -- coordinates on `Z`
  set χ := complexChartAt (n := n) z
  have hχz : χ.val z ∈ χ.val.target := χ.val.map_source (mem_complexChartAt_source z)
  set Φ := translationEquivAt χ.val.target χ.val.open_target (χ.val z) hχz
  have hO : IsOpen (χ.val.target ∩ χ.val.symm ⁻¹' V) := χ.val.isOpen_inter_preimage_symm hVopen
  have hχzO : χ.val z ∈ χ.val.target ∩ χ.val.symm ⁻¹' V :=
    ⟨hχz, by
      change χ.val.symm (χ.val z) ∈ V
      rw [χ.val.left_inv (mem_complexChartAt_source z)]
      exact hzV⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO _ hχzO
  have hball : ∀ w ∈ ball (0 : ComplexModel n) r,
      w + χ.val z ∈ χ.val.target ∩ χ.val.symm ⁻¹' V := by
    intro w hw
    apply hrO
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
    simpa using hw
  have hS₀ := contDiffOn_comp_holomorphic hℓ₀.1 hN₀ hH₀ χ
  have hS₁ := contDiffOn_comp_holomorphic hℓ₁.1 hN₁ hH₁ χ
  have htrans : ContDiffOn ℝ ∞ (fun w : ComplexModel n => w + χ.val z) (ball 0 r) :=
    (contDiff_id.add contDiff_const).contDiffOn
  have hmaps₀ : MapsTo (fun w : ComplexModel n => w + χ.val z) (ball 0 r)
      (χ.val.target ∩ χ.val.symm ⁻¹' (ℓ₀ ⁻¹' N₀)) :=
    fun w hw => ⟨(hball w hw).1, (hball w hw).2.1⟩
  have hmaps₁ : MapsTo (fun w : ComplexModel n => w + χ.val z) (ball 0 r)
      (χ.val.target ∩ χ.val.symm ⁻¹' (ℓ₁ ⁻¹' N₁)) :=
    fun w hw => ⟨(hball w hw).1, (hball w hw).2.2⟩
  refine ⟨V, hVopen, hzV, _, hGhol, hGnon, hGgen, Φ, subset_rfl, sub_self _,
    fun w => (a : ℝ) * H₀ (ℓ₀ (χ.val.symm (w + χ.val z))) +
      (b : ℝ) * H₁ (ℓ₁ (χ.val.symm (w + χ.val z))), r, hr, fun w hw => (hball w hw).1,
    ((hS₀.comp htrans hmaps₀).const_smul (a : ℝ)).add ((hS₁.comp htrans hmaps₁).const_smul (b : ℝ)),
    fun w hw => ⟨(hball w hw).2, ?_⟩⟩
  -- the formula
  set p := χ.val.symm (w + χ.val z)
  have hpV : p ∈ V := (hball w hw).2
  change ((a : ℝ) : EReal) * φ (f₀ (ℓ₀ p)) + ((b : ℝ) : EReal) * ψ (f₀ (ℓ₀ p)) = _
  rw [show f₀ (ℓ₀ p) = f₁ (ℓ₁ p) from congrFun hover p]
  rw [show f₁ (ℓ₁ p) = f₀ (ℓ₀ p) from (congrFun hover p).symm, hpres₀ _ hpV.1]
  rw [show f₀ (ℓ₀ p) = f₁ (ℓ₁ p) from congrFun hover p, hpres₁ _ hpV.2]
  rw [ereal_mul_add_coe haR.le, ereal_mul_add_coe hbR.le, hacR, hbcR]
  change _ = (((((N : ℚ)⁻¹ : ℚ) : ℝ)) : EReal) * ENNReal.log (ENNReal.ofReal
    (‖s₀ (ℓ₀ p) ^ (k + 1) * s₁ (ℓ₁ p) ^ (k' + 1)‖ ^ 2)) +
      (((a : ℝ) * H₀ (ℓ₀ p) + (b : ℝ) * H₁ (ℓ₁ p) : ℝ) : EReal)
  rw [log_norm_sq_pow_mul_pow, EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (by positivity)) (EReal.coe_ne_top _), ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_add]
  have e1 : (((k.succ : ℕ) : ℝ) / N) = ((((N : ℚ)⁻¹ : ℚ) : ℝ)) * ((k + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have e2 : (((k'.succ : ℕ) : ℝ) / N) = ((((N : ℚ)⁻¹ : ℚ) : ℝ)) * ((k' + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [e1, e2]
  exact add_add_add_comm _ _ _ _

/-- `aφ + bψ` is gentle for `a, b ∈ ℚ_{≥ 0}` not both zero (and `aφ + bψ` quasi-psh). -/
theorem exists_hasGentleAnalyticSingularitiesOfType_add_nonneg_smul {φ ψ : X → EReal}
    {c c' : ℚ} {𝔞 𝔟 : GermIdeal n X}
    (hφ : HasGentleAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hψ : HasGentleAnalyticSingularitiesOfType (n := n) ψ c' 𝔟) {a b : ℚ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b)
    (hq : IsGlobalQuasiPshPotential (n := n)
      (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x)) :
    ∃ (c'' : ℚ) (𝔠 : GermIdeal n X), HasGentleAnalyticSingularitiesOfType (n := n)
      (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) c'' 𝔠 := by
  rcases ha.lt_or_eq with ha | rfl
  · rcases hb.lt_or_eq with hb | rfl
    · exact exists_hasGentleAnalyticSingularitiesOfType_add_smul hφ hψ ha hb hq
    · have hfun : (fun x => ((a : ℝ) : EReal) * φ x + (((0 : ℚ) : ℝ) : EReal) * ψ x) =
          fun x => ((a : ℝ) : EReal) * φ x := by
        funext x
        simp
      rw [hfun] at hq ⊢
      exact ⟨a * c, 𝔞, hasGentleAnalyticSingularitiesOfType_pos_rat_smul hφ ha hq⟩
  · have hb : 0 < b := hab.resolve_left (lt_irrefl 0)
    have hfun : (fun x => (((0 : ℚ) : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) =
        fun x => ((b : ℝ) : EReal) * ψ x := by
      funext x
      simp
    rw [hfun] at hq ⊢
    exact ⟨b * c', 𝔟, hasGentleAnalyticSingularitiesOfType_pos_rat_smul hψ hb hq⟩

/-- **Blueprint `tok:gentle-sum`, `𝒢`**: if `T ∈ 𝒢(ξ)`, `S ∈ 𝒢(ξ')` and `a, b ∈ ℚ_{≥ 0}` are not
both zero, then `aT + bS ∈ 𝒢(aξ + bξ')`. -/
theorem add_smul_mem_gentleCurrents {θ θ' : ClosedRealOneOneForm n X} {φ ψ : X → EReal}
    (hφ : φ ∈ gentleCurrents θ) (hψ : ψ ∈ gentleCurrents θ') {a b : ℚ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : 0 < a ∨ 0 < b) :
    (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) ∈
      gentleCurrents ((a : ℝ) • θ + (b : ℝ) • θ') := by
  obtain ⟨hφpsh, c, 𝔞, -, hφg⟩ := hφ
  obtain ⟨hψpsh, c', 𝔟, -, hψg⟩ := hψ
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hpsh := isThetaPshPotential_add_from_positive_sum
    (isThetaPshPotential_nonneg_smul hφpsh haR) (isThetaPshPotential_nonneg_smul hψpsh hbR)
  obtain ⟨c'', 𝔠, hg⟩ := exists_hasGentleAnalyticSingularitiesOfType_add_nonneg_smul hφg hψg
    ha hb hab hpsh.quasiPshPotential
  exact ⟨hpsh, c'', 𝔠, ⟨_, hpsh⟩, hg⟩

/-- **Blueprint `tok:gentle-sum`, `𝒢`, all coefficients**: on a compact connected Kähler manifold,
if `T ∈ 𝒢(ξ)`, `S ∈ 𝒢(ξ')` and `a, b ∈ ℚ_{≥ 0}`, then `aT + bS ∈ 𝒢(aξ + bξ')`. -/
theorem add_smul_mem_gentleCurrents_of_kahler (hK : Nonempty (KahlerBackground n X))
    {θ θ' : ClosedRealOneOneForm n X} {φ ψ : X → EReal}
    (hφ : φ ∈ gentleCurrents θ) (hψ : ψ ∈ gentleCurrents θ') {a b : ℚ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) ∈
      gentleCurrents ((a : ℝ) • θ + (b : ℝ) • θ') := by
  by_cases hab : 0 < a ∨ 0 < b
  · exact add_smul_mem_gentleCurrents hφ hψ ha hb hab
  push Not at hab
  obtain rfl : a = 0 := le_antisymm hab.1 ha
  obtain rfl : b = 0 := le_antisymm hab.2 hb
  have hpsh := isThetaPshPotential_add_from_positive_sum
    (isThetaPshPotential_nonneg_smul (c := ((0 : ℚ) : ℝ)) hφ.1 (by norm_num))
    (isThetaPshPotential_nonneg_smul (c := ((0 : ℚ) : ℝ)) hψ.1 (by norm_num))
  have hfun : (fun x => (((0 : ℚ) : ℝ) : EReal) * φ x + (((0 : ℚ) : ℝ) : EReal) * ψ x) =
      fun _ => (0 : EReal) := by
    funext x
    simp
  refine ⟨hpsh, 1, unitIdeal n X, ⟨_, hpsh⟩, ?_⟩
  rw [hfun]
  exact hasGentleAnalyticSingularitiesOfType_zero hK

omit [ConnectedSpace X] [CompactSpace X] in
/-- `θ + dd^c φ ≥ κ` gives `aθ + bθ' + dd^c(aφ + bψ) ≥ aκ` for `a > 0`. -/
theorem isKahlerCurrentPotential_add_smul {θ θ' : ClosedRealOneOneForm n X}
    {φ ψ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ) (hψ : IsThetaPshPotential θ'.val ψ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    IsKahlerCurrentPotential (a • θ + b • θ')
      (fun x => (a : EReal) * φ x + (b : EReal) * ψ x) := by
  obtain ⟨κ, hκ⟩ := hφ
  refine ⟨KahlerBackground.smul ha κ, ?_⟩
  have hform : a • (θ - κ.form) + b • θ' = (a • θ + b • θ') - (KahlerBackground.smul ha κ).form := by
    rw [KahlerBackground.smul_form, smul_sub]
    abel
  rw [← hform]
  exact isThetaPshPotential_add_from_positive_sum (isThetaPshPotential_nonneg_smul hκ ha.le)
    (isThetaPshPotential_nonneg_smul hψ hb)

/-- **Blueprint `tok:gentle-sum`, `Ω`**: if `T ∈ Ω(ξ)`, `S ∈ 𝒢(ξ')`, `a ∈ ℚ_{>0}` and `b ∈ ℚ_{≥ 0}`,
then `aT + bS ∈ Ω(aξ + bξ')`. -/
theorem add_smul_mem_gentleKahlerCurrents {θ θ' : ClosedRealOneOneForm n X} {φ ψ : X → EReal}
    (hφ : φ ∈ gentleKahlerCurrents θ) (hψ : ψ ∈ gentleCurrents θ') {a b : ℚ} (ha : 0 < a)
    (hb : 0 ≤ b) :
    (fun x => ((a : ℝ) : EReal) * φ x + ((b : ℝ) : EReal) * ψ x) ∈
      gentleKahlerCurrents ((a : ℝ) • θ + (b : ℝ) • θ') :=
  ⟨add_smul_mem_gentleCurrents hφ.1 hψ ha.le hb (Or.inl ha),
    isKahlerCurrentPotential_add_smul hφ.2 hψ.1 (by exact_mod_cast ha) (by exact_mod_cast hb)⟩

end Manifold

end SGPT.Okounkov.TranscendentalCore
