import SGPT.NPP.RieszCurrent
import SGPT.NPP.NonPluripolarCurrent3DegreeOne
import SGPT.NPP.NonPluripolarCurrent3Gauge
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing

/-!
# The degree-one non-pluripolar product in one variable

Source `ex:1Dnpp` (`chapter_npp.tex`), the reverse inequality `1_{u>-∞} dd^c u ≤ (dd^c u)^1` in
one complex variable (blueprint `claude-rc:planar-reverse`), hence the identity
`(dd^c u)^1 = 1_{u>-∞} dd^c u` for every psh `u` on an open subset of `ℂ¹`
(`nonPluripolarProduct_eq_indicator_ddcL1_of_dim_one`).

The proof (the route of Xia, *Foundations of pluripotential theory*,
`prop:nonpluripolar-degree-one-restriction`, "One variable", with bounded instead of continuous
potentials, so that no continuity principle is needed): on a disc `V = D(x, r)` with
`D̄ ⊆ U`, let `ν = 1_V dd^c u` and `p = p_ν` its logarithmic potential.  Then `dd^c p = dd^c u`
on `V`, so `u = p + h` with `h` pluriharmonic (Weyl), and `⟨dd^c u⟩ = ⟨dd^c p⟩` on `V`.  With
`ν_f = 1_{p > -∞} ν` and the compact sets `A_N = D̄ ∩ {p_{ν_f} ≥ -N}`, the measures
`λ_N = 1_{A_N} ν_f` increase to `ν_f`, their potentials are bounded (the closest-point bound),
and `p = p_{λ_N} + p_{ν - λ_N}`; multilinearity gives
`⟨dd^c u⟩ = dd^c p_{λ_N} + ⟨dd^c p_{ν - λ_N}⟩ ≥ λ_N`, and `N → ∞` gives
`⟨dd^c u⟩ ≥ ν_f = 1_{u > -∞} dd^c u` on `V`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.Riesz

open Set Filter MeasureTheory TopologicalSpace SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.NPP.NonPluripolarCurrent
open scoped Topology ENNReal Distributions

/-- The level `log (16 r²)` bounds the kernel for `z ∈ D(x, 2r)` and `w ∈ D̄(x, r)`. -/
theorem logNormSq_sub_le_of_mem {x z w : ComplexModel 1} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ Metric.ball x (2 * r)) (hw : w ∈ Metric.closedBall x r) :
    logNormSq (z - w) ≤ ((Real.log (16 * r ^ 2) : ℝ) : EReal) := by
  by_cases hzw : z = w
  · rw [hzw, sub_self, logNormSq_zero]
    exact bot_le
  rw [logNormSq_of_ne_zero (sub_ne_zero.mpr hzw), EReal.coe_le_coe_iff]
  have hpos : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  refine Real.log_le_log (by positivity) ?_
  rw [Metric.mem_ball, dist_eq_norm] at hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h3 : ‖z - w‖ ≤ 3 * r := by
    calc ‖z - w‖ = ‖(z - x) - (w - x)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖w - x‖ := norm_sub_le _ _
      _ ≤ 3 * r := by linarith
  nlinarith

/-- Two restrictions of currents are restrictions of the difference. -/
theorem restrict_sub' {n q : ℕ} {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    (S T : LocalProductCurrent n U q) :
    restrict hVU (S - T) = restrict hVU S - restrict hVU T := by
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply, LinearMap.sub_apply, _root_.sub_apply]

/-- The trace measure does not depend on the proof of positivity, nor on the presentation of the
current. -/
theorem traceMeasure_eq_of_eq {n q : ℕ} {U : Opens (ComplexModel n)}
    {S T : LocalProductCurrent n U q} (h : S = T) (hS : IsPositive S) (hT : IsPositive T) :
    hS.traceMeasure = hT.traceMeasure := by
  subst h
  rfl

/-- **The planar case on a disc.** -/
theorem isPositive_nonPluripolarProduct_sub_on_ball {U : Opens (ComplexModel 1)}
    {u : ComplexModel 1 → EReal} (hu : IsL1PshOn U u) (hqp : 0 + 1 = 1)
    {x : ComplexModel 1} {r : ℝ} (hr : 0 < r) (hrU : Metric.closedBall x r ⊆ U) :
    IsPositive (NonPluripolarCurrent.nonPluripolarProduct hqp
        (⟨Metric.ball x r, Metric.isOpen_ball⟩ : Opens (ComplexModel 1))
        (fun _ : Fin 1 => u) -
      mulBorel (ddcL1 (m := 0) (⟨Metric.ball x r, Metric.isOpen_ball⟩ : Opens (ComplexModel 1)) u)
        ({z | z ∈ U ∧ u z ≠ ⊥}.indicator fun _ => (1 : ℝ))) := by
  classical
  set V : Opens (ComplexModel 1) := ⟨Metric.ball x r, Metric.isOpen_ball⟩ with hVdef
  set K : Set (ComplexModel 1) := Metric.closedBall x r with hKdef
  have hKc : IsCompact K := isCompact_closedBall x r
  have hVK : (V : Set (ComplexModel 1)) ⊆ K := Metric.ball_subset_closedBall
  have hVU : V ≤ U := fun z hz => hrU (hVK hz)
  have huV : IsL1PshOn V u := hu.mono hVU
  -- the measure `ν = 1_V dd^c u`
  have hTU : IsPositive (ddcL1 (m := 0) U u) := hu.isPositive_ddcL1
  have hTV : IsPositive (ddcL1 (m := 0) V u) := huV.isPositive_ddcL1
  set ν : Measure (ComplexModel 1) := hTU.traceMeasure.restrict V with hνdef
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono hVK).trans_lt (hTU.traceMeasure_lt_top hKc hrU)
  have hνK : ν Kᶜ = 0 := by
    rw [hνdef, Measure.restrict_apply hKc.measurableSet.compl]
    exact measure_mono_null (fun z hz => hz.1 (hVK hz.2)) (measure_empty (μ := hTU.traceMeasure))
  set C : ℝ := Real.log (16 * r ^ 2) with hCdef
  set W2 : Set (ComplexModel 1) := Metric.ball x (2 * r) with hW2def
  have hKW2 : K ⊆ W2 := Metric.closedBall_subset_ball (by linarith)
  have hVW2 : (V : Set (ComplexModel 1)) ⊆ W2 := fun z hz => hKW2 (hVK hz)
  have hC2 : ∀ z ∈ W2, ∀ w ∈ K, logNormSq (z - w) ≤ (C : EReal) := fun z hz w hw =>
    logNormSq_sub_le_of_mem hr hz hw
  have hCV : ∀ z ∈ (V : Set (ComplexModel 1)), ∀ w ∈ K, logNormSq (z - w) ≤ (C : EReal) :=
    fun z hz => hC2 z (hVW2 hz)
  -- `dd^c u` against test functions on `V`
  have hTVapply : ∀ φ : 𝓓(V, ℝ), ddcL1 (m := 0) V u (kahlerPower 1 0) φ = ∫ w, φ w ∂ν := by
    intro φ
    rw [← restrict_ddcL1 hVU hu.locallyIntegrableOn, LocalBedfordTaylorLocality.restrict_apply,
      ← hTU.integral_traceMeasure, hνdef]
    have hf : ((extTest hVU φ : 𝓓(U, ℝ)) : ComplexModel 1 → ℝ) = (φ : ComplexModel 1 → ℝ) :=
      funext (extTest_apply hVU φ)
    rw [hf]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      testFunction_eq_zero_of_notMem φ hz).symm
  -- the potential and the Riesz decomposition
  set pν : ComplexModel 1 → EReal := logPotential C ν with hpνdef
  have hpV : IsL1PshOn V pν := isL1PshOn_logPotential hKc hνK hCV
  have hddc : ddcL1 (m := 0) V u = ddcL1 (m := 0) V pν := by
    refine eq_of_apply_kahlerPower fun φ => ?_
    rw [hTVapply, ddcL1_logPotential_apply_kahlerPower hKc hνK hCV]
  obtain ⟨g, -, -, hug⟩ := SGPT.Currents.exists_pluriharmonic_of_ddcL1_eq hpV huV hddc.symm
  have hpole : ∀ z ∈ (V : Set (ComplexModel 1)), u z ≠ ⊥ ↔ pν z ≠ ⊥ := by
    intro z hz
    rw [hug z hz]
    constructor
    · intro h h'
      exact h (by rw [h', EReal.bot_add])
    · intro h h'
      rcases EReal.add_eq_bot_iff.mp h' with h'' | h''
      · exact h h''
      · exact EReal.coe_ne_bot _ h''
  -- the finite part `ν_f = 1_{p > -∞} ν`
  have hXmeas : Measurable fun z => ∫⁻ w, kernelDeficit C z w ∂ν :=
    (measurable_kernelDeficit C).lintegral_prod_right'
  set F : Set (ComplexModel 1) := {z | pν z ≠ ⊥} with hFdef
  have hFm : MeasurableSet F := by
    have : F = {z | ∫⁻ w, kernelDeficit C z w ∂ν < ⊤} := by
      ext z
      simp only [hFdef, mem_ofPred_eq, hpνdef, Ne, logPotential_eq_bot_iff, lt_top_iff_ne_top]
    rw [this]
    exact measurableSet_lt hXmeas measurable_const
  set νf : Measure (ComplexModel 1) := ν.restrict F with hνfdef
  have hνfle : νf ≤ ν := Measure.restrict_le_self
  have hle0 : ∀ {μ' : Measure (ComplexModel 1)}, μ' ≤ ν → μ' Kᶜ = 0 := fun h =>
    le_antisymm ((Measure.le_iff'.mp h Kᶜ).trans hνK.le) zero_le
  have hνfK : νf Kᶜ = 0 := hle0 hνfle
  set pf : ComplexModel 1 → EReal := logPotential C νf with hpfdef
  have hpfusc : UpperSemicontinuousOn pf K :=
    (discPshOn_logPotential hKc.measurableSet hνfK hC2).upperSemicontinuousOn.mono hKW2
  -- the compact superlevel sets and the measures `λ_N`
  set A : ℕ → Set (ComplexModel 1) := fun N => K ∩ pf ⁻¹' Ici (((-(N : ℝ)) : ℝ) : EReal)
    with hAdef
  have hAc : ∀ N, IsCompact (A N) := fun N => hpfusc.isCompact_inter_preimage_Ici hKc _
  have hAmono : Monotone A := by
    intro N N' hNN' z hz
    refine ⟨hz.1, ?_⟩
    simp only [mem_preimage, mem_Ici] at hz ⊢
    have : (N : ℝ) ≤ N' := by exact_mod_cast hNN'
    exact le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hz.2
  set G : ℕ → Set (ComplexModel 1) := fun N => F ∩ A N with hGdef
  have hGm : ∀ N, MeasurableSet (G N) := fun N => hFm.inter (hAc N).isClosed.measurableSet
  have hGmono : Monotone G := fun N N' h => inter_subset_inter_right _ (hAmono h)
  set lamN : ℕ → Measure (ComplexModel 1) := fun N => ν.restrict (G N) with hlamdef
  set ρN : ℕ → Measure (ComplexModel 1) := fun N => ν.restrict (G N)ᶜ with hρdef
  have hsplit : ∀ N, lamN N + ρN N = ν := fun N => Measure.restrict_add_restrict_compl (hGm N)
  have hlamle : ∀ N, lamN N ≤ ν := fun N => Measure.restrict_le_self
  have hρle : ∀ N, ρN N ≤ ν := fun N => Measure.restrict_le_self
  have hlamνf : ∀ N, lamN N ≤ νf := fun N => Measure.restrict_mono inter_subset_left le_rfl
  have hlamK : ∀ N, lamN N Kᶜ = 0 := fun N => hle0 (hlamle N)
  have hρK : ∀ N, ρN N Kᶜ = 0 := fun N => hle0 (hρle N)
  set mass : ℝ := (ν univ).toReal with hmassdef
  have hmass_le : ∀ {μ' : Measure (ComplexModel 1)}, μ' ≤ ν → (μ' univ).toReal ≤ mass :=
    fun h => ENNReal.toReal_mono (measure_ne_top ν univ) (Measure.le_iff'.mp h univ)
  have hmass0 : 0 ≤ mass := ENNReal.toReal_nonneg
  -- the potentials of `λ_N` are bounded
  set Mb : ℕ → ℝ := fun N => N + 2 * |C| * mass + mass * Real.log 4 with hMbdef
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlamlower : ∀ N z, (((-Mb N) : ℝ) : EReal) ≤ logPotential C (lamN N) z := by
    intro N z
    rcases (A N).eq_empty_or_nonempty with hAe | hAne
    · have h0 : lamN N = 0 := by
        rw [hlamdef]
        simp only
        rw [show G N = ∅ from by rw [hGdef]; simp only [hAe, inter_empty], Measure.restrict_empty]
      rw [h0]
      have : logPotential C 0 z = 0 := by simp [logPotential]
      rw [this, EReal.coe_nonpos]
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : 0 ≤ |C| := abs_nonneg C
      simp only [hMbdef]
      nlinarith
    · have hlamA : lamN N (A N)ᶜ = 0 := by
        rw [hlamdef]
        simp only
        rw [Measure.restrict_apply (hAc N).isClosed.measurableSet.compl]
        exact measure_mono_null (fun z hz => hz.1 hz.2.2) (measure_empty (μ := ν))
      have hM : ∀ y ∈ A N, ((-((N : ℝ) + 2 * |C| * mass) : ℝ) : EReal) ≤
          logPotential C (lamN N) y := by
        intro y hy
        have hpfy : (((-(N : ℝ)) : ℝ) : EReal) ≤ pf y := hy.2
        have hpfne : pf y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hpfy
        have hXf := lintegral_kernelDeficit_eq (C := C) (ν := νf) hpfne
        have hpfr : -(N : ℝ) ≤ (pf y).toReal := by
          have hpfy' := hpfy
          rw [← EReal.coe_toReal (show pf y ≠ ⊤ from logPotential_ne_top C νf y) hpfne] at hpfy'
          exact EReal.coe_le_coe_iff.mp hpfy'
        set D : ℝ := max ((νf univ).toReal * C + N) 0 with hDdef
        have hXlam : ∫⁻ w, kernelDeficit C y w ∂(lamN N) ≤ ENNReal.ofReal D := by
          refine (lintegral_kernelDeficit_mono (hlamνf N) y).trans ?_
          rw [hXf]
          exact ENNReal.ofReal_le_ofReal (le_trans (by linarith) (le_max_left _ _))
        refine le_trans ?_ (coe_sub_le_logPotential (le_max_right _ _) hXlam)
        rw [EReal.coe_le_coe_iff]
        have h1 : -(|C| * mass) ≤ ((lamN N) univ).toReal * C := by
          have := hmass_le (hlamle N)
          have h0 : 0 ≤ ((lamN N) univ).toReal := ENNReal.toReal_nonneg
          nlinarith [abs_nonneg C, neg_abs_le C, le_abs_self C]
        have h2 : D ≤ |C| * mass + N := by
          refine max_le ?_ (by positivity)
          have := hmass_le hνfle
          have h0 : 0 ≤ (νf univ).toReal := ENNReal.toReal_nonneg
          nlinarith [abs_nonneg C, neg_abs_le C, le_abs_self C]
        linarith
      have h := logPotential_ge_of_closest (hAc N) hAne hlamA hM z
      refine le_trans ?_ h
      rw [EReal.coe_le_coe_iff]
      have := hmass_le (hlamle N)
      simp only [hMbdef]
      nlinarith
  -- the bounded potentials `v_N` and the remainders `w_N`
  have hlamfin : ∀ N z, logPotential C (lamN N) z ≠ ⊥ := fun N z =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlamlower N z)
  set v : ℕ → ComplexModel 1 → ℝ := fun N z => (logPotential C (lamN N) z).toReal with hvdef
  have hvcoe : ∀ N, (fun z => (v N z : EReal)) = logPotential C (lamN N) := fun N =>
    funext fun z => EReal.coe_toReal (logPotential_ne_top _ _ _) (hlamfin N z)
  have hlamL1 : ∀ N, IsL1PshOn V (logPotential C (lamN N)) := fun N =>
    isL1PshOn_logPotential hKc (hlamK N) hCV
  have hvB : ∀ N, IsLocallyBoundedPshOn V (v N) := by
    intro N
    refine ⟨by rw [hvcoe N]; exact (hlamL1 N).psh, fun z hz =>
      ⟨V, hz, le_rfl, max (Mb N) (|C| * mass), fun w _ => ?_⟩⟩
    have hlo := hlamlower N w
    have hhi := logPotential_le C (lamN N) w
    rw [← EReal.coe_toReal (logPotential_ne_top _ _ _) (hlamfin N w), EReal.coe_le_coe_iff]
      at hlo hhi
    have h1 : ((lamN N) univ).toReal * C ≤ |C| * mass := by
      have := hmass_le (hlamle N)
      have h0 : 0 ≤ ((lamN N) univ).toReal := ENNReal.toReal_nonneg
      nlinarith [abs_nonneg C, le_abs_self C]
    rw [abs_le]
    constructor
    · linarith [le_max_left (Mb N) (|C| * mass)]
    · linarith [le_max_right (Mb N) (|C| * mass)]
  have hvL1 : ∀ N, IsL1PshOn V (fun z => (v N z : EReal)) := fun N => by
    rw [hvcoe N]; exact hlamL1 N
  have hwV : ∀ N, IsL1PshOn V (logPotential C (ρN N)) := fun N =>
    isL1PshOn_logPotential hKc (hρK N) hCV
  have hdecomp : ∀ N z, pν z = (v N z : EReal) + logPotential C (ρN N) z := by
    intro N z
    have h := logPotential_add C (lamN N) (ρN N) z
    rw [hsplit N] at h
    rw [hpνdef, h, ← hvcoe N]
  -- the density of `dd^c u` on `V`
  have hdens : IsLocalDensity (U := V) ν (fun _ => (1 : ℝ)) :=
    ⟨by rw [hνdef, Measure.restrict_apply V.isOpen.measurableSet.compl]; simp,
      fun K' _ _ => measure_lt_top ν K', measurable_const,
      fun K' _ _ => ⟨1, fun _ _ => by simp⟩⟩
  have hrep : ∀ ψ : 𝓓(V, ℝ), ddcL1 (m := 0) V u (kahlerPower 1 0) ψ = ∫ x, ψ x * 1 ∂ν := by
    intro ψ
    simp only [mul_one]
    exact hTVapply ψ
  -- each truncation gives a lower bound
  have hWu : IsWellDefinedOn hqp V (fun _ : Fin 1 => u) := isWellDefinedOn_one huV hqp
  have hSu : NonPluripolarCurrent.nonPluripolarProduct hqp V (fun _ : Fin 1 => u) =
      NonPluripolarCurrent.nonPluripolarProduct hqp V (fun _ : Fin 1 => pν) :=
    (nonPluripolarProduct_eq_of_ddcL1_eq hqp (U := V) (φ := fun _ : Fin 1 => u)
      (ψ := fun _ : Fin 1 => pν) (fun _ => huV) (fun _ => hpV) (fun _ => hddc)).2 hWu
  have hstep : ∀ N, IsPositive (NonPluripolarCurrent.nonPluripolarProduct hqp V
      (fun _ : Fin 1 => u) - mulBorel (ddcL1 (m := 0) V u) ((G N).indicator fun _ => (1 : ℝ))) := by
    intro N
    set φN : Fin 1 → ComplexModel 1 → EReal := fun _ z => (v N z : EReal) with hφNdef
    set ψN : ComplexModel 1 → EReal := logPotential C (ρN N) with hψNdef
    have hφpsh : ∀ i, PlurisubharmonicOn (φN i) V := fun _ => (hvB N).1
    have hψpsh : PlurisubharmonicOn ψN V := (hwV N).psh
    have hφnd : LocallyNondegenerate fun x : V => φN 0 x := locallyNondegenerate_of_isL1PshOn (hvL1 N)
    have hψnd : LocallyNondegenerate fun x : V => ψN x := locallyNondegenerate_of_isL1PshOn (hwV N)
    have hWφ : IsWellDefinedOn hqp V φN :=
      isWellDefinedOn_of_isLocallyBoundedPshOn hqp (u := fun _ => v N) (fun _ => hvB N)
    have hupd : Function.update φN 0 ψN = fun _ => ψN := by
      funext i
      fin_cases i
      simp
    have hWψ : IsWellDefinedOn hqp V (Function.update φN 0 ψN) := by
      rw [hupd]
      exact isWellDefinedOn_one (hwV N) hqp
    have hcombo := nonPluripolarProduct_combo hqp hφpsh hψpsh hφnd hψnd one_pos one_pos hWφ hWψ
    have hcongr : NonPluripolarCurrent.nonPluripolarProduct hqp V (fun _ : Fin 1 => pν) =
        NonPluripolarCurrent.nonPluripolarProduct hqp V (comboTuple φN 0 1 1 ψN) := by
      refine (nonPluripolarProduct_congr hqp (fun i z _ => ?_)).2
      fin_cases i
      simp only [comboTuple, EReal.coe_one, one_mul, hφNdef, hψNdef]
      exact hdecomp N z
    have hbt : NonPluripolarCurrent.nonPluripolarProduct hqp V φN =
        mulBorel (ddcL1 (m := 0) V u) ((G N).indicator fun _ => (1 : ℝ)) := by
      rw [show φN = fun i z => ((fun _ : Fin 1 => v N) i z : EReal) from rfl,
        nonPluripolarProduct_of_isLocallyBoundedPshOn hqp (u := fun _ => v N) (fun _ => hvB N)]
      change ddcMul (oneCurrent V) (v N) = _
      rw [← ddcL1_coe_eq_ddcMul (hvB N), hvcoe N]
      refine eq_of_apply_kahlerPower fun φ => ?_
      rw [ddcL1_logPotential_apply_kahlerPower hKc (hlamK N) hCV,
        mulBorel_apply_of_integral_eq hTV (kahlerPower 1 0) hdens hrep
          (measurable_const.indicator (hGm N)) (isLocallyBoundedOn_indicator_one _) φ]
      rw [hlamdef]
      simp only
      rw [← integral_indicator (hGm N)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ G N <;> simp [Set.indicator, hz]
    rw [hSu, hcongr, hcombo, one_smul, one_smul, hbt, add_sub_cancel_left]
    exact isPositive_nonPluripolarProduct hqp (fun i => by rw [hupd]; exact hψpsh) hWψ
  -- the limit `N → ∞`
  set Ginf : Set (ComplexModel 1) := ⋃ N, G N with hGinfdef
  have hGinfm : MeasurableSet Ginf := MeasurableSet.iUnion hGm
  have hind_tendsto : ∀ z, Tendsto (fun N => (G N).indicator (fun _ => (1 : ℝ)) z) atTop
      (𝓝 (Ginf.indicator (fun _ => (1 : ℝ)) z)) := by
    intro z
    by_cases hz : z ∈ Ginf
    · obtain ⟨N₀, hN₀⟩ := mem_iUnion.mp hz
      rw [Set.indicator_of_mem hz]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N₀] with N hN
      rw [Set.indicator_of_mem (hGmono hN hN₀)]
    · rw [Set.indicator_of_notMem hz]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
      show (0 : ℝ) = (G N).indicator (fun _ => (1 : ℝ)) z
      rw [Set.indicator_of_notMem fun h => hz (mem_iUnion.mpr ⟨N, h⟩)]
  have hlim : WeakTendsto (fun N => NonPluripolarCurrent.nonPluripolarProduct hqp V
        (fun _ : Fin 1 => u) - mulBorel (ddcL1 (m := 0) V u) ((G N).indicator fun _ => (1 : ℝ)))
      (NonPluripolarCurrent.nonPluripolarProduct hqp V (fun _ : Fin 1 => u) -
        mulBorel (ddcL1 (m := 0) V u) (Ginf.indicator fun _ => (1 : ℝ))) := by
    intro γ φ
    simp only [LinearMap.sub_apply, _root_.sub_apply]
    refine tendsto_const_nhds.sub ?_
    simp_rw [mulBorel_apply hTV (measurable_const.indicator (hGm _))
      (isLocallyBoundedOn_indicator_one _) γ φ]
    rw [mulBorel_apply hTV (measurable_const.indicator hGinfm) (isLocallyBoundedOn_indicator_one _)
      γ φ]
    have hint := IsPositive.integrable_mul_density hTV (u := fun _ => (1 : ℝ)) measurable_const
      (fun _ _ _ => ⟨1, fun _ _ => by simp⟩) γ φ
    refine tendsto_integral_of_dominated_convergence (fun z => ‖φ z * (1 * hTV.density γ z)‖)
      (fun N => (IsPositive.integrable_mul_density hTV (measurable_const.indicator (hGm N))
        (isLocallyBoundedOn_indicator_one _) γ φ).aestronglyMeasurable) hint.norm
      (fun N => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · rw [norm_mul, norm_mul, norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        (norm_nonneg _)
      by_cases hz : z ∈ G N <;> simp [Set.indicator, hz]
    · exact tendsto_const_nhds.mul ((hind_tendsto z).mul tendsto_const_nhds)
  have hposlim := isPositive_of_weakTendsto hstep hlim
  -- identification of the limit set with the finite locus of `u` on `V`
  have hUm : MeasurableSet {z | z ∈ U ∧ u z ≠ ⊥} := by
    rw [← iUnion_strictLocus_one (m := 0) (U := U) (u := u)]
    exact MeasurableSet.iUnion (BedfordTaylorTopDegree.measurableSet_strictLocus
      (fun _ : Fin 1 => hu.psh))
  have hiff : ∀ z ∈ (V : Set (ComplexModel 1)), z ∈ Ginf ↔ z ∈ {z | z ∈ U ∧ u z ≠ ⊥} := by
    intro z hz
    constructor
    · intro h
      obtain ⟨N, hN⟩ := mem_iUnion.mp h
      exact ⟨hVU hz, (hpole z hz).mpr hN.1⟩
    · rintro ⟨-, huz⟩
      have hpz : pν z ≠ ⊥ := (hpole z hz).mp huz
      have hpfz : pf z ≠ ⊥ := logPotential_ne_bot_of_le hνfle hpz
      have hpft : pf z ≠ ⊤ := logPotential_ne_top C νf z
      obtain ⟨N, hN⟩ := exists_nat_gt (-(pf z).toReal)
      refine mem_iUnion.mpr ⟨N, hpz, hVK hz, ?_⟩
      show (((-(N : ℝ)) : ℝ) : EReal) ≤ pf z
      rw [← EReal.coe_toReal hpft hpfz, EReal.coe_le_coe_iff]
      linarith
  have hind : mulBorel (ddcL1 (m := 0) V u) (Ginf.indicator fun _ => (1 : ℝ)) =
      mulBorel (ddcL1 (m := 0) V u) ({z | z ∈ U ∧ u z ≠ ⊥}.indicator fun _ => (1 : ℝ)) := by
    ext γ φ
    rw [mulBorel_apply hTV (measurable_const.indicator hGinfm) (isLocallyBoundedOn_indicator_one _),
      mulBorel_apply hTV (measurable_const.indicator hUm) (isLocallyBoundedOn_indicator_one _)]
    refine integral_congr_ae ?_
    have hVae : ∀ᵐ z ∂hTV.traceMeasure, z ∈ (V : Set (ComplexModel 1)) := by
      rw [ae_iff]
      exact hTV.traceMeasure_compl
    filter_upwards [hVae] with z hz
    have h := hiff z hz
    by_cases hz1 : z ∈ Ginf
    · rw [Set.indicator_of_mem hz1, Set.indicator_of_mem (h.mp hz1)]
    · rw [Set.indicator_of_notMem hz1, Set.indicator_of_notMem (fun h' => hz1 (h.mpr h'))]
  rw [← hind]
  exact hposlim

/-- **Source `ex:1Dnpp`, the reverse inequality, in one variable**: for `u` psh and locally
integrable on an open set `U ⊆ ℂ¹`, `1_{u > -∞} dd^c u ≤ (dd^c u)^1`. -/
theorem isPositive_nonPluripolarProduct_sub_indicator_ddcL1_of_dim_one
    {U : Opens (ComplexModel 1)} {u : ComplexModel 1 → EReal} (hu : IsL1PshOn U u)
    (hqp : 0 + 1 = 1) :
    IsPositive (NonPluripolarCurrent.nonPluripolarProduct hqp U (fun _ : Fin 1 => u) -
      mulBorel (ddcL1 (m := 0) U u) ({z | z ∈ U ∧ u z ≠ ⊥}.indicator fun _ => (1 : ℝ))) := by
  refine LocalPositiveCurrentGluing.isPositive_of_local_restrict fun x hx => ?_
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (U.isOpen.mem_nhds hx)
  set V : Opens (ComplexModel 1) := ⟨Metric.ball x r, Metric.isOpen_ball⟩ with hVdef
  have hVU : V ≤ U := fun z hz => hrU (Metric.ball_subset_closedBall hz)
  have hTU : IsPositive (ddcL1 (m := 0) U u) := hu.isPositive_ddcL1
  have hUm : MeasurableSet {z | z ∈ U ∧ u z ≠ ⊥} := by
    rw [← iUnion_strictLocus_one (m := 0) (U := U) (u := u)]
    exact MeasurableSet.iUnion (BedfordTaylorTopDegree.measurableSet_strictLocus
      (fun _ : Fin 1 => hu.psh))
  refine ⟨V, hVU, Metric.mem_ball_self hr, ?_⟩
  rw [restrict_sub', restrict_nonPluripolarProduct hqp (fun _ => hu.psh)
      (isWellDefinedOn_one hu hqp) hVU,
    ← mulBorel_restrict hTU hVU (measurable_const.indicator hUm)
      (isLocallyBoundedOn_indicator_one _),
    restrict_ddcL1 hVU hu.locallyIntegrableOn]
  exact isPositive_nonPluripolarProduct_sub_on_ball hu hqp hr hrU

/-- A current of bidimension `(0,0)` which is positive together with its negative vanishes. -/
theorem eq_zero_of_isPositive_of_isPositive_neg {n : ℕ} {W : Opens (ComplexModel n)}
    {D : LocalProductCurrent n W 0} (hD : IsPositive D) (hD' : IsPositive (-D)) : D = 0 := by
  have hpos : ∀ {T : LocalProductCurrent n W 0}, IsPositive T →
      PositiveDistribution (T (kahlerPower n 0)) := by
    intro T hT ψ hψ
    have := hT Unit (fun _ => kahlerPower n 0) (fun _ => ψ) (fun z => by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact StronglyPositiveForms.smul_mem_spCone
        (StronglyPositiveForms.formPower_mem_spCone isSemipositiveOneOne_kahlerForm 0) (hψ z))
    simpa using this
  refine eq_of_apply_kahlerPower fun φ => ?_
  have h := SGPT.Currents.eq_zero_of_positiveDistribution_of_neg (hpos hD) (by
    simpa using hpos hD')
  rw [h]
  rfl

/-- **Source `ex:1Dnpp` in one variable**: for `u` psh and locally integrable on an open set
`U ⊆ ℂ¹`, the degree-one non-pluripolar product is `(dd^c u)^1 = 1_{u > -∞} dd^c u`. -/
theorem nonPluripolarProduct_eq_indicator_ddcL1_of_dim_one
    {U : Opens (ComplexModel 1)} {u : ComplexModel 1 → EReal} (hu : IsL1PshOn U u)
    (hqp : 0 + 1 = 1) :
    NonPluripolarCurrent.nonPluripolarProduct hqp U (fun _ : Fin 1 => u) =
      mulBorel (ddcL1 (m := 0) U u) ({z | z ∈ U ∧ u z ≠ ⊥}.indicator fun _ => (1 : ℝ)) := by
  have h1 := isPositive_nonPluripolarProduct_sub_indicator_ddcL1_of_dim_one hu hqp
  have h2 := (isPositive_indicator_ddcL1_sub_nonPluripolarProduct_one (m := 0) hu hqp).2.2
  have h3 := eq_zero_of_isPositive_of_isPositive_neg h1 (by rwa [neg_sub])
  exact sub_eq_zero.mp h3

end SGPT.NPP.Riesz

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (0 + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (0 + 1))) ∞ M]

/-- **Source `ex:1Dnpp`, the reverse inequality, on a Riemann surface**: in every chart,
`1_{φ > -∞} dd^c φ ≤ (dd^c φ)^1`. -/
theorem isPositive_nonPluripolarProduct_sub_indicator_ddcCurrent_of_dim_one {φ : M → EReal}
    (hφ : SGPT.PSH.ManifoldPSH (n := 0 + 1) φ) (hqp : 0 + 1 = 0 + 1)
    (e : ComplexChart (0 + 1) M) :
    IsPositive ((nonPluripolarProduct hqp (fun _ : Fin 1 => φ) (fun _ => hφ)
        (isNonPluripolarWellDefined_one hφ hqp)).inChart e -
      mulBorel ((ddcCurrent 0 φ hφ).inChart e)
        ({z | z ∈ chartTarget e ∧ φ (e.val.symm z) ≠ ⊥}.indicator fun _ => (1 : ℝ))) :=
  SGPT.NPP.Riesz.isPositive_nonPluripolarProduct_sub_indicator_ddcL1_of_dim_one
    (isL1PshOn_chart hφ e) hqp

/-- **Source `ex:1Dnpp` on a Riemann surface**: in every chart,
`(dd^c φ)^1 = 1_{φ > -∞} dd^c φ`. -/
theorem nonPluripolarProduct_inChart_eq_indicator_ddcCurrent_of_dim_one {φ : M → EReal}
    (hφ : SGPT.PSH.ManifoldPSH (n := 0 + 1) φ) (hqp : 0 + 1 = 0 + 1)
    (e : ComplexChart (0 + 1) M) :
    (nonPluripolarProduct hqp (fun _ : Fin 1 => φ) (fun _ => hφ)
        (isNonPluripolarWellDefined_one hφ hqp)).inChart e =
      mulBorel ((ddcCurrent 0 φ hφ).inChart e)
        ({z | z ∈ chartTarget e ∧ φ (e.val.symm z) ≠ ⊥}.indicator fun _ => (1 : ℝ)) :=
  SGPT.NPP.Riesz.nonPluripolarProduct_eq_indicator_ddcL1_of_dim_one (isL1PshOn_chart hφ e) hqp

end SGPT.NPP
