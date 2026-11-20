import SGPT.Envelopes.RelativeCYDinew
import SGPT.Envelopes.RelativeCYExistence
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Uniqueness for the relative Calabi–Yau equation, from Dinew's inequality

Source `thm:Yau_rel` (`author/chapter_envelopes.tex`, lines 1021–1027), uniqueness part,
following Xia, *Foundations of pluripotential theory*, `thm:relative-prescribed-measure-uniqueness`
(concentration of mass, after Kołodziej and Dinew).

Let `u, v ∈ E(X, θ; φ)` with `θ_u^n = θ_v^n = μ`. If `u - v` is not `μ`-almost everywhere
constant, there is `c` with `μ{u - v < c} > 0`, `μ{u - v > c} > 0` and `μ{u - v = c} = 0`
(`exists_level_split`; the level sets of positive measure are countable). Replace `v` by
`v + c` and put `U = {u < v}`, so `0 < μ(U) < μ(X)`. With `q = (μ(X)/μ(U))^{1/n} > 1`, the
existence theorem gives `h ∈ E(X, θ; φ)` with `θ_h^n = q^n 1_U μ`. Dinew's lower bound
(`CommonMeasureConvexLowerBound`, the only conditional input) gives, for `0 < t < 1` and
`w_t = t h + (1 - t) v`,
`θ_{w_t}^n ≥ ((1 - t) + t q 1_U)^n μ`, and the comparison principle on `U_t = {u < w_t}`
gives `(1 + t(q-1))^n μ(U_t ∩ U) + (1 - t)^n μ(U_t \ U) ≤ μ(U_t)`. Bernoulli's inequality
turns this into `(q - 1) μ(U_t ∩ U) ≤ μ(U_t \ U)`; letting `t → 0`, `μ(U_t ∩ U) → μ(U)` and
`μ(U_t \ U) → 0`, a contradiction. Finally the domination principle turns `u = v + C`
`μ`-almost everywhere into `u = v + C` everywhere.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeCY

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Envelopes.RelativeMA

/-- If a real function `D` is not almost everywhere constant for a finite measure `μ ≠ 0`, there
is a level `c` with `μ{D < c} > 0`, `μ{D > c} > 0` and `μ{D = c} = 0`. -/
theorem exists_level_split {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {D : X → ℝ} (hD : Measurable D) (hnc : ∀ c : ℝ, ¬ ∀ᵐ x ∂μ, D x = c) :
    ∃ c : ℝ, 0 < μ {x | D x < c} ∧ 0 < μ {x | c < D x} ∧ μ {x | D x = c} = 0 := by
  have hk : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hunion_lt : ∀ c : ℝ, {x | D x < c} = ⋃ k : ℕ, {x | D x < c - 1 / ((k : ℝ) + 1)} := by
    intro c
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk'⟩
      linarith [hk k]
  have hunion_gt : ∀ c : ℝ, {x | c < D x} = ⋃ k : ℕ, {x | c + 1 / ((k : ℝ) + 1) < D x} := by
    intro c
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk'⟩
      linarith [hk k]
  have hA : ∃ c₁ : ℝ, 0 < μ {x | D x < c₁} ∧ 0 < μ {x | c₁ < D x} := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ c : ℝ, μ {x | D x < c} ≠ 0 → μ {x | c < D x} = 0 := fun c hc =>
      le_antisymm (hcon c (pos_iff_ne_zero.mpr hc)) zero_le
    set S0 : Set ℝ := {c | μ {x | D x < c} = 0} with hS0
    have hunivlt : (univ : Set X) = ⋃ k : ℕ, {x | D x < k} := by
      ext x
      simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]
      exact exists_nat_gt (D x)
    have hunivgt : (univ : Set X) = ⋃ k : ℕ, {x | -(k : ℝ) < D x} := by
      ext x
      simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]
      obtain ⟨k, hk'⟩ := exists_nat_gt (-D x)
      exact ⟨k, by linarith⟩
    have hne : S0.Nonempty := by
      by_contra h
      have h' : ∀ c : ℝ, μ {x | D x < c} ≠ 0 := fun c hc => h ⟨c, hc⟩
      apply hμ
      rw [hunivgt]
      exact measure_iUnion_null fun k => hz _ (h' _)
    have hbdd : BddAbove S0 := by
      by_contra h
      rw [not_bddAbove_iff] at h
      apply hμ
      rw [hunivlt]
      refine measure_iUnion_null fun k => ?_
      obtain ⟨c, hc, hkc⟩ := h k
      exact measure_mono_null (fun x hx => lt_trans hx hkc) hc
    set cs := sSup S0 with hcs
    have hlow : μ {x | D x < cs} = 0 := by
      rw [hunion_lt cs]
      refine measure_iUnion_null fun k => ?_
      obtain ⟨c, hc, hkc⟩ := exists_lt_of_lt_csSup hne (show cs - 1 / ((k : ℝ) + 1) < cs by
        linarith [hk k])
      exact measure_mono_null (fun x hx => lt_trans hx hkc) hc
    have hhigh : μ {x | cs < D x} = 0 := by
      rw [hunion_gt cs]
      refine measure_iUnion_null fun k => hz _ fun h0 => ?_
      have := le_csSup hbdd (show cs + 1 / ((k : ℝ) + 1) ∈ S0 from h0)
      linarith [hk k]
    apply hnc cs
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hlow hhigh)
    exact lt_or_gt_of_ne hx
  obtain ⟨c₁, h₁, h₂⟩ := hA
  obtain ⟨k, hk₂⟩ : ∃ k : ℕ, 0 < μ {x | c₁ + 1 / ((k : ℝ) + 1) < D x} := by
    by_contra h
    push Not at h
    rw [hunion_gt c₁] at h₂
    exact h₂.ne' (measure_iUnion_null fun k => le_antisymm (h k) zero_le)
  set c₂ := c₁ + 1 / ((k : ℝ) + 1) with hc₂
  have hc12 : c₁ < c₂ := by linarith [hk k]
  have hcount := Measure.countable_meas_level_set_pos (μ := μ) hD
  obtain ⟨c, hc, hcz⟩ : ∃ c ∈ Ioo c₁ c₂, μ {x | D x = c} = 0 := by
    by_contra h
    push Not at h
    have hsub : Ioo c₁ c₂ ⊆ {t | 0 < μ {a | D a = t}} := fun c hc => pos_iff_ne_zero.mpr (h c hc)
    have := hcount.mono hsub
    rw [Cardinal.Real.Ioo_countable_iff] at this
    linarith
  exact ⟨c, h₁.trans_le (measure_mono fun x hx => lt_trans hx hc.1),
    hk₂.trans_le (measure_mono fun x hx => lt_trans hc.2 hx), hcz⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal}

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
/-- The value of `t h + (1 - t) v` at a point where `h, v` are finite. -/
theorem convexComb_apply_coe {h v : M → EReal} {x : M} {e b : ℝ} (he : h x = e) (hb : v x = b)
    (t : ℝ) : ThetaPshConvexCombination.convexComb t h v x = ((t * e + (1 - t) * b : ℝ) : EReal) := by
  rw [ThetaPshConvexCombination.convexComb_apply, he, hb, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_add]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
/-- Bernoulli's inequalities turn the concentration inequality into
`(q - 1) p ≤ r`. -/
theorem concentration_real {t q p r : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hq : 1 ≤ q) (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hn : 0 < n)
    (h : (t * q + (1 - t)) ^ n * p + (1 - t) ^ n * r ≤ p + r) : (q - 1) * p ≤ r := by
  have hB1 : 1 + (n : ℝ) * (t * (q - 1)) ≤ (t * q + (1 - t)) ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ t * (q - 1) by nlinarith) n
    calc 1 + (n : ℝ) * (t * (q - 1)) ≤ (1 + t * (q - 1)) ^ n := this
      _ = (t * q + (1 - t)) ^ n := by ring_nf
  have hB2 : 1 + (n : ℝ) * (-t) ≤ (1 - t) ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith) n
    calc 1 + (n : ℝ) * (-t) ≤ (1 + -t) ^ n := this
      _ = (1 - t) ^ n := by ring_nf
  have h1 : (1 + (n : ℝ) * (t * (q - 1))) * p + (1 + (n : ℝ) * (-t)) * r ≤ p + r :=
    le_trans (add_le_add (mul_le_mul_of_nonneg_right hB1 hp) (mul_le_mul_of_nonneg_right hB2 hr)) h
  have hnt : 0 < (n : ℝ) * t := mul_pos (Nat.cast_pos.mpr hn) ht0
  have h2 : ((n : ℝ) * t) * ((q - 1) * p) ≤ ((n : ℝ) * t) * r := by nlinarith
  exact le_of_mul_le_mul_left h2 hnt

variable [ConnectedSpace M]

/-- **Uniqueness up to a constant, almost everywhere** (conditional on
`CommonMeasureConvexLowerBound`). If `u, v ∈ E(X, θ; φ)` have the same measure `μ`, then
`u = v + C` `μ`-almost everywhere for a real constant `C`. -/
theorem exists_const_ae_eq_of_measure_eq (hD : CommonMeasureConvexLowerBound n M)
    (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hφ : IsModelPotential θ φ)
    {u v : M → EReal} (hu : RelativeFullMassPreceq θ φ u hφ) (hv : RelativeFullMassPreceq θ φ v hφ)
    (heq : diagonalPotentialMeasure θ u hu.1 = diagonalPotentialMeasure θ v hv.1) :
    ∃ C : ℝ, ∀ᵐ x ∂diagonalPotentialMeasure θ u hu.1, u x = v x + (C : EReal) := by
  have huP := hu.1
  have hvP := hv.1
  have hφP := hφ.plurisubharmonic
  set μ := diagonalPotentialMeasure θ u huP with hμdef
  have : IsFiniteMeasure μ :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ huP
  have hμpp : DoesNotChargeManifoldPluripolar (n := n) μ :=
    DominationPrincipleReduction.diagonalPotentialMeasure_doesNotChargeManifoldPluripolar θ huP
  have hμm : μ univ = diagonalPotentialMass θ φ hφP := hu.mass_eq huP
  have hμ0 : μ univ ≠ 0 := (hμm ▸ hφ.positive_mass).ne'
  have hum := measurable_of_isThetaPshPotential huP
  have hvm := measurable_of_isThetaPshPotential hvP
  have hut : ∀ x, u x ≠ ⊤ := huP.1.quasiPlurisubharmonic.ne_top
  have hvt : ∀ x, v x ≠ ⊤ := hvP.1.quasiPlurisubharmonic.ne_top
  set D : M → ℝ := fun x => (u x).toReal - (v x).toReal with hDdef
  have hDm : Measurable D := (measurable_ereal_toReal.comp hum).sub (measurable_ereal_toReal.comp hvm)
  have hgood : ∀ᵐ x ∂μ, u x ≠ ⊥ ∧ v x ≠ ⊥ :=
    (ae_ne_bot_of_doesNotCharge hμpp huP).and (ae_ne_bot_of_doesNotCharge hμpp hvP)
  have hreal : ∀ x, u x ≠ ⊥ → v x ≠ ⊥ → ∀ c : ℝ, (u x < v x + (c : EReal) ↔ D x < c) ∧
      (u x = v x + (c : EReal) ↔ D x = c) ∧ (v x + (c : EReal) < u x ↔ c < D x) := by
    intro x hux hvx c
    obtain ⟨a, ha⟩ : ∃ a : ℝ, u x = a := ⟨_, (EReal.coe_toReal (hut x) hux).symm⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, v x = b := ⟨_, (EReal.coe_toReal (hvt x) hvx).symm⟩
    simp only [hDdef, ha, hb, EReal.toReal_coe, ← EReal.coe_add, EReal.coe_lt_coe_iff,
      EReal.coe_eq_coe_iff]
    refine ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
      fun h => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  by_contra hcon
  have hcon' : ∀ C : ℝ, ¬ ∀ᵐ x ∂μ, u x = v x + (C : EReal) := fun C h => hcon ⟨C, h⟩
  have hnc : ∀ c : ℝ, ¬ ∀ᵐ x ∂μ, D x = c := by
    intro c hc
    apply hcon' c
    filter_upwards [hc, hgood] with x hx hg
    exact ((hreal x hg.1 hg.2 c).2.1).mpr hx
  obtain ⟨c, hlt, hgt, hzero⟩ := exists_level_split hμ0 hDm hnc
  -- the shifted potential `v' = v + c`
  set v' : M → EReal := fun x => v x + (c : EReal) with hv'def
  have hv'F : RelativeFullMassPreceq θ φ v' hφ := hv.add_const c
  have hv'P : IsThetaPshPotential θ.val v' := hvP.add_const c
  have hv'm := measurable_of_isThetaPshPotential hv'P
  have hμv' : diagonalPotentialMeasure θ v' hv'P = μ :=
    (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hvP c hv'P).trans heq.symm
  set U : Set M := {x | u x < v' x} with hUdef
  have hUm : MeasurableSet U := measurableSet_lt hum hv'm
  have hμU : μ U = μ {x | D x < c} := by
    refine measure_congr (eventuallyEq_set.mpr ?_)
    filter_upwards [hgood] with x hg
    exact (hreal x hg.1 hg.2 c).1
  have hμV : μ {x | v' x < u x} = μ {x | c < D x} := by
    refine measure_congr (eventuallyEq_set.mpr ?_)
    filter_upwards [hgood] with x hg
    exact (hreal x hg.1 hg.2 c).2.2
  have hμZ : μ {x | u x = v' x} = 0 := by
    rw [← hzero]
    refine measure_congr (eventuallyEq_set.mpr ?_)
    filter_upwards [hgood] with x hg
    exact (hreal x hg.1 hg.2 c).2.1
  have hU0 : 0 < μ U := hμU ▸ hlt
  have hUlt : μ U < μ univ := by
    have hdisj : Disjoint U {x | v' x < u x} :=
      Set.disjoint_left.mpr fun x (hx : u x < v' x) (hx' : v' x < u x) => lt_asymm hx hx'
    calc μ U < μ U + μ {x | v' x < u x} :=
          ENNReal.lt_add_right (measure_ne_top _ _) (hμV ▸ hgt).ne'
      _ = μ (U ∪ {x | v' x < u x}) := (measure_union hdisj (measurableSet_lt hv'm hum)).symm
      _ ≤ μ univ := measure_mono (subset_univ _)
  -- the auxiliary measure `q^n 1_U μ`
  set mU : ℝ := (μ U).toReal with hmU
  set mX : ℝ := (μ univ).toReal with hmX
  have hmU0 : 0 < mU := ENNReal.toReal_pos hU0.ne' (measure_ne_top _ _)
  have hmUX : mU < mX := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hUlt
  set κ : ℝ := mX / mU with hκdef
  have hκ : 1 < κ := (one_lt_div hmU0).mpr hmUX
  set q : ℝ := κ ^ ((n : ℝ)⁻¹) with hqdef
  have hq1 : 1 < q := Real.one_lt_rpow hκ (inv_pos.mpr (Nat.cast_pos.mpr hn))
  have hqn : q ^ n = κ := Real.rpow_inv_natCast_pow (by linarith) hn.ne'
  set Q : ℝ≥0∞ := ENNReal.ofReal q with hQdef
  set g : M → ℝ≥0∞ := U.indicator (fun _ => Q ^ n) with hgdef
  have hgm : Measurable g := measurable_const.indicator hUm
  set ν' : Measure M := μ.withDensity g with hν'def
  have hν'univ : ν' univ = μ univ := by
    rw [hν'def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_indicator_const hUm, hQdef, ← ENNReal.ofReal_pow (by linarith), hqn,
      ← ENNReal.ofReal_toReal (measure_ne_top μ U), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_toReal (measure_ne_top μ univ), ← hmU, ← hmX, hκdef,
      div_mul_cancel₀ _ hmU0.ne']
  have : IsFiniteMeasure ν' := ⟨by rw [hν'univ]; exact measure_lt_top _ _⟩
  have hν'pp : DoesNotChargeManifoldPluripolar (n := n) ν' := fun S hS =>
    withDensity_absolutelyContinuous μ g (hμpp S hS)
  obtain ⟨h, hh, hμh, -, -⟩ :=
    exists_relativeFullMass_measure_solution omega hn hbig hφ hν'pp (hν'univ.trans hμm)
  have hhP := hh.1
  have hht : ∀ x, h x ≠ ⊤ := hhP.1.quasiPlurisubharmonic.ne_top
  -- the concentration inequality for `w_t = t h + (1 - t) v'`
  have hkey : ∀ t : ℝ, 0 < t → t < 1 →
      (q - 1) * (μ ({x | u x < ThetaPshConvexCombination.convexComb t h v' x} ∩ U)).toReal ≤
        (μ ({x | u x < ThetaPshConvexCombination.convexComb t h v' x} \ U)).toReal := by
    intro t ht0 ht1
    set w := ThetaPshConvexCombination.convexComb t h v' with hwdef
    have hwP : IsThetaPshPotential θ.val w :=
      ThetaPshConvexCombination.isThetaPshPotential_convexComb hhP hv'P ht0 ht1
    have hhigh : w ≤ fun x => max (h x) (v' x) := by
      have h0 := ThetaPshConvexCombination.convexComb_mono ht0.le ht1.le
        (show h ≤ fun x => max (h x) (v' x) from fun _ => le_max_left _ _)
        (show v' ≤ fun x => max (h x) (v' x) from fun _ => le_max_right _ _)
      rwa [ThetaCapacity.convexComb_self ht0 ht1] at h0
    have hwpre : RelativePSHPreceq θ φ w := ⟨hwP, (MoreSingularOn.of_le fun x _ => hhigh x).trans
      (DominationPrincipleReduction.moreSingularOn_max hh.relativePSHPreceq.2
        hv'F.relativePSHPreceq.2)⟩
    set Ut : Set M := {x | u x < w x} with hUtdef
    have hUtm : MeasurableSet Ut := measurableSet_lt hum (measurable_of_isThetaPshPotential hwP)
    have hcomp : diagonalPotentialMeasure θ w hwP Ut ≤ μ Ut :=
      diagonalPotentialMeasure_strict_comparison' omega hu hwpre
    have hdin := hD hn θ h v' hhP hv'P μ g (fun _ => 1) hgm measurable_const (by rw [hμh])
      (by
        rw [hμv']
        exact (withDensity_one (μ := μ)).le) t ht0.le ht1.le hwP
    set b : ℝ≥0∞ := (ENNReal.ofReal t * Q + ENNReal.ofReal (1 - t)) ^ n with hbdef
    set d : ℝ≥0∞ := (ENNReal.ofReal (1 - t)) ^ n with hddef
    set dens : M → ℝ≥0∞ := fun x => (ENNReal.ofReal t * g x ^ ((n : ℝ)⁻¹) +
      ENNReal.ofReal (1 - t) * (fun _ => (1 : ℝ≥0∞)) x ^ ((n : ℝ)⁻¹)) ^ n with hdensdef
    have hdU : ∀ x ∈ U, dens x = b := by
      intro x hx
      simp only [hdensdef, hbdef, hgdef, indicator_of_mem hx, ENNReal.pow_rpow_inv_natCast hn.ne',
        ENNReal.one_rpow, mul_one]
    have hdnU : ∀ x ∉ U, dens x = d := by
      intro x hx
      simp only [hdensdef, hddef, hgdef, indicator_of_notMem hx,
        ENNReal.zero_rpow_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn)), mul_zero, zero_add,
        ENNReal.one_rpow, mul_one]
    have hlow : b * μ (Ut ∩ U) + d * μ (Ut \ U) ≤ μ Ut := by
      calc b * μ (Ut ∩ U) + d * μ (Ut \ U) =
            μ.withDensity dens (Ut ∩ U) + μ.withDensity dens (Ut \ U) := by
            rw [withDensity_apply _ (hUtm.inter hUm), withDensity_apply _ (hUtm.diff hUm),
              setLIntegral_congr_fun (hUtm.inter hUm) (fun x hx => hdU x hx.2),
              setLIntegral_congr_fun (hUtm.diff hUm) (fun x hx => hdnU x hx.2),
              setLIntegral_const, setLIntegral_const]
        _ = μ.withDensity dens Ut := measure_inter_add_sdiff Ut hUm
        _ ≤ diagonalPotentialMeasure θ w hwP Ut := hdin Ut
        _ ≤ μ Ut := hcomp
    have hsplit : μ Ut = μ (Ut ∩ U) + μ (Ut \ U) := (measure_inter_add_sdiff Ut hUm).symm
    have hbfin : b ≠ ⊤ := by rw [hbdef]; finiteness
    have hdfin : d ≠ ⊤ := by rw [hddef]; finiteness
    have hbr : b.toReal = (t * q + (1 - t)) ^ n := by
      rw [hbdef, ENNReal.toReal_pow, ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal ht0.le, hQdef,
        ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    have hdr : d.toReal = (1 - t) ^ n := by
      rw [hddef, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]
    have hR := ENNReal.toReal_mono (measure_ne_top μ Ut) hlow
    rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (ENNReal.mul_ne_top hbfin (measure_ne_top _ _))
        (ENNReal.mul_ne_top hdfin (measure_ne_top _ _)), ENNReal.toReal_mul, ENNReal.toReal_mul,
      hbr, hdr] at hR
    exact concentration_real ht0 ht1 hq1.le ENNReal.toReal_nonneg ENNReal.toReal_nonneg hn hR
  -- letting `t → 0`
  set tk : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with htkdef
  have htk0 : ∀ k, 0 < tk k := fun k => by positivity
  have htk1 : ∀ k, tk k < 1 := fun k => by
    rw [htkdef, div_lt_one (by positivity)]
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have htk : Tendsto tk atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine h0.congr fun k => ?_
    simp only [htkdef, Nat.cast_add, Nat.cast_one]
    ring_nf
  set Ut : ℕ → Set M := fun k => {x | u x < ThetaPshConvexCombination.convexComb (tk k) h v' x}
    with hUtdef
  have hUtm : ∀ k, MeasurableSet (Ut k) := fun k => measurableSet_lt hum
    (measurable_of_isThetaPshPotential
      (ThetaPshConvexCombination.isThetaPshPotential_convexComb hhP hv'P (htk0 k) (htk1 k)))
  have hgood2 : ∀ᵐ x ∂μ, u x ≠ ⊥ ∧ v x ≠ ⊥ ∧ h x ≠ ⊥ ∧ u x ≠ v' x := by
    have hZ' : ∀ᵐ x ∂μ, u x ≠ v' x := by
      rw [ae_iff]
      simpa only [ne_eq, not_not] using hμZ
    filter_upwards [hgood, ae_ne_bot_of_doesNotCharge hμpp hhP, hZ'] with x hg hhx hz
    exact ⟨hg.1, hg.2, hhx, hz⟩
  have hpoint : ∀ᵐ x ∂μ, ∀ᶠ k in atTop, (x ∈ Ut k ↔ x ∈ U) := by
    filter_upwards [hgood2] with x hx
    obtain ⟨hux, hvx, hhx, hne⟩ := hx
    obtain ⟨a, ha⟩ : ∃ a : ℝ, u x = a := ⟨_, (EReal.coe_toReal (hut x) hux).symm⟩
    obtain ⟨bv, hbv⟩ : ∃ b : ℝ, v x = b := ⟨_, (EReal.coe_toReal (hvt x) hvx).symm⟩
    obtain ⟨e, he⟩ : ∃ e : ℝ, h x = e := ⟨_, (EReal.coe_toReal (hht x) hhx).symm⟩
    have hv'x : v' x = ((bv + c : ℝ) : EReal) := by rw [hv'def]; simp only [hbv, ← EReal.coe_add]
    have hval : ∀ k, ThetaPshConvexCombination.convexComb (tk k) h v' x =
        ((tk k * e + (1 - tk k) * (bv + c) : ℝ) : EReal) := fun k =>
      convexComb_apply_coe he hv'x (tk k)
    have hlim : Tendsto (fun k => tk k * e + (1 - tk k) * (bv + c)) atTop (𝓝 (bv + c)) := by
      have := ((htk.mul_const e).add
        (((tendsto_const_nhds (x := (1 : ℝ))).sub htk).mul_const (bv + c)))
      simpa only [zero_mul, zero_add, sub_zero, one_mul] using this
    have hmemU : x ∈ U ↔ a < bv + c := by
      change u x < v' x ↔ _
      rw [ha, hv'x, EReal.coe_lt_coe_iff]
    have hmemUt : ∀ k, x ∈ Ut k ↔ a < tk k * e + (1 - tk k) * (bv + c) := fun k => by
      change u x < ThetaPshConvexCombination.convexComb (tk k) h v' x ↔ _
      rw [ha, hval k, EReal.coe_lt_coe_iff]
    have hab : a ≠ bv + c := by
      intro h'
      apply hne
      rw [ha, hv'x, h']
    rcases lt_or_gt_of_ne hab with hab | hab
    · filter_upwards [hlim.eventually (lt_mem_nhds hab)] with k hk
      rw [hmemUt k, hmemU]
      exact iff_of_true hk hab
    · filter_upwards [hlim.eventually (gt_mem_nhds hab)] with k hk
      rw [hmemUt k, hmemU]
      exact iff_of_false (not_lt.mpr hk.le) (not_lt.mpr hab.le)
  have hP : Tendsto (fun k => μ (Ut k ∩ U)) atTop (𝓝 (μ U)) := by
    refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hUm
      (fun k => (hUtm k).inter hUm) ?_
    filter_upwards [hpoint] with x hx
    filter_upwards [hx] with k hk
    exact ⟨fun h' => h'.2, fun h' => ⟨hk.mpr h', h'⟩⟩
  have hR : Tendsto (fun k => μ (Ut k \ U)) atTop (𝓝 (μ ∅)) := by
    refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
      (fun k => (hUtm k).diff hUm) ?_
    filter_upwards [hpoint] with x hx
    filter_upwards [hx] with k hk
    exact ⟨fun h' => absurd (hk.mp h'.1) h'.2, fun h' => h'.elim⟩
  rw [measure_empty] at hR
  have hPr := (ENNReal.tendsto_toReal (measure_ne_top μ U)).comp hP
  have hRr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hR
  have hlim := le_of_tendsto_of_tendsto' (hPr.const_mul (q - 1)) hRr fun k =>
    hkey (tk k) (htk0 k) (htk1 k)
  rw [ENNReal.toReal_zero] at hlim
  have : 0 < (q - 1) * (μ U).toReal := mul_pos (by linarith) hmU0
  linarith

/-- **Uniqueness up to a constant** (Xia, *Foundations of pluripotential theory*,
`thm:relative-prescribed-measure-uniqueness`, conditional on `CommonMeasureConvexLowerBound`):
if `u, v ∈ E(X, θ; φ)` and `θ_u^n = θ_v^n`, then `u = v + C` everywhere for a real `C`. -/
theorem eq_add_const_of_measure_eq (hD : CommonMeasureConvexLowerBound n M)
    (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hφ : IsModelPotential θ φ)
    {u v : M → EReal} (hu : RelativeFullMassPreceq θ φ u hφ) (hv : RelativeFullMassPreceq θ φ v hφ)
    (heq : diagonalPotentialMeasure θ u hu.1 = diagonalPotentialMeasure θ v hv.1) :
    ∃ C : ℝ, u = fun x => v x + (C : EReal) := by
  obtain ⟨C, hC⟩ := exists_const_ae_eq_of_measure_eq hD omega hn hbig hφ hu hv heq
  have : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  have huP := hu.1
  have hφP := hφ.plurisubharmonic
  set v' : M → EReal := fun x => v x + (C : EReal) with hv'def
  have hv'F : RelativeFullMassPreceq θ φ v' hφ := hv.add_const C
  have hv'P : IsThetaPshPotential θ.val v' := hv.1.add_const C
  have hμv' : diagonalPotentialMeasure θ v' hv'P = diagonalPotentialMeasure θ u huP :=
    (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hv.1 C hv'P).trans heq.symm
  have hupos : HasPositivePotentialMass θ u huP := by
    unfold HasPositivePotentialMass
    rw [hu.mass_eq huP]
    exact hφ.positive_mass
  have hv'pos : HasPositivePotentialMass θ v' hv'P := by
    unfold HasPositivePotentialMass
    rw [hv'F.mass_eq hv'P]
    exact hφ.positive_mass
  have hz1 : diagonalPotentialMeasure θ u huP {x | u x < v' x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hC] with x hx
    simp only [hv'def, hx, lt_irrefl, not_false_eq_true]
  have hz2 : diagonalPotentialMeasure θ v' hv'P {x | v' x < u x} = 0 := by
    rw [hμv', measure_eq_zero_iff_ae_notMem]
    filter_upwards [hC] with x hx
    simp only [hv'def, hx, lt_irrefl, not_false_eq_true]
  have h1 : v' ≤ u := DominationPrinciple.le_of_diagonalPotentialMeasure_lt_eq_zero omega θ huP hv'P
    hφP hupos hv'pos hu.relativePSHPreceq.2 hv'F.relativePSHPreceq.2 (hu.mass_eq huP)
    (hv'F.mass_eq hv'P) hz1
  have h2 : u ≤ v' := DominationPrinciple.le_of_diagonalPotentialMeasure_lt_eq_zero omega θ hv'P
    huP hφP hv'pos hupos hv'F.relativePSHPreceq.2 hu.relativePSHPreceq.2 (hv'F.mass_eq hv'P)
    (hu.mass_eq huP) hz2
  exact ⟨C, le_antisymm h2 h1⟩

end SGPT.Envelopes.RelativeCY
