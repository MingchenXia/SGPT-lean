import SGPT.Trace.TwistedL2SingularCompact

/-!
# Sublevel Kähler modifications with complete cutoffs away from a pole set

The sublevel step in the proof of `claude-twisted-l2:weakly-pseudoconvex`
in `claude-twisted-l2.tex` (Demailly, *Analytic methods in algebraic geometry*,
Theorem 5.1), combined with FPT `lem:analytic-complement-cutoffs` for the pole set.
The conclusion supplies a Kähler modification with `HasCompleteCutoffs`; it does not
assert a separate `CompleteSpace` instance.

## Main results

* `half_add_le_kahlerQuad_add_leviForm`: the pointwise estimate behind FPT's metric
  `-log(c₀ - ψ)`.
* `exists_complete_metric_sublevel` (`claude-twisted-l2-c:sublevel-metric`): for a smooth psh
  exhaustion `Ψ` and an admissible singular weight `ψ`, the open set
  `U_t = {Ψ < t} \ {ψ = -∞}` carries `σ_t = ω + ddᶜ r_t ≥ ω/2`,
  `r_t = -log(c_t - ψ) - log(t - Ψ)`, with complete cut-offs (exhaustion
  `s_t = log(c_t - ψ) - log(t - Ψ)`, `|ds_t|²_σ ≤ 8π`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The pointwise estimate of FPT's metric: if `Levi(g)/π ≥ -C ω` at `z` and `c₀ - g(z) ≥ 2C`,
then `ω/2 + |∂g|²/(π (c₀ - g)²) ≤ ω + Levi(-log(c₀ - g))/π`. -/
theorem half_add_le_kahlerQuad_add_leviForm (omega : KahlerBackground n X) (c : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ c.val.target) {g : ComplexModel n → ℝ}
    (hg : ContDiffAt ℝ 2 g z) {C c₀ : ℝ} (hC : 0 < C) (hgz : 2 * C ≤ c₀ - g z)
    (hlev : ∀ v, -(C * kahlerQuad omega c z v) ≤ leviForm g z v / Real.pi)
    (v : ComplexModel n) :
    kahlerQuad omega c z v / 2 + holDerivSq g z v / (Real.pi * (c₀ - g z) ^ 2) ≤
      kahlerQuad omega c z v + leviForm (fun y => -Real.log (c₀ - g y)) z v / Real.pi := by
  have hpos : 0 < c₀ - g z := by linarith
  rw [leviForm_neg_log_sub hg (by linarith) v]
  have hkq := kahlerQuad_nonneg omega c hz v
  have hl := hlev v
  have hpi := Real.pi_pos
  set u := c₀ - g z
  set L := leviForm g z v
  set Q := holDerivSq g z v
  set k := kahlerQuad omega c z v
  have h1 : -(k / 2) ≤ L / Real.pi / u := by
    rw [le_div_iff₀ hpos]
    have : C * k ≤ u * (k / 2) := by nlinarith
    nlinarith
  have h2 : (L / u + Q / u ^ 2) / Real.pi = L / Real.pi / u + Q / (Real.pi * u ^ 2) := by
    field_simp
  rw [h2]
  linarith


omit [IsComplexManifold n X] in
/-- A function smooth (in charts) on an open set is continuous there. -/
theorem continuousOn_of_chartSmoothOn {f : X → ℝ} {U : Set X} (hU : IsOpen U)
    (hf : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) f U) : ContinuousOn f U := by
  intro x hxU
  refine ContinuousAt.continuousWithinAt ?_
  set c := complexChartAt (n := n) x
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' U) := c.val.isOpen_inter_preimage_symm hU
  have hz : c.val x ∈ c.val.target ∩ c.val.symm ⁻¹' U :=
    ⟨c.val.map_source hx, by rw [mem_preimage, c.val.left_inv hx]; exact hxU⟩
  have h1 : ContinuousAt (fun z => f (c.val.symm z)) (c.val x) :=
    (hf c).continuousOn.continuousAt (hO.mem_nhds hz)
  refine (h1.comp (c.val.continuousAt hx)).congr
    (eventually_of_mem (c.val.open_source.mem_nhds hx) fun y hy => ?_)
  simp only [Function.comp, c.val.left_inv hy]

/-- **A Kähler modification with complete cutoffs on `{Ψ < t} \ {ψ = -∞}`** (`claude-twisted-l2-c:sublevel-metric`).
For a smooth psh exhaustion `Ψ` and an admissible singular weight `ψ`, with `ddᶜψ ≥ -C ω` and
`ψ ≤ M` on the compact `{Ψ ≤ t}` and `c₀ = M + 2C + 1`, the potential
`r = -log(c₀ - ψ) - log(t - Ψ)` gives `σ = ω + ddᶜr ≥ ω/2 + |∂ log(c₀-ψ)|²/π + |∂ log(t-Ψ)|²/π`,
and `s = log(c₀ - ψ) - log(t - Ψ)` is an exhaustion of `U_t` with `|ds|²_σ ≤ 8π`. -/
theorem exists_complete_metric_sublevel (omega : KahlerBackground n X) {Ψ : X → ℝ}
    (hΨ : ChartSmooth (n := n) Ψ)
    (hΨpsh : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun y => Ψ (c.val.symm y)) z v)
    (hΨc : ∀ t : ℝ, IsCompact {x | Ψ x ≤ t}) {ψ : X → EReal}
    (hψ : IsAdmissibleSingularWeight (n := n) ψ) (t : ℝ) :
    ∃ r : X → ℝ, IsKahlerModificationOn omega r {x | Ψ x < t ∧ ψ x ≠ ⊥} ∧
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, Ψ (c.val.symm z) < t →
        ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
          kahlerQuad omega c z v / 2 ≤ modifiedKahlerQuad omega r c z v) ∧
      HasCompleteCutoffs omega r {x | Ψ x < t ∧ ψ x ≠ ⊥} := by
  obtain ⟨hqpsh, htop, hcl, -, hsm⟩ := hψ
  set Ut : Set X := {x | Ψ x < t ∧ ψ x ≠ ⊥} with hUt
  set Kt : Set X := {x | Ψ x ≤ t} with hKt
  have hΨcont : Continuous Ψ := continuous_of_chartSmooth' hΨ
  have hUto : IsOpen Ut := (isOpen_lt hΨcont continuous_const).inter hcl.isOpen_compl
  have hUtK : Ut ⊆ Kt := fun x hx => le_of_lt hx.1
  have hUU : Ut ⊆ {x | ψ x ≠ ⊥} := fun x hx => hx.2
  obtain ⟨C, hC, hlev⟩ := exists_neg_le_leviForm_of_isCompact omega hqpsh (hΨc t)
  obtain ⟨Mψ, hMψ⟩ := exists_le_coe_of_isCompact hqpsh (hΨc t)
  obtain ⟨B, hB⟩ := (hΨc t).exists_bound_of_continuousOn hΨcont.continuousOn
  set c₀ : ℝ := Mψ + 2 * C + 1 with hc₀
  have hle : ∀ x ∈ Ut, (ψ x).toReal ≤ Mψ := fun x hx => by
    have h := hMψ x (hUtK hx)
    rw [← EReal.coe_toReal (htop x) hx.2] at h
    exact_mod_cast h
  have hgap : ∀ x ∈ Ut, 2 * C + 1 ≤ c₀ - (ψ x).toReal := fun x hx => by
    have := hle x hx; rw [hc₀]; linarith
  have hu0 : ∀ x ∈ Ut, 0 < c₀ - (ψ x).toReal := fun x hx => by
    have := hgap x hx; linarith
  have hΨt : ∀ x ∈ Ut, 0 < t - Ψ x := fun x hx => sub_pos.mpr hx.1
  have hΨB : ∀ x ∈ Ut, t - Ψ x ≤ t + B := fun x hx => by
    have := hB x (hUtK hx); rw [Real.norm_eq_abs] at this; linarith [neg_abs_le (Ψ x)]
  set r : X → ℝ := fun x => -Real.log (c₀ - (ψ x).toReal) + -Real.log (t - Ψ x) with hr
  set s : X → ℝ := fun x => Real.log (c₀ - (ψ x).toReal) - Real.log (t - Ψ x) with hs
  have hgs : ∀ c : ComplexChart n X, ContDiffOn ℝ ∞ (fun y => (ψ (c.val.symm y)).toReal)
      (c.val.target ∩ c.val.symm ⁻¹' Ut) := fun c =>
    (hsm c).mono fun z hz => ⟨hz.1, hz.2.2⟩
  have hΨs : ∀ c : ComplexChart n X, ContDiffOn ℝ ∞ (fun y => Ψ (c.val.symm y))
      (c.val.target ∩ c.val.symm ⁻¹' Ut) := fun c => (hΨ c).mono inter_subset_left
  have hne1 : ∀ c : ComplexChart n X, ∀ y ∈ c.val.target ∩ c.val.symm ⁻¹' Ut,
      c₀ - (ψ (c.val.symm y)).toReal ≠ 0 := fun c y hy => (hu0 _ hy.2).ne'
  have hne2 : ∀ c : ComplexChart n X, ∀ y ∈ c.val.target ∩ c.val.symm ⁻¹' Ut,
      t - Ψ (c.val.symm y) ≠ 0 := fun c y hy => (hΨt _ hy.2).ne'
  have hr_s : ∀ c : ComplexChart n X, ContDiffOn ℝ ∞ (fun y => r (c.val.symm y))
      (c.val.target ∩ c.val.symm ⁻¹' Ut) := fun c =>
    (((contDiffOn_const.sub (hgs c)).log (hne1 c)).neg).add
      (((contDiffOn_const.sub (hΨs c)).log (hne2 c)).neg)
  have hs_s : ∀ c : ComplexChart n X, ContDiffOn ℝ ∞ (fun y => s (c.val.symm y))
      (c.val.target ∩ c.val.symm ⁻¹' Ut) := fun c =>
    ((contDiffOn_const.sub (hgs c)).log (hne1 c)).sub
      ((contDiffOn_const.sub (hΨs c)).log (hne2 c))
  -- the pointwise estimate
  have hcore : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      c.val.symm z ∈ Ut → ∀ v : ComplexModel n,
        kahlerQuad omega c z v / 2 +
          holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
            (Real.pi * (c₀ - (ψ (c.val.symm z)).toReal) ^ 2) +
          holDerivSq (fun y => Ψ (c.val.symm y)) z v / (Real.pi * (t - Ψ (c.val.symm z)) ^ 2) ≤
        modifiedKahlerQuad omega r c z v := by
    intro c z hz hzU v
    have hzO : z ∈ c.val.target ∩ c.val.symm ⁻¹' Ut := ⟨hz, hzU⟩
    obtain ⟨hgev, hgeq⟩ := eventually_chartFunction_eq_toReal htop hcl hsm c hz hzU.2
    have hg2 : ContDiffAt ℝ 2 (fun y => (ψ (c.val.symm y)).toReal) z :=
      hgev.self_of_nhds.of_le (by norm_cast)
    have hΨ2 : ContDiffAt ℝ 2 (fun y => Ψ (c.val.symm y)) z :=
      ((hΨ c z hz).contDiffAt (c.val.open_target.mem_nhds hz)).of_le (by norm_cast)
    have h1 := half_add_le_kahlerQuad_add_leviForm omega c hz hg2 hC (c₀ := c₀)
      (by linarith [hgap _ hzU]) (hlev c z hz (hUtK hzU) _ hgev hgeq) v
    have hf1 : ContDiffAt ℝ 2 (fun y => -Real.log (c₀ - (ψ (c.val.symm y)).toReal)) z :=
      ((contDiffAt_const.sub hg2).log (hne1 c z hzO)).neg
    have hf2 : ContDiffAt ℝ 2 (fun y => -Real.log (t - Ψ (c.val.symm y))) z :=
      ((contDiffAt_const.sub hΨ2).log (hne2 c z hzO)).neg
    have hsplit : leviForm (fun y => r (c.val.symm y)) z v =
        leviForm (fun y => -Real.log (c₀ - (ψ (c.val.symm y)).toReal)) z v +
          leviForm (fun y => -Real.log (t - Ψ (c.val.symm y))) z v :=
      leviForm_add hf1 hf2 v
    have h2 := leviForm_neg_log_sub hΨ2 (sub_pos.mp (hΨt _ hzU)) v
    have hL := hΨpsh c z hz v
    have hpos := hΨt _ hzU
    have hpi := Real.pi_pos
    have h3 : holDerivSq (fun y => Ψ (c.val.symm y)) z v / (Real.pi * (t - Ψ (c.val.symm z)) ^ 2) ≤
        leviForm (fun y => -Real.log (t - Ψ (c.val.symm y))) z v / Real.pi := by
      rw [h2, add_div]
      have h4 : 0 ≤ leviForm (fun y => Ψ (c.val.symm y)) z v / (t - Ψ (c.val.symm z)) /
          Real.pi := by positivity
      have h5 : holDerivSq (fun y => Ψ (c.val.symm y)) z v / (t - Ψ (c.val.symm z)) ^ 2 /
          Real.pi = holDerivSq (fun y => Ψ (c.val.symm y)) z v /
            (Real.pi * (t - Ψ (c.val.symm z)) ^ 2) := by
        rw [div_div, mul_comm]
      linarith
    unfold modifiedKahlerQuad
    rw [hsplit, add_div]
    linarith
  have hnn : ∀ (c : ComplexChart n X) (z : ComplexModel n), ∀ v : ComplexModel n,
      0 ≤ holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
            (Real.pi * (c₀ - (ψ (c.val.symm z)).toReal) ^ 2) +
          holDerivSq (fun y => Ψ (c.val.symm y)) z v /
            (Real.pi * (t - Ψ (c.val.symm z)) ^ 2) := fun c z v => by
    unfold holDerivSq
    positivity
  refine ⟨r, ⟨hr_s, fun c z hz hzU v hv => ?_⟩, fun c z hz hΨz hψz v => ?_, ?_⟩
  · have h := hcore c z hz hzU v
    have hk := kahlerQuad_pos omega c hz hv
    have := hnn c z v
    linarith
  · have h := hcore c z hz ⟨hΨz, hψz⟩ v
    have := hnn c z v
    linarith
  · have hscont : ContinuousOn s Ut := continuousOn_of_chartSmoothOn hUto hs_s
    refine hasCompleteCutoffs_of_exhaustion omega r hUto s hs_s (fun T => ?_)
      (C := 8 * Real.pi) (by positivity) fun c z hz hzU v => ?_
    · set K' : Set X := {x | Ψ x ≤ t - Real.exp (-T)} ∩
        ψ ⁻¹' Ici ((c₀ - Real.exp (T + Real.log (t + B)) : ℝ) : EReal) with hK'
      have hK'cl : IsClosed K' := (isClosed_le hΨcont continuous_const).inter
        (hqpsh.upperSemicontinuous.isClosed_preimage _)
      have hK'K : K' ⊆ Kt := fun x hx => by
        have h1 : Ψ x ≤ t - Real.exp (-T) := hx.1
        have := Real.exp_pos (-T)
        change Ψ x ≤ t; linarith
      have hK'c : IsCompact K' := (hΨc t).of_isClosed_subset hK'cl hK'K
      have hK'U : K' ⊆ Ut := fun x hx => by
        have h1 : Ψ x ≤ t - Real.exp (-T) := hx.1
        refine ⟨by have := Real.exp_pos (-T); linarith, fun h => ?_⟩
        have h2 := hx.2
        rw [mem_preimage, h, mem_Ici, le_bot_iff] at h2
        exact EReal.coe_ne_bot _ h2
      have hsubK : {x | x ∈ Ut ∧ s x ≤ T} ⊆ K' := by
        rintro x ⟨hx, hxT⟩
        have hu := hu0 x hx
        have hw := hΨt x hx
        have hlogu : 0 ≤ Real.log (c₀ - (ψ x).toReal) :=
          Real.log_nonneg (by linarith [hgap x hx])
        have hlogw : Real.log (t - Ψ x) ≤ Real.log (t + B) := Real.log_le_log hw (hΨB x hx)
        have hsx : Real.log (c₀ - (ψ x).toReal) - Real.log (t - Ψ x) ≤ T := hxT
        refine ⟨?_, ?_⟩
        · have h1 : -T ≤ Real.log (t - Ψ x) := by linarith
          have h2 := (Real.le_log_iff_exp_le hw).mp h1
          change Ψ x ≤ t - Real.exp (-T)
          linarith
        · have h1 : Real.log (c₀ - (ψ x).toReal) ≤ T + Real.log (t + B) := by linarith
          have h2 := (Real.log_le_iff_le_exp hu).mp h1
          rw [mem_preimage, mem_Ici, ← EReal.coe_toReal (htop x) hx.2, EReal.coe_le_coe_iff]
          linarith
      have hset : {x | x ∈ Ut ∧ s x ≤ T} = K' ∩ s ⁻¹' Iic T := by
        ext x
        exact ⟨fun h => ⟨hsubK h, h.2⟩, fun h => ⟨hK'U h.1, h.2⟩⟩
      rw [hset]
      exact hK'c.of_isClosed_subset
        ((hscont.mono hK'U).preimage_isClosed_of_isClosed hK'cl isClosed_Iic) inter_subset_left
    · have h := hcore c z hz hzU v
      have hk := kahlerQuad_nonneg omega c hz v
      have hzO : z ∈ c.val.target ∩ c.val.symm ⁻¹' Ut := ⟨hz, hzU⟩
      obtain ⟨hgev, -⟩ := eventually_chartFunction_eq_toReal htop hcl hsm c hz hzU.2
      have hgd : DifferentiableAt ℝ (fun y => (ψ (c.val.symm y)).toReal) z :=
        hgev.self_of_nhds.differentiableAt (by simp)
      have hΨd : DifferentiableAt ℝ (fun y => Ψ (c.val.symm y)) z :=
        ((hΨ c z hz).contDiffAt (c.val.open_target.mem_nhds hz)).differentiableAt (by simp)
      have hlt1 : (ψ (c.val.symm z)).toReal < c₀ := by linarith [hu0 _ hzU]
      have hlt2 : Ψ (c.val.symm z) < t := hzU.1
      have hd1 : DifferentiableAt ℝ (fun y => Real.log (c₀ - (ψ (c.val.symm y)).toReal)) z :=
        (hgd.const_sub c₀).log (by linarith)
      have hd2 : DifferentiableAt ℝ (fun y => Real.log (t - Ψ (c.val.symm y))) z :=
        (hΨd.const_sub t).log (by linarith)
      have hg1 := sq_fderiv_log_sub_le hgd hlt1 v
      have hg2 := sq_fderiv_log_sub_le hΨd hlt2 v
      have hfd : fderiv ℝ (fun y => s (c.val.symm y)) z v =
          fderiv ℝ (fun y => Real.log (c₀ - (ψ (c.val.symm y)).toReal)) z v -
            fderiv ℝ (fun y => Real.log (t - Ψ (c.val.symm y))) z v := by
        have := fderiv_sub hd1 hd2
        change fderiv ℝ ((fun y => Real.log (c₀ - (ψ (c.val.symm y)).toReal)) -
          fun y => Real.log (t - Ψ (c.val.symm y))) z v = _
        rw [fderiv_sub hd1 hd2]
        rfl
      rw [hfd]
      set p := fderiv ℝ (fun y => Real.log (c₀ - (ψ (c.val.symm y)).toReal)) z v
      set q := fderiv ℝ (fun y => Real.log (t - Ψ (c.val.symm y))) z v
      have hpq : (p - q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (p + q)]
      have hpi := Real.pi_pos
      have e1 : holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
          (c₀ - (ψ (c.val.symm z)).toReal) ^ 2 = Real.pi *
          (holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
            (Real.pi * (c₀ - (ψ (c.val.symm z)).toReal) ^ 2)) := by
        field_simp
      have e2 : holDerivSq (fun y => Ψ (c.val.symm y)) z v / (t - Ψ (c.val.symm z)) ^ 2 =
          Real.pi * (holDerivSq (fun y => Ψ (c.val.symm y)) z v /
            (Real.pi * (t - Ψ (c.val.symm z)) ^ 2)) := by
        field_simp
      rw [e1] at hg1
      rw [e2] at hg2
      nlinarith

end SGPT.Trace.TwistedL2
