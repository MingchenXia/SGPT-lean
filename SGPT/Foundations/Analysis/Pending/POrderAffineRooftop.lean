import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound
import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierModelReduction
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.FirstPass.POrder

set_option autoImplicit false

/-!
# Affine rooftop obstacles under the `P`-order (Xia, Theorem 6.1.1)

Xia, *Singularities in global pluripotential theory* (SGPT), Theorem 6.1.1
(`xia-sgpt:page-0217`, proof on `xia-sgpt:page-0217`--`page-0218`): the `P`-order form of
Lemma 2.4.4.  Let `X` be a connected compact Kähler manifold of dimension `n`, `θ` a closed real
`(1,1)`-form, `φ, ψ ∈ PSH(X, θ)` with `∫ θ_φ^n > 0` and `φ ⪯_P ψ`, i.e. `P_θ[φ] ≤ P_θ[ψ]`.  For
every weight `a` in Xia's interval (6.5),

  `a ∈ (1, (∫θ_ψ^n / (∫θ_ψ^n - ∫θ_φ^n))^{1/n})`,

the envelope `η = P_θ(aφ + (1 - a)ψ)` of the affine obstacle is a genuine `θ`-PSH potential of
positive mass, and `a⁻¹ η + (1 - a⁻¹) ψ ≤ φ` (6.6).  This is Copy-4's `thm:rooftop` (blueprint
`ana:rooftop-positive-mass`), which cites Xia's theorem.

Unlike Lemma 2.4.4 (`Pending.ConvexCombEnvelopeMass`), `φ ≤ ψ` is not assumed, so the
competitors of the obstacle are no longer bounded above by `φ`.  Xia bounds them with Remark
1.5.2 (the supremum over a closed non-pluripolar set controls the supremum over `X`).  Here the
bound comes from the uniform `L¹` estimate of normalized `θ`-PSH functions on a chart ball
(`Pending.ThetaPshUniformL1Bound`, Guedj--Zeriahi Prop. 8.5), in the general form

  `exists_upper_bound_of_convexComb_le`: for a fixed `θ`-PSH potential `ψ`, `0 < s < 1` and a real
  `B`, every `θ`-PSH potential `v` with `s v + (1 - s) ψ ≤ B` satisfies `v ≤ C`, one `C` for all `v`.

The rest is Xia's proof: `φ ≤ P_θ[ψ] + C_φ` (the `P`-order, after a shift), Lemma 2.4.4 applied to
`φ ≤ Ψ := P_θ[ψ] + C_φ` (same mass as `ψ`, Xia's Proposition 3.1.3), and a shift of its envelope is
a competitor of the original obstacle, because `ψ ≤ Ψ + C'`.

The `P`-order conclusions of Xia's theorem (`η ⪯_P φ`, and `η ∼_P φ` when `φ ∼_P ψ`) need Xia's
Proposition 3.1.10 and are not formalized here.

## Main results

* `IsThetaPshPotential.exists_max`, `HarnackBall.exists_lintegral_max_sub_le`,
  `exists_upper_bound_of_convexComb_le` (general, no Kähler form, no mass).
* `IsAdmissibleWeight.exists_gt`, `isAdmissibleWeight_of_lt_mul`.
* `xiaTheorem611` (Xia Theorem 6.1.1 without its `P`-order clauses, with the quantitative mass
  bound (2.38)) and `isThetaPshPotential_rooftopEnvelope_of_pOrderWith`
  (`ana:rooftop-positive-mass` in the source's form).
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.POrderAffineRooftop

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
open ThetaPshConvexCombination ThetaPshUniformL1Bound ConvexCombEnvelopeMass
open ConvexCombObstacleAlgebra RooftopEnvelopeAeObstacle RooftopConvexCombBarrierModelReduction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### A uniform upper bound from a convex-combination bound -/

/-- A `θ`-PSH potential on a nonempty compact manifold attains a finite maximum. -/
theorem _root_.SGPT.Foundations.Analysis.FirstPass.IsThetaPshPotential.exists_max [CompactSpace M]
    [Nonempty M] {θ : SmoothRealForm n M 2} {u : M → EReal} (hu : IsThetaPshPotential θ u) :
    ∃ y : M, ∃ m : ℝ, u y = (m : EReal) ∧ ∀ x, u x ≤ (m : EReal) := by
  obtain ⟨y, -, hmax⟩ :=
    (hu.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
      univ_nonempty isCompact_univ
  have htop : u y ≠ ⊤ := hu.1.quasiPlurisubharmonic.ne_top y
  have hbot : u y ≠ ⊥ := by
    intro h
    obtain ⟨z, -, hz⟩ := hu.2 y univ isOpen_univ (mem_univ y)
    exact hz (le_bot_iff.mp (h ▸ hmax (mem_univ z)))
  refine ⟨y, (u y).toReal, (EReal.coe_toReal htop hbot).symm, fun x => ?_⟩
  rw [EReal.coe_toReal htop hbot]
  exact hmax (mem_univ x)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `-(a - m) = m - a` in `EReal`, poles included. -/
theorem neg_add_neg_coe (a : EReal) (m : ℝ) : -(a + ((-m : ℝ) : EReal)) = (m : EReal) - a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_sub]
    congr 1
    ring

/-- **The `L¹` deficit from the maximum is uniformly bounded on a Harnack ball** (Guedj--Zeriahi,
Prop. 8.5): on a compact connected manifold, one `B < ∞` bounds `∫_{ball} (m - u ∘ e⁻¹)` for every
`θ`-psh `u` attaining its maximum `m`. -/
theorem HarnackBall.exists_lintegral_max_sub_le [CompactSpace M] [ConnectedSpace M]
    {θ : SmoothRealForm n M 2} (hθ : HasSmoothLocalPotentials θ) (H : HarnackBall θ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ u : M → EReal, IsThetaPshPotential θ u → ∀ m : ℝ,
      (∀ x, u x ≤ (m : EReal)) → (∃ y, u y = (m : EReal)) →
        ∫⁻ z in ball H.z H.r, ((m : EReal) - u (H.e.val.symm z)).toENNReal ≤ B := by
  obtain ⟨B, hB, hBu⟩ := H.exists_lintegral_le hθ 0
  refine ⟨B, hB, fun u hu m hle hmax => ?_⟩
  have hw := hu.add_const (-m)
  have hw0 : ∀ x, u x + ((-m : ℝ) : EReal) ≤ 0 := by
    intro x
    have h := add_le_add (hle x) (le_refl ((-m : ℝ) : EReal))
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
  obtain ⟨y, hy⟩ := hmax
  have hwy : ((-0 : ℝ) : EReal) ≤ u y + ((-m : ℝ) : EReal) := by
    rw [hy, ← EReal.coe_add, add_neg_cancel, neg_zero]
  have key := hBu _ hw.1 hw0 ⟨y, hwy⟩
  simpa only [neg_add_neg_coe] using key

/-- **A convex-combination bound bounds the potential** (in place of Xia's Remark 1.5.2).  On a
nonempty compact connected complex manifold, fix a `θ`-PSH potential `ψ`, a weight `0 < s < 1`
and a level `B`.  There is one real `C` such that every `θ`-PSH potential `v` with
`s v + (1 - s) ψ ≤ B` satisfies `v ≤ C`.

Proof: on a Harnack ball of volume `V`, write `v = m_v - d_v` and `ψ = m_ψ - d_ψ` with their maxima
`m_v, m_ψ`; then `s m_v ≤ B - (1 - s) m_ψ + s d_v + (1 - s) d_ψ` pointwise, and the integrals of
`d_v, d_ψ` over the ball are at most one constant `B₁` (`HarnackBall.exists_lintegral_max_sub_le`),
so `s m_v ≤ B - (1 - s) m_ψ + 2 B₁ / V`. -/
theorem exists_upper_bound_of_convexComb_le [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [ConnectedSpace M] [Nonempty M] {θ : SmoothRealForm n M 2} {ψ : M → EReal}
    (hψ : IsThetaPshPotential θ ψ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (B : ℝ) :
    ∃ C : ℝ, ∀ v : M → EReal, IsThetaPshPotential θ v →
      (∀ x, convexComb s v ψ x ≤ (B : EReal)) → ∀ x, v x ≤ (C : EReal) := by
  have hθ : HasSmoothLocalPotentials θ := hψ.1.hasSmoothLocalPotentials
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨H, -, -, -⟩ := exists_harnackBall hθ (complexChartAt (n := n) x₀)
    ((complexChartAt (n := n) x₀).val.map_source (mem_complexChartAt_source x₀)) one_pos
  obtain ⟨B₁, hB₁, hB₁u⟩ := HarnackBall.exists_lintegral_max_sub_le hθ H
  obtain ⟨yψ, mψ, hyψ, hmψ⟩ := hψ.exists_max
  set V : ℝ≥0∞ := volume (ball H.z H.r) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume H.z H.r_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set T : ℝ := ((B₁ + B₁) / V).toReal with hT
  refine ⟨(B - (1 - s) * mψ + T) / s, fun v hv hbar => ?_⟩
  obtain ⟨yv, mv, hyv, hmv⟩ := hv.exists_max
  suffices hkey : s * mv - B + (1 - s) * mψ ≤ T by
    intro x
    refine (hmv x).trans (EReal.coe_le_coe_iff.mpr ?_)
    rw [le_div_iff₀ hs0]
    linarith
  set K : ℝ := s * mv - B + (1 - s) * mψ with hK
  set f : ComplexModel n → ℝ≥0∞ := fun z => ((mv : EReal) - v (H.e.val.symm z)).toENNReal
    with hf
  set g : ComplexModel n → ℝ≥0∞ := fun z => ((mψ : EReal) - ψ (H.e.val.symm z)).toENNReal
    with hg
  have hs1' : (0 : ℝ) < 1 - s := by linarith
  -- the pointwise inequality
  have hpt : ∀ z, ENNReal.ofReal K ≤ ENNReal.ofReal s * f z + ENNReal.ofReal (1 - s) * g z := by
    intro z
    set x := H.e.val.symm z
    have hb := hbar x
    rw [convexComb_apply] at hb
    have hvt : v x ≠ ⊤ := hv.1.quasiPlurisubharmonic.ne_top x
    have hψt : ψ x ≠ ⊤ := hψ.1.quasiPlurisubharmonic.ne_top x
    by_cases hvb : v x = ⊥
    · have : f z = ⊤ := by simp [hf, x, hvb]
      rw [this, ENNReal.mul_top (by simpa using hs0)]
      simp
    by_cases hψb : ψ x = ⊥
    · have : g z = ⊤ := by simp [hg, x, hψb]
      rw [this, ENNReal.mul_top (by simpa using hs1')]
      simp
    obtain ⟨a, ha⟩ : ∃ a : ℝ, v x = (a : EReal) := ⟨(v x).toReal, (EReal.coe_toReal hvt hvb).symm⟩
    obtain ⟨b, hb'⟩ : ∃ b : ℝ, ψ x = (b : EReal) :=
      ⟨(ψ x).toReal, (EReal.coe_toReal hψt hψb).symm⟩
    rw [ha, hb', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at hb
    have hav : a ≤ mv := by simpa [ha] using hmv x
    have hbψ : b ≤ mψ := by simpa [hb'] using hmψ x
    have hfz : f z = ENNReal.ofReal (mv - a) := by
      simp only [hf, x, ha, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    have hgz : g z = ENNReal.ofReal (mψ - b) := by
      simp only [hg, x, hb', ← EReal.coe_sub, EReal.real_coe_toENNReal]
    rw [hfz, hgz, ← ENNReal.ofReal_mul hs0.le, ← ENNReal.ofReal_mul hs1'.le,
      ← ENNReal.ofReal_add (mul_nonneg hs0.le (by linarith)) (mul_nonneg hs1'.le (by linarith))]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  -- measurability of `f`
  have hfm : AEMeasurable f (volume.restrict (ball H.z H.r)) := by
    have hsymm : AEMeasurable H.e.val.symm (volume.restrict (ball H.z H.r)) :=
      (H.e.val.continuousOn_symm.mono H.ball_subset_target).aemeasurable measurableSet_ball
    have hvm : Measurable v := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
    have hsub : Measurable fun a : EReal => ((mv : EReal) - a).toENNReal := by
      refine Antitone.measurable fun a b hab => ?_
      exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hab)
    exact hsub.comp_aemeasurable (hvm.comp_aemeasurable hsymm)
  -- integrate over the ball
  have hint : ENNReal.ofReal K * V ≤ B₁ + B₁ := by
    calc ENNReal.ofReal K * V = ∫⁻ _ in ball H.z H.r, ENNReal.ofReal K := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ z in ball H.z H.r, (ENNReal.ofReal s * f z + ENNReal.ofReal (1 - s) * g z) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal s * (∫⁻ z in ball H.z H.r, f z) +
            ENNReal.ofReal (1 - s) * ∫⁻ z in ball H.z H.r, g z := by
          rw [lintegral_add_left' (hfm.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ 1 * B₁ + 1 * B₁ := by
          gcongr
          · exact ENNReal.ofReal_le_one.mpr hs1.le
          · exact hB₁u v hv mv hmv ⟨yv, hyv⟩
          · exact ENNReal.ofReal_le_one.mpr (by linarith)
          · exact hB₁u ψ hψ mψ hmψ ⟨yψ, hyψ⟩
      _ = B₁ + B₁ := by rw [one_mul]
  have hdiv : ENNReal.ofReal K ≤ (B₁ + B₁) / V := (ENNReal.le_div_iff_mul_le (Or.inl hV0)
    (Or.inl hVt)).mpr hint
  have hne : (B₁ + B₁) / V ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨hB₁.ne, hB₁.ne⟩) hV0
  exact (ENNReal.ofReal_le_iff_le_toReal hne).mp hdiv

/-! ### Admissible weights -/

/-- The admissible interval (6.5) is open to the right: every admissible weight is below a
larger admissible one. -/
theorem IsAdmissibleWeight.exists_gt {mphi mpsi : ℝ≥0∞} {a : ℝ}
    (ha : IsAdmissibleWeight n mphi mpsi a) :
    ∃ a' : ℝ, a < a' ∧ IsAdmissibleWeight n mphi mpsi a' := by
  obtain ⟨ha1, ha2⟩ := ha
  set d : ℝ≥0∞ := mpsi - mphi with hd
  by_cases hd0 : d = 0
  · refine ⟨a + 1, by linarith, by linarith, ?_⟩
    have h0 : mpsi - mphi = 0 := hd.symm.trans hd0
    rw [hd0, mul_zero] at ha2
    rw [h0, mul_zero]
    exact ha2
  have hpow : (1 : ℝ) ≤ a ^ n := one_le_pow₀ ha1.le
  have hdt : d ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by simp; linarith)] at ha2
    exact (not_top_lt ha2).elim
  have hcont : Continuous fun b : ℝ => ENNReal.ofReal (b ^ n) * d :=
    (ENNReal.continuous_mul_const hdt).comp (ENNReal.continuous_ofReal.comp (continuous_pow n))
  have hev : ∀ᶠ b in 𝓝 a, 1 < b ∧ ENNReal.ofReal (b ^ n) * d < mpsi :=
    (lt_mem_nhds ha1).and ((hcont.tendsto a).eventually (gt_mem_nhds ha2))
  obtain ⟨b, hb, hab⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi a))).exists
  exact ⟨b, hab, hb⟩

/-- The hypothesis of Copy-4's `thm:rooftop`, `tⁿ ∫θ_φⁿ > (tⁿ - 1) ∫θ_ψⁿ` with `t > 1`, is Xia's
interval (6.5) when `∫θ_φⁿ ≤ ∫θ_ψⁿ < ∞`. -/
theorem isAdmissibleWeight_of_lt_mul {mphi mpsi : ℝ≥0∞} (hle : mphi ≤ mpsi) (hfin : mpsi ≠ ⊤)
    {t : ℝ} (ht : 1 < t)
    (h : ENNReal.ofReal (t ^ n - 1) * mpsi < ENNReal.ofReal (t ^ n) * mphi) :
    IsAdmissibleWeight n mphi mpsi t := by
  refine ⟨ht, ?_⟩
  have hfin' : mphi ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  set p := mphi.toReal with hp
  set q := mpsi.toReal with hq
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hpq : p ≤ q := ENNReal.toReal_mono hfin hle
  have hmphi : mphi = ENNReal.ofReal p := (ENNReal.ofReal_toReal hfin').symm
  have hmpsi : mpsi = ENNReal.ofReal q := (ENNReal.ofReal_toReal hfin).symm
  have hx : (1 : ℝ) ≤ t ^ n := one_le_pow₀ ht.le
  rw [hmphi, hmpsi] at h ⊢
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ENNReal.ofReal_lt_ofReal_iff'] at h
  obtain ⟨h1, h2⟩ := h
  have hq0 : 0 < q := by
    rcases eq_or_lt_of_le (hp0.trans hpq) with hq' | hq'
    · exfalso
      have hp00 : p = 0 := le_antisymm (hpq.trans_eq hq'.symm) hp0
      rw [hp00, mul_zero] at h2
      exact lt_irrefl 0 h2
    · exact hq'
  rw [← ENNReal.ofReal_sub _ hp0, ← ENNReal.ofReal_mul (by linarith),
    ENNReal.ofReal_lt_ofReal_iff hq0]
  nlinarith

/-! ### Convex combinations and constants -/

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Finite constants pass through a convex combination with weights in `(0, 1)`. -/
theorem convexComb_add_const {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (u v : M → EReal) (c d : ℝ) :
    convexComb t (fun x => u x + (c : EReal)) (fun x => v x + (d : EReal)) =
      fun x => convexComb t u v x + ((t * c + (1 - t) * d : ℝ) : EReal) := by
  funext x
  simp only [convexComb_apply]
  rw [coe_mul_add_coe ht0, coe_mul_add_coe (by linarith : (0 : ℝ) < 1 - t), EReal.coe_add,
    add_add_add_comm]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `a - c ≤ b` in `EReal` gives `a ≤ b + c` for a finite `c`. -/
theorem le_add_coe_of_add_neg_le {a b : EReal} {c : ℝ} (h : a + ((-c : ℝ) : EReal) ≤ b) :
    a ≤ b + (c : EReal) := by
  have h' := add_le_add h (le_refl (c : EReal))
  rwa [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h'

/-! ### Xia's Theorem 6.1.1 -/

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **Xia's Theorem 6.1.1** (SGPT, `xia-sgpt:page-0217`--`page-0218`), without its `P`-order
clauses.  On a connected compact Kähler manifold, let `φ, ψ` be `θ`-PSH potentials with
`∫θ_φⁿ > 0` and `φ ⪯_{P,θ} ψ` (`P_θ[φ] ≤ P_θ[ψ]`), and let `a` lie in Xia's interval (6.5)
(`IsAdmissibleWeight`).  Then `η = P_θ(aφ + (1 - a)ψ)` is a genuine `θ`-PSH potential, of mass at
least `((a' - a)/a')ⁿ ∫θ_φⁿ` for every admissible `a' > a` (Xia's (2.38)), hence of positive mass,
and `a⁻¹ η + (1 - a⁻¹) ψ ≤ φ` everywhere (6.6).  No positivity of `∫θ_ψⁿ` is assumed (it follows). -/
theorem xiaTheorem611 (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hpos : 0 < diagonalPotentialMass theta phi hphi)
    (hP : POrderWith theta phi psi) {a : ℝ}
    (ha : IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a) :
    ∃ heta : IsThetaPshPotential theta.val (rooftopEnvelope theta.val (convexComb a phi psi)),
      (∀ a' : ℝ, a < a' → IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
          (diagonalPotentialMass theta psi hpsi) a' →
        ENNReal.ofReal ((1 - a / a') ^ n) * diagonalPotentialMass theta phi hphi ≤
          diagonalPotentialMass theta (rooftopEnvelope theta.val (convexComb a phi psi)) heta) ∧
      0 < diagonalPotentialMass theta (rooftopEnvelope theta.val (convexComb a phi psi)) heta ∧
      convexComb a⁻¹ (rooftopEnvelope theta.val (convexComb a phi psi)) psi ≤ phi := by
  have ha1 : 1 < a := ha.one_lt
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha1
  have hai0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have hai1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha1
  have hlocal : HasSmoothLocalPotentials theta.val := hphi.1.hasSmoothLocalPotentials
  -- the `P`-envelope of `psi`, shifted above `phi`
  set P0 : M → EReal := singularityEnvelope theta.val psi with hP0def
  have hP0 : IsThetaPshPotential theta.val P0 :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1 theta.property.2 hlocal
      psi hpsi
  obtain ⟨Cφ, hCφ⟩ := hphi.exists_global_upper_bound
  obtain ⟨Cψ, hCψ⟩ := hpsi.exists_global_upper_bound
  set Psi : M → EReal := fun x => P0 x + (Cφ : EReal) with hPsidef
  have hPsi : IsThetaPshPotential theta.val Psi := hP0.add_const Cφ
  have hnorm : ∀ {u : M → EReal} {C : ℝ}, (∀ x, u x ≤ (C : EReal)) →
      ∀ x, u x + ((-C : ℝ) : EReal) ≤ 0 := by
    intro u C hC x
    have h := add_le_add (hC x) (le_refl ((-C : ℝ) : EReal))
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
  -- `phi ≤ Psi`: the `P`-order after the shift by `sup phi`
  have hphiPsi : phi ≤ Psi := by
    intro x
    have h1 : phi x + ((-Cφ : ℝ) : EReal) ≤ singularityEnvelope theta.val phi x :=
      le_singularityEnvelope (hphi.add_const (-Cφ)) (hnorm hCφ)
        (sameSingularityTypeOn_add_const phi univ (-Cφ)).1 x
    exact le_add_coe_of_add_neg_le (h1.trans (hP x))
  -- `psi ≤ Psi + C'`
  set C' : ℝ := Cψ - Cφ with hC'
  have hpsiPsi : psi ≤ fun x => Psi x + (C' : EReal) := by
    intro x
    have h1 : psi x + ((-Cψ : ℝ) : EReal) ≤ P0 x :=
      le_singularityEnvelope (hpsi.add_const (-Cψ)) (hnorm hCψ)
        (sameSingularityTypeOn_add_const psi univ (-Cψ)).1 x
    have h2 := le_add_coe_of_add_neg_le h1
    calc psi x ≤ P0 x + (Cψ : EReal) := h2
      _ = Psi x + (C' : EReal) := by
          simp only [hPsidef, hC', add_assoc, ← EReal.coe_add]
          congr 2
          ring
  -- the masses of `Psi` and `psi` agree (Xia, Proposition 3.1.3)
  have hmassPsi : diagonalPotentialMass theta Psi hPsi = diagonalPotentialMass theta psi hpsi :=
    (diagonalPotentialMass_add_const theta hP0 Cφ hPsi).trans
      (singularityEnvelopeMassPreserving omega theta psi hpsi hP0)
  have hadm : ∀ b, IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) b →
      IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
        (diagonalPotentialMass theta Psi hPsi) b := fun b hb => hmassPsi ▸ hb
  -- Lemma 2.4.4 for `phi ≤ Psi`
  obtain ⟨hE', hbar'⟩ :=
    isThetaPshPotential_rooftopEnvelope_convexComb omega theta hphi hPsi hphiPsi hpos (hadm a ha)
  set E' : M → EReal := rooftopEnvelope theta.val (convexComb a phi Psi) with hE'def
  -- its shift is a competitor of the original obstacle
  set D : ℝ := -((a - 1) * C') with hD
  set E'' : M → EReal := fun x => E' x + (D : EReal) with hE''def
  have hE'' : IsThetaPshPotential theta.val E'' := hE'.add_const D
  have hbar'' : convexComb a⁻¹ E'' psi ≤ phi := by
    have hmono : convexComb a⁻¹ E'' psi ≤ convexComb a⁻¹ E'' (fun x => Psi x + (C' : EReal)) :=
      convexComb_mono hai0.le hai1.le le_rfl hpsiPsi
    rw [hE''def, convexComb_add_const hai0 hai1] at hmono
    have hzero : a⁻¹ * D + (1 - a⁻¹) * C' = 0 := by
      rw [hD]
      field_simp
      ring
    rw [hzero, EReal.coe_zero] at hmono
    intro x
    have hx := hmono x
    simp only [add_zero] at hx
    exact hx.trans (hbar' x)
  have hcomp : E'' ∈ rooftopCompetitors theta.val (convexComb a phi psi) :=
    mem_rooftopCompetitors_of_barrier hpsi ha1 hE'' hbar''
  have hne : (rooftopCompetitors theta.val (convexComb a phi psi)).Nonempty := ⟨E'', hcomp⟩
  -- the competitors are uniformly bounded above
  have hbound : ∃ B : ℝ, ∀ g ∈ rooftopCompetitors theta.val (convexComb a phi psi), ∀ x,
      g x ≤ (B : EReal) := by
    obtain ⟨C, hC⟩ := exists_upper_bound_of_convexComb_le hpsi hai0 hai1 Cφ
    exact ⟨C, fun g hg => hC g hg.1 fun x =>
      (barrier_of_mem_rooftopCompetitors hphi hpsi ha1 hg.1 hg x).trans (hCφ x)⟩
  have heta : IsThetaPshPotential theta.val (rooftopEnvelope theta.val (convexComb a phi psi)) :=
    isThetaPshPotential_rooftop_of_nonempty hne hbound
  -- the mass
  have hE''le : E'' ≤ rooftopEnvelope theta.val (convexComb a phi psi) :=
    le_rooftopEnvelope hcomp.1 hcomp.2
  have hmassE : diagonalPotentialMass theta E' hE' ≤
      diagonalPotentialMass theta (rooftopEnvelope theta.val (convexComb a phi psi)) heta := by
    rw [← diagonalPotentialMass_add_const theta hE' D hE'']
    exact diagonalPotentialMass_mono_of_kahler omega hE'' heta
      (MoreSingularOn.of_le fun x _ => hE''le x)
  have hlower : ∀ a' : ℝ, a < a' → IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a' →
      ENNReal.ofReal ((1 - a / a') ^ n) * diagonalPotentialMass theta phi hphi ≤
        diagonalPotentialMass theta (rooftopEnvelope theta.val (convexComb a phi psi)) heta :=
    fun a' haa ha' => (ofReal_pow_mul_mass_le_mass_rooftopEnvelope omega theta hphi hPsi hphiPsi
      hpos (hadm a ha) haa (hadm a' ha') hE').trans hmassE
  refine ⟨heta, hlower, ?_, ?_⟩
  · obtain ⟨a', haa, ha'⟩ := IsAdmissibleWeight.exists_gt ha
    refine lt_of_lt_of_le ?_ (hlower a' haa ha')
    have ha'0 : (0 : ℝ) < a' := ha0.trans haa
    have hr : (0 : ℝ) < 1 - a / a' := by
      rw [sub_pos, div_lt_one ha'0]
      exact haa
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne' hpos.ne'
  · -- (6.6): the envelope satisfies the barrier inequality itself
    have hW : IsThetaPshPotential theta.val
        (convexComb a⁻¹ (rooftopEnvelope theta.val (convexComb a phi psi)) psi) :=
      isThetaPshPotential_convexComb heta hpsi hai0 hai1
    refine ThetaPlurisubharmonic.le_of_ae_in_charts_le hW.1 hphi.1 ?_
    intro e
    have hae1 := ae_rooftopEnvelope_le_obstacle theta hne hbound e
    have hae2 := (quasiPsh_finite_quasiEverywhere
      (u := psi) hpsi.quasiPshPotential).ae_in_chart e volume
    filter_upwards [hae1, hae2] with z h1 h2
    exact (convexCombValue_le_iff ha1 h2.1 h2.2).mpr h1

/-- **Positive mass for affine rooftop obstacles** (Copy-4 `thm:rooftop`, citing Xia's Theorem
6.1.1; blueprint `ana:rooftop-positive-mass`).  On a connected compact Kähler manifold, let
`φ, ψ ∈ PSH(X, θ)` with `∫θ_φⁿ > 0` and `φ ⪯_{P,θ} ψ`.  If `t > 1` and
`tⁿ ∫θ_φⁿ > (tⁿ - 1) ∫θ_ψⁿ`, then `P_θ(tφ - (t - 1)ψ) = P_θ(tφ + (1 - t)ψ)` is a genuine
`θ`-PSH potential of positive mass.  (Positivity of `∫θ_ψⁿ`, which the source also assumes, is not
needed.) -/
theorem isThetaPshPotential_rooftopEnvelope_of_pOrderWith (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi) (hP : POrderWith theta phi psi) {t : ℝ}
    (ht : 1 < t)
    (hmass : ENNReal.ofReal (t ^ n - 1) * diagonalPotentialMass theta psi hpsi <
      ENNReal.ofReal (t ^ n) * diagonalPotentialMass theta phi hphi) :
    ∃ heta : IsThetaPshPotential theta.val (rooftopEnvelope theta.val (convexComb t phi psi)),
      0 < diagonalPotentialMass theta (rooftopEnvelope theta.val (convexComb t phi psi)) heta := by
  have hlocal : HasSmoothLocalPotentials theta.val := hphi.1.hasSmoothLocalPotentials
  -- `∫θ_φⁿ ≤ ∫θ_ψⁿ` (Xia, Proposition 6.1.4, diagonal case)
  have hPphi : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1 theta.property.2 hlocal
      phi hphi
  have hPpsi : IsThetaPshPotential theta.val (singularityEnvelope theta.val psi) :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1 theta.property.2 hlocal
      psi hpsi
  have hle : diagonalPotentialMass theta phi hphi ≤ diagonalPotentialMass theta psi hpsi := by
    rw [← singularityEnvelopeMassPreserving omega theta phi hphi hPphi,
      ← singularityEnvelopeMassPreserving omega theta psi hpsi hPpsi]
    exact diagonalPotentialMass_mono_of_kahler omega hPphi hPpsi
      (MoreSingularOn.of_le fun x _ => hP x)
  have hfin : diagonalPotentialMass theta psi hpsi ≠ ⊤ :=
    (DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top omega theta hpsi univ).ne
  obtain ⟨heta, -, hpos', -⟩ := xiaTheorem611 omega theta hphi hpsi hpos hP
    (isAdmissibleWeight_of_lt_mul hle hfin ht hmass)
  exact ⟨heta, hpos'⟩

end

end SGPT.Foundations.Analysis.Pending.POrderAffineRooftop
