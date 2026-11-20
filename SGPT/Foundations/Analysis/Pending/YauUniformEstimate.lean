import SGPT.Foundations.Analysis.Pending.MongeAmpereLocalStability
import SGPT.Foundations.Analysis.Pending.KahlerPotentialNormalization
import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound
import SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
import SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison
import SGPT.Foundations.Analysis.Pending.RegularPatchDensityContinuity
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The uniform (`C⁰`) estimate for the complex Monge--Ampère equation (Błocki)

Let `Y` be a compact connected complex manifold of dimension `N` with a Kähler form `A`, and
`B ∈ ℝ`.  There is `C = C(Y, A, B)` such that every chart-smooth `φ` with `A + ddᶜφ ≥ 0` and
`(A + ddᶜφ)^N ≤ B A^N` (pointwise in charts) has `osc φ ≤ C`
(`exists_sub_le_of_mongeAmpere_le`).  This is Błocki's Theorem 4
(`blocki05-uniform-estimate:page-0003`--`page-0004`) = Theorem 5.6 of `lnm2038-monge-ampere:page-0217`
(second proof, `page-0221`), the `C⁰` estimate (N2) of Yau's theorem (plan
the proof of Yau's theorem §2).

## Proof

* `exists_ofReal_neg_le` (in one chart, Euclidean): with `ρ` a local potential of `A` on `W ⊇ K =
  closedBall c (3R)` and `ψ` a `C²` function attaining its minimum over `K` at `z₀ ∈ closedBall c R`,
  with `det(ρ + ψ)_{jk̄} ≤ F` on `K`: `(-ψ(z₀))⁺ ≤ C₁ + C₂ ∫_K (-ψ)⁺`.  Proof: the normalised potential
  `g = ρ - pluriharmonicPart ρ z₀` (`KahlerPotentialNormalization.exists_normalized_potential`) and
  `u = g + ψ` on `Ω = B(z₀, 2r)`: `{u < u(z₀) + a} ⊆ B(z₀, r)`, so Błocki's Proposition 3
  (`MongeAmpereLocalStability.volume_ball_mul_le_lintegral`) applies.
* `exists_local_bound` (on `Y`, near a point): the `L¹` bound of normalised `A`-psh functions on
  compact chart sets (`ThetaPshUniformL1Bound.exists_lintegral_compact_le`, Błocki's (3) /
  LNM Prop. 5.7 for `p = 1`) bounds `∫_K (-ψ)⁺` for `ψ = φ ∘ e⁻¹`, `max φ = 0`.
* compactness of `Y` (finitely many charts), normalisation `φ - max φ`; dimension `0` is trivial
  (a connected `0`-dimensional manifold is a point).
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.YauUniformEstimate

open FirstPass FirstPass.MongeAmpere MongeAmpereLocalStability KahlerPotentialNormalization

/-! ### The estimate in one chart -/

section Euclidean

variable {n : ℕ}

/-- **The `C⁰` estimate in one chart**: `(-ψ(z₀))⁺ ≤ C₁ + C₂ ∫_K (-ψ)⁺` at a minimum point
`z₀ ∈ closedBall c R` of `ψ` over `K = closedBall c (3R)`, when `det (ρ + ψ)_{jk̄} ≤ F` on `K`. -/
theorem exists_ofReal_neg_le (hn : 0 < n) {ρ : ComplexModel n → ℝ} {W : Set (ComplexModel n)}
    (hW : IsOpen W) (hρ : ContDiffOn ℝ 2 ρ W)
    (hlevi : ∀ z ∈ W, ∀ v, v ≠ 0 → 0 < leviForm ρ z v) {c : ComplexModel n} {R : ℝ}
    (hR : 0 < R) (hcW : closedBall c (3 * R) ⊆ W) (F : ℝ) :
    ∃ C₁ C₂ : ℝ≥0∞, C₁ ≠ ⊤ ∧ C₂ ≠ ⊤ ∧ ∀ ψ : ComplexModel n → ℝ, ContDiffOn ℝ 2 ψ W →
      ∀ z₀ ∈ closedBall c R, (∀ z ∈ closedBall c (3 * R), ψ z₀ ≤ ψ z) →
      (∀ z ∈ closedBall c (3 * R), (complexHessian (fun w => ρ w + ψ w) z).det.re ≤ F) →
      ENNReal.ofReal (-ψ z₀) ≤ C₁ + C₂ * ∫⁻ z in closedBall c (3 * R), ENNReal.ofReal (-ψ z) := by
  obtain ⟨r, a, hr, hrR, ha, hnorm⟩ := exists_normalized_potential hn hW hρ hlevi hR hcW
  set V := volume (ball (0 : ComplexModel n) (a / (2 * r))) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ (by positivity)).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨ENNReal.ofReal a, V⁻¹ * ENNReal.ofReal (4 ^ n * F ^ 2), ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV0) ENNReal.ofReal_ne_top,
    fun ψ hψ z₀ hz₀ hmin hdet => ?_⟩
  obtain ⟨hg0, hgnn, hga⟩ := hnorm z₀ hz₀
  set K := closedBall c (3 * R) with hKdef
  set Ω := ball z₀ (2 * r) with hΩdef
  have hΩK : Ω ⊆ K := by
    intro z hz
    rw [hΩdef, mem_ball, dist_eq_norm] at hz
    have : ‖z₀ - c‖ ≤ R := by simpa [dist_eq_norm] using hz₀
    rw [hKdef, mem_closedBall, dist_eq_norm]
    calc ‖z - c‖ = ‖(z - z₀) + (z₀ - c)‖ := by congr 1; abel
      _ ≤ ‖z - z₀‖ + ‖z₀ - c‖ := norm_add_le _ _
      _ ≤ 3 * R := by linarith
  have hz₀K : z₀ ∈ K := by
    have : closedBall c R ⊆ K := closedBall_subset_closedBall (by linarith)
    exact this hz₀
  have hz₀W : z₀ ∈ W := hcW hz₀K
  have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ ρ) z₀ v w = fderiv ℝ (fderiv ℝ ρ) z₀ w v :=
    fun v w => (hρ.contDiffAt (hW.mem_nhds hz₀W)).isSymmSndFDerivAt (by simp) v w
  set u : ComplexModel n → ℝ := fun z => (ρ z - pluriharmonicPart ρ z₀ z) + ψ z with hudef
  have hu : ContDiffOn ℝ 2 u Ω :=
    ((hρ.sub (contDiff_pluriharmonicPart ρ z₀).contDiffOn).add hψ).mono
      (hΩK.trans hcW)
  have hF : ∀ z ∈ Ω, (complexHessian u z).det.re ≤ F := by
    intro z hz
    have hzW : z ∈ W := hcW (hΩK hz)
    have hf : ContDiffAt ℝ 2 (fun w => ρ w + ψ w) z :=
      (hρ.add hψ).contDiffAt (hW.mem_nhds hzW)
    have hueq : u = fun w => (ρ w + ψ w) - pluriharmonicPart ρ z₀ w := by
      funext w; simp only [hudef]; ring
    rw [hueq, complexHessian_sub_pluriharmonicPart hsymm hf]
    exact hdet z (hΩK hz)
  have hz₀Ω : z₀ ∈ Ω := mem_ball_self (by positivity)
  have hd : ∀ z ∈ Ω, ‖z - z₀‖ ≤ 2 * r := fun z hz => by
    rw [hΩdef, mem_ball, dist_eq_norm] at hz; exact hz.le
  -- the sublevel set lies in `B(z₀, r)`
  have hsub : {z | z ∈ Ω ∧ u z < u z₀ + a} ⊆ closedBall z₀ r := by
    intro z ⟨hzΩ, hzu⟩
    rw [mem_closedBall, dist_eq_norm]
    by_contra hfar
    rw [not_le] at hfar
    have h1 := hga z hzΩ hfar.le
    have h2 := hmin z (hΩK hzΩ)
    simp only [hudef, hg0, zero_add] at hzu
    linarith
  have hcl : closure {z | z ∈ Ω ∧ u z < u z₀ + a} ⊆ closedBall z₀ r :=
    closure_minimal hsub isClosed_closedBall
  have hKc : IsCompact (closure {z | z ∈ Ω ∧ u z < u z₀ + a}) :=
    (isCompact_closedBall z₀ r).of_isClosed_subset isClosed_closure hcl
  have hKΩ : closure {z | z ∈ Ω ∧ u z < u z₀ + a} ⊆ Ω :=
    hcl.trans (closedBall_subset_ball (by linarith))
  have hstab := volume_ball_mul_le_lintegral isOpen_ball hu hF hz₀Ω ha hd hKc hKΩ
  -- bound the integral over `Ω` by the integral of `(-ψ)⁺` over `K`
  have hint : ∫⁻ z in Ω, ENNReal.ofReal (-u z) ≤ ∫⁻ z in K, ENNReal.ofReal (-ψ z) := by
    calc ∫⁻ z in Ω, ENNReal.ofReal (-u z) ≤ ∫⁻ z in Ω, ENNReal.ofReal (-ψ z) :=
          setLIntegral_mono' isOpen_ball.measurableSet fun z hz =>
            ENNReal.ofReal_le_ofReal (by simp only [hudef]; linarith [hgnn z hz])
      _ ≤ ∫⁻ z in K, ENNReal.ofReal (-ψ z) := lintegral_mono_set hΩK
  have huz₀ : -u z₀ - a = -ψ z₀ - a := by simp only [hudef, hg0, zero_add]
  rw [huz₀] at hstab
  have h1 : ENNReal.ofReal (-ψ z₀ - a) ≤
      V⁻¹ * (ENNReal.ofReal (4 ^ n * F ^ 2) * ∫⁻ z in K, ENNReal.ofReal (-ψ z)) := by
    rw [← ENNReal.mul_le_iff_le_inv hV0 hVt]
    exact hstab.trans (by gcongr)
  calc ENNReal.ofReal (-ψ z₀) = ENNReal.ofReal ((-ψ z₀ - a) + a) := by ring_nf
    _ ≤ ENNReal.ofReal (-ψ z₀ - a) + ENNReal.ofReal a := ENNReal.ofReal_add_le
    _ ≤ V⁻¹ * (ENNReal.ofReal (4 ^ n * F ^ 2) * ∫⁻ z in K, ENNReal.ofReal (-ψ z)) +
          ENNReal.ofReal a := by gcongr
    _ = ENNReal.ofReal a + V⁻¹ * ENNReal.ofReal (4 ^ n * F ^ 2) *
          ∫⁻ z in K, ENNReal.ofReal (-ψ z) := by rw [add_comm, mul_assoc]

end Euclidean

/-! ### On the manifold -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

open ManifoldTubePositivity

/-- A chart-smooth function is continuous. -/
theorem continuous_of_chartSmooth {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) : Continuous φ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  let e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hc : ContinuousAt (fun z => φ (e.val.symm z)) (e.val x) :=
    ((hφ e).continuousOn).continuousAt (e.val.open_target.mem_nhds hz)
  have hcomp : ContinuousAt (fun y => φ (e.val.symm (e.val y))) x :=
    hc.comp (e.val.continuousAt hx)
  refine hcomp.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  rw [e.val.left_inv hy]

/-- The chart density of `A + ddᶜφ` is `(N!/πᴺ) det` of the complex Hessian of `ρ + φ ∘ e⁻¹`. -/
theorem re_det_complexHessian_eq {A : PositiveClasses.KahlerBackground N Y} {φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) {e : ComplexChart N Y} {W : Set (ComplexModel N)}
    {ρ : ComplexModel N → ℝ} (hpot : IsSmoothLocalPotential A.form.val e W ρ)
    {z : ComplexModel N} (hz : z ∈ W) :
    (complexHessian (fun w => ρ w + φ (e.val.symm w)) z).det.re =
      Real.pi ^ N / N.factorial *
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) := by
  have hzt : z ∈ e.val.target := hpot.2.1 hz
  have hρ : ContDiffOn ℝ ∞ ρ W := hpot.2.2.1
  have hψ : ContDiffOn ℝ ∞ (fun w => φ (e.val.symm w)) W := (hφ e).mono hpot.2.1
  have hsum : ContDiffAt ℝ 2 (fun w => ρ w + φ (e.val.symm w)) z :=
    ((hρ.add hψ).contDiffAt (hpot.1.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcoeff : (A.form + ddcClosedForm φ hφ).val.coeff e z =
      smoothDDC (fun w => ρ w + φ (e.val.symm w)) z := by
    rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff, smoothDDC_add hpot.1 hρ hψ hz,
      hpot.2.2.2 hz]
  have h11 : IsOneOne ((A.form + ddcClosedForm φ hφ).val.coeff e z) :=
    (A.form + ddcClosedForm φ hφ).property.2 e z hzt
  rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det h11, hcoeff,
    normalizedHermitianMatrix_smoothDDC hsum]
  have hpi : (0 : ℝ) < Real.pi ^ N := pow_pos Real.pi_pos N
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  field_simp

/-- **The `C⁰` estimate near a point** (Błocki's Theorem 4 locally). -/
theorem exists_local_bound (hN : 0 < N) [CompactSpace Y] [ConnectedSpace Y]
    (A : PositiveClasses.KahlerBackground N Y) (B : ℝ) (p : Y) :
    ∃ O : Set Y, IsOpen O ∧ p ∈ O ∧ ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ddcClosedForm φ hφ).val.IsSemipositive →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) ≤
          B * actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ x, φ x ≤ 0) → (∃ x₁, φ x₁ = 0) →
      ∀ y ∈ O, (∀ x, φ y ≤ φ x) → -φ y ≤ C := by
  set e := complexChartAt (n := N) p with he
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  have hzp : e.val p ∈ e.val.target := e.val.map_source hp
  obtain ⟨W, ρ, hzW, hpot⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials A.form e (e.val p) hzp
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.mp hpot.1 (e.val p) hzW
  set R := R₀ / 4 with hRdef
  have hR : 0 < R := by positivity
  have hcW : closedBall (e.val p) (3 * R) ⊆ W :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hball
  set K := closedBall (e.val p) (3 * R) with hKdef
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ e.val.target := hcW.trans hpot.2.1
  have hρ2 : ContDiffOn ℝ 2 ρ W :=
    hpot.2.2.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  -- the Levi form of `ρ` is positive (`A` is Kähler)
  have hlevi : ∀ z ∈ W, ∀ v, v ≠ 0 → 0 < leviForm ρ z v := by
    intro z hz v hv
    have hpos := (A.isKahler.1 e z (hpot.2.1 hz)).2 v hv
    rw [← hpot.2.2.2 hz,
      smoothDDC_complexDiagonal_eq_leviForm ((hρ2.contDiffAt (hpot.1.mem_nhds hz)))] at hpos
    exact (div_pos_iff_of_pos_right Real.pi_pos).mp hpos
  -- a bound for the density of `A` on `K`
  have hdc : ContinuousOn (fun z => actualTopPowerDensity (A.form.val.coeff e z)) K :=
    (RegularPatchTransition.continuous_topPowerDensity N).comp_continuousOn
      ((A.form.val.smooth e).continuousOn.mono hKt)
  obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn hdc
  set F : ℝ := Real.pi ^ N / N.factorial * (max B 0 * D) with hFdef
  obtain ⟨C₁, C₂, hC₁, hC₂, hloc⟩ := exists_ofReal_neg_le hN hpot.1 hρ2 hlevi hR hcW F
  obtain ⟨BL, hBL, hBLu⟩ := ThetaPshUniformL1Bound.exists_lintegral_compact_le
    (LocalPotentials.closedRealOneOne_hasLocalPotentials A.form) e hKc hKt 0
  refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val p) R, e.val.isOpen_inter_preimage isOpen_ball,
    ⟨hp, mem_ball_self hR⟩, (C₁ + C₂ * BL).toReal,
    fun φ hφ hsemi hdens hle hzero y hy hmin => ?_⟩
  set ψ : ComplexModel N → ℝ := fun z => φ (e.val.symm z) with hψdef
  have hψ : ContDiffOn ℝ 2 ψ W :=
    ((hφ e).mono hpot.2.1).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hz₀ : e.val y ∈ closedBall (e.val p) R := ball_subset_closedBall hy.2
  have hmin' : ∀ z ∈ K, ψ (e.val y) ≤ ψ z := fun z _ => by
    simp only [hψdef, e.val.left_inv hy.1]; exact hmin _
  have hdet : ∀ z ∈ K, (complexHessian (fun w => ρ w + ψ w) z).det.re ≤ F := by
    intro z hz
    have hzt : z ∈ e.val.target := hKt hz
    rw [re_det_complexHessian_eq hφ hpot (hcW hz), hFdef]
    have hA0 : 0 ≤ actualTopPowerDensity (A.form.val.coeff e z) :=
      actualTopPowerDensity_nonneg (A.form.property.2 e z hzt) (A.isSemipositive e z hzt)
    have hAD : actualTopPowerDensity (A.form.val.coeff e z) ≤ D :=
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hD z hz)
    have h1 := hdens e z hzt
    have h2 : B * actualTopPowerDensity (A.form.val.coeff e z) ≤ max B 0 * D :=
      (mul_le_mul_of_nonneg_right (le_max_left B 0) hA0).trans
        (mul_le_mul_of_nonneg_left hAD (le_max_right B 0))
    have hc : 0 ≤ Real.pi ^ N / N.factorial := by positivity
    exact mul_le_mul_of_nonneg_left (h1.trans h2) hc
  have hloc' := hloc ψ hψ (e.val y) hz₀ hmin' hdet
  -- the `L¹` bound
  have hpsh : ThetaPlurisubharmonic A.form.val (fun x => (φ x : EReal)) := by
    refine (LocalPotentials.thetaPlurisubharmonic_smooth_iff A.form φ hφ).mpr
      fun e' z hz v => ?_
    have := hsemi e' z hz v
    simpa [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff] using this
  obtain ⟨x₁, hx₁⟩ := hzero
  have hL1 := hBLu (fun x => (φ x : EReal)) hpsh (fun x => by exact_mod_cast hle x)
    ⟨x₁, by simp [hx₁]⟩
  have hint : ∫⁻ z in K, ENNReal.ofReal (-ψ z) ≤ BL := by
    refine le_trans (le_of_eq ?_) hL1
    refine lintegral_congr fun z => ?_
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have htop : C₁ + C₂ * BL ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hC₁, ENNReal.mul_ne_top hC₂ hBL.ne⟩
  have : ENNReal.ofReal (-φ y) ≤ C₁ + C₂ * BL := by
    have h : ENNReal.ofReal (-ψ (e.val y)) ≤ C₁ + C₂ * BL :=
      le_trans hloc' (by gcongr)
    have hψy : ψ (e.val y) = φ y := by simp only [hψdef, e.val.left_inv hy.1]
    rwa [hψy] at h
  exact (ENNReal.ofReal_le_iff_le_toReal htop).mp this

/-- A connected complex manifold of dimension `0` is a point. -/
theorem eq_of_dim_zero [ConnectedSpace Y] (hN : N = 0) (x y : Y) : x = y := by
  subst hN
  have hopen : ∀ x : Y, IsOpen ({x} : Set Y) := fun x => by
    have hsub : (chartAt (ComplexModel 0) x).source ⊆ {x} := fun y hy =>
      (chartAt (ComplexModel 0) x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
    have hsup : ({x} : Set Y) ⊆ (chartAt (ComplexModel 0) x).source :=
      singleton_subset_iff.mpr (mem_chart_source _ x)
    rw [← Subset.antisymm hsub hsup]
    exact (chartAt (ComplexModel 0) x).open_source
  have hclosed : IsClosed ({x} : Set Y) := by
    rw [← isOpen_compl_iff]
    have : ({x} : Set Y)ᶜ = ⋃ z ∈ ({x} : Set Y)ᶜ, {z} := by ext; simp
    rw [this]
    exact isOpen_biUnion fun z _ => hopen z
  rcases isClopen_iff.mp ⟨hclosed, hopen x⟩ with h | h
  · exact absurd (h ▸ mem_singleton x) (Set.notMem_empty x)
  · have : y ∈ ({x} : Set Y) := h ▸ mem_univ y
    exact (mem_singleton_iff.mp this).symm

/-- **The uniform estimate** (Błocki's Theorem 4, `blocki05-uniform-estimate:page-0003`; LNM 2038,
Theorem 5.6, `lnm2038-monge-ampere:page-0217`, second proof `page-0221`): on a compact connected
complex manifold `Y` with a Kähler form `A`, for every `B` there is `C` such that every chart-smooth
`φ` with `A + ddᶜφ ≥ 0` and `(A + ddᶜφ)^N ≤ B A^N` in every chart has `φ x - φ y ≤ C`. -/
theorem exists_sub_le_of_mongeAmpere_le {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y]
    (A : PositiveClasses.KahlerBackground N Y) (B : ℝ) :
    ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ManifoldTubePositivity.ddcClosedForm φ hφ).val.IsSemipositive →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ManifoldTubePositivity.ddcClosedForm φ hφ).val.coeff e z) ≤
          B * actualTopPowerDensity (A.form.val.coeff e z)) →
      ∀ x y, φ x - φ y ≤ C := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact ⟨0, fun φ _ _ _ x y => by rw [eq_of_dim_zero hN x y, sub_self]⟩
  choose O hO hpO C hC using exists_local_bound hN A B
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  refine ⟨∑ p ∈ t, max (C p) 0, fun φ hφ hsemi hdens x y => ?_⟩
  have hφc := continuous_of_chartSmooth hφ
  obtain ⟨xM, -, hxM⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hφc.continuousOn
  obtain ⟨ym, -, hym⟩ := isCompact_univ.exists_isMinOn ⟨x, mem_univ x⟩ hφc.continuousOn
  set m := φ xM with hm
  -- the normalised function `φ - max φ`
  set φ' : Y → ℝ := fun x => φ x - m with hφ'def
  have hφ' : ChartSmooth (n := N) φ' := fun e => (hφ e).sub contDiffOn_const
  have hco : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
      (ManifoldTubePositivity.ddcClosedForm φ' hφ').val.coeff e z =
        (ManifoldTubePositivity.ddcClosedForm φ hφ).val.coeff e z := by
    intro e z hz
    rw [ManifoldTubePositivity.ddcClosedForm_coeff, ManifoldTubePositivity.ddcClosedForm_coeff]
    simp only [hφ'def]
    rw [PositiveClasses.smoothDDC_sub e.val.open_target (hφ e) contDiffOn_const hz,
      GlobalPotentialTransforms.smoothDDC_const, sub_zero]
  have hcoA : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
      (A.form + ManifoldTubePositivity.ddcClosedForm φ' hφ').val.coeff e z =
        (A.form + ManifoldTubePositivity.ddcClosedForm φ hφ).val.coeff e z := by
    intro e z hz
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, hco e z hz]
  have hsemi' : (A.form + ManifoldTubePositivity.ddcClosedForm φ' hφ').val.IsSemipositive :=
    fun e z hz v => by rw [hcoA e z hz]; exact hsemi e z hz v
  have hdens' : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ManifoldTubePositivity.ddcClosedForm φ' hφ').val.coeff e z) ≤
        B * actualTopPowerDensity (A.form.val.coeff e z) :=
    fun e z hz => by rw [hcoA e z hz]; exact hdens e z hz
  have hle : ∀ x, φ' x ≤ 0 := fun x => by
    simp only [hφ'def]; linarith [isMaxOn_iff.mp hxM x (mem_univ x)]
  have hzero : ∃ x₁, φ' x₁ = 0 := ⟨xM, by simp [hφ'def, hm]⟩
  have hmin' : ∀ x, φ' ym ≤ φ' x := fun x => by
    simp only [hφ'def]; linarith [isMinOn_iff.mp hym x (mem_univ x)]
  obtain ⟨p, hpt, hyp⟩ : ∃ p ∈ t, ym ∈ O p := by
    have := ht (mem_univ ym)
    simpa only [mem_iUnion, exists_prop] using this
  have hb := hC p φ' hφ' hsemi' hdens' hle hzero ym hyp hmin'
  have hsum : C p ≤ ∑ p ∈ t, max (C p) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun p => max (C p) 0)
      (fun _ _ => le_max_right _ _) hpt)
  have h1 : φ x ≤ m := isMaxOn_iff.mp hxM x (mem_univ x)
  have h2 : φ ym ≤ φ y := isMinOn_iff.mp hym y (mem_univ y)
  simp only [hφ'def] at hb
  linarith

end Manifold

end SGPT.Foundations.Analysis.Pending.YauUniformEstimate
