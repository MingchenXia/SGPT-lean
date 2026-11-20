import SGPT.NPP.CapacityConvergenceGlobal
import SGPT.Foundations.Analysis.Pending.ActualUnboundedDecreasingCapacity
import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingRegularizedCapacity
import SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness

/-!
# Monotone sequences of quasi-psh potentials converge in capacity

The monotone hypotheses of the semicontinuity theorem (source `thm:semicon`, chapter
`chapter_npp.tex`: "either `φ_j^k` decreases to `φ_j` or increases to `φ_j` almost everywhere")
produce convergence in Kähler capacity of the gap sets
`{u_j ≠ -∞, v ≠ -∞, |u_j - v| > a}` (Xia, *Foundations of pluripotential theory*,
`lem:extended-capacity-truncations`; Guedj–Zeriahi, Proposition 4.25, for global
`θ`-psh potentials on a compact Kähler manifold).

* Decreasing sequences: the existing unbounded result
  `ActualUnboundedDecreasingCapacity.polar_capacity_zero_and_tendsto_capacity`.
* Increasing sequences converging almost everywhere (in the Lebesgue measures of the charts):
  `tendsto_capacity_gap_of_monotone_ae`. The limit is the regularized supremum
  (`uscRegularization_iSup_eq_of_monotone_ae`, by the almost-everywhere comparison principle
  `le_of_chart_ae_le`); after normalizing to nonpositive `ω`-psh potentials and truncating at
  `-C`, the bounded increasing case is
  `SingularModelIncreasingRegularizedCapacity.tendsto_capacity_canonicalGap_of_monotone_regularized`,
  and the sublevel sets `{u_0 < -C}` have small capacity for large `C`
  (`exists_reference_tail_small`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.NPP.CapacityConvergence

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open ThetaCapacity RelativeEnergyIntegrability

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Convergence almost everywhere on the manifold: in every atlas chart, for Lebesgue-almost
every point of the coordinate domain (null sets of a manifold are measured by the Lebesgue
measures of its charts). -/
def ChartTendstoAE (u : ℕ → M → EReal) (v : M → EReal) : Prop :=
  ∀ e : ComplexChart n M, ∀ᵐ z ∂volume.restrict e.val.target,
    Tendsto (fun k => u k (e.val.symm z)) atTop (𝓝 (v (e.val.symm z)))

/-- Almost-everywhere order on the manifold, in the Lebesgue measures of the charts. -/
def ChartAELE (f g : M → EReal) : Prop :=
  ∀ e : ComplexChart n M, ∀ᵐ z ∂volume.restrict e.val.target, f (e.val.symm z) ≤ g (e.val.symm z)

variable [IsComplexManifold n M]

/-- **Almost-everywhere comparison for `θ`-psh functions**: almost-everywhere order in the
charts implies order everywhere. -/
theorem le_of_chartAELE {θ : SmoothRealForm n M 2} {f g : M → EReal}
    (hf : ThetaPlurisubharmonic θ f) (hg : ThetaPlurisubharmonic θ g)
    (hae : ChartAELE (n := n) f g) : f ≤ g := by
  intro x
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpg⟩ := hg e (e.val x) hz
  have hpf := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hf e hρ
  have hle := hpf.le_of_ae_le hρ.1 hpg.upperSemicontinuousOn volume (by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hρ.2.1 (hae e)] with y hy
    exact add_le_add_left hy _)
    (e.val x) hzW
  have hcancel := EReal.sub_le_sub hle (le_refl ((ρ (e.val x) : ℝ) : EReal))
  rw [EReal.add_sub_cancel_right, EReal.add_sub_cancel_right] at hcancel
  simpa only [chartFunction, e.val.left_inv hx] using hcancel

variable [CompactSpace M]

/-- An increasing sequence of `θ`-psh potentials converging almost everywhere to a `θ`-psh
potential `v` lies below `v`, and `v` is the regularized supremum. -/
theorem uscRegularization_iSup_eq_of_monotone_ae {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ.val (u j)) (hv : IsThetaPshPotential θ.val v)
    (hm : ∀ x, Monotone fun j => u j x) (hae : ChartTendstoAE (n := n) u v) :
    (∀ j, u j ≤ v) ∧ uscRegularization (⨆ j, u j) = v := by
  have hle : ∀ j, u j ≤ v := fun j => le_of_chartAELE (hu j).1 hv.1 fun e => by
    filter_upwards [hae e] with z hz
    exact (hm _).ge_of_tendsto hz j
  refine ⟨hle, le_antisymm ?_ ?_⟩
  · exact FirstPass.uscRegularization_le hv.1.quasiPlurisubharmonic.upperSemicontinuous
      (fun x => by simpa only [iSup_apply] using iSup_le fun j => hle j x)
  · rcases isEmpty_or_nonempty M with hM | hM
    · intro x; exact isEmptyElim x
    obtain ⟨C, hC⟩ := hv.exists_global_upper_bound
    have hw := IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded
      hu (fun j x => (hle j x).trans (hC x))
    refine le_of_chartAELE hv.1 hw.1 fun e => ?_
    filter_upwards [hae e] with z hz
    refine le_of_tendsto' hz fun j => ?_
    refine le_trans ?_ (FirstPass.le_uscRegularization _ _)
    simpa only [iSup_apply] using le_iSup (fun j => u j (e.val.symm z)) j

variable [MeasurableSpace M] [BorelSpace M]

/-- Decreasing sequences of `θ`-psh potentials converge to their limit in Kähler capacity,
in the gap form used by the semicontinuity theorem. -/
theorem tendsto_capacity_gap_of_antitone (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential α.val (u j)) (hv : IsThetaPshPotential α.val v)
    (ha : ∀ x, Antitone fun j => u j x)
    (hl : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x))) :
    ∀ a : ℝ, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|}) atTop (𝓝 0) := by
  intro a ha0
  have h := (ActualUnboundedDecreasingCapacity.polar_capacity_zero_and_tendsto_capacity
    omega hu hv ha hl).2 a ha0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun j => thetaCapacity_mono ?_)
  rintro x ⟨_, hvx, hgap⟩
  exact ⟨hvx, hgap.le⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem normalized_genuine
    (omega : KahlerBackground n M) {α : ClosedRealOneOneForm n M}
    {A b : ℝ} (hA : 0 < A) (hdom : (-α + A • omega.form).val.IsSemipositive)
    {u : M → EReal} (hu : IsThetaPshPotential α.val u) :
    IsThetaPshPotential omega.form.val (fun x => ((A⁻¹ : ℝ) : EReal) * (u x - (b : EReal))) := by
  have he : α + (-α + A • omega.form) = A • omega.form := by abel
  have hbg : IsThetaPshPotential (A • omega.form).val (fun x => u x - (b : EReal)) := by
    simpa only [he] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hu.sub_const b) hdom
  have hq := RestrictedApproximantComparison.isThetaPshPotential_smul hbg (inv_pos.mpr hA)
  have hf : A⁻¹ • (A • omega.form) = omega.form := by
    rw [smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
  simpa only [hf] using hq

private theorem normalized_toReal {A b : ℝ} {v : EReal} (hvt : v ≠ ⊤) (hvb : v ≠ ⊥) :
    (((A⁻¹ : ℝ) : EReal) * (v - (b : EReal))).toReal = A⁻¹ * (v.toReal - b) := by
  have he : ((A⁻¹ * (v.toReal - b) : ℝ) : EReal) =
      ((A⁻¹ : ℝ) : EReal) * (v - (b : EReal)) := by
    rw [EReal.coe_mul, EReal.coe_sub, EReal.coe_toReal hvt hvb]
  rw [← he, EReal.toReal_coe]

/-- The normalized truncation `w ↦ max(A⁻¹ (w - b), -C)` is continuous on the extended reals. -/
private theorem tendsto_normalized_truncation {A b C : ℝ} (hA : 0 < A) {w : ℕ → EReal}
    {w₀ : EReal} (h : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun j => max (((A⁻¹ : ℝ) : EReal) * (w j - (b : EReal))) ((0 : EReal) - (C : EReal)))
      atTop (𝓝 (max (((A⁻¹ : ℝ) : EReal) * (w₀ - (b : EReal))) ((0 : EReal) - (C : EReal)))) := by
  have h1 : Tendsto (fun j => w j - (b : EReal)) atTop (𝓝 (w₀ - (b : EReal))) := by
    have hc : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (w₀, -(b : EReal)) :=
      EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hc.tendsto.comp (h.prodMk_nhds tendsto_const_nhds)
  have hA' : ((A⁻¹ : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast (inv_pos.mpr hA).ne'
  have h2 : Tendsto (fun j => ((A⁻¹ : ℝ) : EReal) * (w j - (b : EReal))) atTop
      (𝓝 (((A⁻¹ : ℝ) : EReal) * (w₀ - (b : EReal)))) := by
    have hc : ContinuousAt (fun p : EReal × EReal => p.1 * p.2)
        (((A⁻¹ : ℝ) : EReal), w₀ - (b : EReal)) :=
      EReal.continuousAt_mul (Or.inl hA') (Or.inl hA') (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))
    exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds h1)
  exact h2.max tendsto_const_nhds

private theorem normalized_mono {A b : ℝ} (hA : 0 < A) {w w' : EReal} (h : w ≤ w') :
    ((A⁻¹ : ℝ) : EReal) * (w - (b : EReal)) ≤ ((A⁻¹ : ℝ) : EReal) * (w' - (b : EReal)) :=
  mul_le_mul_of_nonneg_left (EReal.sub_le_sub h le_rfl)
    (EReal.coe_nonneg.mpr (inv_pos.mpr hA).le)

variable [ConnectedSpace M] in
/-- **Increasing sequences converging almost everywhere converge in capacity**: if
`u_j ↑ v` almost everywhere, with `u_j, v` `θ`-psh, then the gap sets
`{u_j ≠ -∞, v ≠ -∞, |u_j - v| > a}` have Kähler capacity tending to zero. -/
theorem tendsto_capacity_gap_of_monotone_ae (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential α.val (u j)) (hv : IsThetaPshPotential α.val v)
    (hm : ∀ x, Monotone fun j => u j x) (hae : ChartTendstoAE (n := n) u v) :
    ∀ a : ℝ, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|}) atTop (𝓝 0) := by
  intro a ha
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [Set.eq_empty_of_isEmpty, thetaCapacity_empty]
    exact tendsto_const_nhds
  obtain ⟨hle, -⟩ := uscRegularization_iSup_eq_of_monotone_ae hu hv hm hae
  obtain ⟨b, hb⟩ := hv.exists_global_upper_bound
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-α)
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr
    omega.isSemipositive
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have hε' : 0 < ε.toReal / 2 := half_pos (ENNReal.toReal_pos hε.ne' htop)
  -- the tail of the first potential
  have hu0 : IsThetaPshPotential α.val (fun x => u 0 x - (b : EReal)) := (hu 0).sub_const b
  have hu00 : (fun x => u 0 x - (b : EReal)) ≤ 0 := fun x =>
    (EReal.sub_le_sub ((hle 0 x).trans (hb x)) le_rfl).trans EReal.sub_self_le_zero
  obtain ⟨B, hB, htail⟩ := exists_reference_tail_small omega hu0 hu00 hε'
  -- the truncation level
  let C : ℝ := (B + 1) / A
  have hC : 0 ≤ C := div_nonneg (by linarith) hA.le
  let q (w : M → EReal) (x : M) : EReal :=
    max (((A⁻¹ : ℝ) : EReal) * (w x - (b : EReal))) ((0 : EReal) - (C : EReal))
  have hq (w : M → EReal) (hw : IsThetaPshPotential α.val w) :
      IsThetaPshPotential omega.form.val (q w) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max
      (normalized_genuine (b := b) omega hA hdom hw) (hzero.sub_const C)
  have hqv0 : q v ≤ 0 := by
    intro x
    refine max_le ?_ ?_
    · refine mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (inv_pos.mpr hA).le) ?_
      exact (EReal.sub_le_sub (hb x) le_rfl).trans EReal.sub_self_le_zero
    · exact EReal.sub_nonpos.mpr (EReal.coe_nonneg.mpr hC)
  have hqlo (w : M → EReal) (x : M) : ((0 : EReal) - (C : EReal)) ≤ q w x := le_max_right _ _
  have hqm : ∀ x, Monotone fun j => q (u j) x := fun x i j hij =>
    max_le_max (normalized_mono hA (hm x hij)) le_rfl
  have hqle : ∀ j x, q (u j) x ≤ q v x := fun j x =>
    max_le_max (normalized_mono hA (hle j x)) le_rfl
  have hqae : ChartTendstoAE (n := n) (fun j => q (u j)) (q v) := fun e => by
    filter_upwards [hae e] with z hz
    exact tendsto_normalized_truncation hA hz
  have hreg := (uscRegularization_iSup_eq_of_monotone_ae (fun j => hq (u j) (hu j)) (hq v hv)
    hqm hqae).2
  have hCsub : (0 : EReal) - (C : EReal) = ((-C : ℝ) : EReal) := by
    rw [zero_sub, EReal.coe_neg]
  have htype : SameSingularityTypeOn (q (u 0)) (q v) univ := by
    refine ⟨⟨C, fun x _ => ?_⟩, ⟨C, fun x _ => ?_⟩⟩
    · calc q (u 0) x ≤ 0 := (hqle 0 x).trans (hqv0 x)
        _ = ((-C : ℝ) : EReal) + (C : EReal) := by rw [← EReal.coe_add]; simp
        _ ≤ q v x + (C : EReal) := by rw [← hCsub]; exact add_le_add_left (hqlo v x) _
    · calc q v x ≤ 0 := hqv0 x
        _ = ((-C : ℝ) : EReal) + (C : EReal) := by rw [← EReal.coe_add]; simp
        _ ≤ q (u 0) x + (C : EReal) := by rw [← hCsub]; exact add_le_add_left (hqlo (u 0) x) _
  have hδ : 0 < A⁻¹ * a := mul_pos (inv_pos.mpr hA) ha
  have hgap := SingularModelIncreasingRegularizedCapacity.tendsto_capacity_canonicalGap_of_monotone_regularized
    omega (fun j => hq (u j) (hu j)) (hq v hv) hqm hqv0 htype hreg hδ
  have hev := (ENNReal.tendsto_nhds_zero.mp hgap) (ENNReal.ofReal (ε.toReal / 2))
    (ENNReal.ofReal_pos.mpr hε')
  filter_upwards [hev] with j hj
  have hsub : {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|} ⊆
      {x | u 0 x - (b : EReal) < ((-B : ℝ) : EReal)} ∪
        {x | A⁻¹ * a < |canonicalERealDiffToReal (q v x) (q (u j) x)|} := by
    rintro x ⟨hujx, hvx, hgapx⟩
    have hujt : u j x ≠ ⊤ := (hu j).1.quasiPlurisubharmonic.ne_top x
    have hvt : v x ≠ ⊤ := hv.1.quasiPlurisubharmonic.ne_top x
    by_cases hcut : ((A⁻¹ : ℝ) : EReal) * (u j x - (b : EReal)) ≤ (0 : EReal) - (C : EReal)
    · left
      change u 0 x - (b : EReal) < ((-B : ℝ) : EReal)
      have h0 : ((A⁻¹ : ℝ) : EReal) * (u 0 x - (b : EReal)) ≤ ((-C : ℝ) : EReal) :=
        hCsub ▸ (normalized_mono hA (hm x (Nat.zero_le j))).trans hcut
      by_cases hu0b : u 0 x = ⊥
      · rw [hu0b, EReal.bot_sub]
        exact EReal.bot_lt_coe _
      have hu0t : u 0 x ≠ ⊤ := (hu 0).1.quasiPlurisubharmonic.ne_top x
      rw [← EReal.coe_toReal hu0t hu0b, ← EReal.coe_sub, ← EReal.coe_mul,
        EReal.coe_le_coe_iff] at h0
      rw [← EReal.coe_toReal hu0t hu0b, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
      have h1 : (u 0 x).toReal - b ≤ -(A * C) := by
        have := mul_le_mul_of_nonneg_left h0 hA.le
        rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
        linarith
      have h2 : A * C = B + 1 := by
        dsimp only [C]
        field_simp
      linarith
    · right
      change A⁻¹ * a < |canonicalERealDiffToReal (q v x) (q (u j) x)|
      have hlt : (0 : EReal) - (C : EReal) < ((A⁻¹ : ℝ) : EReal) * (u j x - (b : EReal)) :=
        lt_of_not_ge hcut
      have hlt' : (0 : EReal) - (C : EReal) < ((A⁻¹ : ℝ) : EReal) * (v x - (b : EReal)) :=
        hlt.trans_le (normalized_mono hA (hle j x))
      have hqj : q (u j) x = ((A⁻¹ : ℝ) : EReal) * (u j x - (b : EReal)) :=
        max_eq_left hlt.le
      have hqv : q v x = ((A⁻¹ : ℝ) : EReal) * (v x - (b : EReal)) := max_eq_left hlt'.le
      rw [hqj, hqv]
      have hr1 : ((A⁻¹ : ℝ) : EReal) * (v x - (b : EReal)) =
          ((A⁻¹ * ((v x).toReal - b) : ℝ) : EReal) := by
        rw [EReal.coe_mul, EReal.coe_sub, EReal.coe_toReal hvt hvx]
      have hr2 : ((A⁻¹ : ℝ) : EReal) * (u j x - (b : EReal)) =
          ((A⁻¹ * ((u j x).toReal - b) : ℝ) : EReal) := by
        rw [EReal.coe_mul, EReal.coe_sub, EReal.coe_toReal hujt hujx]
      rw [hr1, hr2, canonicalDiff_eq_sub_toReal (EReal.coe_ne_top _) (EReal.coe_ne_top _)
        (iff_of_false (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)), EReal.toReal_coe,
        EReal.toReal_coe]
      have he : A⁻¹ * ((v x).toReal - b) - A⁻¹ * ((u j x).toReal - b) =
          A⁻¹ * ((v x).toReal - (u j x).toReal) := by ring
      rw [he, abs_mul, abs_of_pos (inv_pos.mpr hA), abs_sub_comm]
      exact mul_lt_mul_of_pos_left hgapx (inv_pos.mpr hA)
  calc thetaCapacity omega.form (fun _ => 0)
        {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|}
      ≤ thetaCapacity omega.form (fun _ => 0) {x | u 0 x - (b : EReal) < ((-B : ℝ) : EReal)} +
        thetaCapacity omega.form (fun _ => 0)
          {x | A⁻¹ * a < |canonicalERealDiffToReal (q v x) (q (u j) x)|} :=
        (thetaCapacity_mono hsub).trans (thetaCapacity_union_le _ _ _ _)
    _ ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal (ε.toReal / 2) :=
        add_le_add htail.le hj
    _ = ε := by
        rw [← ENNReal.ofReal_add hε'.le hε'.le, add_halves, ENNReal.ofReal_toReal htop]

end SGPT.NPP.CapacityConvergence
