import SGPT.PSH.HermitianLocalPositivity
import SGPT.PSH.HermitianFreezing
import SGPT.PSH.Supremum
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

/-!
# Maxima and bounded upper envelopes for nonclosed backgrounds

The smooth correction of a background is chosen before all potentials.
Freezing its coefficients makes the correction error arbitrarily small;
the sharp full-current criterion then preserves the original background.
No local exact potential of that background is used.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Hermitian

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- One genuine local correction, with arbitrarily small Hessian error,
works simultaneously for the entire background-relative PSH class. -/
theorem exists_common_approximate_correction
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
      (q : ComplexModel (m + 1) → ℝ), z ∈ W ∧ ContDiffOn ℝ ∞ q W ∧
      (∀ u : M → EReal, IsFormPSH θ u →
        PlurisubharmonicOn (fun y => chartFunction u e y + (q y : EReal)) W) ∧
      ∀ y ∈ W, ∀ v : ComplexModel (m + 1), smoothDDC q y ![v, Complex.I • v] ≤
        θ.coeff e y ![v, Complex.I • v] + ε * ‖v‖ ^ 2 := by
  obtain ⟨W, q, hzW, hW, hsub, hq, hbounds⟩ :=
    HermitianFreezing.exists_local_approximate_potential e.val.open_target
      (θ.coeff e) (θ.smooth e) (hθ₁ e) hz hε
  let V : Opens (ComplexModel (m + 1)) := ⟨W, hW⟩
  refine ⟨V, hsub, q, hzW, hq, ?_, fun y hy v => (hbounds y hy v).2⟩
  intro u hu
  exact chart_add_smooth_plurisubharmonicOn hθ₁ hu e hsub hq
    (fun y hy v => (hbounds y hy v).1)

private theorem max_add_coe (a b : EReal) (r : ℝ) :
    max a b + (r : EReal) = max (a + (r : EReal)) (b + (r : EReal)) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,
      max_eq_right ((EReal.addLECancellable_coe r).add_le_add_iff_right.mpr h)]
  · rw [max_eq_left h,
      max_eq_left ((EReal.addLECancellable_coe r).add_le_add_iff_right.mpr h)]

private theorem quasiPsh_of_localCorrections (u : M → EReal)
    (hn : LocallyNondegenerate u)
    (hlocal : ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
      ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
        (q : ComplexModel (m + 1) → ℝ), z ∈ W ∧ ContDiffOn ℝ ∞ q W ∧
        PlurisubharmonicOn (fun y => chartFunction u e y + (q y : EReal)) W) :
    IsGlobalQuasiPshPotential (n := m + 1) u := by
  refine ⟨?_, hn⟩
  intro e z hz
  obtain ⟨W, _hW, q, hzW, hq, hp⟩ := hlocal e z hz
  refine ⟨fun y => chartFunction u e y + (q y : EReal), fun y => -q y,
    hp z hzW, ?_, ?_⟩
  · filter_upwards [W.isOpen.mem_nhds hzW] with y hy
    exact ((hq.neg) y hy).contDiffAt (W.isOpen.mem_nhds hy)
  · exact Eventually.of_forall fun y => by
      dsimp only
      rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/-- A finite maximum retains the exact original background inequality,
even when that smooth real `(1,1)`-form is not closed. -/
theorem isFormPSH_max
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    {u v : M → EReal} (hu : IsFormPSH θ u) (hv : IsFormPSH θ v) :
    IsFormPSH θ (fun x => max (u x) (v x)) := by
  let w : M → EReal := fun x => max (u x) (v x)
  have hlocal : ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
      ∀ ε : ℝ, 0 < ε → ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
        (q : ComplexModel (m + 1) → ℝ), z ∈ W ∧ ContDiffOn ℝ ∞ q W ∧
        PlurisubharmonicOn (fun y => chartFunction w e y + (q y : EReal)) W ∧
        ∀ y ∈ W, ∀ a : ComplexModel (m + 1), smoothDDC q y ![a, Complex.I • a] ≤
          θ.coeff e y ![a, Complex.I • a] + ε * ‖a‖ ^ 2 := by
    intro e z hz ε hε
    obtain ⟨W, hW, q, hzW, hq, hp, hbound⟩ :=
      exists_common_approximate_correction θ hθ₁ e hz hε
    refine ⟨W, hW, q, hzW, hq, ?_, hbound⟩
    intro y hy
    apply (((hp u hu).max (hp v hv)) y hy).congr
    exact Eventually.of_forall fun a => (max_add_coe
      (chartFunction u e a) (chartFunction v e a) (q a)).symm
  have hn : LocallyNondegenerate w := by
    intro x O hO hx
    obtain ⟨y, hy, huFin⟩ := hu.quasiPshPotential.2 x O hO hx
    refine ⟨y, hy, ?_⟩
    intro hw
    exact huFin (le_bot_iff.mp (hw ▸ (le_max_left (u y) (v y))))
  have hw := quasiPsh_of_localCorrections w hn (fun e z hz => by
    obtain ⟨W, hW, q, hzW, hq, hp, _⟩ := hlocal e z hz 1 zero_lt_one
    exact ⟨W, hW, q, hzW, hq, hp⟩)
  exact isFormPSH_of_approximate_local_psh θ hθ₁ w hw hlocal

theorem IsHermitianPSH.max {omega : Background (m + 1) M}
    {u v : M → EReal} (hu : IsHermitianPSH omega u) (hv : IsHermitianPSH omega v) :
    IsHermitianPSH omega (fun x => max (u x) (v x)) :=
  isFormPSH_max omega.form omega.isTypeOneOne hu hv

omit [IsComplexManifold (m + 1) M] in
private theorem corrected_uscSup_psh {ι : Type*} [Nonempty ι]
    (u : ι → M → EReal) (C : ℝ) (hupper : ∀ i x, u i x ≤ (C : EReal))
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q W)
    (hp : ∀ i, PlurisubharmonicOn (fun y => chartFunction (u i) e y + (q y : EReal)) W) :
    PlurisubharmonicOn (fun y =>
      chartFunction (uscRegularization (fun x => ⨆ i, u i x)) e y + (q y : EReal)) W := by
  let f : ι → ComplexModel (m + 1) → EReal :=
    fun i y => chartFunction (u i) e y + (q y : EReal)
  have hb : FirstPass.LocallyUniformlyBoundedAbove (range f) W := by
    intro z hz
    have hc : ContinuousAt q z := hq.continuousOn.continuousAt (W.isOpen.mem_nhds hz)
    have hn : {y | q y < q z + 1} ∈ 𝓝 z :=
      hc.eventually (isOpen_Iio.mem_nhds (show q z < q z + 1 by linarith))
    refine ⟨{y | q y < q z + 1}, mem_nhdsWithin_of_mem_nhds hn,
      C + (q z + 1), ?_⟩
    rintro g ⟨i, rfl⟩ y hy
    change u i (e.val.symm y) + (q y : EReal) ≤ ((C + (q z + 1) : ℝ) : EReal)
    rw [EReal.coe_add]
    exact add_le_add (hupper i (e.val.symm y)) (EReal.coe_le_coe_iff.mpr hy.1.le)
  have hpsh := plurisubharmonicOn_uscRegularization_sSup W.isOpen (range_nonempty f)
    (fun g hg => by obtain ⟨i, rfl⟩ := hg; exact hp i) hb
  rw [SGPT.PSH.sSup_range_eq f] at hpsh
  have hsup : (fun y => ⨆ i, f i y) =
      (fun y => chartFunction (fun x => ⨆ i, u i x) e y + (q y : EReal)) := by
    funext y
    exact iSup_add_coe (fun i => chartFunction (u i) e y) (q y)
  rw [hsup] at hpsh
  intro z hz
  apply (hpsh z hz).congr
  filter_upwards [W.isOpen.mem_nhds hz] with y hy
  rw [uscRegularization_add_coe_continuousAt_apply _
    (hq.continuousOn.continuousAt (W.isOpen.mem_nhds hy)),
    uscRegularization_chartFunction_apply _ e (hW hy)]

/-- A uniformly bounded nonempty family has an actual background-relative
PSH regularized upper envelope, for a possibly nonclosed real `(1,1)`-form. -/
theorem isFormPSH_uscRegularization_iSup_of_uniform_bound {ι : Type*} [Nonempty ι]
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    (u : ι → M → EReal) (hu : ∀ i, IsFormPSH θ (u i))
    (C : ℝ) (hupper : ∀ i x, u i x ≤ (C : EReal)) :
    IsFormPSH θ (uscRegularization (fun x => ⨆ i, u i x)) := by
  let w := uscRegularization (fun x => ⨆ i, u i x)
  have hlocal : ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
      ∀ ε : ℝ, 0 < ε → ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
        (q : ComplexModel (m + 1) → ℝ), z ∈ W ∧ ContDiffOn ℝ ∞ q W ∧
        PlurisubharmonicOn (fun y => chartFunction w e y + (q y : EReal)) W ∧
        ∀ y ∈ W, ∀ a : ComplexModel (m + 1), smoothDDC q y ![a, Complex.I • a] ≤
          θ.coeff e y ![a, Complex.I • a] + ε * ‖a‖ ^ 2 := by
    intro e z hz ε hε
    obtain ⟨W, hW, q, hzW, hq, hp, hbound⟩ :=
      exists_common_approximate_correction θ hθ₁ e hz hε
    exact ⟨W, hW, q, hzW, hq,
      corrected_uscSup_psh u C hupper e hW hq (fun i => hp (u i) (hu i)), hbound⟩
  have hn : LocallyNondegenerate w := by
    intro x O hO hx
    let i : ι := Classical.arbitrary ι
    obtain ⟨y, hy, hfin⟩ := (hu i).quasiPshPotential.2 x O hO hx
    have hle : u i y ≤ w y := (le_iSup (fun j => u j y) i).trans
      (le_uscRegularization (fun z => ⨆ j, u j z) y)
    exact ⟨y, hy, fun hw => hfin (le_bot_iff.mp (hw ▸ hle))⟩
  have hw := quasiPsh_of_localCorrections w hn (fun e z hz => by
    obtain ⟨W, hW, q, hzW, hq, hp, _⟩ := hlocal e z hz 1 zero_lt_one
    exact ⟨W, hW, q, hzW, hq, hp⟩)
  exact isFormPSH_of_approximate_local_psh θ hθ₁ w hw hlocal

/-- Bounded upper envelopes preserve the full Hermitian PSH class. -/
theorem isHermitianPSH_uscRegularization_iSup_of_uniform_bound
    {ι : Type*} [Nonempty ι] (omega : Background (m + 1) M)
    (u : ι → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (C : ℝ) (hupper : ∀ i x, u i x ≤ (C : EReal)) :
    IsHermitianPSH omega (uscRegularization (fun x => ⨆ i, u i x)) :=
  isFormPSH_uscRegularization_iSup_of_uniform_bound omega.form omega.isTypeOneOne u hu C hupper

end SGPT.PSH.Hermitian
