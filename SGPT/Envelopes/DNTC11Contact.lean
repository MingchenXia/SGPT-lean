import SGPT.Envelopes.DNTC11Measure
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Di Nezza–Trapani contact formula for obstacles with bounded complex Hessian

Lane S53 (`claude-dnt-c11`).  Let `X` be a compact complex manifold of dimension `n` with a Kähler
form `ω`, `θ` a closed real `(1,1)`-form, `φ ∈ PSH(X, θ)` and `f` a continuous function with
bounded complex Hessian (`HasBoundedComplexHessian`) with `φ ≤ f`; `E = {φ = f}`.

* `diagonalPotentialMeasure_restrict_contact_le_of_psh`, `..._eq_of_psh`: if `f` is itself
  `θ`-psh, `𝟙_E θ_φⁿ = 𝟙_E θ_fⁿ` (the inequality `≥` by the local mollifier argument of
  `DNTC11LocalContact` and the density formula; `≤` is the maximum principle `lma:lorMAineqe`).
* `diagonalPotentialMeasure_add_smul_toReal_eq_sum`: `t ↦ ⟨(θ + tω + ddᶜφ)ⁿ⟩(A)` is a polynomial
  of degree `≤ n` on `t > 0` with constant term `⟨(θ + ddᶜφ)ⁿ⟩(A)` (multilinearity of
  non-pluripolar products in the background forms).
* `c11TopMeasure`: the Monge–Ampère measure `θ_fⁿ` of `f` (positive part of the signed measure),
  defined by its density `(θ + ddᶜf)ⁿ/ωⁿ`, the value at `t = 0` of the polynomial
  `t ↦ (θ + tω + ddᶜf)ⁿ/ωⁿ` read off from the genuine Monge–Ampère measures `⟨(θ + tω + ddᶜf)ⁿ⟩`
  of the `(θ + tω)`-psh function `f` at `t = T, …, T + n` (Lagrange interpolation).
* `diagonalPotentialMeasure_restrict_contact_eq` (**the contact formula**, book `thm:DNTcontact`,
  diagonal case, for obstacles with bounded complex Hessian): `𝟙_E θ_φⁿ = 𝟙_E θ_fⁿ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The contact set of a `θ`-psh function below a continuous obstacle is closed. -/
theorem isClosed_contact_of_continuous {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) {f : M → ℝ} (hf : Continuous f)
    (hle : ∀ x, u x ≤ (f x : EReal)) : IsClosed {x | u x = (f x : EReal)} := by
  have husc : UpperSemicontinuous u := hu.quasiPlurisubharmonic.upperSemicontinuous
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
  have hlt : u x < (f x : EReal) := lt_of_le_of_ne (hle x) hx
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have h1 : ∀ᶠ y in 𝓝 x, u y < (c : EReal) := husc x _ hc1
  have h2 : ∀ᶠ y in 𝓝 x, c < f y :=
    (hf.continuousAt).eventually (lt_mem_nhds (EReal.coe_lt_coe_iff.mp hc2))
  filter_upwards [h1, h2] with y hy1 hy2
  exact fun h => (lt_irrefl (u y)) (hy1.trans ((EReal.coe_lt_coe_iff.mpr hy2).trans_eq h.symm))

section Measures

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### The contact formula for plurisubharmonic obstacles -/

/-- **The contact bound "`≥`" for a `θ`-psh obstacle with bounded complex Hessian**:
`𝟙_E θ_fⁿ ≤ θ_φⁿ`. -/
theorem diagonalPotentialMeasure_restrict_contact_le_of_psh (hn : 0 < n)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (hfpsh : IsThetaPshPotential θ.val (fun x => (f x : EReal)))
    (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh).restrict
        {x | u x = (f x : EReal)} ≤ diagonalPotentialMeasure θ u hu := by
  set E : Set M := {x | u x = (f x : EReal)} with hE
  have hEc : IsClosed E := isClosed_contact_of_continuous hu.1 hf.1 hle
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA]
  refine le_trans ?_ (measure_mono (inter_subset_left : A ∩ E ⊆ A))
  refine SGPT.Okounkov.TranscendentalWN.le_of_local_le hEc.isCompact ?_
    (hA.inter hEc.measurableSet) inter_subset_right
  intro x hx
  set e := complexChartAt (n := n) x with he
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hu.1 e (e.val x) hz₀
  have hWo : IsOpen W := hρ.1
  have hWt : W ⊆ e.val.target := hρ.2.1
  let Ω : Opens (ComplexModel n) := ⟨W, hWo⟩
  obtain ⟨h, hh⟩ := hf.exists_density_add e hWo hWt hρ.2.2.1
  set q : ComplexModel n → ℝ := fun y => f (e.val.symm y) + ρ y with hqdef
  set U : ComplexModel n → EReal := fun y => chartFunction u e y + (ρ y : EReal) with hUdef
  have hU : PlurisubharmonicOn U Ω := hpsh
  have hUq : ∀ y ∈ Ω, U y ≤ (q y : EReal) := by
    intro y _
    simp only [hUdef, hqdef, chartFunction, EReal.coe_add]
    exact add_le_add_left (hle _) _
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo (e.val x) hz₀W
  set R := ε / 6 with hR
  have hR0 : 0 < R := by positivity
  have hball : closedBall (e.val x) (5 * R) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hεW
  refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val x) R,
    e.val.isOpen_inter_preimage isOpen_ball, ⟨hxe, mem_ball_self hR0⟩, ?_⟩
  intro S hS hSN
  have hSsrc : S ⊆ e.val.source := fun y hy => (hSN hy).1.1
  set T : Set (ComplexModel n) := e.val '' S with hT
  have hST : S = e.val.symm '' T := (e.val.symm_image_image_of_subset_source hSsrc).symm
  have hTball : T ⊆ ball (e.val x) R := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hSN hy).1.2
  have hTΩ : T ⊆ Ω := hTball.trans (ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hball))
  have hTC : T ⊆ {z | z ∈ Ω ∧ U z = (q z : EReal)} ∩ ball (e.val x) R := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨hTΩ ⟨y, hy, rfl⟩, ?_⟩, hTball ⟨y, hy, rfl⟩⟩
    have hyE : u y = (f y : EReal) := (hSN hy).2
    simp only [hUdef, hqdef, chartFunction, e.val.left_inv (hSsrc hy), EReal.coe_add, hyE]
  rw [hST, diagonalPotentialMeasure_image_eq_density hn θ hfpsh hρ hh hTΩ,
    diagonalPotentialMeasure_image_eq_truncation hn θ hu hρ hTΩ]
  exact truncationLimitMeasure_contact_ge hn hU hh hUq hR0 hball hTC

/-- **The contact formula for a `θ`-psh obstacle with bounded complex Hessian**:
`𝟙_E θ_φⁿ = 𝟙_E θ_fⁿ`. -/
theorem diagonalPotentialMeasure_restrict_contact_eq_of_psh (w : KahlerBackground n M) (hn : 0 < n)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (hfpsh : IsThetaPshPotential θ.val (fun x => (f x : EReal)))
    (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh).restrict
        {x | u x = (f x : EReal)} := by
  refine le_antisymm ?_ ?_
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact MaxMassDecomposition.contact_measure_le w hu hfpsh hle hA
  · calc (diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh).restrict
          {x | u x = (f x : EReal)}
        = ((diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh).restrict
            {x | u x = (f x : EReal)}).restrict {x | u x = (f x : EReal)} :=
          (Measure.restrict_restrict_of_subset subset_rfl).symm
      _ ≤ (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} :=
          Measure.restrict_mono subset_rfl
            (diagonalPotentialMeasure_restrict_contact_le_of_psh hn θ hu hf hfpsh hle)

/-! ### Multilinearity in the background: the polynomial `t ↦ ⟨(θ + tω + ddᶜu)ⁿ⟩(A)` -/

/-- Slot forms for the expansion: `ω` on `P`, `θ + tω` on `S` (off `P`), `θ` elsewhere. -/
def slotForm (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) (S P : Finset (Fin n))
    (t : ℝ) (i : Fin n) : ClosedRealOneOneForm n M :=
  if i ∈ P then w.form else if i ∈ S then θ + t • w.form else θ

/-- Slot potentials for the expansion: `0` on `P`, `u` elsewhere. -/
def slotPot (u : M → EReal) (P : Finset (Fin n)) (i : Fin n) : M → EReal :=
  if i ∈ P then fun _ => 0 else u

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem slot_thetaPlurisubharmonic (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ.val u) (S P : Finset (Fin n)) {t : ℝ}
    (ht : 0 ≤ t) (i : Fin n) :
    ThetaPlurisubharmonic (slotForm w θ S P t i).val (slotPot u P i) := by
  unfold slotForm slotPot
  split_ifs
  · exact ((Pending.LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  · exact NefBoundedMixedMass.thetaPlurisubharmonic_add_of_isSemipositive hu
      (NefBoundedMixedMass.isSemipositive_smul w.isSemipositive ht)
  · exact hu

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem slotForm_empty_eq (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (P : Finset (Fin n)) (t s : ℝ) : slotForm w θ ∅ P t = slotForm w θ ∅ P s := by
  funext i
  simp [slotForm]

/-- **Expansion in the background.**  For `t > 0` and disjoint `S, P`,
`μ(S bumped by tω, P replaced by (ω, 0)) = ∑_{S' ⊆ S} tⁱˢ'ⁱ μ(P ∪ S' replaced by (ω, 0))`. -/
theorem globalMixedMeasure_slot_expand (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {t : ℝ} (ht : 0 < t) :
    ∀ S P : Finset (Fin n), Disjoint S P →
      globalMixedMeasure (slotForm w θ S P t) (slotPot u P)
          (slot_thetaPlurisubharmonic w θ hu.1 S P ht.le) =
        ∑ S' ∈ S.powerset, ENNReal.ofReal t ^ S'.card •
          globalMixedMeasure (slotForm w θ ∅ (P ∪ S') t) (slotPot u (P ∪ S'))
            (slot_thetaPlurisubharmonic w θ hu.1 ∅ (P ∪ S') ht.le) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro P _
      simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
        one_smul, Finset.union_empty]
  | insert j S hj ih =>
      intro P hdisj
      have hjP : j ∉ P := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self j S)
      have hSP : Disjoint S P := Finset.disjoint_of_subset_left (Finset.subset_insert j S) hdisj
      have hSjP : Disjoint S (insert j P) := by
        rw [Finset.disjoint_insert_right]
        exact ⟨hj, hSP⟩
      set θs := slotForm w θ S P t with hθs
      set us := slotPot u P with hus
      have hθsj : θs j = θ := by simp [hθs, slotForm, hjP, hj]
      have husj : us j = u := by simp [hus, slotPot, hjP]
      have e1 : slotForm w θ (insert j S) P t = Function.update θs j (θs j + t • w.form) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [slotForm, hjP, hθsj]
        · simp [hθs, slotForm, hi]
      have e2 : Function.update θs j w.form = slotForm w θ S (insert j P) t := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [slotForm]
        · simp [hθs, slotForm, hi]
      have e3 : Function.update us j (fun _ => (0 : EReal)) = slotPot u (insert j P) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [slotPot]
        · simp [hus, slotPot, hi]
      have hpsh := slot_thetaPlurisubharmonic w θ hu.1 S P ht.le
      have hnd : IsThetaPshPotential (θs j).val (us j) := by rw [hθsj, husj]; exact hu
      have hu' : ∀ i, ThetaPlurisubharmonic (Function.update θs j (θs j + t • w.form) i).val
          (us i) := by
        rw [← e1]; exact slot_thetaPlurisubharmonic w θ hu.1 (insert j S) P ht.le
      have h0 : ∀ i, ThetaPlurisubharmonic (Function.update θs j w.form i).val
          (Function.update us j (fun _ => (0 : EReal)) i) := by
        rw [e2, e3]; exact slot_thetaPlurisubharmonic w θ hu.1 S (insert j P) ht.le
      have hinc := NefBoundedMixedMass.globalMixedMeasure_update_add_smul_eq j ht hpsh hnd hu' h0
      rw [AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples e1 rfl _ hu', hinc,
        AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples e2 e3 h0
          (slot_thetaPlurisubharmonic w θ hu.1 S (insert j P) ht.le),
        ih P hSP, ih (insert j P) hSjP, Finset.powerset_insert,
        Finset.sum_union (Finset.disjoint_left.mpr fun A hA hA' => by
          obtain ⟨B, -, rfl⟩ := Finset.mem_image.mp hA'
          exact hj (Finset.mem_powerset.mp hA (Finset.mem_insert_self j B))),
        Finset.sum_image (fun A hA B hB hAB => by
          have hjA : j ∉ A := fun h => hj (Finset.mem_powerset.mp hA h)
          have hjB : j ∉ B := fun h => hj (Finset.mem_powerset.mp hB h)
          rw [← Finset.erase_insert hjA, ← Finset.erase_insert hjB, hAB]),
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun A hA => ?_
      have hjA : j ∉ A := fun h => hj (Finset.mem_powerset.mp hA h)
      have hset : P ∪ insert j A = insert j P ∪ A := by
        ext i
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [Finset.card_insert_of_notMem hjA, pow_succ, mul_comm, mul_smul,
        AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples
          (congrArg (fun Q => slotForm w θ ∅ Q t) hset)
          (congrArg (fun Q => slotPot u Q) hset) _
          (slot_thetaPlurisubharmonic w θ hu.1 ∅ (insert j P ∪ A) ht.le)]

/-- **The polynomial in the background**: for `t > 0`,
`⟨(θ + tω + ddᶜu)ⁿ⟩(A) = ∑_{S ⊆ {1,…,n}} t^{|S|} a_S` with `a_S = ⟨(θ + ddᶜu)^{n-|S|} ∧ ω^{|S|}⟩(A)`;
in particular `a_∅ = ⟨(θ + ddᶜu)ⁿ⟩(A)`. -/
theorem diagonalPotentialMeasure_add_smul_toReal_eq_sum (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {t : ℝ}
    (ht : 0 < t) (hut : IsThetaPshPotential (θ + t • w.form).val u) (A : Set M) :
    (diagonalPotentialMeasure (θ + t • w.form) u hut A).toReal =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, t ^ S.card *
        (globalMixedMeasure (slotForm w θ ∅ S 1) (slotPot u S)
          (slot_thetaPlurisubharmonic w θ hu.1 ∅ S zero_le_one) A).toReal := by
  classical
  have e1 : (fun _ : Fin n => θ + t • w.form) = slotForm w θ Finset.univ ∅ t := by
    funext i
    simp [slotForm]
  have e2 : (fun _ : Fin n => u) = slotPot u ∅ := by
    funext i
    simp [slotPot]
  have hexp := globalMixedMeasure_slot_expand w θ hu ht Finset.univ ∅ (Finset.disjoint_empty_right _)
  rw [diagonalPotentialMeasure, AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples e1 e2 _
    (slot_thetaPlurisubharmonic w θ hu.1 Finset.univ ∅ ht.le), hexp, Measure.coe_finsetSum,
    Finset.sum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun S _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal ht.le,
      AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples
        (by rw [Finset.empty_union, slotForm_empty_eq w θ S t 1])
        (by rw [Finset.empty_union]) _ (slot_thetaPlurisubharmonic w θ hu.1 ∅ S zero_le_one)]
  · intro S _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top w _ A).ne

omit [BorelSpace M] in
theorem slotMeasure_empty (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) (A : Set M) :
    globalMixedMeasure (slotForm w θ ∅ ∅ 1) (slotPot u ∅)
        (slot_thetaPlurisubharmonic w θ hu.1 ∅ ∅ zero_le_one) A =
      diagonalPotentialMeasure θ u hu A := by
  classical
  rw [diagonalPotentialMeasure, AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples
    (show slotForm w θ ∅ ∅ 1 = fun _ => θ by funext i; simp [slotForm])
    (show slotPot u ∅ = fun _ => u by funext i; simp [slotPot]) _ (fun _ => hu.1)]

end Measures

/-! ### Lagrange interpolation at `0` -/

/-- The nodes `T, T + 1, …, T + n`. -/
def lagNode (T : ℝ) (k : Fin (n + 1)) : ℝ := T + k

/-- The Lagrange weights for evaluation at `0` at the nodes `T, …, T + n`. -/
def lagWeight (T : ℝ) (k : Fin (n + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (lagNode T) k).eval 0

theorem lagNode_injOn (T : ℝ) : Set.InjOn (lagNode (n := n) T) (Finset.univ : Finset (Fin (n + 1))) := by
  intro a _ b _ hab
  simp only [lagNode, add_right_inj, Nat.cast_inj] at hab
  exact Fin.ext hab

/-- Evaluation at `0` of a real polynomial of degree `≤ n` from its values at the nodes. -/
theorem eval_zero_eq_sum_lagWeight (T : ℝ) {p : Polynomial ℝ} (hp : p.natDegree ≤ n) :
    p.eval 0 = ∑ k : Fin (n + 1), lagWeight T k * p.eval (lagNode T k) := by
  have hdeg : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self n)
  conv_lhs => rw [Lagrange.eq_interpolate (lagNode_injOn T) hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, lagWeight, mul_comm]

/-- `∑_k L_k t_k^j = 0^j` for `j ≤ n`. -/
theorem sum_lagWeight_mul_pow (T : ℝ) {j : ℕ} (hj : j ≤ n) :
    ∑ k : Fin (n + 1), lagWeight T k * lagNode T k ^ j = (0 : ℝ) ^ j := by
  have h := eval_zero_eq_sum_lagWeight (n := n) T (p := Polynomial.X ^ j)
    (by rw [Polynomial.natDegree_X_pow]; exact hj)
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
  exact h.symm

/-- **Extrapolation to `0`** of `∑_S t^{|S|} a_S` from the nodes. -/
theorem sum_lagWeight_mul_sum_pow (T : ℝ) (a : Finset (Fin n) → ℝ) :
    ∑ k : Fin (n + 1), lagWeight T k *
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, lagNode T k ^ S.card * a S) = a ∅ := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∑ k : Fin (n + 1), lagWeight T k * (lagNode T k ^ S.card * a S) = (0 : ℝ) ^ S.card * a S := by
    intro S _
    have hS : S.card ≤ n := (Finset.card_le_univ S).trans (by simp)
    rw [← sum_lagWeight_mul_pow (n := n) T hS, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_eq_single ∅]
  · simp
  · intro S _ hS
    rw [zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)), zero_mul]
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h

end SGPT.Envelopes.DNTC11
