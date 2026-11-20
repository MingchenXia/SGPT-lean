import SGPT.Envelopes.RelativeCYMeasure
import SGPT.Envelopes.RelativeMAAubinYau
import SGPT.NPP.CapacityConvergenceGlobal
import SGPT.NPP.CapacityConvergenceMonotone
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.IncreasingDiagonalContinuity
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

/-!
# Lower bounds of Monge–Ampère measures pass to tail limits

Input for the relative Calabi–Yau theorem (source `thm:Yau_rel`), following Xia,
*Foundations of pluripotential theory*, `lem:nonpluripolar-measure-lower-bound-lone-limit`.

Let `φ` be a model potential, `w_k ≤ φ` be `θ`-psh, `ν` a finite measure charging no
pluripolar set and `θ_{w_k}^n ≥ f_k ν`. Put `g_j = inf_{k ≥ j} f_k`, the tail envelopes
`a_j = (sup_{k ≥ j} w_k)^*` and their decreasing limit `A = inf_j a_j`. Then
`θ_A^n ≥ (liminf_k f_k) ν` (`withDensity_liminf_le_tailLimit`).

* `withDensity_le_max`: a common lower bound passes to the maximum of two potentials
  (contact decomposition `θ_{max(u,v)}^n ≥ 1_{v ≤ u} θ_u^n + 1_{u < v} θ_v^n`);
* `withDensity_le_tailEnv`: the finite maxima `max(w_j, …, w_{j+l})` increase to a function
  whose regularization is `a_j`, their measures converge weakly to `θ_{a_j}^n` (TN
  `IncreasingDiagonalContinuity`), and weak limits preserve the fixed lower bound
  (`RelativeCYMeasure`);
* `restrict_le_of_antitone`: for a decreasing sequence `a_j ≤ φ` with limit `A` and a fixed
  lower bound `σ ≤ θ_{a_j}^n`, the truncations `max(a_j, φ - C) ∈ E^∞(X, θ; φ)` decrease to
  `max(A, φ - C)`, their measures converge weakly (`thm:semicon`, as
  `SGPT.NPP.CapacityConvergence.tendsto_integral_moving`), and plurifine locality of the
  maximum (TN `GlobalMaxLocality`) twice gives `σ ≤ θ_A^n` on `{A > φ - C}`.

FPT's lemma is stated for an `L¹` limit `q` of the `w_k`; the tail limit `A` dominates `q`
and equals it, but we never need this: in the existence proof `A` itself is the solution.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeCY

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

/-! ### Elementary extended-real facts -/

theorem ereal_add_neg_add_cancel (e : EReal) (c : ℝ) :
    e + ((-c : ℝ) : EReal) + (c : EReal) = e := by
  induction e using EReal.rec with
  | bot => simp
  | top => rw [EReal.top_add_coe, EReal.top_add_coe]
  | coe a => rw [← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

theorem exists_nat_add_neg_lt {a b : EReal} (ha : a ≠ ⊥) (hat : a ≠ ⊤) (hb : b ≠ ⊤) :
    ∃ C : ℕ, b + ((-(C : ℝ) : ℝ) : EReal) < a := by
  induction b using EReal.rec with
  | bot => exact ⟨0, by rw [EReal.bot_add]; exact Ne.bot_lt ha⟩
  | top => exact absurd rfl hb
  | coe r =>
    obtain ⟨C, hC⟩ := exists_nat_gt (r - a.toReal)
    refine ⟨C, ?_⟩
    rw [← EReal.coe_toReal hat ha, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith

theorem ereal_add_neg_le {e : EReal} {c : ℝ} (hc : 0 ≤ c) : e + ((-c : ℝ) : EReal) ≤ e := by
  calc e + ((-c : ℝ) : EReal) ≤ e + 0 :=
        add_le_add le_rfl (EReal.coe_nonpos.mpr (neg_nonpos.mpr hc))
    _ = e := add_zero e

/-! ### Tail maxima and tail envelopes -/

/-- The finite tail maxima `max(w_j, w_{j+1}, …, w_{j+l})`. -/
def tailMax {X : Type*} (w : ℕ → X → EReal) (j : ℕ) : ℕ → X → EReal
  | 0 => w j
  | l + 1 => fun x => max (tailMax w j l x) (w (l + 1 + j) x)

/-- The tail envelope `a_j = (sup_{k ≥ j} w_k)^*`. -/
def tailEnv {X : Type*} [TopologicalSpace X] (w : ℕ → X → EReal) (j : ℕ) : X → EReal :=
  uscRegularization (⨆ k, w (k + j))

/-- The decreasing limit `A = inf_j a_j` of the tail envelopes. -/
def tailLimit {X : Type*} [TopologicalSpace X] (w : ℕ → X → EReal) : X → EReal :=
  fun x => ⨅ j, tailEnv w j x

theorem tailMax_succ {X : Type*} (w : ℕ → X → EReal) (j l : ℕ) :
    tailMax w j (l + 1) = fun x => max (tailMax w j l x) (w (l + 1 + j) x) := rfl

theorem tailMax_monotone {X : Type*} (w : ℕ → X → EReal) (j : ℕ) : Monotone (tailMax w j) :=
  monotone_nat_of_le_succ fun _ _ => le_max_left _ _

theorem le_tailMax {X : Type*} (w : ℕ → X → EReal) (j : ℕ) :
    ∀ {k l : ℕ}, k ≤ l → w (k + j) ≤ tailMax w j l := by
  intro k l hkl
  induction l with
  | zero =>
    rw [Nat.le_zero.mp hkl]
    simp only [zero_add]
    exact le_rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (tailMax_monotone w j (Nat.le_succ l))
    · rw [le_antisymm hkl h]
      intro x
      exact le_max_right _ _

theorem tailMax_le_iSup {X : Type*} (w : ℕ → X → EReal) (j : ℕ) :
    ∀ l : ℕ, tailMax w j l ≤ ⨆ k, w (k + j) := by
  intro l
  induction l with
  | zero => exact le_iSup_of_le 0 (by simp only [zero_add]; exact le_rfl)
  | succ l ih =>
    intro x
    rw [tailMax_succ]
    exact max_le (ih x) (by simpa only [iSup_apply] using le_iSup (fun k => w (k + j) x) (l + 1))

theorem iSup_tailMax {X : Type*} (w : ℕ → X → EReal) (j : ℕ) :
    (⨆ l, tailMax w j l) = ⨆ k, w (k + j) :=
  le_antisymm (iSup_le (tailMax_le_iSup w j)) (iSup_le fun k => le_iSup_of_le k (le_tailMax w j le_rfl))

theorem tailEnv_antitone {X : Type*} [TopologicalSpace X] (w : ℕ → X → EReal) (x : X) :
    Antitone fun j => tailEnv w j x := by
  refine antitone_nat_of_succ_le fun j => ?_
  refine uscRegularization_mono (iSup_le fun k => ?_) x
  rw [show k + (j + 1) = (k + 1) + j by omega]
  exact le_iSup (fun k => w (k + j)) (k + 1)

theorem tailLimit_le_tailEnv {X : Type*} [TopologicalSpace X] (w : ℕ → X → EReal) (j : ℕ) :
    tailLimit w ≤ tailEnv w j := fun x => iInf_le (fun j => tailEnv w j x) j

theorem le_tailEnv {X : Type*} [TopologicalSpace X] (w : ℕ → X → EReal) {j k : ℕ} (hjk : j ≤ k) :
    w k ≤ tailEnv w j := by
  intro x
  refine le_trans ?_ (le_uscRegularization _ x)
  have : k = (k - j) + j := by omega
  rw [this]
  simpa only [iSup_apply] using le_iSup (fun k' => w (k' + j) x) (k - j)

theorem tailEnv_le {X : Type*} [TopologicalSpace X] {w : ℕ → X → EReal} {ψ : X → EReal}
    (hψ : UpperSemicontinuous ψ) (hw : ∀ k, w k ≤ ψ) (j : ℕ) : tailEnv w j ≤ ψ :=
  uscRegularization_le hψ (iSup_le fun k => hw (k + j))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem isThetaPshPotential_tailMax {w : ℕ → M → EReal}
    (hw : ∀ k, IsThetaPshPotential θ.val (w k)) (j : ℕ) :
    ∀ l, IsThetaPshPotential θ.val (tailMax w j l) := by
  intro l
  induction l with
  | zero => exact hw j
  | succ l ih => exact SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max ih (hw _)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem isThetaPshPotential_tailEnv {w : ℕ → M → EReal}
    (hw : ∀ k, IsThetaPshPotential θ.val (w k)) {b : ℝ} (hb : ∀ k x, w k x ≤ (b : EReal))
    (j : ℕ) : IsThetaPshPotential θ.val (tailEnv w j) :=
  NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le
    (fun k => hw (k + j)) (fun k x => hb (k + j) x)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem isThetaPshPotential_tailLimit [ConnectedSpace M] {w : ℕ → M → EReal}
    (hw : ∀ k, IsThetaPshPotential θ.val (w k)) {b : ℝ} (hb : ∀ k x, w k x ≤ (b : EReal))
    (hne : ∃ x, tailLimit w x ≠ ⊥) : IsThetaPshPotential θ.val (tailLimit w) :=
  ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
    (ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
      (fun j => (isThetaPshPotential_tailEnv hw hb j).1) (tailEnv_antitone w)) hne

/-! ### A common lower bound passes to maxima -/

omit [CompactSpace M] in
theorem measurable_of_isThetaPshPotential {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    Measurable u :=
  hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable

/-- If `σ ≤ θ_u^n` and `σ ≤ θ_v^n`, then `σ ≤ θ_{max(u, v)}^n`. -/
theorem le_diagonalPotentialMeasure_max (omega : KahlerBackground n M) {σ : Measure M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hmax : IsThetaPshPotential θ.val (fun x => max (u x) (v x)))
    (hσu : σ ≤ diagonalPotentialMeasure θ u hu) (hσv : σ ≤ diagonalPotentialMeasure θ v hv) :
    σ ≤ diagonalPotentialMeasure θ (fun x => max (u x) (v x)) hmax := by
  rw [Measure.le_iff]
  intro E hE
  have hm : MeasurableSet {x | v x ≤ u x} :=
    measurableSet_le (measurable_of_isThetaPshPotential hv) (measurable_of_isThetaPshPotential hu)
  have hdiff : E \ {x | v x ≤ u x} = E ∩ {x | u x < v x} := by
    ext x; simp [not_le]
  calc σ E = σ (E ∩ {x | v x ≤ u x}) + σ (E \ {x | v x ≤ u x}) :=
        (measure_inter_add_sdiff E hm).symm
    _ ≤ diagonalPotentialMeasure θ u hu (E ∩ {x | v x ≤ u x}) +
          diagonalPotentialMeasure θ v hv (E ∩ {x | u x < v x}) := by
        rw [hdiff]; exact add_le_add (hσu _) (hσv _)
    _ ≤ _ := MaxMassDecomposition.measure_max_ge' omega hu hv hmax hE

/-- A common lower bound passes to the finite tail maxima. -/
theorem le_diagonalPotentialMeasure_tailMax (omega : KahlerBackground n M) {σ : Measure M}
    {w : ℕ → M → EReal} (hw : ∀ k, IsThetaPshPotential θ.val (w k)) (j : ℕ)
    (hσ : ∀ k, σ ≤ diagonalPotentialMeasure θ (w (k + j)) (hw (k + j))) :
    ∀ l, σ ≤ diagonalPotentialMeasure θ (tailMax w j l) (isThetaPshPotential_tailMax hw j l) := by
  intro l
  induction l with
  | zero =>
    exact (hσ 0).trans_eq (SGPT.Envelopes.RelativeMA.diagonalPotentialMeasure_congr_fun
      (by simp only [zero_add]; rfl) _ _)
  | succ l ih =>
    exact le_diagonalPotentialMeasure_max omega (isThetaPshPotential_tailMax hw j l) (hw _)
      (isThetaPshPotential_tailMax hw j (l + 1)) ih (hσ (l + 1))

/-- **Increasing step.** A finite common lower bound of the `θ_{w_k}^n`, `k ≥ j`, is a lower
bound of the measure of the tail envelope `a_j`. -/
theorem le_diagonalPotentialMeasure_tailEnv (omega : KahlerBackground n M) {σ : Measure M}
    [IsFiniteMeasure σ] {w : ℕ → M → EReal} (hw : ∀ k, IsThetaPshPotential θ.val (w k))
    (j : ℕ) (ha : IsThetaPshPotential θ.val (tailEnv w j))
    (hσ : ∀ k, σ ≤ diagonalPotentialMeasure θ (w (k + j)) (hw (k + j))) :
    σ ≤ diagonalPotentialMeasure θ (tailEnv w j) ha := by
  let : TopologicalSpace.PseudoMetrizableSpace M :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n M
  have hT := isThetaPshPotential_tailMax hw j
  have hU : IsThetaPshPotential θ.val (uscRegularization (⨆ l, tailMax w j l)) := by
    rw [iSup_tailMax]; exact ha
  have heq : diagonalPotentialMeasure θ (uscRegularization (⨆ l, tailMax w j l)) hU =
      diagonalPotentialMeasure θ (tailEnv w j) ha :=
    SGPT.Envelopes.RelativeMA.diagonalPotentialMeasure_congr_fun
      (by rw [iSup_tailMax]; rfl) hU ha
  have : IsFiniteMeasure (diagonalPotentialMeasure θ (tailEnv w j) ha) :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ ha
  have : ∀ l, IsFiniteMeasure (diagonalPotentialMeasure θ (tailMax w j l) (hT l)) := fun l =>
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ (hT l)
  refine le_of_tendsto_integral (lams := fun l => diagonalPotentialMeasure θ (tailMax w j l) (hT l))
    (fun g => ?_) (le_diagonalPotentialMeasure_tailMax omega hw j hσ)
  rw [← heq]
  exact IncreasingDiagonalContinuity.tendsto_integral_diagonal_of_monotone omega hT
    (tailMax_monotone w j) hU g

/-! ### Decreasing sequences: truncation and plurifine locality -/

/-- Plurifine locality of the maximum for diagonal measures: `θ_{max(u, w)}^n = θ_u^n` on
every set where `w < u`. -/
theorem diagonalPotentialMeasure_restrict_max_eq {u w : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hw : IsThetaPshPotential θ.val w)
    (hmax : IsThetaPshPotential θ.val (fun x => max (u x) (w x))) {S : Set M}
    (hS : S ⊆ {x | w x < u x}) :
    (diagonalPotentialMeasure θ (fun x => max (u x) (w x)) hmax).restrict S =
      (diagonalPotentialMeasure θ u hu).restrict S := by
  have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq (θ := fun _ : Fin n => θ)
    (u := fun _ => u) (w := fun _ => w) (fun _ => hu.1) (fun _ => hw.1) (fun _ => hmax.1)
  have hS' : S ⊆ {x | ∀ _ : Fin n, w x < u x} := fun x hx _ => hS hx
  have h2 := congrArg (fun μ : Measure M => μ.restrict S) h
  simp only [Measure.restrict_restrict_of_subset hS'] at h2
  exact h2

/-- Weak convergence of the measures along a decreasing sequence of potentials of equal
mass (`thm:semicon`, decreasing branch, weight `1`). -/
theorem tendsto_integral_of_antitone_of_mass_eq (omega : KahlerBackground n M)
    {u : ℕ → M → EReal} {v : M → EReal} (hu : ∀ j, IsThetaPshPotential θ.val (u j))
    (hv : IsThetaPshPotential θ.val v) (hanti : ∀ x, Antitone fun j => u j x)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (hmass : ∀ j, diagonalPotentialMass θ (u j) (hu j) = diagonalPotentialMass θ v hv)
    (g : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, g x ∂diagonalPotentialMeasure θ (u j) (hu j)) atTop
      (𝓝 (∫ x, g x ∂diagonalPotentialMeasure θ v hv)) := by
  have hqc : CapacityWeightedConvergence.QuasiContinuousFor
      (ThetaCapacity.thetaCapacity omega.form (fun _ => 0)) (fun _ : M => (1 : ℝ)) := by
    intro eta heta
    exact ⟨∅, isOpen_empty, by simpa using heta, continuousOn_const⟩
  have hχcap : ∀ c : ℝ, 0 < c → Tendsto (fun j : ℕ => ThetaCapacity.thetaCapacity omega.form
      (fun _ => 0) {x : M | c < |(fun (_ : ℕ) (_ : M) => (1 : ℝ)) j x - (fun _ : M => (1 : ℝ)) x|})
      atTop (𝓝 0) := by
    intro c hc
    have hset : {x : M | c < |(fun (_ : ℕ) (_ : M) => (1 : ℝ)) 0 x - (fun _ : M => (1 : ℝ)) x|} =
        ∅ := by
      ext x
      simp only [sub_self, abs_zero, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact hc.le
    simp only [sub_self, abs_zero] at hset ⊢
    simp only [hset, ThetaCapacity.thetaCapacity_empty]
    exact tendsto_const_nhds
  have h := SGPT.NPP.CapacityConvergence.tendsto_integral_moving omega
    (θ := fun _ : Fin n => θ) (u := fun j _ => u j) (v := fun _ => v)
    (fun j _ => hu j) (fun _ => hv)
    (fun _ a ha => SGPT.NPP.CapacityConvergence.tendsto_capacity_gap_of_antitone omega hu hv
      hanti hlim a ha)
    (tendsto_const_nhds.congr fun j => (hmass j).symm)
    (C := 1) zero_le_one (χ := fun _ _ => (1 : ℝ)) (χ₀ := fun _ => (1 : ℝ))
    (fun _ _ => ⟨zero_le_one, le_rfl⟩) (fun _ => ⟨zero_le_one, le_rfl⟩)
    (fun _ => measurable_const) measurable_const hqc hχcap g
  simp only [mul_one] at h
  exact h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The truncation `max(u, φ - C)` of `u ≤ φ` lies in `E^∞(X, θ; φ)`. -/
theorem relativeEInfinity_max_add_neg {φ u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hφ : IsThetaPshPotential θ.val φ) (huφ : u ≤ φ) {C : ℝ} (hC : 0 ≤ C) :
    RelativeEInfinity θ φ (fun x => max (u x) (φ x + ((-C : ℝ) : EReal))) := by
  refine ⟨SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hu (hφ.add_const (-C)),
    ⟨0, fun x _ => ?_⟩, ⟨C, fun x _ => ?_⟩⟩
  · rw [EReal.coe_zero, add_zero]
    exact max_le (huφ x) (ereal_add_neg_le hC)
  · calc φ x = φ x + ((-C : ℝ) : EReal) + (C : EReal) := (ereal_add_neg_add_cancel _ _).symm
      _ ≤ max (u x) (φ x + ((-C : ℝ) : EReal)) + (C : EReal) := add_le_add (le_max_right _ _) le_rfl

/-- **Decreasing step.** Let `a_j ≤ φ` decrease to `A`, and `σ ≤ θ_{a_j}^n` for every `j`.
Then `σ ≤ θ_A^n` on the set `{A > φ - C}`, for every `C ≥ 0`. -/
theorem restrict_le_of_antitone (omega : KahlerBackground n M) {φ : M → EReal}
    (hφ : IsModelPotential θ φ) {a : ℕ → M → EReal} {A : M → EReal}
    (ha : ∀ j, IsThetaPshPotential θ.val (a j)) (hanti : ∀ x, Antitone fun j => a j x)
    (haφ : ∀ j, a j ≤ φ) (hA : IsThetaPshPotential θ.val A) (hAinf : ∀ x, ⨅ j, a j x = A x)
    {σ : Measure M} [IsFiniteMeasure σ] (hσ : ∀ j, σ ≤ diagonalPotentialMeasure θ (a j) (ha j))
    {C : ℝ} (hC : 0 ≤ C) :
    σ.restrict {x | φ x + ((-C : ℝ) : EReal) < A x} ≤ diagonalPotentialMeasure θ A hA := by
  let : TopologicalSpace.PseudoMetrizableSpace M :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n M
  set c : ℝ := -C with hc
  have hφc : IsThetaPshPotential θ.val (fun x => φ x + (c : EReal)) := hφ.plurisubharmonic.add_const c
  set t : ℕ → M → EReal := fun j x => max (a j x) (φ x + (c : EReal)) with htdef
  set T : M → EReal := fun x => max (A x) (φ x + (c : EReal)) with hTdef
  have ht : ∀ j, IsThetaPshPotential θ.val (t j) := fun j =>
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max (ha j) hφc
  have hT : IsThetaPshPotential θ.val T := SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hA hφc
  have hAφ : A ≤ φ := fun x => by rw [← hAinf x]; exact (iInf_le _ 0).trans (haφ 0 x)
  have hmass : ∀ j, diagonalPotentialMass θ (t j) (ht j) = diagonalPotentialMass θ T hT := by
    intro j
    have h1 := (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity (hφ := hφ)
      omega (relativeEInfinity_max_add_neg (ha j) hφ.plurisubharmonic (haφ j) hC)).1
    have h2 := (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity (hφ := hφ)
      omega (relativeEInfinity_max_add_neg hA hφ.plurisubharmonic hAφ hC)).1
    exact (h1.mass_eq (ht j)).trans (h2.mass_eq hT).symm
  have htanti : ∀ x, Antitone fun j => t j x := fun x i j hij => max_le_max (hanti x hij) le_rfl
  have htlim : ∀ x, Tendsto (fun j => t j x) atTop (𝓝 (T x)) := by
    intro x
    have h := tendsto_atTop_iInf (htanti x)
    have heq : (⨅ j, t j x) = T x := by
      simp only [htdef, hTdef, ← hAinf x]
      exact (iInf_sup_eq (fun j => a j x) (φ x + (c : EReal))).symm
    rwa [heq] at h
  have hweak := tendsto_integral_of_antitone_of_mass_eq omega ht hT htanti htlim hmass
  set S : Set M := {x | φ x + (c : EReal) < A x} with hS
  have hSm : MeasurableSet S :=
    measurableSet_lt (measurable_of_isThetaPshPotential hφc) (measurable_of_isThetaPshPotential hA)
  have hrestr : ∀ (μ : Measure M) (E : Set M), MeasurableSet E →
      μ.restrict S (E ∩ S) = μ (E ∩ S) := fun μ E hE => by
    rw [Measure.restrict_apply (hE.inter hSm), inter_assoc, inter_self]
  have hstep : ∀ j, σ.restrict S ≤ diagonalPotentialMeasure θ (t j) (ht j) := by
    intro j
    have hloc := diagonalPotentialMeasure_restrict_max_eq (ha j) hφc (ht j) (S := S)
      (fun x hx => lt_of_lt_of_le hx (show A x ≤ a j x by rw [← hAinf x]; exact iInf_le _ j))
    rw [Measure.le_iff]
    intro E hE
    rw [Measure.restrict_apply hE]
    calc σ (E ∩ S) ≤ diagonalPotentialMeasure θ (a j) (ha j) (E ∩ S) := hσ j _
      _ = (diagonalPotentialMeasure θ (a j) (ha j)).restrict S (E ∩ S) := (hrestr _ E hE).symm
      _ = (diagonalPotentialMeasure θ (t j) (ht j)).restrict S (E ∩ S) := by rw [← hloc]
      _ = diagonalPotentialMeasure θ (t j) (ht j) (E ∩ S) := hrestr _ E hE
      _ ≤ diagonalPotentialMeasure θ (t j) (ht j) E := measure_mono inter_subset_left
  have : IsFiniteMeasure (diagonalPotentialMeasure θ T hT) :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hT
  have : ∀ j, IsFiniteMeasure (diagonalPotentialMeasure θ (t j) (ht j)) := fun j =>
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ (ht j)
  have hlimle : σ.restrict S ≤ diagonalPotentialMeasure θ T hT :=
    le_of_tendsto_integral (lams := fun j => diagonalPotentialMeasure θ (t j) (ht j)) hweak hstep
  have hloc := diagonalPotentialMeasure_restrict_max_eq hA hφc hT (S := S) (fun x hx => hx)
  rw [Measure.le_iff]
  intro E hE
  calc σ.restrict S E = σ.restrict S (E ∩ S) := by
        rw [Measure.restrict_apply hE, Measure.restrict_apply (hE.inter hSm), inter_assoc, inter_self]
    _ ≤ diagonalPotentialMeasure θ T hT (E ∩ S) := hlimle _
    _ = (diagonalPotentialMeasure θ T hT).restrict S (E ∩ S) := (hrestr _ E hE).symm
    _ = (diagonalPotentialMeasure θ A hA).restrict S (E ∩ S) := by rw [hloc]
    _ = diagonalPotentialMeasure θ A hA (E ∩ S) := hrestr _ E hE
    _ ≤ diagonalPotentialMeasure θ A hA E := measure_mono inter_subset_left

/-! ### Assembly -/

/-- **Lower bounds pass to the tail limit** (Xia, *Foundations of pluripotential theory*,
`lem:nonpluripolar-measure-lower-bound-lone-limit`, for the tail limit). Let `φ` be a model
potential, `w_k ≤ φ` be `θ`-psh, `ν` a finite measure charging no pluripolar set, and
`θ_{w_k}^n ≥ f_k ν` with measurable `f_k ≥ 0`. If the decreasing limit `A` of the tail
envelopes `(sup_{k ≥ j} w_k)^*` is `θ`-psh, then `θ_A^n ≥ (liminf_k f_k) ν`. -/
theorem withDensity_liminf_le_tailLimit (omega : KahlerBackground n M) {φ : M → EReal}
    (hφ : IsModelPotential θ φ) {ν : Measure M} (hν : DoesNotChargeManifoldPluripolar (n := n) ν)
    {w : ℕ → M → EReal} (hw : ∀ k, IsThetaPshPotential θ.val (w k)) (hwφ : ∀ k, w k ≤ φ)
    {f : ℕ → M → ℝ≥0∞} (hf : ∀ k, Measurable (f k))
    (hwf : ∀ k, ν.withDensity (f k) ≤ diagonalPotentialMeasure θ (w k) (hw k))
    (hA : IsThetaPshPotential θ.val (tailLimit w)) :
    ν.withDensity (fun x => liminf (fun k => f k x) atTop) ≤
      diagonalPotentialMeasure θ (tailLimit w) hA := by
  have : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  obtain ⟨b, hb⟩ := hφ.plurisubharmonic.exists_global_upper_bound
  have hwb : ∀ k x, w k x ≤ (b : EReal) := fun k x => (hwφ k x).trans (hb x)
  have haP := isThetaPshPotential_tailEnv hw hwb
  have haφ : ∀ j, tailEnv w j ≤ φ :=
    tailEnv_le hφ.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous hwφ
  set A := tailLimit w with hAdef
  set g : ℕ → M → ℝ≥0∞ := fun j x => ⨅ k, f (k + j) x with hgdef
  have hgm : ∀ j, Measurable (g j) := fun j => Measurable.iInf fun k => hf (k + j)
  have hgmono : Monotone g := by
    intro i j hij x
    refine le_iInf fun k => ?_
    have : k + j = (k + (j - i)) + i := by omega
    rw [this]
    exact iInf_le (fun k => f (k + i) x) (k + (j - i))
  have hσle : ∀ j k, ν.withDensity (g j) ≤ diagonalPotentialMeasure θ (w (k + j)) (hw (k + j)) :=
    fun j k => (withDensity_mono (ae_of_all _ fun x => iInf_le (fun k => f (k + j) x) k)).trans
      (hwf (k + j))
  have hσfin : ∀ j, IsFiniteMeasure (ν.withDensity (g j)) := fun j => by
    have := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ (hw (0 + j))
    exact isFiniteMeasure_of_le _ (hσle j 0)
  -- the increasing step
  have hstep1 : ∀ j₀ j, ν.withDensity (g j₀) ≤
      diagonalPotentialMeasure θ (tailEnv w (j + j₀)) (haP (j + j₀)) := by
    intro j₀ j
    refine le_diagonalPotentialMeasure_tailEnv omega hw (j + j₀) (haP _) fun k => ?_
    exact (withDensity_mono (ae_of_all _ fun x => hgmono (Nat.le_add_left j₀ j) x)).trans
      (hσle (j + j₀) k)
  -- the decreasing step
  have hstep2 : ∀ j₀ (C : ℕ), (ν.withDensity (g j₀)).restrict
      {x | φ x + ((-(C : ℝ) : ℝ) : EReal) < A x} ≤ diagonalPotentialMeasure θ A hA := by
    intro j₀ C
    have hinf : ∀ x, ⨅ j, tailEnv w (j + j₀) x = A x := by
      intro x
      apply le_antisymm
      · exact le_iInf fun j => (iInf_le _ j).trans (tailEnv_antitone w x (Nat.le_add_right j j₀))
      · exact le_iInf fun j => iInf_le (fun j => tailEnv w j x) (j + j₀)
    exact restrict_le_of_antitone omega hφ (a := fun j => tailEnv w (j + j₀)) (fun j => haP _)
      (fun x i j hij => tailEnv_antitone w x (Nat.add_le_add_right hij j₀)) (fun j => haφ _) hA
      hinf (hstep1 j₀) (Nat.cast_nonneg C)
  -- removing the restriction
  have hnull : ν {x | A x = ⊥} = 0 := by
    have h := SGPT.Envelopes.RelativeMA.ae_ne_bot_of_doesNotCharge hν hA
    rw [ae_iff] at h
    simpa only [ne_eq, not_not] using h
  have hstep3 : ∀ j₀, ν.withDensity (g j₀) ≤ diagonalPotentialMeasure θ A hA := by
    intro j₀
    rw [Measure.le_iff]
    intro E hE
    set S : ℕ → Set M := fun C => {x | φ x + ((-(C : ℝ) : ℝ) : EReal) < A x} with hS
    have hSm : ∀ C, MeasurableSet (S C) := fun C =>
      measurableSet_lt (measurable_of_isThetaPshPotential (hφ.plurisubharmonic.add_const _))
        (measurable_of_isThetaPshPotential hA)
    have hSmono : Monotone S := by
      intro C C' hCC' x hx
      have hx' : φ x + ((-(C : ℝ) : ℝ) : EReal) < A x := hx
      show φ x + ((-(C' : ℝ) : ℝ) : EReal) < A x
      exact lt_of_le_of_lt (add_le_add le_rfl
        (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hCC')))) hx'
    have hcover : (⋃ C, S C)ᶜ ⊆ {x | A x = ⊥} := by
      intro x hx
      by_contra hAx
      have hφx : φ x ≠ ⊤ := hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x
      obtain ⟨C, hC⟩ := exists_nat_add_neg_lt hAx (hA.1.quasiPlurisubharmonic.ne_top x) hφx
      exact hx (mem_iUnion.mpr ⟨C, hC⟩)
    have hnull' : ν.withDensity (g j₀) (⋃ C, S C)ᶜ = 0 :=
      withDensity_absolutelyContinuous ν _ (measure_mono_null hcover hnull)
    calc ν.withDensity (g j₀) E ≤ ν.withDensity (g j₀) (E ∩ ⋃ C, S C) +
          ν.withDensity (g j₀) (E \ ⋃ C, S C) := measure_le_inter_add_sdiff _ _ _
      _ = ν.withDensity (g j₀) (⋃ C, E ∩ S C) := by
          rw [measure_mono_null (show E \ ⋃ C, S C ⊆ (⋃ C, S C)ᶜ from fun x hx => hx.2) hnull',
            add_zero, inter_iUnion]
      _ = ⨆ C, ν.withDensity (g j₀) (E ∩ S C) :=
          Monotone.measure_iUnion fun C C' h => inter_subset_inter_right _ (hSmono h)
      _ ≤ diagonalPotentialMeasure θ A hA E := by
          refine iSup_le fun C => ?_
          rw [← Measure.restrict_apply hE]
          exact hstep2 j₀ C E
  -- the liminf
  rw [Measure.le_iff]
  intro E hE
  rw [withDensity_apply _ hE]
  have hlim : (fun x => liminf (fun k => f k x) atTop) = fun x => ⨆ j, g j x :=
    funext fun x => liminf_eq_iSup_iInf_of_nat'
  rw [hlim, lintegral_iSup hgm hgmono]
  refine iSup_le fun j => ?_
  rw [← withDensity_apply _ hE]
  exact hstep3 j E

end SGPT.Envelopes.RelativeCY
