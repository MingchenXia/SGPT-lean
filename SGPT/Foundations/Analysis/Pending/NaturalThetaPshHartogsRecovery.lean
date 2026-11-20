import SGPT.Foundations.Analysis.Pending.NaturalPshHartogsBallEstimate
import SGPT.Foundations.Analysis.Pending.ThetaPshL1Order
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

/-!
# Genuine Hartogs upper recovery and the original canonical USC tail infimum

The actual original theta-PSH functions and canonical chart-local L1 limit
internally produce eventual neighborhood upper recovery, including poles.
The literal original USC tail suprema then decrease to the original limit.
No compactness, connectedness, positive dimension, energy or MA certificate
is assumed or claimed by these statements.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalThetaPshHartogsRecovery

open FirstPass NaturalPshHartogsBallEstimate

/-- Finite translation preserves the actual canonical extended difference, including poles. -/
theorem canonicalERealAbsDiff_add_coe (a b : EReal) (c : ℝ) :
    canonicalERealAbsDiff (a + (c : EReal)) (b + (c : EReal)) =
      canonicalERealAbsDiff a b := by
  induction a using EReal.rec with
  | bot =>
    induction b using EReal.rec <;> simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  | top =>
    induction b using EReal.rec <;>
      simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff, ← EReal.coe_add]
  | coe a =>
    induction b using EReal.rec with
    | bot => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    | top => simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
    | coe b =>
      rw [← EReal.coe_add, ← EReal.coe_add, canonicalERealAbsDiff_coe_coe,
        canonicalERealAbsDiff_coe_coe, add_sub_add_right_eq_sub]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- A single original neighborhood admits one eventual upper bound for all its points. -/
theorem eventually_locally_le_of_manifoldL1LocallyTendsto
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ (u j)) (hv : IsThetaPshPotential θ v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    (x : M) {a : ℝ} (ha : v x < (a : EReal)) :
    ∃ V : Set M, V ∈ 𝓝 x ∧ ∀ᶠ j in atTop, ∀ y ∈ V, u j y ≤ (a : EReal) := by
  obtain ⟨b, hvb, hba⟩ := EReal.exists_rat_btwn_of_lt ha
  have hbaR : (b : ℝ) < a := EReal.coe_lt_coe_iff.mp hba
  let δ : ℝ := (a - (b : ℝ)) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let e : ComplexChart n M := complexChartAt (n := n) x
  let z : ComplexModel n := e.val x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpv⟩ := hv.1 e z hz
  let corrected (f : M → EReal) : ComplexModel n → EReal :=
    fun y => chartFunction f e y + (ρ y : EReal)
  let A : ℝ := (b : ℝ) + ρ z
  have htest : corrected v z < (A : EReal) := by
    have hraw : chartFunction v e z < ((b : ℝ) : EReal) := by
      simpa only [chartFunction, z, e.val.left_inv hx] using hvb
    simpa only [corrected, A, EReal.coe_add] using EReal.add_lt_add_right_coe hraw (ρ z)
  have hupper : ∀ᶠ y in 𝓝 z, corrected v y < (A : EReal) := by
    have h := hpv.upperSemicontinuousOn z hzW (A : EReal) htest
    rw [nhdsWithin_eq_nhds.mpr (hρ.1.mem_nhds hzW)] at h
    exact h
  have hρcont : ContinuousAt ρ z :=
    ((hρ.2.2.1 z hzW).contDiffAt (hρ.1.mem_nhds hzW)).continuousAt
  have hρlow : ∀ᶠ y in 𝓝 z, ρ z - δ < ρ y :=
    hρcont.eventually (lt_mem_nhds (sub_lt_self _ hδ))
  have hnhds : {y | y ∈ W ∧ corrected v y < (A : EReal) ∧ ρ z - δ < ρ y} ∈ 𝓝 z := by
    filter_upwards [hρ.1.mem_nhds hzW, hupper, hρlow] with y hyW hyA hyρ
    exact ⟨hyW, hyA, hyρ⟩
  obtain ⟨ε, hε, hlocal⟩ := Metric.mem_nhds_iff.mp hnhds
  let U : Set (ComplexModel n) := ball z ε
  let r : ℝ := ε / 4
  let K : Set (ComplexModel n) := closedBall z (3 * r)
  have hr : 0 < r := by dsimp [r]; positivity
  have hKU : K ⊆ U := closedBall_subset_ball (by dsimp [r]; linarith)
  have hUW : U ⊆ W := fun y hy => (hlocal hy).1
  have hUt : U ⊆ e.val.target := hUW.trans hρ.2.1
  have hKt : K ⊆ e.val.target := hKU.trans hUt
  have hcpsh (f : M → EReal) (hf : IsThetaPshPotential θ f) :
      PlurisubharmonicOn (corrected f) U :=
    (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      hf.1 e hρ).mono hUW
  have hne (f : M → EReal) (hf : IsThetaPshPotential θ f) :
      ∃ y ∈ U, corrected f y ≠ ⊥ := by
    obtain ⟨y, hyU, hy⟩ := hf.2.exists_chart_ne_bot e isOpen_ball hUt (mem_ball_self hε)
    exact ⟨y, hyU, EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot (ρ y)⟩⟩
  have hcorrL1 : Tendsto (fun j => ∫⁻ y in K,
      canonicalERealAbsDiff (corrected (u j) y) (corrected v y) ∂volume) atTop (𝓝 0) := by
    have h := hlim e K (isCompact_closedBall z (3 * r)) hKt
    simpa only [chartL1EDistance, corrected, canonicalERealAbsDiff_add_coe] using h
  have hlocalBound : ∀ᶠ j in atTop, ∀ y ∈ ball z r,
      corrected (u j) y ≤ ((A + δ : ℝ) : EReal) :=
    eventually_le_on_ball_of_lintegral_canonical_tendsto
      (fun j => hcpsh (u j) (hu j)) (hcpsh v hv) (convex_ball z ε).isPreconnected
      (fun j => hne (u j) (hu j)) (hne v hv) volume z hr hKU
      (fun y hy => (hlocal (hKU hy)).2.1.le) hcorrL1 hδ
  let V : Set M := e.val.source ∩ e.val ⁻¹' ball z r
  have hVopen : IsOpen V := e.val.isOpen_inter_preimage isOpen_ball
  have hxV : x ∈ V := ⟨hx, mem_ball_self hr⟩
  refine ⟨V, hVopen.mem_nhds hxV, ?_⟩
  filter_upwards [hlocalBound] with j hj
  intro y hy
  have hyU : e.val y ∈ U := (ball_subset_ball (by dsimp [r]; linarith)) hy.2
  have hρy := (hlocal hyU).2.2
  have hbound := hj (e.val y) hy.2
  change u j (e.val.symm (e.val y)) + (ρ (e.val y) : EReal) ≤
    ((A + δ : ℝ) : EReal) at hbound
  rw [e.val.left_inv hy.1] at hbound
  have htarget : ((A + δ : ℝ) : EReal) ≤ (a : EReal) + (ρ (e.val y) : EReal) := by
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    dsimp only [A, δ] at hρy ⊢
    linarith
  exact (EReal.addLECancellable_coe (ρ (e.val y))).add_le_add_iff_right.mp
    (hbound.trans htarget)

/-- The literal original canonical USC tails recover the original limit from above. -/
theorem iInf_usc_tailSup_le_of_manifoldL1LocallyTendsto
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ (u j)) (hv : IsThetaPshPotential θ v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v) :
    (⨅ N : ℕ, uscRegularization (⨆ j : ℕ, u (j + N))) ≤ v := by
  intro x
  rw [iInf_apply]
  apply le_of_forall_gt
  intro a ha
  obtain ⟨b, hvb, hba⟩ := EReal.exists_rat_btwn_of_lt ha
  obtain ⟨V, hV, hevent⟩ := eventually_locally_le_of_manifoldL1LocallyTendsto hu hv hlim x hvb
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have htail : uscRegularization (⨆ j : ℕ, u (j + N)) x ≤ ((b : ℝ) : EReal) := by
    refine (uscRegularization_le_localSup _ hV).trans ?_
    refine iSup_le fun y => iSup_le fun hy => ?_
    simp only [iSup_apply]
    exact iSup_le fun j => hN (j + N) (Nat.le_add_left N j) y hy
  exact (iInf_le_of_le N htail :
    (⨅ L : ℕ, uscRegularization (⨆ j : ℕ, u (j + L)) x) ≤ ((b : ℝ) : EReal)).trans_lt hba

/-- Genuine natural bounded tails are antitone and have exactly the original pointwise limit. -/
theorem usc_tailSup_iInf_eq_and_tendsto
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ (u j)) (hv : IsThetaPshPotential θ v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    {C : ℝ} (hC : ∀ j x, u j x ≤ (C : EReal)) :
    (∀ N : ℕ, IsThetaPshPotential θ (uscRegularization (⨆ j : ℕ, u (j + N)))) ∧
    Antitone (fun N : ℕ => uscRegularization (⨆ j : ℕ, u (j + N))) ∧
    (⨅ N : ℕ, uscRegularization (⨆ j : ℕ, u (j + N))) = v ∧
    (∀ x, Tendsto (fun N : ℕ => uscRegularization (⨆ j : ℕ, u (j + N)) x) atTop (𝓝 (v x))) := by
  have hg (N : ℕ) : IsThetaPshPotential θ (uscRegularization (⨆ j : ℕ, u (j + N))) :=
    NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le
      (fun j => hu (j + N)) (fun j x => hC (j + N) x)
  have hanti : Antitone (fun N : ℕ => uscRegularization (⨆ j : ℕ, u (j + N))) := by
    intro N L hNL
    apply uscRegularization_mono
    intro x
    simp only [iSup_apply]
    refine iSup_le fun j => le_iSup_of_le (j + (L - N)) ?_
    have hi : j + (L - N) + N = j + L := by omega
    rw [hi]
  have hlower (N : ℕ) : v ≤ uscRegularization (⨆ j : ℕ, u (j + N)) := by
    apply ThetaPshL1Order.le_of_manifoldL1LocallyTendsto (fun j => hu (j + N)) hv (hg N)
    · intro e K hK hKe
      exact (tendsto_add_atTop_iff_nat N).mpr (hlim e K hK hKe)
    · intro j x
      apply (le_uscRegularization (⨆ j : ℕ, u (j + N)) x).trans'
      simp only [iSup_apply]
      exact le_iSup (fun j => u (j + N) x) j
  have heq : (⨅ N : ℕ, uscRegularization (⨆ j : ℕ, u (j + N))) = v :=
    le_antisymm (iInf_usc_tailSup_le_of_manifoldL1LocallyTendsto hu hv hlim)
      (le_iInf hlower)
  refine ⟨hg, hanti, heq, fun x => ?_⟩
  have h := tendsto_atTop_iInf fun N L hNL => hanti hNL x
  have hinf : (⨅ N : ℕ, uscRegularization (⨆ j : ℕ, u (j + N)) x) = v x := by
    simpa only [iInf_apply] using congrFun heq x
  simpa only [hinf] using h

end SGPT.Foundations.Analysis.Pending.NaturalThetaPshHartogsRecovery
