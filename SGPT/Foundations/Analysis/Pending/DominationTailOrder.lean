import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.StrongOpennessEnvelope
import SGPT.Foundations.Analysis.Pending.StrongOpennessRegularRoute
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.DivisorialDomination

set_option autoImplicit false

/-!
# Tail envelopes are dominated in the multiplier-ideal order

Step 3 of the domination lemma without bigness (Copy-4 `lem:domination`; blueprint
`pc:domination-tail-order`).  For theta-PSH potentials `ŝ_j ≤ 0` with `ŝ_j ≤ v_j + C_j`, where
`(v_j)` decreases, the tail upper envelopes `E_m = (sup_{j ≥ m} ŝ_j)^*` satisfy `E_m ≼_I v_m`; and
if the multiplier ideals of `v_j` eventually sit inside those of `v` (the multiplier clause of a
quasi-equisingular approximation), then every potential below all the `E_m`, in particular the
decreasing limit `s_∞ = lim_m E_m`, satisfies `s_∞ ≼_I v`.

The proof uses only strong openness: for the increasing finite maxima `max_{m ≤ j ≤ M} ŝ_j`, whose
regularized limit is `E_m` (`iOrderOnManifold_uscRegularization_iSup_of_strongOpenness`), and for
the single function `s_∞` (`exists_gt_multiplierIntegrableAt_chartFunction`, any chart).  Copy-4
argues instead with Lelong numbers along divisors over `Z` and the valuative description of
`≼_I`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.DominationTailOrder

open FirstPass FirstPass.IEnvelope FirstPass.QuasiEquisingularApproximation
  DecreasingRooftopTailEnvelope

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Strong openness in an arbitrary chart -/

/-- **Strong openness for a quasi-psh function, in any chart**: if `|f|² e^{-c u}` is integrable
near `z` in the chart `e`, then so is `|f|² e^{-c' u}` for some `c' > c`.  In the chart,
`u = P + h` near `z` with `P` psh and `h` smooth, and the Euclidean statement applies to `P`. -/
theorem exists_gt_multiplierIntegrableAt_chartFunction {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) {c : ℝ} {f : ComplexModel n → ℂ}
    (hint : MultiplierIntegrableAt (chartFunction u e) c f z volume) :
    ∃ c' : ℝ, c < c' ∧ MultiplierIntegrableAt (chartFunction u e) c' f z volume := by
  have hqp := hu e z hz
  obtain ⟨P, h, hP, hh, heq⟩ := hqp
  obtain ⟨U, hUo, hzU, hdisc⟩ := hP
  have hPU : PlurisubharmonicOn P U := fun y hy => ⟨U, hUo, hy, hdisc⟩
  have hhc : ContinuousAt h z := hh.self_of_nhds.continuousAt
  have hnear : ∀ᶠ y in 𝓝 z, |h y - h z| < 1 := by
    filter_upwards [hhc (Metric.ball_mem_nhds (h z) one_pos)] with y hy
    simpa [Real.dist_eq] using hy
  have h1 : MoreSingularAt (chartFunction u e) P z := by
    refine ⟨h z + 1, ?_⟩
    filter_upwards [heq, hnear] with y hy hb
    rw [hy]
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    have := (abs_lt.mp hb).2
    linarith
  have h2 : MoreSingularAt P (chartFunction u e) z := by
    refine ⟨-h z + 1, ?_⟩
    filter_upwards [heq, hnear] with y hy hb
    rw [hy, add_assoc, ← EReal.coe_add]
    refine le_add_of_nonneg_right (EReal.coe_nonneg.mpr ?_)
    have := (abs_lt.mp hb).1
    linarith
  have hPint := multiplierIntegrableAt_of_moreSingularAt
    (hPU _ hzU).quasiPlurisubharmonicAt h1 hint
  obtain ⟨c', hcc', hPint'⟩ :=
    PositiveCurrentTraceMultiplier.exists_gt_multiplierIntegrableAt hUo hPU hzU hPint
  exact ⟨c', hcc', multiplierIntegrableAt_of_moreSingularAt (hu e z hz) h2 hPint'⟩

/-- **Domination by every term of an approximating sequence passes to the limit.**  If a
quasi-psh `w` satisfies `w ≼_I v_m` for every `m`, and for all `0 < c < d` eventually
`I(d v_m) ⊆ I(c v)` (the multiplier clause of a quasi-equisingular approximation of `v`), then
`w ≼_I v`.  Strong openness for `w` supplies the room between `c` and `d`. -/
theorem iOrderOnManifold_of_forall_iOrderOnManifold_of_eventually {w v : M → EReal}
    {vSeq : ℕ → M → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    (hle : ∀ m, IOrderOnManifold (n := n) w (vSeq m))
    (hqe : ∀ c d : ℝ, 0 < c → c < d →
      ∀ᶠ m in atTop, MultiplierIdealIncluded (n := n) (vSeq m) d v c) :
    IOrderOnManifold (n := n) w v := by
  intro c hc e z hz f hf hmem
  have hmem' : MultiplierIntegrableAt (chartFunction w e) c f z volume :=
    (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mpr hmem
  obtain ⟨c', hcc', hint'⟩ := exists_gt_multiplierIntegrableAt_chartFunction hw e hz hmem'
  obtain ⟨m, hm⟩ := (hqe c c' hc hcc').exists
  have hint'' := (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mp hint'
  exact hm e z hz f hf (hle m c' (hc.trans hcc') e z hz f hf hint'')

/-! ### Tail envelopes -/

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The supremum of the running maxima of the shifted tail is the supremum of the tail family. -/
theorem iSup_runningMax_eq_sSup_tailFamily (s : ℕ → M → EReal) (m : ℕ) :
    (⨆ M', runningMax (fun i => s (m + i)) M') = sSup (tailFamily s m) := by
  funext x
  rw [iSup_apply, sSup_apply]
  refine le_antisymm (iSup_le fun M' => ?_) (iSup_le fun ⟨w, j, hmj, hw⟩ => ?_)
  · refine runningMax_apply_le (fun i => ?_) M'
    exact le_iSup (fun w : tailFamily s m => (w : M → EReal) x)
      ⟨s (m + i), m + i, Nat.le_add_right m i, rfl⟩
  · subst hw
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hmj
    exact (le_runningMax (fun i => s (m + i)) i x).trans
      (le_iSup (fun M' => runningMax (fun i => s (m + i)) M' x) i)

/-- **Tail envelopes are dominated in the `I`-order** (blueprint `pc:domination-tail-order`, first
assertion).  Let `ŝ_j ≤ 0` be theta-PSH potentials and `v_j` quasi-psh with `v_{j+1} ≤ v_j` and
`ŝ_j ≤ v_j + C_j`.  Then the tail upper envelope `E_m = (sup_{j ≥ m} ŝ_j)^*` satisfies
`E_m ≼_I v_m`. -/
theorem iOrderOnManifold_tailEnvelope {θ : SmoothRealForm n M 2} {s : ℕ → M → EReal}
    (hs : ∀ j, IsThetaPshPotential θ (s j)) (hs0 : ∀ j, s j ≤ 0) {v : ℕ → M → EReal}
    (hv : ∀ j, ManifoldQuasiPlurisubharmonic (n := n) (v j)) (hanti : ∀ j, v (j + 1) ≤ v j)
    (hdom : ∀ j, ∃ C : ℝ, ∀ x, s j x ≤ v j x + (C : EReal)) (m : ℕ) :
    IOrderOnManifold (n := n) (tailEnvelope s m) (v m) := by
  have hlocal : HasSmoothLocalPotentials θ := (hs 0).1.hasSmoothLocalPotentials
  have hvanti : Antitone v := antitone_nat_of_succ_le hanti
  set W : ℕ → M → EReal := runningMax (fun i => s (m + i)) with hW
  have hWpsh : ∀ M', IsThetaPshPotential θ (W M') :=
    RooftopEnvelopeAeObstacle.isThetaPshPotential_runningMax (fun i => hs (m + i))
  have hW0 : ∀ M', W M' ≤ 0 := fun M' x => runningMax_le (fun i => hs0 (m + i)) M' x
  have hWdom : ∀ M', ∃ K : ℝ, ∀ x, W M' x ≤ v m x + (K : EReal) := by
    intro M'
    induction M' with
    | zero =>
      obtain ⟨C, hC⟩ := hdom m
      exact ⟨C, fun x => by simpa [hW, runningMax] using hC x⟩
    | succ M' ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨C, hC⟩ := hdom (m + (M' + 1))
      refine ⟨max K C, fun x => ?_⟩
      change max (W M' x) (s (m + (M' + 1)) x) ≤ _
      refine max_le ((hK x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left _ _))))
        ((hC x).trans (add_le_add (hvanti (Nat.le_add_right m (M' + 1)) x)
          (EReal.coe_le_coe_iff.mpr (le_max_right _ _))))
  have hWord : ∀ M', IOrderOnManifold (n := n) (W M') (v m) := fun M' => by
    obtain ⟨K, hK⟩ := hWdom M'
    exact iOrderOnManifold_of_le_add (hv m) hK
  have h := iOrderOnManifold_uscRegularization_iSup_of_strongOpenness
    (increasingStrongOpenness_ofRegularRoute n) hlocal hWpsh hW0 (runningMax_monotone _) hWord
  rwa [hW, iSup_runningMax_eq_sSup_tailFamily] at h

/-- **The decreasing limit of the tail envelopes is dominated in the `I`-order** (blueprint
`pc:domination-tail-order`, second assertion).  In the situation of
`iOrderOnManifold_tailEnvelope`, suppose moreover that for all `0 < c < d` eventually
`I(d v_j) ⊆ I(c v)`.  Then every quasi-psh `w` lying below all tail envelopes, in particular
`s_∞ = inf_m E_m` when it is quasi-psh, satisfies `w ≼_I v`. -/
theorem iOrderOnManifold_of_le_tailEnvelope {θ : SmoothRealForm n M 2} {s : ℕ → M → EReal}
    (hs : ∀ j, IsThetaPshPotential θ (s j)) (hs0 : ∀ j, s j ≤ 0) {v : ℕ → M → EReal}
    {v' : M → EReal} (hv : ∀ j, ManifoldQuasiPlurisubharmonic (n := n) (v j))
    (hanti : ∀ j, v (j + 1) ≤ v j) (hdom : ∀ j, ∃ C : ℝ, ∀ x, s j x ≤ v j x + (C : EReal))
    (hqe : ∀ c d : ℝ, 0 < c → c < d →
      ∀ᶠ j in atTop, MultiplierIdealIncluded (n := n) (v j) d v' c)
    {w : M → EReal} (hw : ManifoldQuasiPlurisubharmonic (n := n) w)
    (hwle : ∀ m, w ≤ tailEnvelope s m) :
    IOrderOnManifold (n := n) w v' := by
  have hlocal : HasSmoothLocalPotentials θ := (hs 0).1.hasSmoothLocalPotentials
  refine iOrderOnManifold_of_forall_iOrderOnManifold_of_eventually hw (fun m => ?_) hqe
  exact (iOrderOnManifold_of_le
    (isThetaPshPotential_tailEnvelope hlocal hs hs0 m).1.quasiPlurisubharmonic (hwle m)).trans
    (iOrderOnManifold_tailEnvelope hs hs0 hv hanti hdom m)

/-- **Step 3 of the domination lemma: the limit is dominated in the `I`-order** (blueprint
`pc:domination-tail-order`, in the situation of `pc:domination-tail-limit`).  On a compact connected
manifold, let `s_j` be theta-PSH potentials and `v_j` quasi-psh with `v_{j+1} ≤ v_j`,
`s_j ≤ v_j + C_j`, and, for all `0 < c < d`, eventually `I(d v_j) ⊆ I(c v)`.  With `c_j = max s_j`,
`ŝ_j = s_j - c_j`, `E_m = (sup_{j ≥ m} ŝ_j)^*` and `s_∞ = inf_m E_m`: `s_∞` is a theta-PSH
potential, `E_m ≼_I v_m` for every `m`, and `s_∞ ≼_I v`. -/
theorem exists_tailLimit_iOrderOnManifold {k : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] [CompactSpace Z] [ConnectedSpace Z]
    {θ : ClosedRealOneOneForm k Z} {s : ℕ → Z → EReal}
    (hs : ∀ j, IsThetaPshPotential θ.val (s j)) {v : ℕ → Z → EReal} {v' : Z → EReal}
    (hv : ∀ j, ManifoldQuasiPlurisubharmonic (n := k) (v j)) (hanti : ∀ j, v (j + 1) ≤ v j)
    (hdom : ∀ j, ∃ C : ℝ, ∀ x, s j x ≤ v j x + (C : EReal))
    (hqe : ∀ c d : ℝ, 0 < c → c < d →
      ∀ᶠ j in atTop, MultiplierIdealIncluded (n := k) (v j) d v' c) :
    ∃ c : ℕ → ℝ, (∀ j x, s j x ≤ (c j : EReal)) ∧ (∀ j, ∃ x, s j x = (c j : EReal)) ∧
      IsThetaPshPotential θ.val
        (fun x => ⨅ m, tailEnvelope (fun j y => s j y - (c j : EReal)) m x) ∧
      (∀ m, IOrderOnManifold (n := k) (tailEnvelope (fun j y => s j y - (c j : EReal)) m)
        (v m)) ∧
      IOrderOnManifold (n := k)
        (fun x => ⨅ m, tailEnvelope (fun j y => s j y - (c j : EReal)) m x) v' := by
  obtain ⟨c, hc, hcx, hlim, -⟩ := DivisorialDomination.exists_tailLimit hs
  have hŝ : ∀ j, IsThetaPshPotential θ.val (fun y => s j y - (c j : EReal)) :=
    fun j => (hs j).sub_const (c j)
  have hŝ0 : ∀ j, (fun y => s j y - (c j : EReal)) ≤ 0 := fun j =>
    sub_const_nonpositive_of_le (hc j)
  have hŝdom : ∀ j, ∃ C : ℝ, ∀ x, s j x - (c j : EReal) ≤ v j x + (C : EReal) := by
    intro j
    obtain ⟨C, hC⟩ := hdom j
    refine ⟨C - c j, fun x => ?_⟩
    have h := add_le_add (hC x) (le_refl ((-c j : ℝ) : EReal))
    rw [add_assoc, ← EReal.coe_add, ← sub_eq_add_neg] at h
    rwa [sub_eq_add_neg, ← EReal.coe_neg]
  refine ⟨c, hc, hcx, hlim, fun m => iOrderOnManifold_tailEnvelope hŝ hŝ0 hv hanti hŝdom m, ?_⟩
  exact iOrderOnManifold_of_le_tailEnvelope hŝ hŝ0 hv hanti hŝdom hqe
    hlim.1.quasiPlurisubharmonic fun m x => iInf_le (fun m => tailEnvelope _ m x) m

end

end SGPT.Foundations.Analysis.Pending.DominationTailOrder
