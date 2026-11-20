import SGPT.Siu.SiuLemma
import SGPT.Foundations.Analysis.Pending.AnalyticPoleLelongLowerBound

/-!
# Lelong-number calculus for closed positive currents and currents of prime divisors

Source: the proof of Siu's decomposition `eq:Siudec` (chapter *Plurisubharmonic functions*,
after `lma:Siudec`); we follow Xia, *Foundations of pluripotential theory*,
`thm:siu-divisorial-decomposition`, Steps 2–3, which use

* additivity and positive homogeneity of `x ↦ ν(T, x)` (`prop:lelong-calculus` there):
  `currentLelong_add`, `currentLelong_smul`;
* `ν([D], x) ≥ 1` at every point of a prime divisor `D` and `ν([D], x) = 0` off `D`:
  `one_le_currentLelong_primeDivisorCurrent`, `currentLelong_primeDivisorCurrent_eq_zero`;
* closed positive currents form a convex cone: `IsClosedPositiveCurrent.add`,
  `IsClosedPositiveCurrent.smul`.

All statements are for the raw closed positive currents `SGPT.Siu.IsClosedPositiveCurrent` and
the Lelong reader `SGPT.Siu.currentLelong` of `SGPT.Siu.PrimeDivisorCurrent`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal Manifold ContDiff

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent
open SquaredLogLelongSourceNormalization

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-! ### The cone of closed positive currents -/

theorem isFullPositive_add {S T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hS : IsFullPositive S) (hT : IsFullPositive T) : IsFullPositive (S + T) := by
  intro e α hα
  rw [GlobalCurrent.inChart_add, _root_.add_apply]
  exact add_nonneg (hS e α hα) (hT e α hα)

theorem isFullPositive_smul {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsFullPositive T) {c : ℝ} (hc : 0 ≤ c) : IsFullPositive (c • T) := by
  intro e α hα
  rw [GlobalCurrent.inChart_smul, _root_.smul_apply, smul_eq_mul]
  exact mul_nonneg hc (hT e α hα)

theorem isFullPositive_zero :
    IsFullPositive (0 : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) := by
  intro e α _
  rw [GlobalCurrent.inChart_zero, _root_.zero_apply]

/-- A sum of closed positive currents is a closed positive current. -/
theorem IsClosedPositiveCurrent.add {S T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hS : IsClosedPositiveCurrent S) (hT : IsClosedPositiveCurrent T) :
    IsClosedPositiveCurrent (S + T) :=
  ⟨hS.1.add _ hT.1, hS.2.1.add _ hT.2.1, isFullPositive_add hS.2.2 hT.2.2⟩

/-- A nonnegative multiple of a closed positive current is a closed positive current. -/
theorem IsClosedPositiveCurrent.smul {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsClosedPositiveCurrent T) {c : ℝ} (hc : 0 ≤ c) : IsClosedPositiveCurrent (c • T) :=
  ⟨hT.1.smul _ c, hT.2.1.smul _ c, isFullPositive_smul hT.2.2 hc⟩

theorem isClosedPositiveCurrent_zero :
    IsClosedPositiveCurrent (0 : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) :=
  ⟨GlobalCurrent.isClosed_zero _, by
    intro e v w
    rw [GlobalCurrent.coefficients_zero]
    rfl, isFullPositive_zero⟩

/-- A finite nonnegative combination of closed positive currents is a closed positive current. -/
theorem isClosedPositiveCurrent_finsetSum {ι : Type*} (F : Finset ι)
    (c : ι → ℝ) (A : ι → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i ∈ F, 0 ≤ c i) (hA : ∀ i ∈ F, IsClosedPositiveCurrent (A i)) :
    IsClosedPositiveCurrent (∑ i ∈ F, c i • A i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isClosedPositiveCurrent_zero
  | @insert i F hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hA i (Finset.mem_insert_self i F)).smul (hc i (Finset.mem_insert_self i F))).add
        (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
          (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

/-! ### Additivity and homogeneity of Lelong numbers -/

/-- **Additivity of Lelong numbers**: `ν(S + T, x) = ν(S, x) + ν(T, x)`. -/
theorem currentLelong_add [CompactSpace M]
    {S T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hS : IsClosedPositiveCurrent S) (hT : IsClosedPositiveCurrent T)
    (hST : IsClosedPositiveCurrent (S + T)) (x : M) :
    currentLelong (S + T) hST x = currentLelong S hS x + currentLelong T hT x := by
  obtain ⟨σ, φ, hφ, hSeq⟩ := hS.exists_thetaPotential
  obtain ⟨τ, ψ, hψ, hTeq⟩ := hT.exists_thetaPotential
  obtain ⟨hsum, hsum_eq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hφ hψ
  have heq : S + T = thetaPotentialCurrent (σ + τ).val (fun y => φ y + ψ y) hsum := by
    rw [hsum_eq, hSeq, hTeq]
  rw [currentLelong_eq_of_eq_thetaPotentialCurrent hST heq,
    currentLelong_eq_of_eq_thetaPotentialCurrent hS hSeq,
    currentLelong_eq_of_eq_thetaPotentialCurrent hT hTeq]
  exact SGPT.Okounkov.squaredLogLelongNumber_add_eq hφ.1.quasiPlurisubharmonic
    hψ.1.quasiPlurisubharmonic x

/-- **Homogeneity of Lelong numbers**: `ν(c T, x) = c ν(T, x)` for `c ≥ 0`. -/
theorem currentLelong_smul [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsClosedPositiveCurrent T) {c : ℝ} (hc : 0 ≤ c)
    (hcT : IsClosedPositiveCurrent (c • T)) (x : M) :
    currentLelong (c • T) hcT x = ENNReal.ofReal c * currentLelong T hT x := by
  obtain ⟨σ, φ, hφ, hTeq⟩ := hT.exists_thetaPotential
  obtain ⟨hcφ, hcφ_eq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul hφ hc
  have heq : c • T = thetaPotentialCurrent (c • σ).val (fun y => (c : EReal) * φ y) hcφ := by
    rw [hcφ_eq, hTeq]
  rw [currentLelong_eq_of_eq_thetaPotentialCurrent hcT heq,
    currentLelong_eq_of_eq_thetaPotentialCurrent hT hTeq]
  exact SGPT.Okounkov.squaredLogLelongNumber_nonneg_smul_eq φ x hc

/-- Lelong numbers increase along the positive order: if `T = S + R` with `S, R` closed positive,
then `ν(S, x) ≤ ν(T, x)`. -/
theorem currentLelong_le_of_add [CompactSpace M]
    {S R T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hS : IsClosedPositiveCurrent S) (hR : IsClosedPositiveCurrent R)
    (hT : IsClosedPositiveCurrent T) (heq : T = S + R) (x : M) :
    currentLelong S hS x ≤ currentLelong T hT x := by
  subst heq
  rw [currentLelong_add hS hR hT x]
  exact le_self_add

/-- The Lelong numbers of the zero current vanish. -/
theorem currentLelong_zero [CompactSpace M] (x : M) :
    currentLelong (0 : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
      isClosedPositiveCurrent_zero x = 0 := by
  have h := currentLelong_add isClosedPositiveCurrent_zero isClosedPositiveCurrent_zero
    (by simpa only [add_zero] using
      (isClosedPositiveCurrent_zero (m := m) (M := M))) x
  have h' : currentLelong (0 + 0 : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
      (by simpa only [add_zero] using (isClosedPositiveCurrent_zero (m := m) (M := M))) x =
      currentLelong (0 : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
        isClosedPositiveCurrent_zero x := by
    congr 1
    exact add_zero 0
  rw [h'] at h
  have hfin := currentLelong_ne_top (isClosedPositiveCurrent_zero (m := m) (M := M)) x
  set a := currentLelong (0 : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    isClosedPositiveCurrent_zero x
  have : a + a = a + 0 := by rw [add_zero]; exact h.symm
  exact (ENNReal.add_right_inj hfin).mp this

/-! ### Lelong numbers of the current of a prime divisor -/

/-- The Lelong numbers of `[D]` are those of the weight `log |s_D|²_h` of any smooth metric `h`
on `𝒪(D)`. -/
theorem currentLelong_primeDivisorCurrent_eq [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hE : DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D) E) :
    currentLelong (primeDivisorCurrent D) (isClosedPositiveCurrent_primeDivisorCurrent D) =
      fun x => squaredLogLelongNumber (n := m + 1) E.weight x :=
  currentLelong_eq_of_eq_thetaPotentialCurrent _
    (primeDivisorCurrent_eq_thetaPotentialCurrent D E hE)

/-- `ν([D], x) = 0` at every point `x ∉ D`. -/
theorem currentLelong_primeDivisorCurrent_eq_zero [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) {x : M} (hx : x ∉ D.val) :
    currentLelong (primeDivisorCurrent D) (isClosedPositiveCurrent_primeDivisorCurrent D) x =
      0 := by
  have hspec := Classical.choose_spec (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))
  set E := Classical.choose (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))
  rw [currentLelong_primeDivisorCurrent_eq D E hspec.2]
  have hxE : x ∉ E.support := by
    rw [hspec.1, SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_support]
    exact hx
  have hpbot : E.weight x ≠ ⊥ := hxE
  have hnative : NonKahlerLocus.lelongNumber (n := m + 1) E.weight x = 0 := by
    by_contra hne
    exact hpbot (NonKahlerLocus.eq_bot_of_lelongNumber_pos (Nat.succ_pos m)
      (MeteredDivisorPositivity.thetaPlurisubharmonic_weight E)
      (pos_iff_ne_zero.mpr hne))
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  simpa only [mul_zero] using
    (lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m) E.weight x).symm.trans hnative

omit [IsComplexManifold (m + 1) M] in
/-- A function which is smooth in the charts on an open set is a bounded germ at its points. -/
theorem boundedRealGermAt_of_chartSmooth {V : Set M} (hV : IsOpen V) {h : M → ℝ}
    (hh : ∀ e : ComplexChart (m + 1) M,
      ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V))
    {x : M} (hx : x ∈ V) : BoundedRealGermAt h x := by
  let e := complexChartAt (n := m + 1) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hmem : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' V :=
    ⟨e.val.map_source hxs, by simpa only [mem_preimage, e.val.left_inv hxs] using hx⟩
  have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hV
  have hc : ContinuousAt (fun z => h (e.val.symm z)) (e.val x) :=
    ((hh e).continuousOn).continuousAt (hopen.mem_nhds hmem)
  obtain ⟨C, hC, hCb⟩ :=
    (boundedRealGermAt_of_continuousAt hc).comp_continuousAt (e.val.continuousAt hxs)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCb, e.val.open_source.mem_nhds hxs] with y hy hys
  simpa only [e.val.left_inv hys] using hy

/-- **`ν([D], x) ≥ 1` at every point of a prime divisor `D`**: locally `[D] = ddᶜ log |g|²` for a
local equation `g` of `D`, and `g(x) = 0`. -/
theorem one_le_currentLelong_primeDivisorCurrent [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) {x : M} (hx : x ∈ D.val) :
    1 ≤ currentLelong (primeDivisorCurrent D)
      (isClosedPositiveCurrent_primeDivisorCurrent D) x := by
  have hspec := Classical.choose_spec (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))
  set E := Classical.choose (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))
  have hE : DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D) E := hspec.2
  have hEsupp : E.support = D.val :=
    hspec.1.trans (SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_support D)
  rw [currentLelong_primeDivisorCurrent_eq D E hE]
  obtain ⟨V', hV', hxV', g, hg, -, h, hh, hweq⟩ := hE x
  have hxbot : E.weight x = ⊥ := by
    have : x ∈ E.support := by rw [hEsupp]; exact hx
    by_contra hne
    exact (show x ∉ E.support from hne) this
  have hb : BoundedRealGermAt h x := boundedRealGermAt_of_chartSmooth hV' hh hxV'
  have hrep : E.weight =ᶠ[𝓝 x] fun y => ((1 : ℝ) : EReal) *
      generatorLog (fun _ : Fin 1 => g) y + (h y : EReal) := by
    filter_upwards [hV'.mem_nhds hxV'] with y hy
    rw [hweq y hy, EReal.coe_one, one_mul]
  have hlow := AnalyticPoleLelongLowerBound.ofReal_two_mul_le_lelongNumber_of_local_presentation
    (u := E.weight) one_pos hV' hxV' (g := fun _ : Fin 1 => g) (fun _ => hg) hb hrep hxbot
  rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m), mul_one,
    ENNReal.ofReal_ofNat] at hlow
  have h2 : (2 : ℝ≥0∞) * 1 ≤ 2 * squaredLogLelongNumber (n := m + 1) E.weight x := by
    simpa only [mul_one] using hlow
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

/-- The generic Lelong number of `[D]` along `D` is positive (it is `≥ 1`). -/
theorem one_le_currentGenericLelong_primeDivisorCurrent [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    1 ≤ currentGenericLelong (primeDivisorCurrent D)
      (isClosedPositiveCurrent_primeDivisorCurrent D) D :=
  le_iInf₂ fun _ hx => one_le_currentLelong_primeDivisorCurrent D hx

end SGPT.Siu
