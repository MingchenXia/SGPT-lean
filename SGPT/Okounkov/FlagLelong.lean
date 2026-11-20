import SGPT.Okounkov.SmoothFlags
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.LelongNumberAdditivity
import SGPT.Foundations.Analysis.Pending.SourceGenericPrimeIdealOrder
import SGPT.Foundations.Analysis.Pending.ActualLelongAdditivity
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Foundations.Analysis.Pending.QuasiPshLelongUpperSemicontinuity

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The actual independently defined original squared-logarithmic generic reader. -/
def flagGenericLelong (Y : Fin (n + 1) → Set X) (u : X → EReal)
    (i : Fin (n + 1)) : ℝ≥0∞ :=
  sourceGenericLelongNumber (n := n) (Subtype.val : Y i → X) u

/-- Genuine source nondegeneracy supplies finiteness on every original
closed connected smooth carrier, including whole primes on modifications. -/
theorem sourceGeneric_subtype_ne_top {W : Set X} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) {u : X → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) :
    sourceGenericLelongNumber (n := n) (Subtype.val : W → X) u ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hW.2.1.nonempty
  cases n with
  | zero =>
      let : Nonempty W := ⟨⟨x, hx⟩⟩
      simpa only [sourceGenericLelongNumber_zero_dimension rfl (Subtype.val : W → X) u] using
        (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)
  | succ m =>
      have hfinite : squaredLogLelongNumber (n := m + 1) u x ≠ ⊤ := by
        intro htop
        apply LelongNumberAdditivity.lelongNumber_ne_top (Nat.succ_pos m) hu.1 hu.2 x
        rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m), htop]
        norm_num
      exact ne_top_of_le_ne_top hfinite (iInf_le _ (⟨x, hx⟩ : W))

/-- The original flag reader retains the genuine finite whole-carrier value. -/
theorem IsSmoothFlag.flagGenericLelong_ne_top {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (i : Fin (n + 1)) : flagGenericLelong Y u i ≠ ⊤ :=
  sourceGeneric_subtype_ne_top (hY.2.2 i) hu

/-- The source real generic coefficient retains its true finite extended value. -/
def flagLelongCoefficient (Y : Fin (n + 1) → Set X) (u : X → EReal)
    (i : Fin (n + 1)) : ℝ :=
  (flagGenericLelong Y u i).toReal

omit [IsComplexManifold n X] in
theorem flagLelongCoefficient_nonneg (Y : Fin (n + 1) → Set X) (u : X → EReal)
    (i : Fin (n + 1)) : 0 ≤ flagLelongCoefficient Y u i :=
  ENNReal.toReal_nonneg

/-- No infinite generic value is discarded by the original real coefficient. -/
theorem IsSmoothFlag.ofReal_flagLelongCoefficient {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (i : Fin (n + 1)) :
    ENNReal.ofReal (flagLelongCoefficient Y u i) = flagGenericLelong Y u i :=
  ENNReal.ofReal_toReal (hY.flagGenericLelong_ne_top hu i)

/-- Existing main source generic-minimum attainment applies to the original flag carrier. -/
theorem IsSmoothFlag.exists_flagLelongCoefficient_point {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (i : Fin (n + 1)) : ∃ x ∈ Y i,
      squaredLogLelongNumber (n := n) u x = ENNReal.ofReal (flagLelongCoefficient Y u i) := by
  obtain ⟨x, hx⟩ := SourceGenericSubmanifoldMinimum.exists_sourceGeneric_subtype_minimum
    hu.1 (hY.2.2 i)
  exact ⟨x, x.property, hx.trans (hY.ofReal_flagLelongCoefficient hu i).symm⟩

/-- The actual identity modification has empty exceptional loci. -/
theorem isAnalyticModification_identity :
    AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) (id : X → X) := by
  refine ⟨contMDiff_id, isProperMap_id, ∅, ∅, id, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, ?_, contMDiff_id.contMDiffOn,
    (fun _ _ => rfl), (fun _ _ => rfl)⟩
  exact preimage_empty

/-- Original all-level ideal order compares the same actual smooth hypersurface
through main's genuine whole-prime criterion and the identity modification. -/
theorem sourceGeneric_subtype_le_of_iOrder {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    {u v : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (hv : IsGlobalQuasiPshPotential (n := m + 1) v)
    (hI : IOrderOnManifold (n := m + 1) u v) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v ≤
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u := by
  rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf,
    SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf]
  simpa only [id_eq] using
    (SourceGenericPrimeIdealOrder.iOrder_iff_all_source_prime_orders hu.1 hv).mp hI
      M id isAnalyticModification_identity W hW.1 hW.2.1 ⟨m, rfl, hW.2.2⟩

/-- The literal source generic first coefficient depends only on original
multiplier-ideal equivalence, with no assumed Lelong comparison. -/
theorem sourceGeneric_subtype_eq_of_iEquivalent {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    {u v : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (hv : IsGlobalQuasiPshPotential (n := m + 1) v)
    (hI : IEquivalentOnManifold (n := m + 1) u v) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u =
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v :=
  le_antisymm (sourceGeneric_subtype_le_of_iOrder hW hv hu hI.2)
    (sourceGeneric_subtype_le_of_iOrder hW hu hv hI.1)

/-- Actual native additivity transports to the independently defined source reader. -/
theorem squaredLogLelongNumber_add_eq {u v : X → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) (x : X) :
    squaredLogLelongNumber (n := n) (fun y => u y + v y) x =
      squaredLogLelongNumber (n := n) u x + squaredLogLelongNumber (n := n) v x := by
  by_cases hn : n = 0
  · simp [squaredLogLelongNumber, hn]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn, mul_add,
    ← lelongNumber_eq_two_mul_squaredLog hn, ← lelongNumber_eq_two_mul_squaredLog hn]
  exact ActualLelongAdditivity.lelongNumber_add_eq hu hv x

omit [IsComplexManifold n X] in
/-- Source point readers retain the actual positive homogeneity, including poles. -/
theorem squaredLogLelongNumber_smul_eq (u : X → EReal) (x : X) {c : ℝ} (hc : 0 < c) :
    squaredLogLelongNumber (n := n) (fun y => (c : EReal) * u y) x =
      ENNReal.ofReal c * squaredLogLelongNumber (n := n) u x := by
  by_cases hn : n = 0
  · simp [squaredLogLelongNumber, hn]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn, mul_left_comm 2,
    ← lelongNumber_eq_two_mul_squaredLog hn]
  exact ActualLelongPositiveScaling.lelongNumber_smul_eq hc

/-- Main's true point Lelong upper semicontinuity preserves the source factor two. -/
theorem upperSemicontinuous_squaredLogLelongNumber {u : X → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) :
    UpperSemicontinuous (squaredLogLelongNumber (n := n) u) := by
  by_cases hn : n = 0
  · have hfun : squaredLogLelongNumber (n := n) u = (fun _ : X => (0 : ℝ≥0∞)) :=
      funext fun _ => by simp [squaredLogLelongNumber, hn]
    rw [hfun]
    exact upperSemicontinuous_const
  intro x b hb
  have hnative : SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus.lelongNumber (n := n) u x < 2 * b := by
    rw [lelongNumber_eq_two_mul_squaredLog hn]
    exact (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).mpr hb
  filter_upwards [QuasiPshLelongUpperSemicontinuity.upperSemicontinuous_lelongNumber hu x (2 * b) hnative]
    with y hy
  rw [lelongNumber_eq_two_mul_squaredLog hn] at hy
  exact (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).mp hy

/-- Genuine source minimum attainment on every open carrier piece, together with
actual point USC, produces generic additivity without a common-minimum certificate. -/
theorem sourceGeneric_subtype_add_eq {W : Set X} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) {u v : X → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    sourceGenericLelongNumber (n := n) (Subtype.val : W → X) (fun y => u y + v y) =
      sourceGenericLelongNumber (n := n) (Subtype.val : W → X) u +
        sourceGenericLelongNumber (n := n) (Subtype.val : W → X) v := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hsum
    obtain ⟨x, hx⟩ := SourceGenericSubmanifoldMinimum.exists_sourceGeneric_subtype_minimum
      hu.1 hW
    let O : Set X := {y | squaredLogLelongNumber (n := n) u y <
      sourceGenericLelongNumber (n := n) (Subtype.val : W → X) u + ε}
    have hO : IsOpen O := (upperSemicontinuous_squaredLogLelongNumber hu.1).isOpen_preimage _
    have hxO : (x : X) ∈ O := by
      change squaredLogLelongNumber (n := n) u x <
        sourceGenericLelongNumber (n := n) (Subtype.val : W → X) u + ε
      rw [hx]
      exact ENNReal.lt_add_right (sourceGeneric_subtype_ne_top hW hu)
        (by exact_mod_cast hε.ne')
    obtain ⟨V, hV, _⟩ := SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold
      hW
    obtain ⟨y, hy, hmin⟩ := SourceGenericPrimeIdealOrder.exists_source_minimum_on_open_piece
      hv.1 V hO ⟨x, by simpa only [hV] using x.property, hxO⟩
    have hyW : y ∈ W := by simpa only [hV] using hy.1
    have hminv : squaredLogLelongNumber (n := n) v y =
        sourceGenericLelongNumber (n := n) (Subtype.val : W → X) v := by
      rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf]
      simpa only [hV] using hmin
    calc
      sourceGenericLelongNumber (n := n) (Subtype.val : W → X) (fun z => u z + v z) ≤
          squaredLogLelongNumber (n := n) (fun z => u z + v z) y :=
        iInf_le _ (⟨y, hyW⟩ : W)
      _ = squaredLogLelongNumber (n := n) u y + squaredLogLelongNumber (n := n) v y :=
        squaredLogLelongNumber_add_eq hu.1 hv.1 y
      _ ≤ (sourceGenericLelongNumber (n := n) (Subtype.val : W → X) u + ε) +
          sourceGenericLelongNumber (n := n) (Subtype.val : W → X) v :=
        add_le_add hy.2.le hminv.le
      _ = _ := by ac_rfl
  · change _ ≤ ⨅ y : W, squaredLogLelongNumber (n := n) (fun z => u z + v z) y
    apply le_iInf
    intro y
    rw [squaredLogLelongNumber_add_eq hu.1 hv.1]
    exact add_le_add (iInf_le _ y) (iInf_le _ y)

/-- The genuine carrier arithmetic applies to every original flag level. -/
theorem IsSmoothFlag.flagGenericLelong_add_eq {Y : Fin (n + 1) → Set X}
    (hY : IsSmoothFlag Y) {u v : X → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) (i : Fin (n + 1)) :
    flagGenericLelong Y (fun y => u y + v y) i =
      flagGenericLelong Y u i + flagGenericLelong Y v i :=
  sourceGeneric_subtype_add_eq (hY.2.2 i) hu hv

omit [IsComplexManifold n X] in
/-- Actual whole-level infima preserve original positive scaling. -/
theorem flagGenericLelong_smul_eq (Y : Fin (n + 1) → Set X) (u : X → EReal)
    (i : Fin (n + 1)) {c : ℝ} (hc : 0 < c) :
    flagGenericLelong Y (fun y => (c : EReal) * u y) i =
      ENNReal.ofReal c * flagGenericLelong Y u i := by
  unfold flagGenericLelong sourceGenericLelongNumber
  simp_rw [squaredLogLelongNumber_smul_eq u _ hc,
    ← ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top]

/-- The source zero reader follows from genuine finiteness and actual positive
scaling, without a second logarithmic-growth calculation. -/
theorem squaredLogLelongNumber_zero (x : X) :
    squaredLogLelongNumber (n := n) (fun _ : X => (0 : EReal)) x = 0 := by
  by_cases hn : n = 0
  · simp [squaredLogLelongNumber, hn]
  have hfinite : squaredLogLelongNumber (n := n) (fun _ : X => (0 : EReal)) x ≠ ⊤ := by
    intro htop
    have hu := isGlobalQuasiPshPotential_const (n := n) (M := X) 0
    have hnative : lelongNumber (n := n) (fun _ : X => (0 : EReal)) x ≠ ⊤ := by
      simpa only [EReal.coe_zero] using
        LelongNumberAdditivity.lelongNumber_ne_top (Nat.pos_of_ne_zero hn) hu.1 hu.2 x
    apply hnative
    rw [lelongNumber_eq_two_mul_squaredLog hn, htop]
    norm_num
  have hscale := squaredLogLelongNumber_smul_eq (n := n)
    (fun _ : X => (0 : EReal)) x (c := 2) (by norm_num)
  have hreal := congrArg ENNReal.toReal hscale
  have hzero : (squaredLogLelongNumber (n := n) (fun _ : X => (0 : EReal)) x).toReal = 0 := by
    norm_num [ENNReal.toReal_mul] at hreal
    linarith
  exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hfinite

/-- Original nonnegative scaling includes its genuine zero endpoint. -/
theorem squaredLogLelongNumber_nonneg_smul_eq (u : X → EReal) (x : X)
    {c : ℝ} (hc : 0 ≤ c) :
    squaredLogLelongNumber (n := n) (fun y => (c : EReal) * u y) x =
      ENNReal.ofReal c * squaredLogLelongNumber (n := n) u x := by
  rcases eq_or_lt_of_le hc with h | h
  · subst c
    simpa using squaredLogLelongNumber_zero (n := n) x
  · exact squaredLogLelongNumber_smul_eq u x h

/-- The actual nonempty carrier prevents an empty-infimum exception at zero. -/
theorem sourceGeneric_subtype_zero {W : Set X} (hW : W.Nonempty) :
    sourceGenericLelongNumber (n := n) (Subtype.val : W → X)
      (fun _ : X => (0 : EReal)) = 0 := by
  obtain ⟨x, hx⟩ := hW
  let : Nonempty W := ⟨⟨x, hx⟩⟩
  simp [sourceGenericLelongNumber, squaredLogLelongNumber_zero]

/-- Every original smooth flag level retains the full nonnegative source scaling. -/
theorem IsSmoothFlag.flagGenericLelong_nonneg_smul_eq
    {Y : Fin (n + 1) → Set X} (hY : IsSmoothFlag Y) (u : X → EReal)
    (i : Fin (n + 1)) {c : ℝ} (hc : 0 ≤ c) :
    flagGenericLelong Y (fun y => (c : EReal) * u y) i =
      ENNReal.ofReal c * flagGenericLelong Y u i := by
  rcases eq_or_lt_of_le hc with h | h
  · subst c
    simpa only [EReal.coe_zero, EReal.zero_mul, ENNReal.ofReal_zero, zero_mul,
      flagGenericLelong] using sourceGeneric_subtype_zero (hY.2.2 i).2.1.nonempty
  · exact flagGenericLelong_smul_eq Y u i h

end SGPT.Okounkov
