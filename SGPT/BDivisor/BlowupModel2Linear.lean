import SGPT.BDivisor.BlowupModel2Order
import SGPT.BDivisor.BlowupModelNef

/-!
# Linearity of `T ↦ 𝔻(T)`, `𝔻(ω)`, and `𝓘`-invariance

Source: the remarks after `def:DT` (chapter *The theory of b-divisors*): "if `T'` is another closed
positive `(1,1)`-current on `X` and `λ ≥ 0`, then `𝔻(T + T') = 𝔻(T) + 𝔻(T')`,
`𝔻(λT) = λ𝔻(T)`", and, in the proof of `thm:DT` (Step 1), "`𝔻(ω)` is the Cartier b-divisor
realized by `(X, {ω})`"; in the proof of `thm:bdiv_current_corr`, "this map clearly descends to
`𝒢(α)/∼_𝓘`".

* `currentGenericLelong_add`, `currentGenericLelong_smul`: generic Lelong numbers along prime
  divisors are additive and positively homogeneous (Siu's semicontinuity: almost generic points of
  two currents can be chosen simultaneously, `SGPT.Siu.exists_mem_lt_currentGenericLelong_add`);
* `siuRegularPart_add`, `siuRegularPart_smul`: `Reg(S + S') = Reg S + Reg S'`, `Reg(cS) = c Reg S`;
* `pull_add`, `pull_smul`: the pull-back of currents is additive and positively homogeneous;
* `currentBDivisorOn_add`, `currentBDivisorOn_smul`: **`𝔻(T + T') = 𝔻(T) + 𝔻(T')`,
  `𝔻(cT) = c𝔻(T)` (`c ≥ 0`)**;
* `currentBDivisorOn_smooth`: **for a closed semipositive smooth form `θ` (e.g. a Kähler form),
  `𝔻(θ)` is the Cartier b-divisor realized by `(X, {θ})`**;
* `currentBDivisorOn_eq_of_iEquivalent`: **`𝓘`-equivalent currents in the same class have the same
  b-divisor.**
* `currentBDivisorOn_isNef_of_forall_add`: Step 1 of the proof of `thm:DT` for nefness: if
  `𝔻(T + εθ)` is nef for `ε = 1/(k+1)`, `k ∈ ℕ`, then `𝔻(T)` is nef (`𝔻(T + εθ) = 𝔻(T) + ε𝔻(θ)`
  converges to `𝔻(T)` on every model).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology ContDiff Manifold ENNReal

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

namespace PrimePushforward

section Lelong

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [CompactSpace M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))

/-- **Additivity of generic Lelong numbers**: `ν(A + B, D) = ν(A, D) + ν(B, D)`. -/
theorem currentGenericLelong_add {A B : Cur} (hA : SGPT.Siu.IsClosedPositiveCurrent A)
    (hB : SGPT.Siu.IsClosedPositiveCurrent B) (hAB : SGPT.Siu.IsClosedPositiveCurrent (A + B))
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    SGPT.Siu.currentGenericLelong (A + B) hAB D =
      SGPT.Siu.currentGenericLelong A hA D + SGPT.Siu.currentGenericLelong B hB D := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    obtain ⟨x, hxD, hxA, hxB⟩ := SGPT.Siu.exists_mem_lt_currentGenericLelong_add hA hB D
      (half_pos hδ)
    calc SGPT.Siu.currentGenericLelong (A + B) hAB D
        ≤ SGPT.Siu.currentLelong (A + B) hAB x := SGPT.Siu.currentGenericLelong_le hAB D hxD
      _ = SGPT.Siu.currentLelong A hA x + SGPT.Siu.currentLelong B hB x :=
          SGPT.Siu.currentLelong_add hA hB hAB x
      _ ≤ (SGPT.Siu.currentGenericLelong A hA D + ENNReal.ofReal (δ / 2)) +
          (SGPT.Siu.currentGenericLelong B hB D + ENNReal.ofReal (δ / 2)) :=
          add_le_add hxA.le hxB.le
      _ = SGPT.Siu.currentGenericLelong A hA D + SGPT.Siu.currentGenericLelong B hB D + δ := by
          rw [add_add_add_comm, ← ENNReal.ofReal_add (by positivity) (by positivity),
            add_halves, ENNReal.ofReal_coe_nnreal]
  · refine le_iInf₂ fun x hx => ?_
    rw [SGPT.Siu.currentLelong_add hA hB hAB x]
    exact add_le_add (SGPT.Siu.currentGenericLelong_le hA D hx)
      (SGPT.Siu.currentGenericLelong_le hB D hx)

/-- **Homogeneity of generic Lelong numbers**: `ν(cA, D) = c ν(A, D)` for `c ≥ 0`. -/
theorem currentGenericLelong_smul {A : Cur} (hA : SGPT.Siu.IsClosedPositiveCurrent A) {c : ℝ}
    (hc : 0 ≤ c) (hcA : SGPT.Siu.IsClosedPositiveCurrent (c • A))
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    SGPT.Siu.currentGenericLelong (c • A) hcA D =
      ENNReal.ofReal c * SGPT.Siu.currentGenericLelong A hA D := by
  unfold SGPT.Siu.currentGenericLelong
  simp_rw [SGPT.Siu.currentLelong_smul hA hc hcA]
  rcases hc.lt_or_eq with hc' | hc'
  · rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hc').ne' ENNReal.ofReal_ne_top]
    congr 1
    funext x
    rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hc').ne' ENNReal.ofReal_ne_top]
  · subst hc'
    simp only [ENNReal.ofReal_zero, zero_mul]
    obtain ⟨x, hx⟩ := D.nonempty
    exact le_antisymm (iInf₂_le x hx) bot_le

/-- `Div(A + B) = Div A + Div B` for the divisorial parts of Siu's decomposition. -/
theorem siuDivisorialPart_add {A B : Cur} (hA : SGPT.Siu.IsClosedPositiveCurrent A)
    (hB : SGPT.Siu.IsClosedPositiveCurrent B) (hAB : SGPT.Siu.IsClosedPositiveCurrent (A + B)) :
    SGPT.Siu.siuDivisorialPart (A + B) hAB =
      SGPT.Siu.siuDivisorialPart A hA + SGPT.Siu.siuDivisorialPart B hB := by
  symm
  apply SGPT.Siu.eq_siuDivisorialPart_of_hasSum hAB
  intro e η
  have h := (SGPT.Siu.hasSum_siuDivisorialPart hA e η).add
    (SGPT.Siu.hasSum_siuDivisorialPart hB e η)
  convert h using 1
  · funext D
    rw [currentGenericLelong_add hA hB hAB D,
      ENNReal.toReal_add (SGPT.Siu.currentGenericLelong_ne_top hA D)
        (SGPT.Siu.currentGenericLelong_ne_top hB D), add_smul]
    rfl
  · rfl

/-- `Reg(A + B) = Reg A + Reg B`. -/
theorem siuRegularPart_add {A B : Cur} (hA : SGPT.Siu.IsClosedPositiveCurrent A)
    (hB : SGPT.Siu.IsClosedPositiveCurrent B) (hAB : SGPT.Siu.IsClosedPositiveCurrent (A + B)) :
    SGPT.Siu.siuRegularPart (A + B) hAB =
      SGPT.Siu.siuRegularPart A hA + SGPT.Siu.siuRegularPart B hB := by
  unfold SGPT.Siu.siuRegularPart
  rw [siuDivisorialPart_add hA hB hAB]
  abel

/-- `Div(cA) = c Div A` for `c ≥ 0`. -/
theorem siuDivisorialPart_smul {A : Cur} (hA : SGPT.Siu.IsClosedPositiveCurrent A) {c : ℝ}
    (hc : 0 ≤ c) (hcA : SGPT.Siu.IsClosedPositiveCurrent (c • A)) :
    SGPT.Siu.siuDivisorialPart (c • A) hcA = c • SGPT.Siu.siuDivisorialPart A hA := by
  symm
  apply SGPT.Siu.eq_siuDivisorialPart_of_hasSum hcA
  intro e η
  have h := (SGPT.Siu.hasSum_siuDivisorialPart hA e η).const_smul c
  have hf : (fun D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M =>
      ((SGPT.Siu.currentGenericLelong (c • A) hcA D).toReal •
        SGPT.Siu.primeDivisorCurrent D).inChart e η) = fun D => c • ((SGPT.Siu.currentGenericLelong A hA D).toReal •
          SGPT.Siu.primeDivisorCurrent D).inChart e η := by
    funext D
    rw [currentGenericLelong_smul hA hc hcA D, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
      mul_smul]
    rfl
  rw [hf]
  exact h

/-- `Reg(cA) = c Reg A` for `c ≥ 0`. -/
theorem siuRegularPart_smul {A : Cur} (hA : SGPT.Siu.IsClosedPositiveCurrent A) {c : ℝ}
    (hc : 0 ≤ c) (hcA : SGPT.Siu.IsClosedPositiveCurrent (c • A)) :
    SGPT.Siu.siuRegularPart (c • A) hcA = c • SGPT.Siu.siuRegularPart A hA := by
  unfold SGPT.Siu.siuRegularPart
  rw [siuDivisorialPart_smul hA hc hcA]
  module

/-- A non-divisorial current is its own regular part. -/
theorem siuRegularPart_eq_self {A : Cur} (hA : SGPT.Siu.IsClosedPositiveCurrent A)
    (hnd : ∀ D, SGPT.Siu.currentGenericLelong A hA D = 0) :
    SGPT.Siu.siuRegularPart A hA = A :=
  ((SGPT.Siu.isNonDivisorial_iff hA).mpr hnd).symm

end Lelong

section Pull

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

omit [CompactSpace X] [CompactSpace Y] in
theorem thetaPotentialCurrent_congr {θ θ' : SmoothRealForm (m + 1) Y 2} {u u' : Y → EReal}
    (hθ : θ = θ') (hu : u = u') (h : IsThetaPshPotential θ u) (h' : IsThetaPshPotential θ' u') :
    thetaPotentialCurrent θ u h = thetaPotentialCurrent θ' u' h' := by
  subst hθ hu
  rfl

/-- **The pull-back is additive**: `π^*(S + S') = π^*S + π^*S'`. -/
theorem pull_add {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) {S S' : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) (hS' : SGPT.Siu.IsClosedPositiveCurrent S')
    (hSS' : SGPT.Siu.IsClosedPositiveCurrent (S + S')) :
    Modification4.pull hπ (S + S') hSS' =
      Modification4.pull hπ S hS + Modification4.pull hπ S' hS' := by
  obtain ⟨θ, u, hu, hSeq⟩ := hS.exists_thetaPotential
  obtain ⟨σ, v, hv, hS'eq⟩ := hS'.exists_thetaPotential
  obtain ⟨huv, hsum⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu hv
  have hu' := isThetaPshPotential_comp_of_isAnalyticModification hπ θ hu
  have hv' := isThetaPshPotential_comp_of_isAnalyticModification hπ σ hv
  obtain ⟨huv', hsum'⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu' hv'
  rw [pull_eq_thetaPotentialCurrent hπ hSS' huv (by rw [hsum, hSeq, hS'eq]),
    pull_eq_thetaPotentialCurrent hπ hS hu hSeq, pull_eq_thetaPotentialCurrent hπ hS' hv hS'eq,
    ← hsum']
  exact thetaPotentialCurrent_congr (by rw [closedForm_pullback_add]) rfl _ _

/-- **The pull-back is positively homogeneous**: `π^*(cS) = c π^*S` for `c ≥ 0`. -/
theorem pull_smul {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) {c : ℝ} (hc : 0 ≤ c)
    (hcS : SGPT.Siu.IsClosedPositiveCurrent (c • S)) :
    Modification4.pull hπ (c • S) hcS = c • Modification4.pull hπ S hS := by
  obtain ⟨θ, u, hu, hSeq⟩ := hS.exists_thetaPotential
  obtain ⟨hcu, hsmul⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul hu hc
  have hu' := isThetaPshPotential_comp_of_isAnalyticModification hπ θ hu
  obtain ⟨hcu', hsmul'⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul hu' hc
  rw [pull_eq_thetaPotentialCurrent hπ hcS hcu (by rw [hsmul, hSeq]),
    pull_eq_thetaPotentialCurrent hπ hS hu hSeq, ← hsmul']
  exact thetaPotentialCurrent_congr (by rw [closedForm_pullback_smul]) rfl _ _

omit [CompactSpace Y] in
/-- `id^*S = S`. -/
theorem pull_id {S : CurX} (hS : SGPT.Siu.IsClosedPositiveCurrent S) :
    Modification4.pull (Modification.isAnalyticModification_id (n := m + 1) (X := X)) S hS = S := by
  obtain ⟨θ, u, hu, hSeq⟩ := hS.exists_thetaPotential
  rw [pull_eq_thetaPotentialCurrent _ hS hu hSeq, hSeq]
  exact SGPT.Okounkov.thetaPotentialCurrent_eq_of_geometricallyEq
    (SmoothRealForm.pullback_id_geometricallyEq θ.val) _ _

end Pull

end PrimePushforward

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

omit [CompactSpace X] in
/-- The class map is homogeneous. -/
theorem bottChernClass_smul' {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]
    (c : ℝ) (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (c • T) =
      c • bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T :=
  (bottChernClassLinearMap (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_smul c T

namespace Modification

theorem regPull_add (π : Modification (m + 1) X) {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hTT' : SGPT.Siu.IsClosedPositiveCurrent (T + T')) :
    π.regPull (T + T') hTT' = π.regPull T hT + π.regPull T' hT' := by
  unfold regPull
  have hP := Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT
  have hP' := Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT'
  rw [PrimePushforward.siuRegularPart_congr
      (PrimePushforward.pull_add π.isAnalyticModification hT hT' hTT') _ (hP.add hP'),
    PrimePushforward.siuRegularPart_add hP hP']

theorem regPull_smul (π : Modification (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) {c : ℝ} (hc : 0 ≤ c)
    (hcT : SGPT.Siu.IsClosedPositiveCurrent (c • T)) :
    π.regPull (c • T) hcT = c • π.regPull T hT := by
  unfold regPull
  have hP := Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT
  rw [PrimePushforward.siuRegularPart_congr
      (PrimePushforward.pull_smul π.isAnalyticModification hT hc hcT) _ (hP.smul hc),
    PrimePushforward.siuRegularPart_smul hP hc]

theorem regPullClass_add (π : Modification (m + 1) X) {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hTT' : SGPT.Siu.IsClosedPositiveCurrent (T + T')) :
    π.regPullClass (T + T') hTT' = π.regPullClass T hT + π.regPullClass T' hT' := by
  unfold regPullClass
  rw [← bottChernClass_add']
  congr 1
  exact Subtype.ext (π.regPull_add hT hT' hTT')

theorem regPullClass_smul (π : Modification (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) {c : ℝ} (hc : 0 ≤ c)
    (hcT : SGPT.Siu.IsClosedPositiveCurrent (c • T)) :
    π.regPullClass (c • T) hcT = c • π.regPullClass T hT := by
  unfold regPullClass
  rw [← bottChernClass_smul']
  congr 1
  exact Subtype.ext (π.regPull_smul hT hc hcT)

end Modification

/-- **`𝔻(T + T') = 𝔻(T) + 𝔻(T')`** (the remark after `def:DT`). -/
theorem currentBDivisorOn_add (S : ModelSystem (m + 1) X) {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hTT' : SGPT.Siu.IsClosedPositiveCurrent (T + T')) :
    currentBDivisorOn S (T + T') hTT' = currentBDivisorOn S T hT + currentBDivisorOn S T' hT' :=
  WeilBDivisorOn.ext fun π => π.1.regPullClass_add hT hT' hTT'

/-- **`𝔻(cT) = c𝔻(T)`** for `c ≥ 0` (the remark after `def:DT`). -/
theorem currentBDivisorOn_smul (S : ModelSystem (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) {c : ℝ} (hc : 0 ≤ c)
    (hcT : SGPT.Siu.IsClosedPositiveCurrent (c • T)) :
    currentBDivisorOn S (c • T) hcT = c • currentBDivisorOn S T hT :=
  WeilBDivisorOn.ext fun π => π.1.regPullClass_smul hT hc hcT

/-- **`𝔻(θ)` for a closed semipositive smooth form `θ`** (e.g. `𝔻(ω)` for a Kähler form): the
Cartier b-divisor realized by `(X, {θ})`. On every model, `π^*θ` is smooth, hence has vanishing
Lelong numbers and is its own regular part, with class `π^*{θ}`. -/
theorem currentBDivisorOn_smooth (S : ModelSystem (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    (hθ : IsThetaPshPotential θ.val (fun _ => (0 : EReal))) :
    currentBDivisorOn S (thetaPotentialCurrent θ.val (fun _ => 0) hθ)
        (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hθ) =
      WeilBDivisorOn.cartierOf (Nat.succ_pos m) ModelSystem.Model.root
        (RealBottChern.ofRepresentative θ) := by
  have hT := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hθ
  apply WeilBDivisorOn.IsRealization.eq_cartierOf
  intro π _
  rw [currentBDivisorOn_onModel]
  refine Eq.trans ?_
    (Modification.classPullbackOfLE_root π.1 (RealBottChern.ofRepresentative θ)).symm
  have hpull := PrimePushforward.pull_eq_thetaPotentialCurrent π.1.isAnalyticModification hT hθ rfl
  have hP := Modification4.isClosedPositiveCurrent_pull π.1.isAnalyticModification hT
  have hnd : ∀ D, SGPT.Siu.currentGenericLelong
      (Modification4.pull π.1.isAnalyticModification _ hT) hP D = 0 := by
    intro D
    obtain ⟨x, hx⟩ := D.nonempty
    refine le_antisymm ((SGPT.Siu.currentGenericLelong_le hP D hx).trans (le_of_eq ?_)) bot_le
    rw [SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent hP hpull]
    exact SGPT.Okounkov.squaredLogLelongNumber_zero x
  have hreg : π.1.regPull _ hT = thetaPotentialCurrent
      (ClosedRealOneOneForm.pullback π.1.isAnalyticModification.1 θ).val (fun _ => 0)
      (isThetaPshPotential_comp_of_isAnalyticModification π.1.isAnalyticModification θ hθ) :=
    (PrimePushforward.siuRegularPart_eq_self hP hnd).trans hpull
  unfold Modification.regPullClass
  have hsub : (⟨π.1.regPull _ hT, (π.1.isClosedPositiveCurrent_regPull hT).1,
      (π.1.isClosedPositiveCurrent_regPull hT).2.1⟩ :
        ClosedOneOneCurrent (M := π.1.carrier) (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
      thetaClosedCurrent (ClosedRealOneOneForm.pullback π.1.isAnalyticModification.1 θ)
        (fun _ => 0)
        (isThetaPshPotential_comp_of_isAnalyticModification π.1.isAnalyticModification θ hθ) :=
    Subtype.ext hreg
  rw [hsub, bottChernClass_thetaClosedCurrent, classPullback_ofRepresentative]

/-- **The root of `𝔻(T)` is `{Reg T}`.** -/
theorem currentBDivisorOn_root (S : ModelSystem (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    (currentBDivisorOn S T hT).root = bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨SGPT.Siu.siuRegularPart T hT, (SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hT).1,
        (SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hT).2.1⟩ := by
  unfold WeilBDivisorOn.root
  rw [currentBDivisorOn_onModel]
  unfold Modification.regPullClass
  congr 1
  apply Subtype.ext
  exact PrimePushforward.siuRegularPart_congr (PrimePushforward.pull_id hT) _ _

/-- For a non-divisorial `T` (`T = Reg T`), the root of `𝔻(T)` is `{T}`. -/
theorem currentBDivisorOn_root_of_nonDivisorial (S : ModelSystem (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hnd : SGPT.Siu.IsNonDivisorial T hT) :
    (currentBDivisorOn S T hT).root =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩ := by
  rw [currentBDivisorOn_root]
  congr 1
  exact Subtype.ext hnd.symm

/-- **`𝓘`-equivalent currents in the same class have the same b-divisor** (the descent of
`T ↦ 𝔻(T)` to `𝓘`-equivalence classes in the proof of `thm:bdiv_current_corr`). -/
theorem currentBDivisorOn_eq_of_iEquivalent (S : ModelSystem (m + 1) X) {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T', hT'.1, hT'.2.1⟩)
    (hI : SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T T')
    (hI' : SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T' T) :
    currentBDivisorOn S T hT = currentBDivisorOn S T' hT' := by
  obtain ⟨θ, σ, u, v, hu, hv, hTeq, hT'eq, huv⟩ := hI
  obtain ⟨σ', θ', v', u', hv', hu', hT'eq', hTeq', hvu⟩ := hI'
  ext π
  rw [currentBDivisorOn_onModel, currentBDivisorOn_onModel, π.1.regPullClass_eq hT,
    π.1.regPullClass_eq hT', hclass]
  congr 1
  unfold Modification.divPullClass
  congr 1
  apply Subtype.ext
  change SGPT.Siu.siuDivisorialPart _ _ = SGPT.Siu.siuDivisorialPart _ _
  have hP := Modification4.isClosedPositiveCurrent_pull π.1.isAnalyticModification hT
  have hP' := Modification4.isClosedPositiveCurrent_pull π.1.isAnalyticModification hT'
  have hν : ∀ D, SGPT.Siu.currentGenericLelong _ hP D = SGPT.Siu.currentGenericLelong _ hP' D :=
    fun D => le_antisymm
      (PrimePushforward.currentGenericLelong_pull_le_of_iOrder π.1.isAnalyticModification
        hT' hT hv' hu' hT'eq' hTeq' hvu D)
      (PrimePushforward.currentGenericLelong_pull_le_of_iOrder π.1.isAnalyticModification
        hT hT' hu hv hTeq hT'eq huv D)
  symm
  apply SGPT.Siu.eq_siuDivisorialPart_of_hasSum hP
  intro e η
  convert SGPT.Siu.hasSum_siuDivisorialPart hP' e η using 1
  funext D
  rw [hν D]

/-- **Step 1 of the proof of `thm:DT`, nefness part**: for a closed semipositive smooth form `θ`
(e.g. a Kähler form), if `𝔻(T + εθ)` is nef for every `ε = 1/(k+1)`, then `𝔻(T)` is nef. Indeed
`𝔻(T + εθ) = 𝔻(T) + ε𝔻(θ)` (Proposition on linearity) converges to `𝔻(T)` on every model, and
limits of nef b-divisors are nef. -/
theorem currentBDivisorOn_isNef_of_forall_add (S : ModelSystem (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (θ : ClosedRealOneOneForm (m + 1) X)
    (hθ : IsThetaPshPotential θ.val (fun _ => (0 : EReal)))
    (h : ∀ (k : ℕ) (hk : SGPT.Siu.IsClosedPositiveCurrent
        (T + (1 / ((k : ℝ) + 1)) • thetaPotentialCurrent θ.val (fun _ => 0) hθ)),
      (currentBDivisorOn S _ hk).IsNef) :
    (currentBDivisorOn S T hT).IsNef := by
  have hω := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hθ
  have hc : ∀ k : ℕ, (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hk : ∀ k : ℕ, SGPT.Siu.IsClosedPositiveCurrent
      (T + (1 / ((k : ℝ) + 1)) • thetaPotentialCurrent θ.val (fun _ => 0) hθ) :=
    fun k => hT.add (hω.smul (hc k))
  apply WeilBDivisorOn.IsNef.of_converges (fun k : ℕ => h k (hk k))
  rw [WeilBDivisorOn.converges_iff_forall_dual]
  intro π f
  have heq : ∀ k : ℕ, (currentBDivisorOn S _ (hk k)).onModel π =
      (currentBDivisorOn S T hT).onModel π +
        (1 / ((k : ℝ) + 1)) • (currentBDivisorOn S _ hω).onModel π := by
    intro k
    rw [currentBDivisorOn_add S hT (hω.smul (hc k)) (hk k), WeilBDivisorOn.add_onModel,
      currentBDivisorOn_smul S hω (hc k), WeilBDivisorOn.smul_onModel]
  simp_rw [heq, map_add, map_smul, smul_eq_mul]
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.add (h0.mul_const (f ((currentBDivisorOn S _ hω).onModel π)))

end SGPT.BDivisor
