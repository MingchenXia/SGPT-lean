import SGPT.BDivisor.BlowupModelCurrent
import SGPT.Foundations.Analysis.Pending.ActualFiniteDivisorCurrentOffSupport
import SGPT.Foundations.Analysis.Pending.MeteredDivisorOperations
import SGPT.Foundations.Analysis.Pending.AnalyticModelDomination
import SGPT.Foundations.Analysis.Pending.ProperImageAnalyticInterface

/-!
# Push-forward of currents of integration along modifications

Source: the compatibility claim after `def:DT` (chapter *The theory of b-divisors*), which uses
"`g_* Reg(g^*S) = Reg(S)` by Siu's decomposition and `lma:Siudec_pullpush`"; the proof needs the
push-forward of the currents of integration of prime divisors (Xia, *Foundations of
pluripotential theory*, `lem:nondivisorial-pull-push-exceptional`, third statement: "for a prime
divisor `E` on `Y`, `π_*[E] = 0` if `E` is exceptional, and `π_*[E] = [π(E)]` otherwise") and the
description of the non-exceptional prime divisors as strict transforms (FPT, the paragraph before
`prop:positivity-under-modifications`).

Let `π : Y → X` be a modification of compact complex manifolds (`IsAnalyticModification`).

* `currentEqOn_integrationCurrent_zero`, `currentEqOn_primeDivisorCurrent_zero`: the current of
  integration of a metered divisor (of a prime divisor `D`) vanishes off its support (off `D`).
* `currentEqOn_pull_primeDivisorCurrent_zero`: `π^*[D]` vanishes off `π⁻¹ D` (it is the current of
  integration of the pulled-back metered divisor).
* `currentEqOn_currentPushforward_zero`: if `T` vanishes on `π⁻¹ O`, then `π_*T` vanishes on
  `O ∖ π(Exc π)` (the push-forward is the transport over the isomorphism locus).
* `currentPushforward_primeDivisorCurrent_eq_zero`: **`π_*[E] = 0` for a `π`-exceptional prime
  divisor `E`** (contained in the exceptional locus).
* `currentGenericLelong_primeDivisorCurrent_self`: `ν([D], D) = 1`.
* `pull_primeDivisorCurrent_eq`: `π^*[D] = [D̃] + ∑_E c_E [E]` (`D̃` the strict transform, `E`
  exceptional, finitely many).
* `currentPushforward_primeDivisorCurrent_strictTransformPrime`: **`π_*[D̃] = [D]`**.
* `exists_eq_strictTransformPrime`: **every non-exceptional prime divisor `D'` of `Y` is the
  strict transform of the prime divisor `π(D')` of `X`** (Remmert's proper mapping theorem and a
  dimension count at a regular point over the isomorphism locus).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold

namespace SGPT.BDivisor.PrimePushforward

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalCurrents
  SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor SGPT.NPP.MassPushforward SGPT.Currents.AnalyticSupport

/-! ### Currents of integration vanish off their supports -/

section Vanishing

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))

theorem currentEqOn_mono {S T : Cur} {O O' : Set M} (h : CurrentEqOn S T O) (hO : O' ⊆ O) :
    CurrentEqOn S T O' :=
  fun e z hz hzO => h e z hz (hO hzO)

/-- The current of integration `[F] = Θ_F + ddᶜψ_F` of a metered effective `ℚ`-divisor vanishes
off the support of `F` (the pole set of `ψ_F`). -/
theorem currentEqOn_integrationCurrent_zero (F : MeteredEffectiveQDivisor (m + 1) M) :
    CurrentEqOn (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) F) 0
      F.supportᶜ := by
  intro e z hz hzF
  have hxe : e.val.symm z ∈ e.val.source := e.val.map_target hz
  obtain ⟨r, hr, hW, hj, -⟩ :=
    ActualFiniteDivisorCurrentOffSupport.exists_ball_finite_divisor_current_restrict_zero
      (canonicalBasis (m + 1)) (fun _ : Fin 1 => F) (fun _ => (1 : ℝ)) (x := e.val.symm z)
      (fun _ => hzF) e hxe
  refine ⟨⟨Metric.ball (e.val (e.val.symm z)) r, Metric.isOpen_ball⟩, ?_, hW, ?_⟩
  · change z ∈ Metric.ball (e.val (e.val.symm z)) r
    rw [e.val.right_inv hz]
    exact Metric.mem_ball_self hr
  · rw [(hj 0).2]
    ext
    rfl

/-- `θ + ddᶜψ = [F]` for the curvature `θ` and weight `ψ` of a metered divisor `F`. -/
theorem thetaPotentialCurrent_eq_integrationCurrent (F : MeteredEffectiveQDivisor (m + 1) M)
    (hF : IsThetaPshPotential F.curvature.val F.weight) :
    thetaPotentialCurrent F.curvature.val F.weight hF =
      integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) F := by
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  simp only [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
    coefficients_smoothGlobalCurrent, globalDDC_coefficients, coefficients_integrationCurrent]
  exact add_comm _ _

variable [CompactSpace M]

/-- The chosen metered divisor of the current `[D]` has support `D`. -/
theorem support_primeDivisorMetric (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    (Classical.choose (DivisorMetric.exists_divisorMetric
      (SGPT.Siu.primeEffectiveDivisor D))).support = D.val :=
  (Classical.choose_spec (DivisorMetric.exists_divisorMetric
    (SGPT.Siu.primeEffectiveDivisor D))).1.trans
      (SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_support D)

/-- **`[D]` vanishes off `D`.** -/
theorem currentEqOn_primeDivisorCurrent_zero (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    CurrentEqOn (SGPT.Siu.primeDivisorCurrent D) 0 D.valᶜ := by
  have h := currentEqOn_integrationCurrent_zero
    (Classical.choose (DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor D)))
  rw [support_primeDivisorMetric] at h
  exact h

omit [CompactSpace M] in
/-- A prime divisor has empty interior. -/
theorem interior_primeCarrier_eq_empty (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    interior P.val = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hreg : RegularAtDim (n := m + 1) P.val x (m + 1) :=
    EmbeddedFromResolution.regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  rw [← P.subvariety_carrier] at hreg
  have h1 := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim P.subvariety hreg
  have h2 := P.subvariety_codimension
  omega

omit [CompactSpace M] in
/-- A prime divisor not contained in an analytic set `A` is the closure of its part off `A`. -/
theorem primeCarrier_subset_closure_diff (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) M)
    {A : Set M} (hA : IsComplexAnalyticSubset (n := m + 1) A) (hPA : ¬ P.val ⊆ A) :
    P.val ⊆ closure (P.val \ A) := by
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  by_contra hcon
  have hsub : P.val ∩ O ⊆ P.val ∩ A := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    by_contra hyA
    exact hcon ⟨y, hy.2, hy.1, hyA⟩
  have heq := ClosureDifferenceAnalytic.eq_of_subset_of_inter_open_subset
    ((SGPT.Siu.isComplexAnalyticSubset_primeCarrier P).inter hA)
    (SGPT.Siu.isIrreducible_primeCarrier P) inter_subset_left hO ⟨x, hx, hxO⟩ hsub
  exact hPA fun y hy => (heq.symm ▸ hy : y ∈ P.val ∩ A).2

/-- **`ν([D], D) = 1`.**  By Siu's lemma `[D] - ν([D], D)[D] ≥ 0`; if `ν([D], D) > 1`, the
current `(ν([D], D) - 1)[D]` would be positive with positive negative, hence zero, while
`ν([D], x) ≥ 1` on `D`. -/
theorem currentGenericLelong_primeDivisorCurrent_self
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    SGPT.Siu.currentGenericLelong (SGPT.Siu.primeDivisorCurrent D)
      (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D) D = 1 := by
  have hD := SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D
  set ν := SGPT.Siu.currentGenericLelong (SGPT.Siu.primeDivisorCurrent D) hD D with hνdef
  have h1 : 1 ≤ ν := SGPT.Siu.one_le_currentGenericLelong_primeDivisorCurrent D
  have hfin : ν ≠ ⊤ := SGPT.Siu.currentGenericLelong_ne_top hD D
  set c := ν.toReal with hcdef
  have hc1 : 1 ≤ c := by
    have := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hfin).mpr h1
    simpa using this
  suffices hc : c ≤ 1 by
    have hc' : c = 1 := le_antisymm hc hc1
    rw [← ENNReal.ofReal_toReal hfin, ← hcdef, hc', ENNReal.ofReal_one]
  by_contra hlt
  push Not at hlt
  have hsub := SGPT.Siu.isClosedPositiveCurrent_sub_currentGenericLelong_smul hD D
  have hpos : SGPT.Siu.IsClosedPositiveCurrent ((c - 1) • SGPT.Siu.primeDivisorCurrent D) :=
    hD.smul (by linarith)
  have hneg : -((c - 1) • SGPT.Siu.primeDivisorCurrent D) =
      SGPT.Siu.primeDivisorCurrent D - c • SGPT.Siu.primeDivisorCurrent D := by
    module
  have h0 := eq_zero_of_isFullPositive_of_neg hpos (by rw [hneg]; exact hsub.2.2)
  have hD0 : SGPT.Siu.primeDivisorCurrent D = 0 := by
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd h (by linarith)
    · exact h
  obtain ⟨x, hx⟩ := D.nonempty
  have key : ∀ (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
      (hT : SGPT.Siu.IsClosedPositiveCurrent T), T = 0 → SGPT.Siu.currentLelong T hT x = 0 := by
    rintro T hT rfl
    exact SGPT.Siu.currentLelong_zero x
  have h2 := SGPT.Siu.one_le_currentLelong_primeDivisorCurrent D hx
  rw [key _ _ hD0] at h2
  exact absurd h2 (by norm_num)

end Vanishing

/-! ### Pull-back and push-forward along a modification -/

section Modification

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurY" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))
local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))
local notation "PrimeX" => SGPT.PSH.GeometricPrimeCarrier (m + 1) X
local notation "PrimeY" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y

/-- The chosen metered divisor of `[D]`. -/
abbrev primeMetric (D : PrimeX) : MeteredEffectiveQDivisor (m + 1) X :=
  Classical.choose (DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor D))

/-- **`π^*[D]` is the current of integration of the pulled-back metered divisor.** -/
theorem pull_primeDivisorCurrent {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (D : PrimeX) :
    Modification4.pull hπ (SGPT.Siu.primeDivisorCurrent D)
        (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D) =
      integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (MeteredDivisorOperations.pullback hπ.1
          (Modification4.interior_exceptionalLocus_eq_empty hπ) (primeMetric D)) := by
  have hE : DivisorMetric.IsDivisorMetric (SGPT.Siu.primeEffectiveDivisor D) (primeMetric D) :=
    (Classical.choose_spec (DivisorMetric.exists_divisorMetric
      (SGPT.Siu.primeEffectiveDivisor D))).2
  have hrep := SGPT.Siu.primeDivisorCurrent_eq_thetaPotentialCurrent D (primeMetric D) hE
  have hS := SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D
  have h1 := (SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hπ _ hS.1
    hS.2.1 hS.2.2).2.2.2 (primeMetric D).curvature (primeMetric D).weight _ hrep
  set F := MeteredDivisorOperations.pullback hπ.1
    (Modification4.interior_exceptionalLocus_eq_empty hπ) (primeMetric D) with hFdef
  have hF : IsThetaPshPotential F.curvature.val F.weight :=
    isThetaPshPotential_comp_of_isAnalyticModification hπ (primeMetric D).curvature
      (SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ _ hE)
  have h2 : SGPT.Okounkov.analyticModificationThetaCurrent hπ (primeMetric D).curvature
      (primeMetric D).weight (SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ _ hE) =
      thetaPotentialCurrent F.curvature.val F.weight hF := rfl
  exact h1.trans (h2.trans (thetaPotentialCurrent_eq_integrationCurrent F hF))

/-- **`π^*[D]` vanishes off `π⁻¹ D`.** -/
theorem currentEqOn_pull_primeDivisorCurrent_zero {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (D : PrimeX) :
    CurrentEqOn (Modification4.pull hπ (SGPT.Siu.primeDivisorCurrent D)
      (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D)) 0 (π ⁻¹' D.val)ᶜ := by
  rw [pull_primeDivisorCurrent]
  have h := currentEqOn_integrationCurrent_zero
    (MeteredDivisorOperations.pullback hπ.1 (Modification4.interior_exceptionalLocus_eq_empty hπ)
      (primeMetric D))
  rw [MeteredDivisorOperations.pullback_support, support_primeDivisorMetric] at h
  exact h

omit [CompactSpace X] in
/-- **Locality of the push-forward over the isomorphism locus**: if `T` vanishes on `π⁻¹ O`, then
`π_*T` vanishes on `O ∖ π(Exc π)`. -/
theorem currentEqOn_currentPushforward_zero {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T : CurY} {O : Set X}
    (h0 : CurrentEqOn T 0 (π ⁻¹' O)) :
    CurrentEqOn (currentPushforward hπ.1 T) 0 (O \ π '' exceptionalLocus (m + 1) π) := by
  classical
  intro d z hz hzO
  set x := d.val.symm z with hxdef
  have hxd : x ∈ d.val.source := d.val.map_target hz
  have hdx : d.val x = z := d.val.right_inv hz
  obtain ⟨s, hs, hright, hleft⟩ := SGPT.Siu.exists_inverse_off_image_exceptionalLocus hπ
  have hEc := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hπ
  have hxE : x ∉ π '' exceptionalLocus (m + 1) π := hzO.2
  set y := s x with hydef
  have hπy : π y = x := hright x hxE
  have hyE : π y ∉ π '' exceptionalLocus (m + 1) π := by rw [hπy]; exact hxE
  let e := complexChartAt (n := m + 1) y
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hyd : π y ∈ d.val.source := by rw [hπy]; exact hxd
  obtain ⟨A, B, hyA, hAe, hBd, hAdom, hBE, hBs, hp⟩ :=
    SGPT.Siu.exists_coordinatePairs_of_inverse hπ.1 hEc hs hright hleft y hyE e d hye hyd
  set τ := coordinateMap π e d with hτdef
  set σ := coordinateMap s d e with hσdef
  have hτy : τ (e.val y) = z := by
    change d.val (π (e.val.symm (e.val y))) = z
    rw [e.val.left_inv hye, hπy, hdx]
  obtain ⟨D', hyD', hD'e, hres⟩ := h0 e (e.val y) (e.val.map_source hye) (by
    change π (e.val.symm (e.val y)) ∈ O
    rw [e.val.left_inv hye, hπy]
    exact hzO.1)
  let D : Opens (ComplexModel (m + 1)) := A ⊓ D'
  have hDA : D ≤ A := inf_le_left
  have hDD' : D ≤ D' := inf_le_right
  have hDe : D ≤ chartTarget e := hDA.trans hAe
  have hDdom : (D : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d := fun _ hw =>
    hAdom (hDA hw)
  have hyD : e.val y ∈ D := ⟨hyA, hyD'⟩
  have hpD := restrictPair hp hDA
  set B₀ : Opens (ComplexModel (m + 1)) :=
    ⟨(B : Set (ComplexModel (m + 1))) ∩ σ ⁻¹' D,
      hp.holo_inv.continuousOn.isOpen_inter_preimage B.isOpen D.isOpen⟩ with hB₀def
  have hB₀d : B₀ ≤ chartTarget d := fun w hw => hBd hw.1
  have hzB₀ : z ∈ B₀ := by
    refine ⟨?_, ?_⟩
    · rw [← hτy]; exact hp.mapsTo (hDA hyD)
    · change σ z ∈ D
      rw [← hτy, hp.left_inv _ (hDA hyD)]; exact hyD
  have hfib : ∀ y', π y' ∈ d.val.source → d.val (π y') ∈ B₀ →
      y' ∈ e.val.source ∧ e.val y' ∈ D := fun y' h1 h2 =>
    fibre_mem hleft hBE hBs h1 h2
  refine ⟨B₀, hzB₀, hB₀d, ?_⟩
  ext ζ
  change (currentPushforward hπ.1 T).inChart d (TestFunction.monoCLM ℝ ζ) =
    (0 : CurX).inChart d (TestFunction.monoCLM ℝ ζ)
  set η : TestForm D _ := pushTest (pairSymm hpD) ζ with hηdef
  have hrel : ∀ w ∈ D, ∀ v : Fin (Module.finrank ℝ (ComplexModel (m + 1)) -
      (degreeTwo (Nat.succ_pos m)).val) → ComplexModel (m + 1),
      η w v = ζ (τ w) (fun i => fderiv ℝ τ w (v i)) := by
    intro w hw v
    have h := pushTest_rel (pairSymm hpD) ζ (τ w) (hpD.mapsTo hw)
      (fun i => fderiv ℝ τ w (v i))
    rw [h, hpD.left_inv w hw]
    congr 1
    funext i
    have hc := congrArg (fun L : ComplexModel (m + 1) →L[ℝ] ComplexModel (m + 1) => L (v i))
      (fderiv_symm_comp hpD hw)
    simpa using hc.symm
  have h1 := currentPushforward_inChart_eq hπ.1 T e d hDe hB₀d hDdom hpD.mapsTo hfib η ζ hrel
  rw [h1]
  have hmono : (TestFunction.monoCLM ℝ η : TestForm (chartTarget e) _) =
      TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm D' _) := by
    apply TestFunction.ext
    intro w
    rw [testForm_inclusion_apply hDe, testForm_inclusion_apply hD'e,
      testForm_inclusion_apply hDD']
  have h2 := congrArg (fun L => L (TestFunction.monoCLM ℝ η : TestForm D' _)) hres
  change T.inChart e (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm D' _)) =
    (0 : CurY).inChart e (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm D' _))
    at h2
  rw [hmono, h2]
  rfl

/-- **`π_*[E] = 0` for a prime divisor `E` contained in the exceptional locus of `π`.** -/
theorem currentPushforward_primeDivisorCurrent_eq_zero {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (E : PrimeY)
    (hE : E.val ⊆ exceptionalLocus (m + 1) π) :
    currentPushforward hπ.1 (SGPT.Siu.primeDivisorCurrent E) = 0 := by
  have h0 : CurrentEqOn (SGPT.Siu.primeDivisorCurrent E) 0
      (π ⁻¹' (π '' exceptionalLocus (m + 1) π)ᶜ) :=
    currentEqOn_mono (currentEqOn_primeDivisorCurrent_zero E)
      (fun y hy hyE => hy ⟨y, hE hyE, rfl⟩)
  have h1 := currentEqOn_currentPushforward_zero hπ h0
  have h2 : CurrentEqOn (currentPushforward hπ.1 (SGPT.Siu.primeDivisorCurrent E)) 0
      (π '' exceptionalLocus (m + 1) π)ᶜ :=
    currentEqOn_mono h1 (fun x hx => ⟨hx, hx⟩)
  exact eq_zero_of_currentEqOn_zero
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1
      (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent E))
    (AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus
      hπ)
    (Modification4.interior_image_exceptionalLocus_eq_empty hπ)
    (Modification4.not_prime_subset_image_exceptionalLocus hπ) h2

omit [CompactSpace X] [CompactSpace Y] in
/-- The strict transform of a prime divisor is not exceptional. -/
theorem not_strictTransformPrime_subset_exceptionalLocus {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (D : PrimeX) :
    ¬ (SGPT.Siu.strictTransformPrime hπ D).val ⊆ exceptionalLocus (m + 1) π := by
  intro h
  apply Modification4.not_prime_subset_image_exceptionalLocus hπ D
  rw [← SGPT.Siu.image_strictTransformPrime hπ D]
  exact image_mono h

omit [CompactSpace X] [CompactSpace Y] in
/-- The prime divisors contained in `π⁻¹ D` are the strict transform `D̃` and exceptional ones. -/
theorem eq_strictTransformPrime_or_subset {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (D : PrimeX) (Q : PrimeY)
    (hQ : Q.val ⊆ π ⁻¹' D.val) :
    Q = SGPT.Siu.strictTransformPrime hπ D ∨ Q.val ⊆ exceptionalLocus (m + 1) π := by
  by_cases hQE : Q.val ⊆ exceptionalLocus (m + 1) π
  · exact Or.inr hQE
  left
  apply SGPT.Siu.eq_of_subset
  have hE := HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hπ.1
  refine (primeCarrier_subset_closure_diff Q hE hQE).trans ?_
  rw [SGPT.Siu.strictTransformPrime_val]
  exact closure_mono (sdiff_subset_sdiff_left hQ)

/-- **`π^*[D] = [D̃] + ∑_{E} c_E [E]`**, a finite sum over exceptional prime divisors `E`, with
`c_E = ν(π^*[D], E) ≥ 0`. -/
theorem pull_primeDivisorCurrent_eq {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (D : PrimeX) :
    ∃ (F : Finset PrimeY) (c : PrimeY → ℝ),
      (∀ E ∈ F, E.val ⊆ exceptionalLocus (m + 1) π ∧ 0 ≤ c E) ∧
      Modification4.pull hπ (SGPT.Siu.primeDivisorCurrent D)
          (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D) =
        SGPT.Siu.primeDivisorCurrent (SGPT.Siu.strictTransformPrime hπ D) +
          ∑ E ∈ F, c E • SGPT.Siu.primeDivisorCurrent E := by
  classical
  have hD := SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D
  set P := Modification4.pull hπ (SGPT.Siu.primeDivisorCurrent D) hD with hPdef
  have hP : SGPT.Siu.IsClosedPositiveCurrent P := Modification4.isClosedPositiveCurrent_pull hπ hD
  set Dt := SGPT.Siu.strictTransformPrime hπ D with hDtdef
  have h0 : CurrentEqOn P 0 (π ⁻¹' D.val)ᶜ := currentEqOn_pull_primeDivisorCurrent_zero hπ D
  have hA : IsComplexAnalyticSubset (n := m + 1) (π ⁻¹' D.val) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.1
      (SGPT.Siu.isComplexAnalyticSubset_primeCarrier D)
  have hAi : interior (π ⁻¹' D.val) = ∅ :=
    AnalyticModelDomination.interior_preimage_eq_empty_of_isAnalyticModification hπ
      (interior_primeCarrier_eq_empty D)
  obtain ⟨hPdiv, hPoff⟩ := eq_siuDivisorialPart_of_currentEqOn_zero hP hA hAi h0
  have hExc := HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hπ.1
  have hExci := Modification4.interior_exceptionalLocus_eq_empty hπ
  set F := (finite_setOf_prime_subset hExc hExci).toFinset with hFdef
  have hDtF : Dt ∉ F := by
    rw [hFdef, Set.Finite.mem_toFinset]
    exact not_strictTransformPrime_subset_exceptionalLocus hπ D
  set c : PrimeY → ℝ := fun Q => (SGPT.Siu.currentGenericLelong P hP Q).toReal with hcdef
  have hcDt : c Dt = 1 := by
    rw [hcdef]
    dsimp only
    rw [show SGPT.Siu.currentGenericLelong P hP Dt =
        SGPT.Siu.currentGenericLelong (SGPT.Siu.primeDivisorCurrent D) hD D from
      currentGenericLelong_pull_strictTransformPrime hπ hD D,
      currentGenericLelong_primeDivisorCurrent_self D, ENNReal.toReal_one]
  refine ⟨F, c, fun E hE => ⟨?_, ENNReal.toReal_nonneg⟩, ?_⟩
  · rw [hFdef, Set.Finite.mem_toFinset] at hE
    exact hE
  have hsum : P = ∑ Q ∈ insert Dt F, c Q • SGPT.Siu.primeDivisorCurrent Q := by
    refine hPdiv.trans ?_
    ext e η
    have h1 := SGPT.Siu.hasSum_siuDivisorialPart hP e η
    have h2 : HasSum (fun Q : PrimeY =>
        ((SGPT.Siu.currentGenericLelong P hP Q).toReal • SGPT.Siu.primeDivisorCurrent Q).inChart
          e η)
        (∑ Q ∈ insert Dt F, ((SGPT.Siu.currentGenericLelong P hP Q).toReal •
          SGPT.Siu.primeDivisorCurrent Q).inChart e η) := by
      apply hasSum_sum_of_ne_finset_zero
      intro Q hQ
      have hc0 : SGPT.Siu.currentGenericLelong P hP Q = 0 := by
        apply hPoff Q
        intro hQD
        rcases eq_strictTransformPrime_or_subset hπ D Q hQD with h | h
        · exact hQ (h ▸ Finset.mem_insert_self _ _)
        · apply hQ
          apply Finset.mem_insert_of_mem
          rw [hFdef, Set.Finite.mem_toFinset]
          exact h
      rw [hc0, ENNReal.toReal_zero, zero_smul]
      rfl
    rw [h1.unique h2, SGPT.Siu.inChart_finsetSum]
  rw [hsum, Finset.sum_insert hDtF, hcDt, one_smul]

/-- **`π_*[D̃] = [D]`** for the strict transform `D̃` of a prime divisor `D` of `X`. -/
theorem currentPushforward_primeDivisorCurrent_strictTransformPrime {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (D : PrimeX) :
    currentPushforward hπ.1 (SGPT.Siu.primeDivisorCurrent (SGPT.Siu.strictTransformPrime hπ D)) =
      SGPT.Siu.primeDivisorCurrent D := by
  obtain ⟨F, c, hF, heq⟩ := pull_primeDivisorCurrent_eq hπ D
  have hpush := Modification4.pushforward_pull_eq hπ
    (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D)
  rw [heq] at hpush
  have hlin : currentPushforward hπ.1
      (SGPT.Siu.primeDivisorCurrent (SGPT.Siu.strictTransformPrime hπ D) +
        ∑ E ∈ F, c E • SGPT.Siu.primeDivisorCurrent E) =
      currentPushforward hπ.1
        (SGPT.Siu.primeDivisorCurrent (SGPT.Siu.strictTransformPrime hπ D)) := by
    have h := (currentPushforwardLM (k := degreeTwo (Nat.succ_pos m)) hπ.1).map_add
      (SGPT.Siu.primeDivisorCurrent (SGPT.Siu.strictTransformPrime hπ D))
      (∑ E ∈ F, c E • SGPT.Siu.primeDivisorCurrent E)
    rw [map_sum] at h
    simp only [currentPushforwardLM_apply, map_smul] at h
    rw [h, Finset.sum_eq_zero (fun E hE => by
      rw [currentPushforward_primeDivisorCurrent_eq_zero hπ E (hF E hE).1, smul_zero]),
      add_zero]
  rw [← hlin, hpush]

omit [CompactSpace X] in
/-- **Every non-exceptional prime divisor is a strict transform**: if `D'` is a prime divisor of
`Y` not contained in the exceptional locus of `π`, then `π(D')` is a prime divisor of `X` (Remmert's
proper mapping theorem; its dimension is read at a regular point over the isomorphism locus) and
`D'` is its strict transform. -/
theorem exists_eq_strictTransformPrime {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (D' : PrimeY) (hD' : ¬ D'.val ⊆ exceptionalLocus (m + 1) π) :
    ∃ D : PrimeX, SGPT.Siu.strictTransformPrime hπ D = D' := by
  classical
  obtain ⟨W', hW'⟩ := ProperImageAnalytic.remmert1956_exists_image_subvariety hπ.1 D'.subvariety
  rw [D'.subvariety_carrier] at hW'
  obtain ⟨z₀, hz₀D, hz₀E⟩ := not_subset.mp hD'
  obtain ⟨s, -, -, hleft⟩ := SGPT.Siu.exists_inverse_off_image_exceptionalLocus hπ
  have hpre := AnalyticModificationExceptionalFibres.preimage_image_exceptionalLocus hπ
  have hnot : ∀ z, z ∉ exceptionalLocus (m + 1) π →
      π z ∉ π '' exceptionalLocus (m + 1) π := fun z hz h => by
    have : z ∈ π ⁻¹' (π '' exceptionalLocus (m + 1) π) := h
    rw [hpre] at this
    exact hz this
  have hinj : ∀ u v, u ∉ exceptionalLocus (m + 1) π → π u = π v → u = v := by
    intro u v hu huv
    have h1 := hleft u (hnot u hu)
    have h2 := hleft v (by rw [← huv]; exact hnot u hu)
    rw [← h1, ← h2, huv]
  have hEc := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hπ
  have hExc := HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hπ.1
  obtain ⟨c, hcO, k, hck⟩ := RegularLocusDense.exists_regularAtDim_mem_of_isOpen W'.analytic
    hEc.isOpen_compl (y := π z₀) (by rw [hW']; exact ⟨z₀, hz₀D, rfl⟩) (hnot z₀ hz₀E)
  have hk : k = W'.dim := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim W' hck
  have hcW : c ∈ W'.carrier := hck.2.1
  rw [hW'] at hcW
  obtain ⟨z', hz'D, rfl⟩ := hcW
  have hz'E : z' ∉ exceptionalLocus (m + 1) π := fun h => hcO ⟨z', h, rfl⟩
  have hAO : ∀ u ∈ (exceptionalLocus (m + 1) π)ᶜ, u ∈ D'.val ↔ π u ∈ W'.carrier := by
    intro u hu
    rw [hW']
    constructor
    · intro h
      exact ⟨u, h, rfl⟩
    · rintro ⟨v, hv, hvu⟩
      rw [hinj u v hu hvu.symm]
      exact hv
  have hreg := RegularAtDimTransport.regularAtDim_of_preimage hπ.1 hz'E hExc.isClosed.isOpen_compl
    hz'E hAO hck
  rw [← D'.subvariety_carrier] at hreg
  have hk' := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim D'.subvariety hreg
  have hcod := D'.subvariety_codimension
  let D : PrimeX := ⟨π '' D'.val, W', hW', by omega⟩
  refine ⟨D, SGPT.PSH.GeometricPrimeCarrier.ext ?_⟩
  rw [SGPT.Siu.strictTransformPrime_val]
  change closure (π ⁻¹' (π '' D'.val) \ exceptionalLocus (m + 1) π) = D'.val
  have hset : π ⁻¹' (π '' D'.val) \ exceptionalLocus (m + 1) π =
      D'.val \ exceptionalLocus (m + 1) π := by
    ext u
    constructor
    · rintro ⟨⟨v, hv, hvu⟩, hu⟩
      refine ⟨?_, hu⟩
      rw [hinj u v hu hvu.symm]
      exact hv
    · rintro ⟨hu, hu'⟩
      exact ⟨⟨u, hu, rfl⟩, hu'⟩
  rw [hset]
  exact Subset.antisymm (closure_minimal sdiff_subset D'.isClosed)
    (primeCarrier_subset_closure_diff D' hExc hD')

end Modification

end SGPT.BDivisor.PrimePushforward
