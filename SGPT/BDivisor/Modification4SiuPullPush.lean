import SGPT.Currents.AnalyticSupport
import SGPT.Siu.SiuModificationLelong
import SGPT.PSH.SourceBimeromorphicMixedIVolume
import SGPT.Foundations.Analysis.Pending.HolomorphicIntrinsicExceptionalAnalytic
import SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalImageCodimension
import SGPT.Foundations.Analysis.Pending.EmbeddedFromResolution

/-!
# `π^*π_*T = T + ∑ cᵢ [Eᵢ]` (`lma:Siudec_pullpush`)

Source `lma:Siudec_pullpush` (chapter *I-good singularities*): let `π : Y → X` be a proper
bimeromorphic morphism; for every non-divisorial closed positive `(1,1)`-current `T` on `Y`,
`π^*π_*T = T + ∑_{i=1}^N cᵢ [Eᵢ]` for finitely many `π`-exceptional prime divisors `Eᵢ` and
`cᵢ > 0`.  The book's proof: `T = 𝟙_{Y \ E} π^*π_*T`, so the difference is `𝟙_E π^*π_*T`, a closed
positive current supported on the exceptional locus, "which has the stated form due to the
support theorems".

* `currentEqOn_pullback_pushforward`: `π^*π_*T` and `T` agree off the exceptional locus
  `Exc π` (in every chart, near every point where `dπ` is bijective): over the isomorphism locus
  the corrected local potentials of `T` and of `π^*π_*T` pair identically with all test forms
  (`SGPT.NPP.MassPushforward.integral_corrected_pushforward`, S27).
* `isClosedPositiveCurrent_pullback_pushforward_sub`: `π^*π_*T - T ≥ 0` (the comparison theorem
  `SGPT.Currents.AnalyticSupport.isClosedPositiveCurrent_sub_of_currentEqOn`, `T` non-divisorial).
* `pullback_pushforward_eq_add`: **`lma:Siudec_pullpush`**.

Here `π^*` is `SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback` (pull-back of
local potentials), `π_*` is `SGPT.BDivisor.currentPushforward`, and the `π`-exceptional prime
divisors are the prime divisors of `Y` contained in `Exc π` (the points where `dπ` is not
bijective).  No Kähler hypothesis on `Y` is needed.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold

namespace SGPT.BDivisor.Modification4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor SGPT.NPP.MassPushforward SGPT.Currents.AnalyticSupport

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

local notation "CurY" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))
local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

/-- The pull-back `π^*π_*T` of the push-forward of a closed positive current. -/
def pullPush [CompactSpace X] [CompactSpace Y] {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (T : CurY) (hT : SGPT.Siu.IsClosedPositiveCurrent T) : CurY :=
  SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback hπ (currentPushforward hπ.1 T)
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT).1
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT).2.1
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT).2.2

theorem isClosedPositiveCurrent_pullPush [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    SGPT.Siu.IsClosedPositiveCurrent (pullPush hπ T hT) :=
  let h := SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hπ
    (currentPushforward hπ.1 T)
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT).1
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT).2.1
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT).2.2
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`π^*π_*T = T` off the exceptional locus.** -/
theorem currentEqOn_pullback_pushforward [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    CurrentEqOn (pullPush hπ T hT) T (exceptionalLocus (m + 1) π)ᶜ := by
  classical
  intro e z hz hzE
  set y := e.val.symm z with hydef
  have hye : y ∈ e.val.source := e.val.map_target hz
  have hey : e.val y = z := e.val.right_inv hz
  have hyE : y ∉ exceptionalLocus (m + 1) π := hzE
  obtain ⟨s, hs, hright, hleft⟩ := SGPT.Siu.exists_inverse_off_image_exceptionalLocus hπ
  have hEc := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hπ
  have hxE := SGPT.Siu.notMem_image_of_notMem_exceptionalLocus hπ hyE
  let d := complexChartAt (n := m + 1) (π y)
  have hyd : π y ∈ d.val.source := mem_complexChartAt_source (π y)
  obtain ⟨A, B, hyA, hAe, hBd, hAdom, hBE, hBs, hp⟩ :=
    SGPT.Siu.exists_coordinatePairs_of_inverse hπ.1 hEc hs hright hleft y hxE e d hye hyd
  set τ := coordinateMap π e d with hτdef
  have hτy : τ (e.val y) = d.val (π y) := by
    change d.val (π (e.val.symm (e.val y))) = d.val (π y)
    rw [e.val.left_inv hye]
  -- representations
  have hS := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT
  obtain ⟨σ, φ, hφ, hTeq⟩ := hT.exists_thetaPotential
  obtain ⟨θ', u', hu', hSeq⟩ := hS.exists_thetaPotential
  have hPeq : pullPush hπ T hT = SGPT.Okounkov.analyticModificationThetaCurrent hπ θ' u' hu' :=
    (SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hπ _ hS.1 hS.2.1
      hS.2.2).2.2.2 θ' u' hu' hSeq
  have hpush : currentPushforward hπ.1 (thetaPotentialCurrent σ.val φ hφ) =
      thetaPotentialCurrent θ'.val u' hu' := by rw [← hTeq]; exact hSeq
  -- local potentials
  obtain ⟨W, ρ, hyW, hρ, -⟩ := hφ.1 e (e.val y) (e.val.map_source hye)
  obtain ⟨W', κ, hxW', hκ, -⟩ := hu'.1 d (d.val (π y)) (d.val.map_source hyd)
  let Wo : Opens (ComplexModel (m + 1)) := ⟨W, hρ.1⟩
  let W'o : Opens (ComplexModel (m + 1)) := ⟨W', hκ.1⟩
  let D : Opens (ComplexModel (m + 1)) :=
    ⟨(A : Set (ComplexModel (m + 1))) ∩ W ∩ τ ⁻¹' W',
      (hp.holo.continuousOn.mono inter_subset_left).isOpen_inter_preimage
        (A.isOpen.inter hρ.1) hκ.1⟩
  have hDA : D ≤ A := fun _ hw => hw.1.1
  have hDW : D ≤ Wo := fun _ hw => hw.1.2
  have hDe : D ≤ chartTarget e := hDA.trans hAe
  have hDdom : (D : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d := fun _ hw =>
    hAdom (hDA hw)
  have hyD : e.val y ∈ D := ⟨⟨hyA, hyW⟩, by
    change τ (e.val y) ∈ W'
    rw [hτy]
    exact hxW'⟩
  have hpD := restrictPair hp hDA
  set B' : Opens (ComplexModel (m + 1)) :=
    ⟨(B : Set (ComplexModel (m + 1))) ∩ coordinateMap s d e ⁻¹' D,
      hp.holo_inv.continuousOn.isOpen_inter_preimage B.isOpen D.isOpen⟩ with hB'
  have hB'W' : B' ≤ W'o := by
    intro w hw
    have h1 : τ (coordinateMap s d e w) ∈ W' := hw.2.2
    rwa [hp.right_inv w hw.1] at h1
  have hfib : ∀ y', π y' ∈ d.val.source → d.val (π y') ∈ B' →
      y' ∈ e.val.source ∧ e.val y' ∈ D := fun y' h1 h2 =>
    fibre_mem hleft hBE hBs h1 h2
  -- the pulled-back local potential
  set W'' : Opens (ComplexModel (m + 1)) :=
    ⟨LocalPotentialPullback.potentialDomain π e d W',
      LocalPotentialPullback.potentialDomain_isOpen hπ.1 e d hκ.1⟩ with hW''def
  have hDW'' : D ≤ W'' := fun w hw => ⟨hDdom hw, hw.2⟩
  have hpot'' := LocalPotentialPullback.isSmoothLocalPotential_pullback hπ.1 e hκ
  have hcomp := isThetaPshPotential_comp_of_isAnalyticModification hπ θ' hu'
  refine ⟨D, by rw [← hey]; exact hyD, hDe, ?_⟩
  ext η
  change (pullPush hπ T hT).inChart e (TestFunction.monoCLM ℝ η) =
    T.inChart e (TestFunction.monoCLM ℝ η)
  rw [hPeq, hTeq]
  have h1 := chart_reader_eq_integral (ClosedRealOneOneForm.pullback hπ.1 θ').val hcomp e
    hDW'' (κ ∘ τ) (by rw [ClosedRealOneOneForm.pullback_val]; exact hpot'') η
  have h2 := chart_reader_eq_integral σ.val hφ e hDW ρ hρ η
  have hk := integral_corrected_pushforward hπ.1 σ.val hφ θ'.val hu' hpush e d hpD hDW hB'W'
    hDdom hfib ρ hρ κ hκ η
  have key : ∫ x, DDCOverlap.ddcAdjoint (pairFrame m) η x *
      (chartFunction (fun y => u' (π y)) e x + ((κ ∘ τ) x : EReal)).toReal =
      ∫ x, DDCOverlap.ddcAdjoint (pairFrame m) η x *
        (chartFunction φ e x + (ρ x : EReal)).toReal := by
    rw [hk]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ D
    · have hxd : π (e.val.symm x) ∈ d.val.source := (hDdom hx).2
      simp only [chartFunction, Function.comp_apply]
      change _ = _ * (u' (d.val.symm (d.val (π (e.val.symm x)))) + _).toReal
      rw [d.val.left_inv hxd]
    · have h0 : DDCOverlap.ddcAdjoint (pairFrame m) η x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h =>
          hx ((DDCOverlap.ddcAdjoint (pairFrame m) η).tsupport_subset h)
      simp only [h0, zero_mul]
  exact h1.trans (key.trans h2.symm)

/-- The exceptional locus of a modification has empty interior. -/
theorem interior_exceptionalLocus_eq_empty {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) : interior (exceptionalLocus (m + 1) π) = ∅ := by
  obtain ⟨A, -, -, hint, -, hnon⟩ := exists_analytic_exceptional_set_of_isAnalyticModification hπ
  have hEA : exceptionalLocus (m + 1) π ⊆ A := fun y hy => by
    by_contra hyA; exact hnon y hyA hy
  exact subset_empty_iff.mp (hint ▸ interior_mono hEA)

/-- `π^*π_*T - T` vanishes off the exceptional locus. -/
theorem currentEqOn_pullPush_sub_zero [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    CurrentEqOn (pullPush hπ T hT - T) 0 (exceptionalLocus (m + 1) π)ᶜ := by
  intro e z hz hzE
  obtain ⟨D, hzD, hD, heq⟩ := currentEqOn_pullback_pushforward hπ hT e z hz hzE
  refine ⟨D, hzD, hD, ?_⟩
  ext η
  have h := congrArg (fun L => L η) heq
  change (pullPush hπ T hT).inChart e (TestFunction.monoCLM ℝ η) =
    T.inChart e (TestFunction.monoCLM ℝ η) at h
  change (pullPush hπ T hT).inChart e (TestFunction.monoCLM ℝ η) -
    T.inChart e (TestFunction.monoCLM ℝ η) = 0
  rw [h, sub_self]

/-- **`lma:Siudec_pullpush`.**  Let `π : Y → X` be a modification of compact complex manifolds
and `T` a non-divisorial closed positive `(1,1)`-current on `Y`.  Then
`π^*π_*T = T + ∑_{D ∈ F} c_D [D]` for a finite set `F` of prime divisors contained in the
exceptional locus of `π` (the `π`-exceptional prime divisors) and coefficients `c_D > 0`;
explicitly `c_D = ν(π^*π_*T - T, D)`. -/
theorem pullback_pushforward_eq_add [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hnd : SGPT.Siu.IsNonDivisorial T hT) :
    ∃ (F : Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) Y))
      (c : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y → ℝ),
      (∀ D ∈ F, D.val ⊆ exceptionalLocus (m + 1) π ∧ 0 < c D) ∧
      pullPush hπ T hT = T + ∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D := by
  classical
  have hP := isClosedPositiveCurrent_pullPush hπ hT
  have hE := HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hπ.1
  have hEi := interior_exceptionalLocus_eq_empty hπ
  have hν : ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y,
      D.val ⊆ exceptionalLocus (m + 1) π → SGPT.Siu.currentGenericLelong T hT D = 0 :=
    fun D _ => (SGPT.Siu.isNonDivisorial_iff hT).mp hnd D
  have hR := isClosedPositiveCurrent_sub_of_currentEqOn hP hT hE hEi
    (currentEqOn_pullback_pushforward hπ hT) hν
  set R := pullPush hπ T hT - T with hRdef
  obtain ⟨hRdiv, hRoff⟩ :=
    eq_siuDivisorialPart_of_currentEqOn_zero hR hE hEi (currentEqOn_pullPush_sub_zero hπ hT)
  set F₀ := (finite_setOf_prime_subset hE hEi).toFinset with hF₀def
  set c : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y → ℝ :=
    fun D => (SGPT.Siu.currentGenericLelong R hR D).toReal with hcdef
  set F := F₀.filter (fun D => 0 < c D) with hFdef
  refine ⟨F, c, fun D hD => ?_, ?_⟩
  · rw [hFdef, Finset.mem_filter, hF₀def, Set.Finite.mem_toFinset] at hD
    exact ⟨hD.1, hD.2⟩
  have hsum : R = ∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D := by
    rw [hRdiv]
    ext e η
    have h1 := SGPT.Siu.hasSum_siuDivisorialPart hR e η
    have h2 : HasSum (fun D : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y =>
        ((SGPT.Siu.currentGenericLelong R hR D).toReal • SGPT.Siu.primeDivisorCurrent D).inChart e η)
        (∑ D ∈ F, ((SGPT.Siu.currentGenericLelong R hR D).toReal •
          SGPT.Siu.primeDivisorCurrent D).inChart e η) := by
      apply hasSum_sum_of_ne_finset_zero
      intro D hD
      have hc0 : c D = 0 := by
        by_cases hDE : D.val ⊆ exceptionalLocus (m + 1) π
        · have hmem : D ∈ F₀ := by rw [hF₀def, Set.Finite.mem_toFinset]; exact hDE
          have hnot : ¬ 0 < c D := fun h => hD (Finset.mem_filter.mpr ⟨hmem, h⟩)
          exact le_antisymm (not_lt.mp hnot) ENNReal.toReal_nonneg
        · rw [hcdef]; simp only [hRoff D hDE, ENNReal.toReal_zero]
      change (c D • SGPT.Siu.primeDivisorCurrent D).inChart e η = 0
      rw [hc0, zero_smul]
      rfl
    rw [h1.unique h2, SGPT.Siu.inChart_finsetSum]
  have hPT : pullPush hπ T hT = T + R := by rw [hRdef]; abel
  rw [hPT, hsum]

/-! ### `π_*π^*S = S` -/

/-- The pull-back `π^*S` of a closed positive current on `X`. -/
def pull [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (S : CurX)
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) : CurY :=
  SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback hπ S hS.1 hS.2.1 hS.2.2

theorem isClosedPositiveCurrent_pull [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) : SGPT.Siu.IsClosedPositiveCurrent (pull hπ S hS) :=
  let h := SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hπ S hS.1 hS.2.1
    hS.2.2
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`π_*π^*S = S` off the exceptional image.** -/
theorem currentEqOn_pushforward_pullback [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) :
    CurrentEqOn (currentPushforward hπ.1 (pull hπ S hS)) S (π '' exceptionalLocus (m + 1) π)ᶜ := by
  classical
  intro d z hz hzE
  set x := d.val.symm z with hxdef
  have hxd : x ∈ d.val.source := d.val.map_target hz
  have hdx : d.val x = z := d.val.right_inv hz
  obtain ⟨s, hs, hright, hleft⟩ := SGPT.Siu.exists_inverse_off_image_exceptionalLocus hπ
  have hEc := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hπ
  have hxE : x ∉ π '' exceptionalLocus (m + 1) π := hzE
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
  -- representations
  obtain ⟨θ', u', hu', hSeq⟩ := hS.exists_thetaPotential
  have hPeq : pull hπ S hS = SGPT.Okounkov.analyticModificationThetaCurrent hπ θ' u' hu' :=
    (SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hπ S hS.1 hS.2.1
      hS.2.2).2.2.2 θ' u' hu' hSeq
  have hzt : z ∈ d.val.target := hz
  obtain ⟨W', κ, hzW', hκ, -⟩ := hu'.1 d z hzt
  let D : Opens (ComplexModel (m + 1)) :=
    ⟨(A : Set (ComplexModel (m + 1))) ∩ τ ⁻¹' W',
      (hp.holo.continuousOn).isOpen_inter_preimage A.isOpen hκ.1⟩
  have hDA : D ≤ A := fun _ hw => hw.1
  have hDe : D ≤ chartTarget e := hDA.trans hAe
  have hDdom : (D : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d := fun _ hw =>
    hAdom (hDA hw)
  have hyD : e.val y ∈ D := ⟨hyA, by change τ (e.val y) ∈ W'; rw [hτy]; exact hzW'⟩
  have hpD := restrictPair hp hDA
  set B₀ : Opens (ComplexModel (m + 1)) :=
    ⟨(B : Set (ComplexModel (m + 1))) ∩ σ ⁻¹' D,
      hp.holo_inv.continuousOn.isOpen_inter_preimage B.isOpen D.isOpen⟩ with hB₀def
  have hB₀d : B₀ ≤ chartTarget d := fun w hw => hBd hw.1
  have hB₀W' : B₀ ≤ (⟨W', hκ.1⟩ : Opens _) := by
    intro w hw
    have h1 : τ (σ w) ∈ W' := hw.2.2
    rwa [hp.right_inv w hw.1] at h1
  have hzB₀ : z ∈ B₀ := by
    refine ⟨?_, ?_⟩
    · rw [← hτy]; exact hp.mapsTo (hDA hyD)
    · change σ z ∈ D
      rw [← hτy, hp.left_inv _ (hDA hyD)]; exact hyD
  have hfib : ∀ y', π y' ∈ d.val.source → d.val (π y') ∈ B₀ →
      y' ∈ e.val.source ∧ e.val y' ∈ D := fun y' h1 h2 =>
    fibre_mem hleft hBE hBs h1 h2
  have hW'' : D ≤ (⟨LocalPotentialPullback.potentialDomain π e d W',
      LocalPotentialPullback.potentialDomain_isOpen hπ.1 e d hκ.1⟩ : Opens _) :=
    fun w hw => ⟨hDdom hw, hw.2⟩
  have hpot'' := LocalPotentialPullback.isSmoothLocalPotential_pullback hπ.1 e hκ
  have hcomp := isThetaPshPotential_comp_of_isAnalyticModification hπ θ' hu'
  refine ⟨B₀, hzB₀, hB₀d, ?_⟩
  ext ζ
  change (currentPushforward hπ.1 (pull hπ S hS)).inChart d (TestFunction.monoCLM ℝ ζ) =
    S.inChart d (TestFunction.monoCLM ℝ ζ)
  -- the pulled-back test form
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
  have h1 := currentPushforward_inChart_eq hπ.1 (pull hπ S hS) e d hDe hB₀d hDdom hpD.mapsTo
    hfib η ζ hrel
  rw [h1, hPeq, hSeq]
  have h2 := chart_reader_eq_integral (ClosedRealOneOneForm.pullback hπ.1 θ').val hcomp e
    hW'' (κ ∘ τ) (by rw [ClosedRealOneOneForm.pullback_val]; exact hpot'') η
  have h3 := chart_reader_eq_integral θ'.val hu' d hB₀W' κ hκ ζ
  have key : ∫ w, DDCOverlap.ddcAdjoint (pairFrame m) η w *
      (chartFunction (fun y => u' (π y)) e w + ((κ ∘ τ) w : EReal)).toReal =
      ∫ w, DDCOverlap.ddcAdjoint (pairFrame m) η w *
        (fun v => (chartFunction u' d v + (κ v : EReal)).toReal) (τ w) := by
    apply integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ D
    · have hwd : π (e.val.symm w) ∈ d.val.source := (hDdom hw).2
      simp only [chartFunction, Function.comp_apply]
      change _ = _ * (u' (d.val.symm (d.val (π (e.val.symm w)))) + _).toReal
      rw [d.val.left_inv hwd]
    · have h0 : DDCOverlap.ddcAdjoint (pairFrame m) η w = 0 :=
        image_eq_zero_of_notMem_tsupport fun h =>
          hw ((DDCOverlap.ddcAdjoint (pairFrame m) η).tsupport_subset h)
      simp only [h0, zero_mul]
  have h4 := integral_ddcAdjoint_mul_comp (μ := volume) (pairFrame m) hpD η ζ hrel
    (fun v => (chartFunction u' d v + (κ v : EReal)).toReal)
  exact h2.trans (key.trans (h4.trans h3.symm))

/-- The exceptional image has empty interior and contains no prime divisor. -/
theorem interior_image_exceptionalLocus_eq_empty {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) :
    interior (π '' exceptionalLocus (m + 1) π) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hreg : RegularAtDim (n := m + 1) (π '' exceptionalLocus (m + 1) π) x (m + 1) :=
    EmbeddedFromResolution.regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  have := AnalyticModificationExceptionalImageCodimension.add_one_le_pred_of_regularAtDim_image hπ
    hreg
  omega

theorem not_prime_subset_image_exceptionalLocus {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    ¬ D.val ⊆ π '' exceptionalLocus (m + 1) π := by
  intro hD
  apply AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
    hπ D.subvariety D.subvariety_codimension
  rw [D.subvariety_carrier]; exact hD

/-- **`π_*π^*S = S`** for every closed positive `(1,1)`-current `S` on `X` (Xia, *Foundations of
pluripotential theory*, `lem:nondivisorial-pull-push-exceptional`, second statement). -/
theorem pushforward_pull_eq [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) : currentPushforward hπ.1 (pull hπ S hS) = S :=
  eq_of_currentEqOn
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 (isClosedPositiveCurrent_pull hπ hS))
    hS (AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hπ)
    (interior_image_exceptionalLocus_eq_empty hπ) (currentEqOn_pushforward_pullback hπ hS)
    (fun D hD => absurd hD (not_prime_subset_image_exceptionalLocus hπ D))
    (fun D hD => absurd hD (not_prime_subset_image_exceptionalLocus hπ D))

end SGPT.BDivisor.Modification4
