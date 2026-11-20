import SGPT.Hodge.ExceptionalBDivisor
import SGPT.Foundations.Analysis.BallSubmean
import SGPT.Foundations.Analysis.PlurisubharmonicAE
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.Foundations.Analysis.Pending.FiniteGlobalCurrentSmoothLocalDensity

/-!
# Negativity of exceptional classes

* `eq_const_of_isThetaPshPotential_zero`: a plurisubharmonic function (a `0`-psh potential) on a
  compact connected complex manifold is constant (strong maximum principle).
* `eq_zero_of_bottChernClass_eq_zero`: a closed positive `(1,1)`-current with zero class on a
  compact connected complex manifold vanishes.
* `exceptional_negativity` (`claude-hodge:prop-exceptional-negativity`): for a modification
  `π : Y → X` of compact complex manifolds, `X` connected, if `∑_{E ∈ F} a_E {E}` is
  pseudo-effective for a finite set `F` of `π`-exceptional prime divisors, then all `a_E ≥ 0`.
* `iOrder_of_currentBDivisor_le` (**`cor:Dorder_Iorder`, `(1) ⇒ (2)`**) and
  `currentBDivisor_le_iff_iOrder` (the equivalence): for non-divisorial closed positive
  `(1,1)`-currents `T, T'` on a compact connected `X` with `{T} = {T'}`,
  `𝔻(T) ≤ 𝔻(T') ↔ T ≼_𝓘 T'`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff Manifold ENNReal

namespace SGPT.Hodge.Exceptional

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalCurrents
  SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor SGPT.Currents.AnalyticSupport

/-! ### Plurisubharmonic functions on compact manifolds are constant -/

section MaxPrinciple

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A `0`-psh potential is plurisubharmonic in every chart. -/
theorem plurisubharmonicOn_chartFunction_of_zero {u : M → EReal}
    (hu : IsThetaPshPotential (0 : ClosedRealOneOneForm n M).val u) (e : ComplexChart n M) :
    PlurisubharmonicOn (chartFunction u e) e.val.target := by
  have hρ : IsSmoothLocalPotential (0 : ClosedRealOneOneForm n M).val e e.val.target
      (fun _ => (0 : ℝ)) :=
    ⟨e.val.open_target, subset_rfl, contDiffOn_const, fun z _ => by
      rw [smoothDDC_zero, ClosedRealOneOneForm.coeff_zero]⟩
  have h := chartCorrectedFamily_plurisubharmonicOn (F := {u})
    (fun v hv => by rw [mem_singleton_iff.mp hv]; exact hu) e hρ _ ⟨u, mem_singleton _, rfl⟩
  simpa using h

/-- **Strong maximum principle**: a plurisubharmonic function on an open set `W` of `ℂⁿ` which is
bounded by a real constant `C` and equals `C` at `a ∈ W` equals `C` near `a`. -/
theorem eventually_eq_of_isMax {u : ComplexModel n → EReal} {W : Set (ComplexModel n)}
    (hu : PlurisubharmonicOn u W) (hW : IsOpen W) {a : ComplexModel n} (ha : a ∈ W) {C : ℝ}
    (hC : ∀ y ∈ W, u y ≤ (C : EReal)) (hua : u a = (C : EReal)) :
    ∀ᶠ y in 𝓝 a, u y = (C : EReal) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨R, hR, hBW⟩ := Metric.isOpen_iff.mp hW a ha
  have hdisc := (hu.mono hBW).discPshOn_of_isOpen isOpen_ball
  have hle := hdisc.ball_deficit_le (MeasureTheory.Measure.addHaar) a R C subset_rfl
    (fun y hy => hC y (hBW hy))
  have hzero : ∫⁻ x in ball a R, ((C : EReal) - u x).toENNReal ∂Measure.addHaar = 0 := by
    apply le_antisymm
    · simpa [hua] using hle
    · exact bot_le
  have hae0 : (fun x => ((C : EReal) - u x).toENNReal) =ᵐ[
      (Measure.addHaar : Measure (ComplexModel n)).restrict (ball a R)] 0 :=
    (MeasureTheory.lintegral_eq_zero_iff'
      (hdisc.aemeasurable_deficit_restrict measurableSet_ball subset_rfl C _)).mp hzero
  have hae : u =ᵐ[(Measure.addHaar : Measure (ComplexModel n)).restrict (ball a R)]
      fun _ => (C : EReal) := by
    filter_upwards [hae0, ae_restrict_mem measurableSet_ball] with x hx hmem
    exact le_antisymm (hC x (hBW hmem))
      (EReal.sub_nonpos.mp (EReal.toENNReal_eq_zero_iff.mp hx))
  have hconst : PlurisubharmonicOn (fun _ : ComplexModel n => (C : EReal)) (ball a R) :=
    fun x _ => plurisubharmonicAt_const (C : EReal) (by simp) x
  have heq := (hu.mono hBW).eqOn_of_ae_eq hconst isOpen_ball _ hae
  filter_upwards [ball_mem_nhds a hR] with y hy
  exact heq hy

/-- **A plurisubharmonic function on a compact connected complex manifold is constant.** -/
theorem eq_const_of_isThetaPshPotential_zero [CompactSpace M] [ConnectedSpace M] {u : M → EReal}
    (hu : IsThetaPshPotential (0 : ClosedRealOneOneForm n M).val u) :
    ∃ c : ℝ, ∀ x, u x = (c : EReal) := by
  have husc : UpperSemicontinuous u :=
    ManifoldQuasiPlurisubharmonic.upperSemicontinuous hu.1.quasiPlurisubharmonic
  obtain ⟨x₀, -, hmax⟩ := (husc.upperSemicontinuousOn univ).exists_isMaxOn univ_nonempty
    isCompact_univ
  -- the maximum is finite
  have hne_top : ∀ x, u x ≠ ⊤ := by
    intro x
    let e := complexChartAt (n := n) x
    have hx : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    have h := ((plurisubharmonicOn_chartFunction_of_zero hu e) _ hx)
    obtain ⟨U, -, hxU, hU⟩ := h
    have := hU.ne_top _ hxU
    simpa [chartFunction, e.val.left_inv (mem_complexChartAt_source x)] using this
  have hne_bot : u x₀ ≠ ⊥ := by
    intro hbot
    obtain ⟨y, -, hy⟩ := hu.2 x₀ univ isOpen_univ (mem_univ _)
    exact hy (le_bot_iff.mp (hbot ▸ hmax (mem_univ y)))
  set c : ℝ := (u x₀).toReal with hc
  have hcx : u x₀ = (c : EReal) := (EReal.coe_toReal (hne_top x₀) hne_bot).symm
  have hle : ∀ x, u x ≤ (c : EReal) := fun x => hcx ▸ hmax (mem_univ x)
  refine ⟨c, ?_⟩
  -- `{u = c}` is clopen and nonempty
  let K : Set M := {x | u x = (c : EReal)}
  have hKclosed : IsClosed K := by
    have : K = {x | (c : EReal) ≤ u x} := by
      ext x
      exact ⟨fun h => h.ge, fun h => le_antisymm (hle x) h⟩
    rw [this]
    have hopen : IsOpen {x | u x < (c : EReal)} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      exact husc x _ hx
    have h2 := hopen.isClosed_compl
    have h3 : {x | u x < (c : EReal)}ᶜ = {x | (c : EReal) ≤ u x} := by
      ext x
      simp [not_lt]
    rwa [h3] at h2
  have hKopen : IsOpen K := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    let e := complexChartAt (n := n) x
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hz : e.val x ∈ e.val.target := e.val.map_source hxe
    have hpsh := plurisubharmonicOn_chartFunction_of_zero hu e
    have hev := eventually_eq_of_isMax hpsh e.val.open_target hz
      (fun y _ => hle _) (by
        change u (e.val.symm (e.val x)) = _
        rw [e.val.left_inv hxe]
        exact hx)
    have hcont : ContinuousAt e.val x := e.val.continuousAt hxe
    filter_upwards [hcont.preimage_mem_nhds hev, e.val.open_source.mem_nhds hxe] with y hy hys
    change u (e.val.symm (e.val y)) = _ at hy
    rw [e.val.left_inv hys] at hy
    exact hy
  have hK : K = univ := IsClopen.eq_univ ⟨hKclosed, hKopen⟩ ⟨x₀, hcx⟩
  intro x
  have : x ∈ K := hK ▸ mem_univ x
  exact this

/-- **A closed positive `(1,1)`-current with zero class on a compact connected complex manifold
vanishes.** -/
theorem eq_zero_of_bottChernClass_eq_zero {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]
    [ConnectedSpace M] {S : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S)
    (h0 : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨S, hS.1, hS.2.1⟩ = 0) :
    S = 0 := by
  obtain ⟨u, hu, hSeq, -⟩ :=
    PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
      ⟨S, hS.1, hS.2.1⟩ 0 hS.2.2 (by rw [h0]; rfl)
  obtain ⟨c, hc⟩ := eq_const_of_isThetaPshPotential_zero hu
  change S = thetaPotentialCurrent _ u hu at hSeq
  rw [hSeq]
  apply LelongPoincareDivisor.globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  rw [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
    FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent, globalDDC_coefficients,
    smoothFormDistribution_zero, zero_add, GlobalCurrent.coefficients_zero]
  have hfun : (fun z => (chartFunction u e z).toReal) = fun _ => c := by
    funext z
    simp [chartFunction, hc]
  unfold chartDDC
  simp_rw [hfun]
  rw [FiniteGlobalCurrentSmoothLocalDensity.ddC_regular_eq_regularForm _ contDiffOn_const]
  ext v φ
  rw [regularFormDistribution_apply]
  simp

end MaxPrinciple

/-! ### Negativity -/

section Negativity

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurY" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))
local notation "PrimeY" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y

/-- A closed positive current with `π_*T = 0` is a finite combination
`∑_{E exceptional} ν(T, E)[E]` (support theorem). -/
theorem eq_sum_of_currentPushforward_eq_zero {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {T : CurY}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (h0 : currentPushforward hπ.1 T = 0) :
    T = ∑ D ∈ excPrimes hπ,
      (SGPT.Siu.currentGenericLelong T hT D).toReal • SGPT.Siu.primeDivisorCurrent D := by
  classical
  have hW0 := currentEqOn_zero_of_currentPushforward_eq_zero hπ h0
  rw [AnalyticModificationExceptionalFibres.preimage_image_exceptionalLocus hπ] at hW0
  obtain ⟨hdiv, hoff⟩ := eq_siuDivisorialPart_of_currentEqOn_zero hT
    (HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hπ.1)
    (Modification4.interior_exceptionalLocus_eq_empty hπ) hW0
  refine hdiv.trans ?_
  ext e η
  have h1 := SGPT.Siu.hasSum_siuDivisorialPart hT e η
  have h2 : HasSum (fun D : PrimeY =>
      ((SGPT.Siu.currentGenericLelong T hT D).toReal • SGPT.Siu.primeDivisorCurrent D).inChart e η)
      (∑ D ∈ excPrimes hπ, ((SGPT.Siu.currentGenericLelong T hT D).toReal •
        SGPT.Siu.primeDivisorCurrent D).inChart e η) := by
    apply hasSum_sum_of_ne_finset_zero
    intro D hD
    rw [mem_excPrimes] at hD
    rw [hoff D hD, ENNReal.toReal_zero, zero_smul]
    rfl
  rw [h1.unique h2, SGPT.Siu.inChart_finsetSum]

/-- **Negativity of exceptional classes** (`claude-hodge:prop-exceptional-negativity`): for a
modification `π : Y → X` of compact complex manifolds with `X` connected, if `∑_{E ∈ F} a_E {E}`
is pseudo-effective for a finite set `F` of `π`-exceptional prime divisors, then `a_E ≥ 0` for
all `E ∈ F`. -/
theorem exceptional_negativity [ConnectedSpace X] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (F : Finset PrimeY)
    (hF : ∀ E ∈ F, E.val ⊆ exceptionalLocus (m + 1) π) (a : PrimeY → ℝ)
    (hpsef : ClassPseudoeffectiveViaPotentials (∑ E ∈ F, a E • primeDivisorClass E)) :
    ∀ E ∈ F, 0 ≤ a E := by
  classical
  rw [← SGPT.PSH.BookCurrent.isPseudoeffective_iff_classPseudoeffectiveViaPotentials] at hpsef
  obtain ⟨T₀, hT₀⟩ := hpsef
  set T := T₀.current
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T₀
  -- `π_*T` has zero class, hence vanishes
  have hpushE : ∀ E ∈ F, classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (primeDivisorClass E) = 0 := by
    intro E hE
    rw [primeDivisorClass, SGPT.PSH.BookCurrent.currentClass,
      ← bottChernClass_closedCurrentPushforward]
    have h0 : closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (SGPT.Siu.primeDivisorBookCurrent E).val = 0 :=
      Subtype.ext (PrimePushforward.currentPushforward_primeDivisorCurrent_eq_zero hπ E (hF E hE))
    rw [h0]
    exact (bottChernClassLinearMap (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_zero
  have hTX := SGPT.Siu.isClosedPositiveCurrent_currentPushforward hπ.1 hT
  have hclassX : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨currentPushforward hπ.1 T, hTX.1, hTX.2.1⟩ = 0 := by
    have e1 : (⟨currentPushforward hπ.1 T, hTX.1, hTX.2.1⟩ :
        ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
        closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) T₀.val :=
      Subtype.ext rfl
    rw [e1, bottChernClass_closedCurrentPushforward]
    change classPushforward hπ.1 _ _ (SGPT.PSH.BookCurrent.currentClass T₀) = 0
    rw [hT₀, map_sum]
    exact Finset.sum_eq_zero fun E hE => by rw [map_smul, hpushE E hE, smul_zero]
  have hpush0 := eq_zero_of_bottChernClass_eq_zero hTX hclassX
  -- hence `T = ∑ ν(T, E)[E]` over the exceptional primes
  have hTsum := eq_sum_of_currentPushforward_eq_zero hπ hT hpush0
  set ν : PrimeY → ℝ := fun D => (SGPT.Siu.currentGenericLelong T hT D).toReal with hν
  have hcls : SGPT.PSH.BookCurrent.currentClass T₀ =
      ∑ D ∈ excPrimes hπ, ν D • primeDivisorClass D := by
    have hc := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T₀
    unfold SGPT.PSH.BookCurrent.currentClass
    rw [← bottChernClass_sum_primeDivisorCurrent _ _ (hTsum ▸ hc.1) (hTsum ▸ hc.2.1)]
    congr 1
    exact Subtype.ext hTsum
  have hsF := sum_eq_sum_excPrimes hπ F hF a primeDivisorClass
  have hdiff : ∑ D ∈ excPrimes hπ, (ν D - (if D ∈ F then a D else 0)) • primeDivisorClass D = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← hcls, ← hsF, hT₀, sub_self]
  have hcoef := exceptional_coeff_eq_zero hπ _ (fun E hE => (mem_excPrimes hπ).mp hE) _ hdiff
  intro E hE
  have h := hcoef E ((mem_excPrimes hπ).mpr (hF E hE))
  rw [if_pos hE, sub_eq_zero] at h
  rw [← h]
  exact ENNReal.toReal_nonneg

end Negativity

/-! ### `cor:Dorder_Iorder` -/

section Dorder

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **`cor:Dorder_Iorder`, `(1) ⇒ (2)`**: for non-divisorial closed positive `(1,1)`-currents
`T, T'` on a compact connected `X` with `{T} = {T'}`, `𝔻(T) ≤ 𝔻(T')` (over the book's blow-up
models) implies `T ≼_𝓘 T'`. -/
theorem iOrder_of_currentBDivisor_le {T T' : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X}
    (hnd : SGPT.Siu.IsNonDivisorial T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))
    (hnd' : SGPT.Siu.IsNonDivisorial T'.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T'))
    (hclass : SGPT.PSH.BookCurrent.currentClass T = SGPT.PSH.BookCurrent.currentClass T')
    (hle : (currentBDivisor T).LE (currentBDivisor T')) :
    SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T.current T'.current := by
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  have hT' := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T'
  apply sourceCurrentIOrder_of_forall_blowupModel hT hT'
  intro π hπ D
  have hpsef := hle ⟨π, hπ⟩
  change ClassPseudoeffectiveViaPotentials
    (π.regPullClass T'.current hT' - π.regPullClass T.current hT) at hpsef
  rw [regPullClass_sub_eq_sum π hT hT' hnd hnd' hclass] at hpsef
  by_cases hD : D ∈ excPrimes π.isAnalyticModification
  · have h := exceptional_negativity π.isAnalyticModification _
      (fun E hE => (mem_excPrimes _).mp hE) _ hpsef D hD
    rw [sub_nonneg] at h
    exact (ENNReal.toReal_le_toReal (SGPT.Siu.currentGenericLelong_ne_top _ D)
      (SGPT.Siu.currentGenericLelong_ne_top _ D)).mp h
  · rw [mem_excPrimes] at hD
    rw [genericLelong_pull_eq_zero_of_not_subset _ hT' hnd' D hD]
    exact bot_le

/-- **`cor:Dorder_Iorder`**: for non-divisorial closed positive `(1,1)`-currents `T, T'` on a
compact connected `X` with `{T} = {T'}`, `𝔻(T) ≤ 𝔻(T')` if and only if `T ≼_𝓘 T'`. -/
theorem currentBDivisor_le_iff_iOrder {T T' : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X}
    (hnd : SGPT.Siu.IsNonDivisorial T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T))
    (hnd' : SGPT.Siu.IsNonDivisorial T'.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T'))
    (hclass : SGPT.PSH.BookCurrent.currentClass T = SGPT.PSH.BookCurrent.currentClass T') :
    (currentBDivisor T).LE (currentBDivisor T') ↔
      SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T.current T'.current :=
  ⟨iOrder_of_currentBDivisor_le hnd hnd' hclass, currentBDivisor_le_of_iOrder hclass⟩

end Dorder

end SGPT.Hodge.Exceptional
