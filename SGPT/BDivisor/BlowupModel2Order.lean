import SGPT.BDivisor.BlowupModel2DT
import SGPT.PSH.SourceCurrentMixedIVolumeAlgebra
import SGPT.Foundations.Analysis.Pending.GenuineModificationIdealOrderInvariance
import SGPT.Foundations.Analysis.Pending.RawIntegerPointComparison

/-!
# The `𝓘`-order and the order of b-divisors of currents (`cor:Dorder_Iorder`, `(2) ⇒ (1)`)

Source `cor:Dorder_Iorder` (chapter *The theory of b-divisors*): for non-divisorial closed positive
`(1,1)`-currents `T, T'` with `{T} = {T'}`, `𝔻(T) ≤ 𝔻(T')` iff `T ≼_𝓘 T'`. This file proves the
implication `T ≼_𝓘 T' ⇒ 𝔻(T) ≤ 𝔻(T')`, without the non-divisoriality hypothesis:

* `currentGenericLelong_pull_le_of_iOrder`: if `T ≼_𝓘 T'` then `ν(π^*T', E) ≤ ν(π^*T, E)` for every
  modification `π : Y → X` and every prime divisor `E` of `Y` (`𝓘`-orders are preserved by
  pull-back, and Lelong numbers are monotone for the `𝓘`-order; `prop:Iequivchar2`);
* `isClosedPositiveCurrent_siuDivisorialPart_sub_of_le`: if `ν(T', D) ≤ ν(T, D)` for all prime
  divisors, `∑ ν(T, D)[D] - ∑ ν(T', D)[D]` is a closed positive current (a weak limit of positive
  currents);
* `bottChernClass_pull`: `{π^*T} = π^*{T}`;
* `currentBDivisorOn_le_of_iOrder`, `currentBDivisor_le_of_iOrder`: **`T ≼_𝓘 T'`, `{T} = {T'}`
  `⇒ 𝔻(T) ≤ 𝔻(T')`**: on every model `𝔻(T')_Y - 𝔻(T)_Y = {Div π^*T - Div π^*T'}`, the class of a
  closed positive current.

The converse needs that pseudo-effective exceptional classes have nonnegative coefficients
(`prop:blowup_cone` / the negativity lemma), which is not formalized.
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
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

namespace PrimePushforward

section Lelong

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

/-- `π^*(θ + ddᶜu) = π^*θ + ddᶜ(u ∘ π)`. -/
theorem pull_eq_thetaPotentialCurrent {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {S : CurX} (hS : SGPT.Siu.IsClosedPositiveCurrent S) {θ : ClosedRealOneOneForm (m + 1) X}
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hSeq : S = thetaPotentialCurrent θ.val u hu) :
    Modification4.pull hπ S hS = thetaPotentialCurrent (ClosedRealOneOneForm.pullback hπ.1 θ).val
      (fun y => u (π y)) (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hu) :=
  (SGPT.PSH.VariableComplexAtlas.sourceCurrentModificationPullback_spec hπ S hS.1 hS.2.1
    hS.2.2).2.2.2 θ u hu hSeq

/-- **The `𝓘`-order controls the Lelong numbers of the pull-backs**: if `S = θ + ddᶜu`,
`S' = σ + ddᶜv` and `u ≼_𝓘 v`, then `ν(π^*S', E) ≤ ν(π^*S, E)` for every modification `π` and every
prime divisor `E` of its source. -/
theorem currentGenericLelong_pull_le_of_iOrder {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {S S' : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) (hS' : SGPT.Siu.IsClosedPositiveCurrent S')
    {θ σ : ClosedRealOneOneForm (m + 1) X} {u v : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential σ.val v) (hSeq : S = thetaPotentialCurrent θ.val u hu)
    (hS'eq : S' = thetaPotentialCurrent σ.val v hv) (hI : IOrderOnManifold (n := m + 1) u v)
    (E : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y) :
    SGPT.Siu.currentGenericLelong (Modification4.pull hπ S' hS')
        (Modification4.isClosedPositiveCurrent_pull hπ hS') E ≤
      SGPT.Siu.currentGenericLelong (Modification4.pull hπ S hS)
        (Modification4.isClosedPositiveCurrent_pull hπ hS) E := by
  have hIpull := (GenuineModificationIdealOrderInvariance.iOrder_iff_comp hπ
    hu.1.quasiPlurisubharmonic hv.quasiPshPotential).mp hI
  have hpoint : ∀ y, SGPT.Siu.currentLelong (Modification4.pull hπ S' hS')
      (Modification4.isClosedPositiveCurrent_pull hπ hS') y ≤
      SGPT.Siu.currentLelong (Modification4.pull hπ S hS)
        (Modification4.isClosedPositiveCurrent_pull hπ hS) y := by
    intro y
    rw [SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent _
        (pull_eq_thetaPotentialCurrent hπ hS' hv hS'eq),
      SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent _
        (pull_eq_thetaPotentialCurrent hπ hS hu hSeq)]
    have h := RawIntegerPointComparison.lelongNumber_le_of_iOrderOnManifold
      (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 hu.1.quasiPlurisubharmonic)
      hIpull y
    rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
      lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)] at h
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h
  exact le_iInf₂ fun y hy => (SGPT.Siu.currentGenericLelong_le _ E hy).trans (hpoint y)

end Lelong

section Divisorial

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [CompactSpace M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))

/-- **Coefficientwise domination of divisorial parts gives a positive difference**: if
`ν(T', D) ≤ ν(T, D)` for every prime divisor `D`, then `∑ ν(T, D)[D] - ∑ ν(T', D)[D]` is a closed
positive current. -/
theorem isClosedPositiveCurrent_siuDivisorialPart_sub_of_le {T T' : Cur}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hle : ∀ D, SGPT.Siu.currentGenericLelong T' hT' D ≤ SGPT.Siu.currentGenericLelong T hT D) :
    SGPT.Siu.IsClosedPositiveCurrent
      (SGPT.Siu.siuDivisorialPart T hT - SGPT.Siu.siuDivisorialPart T' hT') := by
  have h1 := SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT
  have h2 := SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT'
  have hsub : SGPT.Siu.siuDivisorialPart T hT - SGPT.Siu.siuDivisorialPart T' hT' =
      SGPT.Siu.siuDivisorialPart T hT + (-1 : ℝ) • SGPT.Siu.siuDivisorialPart T' hT' := by
    module
  refine ⟨hsub ▸ h1.1.add _ (h2.1.smul _ _), hsub ▸ h1.2.1.add _ (h2.2.1.smul _ (-1)), ?_⟩
  intro e α hα
  set η := CanonicalComplementaryCurrentTests.castTestDegree
    (by rw [complexModel_real_finrank]; omega :
      2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α
  have hs := (SGPT.Siu.hasSum_siuDivisorialPart hT e η).sub
    (SGPT.Siu.hasSum_siuDivisorialPart hT' e η)
  change 0 ≤ (SGPT.Siu.siuDivisorialPart T hT).inChart e η -
    (SGPT.Siu.siuDivisorialPart T' hT').inChart e η
  refine hs.nonneg fun D => ?_
  have hD := (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).2.2 e α hα
  have hc : (SGPT.Siu.currentGenericLelong T' hT' D).toReal ≤
      (SGPT.Siu.currentGenericLelong T hT D).toReal :=
    ENNReal.toReal_mono (SGPT.Siu.currentGenericLelong_ne_top hT D) (hle D)
  simp only [GlobalCurrent.inChart_smul]
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
    ← sub_mul]
  exact mul_nonneg (by linarith) hD

end Divisorial

section Class

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

/-- **`{π^*S} = π^*{S}`**. -/
theorem bottChernClass_pull {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) {S : CurX}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨Modification4.pull hπ S hS, (Modification4.isClosedPositiveCurrent_pull hπ hS).1,
          (Modification4.isClosedPositiveCurrent_pull hπ hS).2.1⟩ =
      classPullback hπ.1 (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨S, hS.1, hS.2.1⟩) := by
  obtain ⟨θ, u, hu, hSeq⟩ := hS.exists_thetaPotential
  have h1 : (⟨Modification4.pull hπ S hS, (Modification4.isClosedPositiveCurrent_pull hπ hS).1,
      (Modification4.isClosedPositiveCurrent_pull hπ hS).2.1⟩ :
        ClosedOneOneCurrent (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
      thetaClosedCurrent (ClosedRealOneOneForm.pullback hπ.1 θ) (fun y => u (π y))
        (isThetaPshPotential_comp_of_isAnalyticModification hπ θ hu) :=
    Subtype.ext (pull_eq_thetaPotentialCurrent hπ hS hu hSeq)
  have h2 : (⟨S, hS.1, hS.2.1⟩ :
        ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
      thetaClosedCurrent θ u hu := Subtype.ext hSeq
  rw [h1, h2, bottChernClass_thetaClosedCurrent, bottChernClass_thetaClosedCurrent,
    classPullback_ofRepresentative]

end Class

end PrimePushforward

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

omit [CompactSpace X] in
/-- The class map is additive. -/
theorem bottChernClass_add' {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]
    (T U : ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (T + U) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T +
        bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) U :=
  (bottChernClassLinearMap (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_add T U

/-- The class of the divisorial part `∑_E ν(π^*T, E)[E]` of `π^*T`. -/
def Modification.divPullClass (π : Modification (m + 1) X) (T : CurX)
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) : RealBottChern (m + 1) π.carrier :=
  bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
    ⟨SGPT.Siu.siuDivisorialPart (Modification4.pull π.isAnalyticModification T hT)
        (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT),
      (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart _).1,
      (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart _).2.1⟩

/-- `{Reg π^*T} = π^*{T} - {∑_E ν(π^*T, E)[E]}`. -/
theorem Modification.regPullClass_eq (π : Modification (m + 1) X) {T : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) :
    π.regPullClass T hT = classPullback π.isAnalyticModification.1
        (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩) -
      π.divPullClass T hT := by
  rw [← PrimePushforward.bottChernClass_pull π.isAnalyticModification hT, eq_sub_iff_add_eq,
    regPullClass, divPullClass,
    ← bottChernClass_add']
  congr 1
  apply Subtype.ext
  change Modification4.pull π.isAnalyticModification T hT - _ + _ = _
  abel

/-- **`T ≼_𝓘 T'` and `{T} = {T'}` imply `{Reg π^*T} ≤ {Reg π^*T'}` on every modification.** -/
theorem Modification.classPseudoeffective_regPullClass_sub_of_iOrder (π : Modification (m + 1) X)
    {T T' : CurX} (hT : SGPT.Siu.IsClosedPositiveCurrent T)
    (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T', hT'.1, hT'.2.1⟩)
    (hI : SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T T') :
    ClassPseudoeffectiveViaPotentials (π.regPullClass T' hT' - π.regPullClass T hT) := by
  obtain ⟨θ, σ, u, v, hu, hv, hTeq, hT'eq, hIuv⟩ := hI
  have hle := fun E => PrimePushforward.currentGenericLelong_pull_le_of_iOrder
    π.isAnalyticModification hT hT' hu hv hTeq hT'eq hIuv E
  have hP := PrimePushforward.isClosedPositiveCurrent_siuDivisorialPart_sub_of_le
    (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT)
    (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hT') hle
  have hadd : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨_, hP.1, hP.2.1⟩ +
      π.divPullClass T' hT' = π.divPullClass T hT := by
    rw [divPullClass, divPullClass, ← bottChernClass_add']
    congr 1
    apply Subtype.ext
    change _ - _ + _ = _
    abel
  have heq : π.regPullClass T' hT' - π.regPullClass T hT =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨_, hP.1, hP.2.1⟩ := by
    rw [π.regPullClass_eq hT, π.regPullClass_eq hT', hclass, ← hadd]
    abel
  rw [heq, ← SGPT.PSH.BookCurrent.isPseudoeffective_iff_classPseudoeffectiveViaPotentials]
  exact ⟨SGPT.Siu.toBookCurrent _ hP, rfl⟩

/-- **`cor:Dorder_Iorder`, `(2) ⇒ (1)`, over any model system**: `T ≼_𝓘 T'` and `{T} = {T'}` imply
`𝔻(T) ≤ 𝔻(T')`. -/
theorem currentBDivisorOn_le_of_iOrder (S : ModelSystem (m + 1) X) {T T' : CurX}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T')
    (hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T, hT.1, hT.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨T', hT'.1, hT'.2.1⟩)
    (hI : SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T T') :
    (currentBDivisorOn S T hT).LE (currentBDivisorOn S T' hT') :=
  fun π => π.1.classPseudoeffective_regPullClass_sub_of_iOrder hT hT' hclass hI

/-- **`cor:Dorder_Iorder`, `(2) ⇒ (1)`**: for closed positive `(1,1)`-currents `T, T'` on `X` with
`{T} = {T'}` and `T ≼_𝓘 T'`, `𝔻(T) ≤ 𝔻(T')` (over the book's blow-up models; non-divisoriality is
not needed for this implication). -/
theorem currentBDivisor_le_of_iOrder {T T' : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X}
    (hclass : SGPT.PSH.BookCurrent.currentClass T = SGPT.PSH.BookCurrent.currentClass T')
    (hI : SGPT.PSH.VariableComplexAtlas.sourceCurrentIOrder T.current T'.current) :
    (currentBDivisor T).LE (currentBDivisor T') :=
  currentBDivisorOn_le_of_iOrder _ _ _ hclass hI

end SGPT.BDivisor
