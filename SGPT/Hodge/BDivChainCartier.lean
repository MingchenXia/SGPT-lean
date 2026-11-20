import SGPT.Hodge.BDivChainDivisorial
import SGPT.BDivisor.BlowupModel2Divisor
import SGPT.BDivisor.BlowupModelNef
import SGPT.PSH.LogResolution
import SGPT.Okounkov.TranscendentalLiftingIntegral
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization
import SGPT.Foundations.Analysis.Pending.ResidualNef
import SGPT.Foundations.Analysis.Pending.MeteredDivisorOperations

/-!
# `𝔻(T)` for currents with analytic singularities (`thm:DT`, Step 2)

Source `thm:DT` (chapter *The theory of b-divisors*), Step 2: if `T` has analytic singularities,
take a log resolution `π : Y → X`, `π^*T = [D] + R` with `R` of bounded local potentials; then
`𝔻(T)` is the nef Cartier b-divisor realized by `(π, {R})`.

Formal statements.

* `siuDivisorialPart_eq_of_currentGenericLelong_eq`: the divisorial part `Div T = ∑ ν(T, D)[D]`
  only depends on the generic Lelong numbers of `T`.
* `currentGenericLelong_eq_of_eq_add_bounded`: adding a bounded function to a potential does not
  change generic Lelong numbers.
* `siuDivisorialPart_weightCurrent`: the current `[F] = Θ_F + ddᶜψ_F` of a metered effective
  `ℚ`-divisor is its own divisorial part (support theorem: `[F]` vanishes off `Supp F`).
* `currentBDivisorOn_isRealization_of_logSingularities`: if `u ∘ π = ψ_F + b` with `b` bounded
  (`ResidualNefReduction.HasLogSingularitiesAlong F (u ∘ π)`), then `𝔻(θ + ddᶜu)` is realized by
  `(π, π^*{θ} - {Θ_F})`: on every model `ρ = π ∘ g` dominating `π`,
  `{Reg ρ^*T} = g^*(π^*{θ} - {Θ_F})` (the residual `ρ^*T - [g^*F]` has the Lelong numbers of a
  bounded function).
* `currentBDivisor_isNefCartier_of_hasAnalyticSingularitiesOfType`: for `u ∈ PSH(X, θ)` with
  analytic singularities of a global type `(c, 𝔞)` on a compact connected Kähler `X`, `𝔻(θ_u)` is
  a **nef Cartier b-divisor** over the book's models (`π` a log resolution, Hironaka
  principalization, `π^*{θ} - {Θ_{cD}}` nef: `SGPT.PSH.exists_kahler_logResolution`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology ENNReal Manifold ContDiff

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.BDivisor

/-! ### Divisorial parts and generic Lelong numbers -/

section General

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [CompactSpace M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))

/-- **The divisorial part only depends on the generic Lelong numbers.** -/
theorem siuDivisorialPart_eq_of_currentGenericLelong_eq {S S' : Cur}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) (hS' : SGPT.Siu.IsClosedPositiveCurrent S')
    (h : ∀ D, SGPT.Siu.currentGenericLelong S hS D = SGPT.Siu.currentGenericLelong S' hS' D) :
    SGPT.Siu.siuDivisorialPart S hS = SGPT.Siu.siuDivisorialPart S' hS' := by
  symm
  apply SGPT.Siu.eq_siuDivisorialPart_of_hasSum hS
  intro e η
  simpa only [h] using SGPT.Siu.hasSum_siuDivisorialPart hS' e η

omit [CompactSpace M] in
/-- **Bounded perturbations of the potential do not change generic Lelong numbers**: if
`a = a' + b` with `b` a bounded real function, then `ν(σ + ddᶜa, D) = ν(σ' + ddᶜa', D)`. -/
theorem currentGenericLelong_eq_of_eq_add_bounded {S S' : Cur}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) (hS' : SGPT.Siu.IsClosedPositiveCurrent S')
    {σ σ' : SmoothRealForm (m + 1) M 2} {a a' : M → EReal} {ha : IsThetaPshPotential σ a}
    {ha' : IsThetaPshPotential σ' a'} (hSe : S = thetaPotentialCurrent σ a ha)
    (hS'e : S' = thetaPotentialCurrent σ' a' ha') (b : M → ℝ) (C : ℝ) (hb : ∀ x, |b x| ≤ C)
    (hab : ∀ x, a x = a' x + (b x : EReal)) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    SGPT.Siu.currentGenericLelong S hS D = SGPT.Siu.currentGenericLelong S' hS' D := by
  rw [SGPT.Siu.currentGenericLelong_eq_primeGenericLelong hS hSe,
    SGPT.Siu.currentGenericLelong_eq_primeGenericLelong hS' hS'e]
  unfold SGPT.Siu.primeGenericLelong
  refine iInf_congr fun x => iInf_congr fun _ => ?_
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb x)
  have hgerm : BoundedRealGermAt b x := ⟨C, hC, Eventually.of_forall hb⟩
  have hfun : a = fun y => a' y + (b y : EReal) := funext hab
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
    ← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m), hfun]
  exact CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq hgerm

/-- **The current of a metered divisor is divisorial**: `Div [F] = [F]`. -/
theorem siuDivisorialPart_weightCurrent (F : MeteredEffectiveQDivisor (m + 1) M)
    (hF : IsThetaPshPotential F.curvature.val F.weight)
    (hS : SGPT.Siu.IsClosedPositiveCurrent (thetaPotentialCurrent F.curvature.val F.weight hF)) :
    SGPT.Siu.siuDivisorialPart _ hS = thetaPotentialCurrent F.curvature.val F.weight hF := by
  have h0 : SGPT.Currents.AnalyticSupport.CurrentEqOn
      (thetaPotentialCurrent F.curvature.val F.weight hF) 0 F.supportᶜ := by
    rw [PrimePushforward.thetaPotentialCurrent_eq_integrationCurrent F hF]
    exact PrimePushforward.currentEqOn_integrationCurrent_zero F
  have hint : interior F.support = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨y, hyV, hy⟩ := hF.2 x (interior F.support) isOpen_interior hx
    have hmem : y ∈ F.support := interior_subset hyV
    exact hy hmem
  exact ((SGPT.Currents.AnalyticSupport.eq_siuDivisorialPart_of_currentEqOn_zero hS
    (ResidualNef.isComplexAnalyticSubset_support F) hint h0).1).symm

end General

/-! ### The realization on a log resolution -/

section Realization

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

theorem bottChernClass_congr {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]
    {S S' : ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)}
    (h : S.val = S'.val) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S' :=
  congrArg _ (Subtype.ext h)

/-- **`𝔻(θ_u)` is Cartier, realized on a log resolution.** Let `π` be a model and `F` a metered
effective `ℚ`-divisor on `Y_π` such that `u ∘ π = ψ_F + b` with `b` bounded. Then `𝔻(θ + ddᶜu)` is
realized by `(π, π^*{θ} - {Θ_F})`. -/
theorem currentBDivisorOn_isRealization_of_logSingularities (S : ModelSystem (m + 1) X)
    (π : S.Model) (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) (F : MeteredEffectiveQDivisor (m + 1) π.1.carrier)
    (L : ResidualNefReduction.HasLogSingularitiesAlong F (u ∘ π.1.map)) :
    (currentBDivisorOn S (thetaPotentialCurrent θ.val u hu)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu)).IsRealization π
      (classPullback π.1.isAnalyticModification.1 (RealBottChern.ofRepresentative θ) -
        RealBottChern.ofRepresentative F.curvature) := by
  intro ρ h
  have hle : π.1 ≤ ρ.1 := h
  have hT := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu
  set g := Modification.homOfLE hle with hgdef
  have hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g :=
    Modification.contMDiff_homOfLE hle
  have hgc : π.1.map ∘ g = ρ.1.map := Modification.map_comp_homOfLE hle
  have hgm := Modification.Dominates.isAnalyticModification hle
  have hint : interior (exceptionalLocus (m + 1) g) = ∅ :=
    Modification4.interior_exceptionalLocus_eq_empty hgm
  -- the pulled-back metered divisor and its current on `Y_ρ`
  set FZ := MeteredDivisorOperations.pullback hg hint F with hFZ
  have hFZψ : IsThetaPshPotential FZ.curvature.val FZ.weight :=
    SGPT.Okounkov.TranscendentalLifting.isThetaPshPotential_weight FZ
  have hA := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hFZψ
  -- the pull-back of `T` and its generic Lelong numbers
  have hpull := PrimePushforward.pull_eq_thetaPotentialCurrent ρ.1.isAnalyticModification hT hu
    rfl
  have hP := Modification4.isClosedPositiveCurrent_pull ρ.1.isAnalyticModification hT
  have hν : ∀ D, SGPT.Siu.currentGenericLelong
      (Modification4.pull ρ.1.isAnalyticModification (thetaPotentialCurrent θ.val u hu) hT) hP D =
        SGPT.Siu.currentGenericLelong _ hA D := by
    intro D
    refine currentGenericLelong_eq_of_eq_add_bounded hP hA hpull rfl
      (fun y => L.residual (g y)) L.bound (fun y => L.residual_bound (g y)) (fun y => ?_) D
    have h1 : ρ.1.map y = π.1.map (g y) := (congrFun hgc y).symm
    have h2 := L.weight_add (g y)
    simp only [Function.comp_apply] at h2
    change u (ρ.1.map y) = F.weight (g y) + _
    rw [h1, h2]
  have hDiv : SGPT.Siu.siuDivisorialPart _ hP = thetaPotentialCurrent FZ.curvature.val FZ.weight
      hFZψ := by
    rw [siuDivisorialPart_eq_of_currentGenericLelong_eq hP hA hν]
    exact siuDivisorialPart_weightCurrent FZ hFZψ hA
  -- the classes
  change ρ.1.regPullClass _ hT = _
  rw [Modification.regPullClass_eq, Modification.divPullClass]
  have hclA : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨thetaPotentialCurrent FZ.curvature.val FZ.weight hFZψ, hA.1, hA.2.1⟩ =
        RealBottChern.ofRepresentative FZ.curvature :=
    ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent _ _ hFZψ
  have hclT : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      ⟨thetaPotentialCurrent θ.val u hu, hT.1, hT.2.1⟩ = RealBottChern.ofRepresentative θ :=
    ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent _ _ hu
  rw [bottChernClass_congr (S' := ⟨thetaPotentialCurrent FZ.curvature.val FZ.weight hFZψ, hA.1,
      hA.2.1⟩) hDiv, hclA, hclT]
  rw [Modification.classPullbackOfLE_eq hle hg hgc, map_sub,
    ← classPullback_comp π.1.isAnalyticModification.1 hg]
  congr 1
  exact classPullback_congr hgc.symm _ _ _

end Realization

/-! ### Nefness -/

section Nef

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **`thm:DT`, Step 2: for `T` with analytic singularities, `𝔻(T)` is a nef Cartier b-divisor.**
`X` compact connected Kähler, `u ∈ PSH(X, θ)` with analytic singularities of a global type
`(c, 𝔞)`; models: the book's (finite compositions of blow-ups with smooth centres). -/
theorem currentBDivisor_isNefCartier_of_hasAnalyticSingularitiesOfType
    (ωX : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℚ} {𝔞 : GermIdeal (m + 1) X}
    (htype : HasAnalyticSingularitiesOfType u c 𝔞) :
    (currentBDivisorOn (ModelSystem.blowup (m + 1) X) (thetaPotentialCurrent θ.val u hu)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu)).IsNefCartier := by
  obtain ⟨Y, tY, cY, mY, π, hπ, D, EH, hcpt, -, ⟨κ⟩, -, -, -, -, -, ⟨L⟩, hnef⟩ :=
    SGPT.PSH.exists_kahler_logResolution ωX θ hu htype
  let πM : (ModelSystem.blowup (m + 1) X).Model :=
    ⟨Modification.ofIsBlowupSequence hπ, Modification.isBlowupModel_ofIsBlowupSequence hπ⟩
  have hreal := currentBDivisorOn_isRealization_of_logSingularities
    (ModelSystem.blowup (m + 1) X) πM θ hu _ L
  refine ⟨πM, _, hreal, κ, ?_⟩
  have hsub : ∀ a b : ClosedRealOneOneForm (m + 1) Y, RealBottChern.ofRepresentative (a - b) =
      RealBottChern.ofRepresentative a - RealBottChern.ofRepresentative b := by
    intro a b
    have hab : a - b = a + (-1 : ℝ) • b := by rw [neg_one_smul, sub_eq_add_neg]
    rw [hab, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul, neg_one_smul,
      sub_eq_add_neg]
  change ClassNefWithRespectTo κ (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hπ.contMDiff θ) -
    RealBottChern.ofRepresentative (MeteredDivisorScaling.smul htype.1.le EH).curvature)
  rw [← hsub]
  exact hnef κ

end Nef

end SGPT.Hodge.BDivChain
