import SGPT.Okounkov.TranscendentalLiftingValuation
import SGPT.Okounkov.TranscendentalLiftingIntegral
import SGPT.Okounkov.TranscendentalLiftingBlowupKahler
import SGPT.Okounkov.FlagLiftingExistence
import SGPT.Okounkov.FlagLiftingComposition
import SGPT.Okounkov.TranscendentalCoreDivisorGenerators
import SGPT.PSH.LogResolution
import SGPT.Okounkov.FlagLiftingStrictTransform

/-!
# Log resolutions with a lifted flag

Source: blueprint node `tok:resolution-lifting` (chapter `claude-okounkov-transcendental`), i.e.
DRWNXZ Theorem 4.3 combined with the resolution of §2 (Włodarczyk 2009, Theorem 3.6.1). As in the
blueprint, the smooth semipositive form `β` of the source is replaced by the bounded remainder of
the log resolution (`ψ ∘ p = ψ_D + b`, `b` bounded), i.e. by the current
`R' = p^*θ - Θ_D + dd^c b` with bounded potentials.

`exists_logResolution_flagLifting`: let `(W, W•)` be a compact connected Kähler manifold with a
smooth flag and `ψ ∈ PSH(W, θ)` with analytic singularities of a global type `(c, 𝔞)` (for
instance `θ + dd^c ψ ∈ 𝒜ᵍ(θ)`). There are a finite sequence of blow-ups with smooth centres
`p : V → W` from a compact connected Kähler manifold `V` carrying a smooth flag `V•` that lifts
`W•` along `p` (`IsFlagLifting W V p`), and a metered effective `ℚ`-divisor `D` on `V` (the pullback
of `c` times the principalized divisor of `𝔞`), such that `ψ ∘ p = ψ_D + b` with `b` bounded
(`ResidualNefReduction.HasLogSingularitiesAlong D (ψ ∘ p)`), `b` may be chosen
`(p^*θ - Θ_D)`-psh (so `p^*T = [D] + R'` with `R' = p^*θ - Θ_D + dd^c b` closed positive with
bounded potentials, `exists_residual_current`), and `ν_{V•}(p^* T) = ν_{V•}([D])`
(`flagValuation V (ψ ∘ p) = flagValuation V ψ_D`).

Auxiliary facts used for the first coordinate in `tok:approx-pushforward`:
`IsFlagLifting.exists_mem_first_notMem_exceptionalLocus` (a lifted `W₁` is not contained in the
exceptional locus), `flagValuation_zero_eq_zero_of_ne_bot`, and
`vecMul_correctionMatrixReal_zero` (correction matrices preserve the first coordinate).

`flagLifting_comp_correction`: if `W•` lifts a flag `Y•` of `X` along `π` with correction `g`, then
`V•` lifts `Y•` along `π ∘ p` with correction `g h`, `h = cor(W•, p)`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalLifting

open Set Filter
open scoped Topology Manifold ContDiff Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Okounkov.TranscendentalCore

section Residual

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The residual current of a log resolution is positive with bounded potentials** (book
`lma:logsingrem`, first part; DRWNXZ §2). On a compact connected complex manifold, if
`φ ∈ PSH(M, θ)` has log singularities along a metered effective `ℚ`-divisor `D`
(`φ = ψ_D + b` with `b` bounded), then the residual `b` has a bounded `(θ - Θ_D)`-psh
representative `b*` with `φ = ψ_D + b*` everywhere: `θ + dd^c φ = [D] + R'` with
`R' = θ - Θ_D + dd^c b*` closed positive with bounded potentials. -/
theorem exists_residual_current [CompactSpace M] [ConnectedSpace M]
    {θ : ClosedRealOneOneForm n M} {D : MeteredEffectiveQDivisor n M} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (L : ResidualNefReduction.HasLogSingularitiesAlong D φ) :
    ∃ b : M → EReal, ThetaPlurisubharmonic (θ - D.curvature).val b ∧
      (∀ x, ((-L.bound : ℝ) : EReal) ≤ b x ∧ b x ≤ (L.bound : EReal)) ∧
      ∀ x, φ x = D.weight x + b x := by
  have : Nonempty M := ConnectedSpace.toNonempty
  set A := D.support with hA
  have hoff := ResidualNefReduction.thetaPshOff_residual hφ.1 L
  have hanalytic : IsComplexAnalyticSubset (n := n) A :=
    ResidualNef.isComplexAnalyticSubset_support D
  have hproper : A ≠ univ := L.support_ne_univ hφ.2
  have hAi : interior A = ∅ :=
    PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ hanalytic hproper
  obtain ⟨hext, hoffeq, -⟩ := thetaPsh_extend_across_analytic (θ - D.curvature) hanalytic hAi hoff
    L.locallyBoundedAboveOff
  refine ⟨extensionAcross A (fun x => (L.residual x : EReal)), hext, fun x =>
    ⟨ResidualNef.le_extensionAcross_of_interior_eq_empty hAi
      (fun y => EReal.coe_le_coe_iff.mpr (L.neg_bound_le y)) x,
    ResidualNef.extensionAcross_le_of_forall_le
      (fun y => EReal.coe_le_coe_iff.mpr (L.le_bound y)) x⟩, fun x => ?_⟩
  by_cases hx : x ∈ A
  · have hbot : D.weight x = ⊥ := hx
    have hne : extensionAcross A (fun x => (L.residual x : EReal)) x ≠ ⊤ := by
      intro htop
      have h := ResidualNef.extensionAcross_le_of_forall_le (A := A)
        (fun y => EReal.coe_le_coe_iff.mpr (L.le_bound y)) x
      rw [htop] at h
      exact (EReal.coe_lt_top _).not_ge h
    rw [L.weight_add x, hbot, EReal.bot_add, EReal.bot_add]
  · rw [hoffeq x hx, L.weight_add x]

end Residual

section FirstCoordinate

/-- A lifted first flag member is not contained in the exceptional locus: there is a point of
`W₁` at which `π` is a local biholomorphism (the image of the exceptional locus has codimension at
least two, while `π(W₁) = Y₁` is a hypersurface). -/
theorem IsFlagLifting.exists_mem_first_notMem_exceptionalLocus {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) :
    ∃ w ∈ W.flag (1 : Fin (m + 2)), w ∉ exceptionalLocus (m + 1) π := by
  obtain ⟨VY, hY, hdY⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold F.firstDivisor
  have hdY' : VY.dim + 1 = m + 1 := by rw [hdY]
  have hav :=
    AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
      hπ.1 VY hdY'
  obtain ⟨y, hy, hyE⟩ := not_subset.mp hav
  have hy' : y ∈ F.flag (1 : Fin (m + 2)) := hY ▸ hy
  obtain ⟨w, hw, hwy⟩ := (Set.ext_iff.mp (hπ.component_image_eq (1 : Fin (m + 2))) y).mpr hy'
  exact ⟨w, hw, fun h => hyE ⟨w, h, hwy⟩⟩

/-- If a quasi-psh potential is finite at a point of `Y₁`, the first coordinate of its valuation
(the generic Lelong number along `Y₁`) vanishes. -/
theorem flagValuation_zero_eq_zero_of_ne_bot {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {y : F.carrier} (hy : y ∈ F.flag (1 : Fin (m + 2)))
    (hφy : φ y ≠ ⊥) : flagValuation F φ 0 = 0 := by
  rw [flagValuation_eq hφ]
  have h0 := potentialFlagValuation_first F hφ
  have hlel : lelongNumber (n := m + 1) φ y = 0 :=
    le_antisymm (le_of_not_gt fun h => hφy (eq_bot_of_lelongNumber_pos (Nat.succ_pos m) hφ.1 h))
      bot_le
  have hsq : squaredLogLelongNumber (n := m + 1) φ y = 0 := by
    have h := lelongNumber_eq_two_mul_squaredLog (n := m + 1) (Nat.succ_ne_zero m) φ y
    rw [hlel] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hsg : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ = 0 :=
    le_antisymm ((iInf_le (fun y : F.flag (1 : Fin (m + 2)) =>
      squaredLogLelongNumber (n := m + 1) φ y.val) ⟨y, hy⟩).trans hsq.le) bot_le
  rw [hsg] at h0
  have h0' : potentialFlagValuation F hφ 0 = 0 := by exact_mod_cast h0
  show ((potentialFlagValuation F hφ 0 : NNReal) : ℝ) = 0
  rw [h0', NNReal.coe_zero]

/-- Correction matrices preserve the first coordinate: `(x g)₀ = x₀` (the first column of `g` is
`e₁`). -/
theorem vecMul_correctionMatrixReal_zero {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (x : Fin (m + 1) → ℝ) :
    (x ᵥ* correctionMatrixReal hπ) 0 = x 0 := by
  have h0 : correctionMatrixReal hπ 0 0 = 1 := by
    show ((flagLiftingCorrectionMatrix (m + 1) F W π hπ 0 0 : ℤ) : ℝ) = 1
    rw [flagLiftingCorrectionMatrix_succ_eq]
    simp
  have hs : ∀ i : Fin m, correctionMatrixReal hπ i.succ 0 = 0 := fun i => by
    show ((flagLiftingCorrectionMatrix (m + 1) F W π hπ i.succ 0 : ℤ) : ℝ) = 0
    rw [flagLiftingCorrectionMatrix_succ_eq]
    simp
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, h0, hs, mul_one, mul_zero,
    Finset.sum_const_zero, add_zero]

/-- The inverse correction matrix preserves the first coordinate too. -/
theorem vecMul_correctionMatrixReal_inv_zero {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (x : Fin (m + 1) → ℝ) :
    (x ᵥ* (correctionMatrixReal hπ)⁻¹) 0 = x 0 := by
  have h := vecMul_correctionMatrixReal_zero hπ (x ᵥ* (correctionMatrixReal hπ)⁻¹)
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_det_correctionMatrixReal hπ),
    Matrix.vecMul_one] at h
  exact h.symm

end FirstCoordinate

/-- A log-singularity presentation pulls back along a holomorphic map whose exceptional locus is
nowhere dense: `φ ∘ p = ψ_{p^*D} + b ∘ p`. -/
def HasLogSingularitiesAlong.pullback {n : ℕ} {M Z : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {p : Z → M}
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ p)
    (hint : interior (exceptionalLocus n p) = ∅) {D : MeteredEffectiveQDivisor n M}
    {φ : M → EReal} (L : ResidualNefReduction.HasLogSingularitiesAlong D φ) :
    ResidualNefReduction.HasLogSingularitiesAlong
      (MeteredDivisorOperations.pullback hp hint D) (fun z => φ (p z)) where
  residual := fun z => L.residual (p z)
  bound := L.bound
  residual_bound := fun z => L.residual_bound (p z)
  weight_add := fun z => L.weight_add (p z)

/-- **Log resolution with a lifted flag** (blueprint `tok:resolution-lifting`). -/
theorem exists_logResolution_flagLifting {m : ℕ} (W : OriginalFlagGeometry.{u} (m + 1))
    (θ : ClosedRealOneOneForm (m + 1) W.carrier) {ψ : W.carrier → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) {c : ℚ} {𝔞 : GermIdeal (m + 1) W.carrier}
    (htype : HasAnalyticSingularitiesOfType ψ c 𝔞) :
    ∃ (V : OriginalFlagGeometry.{u} (m + 1)) (p : V.carrier → W.carrier)
      (hp : IsBlowupSequence (m + 1) W.carrier V.carrier p)
      (D : MeteredEffectiveQDivisor (m + 1) V.carrier), IsFlagLifting W V p ∧
      Nonempty (ResidualNefReduction.HasLogSingularitiesAlong D (fun y => ψ (p y))) ∧
      (∃ (b : V.carrier → EReal) (C : ℝ),
        ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hp.contMDiff θ - D.curvature).val b ∧
        (∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal)) ∧ ∀ y, ψ (p y) = D.weight y + b y) ∧
      flagValuation V (fun y => ψ (p y)) = flagValuation V D.weight := by
  obtain ⟨Y, _, _, _, ρ, hρ, D₁, EH, hcpt, -, hK, -, -, -, -, -, ⟨L⟩, -⟩ :=
    SGPT.PSH.exists_kahler_logResolution W.omega θ hψ htype
  obtain ⟨ωY⟩ := hK
  have hρmod : IsAnalyticModification (n := m + 1) ρ :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hρ
  obtain ⟨V, p, hp, hV⟩ := exists_flagLifting_dominating_nativeModel (m + 1) W Y ωY ρ hρmod
  have hpmod : IsAnalyticModification (n := m + 1) p :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hp
  have hint := interior_exceptionalLocus_eq_empty_of_isAnalyticModification hpmod
  have hρp := HironakaChowLemma.isBlowupSequence_comp hρ hp
  set D := MeteredDivisorOperations.pullback hp.contMDiff hint
    (MeteredDivisorScaling.smul htype.1.le EH) with hD
  let L' : ResidualNefReduction.HasLogSingularitiesAlong D (fun y => ψ (ρ (p y))) :=
    HasLogSingularitiesAlong.pullback hp.contMDiff hint L
  have hmod : IsAnalyticModification (n := m + 1) (ρ ∘ p) :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hρp
  have hψp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hmod θ hψ
  refine ⟨V, ρ ∘ p, hρp, D, hV, ⟨L'⟩, ?_, ?_⟩
  · -- the residual current `R'` is positive with bounded potentials
    obtain ⟨b, hb, hbd, hbeq⟩ := exists_residual_current hψp L'
    exact ⟨b, L'.bound, hb, hbd, hbeq⟩
  -- the valuation only sees the divisor
  have hfun : (fun y => ψ ((ρ ∘ p) y)) = fun y => D.weight y + (L'.residual y : EReal) :=
    funext fun y => L'.weight_add y
  rw [hfun] at hψp ⊢
  exact flagValuation_add_bounded (isThetaPshPotential_weight D) hψp L'.residual_bound

/-- **Composite liftings** (blueprint `tok:resolution-lifting`, last sentence): if `W•` lifts `Y•`
along `π` with correction `g` and `V•` lifts `W•` along `p` with correction `h`, then `V•` lifts
`Y•` along `π ∘ p` with correction `g h`. -/
theorem flagLifting_comp_correction {n : ℕ} {F W V : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) :
    ∃ hπp : IsFlagLifting F V (π ∘ p),
      correctionMatrixReal hπp = correctionMatrixReal hπ * correctionMatrixReal hp :=
  ⟨hπ.comp hp, correctionMatrixReal_comp hπ hp (hπ.comp hp)⟩

end SGPT.Okounkov.TranscendentalLifting
