import SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive
import SGPT.Foundations.Analysis.Pending.PositiveGlobalPEnvelopeSuprema

set_option autoImplicit false

/-! # Actual positive interpolation and global source competitor bounds

PSWZ arXiv2607.12797v1 Theorem5.1 Step5, explicit big theta.
Original minimal model, genuine positive interpolation and envelope model
are internally produced. Original input/candidate masses may both vanish.
No solver, limiting identity or generic zero-mass idempotence is input.
Complete mathematical blueprint and proofs preceded substantive SOURCE.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualPositiveInterpolationGlobalBound

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  DiagonalMass RelativeEnergy ThetaPshConvexCombination GlobalNonPluripolar GlobalDiagonalScaling
  GlobalDiagonalConvexScaling SingularMinimalCanonicalRay SingularGlobalPOrder

noncomputable section

/-- The literal original convex interpolation with the actual minimal potential. -/
def positiveInterpolation {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (θ : ClosedRealOneOneForm n M) (v : M → EReal) (ε : ℝ) : M → EReal :=
  convexComb (1 - ε) v (thetaPshSupremum θ.val)

private theorem self_le_convex_interpolation {M : Type*} {u V : M → EReal}
    (hut : ∀ x, u x ≠ ⊤) (hVt : ∀ x, V x ≠ ⊤) (huV : u ≤ V)
    {ε : ℝ} (hε0 : 0 < ε) : u ≤ convexComb (1 - ε) u V := by
  intro x
  cases hu : u x using EReal.rec with
  | bot => exact bot_le
  | top => exact (hut x hu).elim
  | coe a =>
    cases hV : V x using EReal.rec with
    | bot => have hh := huV x; simp [hu, hV] at hh
    | top => exact (hVt x hV).elim
    | coe b =>
      have hab : a ≤ b := EReal.coe_le_coe_iff.mp (by simpa only [hu, hV] using huV x)
      change (a : EReal) ≤ (↑(1 - ε) : EReal) * u x + (↑(1 - (1 - ε)) : EReal) * V x
      rw [hu, hV, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hprod := mul_nonneg hε0.le (sub_nonneg.mpr hab)
      nlinarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Bigtheta genuinely supplies the positive minimal reference and original
interpolation/envelope model, with a quantitative actual mass lower bound.
No nonpositive bound or positive mass of the original input is required. -/
theorem exists_positive_model_interpolation
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {v : M → EReal}
    (hv : IsThetaPshPotential θ.val v) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ hw : IsThetaPshPotential θ.val (positiveInterpolation θ v ε),
      HasPositivePotentialMass θ (positiveInterpolation θ v ε) hw ∧
      IsModelPotential θ (singularityEnvelope θ.val (positiveInterpolation θ v ε)) ∧
      ∀ hP : IsThetaPshPotential θ.val (singularityEnvelope θ.val (positiveInterpolation θ v ε)),
        ENNReal.ofReal (ε ^ n) * diagonalPotentialMass θ (thetaPshSupremum θ.val)
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic ≤
        diagonalPotentialMass θ (singularityEnvelope θ.val (positiveInterpolation θ v ε)) hP := by
  let V : M → EReal := thetaPshSupremum θ.val
  have hVm : IsModelPotential θ V := isModelPotential_thetaPshSupremum omega θ hbig
  have hV : IsThetaPshPotential θ.val V := hVm.plurisubharmonic
  have hs0 : 0 < 1 - ε := sub_pos.mpr hε1
  have hs1 : 1 - ε < 1 := by linarith
  have hw : IsThetaPshPotential θ.val (positiveInterpolation θ v ε) :=
    isThetaPshPotential_convexComb hv hV hs0 hs1
  have hswap : convexComb ε V v = positiveInterpolation θ v ε := by
    funext x
    simp only [convexComb, positiveInterpolation, show 1 - (1 - ε) = ε by ring]
    exact add_comm _ _
  have hle := globalMixedMeasure_diagonal_convexComb_le hV hv hε0 hε1 univ
  have hrewrite := globalMixedMeasure_congr rfl
    (show (fun _ : Fin n => convexComb ε V v) =
      (fun _ : Fin n => positiveInterpolation θ v ε) from
        congrArg (fun p => fun _ : Fin n => p) hswap)
    (fun _ => (isThetaPshPotential_convexComb hV hv hε0 hε1).1) (fun _ => hw.1)
  rw [hrewrite] at hle
  change ENNReal.ofReal (ε ^ n) * diagonalPotentialMass θ V hV ≤
    diagonalPotentialMass θ (positiveInterpolation θ v ε) hw at hle
  have hpos : HasPositivePotentialMass θ (positiveInterpolation θ v ε) hw :=
    (ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hε0 n), hVm.positive_mass⟩).trans_le hle
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hw.1.hasSmoothLocalPotentials (positiveInterpolation θ v ε) hw
  have hmass := singularityEnvelopeMassPreserving omega θ (positiveInterpolation θ v ε) hw hP
  have hfix := RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
    omega θ (positiveInterpolation θ v ε) hw hpos
  have hmodel : IsModelPotential θ (singularityEnvelope θ.val (positiveInterpolation θ v ε)) :=
    ⟨hP, hfix.symm, hmass.symm ▸ hpos⟩
  refine ⟨hw, hpos, hmodel, ?_⟩
  intro hp
  rw [singularityEnvelopeMassPreserving omega θ (positiveInterpolation θ v ε) hw hp]
  exact hle

/-- Every actual normalized genuine GLOBAL source competitor is bounded
by the internally positive interpolation envelope, even when both original
candidate and reference masses vanish. The remaining limit is not asserted. -/
theorem le_interpolation_envelope_of_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {v q : M → EReal}
    (hv : IsThetaPshPotential θ.val v) (hv0 : v ≤ 0)
    (hq : IsThetaPshPotential θ.val q) (hq0 : q ≤ 0)
    (hqv : SourcePOrder (n := n) q v) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    q ≤ singularityEnvelope θ.val (positiveInterpolation θ v ε) := by
  obtain ⟨hw, hwpos, _hmodel, _hlower⟩ :=
    exists_positive_model_interpolation omega θ hbig hv hε0 hε1
  have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hvV : v ≤ thetaPshSupremum θ.val := le_thetaPshSupremum hv hv0
  have hvw : v ≤ positiveInterpolation θ v ε :=
    self_le_convex_interpolation hv.1.quasiPlurisubharmonic.ne_top
      hV.1.quasiPlurisubharmonic.ne_top hvV hε0
  have hvwP := sourcePOrder_of_moreSingularOn omega θ θ hv hw
    (MoreSingularOn.of_le fun x _ => hvw x)
  exact PositiveGlobalPEnvelopeSuprema.le_singularityEnvelope_of_sourcePOrder_of_nonpositive
    omega θ hw hwpos hq hq0 (hqv.trans omega hvwP)

end

end SGPT.Foundations.Analysis.Pending.ActualPositiveInterpolationGlobalBound
