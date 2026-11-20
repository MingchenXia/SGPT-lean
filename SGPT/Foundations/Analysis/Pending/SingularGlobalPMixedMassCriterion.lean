import SGPT.Foundations.Analysis.Pending.SingularPositiveConvexMixedMass
import SGPT.Foundations.Analysis.Pending.SingularConvexMixedMassContinuity
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMaximum
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality

set_option autoImplicit false

/-! # Actual global P-equivalence criterion with possibly zero original masses -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassCriterion

open FirstPass FirstPass.PositiveClasses RelativeEnergy DiagonalMass GlobalNonPluripolar
  ThetaPshConvexCombination EndpointMixedMassConvexCombination
  SingularPositiveConvexMixedMass SingularConvexMixedMassContinuity SingularGlobalPOrder
  SingularGlobalPMaximum SingularGlobalPMixedMassEquality SingularPositiveCommonBackgroundExistence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
private theorem endpointMixedMass_last {θ : ClosedRealOneOneForm n M}
    {p u : M → EReal} (hp : IsThetaPshPotential θ.val p)
    (hu : IsThetaPshPotential θ.val u) :
    endpointMixedMass θ p u hp hu (Fin.last n) = diagonalPotentialMass θ u hu := by
  have ht : endpointMixedPotential (Fin.last n) u p = (fun _ : Fin n => u) := by
    funext i
    simp only [endpointMixedPotential, Fin.val_last, if_pos i.isLt]
  exact congrArg (fun μ : Measure M => μ univ)
    (UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
      (endpointMixedPotential_thetaPlurisubharmonic θ (Fin.last n) u p hu hp)
      (fun _ : Fin n => hu.1))

private theorem endpointMixedMass_eq_of_sourcePEquivalent
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u v p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hp : IsThetaPshPotential θ.val p)
    (huv : SourcePEquivalent (n := n) u v) (j : Fin (n + 1)) :
    endpointMixedMass θ p u hp hu j = endpointMixedMass θ p v hp hv j := by
  have hup : ∀ i, IsThetaPshPotential θ.val (endpointMixedPotential j u p i) := by
    intro i
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact hu | exact hp
  have hvp : ∀ i, IsThetaPshPotential θ.val (endpointMixedPotential j v p i) := by
    intro i
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact hv | exact hp
  have href := sourcePOrder_refl_of_isThetaPshPotential omega hp
  have hrel : ∀ i, SourcePEquivalent (n := n)
      (endpointMixedPotential j u p i) (endpointMixedPotential j v p i) := by
    intro i
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact huv | exact ⟨href, href⟩
  exact globalMixedMass_eq_of_sourcePEquivalent omega hup hvp hrel

/-- Genuine positive convex perturbations, actual independent mixed
preservation and the coefficient-one limit identify ordered inputs in the
source global relation, even when their original masses vanish. -/
theorem sourcePEquivalent_of_le_of_endpointMixedMass_eq
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u v p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hp : IsThetaPshPotential θ.val p)
    (hpp : HasPositivePotentialMass θ p hp) (hle : u ≤ v)
    (hmass : ∀ j : Fin (n + 1), endpointMixedMass θ p u hp hu j =
      endpointMixedMass θ p v hp hv j) : SourcePEquivalent (n := n) u v := by
  have hstage {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
      SourcePEquivalent (n := n) (convexComb a u p) (convexComb a v p) := by
    have hU := isThetaPshPotential_convexComb_closed hu hp ha0.le ha1.le
    have hV := isThetaPshPotential_convexComb_closed hv hp ha0.le ha1.le
    have hUp := hasPositivePotentialMass_convexComb_of_right hu hp hpp ha0 ha1
    have hVp := hasPositivePotentialMass_convexComb_of_right hv hp hpp ha0 ha1
    have hUV := sourcePOrder_of_moreSingularOn omega θ θ hU hV
      (MoreSingularOn.of_le fun x _ => convexComb_mono ha0.le ha1.le hle le_rfl x)
    exact (sourcePEquivalent_iff_diagonalPotentialMass_eq_of_sourcePOrder omega θ
      hU hV hUp hVp hUV).mpr
      (diagonalPotentialMass_convexComb_eq_of_endpointMixedMass_eq omega
        hu hv hp hmass ha0.le ha1.le)
  let Θ := θ + omega.form
  have huΘ : IsThetaPshPotential Θ.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu omega.isSemipositive
  have hvΘ : IsThetaPshPotential Θ.val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv omega.isSemipositive
  have hpΘ : IsThetaPshPotential Θ.val p :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hp omega.isSemipositive
  have hupΘ : HasPositivePotentialMass Θ u huΘ := by
    simpa only [one_smul] using hasPositivePotentialMass_add_smul omega hu zero_lt_one
  have hvpΘ : HasPositivePotentialMass Θ v hvΘ := by
    simpa only [one_smul] using hasPositivePotentialMass_add_smul omega hv zero_lt_one
  have hcoeff (k : ℕ) : 0 < 1 - 1 / ((k : ℝ) + 2) ∧
      1 - 1 / ((k : ℝ) + 2) < 1 := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    have hden : 0 < (k : ℝ) + 2 := by linarith
    have hsmall : 1 / ((k : ℝ) + 2) < 1 := (div_lt_one hden).mpr (by linarith)
    have hpos : 0 < 1 / ((k : ℝ) + 2) := one_div_pos.mpr hden
    constructor <;> linarith
  let a : ℕ → Icc (0 : ℝ) 1 := fun k =>
    ⟨1 - 1 / ((k : ℝ) + 2), (hcoeff k).1.le, (hcoeff k).2.le⟩
  have hsmall : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hat : Tendsto a atTop
      (𝓝 (⟨1, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)) := by
    apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, sub_zero] using
      (continuous_sub.tendsto (1, (0 : ℝ))).comp
        ((tendsto_const_nhds (x := (1 : ℝ))).prodMk_nhds hsmall)
  let FU : Icc (0 : ℝ) 1 → ℝ := fun a =>
    (endpointMixedMass Θ p (convexComb a.val u p) hpΘ
      (isThetaPshPotential_convexComb_closed huΘ hpΘ a.property.1 a.property.2)
      (Fin.last n)).toReal
  let FV : Icc (0 : ℝ) 1 → ℝ := fun a =>
    (endpointMixedMass Θ p (convexComb a.val v p) hpΘ
      (isThetaPshPotential_convexComb_closed hvΘ hpΘ a.property.1 a.property.2)
      (Fin.last n)).toReal
  have hlimU : Tendsto (fun k => FU (a k)) atTop
      (𝓝 (endpointMixedMass Θ p u hpΘ huΘ (Fin.last n)).toReal) :=
    (tendsto_toReal_endpointMixedMass_convexComb_one omega huΘ hpΘ (Fin.last n)).comp hat
  have hlimV : Tendsto (fun k => FV (a k)) atTop
      (𝓝 (endpointMixedMass Θ p v hpΘ hvΘ (Fin.last n)).toReal) :=
    (tendsto_toReal_endpointMixedMass_convexComb_one omega hvΘ hpΘ (Fin.last n)).comp hat
  have heq : (fun k => FU (a k)) = (fun k => FV (a k)) := by
    funext k
    exact congrArg ENNReal.toReal
      (endpointMixedMass_eq_of_sourcePEquivalent omega
        (isThetaPshPotential_convexComb_closed huΘ hpΘ (a k).property.1 (a k).property.2)
        (isThetaPshPotential_convexComb_closed hvΘ hpΘ (a k).property.1 (a k).property.2)
        hpΘ (hstage (hcoeff k).1 (hcoeff k).2) (Fin.last n))
  rw [heq] at hlimU
  have hreal := tendsto_nhds_unique hlimU hlimV
  rw [endpointMixedMass_last hpΘ huΘ, endpointMixedMass_last hpΘ hvΘ] at hreal
  have hmassΘ : diagonalPotentialMass Θ u huΘ = diagonalPotentialMass Θ v hvΘ :=
    (ENNReal.toReal_eq_toReal_iff'
      (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => huΘ.1)).ne
      (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => hvΘ.1)).ne).mp hreal
  exact (sourcePEquivalent_iff_diagonalPotentialMass_eq_of_sourcePOrder omega Θ
    huΘ hvΘ hupΘ hvpΘ
    (sourcePOrder_of_moreSingularOn omega θ θ hu hv
      (MoreSingularOn.of_le fun x _ => hle x))).mpr hmassΘ

/-- The maximum producer reduces genuine source comparison to pointwise
order; the actual mixed-slot and positive-convex producers then give the
complete criterion without a positive original-mass hypothesis. -/
theorem sourcePEquivalent_iff_endpointMixedMass_eq_of_sourcePOrder
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u v p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hp : IsThetaPshPotential θ.val p)
    (hpp : HasPositivePotentialMass θ p hp) (huv : SourcePOrder (n := n) u v) :
    SourcePEquivalent (n := n) u v ↔
      ∀ j : Fin (n + 1), endpointMixedMass θ p u hp hu j =
        endpointMixedMass θ p v hp hv j := by
  constructor
  · intro h j
    exact endpointMixedMass_eq_of_sourcePEquivalent omega hu hv hp h j
  · intro hmass
    have hw := IsThetaPshPotential.max hu hv
    have hwv := (sourcePOrder_iff_sourcePEquivalent_max omega hu hv).mp huv
    have huw : SourcePEquivalent (n := n) u (fun x => max (u x) (v x)) :=
      sourcePEquivalent_of_le_of_endpointMixedMass_eq omega hu hw hp hpp
        (fun x => le_max_left _ _) (fun j =>
          (hmass j).trans (endpointMixedMass_eq_of_sourcePEquivalent omega hw hv hp hwv j).symm)
    exact ⟨huw.1.trans omega hwv.1, hwv.2.trans omega huw.2⟩

end

end SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassCriterion
