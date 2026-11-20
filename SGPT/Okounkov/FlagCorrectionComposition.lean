import SGPT.Okounkov.FlagTotalTransformComposition
import SGPT.Okounkov.FlagDivisorCurrentCorrection
import SGPT.Okounkov.CurrentFlagCorrection

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open scoped NNReal Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending GermIdealTotalTransform
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent

/-- The same actual reduced downstairs divisor manufactures the geometric
row of a composite. The whole-current consumer is applied to its true
intermediate total transform; no row or current equality is assumed. -/
theorem flagLiftingCorrectionRowNNReal_comp {m : ℕ}
    {F W V : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) :
    flagLiftingCorrectionRowNNReal (hπ.comp hp) =
      flagLiftingCorrectionNNReal m W.tail V.tail hp.tailMap hp.tailMap_isFlagLifting
        (flagLiftingCorrectionRowNNReal hπ) + flagLiftingCorrectionRowNNReal hp := by
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  let : ChartedSpace (ComplexModel m) (V.flag (1 : Fin (m + 2))) := V.tail.charts
  obtain ⟨D, _RA, DtailA, νA, hDI, hstepA, hνA, _hnotA, _htailA, _hcurA,
      _hrowA, hvalA⟩ := hπ.exists_unit_current_correction_row
  obtain ⟨_RC, DtailC, νC, hstepC, hνC, _hnotC, _htailC, _hcurC⟩ :=
    (hπ.comp hp).exists_totalTransform_unit_current_decomposition D hDI
  let DA := EffectiveDivisor.totalTransform hπ.1.1 hπ.interior_exceptional_eq_empty D
  let DC := EffectiveDivisor.totalTransform
    (hπ.comp hp).1.1 (hπ.comp hp).interior_exceptional_eq_empty D
  have hrowA : flagLiftingCorrectionRowNNReal hπ = fun i => (νA i : ℝ≥0) :=
    flagLiftingCorrectionRowNNReal_eq_of_spec hπ ⟨D, hDI, DtailA, hstepA, νA, hνA, rfl⟩
  have hrowC : flagLiftingCorrectionRowNNReal (hπ.comp hp) = fun i => (νC i : ℝ≥0) :=
    flagLiftingCorrectionRowNNReal_eq_of_spec (hπ.comp hp)
      ⟨D, hDI, DtailC, hstepC, νC, hνC, rfl⟩
  have hvalC := currentFlagValuation_totalTransform_eq_of_cartier_step V DC
    DtailC νC hstepC hνC
  have hDA := effectiveDivisorIntegrationCurrent_closed_type_positive W DA
  obtain ⟨R, ⟨hcR, h11R, hR, hall, hNN, _hMatrix⟩, _huniq⟩ :=
    exists_originalCurrentFlagValuation_pullback_correctionMatrix hp
      (effectiveDivisorIntegrationCurrent W DA) hDA.1 hDA.2.1 hDA.2.2
  obtain ⟨EA, _hEAsup, hEA⟩ := DivisorMetric.exists_divisorMetric DA
  let hu := isThetaPshPotential_effectiveDivisorMetric DA EA hEA
  have hread : effectiveDivisorIntegrationCurrent W DA =
      thetaPotentialCurrent EA.curvature.val EA.weight hu :=
    (effectiveDivisorIntegrationCurrent_eq_of_metric W DA EA hEA).trans
      (thetaPotentialCurrent_effectiveDivisorMetric_eq DA EA hEA).symm
  have hcanon : R = effectiveDivisorIntegrationCurrent V DC := by
    calc
      R = thetaPotentialModificationCurrent hp EA.curvature EA.weight hu :=
        hall EA.curvature EA.weight hu hread
      _ = effectiveDivisorIntegrationCurrent V
          (EffectiveDivisor.totalTransform hp.1.1 hp.interior_exceptional_eq_empty DA) :=
        thetaPotentialModificationCurrent_effectiveDivisorMetric_eq_canonicalTotalTransform
          hp DA EA hEA
      _ = effectiveDivisorIntegrationCurrent V DC := by
        rw [← effectiveDivisor_totalTransform_comp hπ hp D]
  have hvalR : currentFlagValuation V R hcR h11R hR =
      (fun i => ((Fin.cons (1 : ℕ) νC : Fin (m + 1) → ℕ) i : ℝ≥0)) := by
    subst R
    exact hvalC
  rw [hvalR, hvalA] at hNN
  funext i
  have hi := congrFun hNN i.succ
  simp only [flagLiftingCorrectionNNReal_succ, Fin.cons_zero, Fin.cons_succ,
    Nat.cast_one, one_mul] at hi
  rw [hrowC, hrowA]
  exact hi

/-- Every integer coefficient follows by genuine finite head/tail induction.
The top row is manufactured by the same-divisor whole-current argument;
the lower block uses the actual composite tail lifting. -/
theorem flagLiftingCorrectionMatrix_comp :
    ∀ (n : ℕ) (F W V : OriginalFlagGeometry.{u} n)
      (π : W.carrier → F.carrier) (p : V.carrier → W.carrier)
      (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p),
      flagLiftingCorrectionMatrix n F V (π ∘ p) (hπ.comp hp) =
        flagLiftingCorrectionMatrix n F W π hπ * flagLiftingCorrectionMatrix n W V p hp := by
  intro n
  induction n with
  | zero =>
      intro F W V π p hπ hp
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      intro F W V π p hπ hp
      have htail : flagLiftingCorrectionMatrix m F.tail V.tail
          (hπ.comp hp).tailMap (hπ.comp hp).tailMap_isFlagLifting =
          flagLiftingCorrectionMatrix m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting *
            flagLiftingCorrectionMatrix m W.tail V.tail hp.tailMap hp.tailMap_isFlagLifting := by
        calc
          _ = flagLiftingCorrectionMatrix m F.tail V.tail (hπ.tailMap ∘ hp.tailMap)
              (hπ.tailMap_isFlagLifting.comp hp.tailMap_isFlagLifting) := by
            congr 1
          _ = _ := ih F.tail W.tail V.tail hπ.tailMap hp.tailMap
            hπ.tailMap_isFlagLifting hp.tailMap_isFlagLifting
      have hrow (j : Fin m) : flagLiftingCorrectionRow (hπ.comp hp) j =
          (∑ k : Fin m, flagLiftingCorrectionRow hπ k *
            flagLiftingCorrectionMatrix m W.tail V.tail hp.tailMap hp.tailMap_isFlagLifting k j) +
          flagLiftingCorrectionRow hp j := by
        obtain ⟨Dπ, hDIπ, DTπ, hstepπ, νπ, hνπ, hcπ⟩ := flagLiftingCorrectionRow_spec hπ
        obtain ⟨Dp, hDIp, DTp, hstepp, νp, hνp, hcp⟩ := flagLiftingCorrectionRow_spec hp
        obtain ⟨Dc, hDIc, DTc, hstepc, νc, hνc, hcc⟩ :=
          flagLiftingCorrectionRow_spec (hπ.comp hp)
        have hnπ := flagLiftingCorrectionRowNNReal_eq_of_spec hπ
          ⟨Dπ, hDIπ, DTπ, hstepπ, νπ, hνπ, rfl⟩
        have hnp := flagLiftingCorrectionRowNNReal_eq_of_spec hp
          ⟨Dp, hDIp, DTp, hstepp, νp, hνp, rfl⟩
        have hnc := flagLiftingCorrectionRowNNReal_eq_of_spec (hπ.comp hp)
          ⟨Dc, hDIc, DTc, hstepc, νc, hνc, rfl⟩
        have hr := congrArg (fun x : ℝ≥0 => (x : ℝ))
          (congrFun (flagLiftingCorrectionRowNNReal_comp hπ hp) j)
        change (flagLiftingCorrectionRowNNReal (hπ.comp hp) j : ℝ) =
          (flagLiftingCorrectionNNReal m W.tail V.tail hp.tailMap hp.tailMap_isFlagLifting
            (flagLiftingCorrectionRowNNReal hπ) j : ℝ) +
          (flagLiftingCorrectionRowNNReal hp j : ℝ) at hr
        have hread := congrFun (flagLiftingCorrectionMatrix_vecMul_nnreal m W.tail V.tail
          hp.tailMap hp.tailMap_isFlagLifting (flagLiftingCorrectionRowNNReal hπ)) j
        rw [← hread, hnc, hnp, hnπ] at hr
        simp only [Matrix.vecMul, dotProduct, NNReal.coe_natCast] at hr
        rw [hcc, hcπ, hcp]
        exact_mod_cast hr
      funext i j
      refine Fin.cases ?_ (fun k => ?_) i
      · refine Fin.cases ?_ (fun l => ?_) j
        · rw [Matrix.mul_apply]
          simp only [flagLiftingCorrectionMatrix, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
        · rw [Matrix.mul_apply]
          simp only [flagLiftingCorrectionMatrix, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ, one_mul]
          exact (hrow l).trans (add_comm _ _)
      · refine Fin.cases ?_ (fun l => ?_) j
        · rw [Matrix.mul_apply]
          simp only [flagLiftingCorrectionMatrix, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
        · have h := congrFun (congrFun htail k) l
          rw [Matrix.mul_apply]
          simpa only [flagLiftingCorrectionMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add] using h

/-- The whole signed-integer correction is first the actual correction of
π, then of p, by the same coefficient product and true finite associativity. -/
theorem flagLiftingCorrection_comp {n : ℕ}
    (F W V : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (p : V.carrier → W.carrier)
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) :
    flagLiftingCorrection n F V (π ∘ p) (hπ.comp hp) =
      (flagLiftingCorrection n F W π hπ).trans (flagLiftingCorrection n W V p hp) := by
  apply DFunLike.ext
  intro v
  apply ofLex.injective
  have hcomp := flagLiftingCorrectionMatrix_vecMul_int n F V (π ∘ p) (hπ.comp hp) (ofLex v)
  have hπv := flagLiftingCorrectionMatrix_vecMul_int n F W π hπ (ofLex v)
  have hpv := flagLiftingCorrectionMatrix_vecMul_int n W V p hp
    (ofLex (flagLiftingCorrection n F W π hπ v))
  calc
    _ = ofLex v ᵥ* flagLiftingCorrectionMatrix n F V (π ∘ p) (hπ.comp hp) := hcomp.symm
    _ = (ofLex v ᵥ* flagLiftingCorrectionMatrix n F W π hπ) ᵥ*
        flagLiftingCorrectionMatrix n W V p hp := by
      rw [flagLiftingCorrectionMatrix_comp]
      exact (Matrix.vecMul_vecMul _ _ _).symm
    _ = _ := by rw [hπv]; exact hpv

end SGPT.Okounkov
