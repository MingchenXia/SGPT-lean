import SGPT.Foundations.Analysis.Pending.PotentialSmoothTruncation
import SGPT.Foundations.Analysis.Pending.SubvarietyStokesMass
import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

set_option autoImplicit false

/-!
# Restricted masses of potentials with poles, by smooth truncation

Source: Boucksom, *On the volume of a line bundle*, Proposition 2.6 (monotone
approximation of non-pluripolar masses by truncations); CT22, Lemma 2.1; blueprint
`ana:kahler-restricted-mass-bound`.

Let `(X, β)` be compact Kähler, `V ⊆ X` irreducible of dimension `k`, and `u` a
`β`-psh potential with smooth analytic singularities not identically `-∞` on `V`.
For `j ∈ ℕ` the smooth truncation `u_j = -j + P(u + j)`
(`PotentialSmoothTruncation.smoothTruncation`) is a smooth `β`-psh function equal
to `u` near every point where `u > -j + 1`.  On a patch piece avoiding the poles of
`u`, the sets `{u ≥ -j + 2}` increase to the whole piece, and on them the
top-power densities of `β + ddᶜu` and `β + ddᶜu_j` coincide.  Hence
`∫_{V_reg \ P(u)} (β + ddᶜu)^k ≤ sup_j ∫_{V_reg} (β + ddᶜu_j)^k`
(`acTopMass_le_iSup_truncPresentation`).  By Stokes against `[V]` every term on the
right equals `∫_{V_reg} β^k`, which is finite by Lelong
(`SubvarietyStokesMass`).  This proves
`exists_acTopMass_le_of_zero_representative_of_stokes`, the content of
`Pending.KahlerRestrictedMassBound`.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.KahlerMassTruncation

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
  PotentialSmoothTruncation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Presentations of the zero class at error `1` for a Kähler background. -/
abbrev ZeroClassPresentation (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) :=
  AdmissibleRestrictedCurrentPresentation beta (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩

variable {beta : KahlerBackground n M} {V : ClosedIrreducibleAnalyticSubvariety n M}

theorem isSemipositive_zero_add_one_smul (beta : KahlerBackground n M) :
    (0 + (1 : ℝ) • beta.form).val.IsSemipositive := by
  rw [zero_add, one_smul]
  exact beta.isSemipositive

theorem not_carrier_subset_empty (V : ClosedIrreducibleAnalyticSubvariety n M) :
    ¬ V.carrier ⊆ (∅ : Set M) := by
  obtain ⟨x, hx, -⟩ := V.exists_regular_point
  exact fun h => h hx

omit [TopologicalSpace M] in
/-- A real-valued potential has no poles. -/
theorem poleSet_coe (v : M → ℝ) : poleSet (fun x => (v x : EReal)) = ∅ := by
  ext x
  simp

/-- The presentation `β + ddᶜ0`. -/
def zeroPresentation (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) : ZeroClassPresentation beta V where
  representative := 0
  represents := rfl
  potential := fun _ => 0
  potential_psh :=
    (LocalPotentials.isThetaPshPotential_zero_iff _).mpr (isSemipositive_zero_add_one_smul beta)
  smoothAnalyticSingularities := by
    refine HasManifoldSmoothAnalyticSingularities.smoothOffPole ?_
    have h := hasManifoldSmoothAnalyticSingularities_coe (n := n) (M := M) (v := fun _ => 0)
      (fun e => contDiffOn_const)
    simpa using h
  not_carrier_subset_poleSet := by
    have h := poleSet_coe (M := M) (fun _ => 0)
    simp only [EReal.coe_zero] at h
    rw [h]
    exact not_carrier_subset_empty V

/-- The smooth truncation of a presentation with zero representative at level `-t`. -/
def truncPresentation (q : ZeroClassPresentation beta V) (hq : q.representative = 0)
    (t : ℝ) : ZeroClassPresentation beta V where
  representative := 0
  represents := rfl
  potential := fun x => (smoothTruncation q.potential t x : EReal)
  potential_psh := by
    have h := q.potential_psh.1
    rw [hq] at h
    exact isThetaPshPotential_smoothTruncation_of_smoothOffPole
      (isSemipositive_zero_add_one_smul beta) h q.smoothAnalyticSingularities t
  smoothAnalyticSingularities := by
    have h := q.potential_psh.1
    rw [hq] at h
    exact (hasManifoldSmoothAnalyticSingularities_coe
      (chartSmooth_smoothTruncation_of_smoothOffPole h q.smoothAnalyticSingularities t)).smoothOffPole
  not_carrier_subset_poleSet := by
    rw [poleSet_coe]
    exact not_carrier_subset_empty V

theorem chartSmooth_truncPresentation (q : ZeroClassPresentation beta V)
    (hq : q.representative = 0) (t : ℝ) :
    ∃ v : M → ℝ, ChartSmooth (n := n) v ∧
      (truncPresentation q hq t).potential = fun x => (v x : EReal) := by
  have h := q.potential_psh.1
  rw [hq] at h
  exact ⟨_, chartSmooth_smoothTruncation_of_smoothOffPole h q.smoothAnalyticSingularities t, rfl⟩

/-- Where `u > -t + 1`, the patch densities of `u` and of its truncation agree. -/
theorem patchDensity_truncPresentation (q : ZeroClassPresentation beta V)
    (hq : q.representative = 0) (t : ℝ) (P : RegularPatch V) {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) (hlt : ((-t + 1 : ℝ) : EReal) < q.potential (P.toManifold w)) :
    patchDensity q P w = patchDensity (truncPresentation q hq t) P w := by
  set e := complexChartAt (n := n) P.center
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hlt' : ((-t + 1 : ℝ) : EReal) < q.potential (e.val.symm (P.coordinateParametrization w)) :=
    hlt
  have heq := eventuallyEq_smoothTruncation_of_smoothOffPole q.smoothAnalyticSingularities t e hz
    hlt'
  have hddc := smoothDDC_congr heq
  simp only [patchDensity, coordinateCurrentForm, perturbedRepresentative, hq]
  simp only [truncPresentation, EReal.toReal_coe]
  rw [hddc]

/-- The truncation region `{w ∈ dom P | u(P w) ≥ c}` is measurable. -/
theorem measurableSet_truncRegion (q : ZeroClassPresentation beta V) (P : RegularPatch V)
    (c : EReal) :
    MeasurableSet {w | w ∈ P.parameterDomain ∧ c ≤ q.potential (P.toManifold w)} := by
  have husc : UpperSemicontinuous q.potential :=
    q.potential_psh.1.quasiPlurisubharmonic.upperSemicontinuous
  have hopen : IsOpen {x | q.potential x < c} := by
    exact upperSemicontinuous_iff_isOpen_preimage.mp husc c
  have hdom := AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P
  have hO := (RegularPatch.continuousOn_toManifold P).isOpen_inter_preimage hdom hopen
  have : {w | w ∈ P.parameterDomain ∧ c ≤ q.potential (P.toManifold w)} =
      P.parameterDomain \ (P.parameterDomain ∩ P.toManifold ⁻¹' {x | q.potential x < c}) := by
    ext w
    simp [not_lt]
  rw [this]
  exact hdom.measurableSet.diff hO.measurableSet

/-- **Truncation bound.**  The restricted mass of a potential with poles is bounded
by the supremum of the restricted masses of its smooth truncations. -/
theorem acTopMass_le_iSup_truncPresentation (q : ZeroClassPresentation beta V)
    (hq : q.representative = 0) :
    acTopMass q ≤ ⨆ j : ℕ, acTopMass (truncPresentation q hq j) := by
  refine iSup_le fun F => ?_
  let S : Fin F.size → ℕ → Set (ComplexModel V.dim) := fun i j =>
    F.piece i ∩ {w | w ∈ (F.patch i).parameterDomain ∧
      (((-(j : ℝ) + 2 : ℝ)) : EReal) ≤ q.potential ((F.patch i).toManifold w)}
  have hSmono : ∀ i, Monotone (S i) := by
    intro i j k hjk w hw
    refine ⟨hw.1, hw.2.1, le_trans ?_ hw.2.2⟩
    have : (j : ℝ) ≤ k := Nat.cast_le.mpr hjk
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hSunion : ∀ i, F.piece i = ⋃ j, S i j := by
    intro i
    ext w
    simp only [mem_iUnion]
    constructor
    · intro hw
      have hdom := F.piece_subset i hw
      have hne : q.potential ((F.patch i).toManifold w) ≠ ⊥ := fun hbot =>
        Set.disjoint_left.mp (F.image_disjoint_avoid i) ⟨w, hw, rfl⟩ hbot
      obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : EReal) ≤ q.potential ((F.patch i).toManifold w) := by
        induction h : q.potential ((F.patch i).toManifold w) using EReal.rec with
        | bot => exact absurd h hne
        | top => exact ⟨0, le_top⟩
        | coe x => exact ⟨x, le_rfl⟩
      obtain ⟨j, hj⟩ := exists_nat_ge (2 - r)
      refine ⟨j, hw, hdom, le_trans (EReal.coe_le_coe_iff.mpr (by linarith)) hr⟩
    · rintro ⟨j, hw, -⟩
      exact hw
  have hSmeas : ∀ i j, MeasurableSet (S i j) := fun i j =>
    (F.measurableSet_piece i).inter (measurableSet_truncRegion q (F.patch i) _)
  have hstep : ∀ i j, ∫⁻ w in S i j, ENNReal.ofReal (patchDensity q (F.patch i) w) ≤
      ∫⁻ w in F.piece i, ENNReal.ofReal
        (patchDensity (truncPresentation q hq j) (F.patch i) w) := by
    intro i j
    rw [setLIntegral_congr_fun (hSmeas i j) fun w hw => by
      rw [patchDensity_truncPresentation q hq j (F.patch i) hw.2.1
        (lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) hw.2.2)]]
    exact lintegral_mono_set inter_subset_left
  calc ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity q (F.patch i) w)
      = ∑ i, ⨆ j, ∫⁻ w in S i j, ENNReal.ofReal (patchDensity q (F.patch i) w) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [hSunion i]
        exact setLIntegral_iUnion_of_directed _ (hSmono i).directed_le
    _ = ⨆ j, ∑ i, ∫⁻ w in S i j, ENNReal.ofReal (patchDensity q (F.patch i) w) :=
        ENNReal.finsetSum_iSup_of_monotone fun i _ _ hjk =>
          lintegral_mono_set (hSmono i hjk)
    _ ≤ ⨆ j : ℕ, acTopMass (truncPresentation q hq j) := by
        refine iSup_mono fun j => ?_
        have hdisj : ∀ i, Disjoint ((F.patch i).toManifold '' F.piece i)
            (poleSet (truncPresentation q hq j).potential) := fun i => by
          have h0 : poleSet (truncPresentation q hq j).potential = ∅ := poleSet_coe _
          rw [h0]
          exact disjoint_empty _
        let F' : RegularPieceFamily V (poleSet (truncPresentation q hq j).potential) :=
          { F with image_disjoint_avoid := hdisj }
        refine le_trans ?_ (le_iSup _ F')
        exact Finset.sum_le_sum fun i _ => hstep i j

/-- **Kähler restricted mass bound, from Stokes and Lelong.**  The restricted masses
of the `β`-psh potentials with smooth analytic singularities are bounded by
`∫_{V_reg} β^{dim V}`. -/
theorem exists_acTopMass_le_of_zero_representative_of_stokes [CompactSpace M]
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ q : ZeroClassPresentation beta V, q.representative = 0 → acTopMass q ≤ C := by
  refine ⟨acTopMass (zeroPresentation beta V),
    SubvarietyStokesMass.acTopMass_ne_top_of_zero_potential beta V _ rfl rfl, fun q hq => ?_⟩
  refine (acTopMass_le_iSup_truncPresentation q hq).trans (iSup_le fun j => le_of_eq ?_)
  exact SubvarietyStokesMass.acTopMass_eq_of_smooth beta V _ _ rfl rfl
    (chartSmooth_truncPresentation q hq j) ⟨fun _ => 0, fun e => contDiffOn_const, by
      funext x; simp [zeroPresentation]⟩

end

end SGPT.Foundations.Analysis.Pending.KahlerMassTruncation
