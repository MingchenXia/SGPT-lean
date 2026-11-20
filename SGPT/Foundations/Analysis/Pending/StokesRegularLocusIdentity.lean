import SGPT.Foundations.Analysis.Pending.StokesPatchIBP
import SGPT.Foundations.Analysis.Pending.StokesProbeLimit
import SGPT.Foundations.Analysis.Pending.StokesSingularLocusAnalytic
import SGPT.Foundations.Analysis.Pending.PositiveTelescopeExhaustion
import SGPT.Foundations.Analysis.Pending.ClosedCurrentMassFinitenessReduction
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity
import SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.TopPowerDensityUpperBound
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

set_option autoImplicit false

/-!
# Stokes on the regular locus: a smooth potential does not change the mass of `V_reg`

Blueprint `ana:stokes-regular-locus-identity` (TN.4 #4, Stokes against `[V]`, part C of
Stokes' theorem on the regular locus).

For a compact Kähler manifold `(X, β)`, an irreducible analytic subvariety `V` and a smooth `v` with
`β + ddᶜv ≥ 0` (an admissible presentation of the zero class with zero representative and potential
`v`), the regular-piece suprema of `(β + ddᶜv)^k` and `β^k` agree
(`iSup_formPieceMass_currentForm_eq`), unconditionally.  Consequently along every exhaustion the
two finite-piece masses have the same limit, and the pairing-remainder data of
`StokesWeightedPairing` have remainders tending to `0`
(`tendsto_pairingRemainder_of_exhaustion`): this is the content of
`CertifiedClosedCurrentStokes.certifiedFinitePairingRemainderData_of_closed_integrationCurrent`, which
is proved from it (its exhaustion hypotheses were added by human decision I-0902, earlier discussion I-0839).

The proof is the one-sided probe (`StokesProbeLimit.integral_eq_zero_of_probe`) on the measure of a
countable decomposition of `V_reg` (`StokesRegularDecomposition`), with `f` the telescope of
`ddᶜv`, `q_m` the same telescope with `ddᶜχ_m` (`χ_m` the cutoffs along `V_sing`,
`StokesSingularLocusAnalytic.exists_stokesCutoffs_singularLocus`), `b` the telescope with `β`, and
the integration by parts `StokesPatchIBP.integral_measure_ibp`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.StokesRegularLocusIdentity

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.RegularPatchNeighborhood
open FirstPass.MongeAmpere StronglyPositiveForms
open RegularPatchTransition StokesRegularDecomposition StokesPatchIBP SmoothDDCForm

noncomputable section

/-! ### Coordinate algebra of the telescope -/

section Algebra

variable {k : ℕ}

/-- The telescope family: `A` in the slots below `j`, `B` above (slot `j` is to be replaced). -/
def teleFamily (A B : CoordinateRealTwoForm k) (j : Fin k) : Fin k → CoordinateRealTwoForm k :=
  fun i => if (i : ℕ) < (j : ℕ) then A else B

theorem isSemipositiveOneOne_teleFamily {A B : CoordinateRealTwoForm k}
    (hA : IsSemipositiveOneOne A) (hB : IsSemipositiveOneOne B) (j i : Fin k) :
    IsSemipositiveOneOne (teleFamily A B j i) := by
  unfold teleFamily; split_ifs <;> assumption

/-- **Slot monotonicity of the mixed density** for semipositive `(1,1)` families. -/
theorem actualMixedTopDensity_mono {A B : Fin k → CoordinateRealTwoForm k}
    (hA : ∀ i, IsSemipositiveOneOne (A i)) (hBA : ∀ i, IsSemipositiveOneOne (B i - A i)) :
    actualMixedTopDensity A ≤ actualMixedTopDensity B := by
  classical
  have key : ∀ s : Finset (Fin k), actualMixedTopDensity A ≤
      actualMixedTopDensity (fun i => if i ∈ s then B i else A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      set C : Fin k → CoordinateRealTwoForm k := fun l => if l ∈ s then B l else A l with hCdef
      have hC : ∀ l, IsSemipositiveOneOne (C l) := fun l => by
        by_cases hl : l ∈ s
        · simp only [hCdef, if_pos hl]
          have := (hA l).add (hBA l)
          rwa [add_sub_cancel] at this
        · simp only [hCdef, if_neg hl]; exact hA l
      have heq : (fun l => if l ∈ insert i s then B l else A l) =
          Function.update C i (C i + (B i - A i)) := by
        funext l
        by_cases hli : l = i
        · subst hli
          simp [hCdef, hi]
        · simp [hCdef, Finset.mem_insert, hli]
      rw [heq]
      have hsplit := (actualMixedTopDensityMultilinear (n := k)).map_update_add C i (C i) (B i - A i)
      simp only [actualMixedTopDensityMultilinear_apply, Function.update_eq_self] at hsplit
      rw [hsplit]
      have hnn : 0 ≤ actualMixedTopDensity (Function.update C i (B i - A i)) := by
        refine TopDegreeDensity.actualMixedTopDensity_nonneg fun l => ?_
        by_cases hli : l = i
        · subst hli; simpa using hBA l
        · simpa [Function.update_of_ne hli] using hC l
      linarith
  simpa using key Finset.univ

/-- One slot replaced by `x + c y`: linearity of the mixed density. -/
theorem actualMixedTopDensity_update_add_smul (F : Fin k → CoordinateRealTwoForm k) (j : Fin k)
    (x y : CoordinateRealTwoForm k) (c : ℝ) :
    actualMixedTopDensity (Function.update F j (x + c • y)) =
      actualMixedTopDensity (Function.update F j x) + c * actualMixedTopDensity (Function.update F j y) := by
  have h1 := (actualMixedTopDensityMultilinear (n := k)).map_update_add F j x (c • y)
  have h2 := (actualMixedTopDensityMultilinear (n := k)).map_update_smul F j c y
  simp only [actualMixedTopDensityMultilinear_apply, smul_eq_mul] at h1 h2
  rw [h1, h2]

/-- `A • B - C` is a semipositive `(1,1)` form when `C ≤ A B` on complex lines. -/
theorem isSemipositiveOneOne_smul_sub {A : ℝ} {B C : CoordinateRealTwoForm k} (hB : IsOneOne B)
    (hC : IsOneOne C) (hle : ∀ w, C ![w, Complex.I • w] ≤ A * B ![w, Complex.I • w]) :
    IsSemipositiveOneOne (A • B - C) := by
  refine ⟨fun u v => ?_, fun w => ?_⟩
  · simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, hB u v,
      hC u v]
  · simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    linarith [hle w]

/-- **The telescope with a nonnegative slot is nonnegative.** -/
theorem sum_teleFamily_nonneg {A B Y : CoordinateRealTwoForm k} (hA : IsSemipositiveOneOne A)
    (hB : IsSemipositiveOneOne B) (hY : IsSemipositiveOneOne Y) :
    0 ≤ ∑ j : Fin k, actualMixedTopDensity (Function.update (teleFamily A B j) j Y) :=
  Finset.sum_nonneg fun j _ => TopDegreeDensity.actualMixedTopDensity_nonneg fun i => by
    by_cases h : i = j
    · subst h; simpa using hY
    · simpa [Function.update_of_ne h] using isSemipositiveOneOne_teleFamily hA hB j i

/-- **The telescope with `B` in the slot is bounded by the top density of `K B`** when
`K B - A` and `K B - B` are semipositive. -/
theorem sum_teleFamily_le {A B : CoordinateRealTwoForm k} (hA : IsSemipositiveOneOne A)
    (hB : IsSemipositiveOneOne B) {K : ℝ} (hKA : IsSemipositiveOneOne (K • B - A))
    (hKB : IsSemipositiveOneOne (K • B - B)) :
    ∑ j : Fin k, actualMixedTopDensity (Function.update (teleFamily A B j) j B) ≤
      k * (K ^ k * actualTopPowerDensity B) := by
  have hterm : ∀ j : Fin k, actualMixedTopDensity (Function.update (teleFamily A B j) j B) ≤
      K ^ k * actualTopPowerDensity B := fun j => by
    rw [← TopPowerDensityUpperBound.actualTopPowerDensity_smul, ← actualMixedTopDensity_const]
    refine actualMixedTopDensity_mono (fun i => ?_) fun i => ?_
    · by_cases h : i = j
      · subst h; simpa using hB
      · simpa [Function.update_of_ne h] using isSemipositiveOneOne_teleFamily hA hB j i
    · by_cases h : i = j
      · subst h; simpa using hKB
      · simp only [Function.update_of_ne h, teleFamily]
        split_ifs
        · exact hKA
        · exact hKB
  calc ∑ j : Fin k, actualMixedTopDensity (Function.update (teleFamily A B j) j B)
      ≤ ∑ _j : Fin k, K ^ k * actualTopPowerDensity B := Finset.sum_le_sum fun j _ => hterm j
    _ = k * (K ^ k * actualTopPowerDensity B) := by simp

/-- **The telescoping identity** in the form used below: the difference of the top densities of
`A + B` and `A` is the telescope with `B` in the slot. -/
theorem actualTopPowerDensity_add_sub_eq_sum_teleFamily (A B : CoordinateRealTwoForm k) :
    actualTopPowerDensity (A + B) - actualTopPowerDensity A =
      ∑ j : Fin k, actualMixedTopDensity (Function.update (teleFamily (A + B) A j) j B) := by
  rw [CoordinateDensityTelescope.actualTopPowerDensity_add_sub]
  refine Finset.sum_congr rfl fun j _ => congrArg _ (funext fun i => ?_)
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with hij | hij | hij
  · have hne : i ≠ j := fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt hij)
    rw [CoordinateDensityTelescope.telescopeFamily_apply_of_lt _ _ hij,
      Function.update_of_ne hne, teleFamily, if_pos hij]
  · have hije : i = j := Fin.ext hij
    subst hije
    rw [CoordinateDensityTelescope.telescopeFamily_apply_self, Function.update_self]
  · have hne : i ≠ j := fun h => absurd (congrArg Fin.val h) (Nat.ne_of_gt hij)
    rw [CoordinateDensityTelescope.telescopeFamily_apply_of_gt _ _ hij,
      Function.update_of_ne hne, teleFamily, if_neg (Nat.not_lt_of_gt hij)]

end Algebra

/-! ### The slots in patch parameters -/

section Patch

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

theorem coordinateParametrization_mem_target (P : RegularPatch V) {u : ComplexModel V.dim}
    (hu : u ∈ P.parameterDomain) :
    P.coordinateParametrization u ∈ (complexChartAt (n := n) P.center).val.target :=
  P.source_subset (P.flattening.mapsTo_invFun hu)

/-- A coordinate form of type `(1,1)` and semipositive at the chart point pulls back to a
semipositive `(1,1)` form. -/
theorem isSemipositiveOneOne_patchCoordinateForm (a : SmoothRealForm n M 2) (P : RegularPatch V)
    {u : ComplexModel V.dim} (hu : u ∈ P.parameterDomain)
    (h11 : IsOneOne (a.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization u)))
    (hpos : CoefficientSemipositive
      (a.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization u))) :
    IsSemipositiveOneOne (patchCoordinateForm a P u) :=
  PatchDensityTelescope.isOneOne_and_semipositive_patchCoordinateForm a P hu h11 hpos

/-- On complex lines the pulled-back form is the form on the image line. -/
theorem patchCoordinateForm_apply_line (a : SmoothRealForm n M 2) (P : RegularPatch V)
    {u : ComplexModel V.dim} (hu : u ∈ P.parameterDomain) (w : ComplexModel V.dim) :
    patchCoordinateForm a P u ![w, Complex.I • w] =
      a.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization u)
        ![fderiv ℝ P.coordinateParametrization u w,
          Complex.I • fderiv ℝ P.coordinateParametrization u w] := by
  have hLI := AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul
    P hu
  simp only [patchCoordinateForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> simp [hLI]

/-- **Kähler domination in patch parameters.**  For a smooth form `X` of type `(1,1)`, there is
`A > 0` with `A • β - X` semipositive `(1,1)` in the parameters of every patch. -/
theorem exists_smul_sub_isSemipositiveOneOne [CompactSpace M] (beta : KahlerBackground n M)
    (X : SmoothRealForm n M 2)
    (hX : X.IsTypeOneOne) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : RegularPatch V) (u : ComplexModel V.dim), u ∈ P.parameterDomain →
      IsSemipositiveOneOne (A • patchCoordinateForm beta.form.val P u - patchCoordinateForm X P u) := by
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_isSemipositive_add_smul
    (ClosedCurrentMassFinitenessReduction.negForm X) beta.form.val beta.isKahler.1
  refine ⟨A, hA, fun P u hu => ?_⟩
  have hz := coordinateParametrization_mem_target P hu
  have hL := AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul
    P hu
  refine isSemipositiveOneOne_smul_sub
    (RestrictedMassEnvelopeMonotone.isOneOne_compContinuousLinearMap
      (fun a b => beta.form.property.2 _ _ hz a b) _ hL)
    (RestrictedMassEnvelopeMonotone.isOneOne_compContinuousLinearMap (hX _ _ hz) _ hL) fun w => ?_
  rw [patchCoordinateForm_apply_line X P hu, patchCoordinateForm_apply_line beta.form.val P hu]
  have h := hdom _ _ hz (fderiv ℝ P.coordinateParametrization u w)
  simp only [ClosedCurrentMassFinitenessReduction.negForm_coeff,
    ContinuousAlternatingMap.neg_apply] at h
  linarith

/-- A pull-back is additive and homogeneous in the form. -/
theorem patchCoordinateForm_add_smul (a b c : SmoothRealForm n M 2) (r : ℝ)
    (hc : ∀ (e : ComplexChart n M) (z : ComplexModel n), c.coeff e z = a.coeff e z + r • b.coeff e z)
    (P : RegularPatch V) (u : ComplexModel V.dim) :
    patchCoordinateForm c P u = patchCoordinateForm a P u + r • patchCoordinateForm b P u := by
  unfold patchCoordinateForm
  rw [hc]
  ext v
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- `ddᶜ` does not see additive constants. -/
theorem patchCoordinateForm_ddcForm_sub_const {v : M → ℝ} (hv : ChartSmooth (n := n) v) (c : ℝ)
    (hvc : ChartSmooth (n := n) fun y => v y - c) (P : RegularPatch V) {u : ComplexModel V.dim}
    (hu : u ∈ P.parameterDomain) :
    patchCoordinateForm (ddcForm (fun y => v y - c) hvc) P u = patchCoordinateForm (ddcForm v hv) P u := by
  rw [PatchDensityTelescope.patchCoordinateForm_ddcForm P hvc hu,
    PatchDensityTelescope.patchCoordinateForm_ddcForm P hv hu]
  have h := smoothDDC_add (isOpen_parameterDomain P) (contDiffOn_comp_toManifold hv P)
    (contDiffOn_const (c := -c)) hu
  simp only [← sub_eq_add_neg] at h
  rw [h, GlobalPotentialTransforms.smoothDDC_const, add_zero]

end Patch

/-! ### The identity on `V_reg` -/

section Identity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The ambient slots of the `j`-th telescope term: `om` below `j`, `β` above. -/
def slots (om β' : SmoothRealForm n M 2) (j : Fin V.dim) : Fin V.dim → SmoothRealForm n M 2 :=
  fun i => if (i : ℕ) < (j : ℕ) then om else β'

theorem patchMixedDensity_slots (om β' X : SmoothRealForm n M 2) (j : Fin V.dim) (P : RegularPatch V)
    (u : ComplexModel V.dim) :
    patchMixedDensity (Function.update (slots om β' j) j X) P u =
      actualMixedTopDensity (Function.update (teleFamily (patchCoordinateForm om P u)
        (patchCoordinateForm β' P u) j) j (patchCoordinateForm X P u)) := by
  rw [patchMixedDensity, patchCoordinateForm_update]
  congr 2
  funext i
  simp only [slots, teleFamily]
  split_ifs <;> rfl

/-- The telescope as a linear function of the swapped slot. -/
def teleLin {k : ℕ} (A B : CoordinateRealTwoForm k) : CoordinateRealTwoForm k →ₗ[ℝ] ℝ :=
  ∑ j : Fin k, (actualMixedTopDensityMultilinear (n := k)).toLinearMap (teleFamily A B j) j

theorem teleLin_apply {k : ℕ} (A B Y : CoordinateRealTwoForm k) :
    teleLin A B Y = ∑ j : Fin k, actualMixedTopDensity (Function.update (teleFamily A B j) j Y) := by
  simp [teleLin, MultilinearMap.toLinearMap_apply]

/-- The integral over the decomposition measure of the top density of `a`, cut to the pieces, is
the regular-piece supremum. -/
theorem integral_indicator_patchFormDensity (D : RegularDecomposition V) (a : SmoothRealForm n M 2)
    (hnn : ∀ (P : RegularPatch V) (u : ComplexModel V.dim), u ∈ P.parameterDomain →
      0 ≤ PatchFormMass.patchFormDensity a P u)
    (hint : Integrable ({x : ℕ × ComplexModel V.dim | x.2 ∈ D.piece x.1}.indicator fun x =>
      PatchFormMass.patchFormDensity a (D.patch x.1) x.2) D.measure)
    (hfin : (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass a F) ≠ ⊤) :
    ∫ x, {x : ℕ × ComplexModel V.dim | x.2 ∈ D.piece x.1}.indicator (fun x =>
      PatchFormMass.patchFormDensity a (D.patch x.1) x.2) x ∂D.measure =
      (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass a F).toReal := by
  have hsum := D.hasSum_integral_measure hint
  rw [D.iSup_formPieceMass_eq_tsum] at hfin ⊢
  have hfin' : ∀ j, ∫⁻ w in D.piece j, ENNReal.ofReal (PatchFormMass.patchFormDensity a (D.patch j) w) ≠ ⊤ :=
    fun j => ne_top_of_le_ne_top hfin (ENNReal.le_tsum j)
  have hcont : ∀ j, ContinuousOn (PatchFormMass.patchFormDensity a (D.patch j)) (D.piece j) := fun j =>
    (RegularPatchTransition.continuousOn_actualTopPowerDensity_patchCoordinateForm a
      (D.patch j)).mono (D.piece_subset j)
  have hterm : ∀ j, ∫ w in D.piece j, {x : ℕ × ComplexModel V.dim | x.2 ∈ D.piece x.1}.indicator
      (fun x => PatchFormMass.patchFormDensity a (D.patch x.1) x.2) (j, w) =
      (∫⁻ w in D.piece j, ENNReal.ofReal (PatchFormMass.patchFormDensity a (D.patch j) w)).toReal := by
    intro j
    rw [setIntegral_congr_fun (D.measurableSet_piece j) (g := PatchFormMass.patchFormDensity a (D.patch j))
      fun w hw => indicator_of_mem (show (j, w) ∈ {x : ℕ × ComplexModel V.dim | x.2 ∈ D.piece x.1} from hw) _]
    exact integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_mem (D.measurableSet_piece j)).mono fun w hw => hnn _ w (D.piece_subset j hw))
      ((hcont j).aestronglyMeasurable (D.measurableSet_piece j))
  rw [funext hterm] at hsum
  have h2 := ENNReal.hasSum_toReal hfin
  rw [← ENNReal.tsum_toReal_eq hfin'] at h2
  exact hsum.unique h2

/-- **Stokes on the regular locus** (blueprint `ana:stokes-regular-locus-identity`).  For a smooth
potential `v` with `β + ddᶜv ≥ 0`, the regular-piece suprema of `(β + ddᶜv)^k` and `β^k` agree. -/
theorem iSup_formPieceMass_currentForm_eq [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    (⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) F) =
      ⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass beta.form.val F := by
  classical
  set om := ACTopMassComparison.currentForm q hvs with hωdef
  set β' := beta.form.val with hβ'def
  obtain ⟨D⟩ := nonempty_regularDecomposition V
  set k := V.dim with hk
  -- the current form is `β + ddᶜv`
  have hωc : ∀ (e : ComplexChart n M) (z : ComplexModel n),
      om.coeff e z = β'.coeff e z + (ddcForm v hvs).coeff e z := fun e z => by
    simp [hωdef, ACTopMassComparison.currentForm, perturbedRepresentative, hq, hβ'def]
  have hpcf : ∀ (P : RegularPatch V) u, patchCoordinateForm om P u =
      patchCoordinateForm β' P u + patchCoordinateForm (ddcForm v hvs) P u := fun P u =>
    PatchDensityTelescope.patchCoordinateForm_add _ _ _ hωc P u
  -- semipositivity of the two fixed slots
  have hpole : ∀ (e : ComplexChart n M) (z : ComplexModel n), e.val.symm z ∉ poleSet q.potential :=
    fun e z => by rw [ACTopMassComparison.poleSet_eq_empty q hpot]; simp
  have hω11 : om.IsTypeOneOne := fun e z hz => by
    have h := (AdmissibleCurrentFormPositivity.coordinateCurrentForm_isOneOne_and_semipositive q e hz
      (hpole e z)).1
    rwa [ACTopMassComparison.coordinateCurrentForm_eq q hvs hpot] at h
  have hΩpos : ∀ (P : RegularPatch V) u, u ∈ P.parameterDomain →
      IsSemipositiveOneOne (patchCoordinateForm om P u) := fun P u hu => by
    have hz := coordinateParametrization_mem_target P hu
    have h := AdmissibleCurrentFormPositivity.coordinateCurrentForm_isOneOne_and_semipositive q _ hz
      (hpole _ _)
    rw [ACTopMassComparison.coordinateCurrentForm_eq q hvs hpot] at h
    exact isSemipositiveOneOne_patchCoordinateForm om P hu h.1 h.2
  have hBpos : ∀ (P : RegularPatch V) u, u ∈ P.parameterDomain →
      IsSemipositiveOneOne (patchCoordinateForm β' P u) := fun P u hu => by
    have hz := coordinateParametrization_mem_target P hu
    exact isSemipositiveOneOne_patchCoordinateForm β' P hu
      (fun a b => beta.form.property.2 _ _ hz a b) (fun w => beta.isSemipositive _ _ hz w)
  obtain ⟨Aω, hAω, hdomω⟩ := exists_smul_sub_isSemipositiveOneOne (V := V) beta om hω11
  -- the cutoffs along `V_sing`
  obtain ⟨C, χ, hχ, hC, h01, hzero, hlim, hsemi⟩ :=
    StokesSingularLocusAnalytic.exists_stokesCutoffs_singularLocus beta V
  have hχ11 : ∀ m, (ddcForm (χ m) (hχ m)).IsTypeOneOne := fun m =>
    (ManifoldTubePositivity.ddcClosedForm (χ m) (hχ m)).property.2
  have hdomχ : ∀ m, ∃ A : ℝ, 0 < A ∧ ∀ (P : RegularPatch V) u, u ∈ P.parameterDomain →
      IsSemipositiveOneOne (A • patchCoordinateForm β' P u -
        patchCoordinateForm (ddcForm (χ m) (hχ m)) P u) := fun m =>
    exists_smul_sub_isSemipositiveOneOne beta _ (hχ11 m)
  choose Aχ hAχ hdomχ' using hdomχ
  -- the decomposition measure and the functions of the probe
  set Pc : Set (ℕ × ComplexModel k) := {x | x.2 ∈ D.piece x.1} with hPc
  set γ : ℕ × ComplexModel k → M := fun x => (D.patch x.1).toManifold x.2 with hγ
  set Ωc : ℕ × ComplexModel k → CoordinateRealTwoForm k := fun x =>
    patchCoordinateForm om (D.patch x.1) x.2 with hΩc
  set Bc : ℕ × ComplexModel k → CoordinateRealTwoForm k := fun x =>
    patchCoordinateForm β' (D.patch x.1) x.2 with hBc
  set T : ℕ × ComplexModel k → CoordinateRealTwoForm k →ₗ[ℝ] ℝ := fun x => teleLin (Ωc x) (Bc x)
    with hT
  set topB : ℕ × ComplexModel k → ℝ := Pc.indicator fun x =>
    PatchFormMass.patchFormDensity β' (D.patch x.1) x.2 with htopB
  set topΩ : ℕ × ComplexModel k → ℝ := Pc.indicator fun x =>
    PatchFormMass.patchFormDensity om (D.patch x.1) x.2 with htopΩ
  set f : ℕ × ComplexModel k → ℝ := fun x => topΩ x - topB x with hf
  set b : ℕ × ComplexModel k → ℝ := Pc.indicator fun x => T x (Bc x) with hb
  set qm : ℕ → ℕ × ComplexModel k → ℝ := fun m => Pc.indicator fun x =>
    T x (patchCoordinateForm (ddcForm (χ m) (hχ m)) (D.patch x.1) x.2) with hqm
  set ε : ℕ → ℝ := fun m => C / ((m : ℝ) + 1) with hε
  have hdom : ∀ x ∈ Pc, x.2 ∈ (D.patch x.1).parameterDomain := fun x hx => D.piece_subset x.1 hx
  -- `T` through the ambient slots
  have hTslots : ∀ x (X : SmoothRealForm n M 2), T x (patchCoordinateForm X (D.patch x.1) x.2) =
      ∑ j : Fin k, patchMixedDensity (Function.update (slots om β' j) j X) (D.patch x.1) x.2 :=
    fun x X => by
      rw [hT, teleLin_apply]
      exact Finset.sum_congr rfl fun j _ => (patchMixedDensity_slots om β' X j _ _).symm
  -- measurability on the decomposition measure
  have hmeasG : ∀ G : ℕ × ComplexModel k → ℝ, (∀ j, ContinuousOn (fun w => G (j, w)) (D.piece j)) →
      AEStronglyMeasurable G D.measure := fun G hG =>
    (D.aestronglyMeasurable_measure_iff).2 fun j => (hG j).aestronglyMeasurable (D.measurableSet_piece j)
  have hmeasI : ∀ G : ℕ × ComplexModel k → ℝ, (∀ j, ContinuousOn (fun w => G (j, w)) (D.piece j)) →
      AEStronglyMeasurable (Pc.indicator G) D.measure := fun G hG =>
    hmeasG _ fun j => (hG j).congr fun w hw => indicator_of_mem (show (j, w) ∈ Pc from hw) G
  have hcontT : ∀ X : SmoothRealForm n M 2, ∀ j,
      ContinuousOn (fun w => T (j, w) (patchCoordinateForm X (D.patch j) w)) (D.piece j) := fun X j => by
    simp_rw [hTslots]
    exact continuousOn_finsetSum _ fun l _ =>
      (continuousOn_patchMixedDensity _ (D.patch j)).mono (D.piece_subset j)
  have hcontTop : ∀ (a : SmoothRealForm n M 2) j,
      ContinuousOn (fun w => PatchFormMass.patchFormDensity a (D.patch j) w) (D.piece j) := fun a j =>
    (RegularPatchTransition.continuousOn_actualTopPowerDensity_patchCoordinateForm a
      (D.patch j)).mono (D.piece_subset j)
  have hcontComp : ∀ {g : M → ℝ}, ChartSmooth (n := n) g → ∀ j,
      ContinuousOn (fun w => g ((D.patch j).toManifold w)) (D.piece j) := fun hg j =>
    (contDiffOn_comp_toManifold hg (D.patch j)).continuousOn.mono (D.piece_subset j)
  -- pointwise bounds
  obtain ⟨C1, hC1, hdens⟩ := ClosedCurrentMassFinitenessReduction.patchFormDensity_currentForm_le_kahler_multiple
    (q := q) (hvs := hvs) (beta := beta) hpot
  have htopB0 : ∀ x, 0 ≤ topB x := fun x => by
    by_cases hx : x ∈ Pc
    · rw [htopB, indicator_of_mem hx]
      exact PatchDensityTelescope.patchFormDensity_kahler_nonneg beta _ (hdom x hx)
    · rw [htopB, indicator_of_notMem hx]
  have hfbd : ∀ x, |f x| ≤ (C1 ^ k + 1) * topB x := fun x => by
    by_cases hx : x ∈ Pc
    · have h1 := PatchDensityTelescope.patchFormDensity_currentForm_nonneg q hvs hpot _ (hdom x hx)
      have h2 := PatchDensityTelescope.patchFormDensity_kahler_nonneg beta _ (hdom x hx)
      have h3 := hdens _ (hdom x hx)
      simp only [hf, htopΩ, htopB, indicator_of_mem hx]
      rw [abs_le]; constructor <;> nlinarith
    · simp [hf, htopΩ, htopB, indicator_of_notMem hx]
  set K : ℝ := Aω + 1 with hK
  have hb0 : ∀ x, 0 ≤ b x := fun x => by
    by_cases hx : x ∈ Pc
    · rw [hb, indicator_of_mem hx, hT, teleLin_apply]
      exact sum_teleFamily_nonneg (hΩpos _ _ (hdom x hx)) (hBpos _ _ (hdom x hx))
        (hBpos _ _ (hdom x hx))
    · rw [hb, indicator_of_notMem hx]
  have hbbd : ∀ x, b x ≤ k * (K ^ k * topB x) := fun x => by
    by_cases hx : x ∈ Pc
    · rw [hb, htopB, indicator_of_mem hx, indicator_of_mem hx, hT, teleLin_apply]
      have hu := hdom x hx
      refine sum_teleFamily_le (hΩpos _ _ hu) (hBpos _ _ hu) ?_ ?_
      · have : K • Bc x - Ωc x = (Aω • Bc x - Ωc x) + Bc x := by
          rw [hK, add_smul, one_smul]; abel
        rw [this]; exact (hdomω _ _ hu).add (hBpos _ _ hu)
      · have : K • Bc x - Bc x = Aω • Bc x := by rw [hK, add_smul, one_smul]; abel
        rw [this]; exact (hBpos _ _ hu).smul hAω.le
    · rw [hb, htopB, indicator_of_notMem hx, indicator_of_notMem hx]; simp
  -- the cutoff slot and `q_m`
  have hqpos : ∀ m x, 0 ≤ qm m x + ε m * b x := fun m x => by
    by_cases hx : x ∈ Pc
    · have hu := hdom x hx
      set Z := ManifoldTubePositivity.ddcClosedForm (χ m) (hχ m) + (C / ((m : ℝ) + 1)) • beta.form
        with hZ
      have hpZ : patchCoordinateForm Z.val (D.patch x.1) x.2 =
          patchCoordinateForm (ddcForm (χ m) (hχ m)) (D.patch x.1) x.2 + ε m • Bc x :=
        patchCoordinateForm_add_smul _ _ _ _ (fun e z => rfl) _ _
      have hz := coordinateParametrization_mem_target _ hu
      have hZpos := isSemipositiveOneOne_patchCoordinateForm Z.val _ hu
        (fun a c => Z.property.2 _ _ hz a c) (fun w => hsemi m _ _ hz w)
      simp only [hqm, hb, indicator_of_mem hx]
      rw [← smul_eq_mul, ← map_smul, ← map_add, ← hpZ, hT, teleLin_apply]
      exact sum_teleFamily_nonneg (hΩpos _ _ hu) (hBpos _ _ hu) hZpos
    · simp [hqm, hb, indicator_of_notMem hx]
  have hqbd : ∀ m x, |qm m x| ≤ (Aχ m + ε m) * b x := fun m x => by
    by_cases hx : x ∈ Pc
    · have hu := hdom x hx
      have hup : qm m x ≤ Aχ m * b x := by
        have h := sum_teleFamily_nonneg (hΩpos _ _ hu) (hBpos _ _ hu) (hdomχ' m _ _ hu)
        rw [← teleLin_apply, map_sub, map_smul, smul_eq_mul] at h
        simp only [hqm, hb, indicator_of_mem hx]
        linarith
      have hlo := hqpos m x
      have hb0x := hb0 x
      have hε0 : 0 ≤ ε m := div_nonneg hC.le (by positivity)
      rw [abs_le]; constructor <;> nlinarith [hAχ m]
    · simp [hqm, hb, indicator_of_notMem hx]
  -- integrability
  have htopB_mem : ∀ j w, w ∈ D.piece j →
      topB (j, w) = PatchFormMass.patchFormDensity β' (D.patch j) w := fun j w hw => by
    rw [htopB]; exact indicator_of_mem (show (j, w) ∈ Pc from hw) _
  have htopΩ_mem : ∀ j w, w ∈ D.piece j →
      topΩ (j, w) = PatchFormMass.patchFormDensity om (D.patch j) w := fun j w hw => by
    rw [htopΩ]; exact indicator_of_mem (show (j, w) ∈ Pc from hw) _
  have htopBint : Integrable topB D.measure := by
    rw [D.integrable_measure_iff]
    refine ⟨fun j => ?_, ?_⟩
    · exact ((hcontTop β' j).congr fun w hw => htopB_mem j w hw).aestronglyMeasurable
        (D.measurableSet_piece j)
    · have heq : ∀ j, ∫⁻ w in D.piece j, ‖topB (j, w)‖ₑ =
          ∫⁻ w in D.piece j, ENNReal.ofReal (PatchFormMass.patchFormDensity β' (D.patch j) w) :=
        fun j => setLIntegral_congr_fun (D.measurableSet_piece j) fun w hw => by
          rw [htopB_mem j w hw, Real.enorm_eq_ofReal
            (PatchDensityTelescope.patchFormDensity_kahler_nonneg beta _ (D.piece_subset j hw))]
      simp_rw [heq]
      rw [← D.iSup_formPieceMass_eq_tsum]
      exact (SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V).lt_top
  have hfint : Integrable f D.measure :=
    (htopBint.const_mul (C1 ^ k + 1)).mono'
      (hmeasG _ fun j => ((hcontTop om j).sub (hcontTop β' j)).congr fun w hw => by
        simp only [hf]; rw [htopΩ_mem j w hw, htopB_mem j w hw]; rfl)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfbd x)
  have hbint : Integrable b D.measure :=
    (htopBint.const_mul ((k : ℝ) * K ^ k)).mono'
      (hmeasI _ fun j => hcontT β' j)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb0 x), mul_assoc]; exact hbbd x)
  have hqint : ∀ m, Integrable (qm m) D.measure := fun m =>
    (hbint.const_mul (Aχ m + ε m)).mono' (hmeasI _ fun j => hcontT (ddcForm (χ m) (hχ m)) j)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hqbd m x)
  -- the potential and the cutoffs along the pieces
  have hvcont : Continuous v := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    set e := complexChartAt (n := n) x
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    have h1 : ContinuousAt (fun z => v (e.val.symm z)) (e.val x) :=
      (hvs e).continuousOn.continuousAt (e.val.open_target.mem_nhds (e.val.map_source hx))
    have h2 : ContinuousAt (fun y => v (e.val.symm (e.val y))) x :=
      h1.comp (e.val.continuousAt hx)
    exact h2.congr (Filter.eventuallyEq_of_mem (e.val.open_source.mem_nhds hx)
      fun y hy => by simp only [e.val.left_inv hy])
  obtain ⟨Cv, hCv⟩ := isCompact_univ.exists_bound_of_continuousOn hvcont.continuousOn
  have hvbd : ∀ x : ℕ × ComplexModel k, -Cv ≤ v (γ x) ∧ v (γ x) ≤ Cv := fun x => by
    have h := hCv (γ x) (mem_univ _)
    rw [Real.norm_eq_abs, abs_le] at h
    exact h
  have hvm : AEStronglyMeasurable (fun x => v (γ x)) D.measure := hmeasG _ fun j => hcontComp hvs j
  have hχm : ∀ m, AEStronglyMeasurable (fun x => χ m (γ x)) D.measure := fun m =>
    hmeasG _ fun j => hcontComp (hχ m) j
  have hχlim : ∀ᵐ x ∂D.measure, Tendsto (fun m => χ m (γ x)) atTop (𝓝 1) :=
    (ae_mem_piece D).mono fun x hx =>
      hlim _ (D.image_subset_regularLocus x.1 ⟨x.2, hx, rfl⟩)
  have hε0 : ∀ m, 0 ≤ ε m := fun m => div_nonneg hC.le (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun m => ?_
    simp only [Function.comp_apply, hε]
    push_cast
    rfl
  -- the integration by parts, telescope term by telescope term
  have hompot : HasPatchPotentials V om :=
    HasPatchPotentials.add (hasPatchPotentials_closed beta.form) (hasPatchPotentials_ddcForm hvs) hωc
  have hslotpot : ∀ j : Fin k, ∀ i, i ≠ j → HasPatchPotentials V (slots om β' j i) := fun j i _ => by
    unfold slots
    split_ifs
    · exact hompot
    · exact hasPatchPotentials_closed beta.form
  have hχreg : ∀ m, ∀ x ∈ tsupport (χ m), x ∈ V.carrier →
      x ∈ regularLocus (n := n) V.carrier V.dim := fun m x hx hxV => by
    obtain ⟨O, hO, hsing, hz⟩ := hzero m
    by_contra hreg
    have hxO : x ∈ O := hsing ⟨hxV, hreg⟩
    obtain ⟨y, hyO, hy⟩ := mem_closure_iff.1 hx O hO hxO
    exact hy (hz y hyO)
  have hibp : ∀ m (c : ℝ), ∫ x, χ m (γ x) * f x ∂D.measure = ∫ x, (v (γ x) - c) * qm m x ∂D.measure := by
    intro m c
    have hvc : ChartSmooth (n := n) fun y => v y - c := fun e => (hvs e).sub contDiffOn_const
    have hI := fun j : Fin k => integral_measure_ibp D (a := slots om β' j) j (hslotpot j) (hχ m) hvc
      (hχreg m)
    have hL : (fun x => χ m (γ x) * f x) =ᵐ[D.measure] fun x => ∑ j : Fin k,
        χ m ((D.patch x.1).toManifold x.2) * patchMixedDensity
          (Function.update (slots om β' j) j (ddcForm (fun y => v y - c) hvc)) (D.patch x.1) x.2 :=
      (ae_mem_piece D).mono fun x hx => by
        have hu := hdom x hx
        beta_reduce
        rw [← Finset.mul_sum]
        congr 1
        simp only [hf, htopΩ, htopB, indicator_of_mem (show x ∈ Pc from hx)]
        simp only [PatchFormMass.patchFormDensity]
        rw [hpcf, actualTopPowerDensity_add_sub_eq_sum_teleFamily, ← hpcf]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [patchMixedDensity_slots, patchCoordinateForm_ddcForm_sub_const hvs c hvc _ hu]
    have hR : (fun x => (v (γ x) - c) * qm m x) =ᵐ[D.measure] fun x => ∑ j : Fin k,
        (v ((D.patch x.1).toManifold x.2) - c) * patchMixedDensity
          (Function.update (slots om β' j) j (ddcForm (χ m) (hχ m))) (D.patch x.1) x.2 :=
      (ae_mem_piece D).mono fun x hx => by
        beta_reduce
        rw [← Finset.mul_sum]
        congr 1
        simp only [hqm, indicator_of_mem (show x ∈ Pc from hx)]
        exact hTslots x _
    rw [integral_congr_ae hL, integral_congr_ae hR,
      integral_finsetSum _ fun j _ => (hI j).1, integral_finsetSum _ fun j _ => (hI j).2.1]
    exact Finset.sum_congr rfl fun j _ => (hI j).2.2
  -- the probe
  have hprobe := StokesProbeLimit.integral_eq_zero_of_probe (μ := D.measure) (f := f) (b := b)
    (v := fun x => v (γ x)) (χ := fun m x => χ m (γ x)) (q := qm) (ε := ε) (lo := -Cv) (hi := Cv)
    hfint hbint hb0 hvbd hvm (fun m x => h01 m (γ x)) hχm hχlim hε0 hεlim hqint hqpos hibp
  -- read off the two suprema
  have hΩint : Integrable topΩ D.measure := by
    have : topΩ = fun x => f x + topB x := by funext x; simp [hf]
    rw [this]; exact hfint.add htopBint
  have hfinB := SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V
  obtain ⟨C2, hC2, hmass⟩ := ClosedCurrentMassFinitenessReduction.formPieceMass_currentForm_le_kahler_multiple
    (q := q) (hvs := hvs) (beta := beta) hpot
  have hfinΩ : (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass om F) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C2 ^ V.dim)) hfinB)
      (iSup_le fun F => ?_)
    exact (hmass F).trans (by gcongr; exact le_iSup (fun F : RegularPieceFamily V (∅ : Set M) =>
      PatchFormMass.formPieceMass β' F) F)
  have hIΩ := integral_indicator_patchFormDensity D om
    (fun P u hu => PatchDensityTelescope.patchFormDensity_currentForm_nonneg q hvs hpot P hu) hΩint hfinΩ
  have hIB := integral_indicator_patchFormDensity D β'
    (fun P u hu => PatchDensityTelescope.patchFormDensity_kahler_nonneg beta P hu) htopBint hfinB
  have hsub : ∫ x, f x ∂D.measure = ∫ x, topΩ x ∂D.measure - ∫ x, topB x ∂D.measure :=
    integral_sub hΩint htopBint
  rw [hprobe] at hsub
  have heq : (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass om F).toReal =
      (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass β' F).toReal := by
    rw [← hIΩ, ← hIB]; linarith
  exact (ENNReal.toReal_eq_toReal_iff' hfinΩ hfinB).mp heq

end Identity

/-! ### Along an exhaustion: the remainder of the pairing data tends to zero -/

section Exhaustion

open PositiveTelescopeExhaustion PartitionPairingCollarErrorReduction

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Along every exhaustion the two finite-piece masses have the same limit**: their difference
tends to `0`. -/
theorem tendsto_abs_formPieceMass_sub_of_exhaustion [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (hmono : ∀ m, RegularPieceExhaustion.coveredRegion (H m) ⊆
      RegularPieceExhaustion.coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m,
        K ⊆ RegularPieceExhaustion.coveredRegion (H m)) :
    Tendsto (fun m => |(PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) (H m)).toReal -
      (PatchFormMass.formPieceMass beta.form.val (H m)).toReal|) atTop (𝓝 0) := by
  have hex : ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
      Disjoint K (∅ : Set M) → ∃ m, K ⊆ RegularPieceExhaustion.coveredRegion (H m) :=
    fun K hK hKreg _ => hexh K hK hKreg
  have hΩ := RegularPieceExhaustion.tendsto_formPieceMass_of_exhaustion isClosed_empty hmono hex
    (ACTopMassComparison.currentForm q hvs)
  have hB := RegularPieceExhaustion.tendsto_formPieceMass_of_exhaustion isClosed_empty hmono hex
    beta.form.val
  have hid := iSup_formPieceMass_currentForm_eq beta V q hq hvs hpot
  have hfinB := SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V
  rw [hid] at hΩ
  have h1 := (ENNReal.tendsto_toReal hfinB).comp hΩ
  have h2 := (ENNReal.tendsto_toReal hfinB).comp hB
  have h3 := (h1.sub h2).abs
  simpa only [Function.comp_apply, sub_self, abs_zero] using h3

/-- **The pairing-remainder datum of the `m`-th family of a certified exhaustion**, with remainder
`|mass_{H m}(β + ddᶜv) - mass_{H m}(β)|` (`StokesWeightedPairing`). -/
noncomputable def pairingRemainder_of_exhaustion [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs ((H m).patch i) ((H m).piece i))
    (m : ℕ) :
    FiniteTelescopePairingRemainderData
      (FormPiecePositiveTelescopeData.of_positiveLocalTelescopePotential (hgood m)).toFormPieceTelescopeData :=
  StokesWeightedPairing.finiteTelescopePairingRemainderData_of_finite _
    (fun i _ hw => PatchDensityTelescope.patchFormDensity_currentForm_nonneg q hvs hpot ((H m).patch i)
      ((H m).piece_subset i hw))
    (fun i _ hw => PatchDensityTelescope.patchFormDensity_kahler_nonneg beta ((H m).patch i)
      ((H m).piece_subset i hw))
    (ClosedCurrentMassFinitenessReduction.formPieceMass_currentForm_ne_top (q := q) (hvs := hvs)
      (beta := beta) hpot (H m))
    (ne_top_of_le_ne_top (SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V)
      (le_iSup (fun F : RegularPieceFamily V (∅ : Set M) =>
        PatchFormMass.formPieceMass beta.form.val F) (H m)))

theorem pairingRemainder_of_exhaustion_remainder [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs ((H m).patch i) ((H m).piece i))
    (m : ℕ) :
    (pairingRemainder_of_exhaustion beta V q hvs hpot H hgood m).remainder =
      |(PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) (H m)).toReal -
        (PatchFormMass.formPieceMass beta.form.val (H m)).toReal| :=
  StokesWeightedPairing.finiteTelescopePairingRemainderData_of_finite_remainder _ _ _ _ _

/-- **The remainders tend to zero along a certified EXHAUSTION** -- the content of
`CertifiedClosedCurrentStokes.certifiedFinitePairingRemainderData_of_closed_integrationCurrent`,
whose body (after its exhaustion hypotheses `hmono`, `hexh` were added, I-0902 on I-0839) is
`⟨pairingRemainder_of_exhaustion .., tendsto_pairingRemainder_of_exhaustion .. hmono hexh⟩`. -/
theorem tendsto_pairingRemainder_of_exhaustion [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs ((H m).patch i) ((H m).piece i))
    (hmono : ∀ m, RegularPieceExhaustion.coveredRegion (H m) ⊆
      RegularPieceExhaustion.coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m,
        K ⊆ RegularPieceExhaustion.coveredRegion (H m)) :
    Tendsto (fun m => (pairingRemainder_of_exhaustion beta V q hvs hpot H hgood m).remainder)
      atTop (𝓝 0) := by
  simp_rw [pairingRemainder_of_exhaustion_remainder]
  exact tendsto_abs_formPieceMass_sub_of_exhaustion beta V q hq hvs hpot hmono hexh


/-- **The pairing-remainder datum for ANY telescope data of the `m`-th family** (the version of
`pairingRemainder_of_exhaustion` that does not fix the certified telescope data): with remainder
`|mass_{H m}(β + ddᶜv) - mass_{H m}(β)|`.  Instantiated with
`FormPieceTelescopeData.of_localTelescopePotential (hgood m)` it is the datum of
`PositiveDimensionalClosedCurrentStokes.ClosedCurrentFinitePairingRemainderData` (the named input
stated with that structure was retired, I-0902). -/
noncomputable def pairingRemainderOfTelescope [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (T : ∀ m, FormPieceMassCurrentPairingBridge.FormPieceTelescopeData beta q hvs (H m)) (m : ℕ) :
    FiniteTelescopePairingRemainderData (T m) :=
  StokesWeightedPairing.finiteTelescopePairingRemainderData_of_finite (T m)
    (fun i _ hw => PatchDensityTelescope.patchFormDensity_currentForm_nonneg q hvs hpot ((H m).patch i)
      ((H m).piece_subset i hw))
    (fun i _ hw => PatchDensityTelescope.patchFormDensity_kahler_nonneg beta ((H m).patch i)
      ((H m).piece_subset i hw))
    (ClosedCurrentMassFinitenessReduction.formPieceMass_currentForm_ne_top (q := q) (hvs := hvs)
      (beta := beta) hpot (H m))
    (ne_top_of_le_ne_top (SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V)
      (le_iSup (fun F : RegularPieceFamily V (∅ : Set M) =>
        PatchFormMass.formPieceMass beta.form.val F) (H m)))

theorem pairingRemainderOfTelescope_remainder [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (T : ∀ m, FormPieceMassCurrentPairingBridge.FormPieceTelescopeData beta q hvs (H m)) (m : ℕ) :
    (pairingRemainderOfTelescope beta V q hvs hpot H T m).remainder =
      |(PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) (H m)).toReal -
        (PatchFormMass.formPieceMass beta.form.val (H m)).toReal| :=
  StokesWeightedPairing.finiteTelescopePairingRemainderData_of_finite_remainder _ _ _ _ _

/-- **The remainders tend to zero along a certified EXHAUSTION, for any telescope data.**  With
the exhaustion hypotheses `hmono`, `hexh`, `⟨pairingRemainderOfTelescope .. T,
tendsto_pairingRemainderOfTelescope .. T hmono hexh⟩` with `T m = of_localTelescopePotential (hgood m)`
is a `PositiveDimensionalClosedCurrentStokes.ClosedCurrentFinitePairingRemainderData` for the
exhaustion. -/
theorem tendsto_pairingRemainderOfTelescope [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (T : ∀ m, FormPieceMassCurrentPairingBridge.FormPieceTelescopeData beta q hvs (H m))
    (hmono : ∀ m, RegularPieceExhaustion.coveredRegion (H m) ⊆
      RegularPieceExhaustion.coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m,
        K ⊆ RegularPieceExhaustion.coveredRegion (H m)) :
    Tendsto (fun m => (pairingRemainderOfTelescope beta V q hvs hpot H T m).remainder)
      atTop (𝓝 0) := by
  simp_rw [pairingRemainderOfTelescope_remainder]
  exact tendsto_abs_formPieceMass_sub_of_exhaustion beta V q hq hvs hpot hmono hexh

end Exhaustion

end

end SGPT.Foundations.Analysis.Pending.StokesRegularLocusIdentity
