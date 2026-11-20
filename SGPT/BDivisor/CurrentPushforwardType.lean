import SGPT.BDivisor.CurrentPushforward
import SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction

/-!
# Type `(1,1)` and positivity of push-forwards of currents

A real current `T` of degree two is of type `(1,1)` (`GlobalCurrent.IsTypeOneOne`: its
distribution coefficients are invariant under the complex structure `J` in both arguments). This
file proves that this is equivalent to invariance of every chart functional under the action
`η ↦ J^*η` of the complex structure on test forms (`J` has real determinant one, so the volume
form is `J`-invariant), and deduces that push-forwards along holomorphic maps preserve type
`(1,1)` (holomorphic maps commute with `J`). It also proves that push-forwards preserve full
positivity (pull-back by a holomorphic map preserves strongly positive forms), as in Xia,
*Foundations of pluripotential theory*, `prop:proper-current-pushforward`.

Main declarations:

* `SGPT.BDivisor.inChart_twist_of_isTypeOneOne`, `SGPT.BDivisor.isTypeOneOne_of_inChart_twist` —
  type `(1,1)` iff `T(J^*η) = T(η)` for all chart test forms;
* `SGPT.BDivisor.isTypeOneOne_currentPushforward` — `g_* T` is of type `(1,1)` if `T` is;
* `SGPT.BDivisor.isFullPositive_currentPushforward` — `g_* T` is positive if `T` is.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.LocalCurrents
  SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormChartTests
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingGeometricEquality
  SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension
  SGPT.Foundations.Analysis.Pending.XiaoComplexDifferential

section Linear

variable {n : ℕ}

/-- The complex structure has real determinant one. -/
theorem det_modelComplexStructure : LinearMap.det
    ((modelComplexStructure n : ComplexModel n →L[ℝ] ComplexModel n) :
      ComplexModel n →ₗ[ℝ] ComplexModel n) = 1 := by
  have h := Pending.DivisorialChangeOfVariables.det_restrictScalars_eq_normSq
    (Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n))
  change ContinuousLinearMap.det
    ((Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ) = 1
  rw [h, ContinuousLinearMap.det]
  change Complex.normSq (LinearMap.det (Complex.I • LinearMap.id)) = 1
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow, Complex.normSq_I, one_pow]

/-- The complex structure as a real linear equivalence. -/
def complexStructureEquiv (n : ℕ) : ComplexModel n ≃ₗ[ℝ] ComplexModel n where
  toFun v := Complex.I • v
  invFun v := (-Complex.I) • v
  map_add' v w := smul_add _ _ _
  map_smul' c v := smul_comm _ _ _
  left_inv v := by simp [smul_smul]
  right_inv v := by simp [smul_smul]

/-- The volume form of any basis is invariant under the complex structure. -/
theorem basis_det_complexStructure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι ℝ (ComplexModel n)) (x : ι → ComplexModel n) :
    B.det (fun i => Complex.I • x i) = B.det x := by
  have h := B.det_comp
    ((modelComplexStructure n : ComplexModel n →L[ℝ] ComplexModel n) :
      ComplexModel n →ₗ[ℝ] ComplexModel n) x
  rw [det_modelComplexStructure, one_mul] at h
  exact h

/-- The action `η ↦ J^*η` of the complex structure on test forms. -/
abbrev twistTestCLM {U : Opens (ComplexModel n)} {q : ℕ} :
    TestForm U q →L[ℝ] TestForm U q :=
  TestFunction.postcompCLM
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (modelComplexStructure n))

theorem twistTestCLM_apply {U : Opens (ComplexModel n)} {q : ℕ} (η : TestForm U q)
    (x : ComplexModel n) (v : Fin q → ComplexModel n) :
    twistTestCLM η x v = η x (fun i => Complex.I • v i) := rfl

/-- The wedge pairing of a `J`-invariant distribution two-form with `J^*η`. -/
theorem wedgePairing_twist {U : Opens (ComplexModel n)} {q : ℕ}
    (v : Fin 2 ⊕ Fin q → ComplexModel n) {A : DistributionForm U 2} (hA : IsOneOne A)
    (η : TestForm U q) :
    wedgePairing v A (twistTestCLM η) = wedgePairing (fun i => Complex.I • v i) A η := by
  rw [wedgePairing_apply, wedgePairing_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  have hA' (u : Fin 2 → ComplexModel n) : A (fun i => Complex.I • u i) = A u := by
    have hu : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
    have hIu : (fun i => Complex.I • u i) = ![Complex.I • u 0, Complex.I • u 1] := by
      ext i; fin_cases i <;> rfl
    rw [hIu, hA (u 0) (u 1), ← hu]
  rw [hA' (fun i => v (s.out (Sum.inl i)))]
  congr 1

/-- **A current of type `(1,1)` is invariant under the complex structure on test forms.** -/
theorem inChart_twist_of_isTypeOneOne {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (hn : 0 < n)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {T : GlobalCurrent n M (degreeTwo hn)} (hT : T.IsTypeOneOne b hn) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - 2)) :
    T.inChart e (twistTestCLM η) = T.inChart e η := by
  have hrec := Pending.CurrentPairing.toLocalCurrent_fromLocalCurrent b (degreeTwo hn)
    (T.inChart e)
  rw [← hrec]
  let B := currentPairingBasis b (degreeTwo hn)
  change wedgePairing B (T.coefficients b e) (twistTestCLM η) =
    wedgePairing B (T.coefficients b e) η
  rw [wedgePairing_twist _ (hT e)]
  let B' := B.map (complexStructureEquiv n)
  have hB' : (fun i => Complex.I • B i) = ⇑B' := by
    funext i
    simp [B', complexStructureEquiv]
  rw [hB', wedgePairing_change_basis B B', smul_apply]
  have hdet : B.det B' = 1 := by
    rw [← hB', basis_det_complexStructure, Module.Basis.det_self]
  rw [hdet, one_smul]

/-- **Invariance under the complex structure on test forms implies type `(1,1)`.** -/
theorem isTypeOneOne_of_inChart_twist {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (hn : 0 < n)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {T : GlobalCurrent n M (degreeTwo hn)}
    (hT : ∀ e (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - 2)),
      T.inChart e (twistTestCLM η) = T.inChart e η) : T.IsTypeOneOne b hn := by
  intro e v w
  ext φ
  rw [GlobalCurrent.coefficients_apply, GlobalCurrent.coefficients_apply, ← hT e]
  congr 1
  apply TestFunction.ext
  intro x
  ext u
  simp only [constantTestFormCLM_apply, twistTestCLM_apply, ContinuousAlternatingMap.smul_apply,
    contractVolume_apply, basisVolume_apply]
  congr 1
  have hfun : Sum.elim ![Complex.I • v, Complex.I • w] (fun j => Complex.I • u j) =
      fun i => Complex.I • Sum.elim ![v, w] u i := by
    funext i
    rcases i with i | j
    · fin_cases i <;> rfl
    · rfl
  rw [hfun, basis_det_complexStructure]

end Linear

variable {n : ℕ} {Z Y : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {g : Z → Y}
  (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)

/-- Holomorphic pull-back commutes with the complex structure. -/
theorem pullback_complexTwist_geometricallyEq {q : ℕ} (a : SmoothRealForm n Y q) :
    (SmoothRealForm.pullback hg (complexTwist a)).GeometricallyEq
      (complexTwist (SmoothRealForm.pullback hg a)) := by
  intro e z hz
  let d := complexChartAt (n := n) (g (e.val.symm z))
  have hzd : z ∈ coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [complexTwist_coeff, SmoothRealForm.pullback_coeff hg _ e d hzd,
    SmoothRealForm.pullback_coeff hg _ e d hzd, complexTwist_coeff]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    modelComplexStructure_apply, Function.comp_def]
  congr 1
  funext i
  exact (coordinateMap_fderiv_map_smul_complex hg e d hzd Complex.I (v i)).symm

/-- The global pairing of a current of type `(1,1)` is invariant under the complex structure. -/
theorem pairingLM_complexTwist {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] (hn : 0 < n)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {T : GlobalCurrent n M (degreeTwo hn)} (hT : T.IsTypeOneOne b hn)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - 2)) :
    pairingLM T (complexTwist γ) = pairingLM T γ := by
  let P : ChartPartitionOfUnity n M := ChartPartitionOfUnity.choice
  choose η hη _ using fun i => exists_testForm (P.chart i) γ (P.weight i) (P.smooth i)
    (P.compact i) (P.subset i)
  have hη' : ∀ i z, twistTestCLM (η i) z = (P.chart i).val.target.indicator
      (fun y => P.weight i ((P.chart i).val.symm y) • (complexTwist γ).coeff (P.chart i) y) z := by
    intro i z
    ext v
    rw [twistTestCLM_apply, hη]
    by_cases hz : z ∈ (P.chart i).val.target
    · simp only [indicator_of_mem hz, ContinuousAlternatingMap.smul_apply, complexTwist_coeff,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rfl
    · simp only [indicator_of_notMem hz]
      rfl
  rw [P.pairingLM_eq_sum T _ (fun i => twistTestCLM (η i)) hη', P.pairingLM_eq_sum T γ η hη]
  exact Finset.sum_congr rfl fun i _ => inChart_twist_of_isTypeOneOne hn b hT _ _

/-- **The push-forward of a current of type `(1,1)` is of type `(1,1)`.** -/
theorem isTypeOneOne_currentPushforward [CompactSpace Z] (hn : 0 < n)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {T : GlobalCurrent n Z (degreeTwo hn)} (hT : T.IsTypeOneOne b hn) :
    (currentPushforward hg T).IsTypeOneOne b hn := by
  apply isTypeOneOne_of_inChart_twist hn b
  intro e η
  rw [currentPushforward_inChart, currentPushforward_inChart]
  have h1 : (SmoothRealForm.pullback hg (testExtension e (twistTestCLM η))).GeometricallyEq
      (complexTwist (SmoothRealForm.pullback hg (testExtension e η))) :=
    (SmoothRealForm.GeometricallyEq.pullback hg
      (Pending.NaturalChartExtensionDifferentials.twist_testExtension_geometricallyEq
        e η).symm).trans (pullback_complexTwist_geometricallyEq hg _)
  rw [pairing_eq_of_geometricallyEq T h1, pairingLM_complexTwist hn b hT]

/-- The global pairing is nonnegative on forms whose chart coefficients lie in a pointed cone `C`,
for a current that is nonnegative on chart test forms with values in `C` (nonnegative partition
weights keep the pieces in `C`). -/
theorem pairingLM_cast_nonneg {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    {k : CurrentDegree n} (T : GlobalCurrent n M k) {a : ℕ}
    (h : a = Module.finrank ℝ (ComplexModel n) - k.val)
    (C : PointedCone ℝ ((ComplexModel n) [⋀^Fin a]→L[ℝ] ℝ))
    (hT : ∀ (e : ComplexChart n M) (ξ : TestForm (chartTarget e) a), (∀ x, ξ x ∈ C) →
      0 ≤ T.inChart e (h ▸ ξ))
    (γ : SmoothRealForm n M a) (hγ : ∀ e z, z ∈ e.val.target → γ.coeff e z ∈ C) :
    0 ≤ pairingLM T (h ▸ γ) := by
  subst h
  let P : ChartPartitionOfUnity n M := ChartPartitionOfUnity.choice
  choose η hη _ using fun i => exists_testForm (P.chart i) γ (P.weight i) (P.smooth i)
    (P.compact i) (P.subset i)
  rw [P.pairingLM_eq_sum T γ η hη]
  refine Finset.sum_nonneg fun i _ => hT (P.chart i) (η i) fun x => ?_
  erw [hη]
  by_cases hx : x ∈ (P.chart i).val.target
  · rw [indicator_of_mem hx]
    exact C.smul_mem (P.nonneg i _) (hγ _ _ hx)
  · rw [indicator_of_notMem hx]
    exact C.zero_mem

/-- **The push-forward of a positive current is positive**: strongly positive test forms pull
back to strongly positive forms under the complex linear derivatives of `g`. -/
theorem isFullPositive_currentPushforward {m : ℕ} {Z Y : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z] [CompactSpace Z]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    {T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m))}
    (hT : Pending.GlobalPositiveCurrentACRestriction.IsFullPositive T) :
    Pending.GlobalPositiveCurrentACRestriction.IsFullPositive (currentPushforward hg T) := by
  intro e α hα
  have hdeg : 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2 := by
    rw [complexModel_real_finrank]; omega
  change 0 ≤ (currentPushforward hg T).inChart e (hdeg ▸ α)
  rw [currentPushforward_inChart_cast hg T e hdeg.symm α]
  refine pairingLM_cast_nonneg T hdeg (Pending.StronglyPositiveForms.spCone (n := m + 1) m)
    (fun f ξ hξ => hT f ξ hξ) _ ?_
  intro f z hz
  let d := complexChartAt (n := m + 1) (g (f.val.symm z))
  have hzd : z ∈ coordinateDomain g f d := ⟨hz, mem_complexChartAt_source _⟩
  rw [SmoothRealForm.pullback_coeff hg _ f d hzd]
  refine Pending.StronglyPositiveForms.compContinuousLinearMap_mem_spCone _
    (fun v => coordinateMap_fderiv_map_smul_complex hg f d hzd Complex.I v) m ?_
  change Pending.NaturalSupportedChartFormExtension.transportedCoeff e d α
    (coordinateMap g f d z) ∈ _
  by_cases ho : coordinateMap g f d z ∈ (chartTransition d e).source
  · rw [Pending.NaturalSupportedChartFormExtension.transportedCoeff, indicator_of_mem ho]
    exact Pending.StronglyPositiveForms.compContinuousLinearMap_mem_spCone _
      (fun v => chartTransitionDerivative_complex_smul d e _ ho Complex.I v) m (hα _)
  · rw [Pending.NaturalSupportedChartFormExtension.transportedCoeff, indicator_of_notMem ho]
    exact (Pending.StronglyPositiveForms.spCone (n := m + 1) m).zero_mem

end SGPT.BDivisor
