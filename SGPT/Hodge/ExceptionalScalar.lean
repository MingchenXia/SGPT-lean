import SGPT.BDivisor.BlowupModel2Divisor
import SGPT.BDivisor.ModificationChangeOfVariables

/-!
# Scalar currents and push-forward along a modification

Infrastructure for the cohomology of modifications (`SGPT.Hodge.ExceptionalIndependence`):
currents of degree `0` (the argument of `ddᶜ` in `SGPT.BDivisor.ddcTwo`) and their behaviour
under the push-forward `π_*` along a modification `π : Y → X` of compact complex manifolds.

* `scalarCoeff_eq_coefficients`, `eq_of_scalarCoeff_eq`: a current of degree `0` is determined by
  its scalar coefficients `φ ↦ U(φ · vol)` in all charts;
* `funCurrent`, `scalarCoeff_funCurrent`: the current `[f]` of a chart-smooth function `f`, with
  scalar coefficients the regular distributions of `f`;
* `currentPushforward_funCurrent_comp`: **`π_*[F ∘ π] = [F]`** (change of variables along the
  modification);
* `currentEqOn_zero_of_currentPushforward_eq_zero`: **if `π_*T = 0`, then `T` vanishes off
  `π⁻¹(π(Exc π))`** (over the isomorphism locus the push-forward is the transport by the
  biholomorphism `π`; converse of `SGPT.BDivisor.PrimePushforward.currentEqOn_currentPushforward_zero`);
* `eq_zero_of_currentEqOn_scalarFamilyCurrent`: a scalar current `[f]` of a locally integrable
  function that vanishes on an open set where `f` is continuous forces `f = 0` there.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.Hodge.Exceptional

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalCurrents
  SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose
  SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentDifferentials
  SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentPairingDifferentials
  SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.ProductTestForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor SGPT.Currents.AnalyticSupport SGPT.NPP.MassPushforward

/-! ### Currents of degree zero -/

section Scalar

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n) in
/-- The real current degree `0`. -/
abbrev degZero : CurrentDegree n := ⟨0, Nat.succ_pos _⟩

/-- The degree of the currents `U` with `ddᶜU = SGPT.BDivisor.ddcTwo hn U` of degree two: real
degree `0`, written as the complement of the top degree. -/
abbrev scalarDegree (hn : 0 < n) : CurrentDegree n :=
  complementDegree n (Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1)
    (finrank_sub_two_add_two hn).le

theorem scalarDegree_val (hn : 0 < n) : (scalarDegree hn).val = 0 := by
  simp only [complementDegree]
  rw [complexModel_real_finrank]
  omega

theorem degZero_eq_scalarDegree (hn : 0 < n) : degZero n = scalarDegree hn :=
  Fin.ext (scalarDegree_val hn).symm

/-- The empty family of vectors, indexed by `Fin (scalarDegree hn).val`. -/
def emptyVec (hn : 0 < n) : Fin (scalarDegree hn).val → ComplexModel n :=
  fun i => Fin.elim0 (Fin.cast (scalarDegree_val hn) i)

theorem eq_emptyVec (hn : 0 < n) (v : Fin (scalarDegree hn).val → ComplexModel n) :
    v = emptyVec hn :=
  funext fun i => Fin.elim0 (Fin.cast (scalarDegree_val hn) i)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem sumElim_finSumFinEquiv_symm {E : Type*} {a c : ℕ} (ha : a = 0) (v : Fin a → E)
    (w : Fin c → E) (x : Fin (a + c)) :
    Sum.elim v w (finSumFinEquiv.symm x) = w (Fin.cast (by omega) x) := by
  refine Fin.addCases (fun y => ?_) (fun y => ?_) x
  · exact Fin.elim0 (Fin.cast ha y)
  · rw [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    congr 1
    apply Fin.ext
    simp [ha]

variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- **The scalar coefficient of a current of degree zero is its coefficient on the empty family
of vectors.** -/
theorem scalarCoeff_eq_coefficients (hn : 0 < n) (U : GlobalCurrent n M (scalarDegree hn))
    (e : ComplexChart n M) :
    scalarCoeff b (finrank_sub_two_add_two hn) U e = U.coefficients b e (emptyVec hn) := by
  ext φ
  rw [NaturalNativeCurrentCoefficientDifferential.coefficient_block_apply b
    (complementDegree_complement n _ (finrank_sub_two_add_two hn).le) U e (emptyVec hn) φ]
  unfold scalarCoeff
  rw [currentCoefficients_apply]
  congr 3
  ext w
  simp only [contractVolume_apply, basisVolume_apply, scalarBasis, Module.Basis.det_reindex]
  congr 1
  funext i
  simp only [Function.comp_apply, Equiv.symm_trans_apply]
  rw [sumElim_finSumFinEquiv_symm rfl, sumElim_finSumFinEquiv_symm (scalarDegree_val hn)]
  congr 1

/-- **A current of degree zero is determined by its scalar coefficients.** -/
theorem eq_of_scalarCoeff_eq (hn : 0 < n) {U V : GlobalCurrent n M (scalarDegree hn)}
    (h : ∀ e, scalarCoeff b (finrank_sub_two_add_two hn) U e =
      scalarCoeff b (finrank_sub_two_add_two hn) V e) : U = V := by
  apply LelongPoincareDivisor.globalCurrent_ext b
  intro e
  ext v φ
  rw [eq_emptyVec hn v, ← scalarCoeff_eq_coefficients, ← scalarCoeff_eq_coefficients, h e]

/-- The smooth `0`-form of a chart-smooth function. -/
abbrev funForm (f : M → ℝ) (hf : ChartSmooth (n := n) f) : SmoothRealForm n M 0 :=
  smulFun f hf unitForm

/-- **The current `[f]` of degree zero of a chart-smooth function** `f`: `φ vol ↦ ∫ f φ vol`. -/
def funCurrent (hn : 0 < n) (f : M → ℝ) (hf : ChartSmooth (n := n) f) :
    GlobalCurrent n M (scalarDegree hn) :=
  degZero_eq_scalarDegree hn ▸
    smoothGlobalCurrent (canonicalBasis n) (k := degZero n) (funForm f hf)

theorem chartSmooth_locallyIntegrableOn (μ : Measure (ComplexModel n)) [IsLocallyFiniteMeasure μ]
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (e : ComplexChart n M) :
    LocallyIntegrableOn (fun z => f (e.val.symm z)) (chartTarget e) μ :=
  (hf e).continuousOn.locallyIntegrableOn e.val.open_target.measurableSet

/-- **The scalar coefficients of `[f]` are the regular distributions of `f`.** -/
theorem scalarCoeff_funCurrent (hn : 0 < n) (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (e : ComplexChart n M) :
    scalarCoeff (canonicalBasis n) (finrank_sub_two_add_two hn) (funCurrent hn f hf) e =
      regularDistribution (canonicalBasis n).addHaar (fun z => f (e.val.symm z))
        (chartSmooth_locallyIntegrableOn _ hf e) := by
  ext φ
  rw [scalarCoeff_eq_coefficients, funCurrent, coefficients_cast,
    FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent,
    smoothFormDistribution_apply, regularDistribution_apply]
  have hint : Integrable (fun z => φ z • (funForm f hf).coeff e z) (canonicalBasis n).addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable (canonicalBasis n) (funForm f hf) e)
  rw [← formEvaluationCLM_apply, ← (formEvaluationCLM _).integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [formEvaluationCLM_apply, ContinuousAlternatingMap.smul_apply, smulFun_coeff,
    unitForm_coeff, MongeAmpere.coordinateWedgeUnit,
    ContinuousAlternatingMap.constOfIsEmpty_apply, smul_eq_mul, mul_one]

end Scalar

end SGPT.Hodge.Exceptional

namespace SGPT.Hodge.Exceptional

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalCurrents
  SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose
  SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.ProductTestForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor SGPT.Currents.AnalyticSupport SGPT.NPP.MassPushforward

/-! ### Local vanishing of scalar currents -/

section Vanishing

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A scalar current that vanishes on an open set forces its density to vanish there**: if the
scalar coefficients of `U` are the regular distributions of `f`, `U` vanishes on the open set `O`
and `f` is continuous on `O`, then `f = 0` on `O`. -/
theorem eq_zero_of_currentEqOn_zero (hn : 0 < n) {f : M → ℝ}
    (hL : ∀ e : ComplexChart n M,
      LocallyIntegrableOn (fun z => f (e.val.symm z)) (chartTarget e) (canonicalBasis n).addHaar)
    {U : GlobalCurrent n M (scalarDegree hn)}
    (hU : ∀ e, scalarCoeff (canonicalBasis n) (finrank_sub_two_add_two hn) U e =
      regularDistribution (canonicalBasis n).addHaar (fun z => f (e.val.symm z)) (hL e))
    {O : Set M} (hO : IsOpen O) (hfO : ContinuousOn f O) (h0 : CurrentEqOn U 0 O) :
    ∀ y ∈ O, f y = 0 := by
  intro y hyO
  set e := complexChartAt (n := n) y with he
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hz : e.val y ∈ e.val.target := e.val.map_source hye
  have hzy : e.val.symm (e.val y) = y := e.val.left_inv hye
  obtain ⟨D, hzD, hD, hres⟩ := h0 e (e.val y) hz (by rw [hzy]; exact hyO)
  let D' : Opens (ComplexModel n) :=
    ⟨(D : Set (ComplexModel n)) ∩ (e.val.target ∩ e.val.symm ⁻¹' O),
      D.isOpen.inter (e.val.isOpen_inter_preimage_symm hO)⟩
  have hD'D : D' ≤ D := fun _ hw => hw.1
  have hD'e : D' ≤ chartTarget e := hD'D.trans hD
  have hzD' : e.val y ∈ D' := ⟨hzD, hz, by rw [Set.mem_preimage, hzy]; exact hyO⟩
  -- the regular distribution of `f ∘ e⁻¹` vanishes on `D'`
  have hvan : regularDistribution (canonicalBasis n).addHaar (fun z => f (e.val.symm z))
      ((hL e).mono_set hD'e) =
      regularDistribution (canonicalBasis n).addHaar (fun _ => (0 : ℝ))
        (locallyIntegrableOn_const 0) := by
    ext φ
    rw [← restrictDistribution_regularDistribution _ (hL e) hD'e, restrictDistribution_apply,
      ← hU e,
      scalarCoeff_eq_coefficients]
    have hmono : (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) =
        TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ φ : 𝓓(D, ℝ)) := by
      apply TestFunction.ext
      intro w
      rw [testFunction_inclusion_coe hD'e, testFunction_inclusion_coe hD,
        testFunction_inclusion_coe hD'D]
    rw [hmono, ← GlobalCurrent.coefficients_restrictChart (canonicalBasis n) U e hD, hres,
      GlobalCurrent.coefficients_restrictChart, GlobalCurrent.coefficients_zero]
    simp [regularDistribution_apply]
  have hae := ae_eq_of_regularDistribution_eq _ _ _ hvan
  have hcont : ContinuousOn (fun z => f (e.val.symm z)) D' :=
    hfO.comp (e.val.continuousOn_symm.mono fun _ hw => hw.2.1) fun _ hw => hw.2.2
  have heq := Measure.eqOn_open_of_ae_eq hae D'.isOpen hcont continuousOn_const
  have := heq hzD'
  simpa [hzy] using this

end Vanishing

/-! ### Push-forward along a modification -/

section Pushforward

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

theorem currentPushforward_cast [CompactSpace Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {k k' : CurrentDegree n}
    (h : k = k') (T : GlobalCurrent n Y k) :
    currentPushforward hπ (h ▸ T) = h ▸ currentPushforward hπ T := by
  subst h
  rfl

/-- **`π_*[F ∘ π] = [F]`** for a chart-smooth function `F` on `X` and a modification `π`. -/
theorem currentPushforward_funCurrent_comp [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) (hn : 0 < n) (F : X → ℝ)
    (hF : ChartSmooth (n := n) F) :
    currentPushforward hπ.1 (funCurrent hn (fun y => F (π y)) (chartSmooth_comp hπ.1 hF)) =
      funCurrent hn F hF := by
  unfold funCurrent
  rw [currentPushforward_cast]
  congr 1
  have h := currentPushforward_smoothGlobalCurrent_pullback hπ (k := degZero n) (funForm F hF)
  rw [funForm, pullback_smulFun, pullback_unitForm] at h
  exact h

/-- **If `π_*T = 0`, then `T` vanishes off `π⁻¹(π(Exc π))`**: over the isomorphism locus the
push-forward is the transport of currents by the biholomorphism `π`. -/
theorem currentEqOn_zero_of_currentPushforward_eq_zero [CompactSpace X] [CompactSpace Y]
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) {k : CurrentDegree n}
    {T : GlobalCurrent n Y k} (h0 : currentPushforward hπ.1 T = 0) :
    CurrentEqOn T 0 (π ⁻¹' (π '' exceptionalLocus n π))ᶜ := by
  classical
  intro e z hz hzO
  set y := e.val.symm z with hydef
  have hye : y ∈ e.val.source := e.val.map_target hz
  have hey : e.val y = z := e.val.right_inv hz
  have hyE : π y ∉ π '' exceptionalLocus n π := hzO
  obtain ⟨s, hs, hright, hleft⟩ := SGPT.Siu.exists_inverse_off_image_exceptionalLocus hπ
  have hEc := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hπ
  let d := complexChartAt (n := n) (π y)
  have hyd : π y ∈ d.val.source := mem_complexChartAt_source (π y)
  obtain ⟨A, B, hyA, hAe, hBd, hAdom, hBE, hBs, hp⟩ :=
    SGPT.Siu.exists_coordinatePairs_of_inverse hπ.1 hEc hs hright hleft y hyE e d hye hyd
  have hpA := restrictPair hp (le_refl A)
  have hB₀d : (⟨(B : Set (ComplexModel n)) ∩ coordinateMap s d e ⁻¹' A,
      hp.holo_inv.continuousOn.isOpen_inter_preimage B.isOpen A.isOpen⟩ :
        Opens (ComplexModel n)) ≤ chartTarget d := fun w hw => hBd hw.1
  have hfib : ∀ y', π y' ∈ d.val.source →
      d.val (π y') ∈ (B : Set (ComplexModel n)) ∩ coordinateMap s d e ⁻¹' A →
        y' ∈ e.val.source ∧ e.val y' ∈ A := fun y' h1 h2 => fibre_mem hleft hBE hBs h1 h2
  refine ⟨A, hey ▸ hyA, hAe, ?_⟩
  ext η
  change T.inChart e (TestFunction.monoCLM ℝ η) =
    (0 : GlobalCurrent n Y k).inChart e (TestFunction.monoCLM ℝ η)
  rw [GlobalCurrent.inChart_zero, ← currentPushforward_inChart_eq hπ.1 T e d hAe hB₀d hAdom
    hpA.mapsTo hfib η (pushTest hpA η) (pushTest_rel hpA η), h0]
  rfl

end Pushforward

end SGPT.Hodge.Exceptional
