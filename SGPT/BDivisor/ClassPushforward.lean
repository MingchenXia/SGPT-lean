import SGPT.BDivisor.ScalarDdcCurrent
import SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.FullSmoothNativeCurrentDifferential
import SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

/-!
# Push-forward of real `(1,1)`-classes along holomorphic maps

For a holomorphic map `g : Z → Y` between compact complex manifolds of the same dimension
`n > 0`, the push-forward of currents (`SGPT.BDivisor.currentPushforward`) maps closed currents of
type `(1,1)` to closed currents of type `(1,1)`, and induces a real linear map

`g_* : H^{1,1}(Z, ℝ) → H^{1,1}(Y, ℝ)`,  `g_*{θ} = {g_* θ}`

on real Bott--Chern classes (Xia, *Foundations of pluripotential theory*, Section `q07`, the
paragraph before `prop:positivity-under-modifications`: "pushforward of currents ... satisfies
`π_* ddᶜf = ddᶜ π_* f` for distributions `f`; hence it induces a linear map
`π_* : H^{1,1}(Y,ℝ) → H^{1,1}(X,ℝ)` with `π_*{S} = {π_*S}`"). This is the push-forward `g_*` of the
b-divisor chapter (`def:bdiv:L38`) and of `prop:cones_modif`, `lma:pushIpo`.

Well-definedness (descent): if `θ' = θ + ddᶜh`, then `[θ'] - [θ] = ddᶜ[h]` as currents, the
push-forward commutes with `ddᶜ` (`currentPushforward_ddcCurrentCLM`), and the class of the `ddᶜ`
of any current of degree zero vanishes (its coefficients are `ddᶜ` of a compatible family of
scalar distributions, `coefficients_ddcCurrentCLM`).

Main declarations:

* `SGPT.BDivisor.closedCurrentPushforward` — `g_*` on closed `(1,1)`-currents;
* `SGPT.BDivisor.classPushforward` — `g_*` on classes, a real linear map;
* `SGPT.BDivisor.classPushforward_ofRepresentative` — `g_*{θ} = {g_*[θ]}`;
* `SGPT.BDivisor.bottChernClass_closedCurrentPushforward` — `{g_* T} = g_*{T}` for every closed
  `(1,1)`-current `T` (in particular for closed positive currents);
* `SGPT.BDivisor.classPushforward_id`, `SGPT.BDivisor.classPushforward_comp` — functoriality.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
  SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose
  SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentDifferentials

variable {n : ℕ}

section ScalarCurrent

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  {q : ℕ} (hqN : q + 1 + 1 = Module.finrank ℝ (ComplexModel n))

omit [IsComplexManifold n M] in
theorem testCoefficientCLM_mono {Ω V : Opens (ComplexModel n)} {r : ℕ} (hV : V ≤ Ω)
    (w : Fin r → ComplexModel n) (η : TestForm V r) :
    testCoefficientCLM w (TestFunction.monoCLM ℝ η : TestForm Ω r) =
      (TestFunction.monoCLM ℝ (testCoefficientCLM w η) : 𝓓(Ω, ℝ)) := by
  apply TestFunction.ext
  intro z
  rw [testCoefficientCLM_apply, testForm_inclusion_apply hV, testFunction_inclusion_coe hV]
  rfl

/-- The current of degree zero with prescribed compatible scalar coefficients `H`:
`ξ ↦ H_e(ξ(b₀))` on top-degree chart test forms. -/
def scalarFamilyCurrent (H : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hH : ScalarFamilyCompatible H) :
    GlobalCurrent n M (complementDegree n (q + 1 + 1) hqN.le) :=
  (nativeDegreeEquiv (complementDegree_complement n (q + 1 + 1) hqN.le)).symm
    ⟨fun e => (H e).comp (testCoefficientCLM (fun j => scalarBasis b hqN (Sum.inr j))), by
      intro e f η ζ hrel
      change H e (testCoefficientCLM _ (TestFunction.monoCLM ℝ η)) =
        H f (testCoefficientCLM _ (TestFunction.monoCLM ℝ ζ))
      rw [testCoefficientCLM_mono (overlapSource_le e f),
        testCoefficientCLM_mono (overlapTarget_le e f)]
      apply hH
      intro y hy
      rw [testCoefficientCLM_apply, testCoefficientCLM_apply, hrel y hy]
      let B' : Module.Basis (Fin (q + 1 + 1)) ℝ (ComplexModel n) :=
        (scalarBasis b hqN).reindex (Equiv.emptySum (Fin 0) (Fin (q + 1 + 1)))
      let D := chartTransitionDerivative e f y
      let W := ζ (chartTransition e f y)
      have hB' : (fun j => scalarBasis b hqN (Sum.inr j)) = ⇑B' := by
        funext j
        simp [B']
      have hDB : (fun i => chartTransitionDerivative e f y (scalarBasis b hqN (Sum.inr i))) =
          D ∘ B' := by
        funext j
        simp [B', D]
      rw [hDB, hB']
      have ht := congrArg
        (fun A : (ComplexModel n) [⋀^Fin (q + 1 + 1)]→ₗ[ℝ] ℝ => A (D ∘ B'))
        (W.toAlternatingMap.eq_smul_basis_det B')
      have hd : B'.det (D ∘ B') = LinearMap.det D.toLinearMap := by
        change B'.det (D.toLinearMap ∘ B') = _
        rw [B'.det_comp, B'.det_self, mul_one]
      change W (D ∘ B') = _
      calc
        W (D ∘ B') = ((W B') • B'.det) (D ∘ B') := ht
        _ = W B' * B'.det (D ∘ B') := by simp
        _ = Pending.ThetaPshChartLimitGluing.transitionJac e f y * W B' := by
          rw [hd, Pending.ThetaPshChartLimitGluing.transitionJac,
            abs_of_nonneg (Pending.GlobalCurrents.chartTransitionDerivative_det_nonneg e f hy)]
          exact mul_comm _ _⟩

/-- The scalar coefficients of `scalarFamilyCurrent H` are `H`. -/
theorem scalarCoeff_scalarFamilyCurrent (H : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hH : ScalarFamilyCompatible H) (e : ComplexChart n M) :
    scalarCoeff b hqN (scalarFamilyCurrent b hqN H hH) e = H e := by
  ext φ
  rw [scalarCoeff, currentCoefficients_apply, scalarFamilyCurrent,
    nativeDegreeEquiv_symm_chart]
  change H e (testCoefficientCLM _ (constantTestFormCLM _ φ)) = H e φ
  rw [testCoefficient_constantTestForm]
  have h1 : contractVolume (basisVolume (scalarBasis b hqN)) Fin.elim0
      (fun j => scalarBasis b hqN (Sum.inr j)) = 1 := by
    rw [contractVolume_apply, basisVolume_apply]
    have : Sum.elim (Fin.elim0 : Fin 0 → ComplexModel n)
        (fun j => scalarBasis b hqN (Sum.inr j)) = ⇑(scalarBasis b hqN) := by
      funext i
      rcases i with i | j
      · exact i.elim0
      · rfl
    rw [this, Module.Basis.det_self]
  rw [h1, one_smul]

end ScalarCurrent

section Degree

theorem finrank_sub_two_add_two (hn : 0 < n) :
    Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1 = Module.finrank ℝ (ComplexModel n) := by
  rw [complexModel_real_finrank]
  omega

theorem even_finrank_sub_two : Even (Module.finrank ℝ (ComplexModel n) - 2) := by
  rw [complexModel_real_finrank]
  exact ⟨n - 1, by omega⟩

theorem complementDegree_eq_degreeTwo (hn : 0 < n) :
    complementDegree n (Module.finrank ℝ (ComplexModel n) - 2)
      (le_of_add_two_eq (finrank_sub_two_add_two hn)) = degreeTwo hn := by
  apply Fin.ext
  simp only [complementDegree]
  rw [complexModel_real_finrank]
  omega

end Degree

section DdcTwo

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n)) (hn : 0 < n)

/-- `ddᶜ U` of a current `U` of degree zero, as a current of degree two. -/
def ddcTwo (U : GlobalCurrent n M (complementDegree n (Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1)
    (finrank_sub_two_add_two hn).le)) : GlobalCurrent n M (degreeTwo hn) :=
  complementDegree_eq_degreeTwo hn ▸
    ddcCurrentCLM (Module.finrank ℝ (ComplexModel n) - 2) (finrank_sub_two_add_two hn).le U

/-- The coefficients of `ddᶜ U` are `ddᶜ` of the scalar coefficients of `U`. -/
theorem coefficients_ddcTwo (U : GlobalCurrent n M (complementDegree n
    (Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1) (finrank_sub_two_add_two hn).le))
    (e : ComplexChart n M) :
    (ddcTwo hn U).coefficients b e = ddC (scalarCoeff b (finrank_sub_two_add_two hn) U e) := by
  ext v φ
  rw [ddcTwo, coefficients_cast, coefficients_ddcCurrentCLM b even_finrank_sub_two
    (finrank_sub_two_add_two hn)]
  rfl

theorem ddcTwo_mem (U : GlobalCurrent n M (complementDegree n
    (Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1) (finrank_sub_two_add_two hn).le)) :
    ddcTwo hn U ∈ closedOneOneSubmodule (M := M) b hn := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [coefficients_ddcTwo]
    exact _root_.SGPT.Foundations.Analysis.Pending.LocalCurrents.ddC_isClosed _
  · change LocalCurrents.IsOneOne ((ddcTwo hn U).coefficients b e)
    rw [coefficients_ddcTwo]
    exact _root_.SGPT.Foundations.Analysis.Pending.LocalCurrents.ddC_isOneOne _

theorem smoothFormDistribution_zero (e : ComplexChart n M) :
    smoothFormDistribution b (0 : ClosedRealOneOneForm n M).val e = 0 := by
  ext v φ
  rw [smoothFormDistribution_apply]
  simp

theorem smoothClosedCurrent_add (σ τ : ClosedRealOneOneForm n M) :
    smoothClosedCurrent b hn (σ + τ) = smoothClosedCurrent b hn σ + smoothClosedCurrent b hn τ := by
  apply Subtype.ext
  apply Pending.LelongPoincareDivisor.globalCurrent_ext b
  intro e
  change (Pending.GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) (σ + τ).val).coefficients b e =
    (Pending.GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val +
      Pending.GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) τ.val).coefficients b e
  rw [GlobalCurrent.coefficients_add,
    Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent,
    Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent,
    Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent]
  ext v φ
  have hσ : Integrable (fun z => φ z • σ.val.coeff e z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b σ.val e)
  have hτ : Integrable (fun z => φ z • τ.val.coeff e z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b τ.val e)
  rw [AlternatingMap.add_apply, add_apply, smoothFormDistribution_apply,
    smoothFormDistribution_apply, smoothFormDistribution_apply]
  simp only [ClosedRealOneOneForm.coeff_add, smul_add]
  rw [integral_add hσ hτ]
  rfl

theorem smoothClosedCurrent_smul (c : ℝ) (σ : ClosedRealOneOneForm n M) :
    smoothClosedCurrent b hn (c • σ) = c • smoothClosedCurrent b hn σ := by
  apply Subtype.ext
  apply Pending.LelongPoincareDivisor.globalCurrent_ext b
  intro e
  change (Pending.GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) (c • σ).val).coefficients b e =
    (c • Pending.GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val).coefficients b e
  rw [GlobalCurrent.coefficients_smul,
    Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent,
    Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent]
  ext v φ
  rw [AlternatingMap.smul_apply, _root_.smul_apply, smoothFormDistribution_apply,
    smoothFormDistribution_apply]
  simp only [ClosedRealOneOneForm.coeff_smul]
  have hfun : (fun z => φ z • (c • σ.val.coeff e z)) = (fun z => c • (φ z • σ.val.coeff e z)) := by
    funext z
    exact smul_comm _ _ _
  rw [hfun, integral_smul]
  rfl

/-- **The class of `ddᶜ U` vanishes** for every current `U` of degree zero on a compact
manifold. -/
theorem bottChernClass_ddcTwo [CompactSpace M] (U : GlobalCurrent n M (complementDegree n
    (Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1) (finrank_sub_two_add_two hn).le)) :
    bottChernClass b hn ⟨ddcTwo hn U, ddcTwo_mem b hn U⟩ = 0 := by
  rw [bottChernClass_eq_of_native_reading b hn _ 0
    (scalarCoeff b (finrank_sub_two_add_two hn) U)
    (scalarFamilyCompatible_scalarCoeff b (finrank_sub_two_add_two hn) U)]
  · rfl
  · intro e
    change (ddcTwo hn U).coefficients b e = _
    rw [smoothFormDistribution_zero, zero_add, coefficients_ddcTwo]

/-- **`[θ'] - [θ] = ddᶜ[h]`** for smooth closed forms with `θ' = θ + ddᶜh`. -/
theorem smoothClosedCurrent_sub_eq_ddcTwo {θ θ' : ClosedRealOneOneForm n M} (h : M → ℝ)
    (hh : ChartSmooth (n := n) h)
    (heq : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z) :
    (smoothClosedCurrent b hn θ').val - (smoothClosedCurrent b hn θ).val =
      ddcTwo hn (scalarFamilyCurrent b (finrank_sub_two_add_two hn)
        (fun e => regularDistribution b.addHaar (fun z => h (e.val.symm z))
          ((hh e).continuousOn.locallyIntegrableOn e.val.open_target.measurableSet))
        (Pending.ThetaPotentialCurrentBottChernClass.scalarFamilyCompatible_regular b.addHaar h
          (fun e => (hh e).continuousOn.locallyIntegrableOn e.val.open_target.measurableSet))) := by
  apply Pending.LelongPoincareDivisor.globalCurrent_ext b
  intro e
  rw [Pending.LelongPoincareDivisor.coefficients_sub, coefficients_ddcTwo,
    scalarCoeff_scalarFamilyCurrent]
  change (Pending.GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) θ'.val).coefficients b e -
      (Pending.GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) θ.val).coefficients b e = _
  rw [Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent,
    Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent]
  ext v φ
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have hddC := Pending.LelongPoincareDivisor.ddC_regularDistribution_apply_of_contDiffOn
    (μ := b.addHaar) (hh e)
    ((hh e).continuousOn.locallyIntegrableOn e.val.open_target.measurableSet) (v 0) (v 1) φ
  rw [AlternatingMap.sub_apply, sub_apply, hv]
  erw [hddC]
  rw [smoothFormDistribution_apply, smoothFormDistribution_apply]
  have hint (σ : ClosedRealOneOneForm n M) :
      Integrable (fun x => φ x • σ.val.coeff e x) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b σ.val e)
  rw [← formEvaluationCLM_apply, ← (formEvaluationCLM _).integral_comp_comm (hint θ'),
    ← formEvaluationCLM_apply, ← (formEvaluationCLM _).integral_comp_comm (hint θ),
    ← integral_sub ((formEvaluationCLM _).integrable_comp (hint θ'))
      ((formEvaluationCLM _).integrable_comp (hint θ))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_smul, formEvaluationCLM_apply, smul_eq_mul]
  by_cases hx : x ∈ e.val.target
  · rw [heq e x hx, ContinuousAlternatingMap.add_apply]
    ring
  · have hφ : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset ht))
    rw [hφ]
    ring

end DdcTwo

section Pushforward

variable {Z Y : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [CompactSpace Z] {g : Z → Y}
  (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n)) (hn : 0 < n)

theorem currentPushforward_cast {k k' : CurrentDegree n} (h : k = k') (T : GlobalCurrent n Z k) :
    currentPushforward hg (h ▸ T : GlobalCurrent n Z k') = h ▸ currentPushforward hg T := by
  subst h
  rfl

/-- `g_*(ddᶜ U) = ddᶜ(g_* U)` in degree two. -/
theorem currentPushforward_ddcTwo (U : GlobalCurrent n Z (complementDegree n
    (Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1) (finrank_sub_two_add_two hn).le)) :
    currentPushforward hg (ddcTwo hn U) = ddcTwo hn (currentPushforward hg U) := by
  rw [ddcTwo, ddcTwo, currentPushforward_cast, currentPushforward_ddcCurrentCLM]

/-- **Push-forward of closed `(1,1)`-currents.** -/
def closedCurrentPushforward : ClosedOneOneCurrent (M := Z) b hn →ₗ[ℝ]
    ClosedOneOneCurrent (M := Y) b hn where
  toFun T := ⟨currentPushforward hg T.val, isClosed_currentPushforward hg b T.property.1,
    isTypeOneOne_currentPushforward hg hn b T.property.2⟩
  map_add' T U := Subtype.ext ((currentPushforwardLM hg).map_add T.val U.val)
  map_smul' c T := Subtype.ext ((currentPushforwardLM hg).map_smul c T.val)

@[simp] theorem closedCurrentPushforward_val (T : ClosedOneOneCurrent (M := Z) b hn) :
    (closedCurrentPushforward hg b hn T).val = currentPushforward hg T.val := rfl

variable [CompactSpace Y]

/-- The class of the push-forward of the current `ddᶜU` vanishes. -/
theorem bottChernClass_closedCurrentPushforward_ddcTwo (U : GlobalCurrent n Z (complementDegree n
    (Module.finrank ℝ (ComplexModel n) - 2 + 1 + 1) (finrank_sub_two_add_two hn).le)) :
    bottChernClass b hn (closedCurrentPushforward hg b hn ⟨ddcTwo hn U, ddcTwo_mem b hn U⟩) = 0 := by
  have h : closedCurrentPushforward hg b hn ⟨ddcTwo hn U, ddcTwo_mem b hn U⟩ =
      ⟨ddcTwo hn (currentPushforward hg U), ddcTwo_mem b hn _⟩ :=
    Subtype.ext (currentPushforward_ddcTwo hg hn U)
  rw [h, bottChernClass_ddcTwo]

/-- The class of the push-forward of the smooth current `[θ]`. -/
def classPushforwardRep (θ : ClosedRealOneOneForm n Z) : RealBottChern n Y :=
  bottChernClass b hn (closedCurrentPushforward hg b hn (smoothClosedCurrent b hn θ))

/-- **Descent to Bott--Chern classes**: `{g_*[θ]}` depends only on `{θ}`. -/
theorem classPushforwardRep_congr {θ θ' : ClosedRealOneOneForm n Z}
    (hθ : ClosedRealOneOneForm.BottChernRel θ θ') :
    classPushforwardRep hg b hn θ = classPushforwardRep hg b hn θ' := by
  obtain ⟨h, hh, heq⟩ := hθ
  set U := scalarFamilyCurrent b (finrank_sub_two_add_two hn)
    (fun e => regularDistribution b.addHaar (fun z => h (e.val.symm z))
      ((hh e).continuousOn.locallyIntegrableOn e.val.open_target.measurableSet))
    (Pending.ThetaPotentialCurrentBottChernClass.scalarFamilyCompatible_regular b.addHaar h
      (fun e => (hh e).continuousOn.locallyIntegrableOn e.val.open_target.measurableSet))
    with hU
  have hadd : smoothClosedCurrent b hn θ' =
      smoothClosedCurrent b hn θ + ⟨ddcTwo hn U, ddcTwo_mem b hn U⟩ := by
    apply Subtype.ext
    have h1 := smoothClosedCurrent_sub_eq_ddcTwo b hn h hh heq
    rw [← hU] at h1
    rw [Submodule.coe_add]
    change _ = _ + ddcTwo hn U
    rw [← h1]
    abel
  have h0 := bottChernClass_closedCurrentPushforward_ddcTwo hg b hn U
  rw [classPushforwardRep, classPushforwardRep, hadd, map_add]
  change bottChernClass b hn _ = bottChernClassLinearMap (M := Y) b hn (_ + _)
  rw [map_add]
  change _ = bottChernClass b hn _ + bottChernClass b hn _
  rw [h0, add_zero]

/-- **The push-forward `g_* : H^{1,1}(Z,ℝ) → H^{1,1}(Y,ℝ)` of real `(1,1)`-classes** along a
holomorphic map between compact complex manifolds of positive dimension, `g_*{θ} = {g_*[θ]}`. -/
def classPushforward : RealBottChern n Z →ₗ[ℝ] RealBottChern n Y where
  toFun α := Quotient.liftOn α (classPushforwardRep hg b hn)
    (fun _ _ h => classPushforwardRep_congr hg b hn h)
  map_add' α β := by
    induction α using Quotient.inductionOn with
    | h θ₁ =>
    induction β using Quotient.inductionOn with
    | h θ₂ =>
    change classPushforwardRep hg b hn (θ₁ + θ₂) =
      classPushforwardRep hg b hn θ₁ + classPushforwardRep hg b hn θ₂
    rw [classPushforwardRep, classPushforwardRep, classPushforwardRep,
      smoothClosedCurrent_add, map_add]
    exact (bottChernClassLinearMap (M := Y) b hn).map_add _ _
  map_smul' c α := by
    induction α using Quotient.inductionOn with
    | h θ =>
    change classPushforwardRep hg b hn (c • θ) = c • classPushforwardRep hg b hn θ
    rw [classPushforwardRep, classPushforwardRep, smoothClosedCurrent_smul, map_smul]
    exact (bottChernClassLinearMap (M := Y) b hn).map_smul _ _

@[simp] theorem classPushforward_ofRepresentative (θ : ClosedRealOneOneForm n Z) :
    classPushforward hg b hn (RealBottChern.ofRepresentative θ) =
      bottChernClass b hn (closedCurrentPushforward hg b hn (smoothClosedCurrent b hn θ)) := rfl

/-- **`{g_* T} = g_*{T}`** for every closed `(1,1)`-current `T` on `Z`: the class of the
push-forward current is the push-forward of the class. -/
theorem bottChernClass_closedCurrentPushforward (T : ClosedOneOneCurrent (M := Z) b hn) :
    bottChernClass b hn (closedCurrentPushforward hg b hn T) =
      classPushforward hg b hn (bottChernClass b hn T) := by
  obtain ⟨σ, R, hR, hread, -⟩ :=
    Pending.CurrentSmoothBottChernChoiceIndependence.exists_unique_smooth_class_of_closed_current
      b hn T.val T.property.1 T.property.2
  rw [bottChernClass_eq_of_native_reading b hn T σ R hR hread]
  set V := scalarFamilyCurrent b (finrank_sub_two_add_two hn) R hR with hV
  have hT : T = smoothClosedCurrent b hn σ + ⟨ddcTwo hn V, ddcTwo_mem b hn V⟩ := by
    apply Subtype.ext
    apply Pending.LelongPoincareDivisor.globalCurrent_ext b
    intro e
    rw [Submodule.coe_add]
    change T.val.coefficients b e = (Pending.GlobalCurrents.smoothGlobalCurrent b
      (k := degreeTwo hn) σ.val + ddcTwo hn V).coefficients b e
    rw [GlobalCurrent.coefficients_add,
      Pending.FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent,
      coefficients_ddcTwo, hV, scalarCoeff_scalarFamilyCurrent, hread e]
  rw [hT, map_add, classPushforward_ofRepresentative]
  change bottChernClassLinearMap (M := Y) b hn (_ + _) = _
  rw [map_add]
  change bottChernClass b hn _ + bottChernClass b hn _ = _
  rw [bottChernClass_closedCurrentPushforward_ddcTwo, add_zero]

end Pushforward

section Functoriality

variable {W Z Y : Type*} [TopologicalSpace W] [ChartedSpace (ComplexModel n) W]
  [IsComplexManifold n W] [CompactSpace W]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] [CompactSpace Z]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace Y]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n)) (hn : 0 < n)

/-- `id_* = id` on classes. -/
theorem classPushforward_id (α : RealBottChern n Z) :
    classPushforward (g := (id : Z → Z)) (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞))
      b hn α = α := by
  induction α using Quotient.inductionOn with
  | h θ =>
    change classPushforward _ b hn (RealBottChern.ofRepresentative θ) = _
    rw [classPushforward_ofRepresentative]
    have h : closedCurrentPushforward (g := (id : Z → Z))
        (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)) b hn (smoothClosedCurrent b hn θ) =
        smoothClosedCurrent b hn θ :=
      Subtype.ext (currentPushforward_id _)
    rw [h, bottChernClass_smoothClosedCurrent]
    rfl

/-- Functoriality `(g ∘ h)_* = g_* ∘ h_*` on classes. -/
theorem classPushforward_comp {g : Z → Y} {h : W → Z}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ h) (α : RealBottChern n W) :
    classPushforward (hg.comp hh) b hn α = classPushforward hg b hn (classPushforward hh b hn α) := by
  induction α using Quotient.inductionOn with
  | h θ =>
    change classPushforward _ b hn (RealBottChern.ofRepresentative θ) =
      classPushforward hg b hn (classPushforward hh b hn (RealBottChern.ofRepresentative θ))
    rw [classPushforward_ofRepresentative, classPushforward_ofRepresentative,
      ← bottChernClass_closedCurrentPushforward]
    congr 1
    exact Subtype.ext (currentPushforward_comp hg hh _)

end Functoriality

end SGPT.BDivisor
