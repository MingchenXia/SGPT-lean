import SGPT.BDivisor.CurrentPushforwardType
import SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentCoefficientDifferential
import SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentPairingDifferentials
import SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarDdc

/-!
# `ddᶜ` of degree-zero currents in coefficients

For a current `F` of degree `0` in a chart (a continuous functional on top-degree test forms),
the current `ddᶜF : η ↦ F(ddᶜη)` of degree two has distribution coefficients `ddᶜ R`, where `R`
is the scalar coefficient of `F` (`R(φ) = F(φ · vol)`). The proof composes the coefficient rule
for the exterior derivative (`block_coefficient_exterior`) twice with the coefficient rule for the
complex structure (the volume form is `J`-invariant), and uses that `ddᶜR` is of type `(1,1)`.

This is the local input of the descent of the push-forward of currents to Bott--Chern classes
(`SGPT.BDivisor.ClassPushforward`): `g_*(ddᶜ h) = ddᶜ(g_* h)` has zero class.

Main declarations:

* `SGPT.BDivisor.currentCoefficients_comp_twist` — coefficients of `T ∘ J^*`;
* `SGPT.BDivisor.currentCoefficients_comp_localDdcTest` — coefficients of `F ∘ ddᶜ` are `ddᶜ` of
  the scalar coefficient of `F`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents
  SGPT.Foundations.Analysis.Pending.CompactDifferentialTests

section Local

variable {n : ℕ} {U : Opens (ComplexModel n)}

theorem currentCoefficients_smul {a q : ℕ}
    (vol : (ComplexModel n) [⋀^(Fin a ⊕ Fin q)]→L[ℝ] ℝ) (c : ℝ) (T : TestForm U q →L[ℝ] ℝ) :
    currentCoefficients vol (c • T) = c • currentCoefficients vol T := by
  ext v φ
  rfl

theorem currentCoefficients_neg {a q : ℕ}
    (vol : (ComplexModel n) [⋀^(Fin a ⊕ Fin q)]→L[ℝ] ℝ) (T : TestForm U q →L[ℝ] ℝ) :
    currentCoefficients vol (-T) = -currentCoefficients vol T := by
  ext v φ
  rfl

/-- **Coefficients of `T ∘ J^*`**: `J^*` acts on the inserted vectors by `J⁻¹ = -J`. -/
theorem currentCoefficients_comp_twist {a q : ℕ}
    (C : Module.Basis (Fin a ⊕ Fin q) ℝ (ComplexModel n)) (T : TestForm U q →L[ℝ] ℝ)
    (v : Fin a → ComplexModel n) (φ : 𝓓(U, ℝ)) :
    currentCoefficients (basisVolume C) (T.comp twistTestCLM) v φ =
      currentCoefficients (basisVolume C) T (fun i => (-Complex.I) • v i) φ := by
  rw [currentCoefficients_apply, currentCoefficients_apply, ContinuousLinearMap.comp_apply]
  congr 1
  apply TestFunction.ext
  intro x
  ext u
  simp only [twistTestCLM_apply, constantTestFormCLM_apply, ContinuousAlternatingMap.smul_apply,
    contractVolume_apply, basisVolume_apply]
  congr 1
  rw [← basis_det_complexStructure C (Sum.elim (fun i => (-Complex.I) • v i) u)]
  congr 1
  funext i
  rcases i with i | j
  · simp [smul_smul]
  · rfl

/-- The scalar `ddᶜ` coefficient is invariant when both inserted vectors are rotated by `-J`. -/
theorem ddC_neg_twist (R : 𝓓'(U, ℝ)) (v : Fin (1 + 1) → ComplexModel n) :
    ddC R (fun i => (-Complex.I) • v i) = ddC R v := by
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have h := _root_.SGPT.Foundations.Analysis.Pending.LocalCurrents.ddC_isOneOne R
    ((-Complex.I) • v 0) ((-Complex.I) • v 1)
  have hI (y : ComplexModel n) : Complex.I • ((-Complex.I) • y) = y := by
    rw [smul_smul]; simp
  rw [hI, hI] at h
  have hfun : (fun i => (-Complex.I) • v i) = ![(-Complex.I) • v 0, (-Complex.I) • v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun, hv]
  exact h.symm

/-- **Coefficients of `F ∘ ddᶜ`.** For a functional `F` on test forms of degree `q + 2` (`q` even),
the degree-two coefficients of `η ↦ F(ddᶜη)` are `ddᶜ` of the degree-zero coefficient of `F`, for
the volume forms of one ordered basis `B`. -/
theorem currentCoefficients_comp_localDdcTest {q a : ℕ} (hq : Even q) (ha : a = 1 + 1)
    (B : Module.Basis (Fin (a + q)) ℝ (ComplexModel n))
    (F : TestForm U (q + 1 + 1) →L[ℝ] ℝ) (v : Fin a → ComplexModel n) (φ : 𝓓(U, ℝ)) :
    currentCoefficients (basisVolume (B.reindex finSumFinEquiv.symm))
        (F.comp localDdcTestCLM) v φ =
      ddC (currentCoefficients (basisVolume (B.reindex (finSumFinEquiv.trans
        (finCongr (by omega : 0 + (q + 1 + 1) = a + q))).symm)) F Fin.elim0)
        (v ∘ Fin.cast ha.symm) φ := by
  subst ha
  set c : ℝ := (-1 : ℝ) ^ (q + 1) / (4 * Real.pi) with hc
  -- the factorization `ddᶜ = d ∘ (c J^* d J^*)` on test forms
  have hG : F.comp localDdcTestCLM = c • ((((F.comp exteriorTestCLM).comp twistTestCLM).comp
      exteriorTestCLM).comp twistTestCLM) := by
    ext η
    simp only [localDdcTestCLM, localDcTestCLM, ContinuousLinearMap.comp_apply,
      smul_apply, map_smul, hc]
  -- the two exterior steps
  let B₁ : Module.Basis (Fin ((0 + 1) + (q + 1))) ℝ (ComplexModel n) :=
    B.reindex (finCongr (by omega))
  have h1 := Pending.NaturalNativeCurrentCoefficientDifferential.block_coefficient_exterior
    (r := 0) (s := q + 1) B₁ F
  have h3 := Pending.NaturalNativeCurrentCoefficientDifferential.block_coefficient_exterior
    (r := 1) (s := q) B ((F.comp exteriorTestCLM).comp twistTestCLM)
  have hB1 : B₁.reindex finSumFinEquiv.symm = B.reindex (finSumFinEquiv.trans
      (finCongr (show 1 + (q + 1) = (1 + 1) + q by omega))).symm := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    simp only [B₁, Module.Basis.reindex_apply]
    congr 1
  have hB0 : B₁.reindex (finSumFinEquiv.trans
      (finCongr (show 0 + (q + 1 + 1) = (0 + 1) + (q + 1) by omega))).symm =
      B.reindex (finSumFinEquiv.trans
        (finCongr (by omega : 0 + (q + 1 + 1) = (1 + 1) + q))).symm := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    simp only [B₁, Module.Basis.reindex_apply]
    congr 1
  rw [hB1, hB0, show ((-1 : ℤ) ^ (0 + 1)) = -1 by norm_num, neg_one_zsmul,
    currentCoefficients_neg] at h1
  rw [show ((-1 : ℤ) ^ (1 + 1)) = 1 by norm_num, one_smul] at h3
  rw [hG, currentCoefficients_smul, AlternatingMap.smul_apply, _root_.smul_apply,
    currentCoefficients_comp_twist, h3]
  set A₀ := currentCoefficients (basisVolume (B.reindex (finSumFinEquiv.trans
    (finCongr (by omega : 0 + (q + 1 + 1) = (1 + 1) + q))).symm)) F with hA₀
  set R : 𝓓'(U, ℝ) := A₀ Fin.elim0 with hR
  -- the one-form coefficient of `(F ∘ d) ∘ J^*`
  have hΨ : currentCoefficients (basisVolume (B.reindex (finSumFinEquiv.trans
      (finCongr (show 1 + (q + 1) = (1 + 1) + q by omega))).symm))
        ((F.comp exteriorTestCLM).comp twistTestCLM) =
      (-4 * Real.pi) • dc R := by
    ext u ψ
    rw [currentCoefficients_comp_twist]
    have hval : currentCoefficients (basisVolume (B.reindex (finSumFinEquiv.trans
        (finCongr (show 1 + (q + 1) = (1 + 1) + q by omega))).symm)) (F.comp exteriorTestCLM) =
        -exteriorDerivative A₀ := by
      rw [← h1, neg_neg]
    rw [hval, AlternatingMap.neg_apply, neg_apply, exteriorDerivative_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul]
    have hrem : (Fin.removeNth 0 fun i => (-Complex.I) • u i) = Fin.elim0 :=
      Subsingleton.elim _ _
    rw [hrem, ← hR]
    simp only [dc, oneForm_apply, AlternatingMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      directionalLM_apply, _root_.smul_apply, smul_eq_mul]
    have hdir : (-Complex.I) • u 0 = (-1 : ℝ) • (Complex.I • u 0) := by
      rw [neg_smul, neg_one_smul]
    rw [hdir, Distribution.lineDerivCLM_smul]
    simp only [_root_.smul_apply, smul_eq_mul]
    field_simp
  rw [hΨ]
  have hd : exteriorDerivative ((-4 * Real.pi) • dc R) = (-4 * Real.pi) • ddC R := by
    ext w χ
    simp only [ddC, exteriorDerivative_apply, AlternatingMap.smul_apply, map_smul,
      Finset.smul_sum, _root_.sum_apply, _root_.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_comm ((-1 : ℤ) ^ (i : ℕ))]
  rw [hd, AlternatingMap.smul_apply, _root_.smul_apply, ddC_neg_twist, smul_eq_mul,
    smul_eq_mul, ← mul_assoc]
  have hconst : c * (-4 * Real.pi) = 1 := by
    rw [hc, pow_succ, hq.neg_one_pow]
    field_simp
  rw [hconst, one_mul]
  rfl

end Local

section Global

open Pending.NaturalFullCurrentTranspose Pending.NaturalNativeCurrentDifferentials
  Pending.NaturalNativeCurrentPairingDifferentials FirstPass.HolomorphicMaps
  Pending.NaturalChartTestGeometricExtension Pending.XiaoComplexDifferential

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The chart functional in its exact complementary degree is the original chart functional
after the degree identification. -/
theorem nativeChartFunctional_eq_cast {k : CurrentDegree n} {a : ℕ}
    (h : Module.finrank ℝ (ComplexModel n) - k.val = a) (T : GlobalCurrent n M k)
    (e : ComplexChart n M) (ξ : TestForm (chartTarget e) a) :
    nativeChartFunctional h T e ξ = T.inChart e (h.symm ▸ ξ) := by
  subst h
  rfl

theorem le_of_add_two_eq {q N : ℕ} (h : q + 1 + 1 = N) : q ≤ N := by omega

/-- The ordered basis `b` with its index set split as `∅ ⊕ (q + 2)`: the volume form of the
degree-zero coefficients. -/
def scalarBasis (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {q : ℕ} (hqN : q + 1 + 1 = Module.finrank ℝ (ComplexModel n)) :
    Module.Basis (Fin 0 ⊕ Fin (q + 1 + 1)) ℝ (ComplexModel n) :=
  (b.reindex (finCongr (by simp only [complementDegree]; omega :
    Module.finrank ℝ (ComplexModel n) = (complementDegree n q (le_of_add_two_eq hqN)).val + q))).reindex
    (finSumFinEquiv.trans (finCongr (by simp only [complementDegree]; omega :
      0 + (q + 1 + 1) = (complementDegree n q (le_of_add_two_eq hqN)).val + q))).symm

/-- The scalar coefficient of a current `U` of degree `N - (q + 2) = 0` (`q + 2 = N`):
`φ ↦ U(φ · vol)` for the volume form of the ordered basis `b`. -/
def scalarCoeff (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {q : ℕ} (hqN : q + 1 + 1 = Module.finrank ℝ (ComplexModel n))
    (U : GlobalCurrent n M (complementDegree n (q + 1 + 1) hqN.le)) (e : ComplexChart n M) :
    𝓓'(chartTarget e, ℝ) :=
  currentCoefficients (basisVolume (scalarBasis b hqN))
    (nativeChartFunctional (complementDegree_complement n (q + 1 + 1) hqN.le) U e) Fin.elim0

/-- **Coefficients of `ddᶜ U`** for a current `U` of degree zero: `ddᶜ` of its scalar
coefficient. -/
theorem coefficients_ddcCurrentCLM
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {q : ℕ} (hqe : Even q) (hqN : q + 1 + 1 = Module.finrank ℝ (ComplexModel n))
    (U : GlobalCurrent n M (complementDegree n (q + 1 + 1) hqN.le)) (e : ComplexChart n M)
    (v : Fin (complementDegree n q (le_of_add_two_eq hqN)).val → ComplexModel n)
    (φ : 𝓓(chartTarget e, ℝ)) :
    (ddcCurrentCLM q hqN.le U).coefficients b e v φ =
      ddC (scalarCoeff b hqN U e)
        (v ∘ Fin.cast (by simp only [complementDegree]; omega)) φ := by
  rw [Pending.NaturalNativeCurrentCoefficientDifferential.coefficient_block_apply b
    (complementDegree_complement n q (by omega))]
  have hchart : nativeChartFunctional (complementDegree_complement n q (by omega))
      (ddcCurrentCLM q hqN.le U) e =
      (nativeChartFunctional (complementDegree_complement n (q + 1 + 1) hqN.le) U e).comp
        localDdcTestCLM := by
    ext η
    exact ddcCurrentCLM_chart q hqN.le U e η
  rw [hchart, ← currentCoefficients_apply]
  exact currentCoefficients_comp_localDdcTest hqe
    (by simp only [complementDegree]; omega) _ _ v φ

/-- **The scalar coefficients of a current of degree zero form a compatible family** of scalar
distributions (transformation by the Jacobian of the chart changes). -/
theorem scalarFamilyCompatible_scalarCoeff
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {q : ℕ} (hqN : q + 1 + 1 = Module.finrank ℝ (ComplexModel n))
    (U : GlobalCurrent n M (complementDegree n (q + 1 + 1) hqN.le)) :
    Pending.FiniteScalarDistributionGluing.ScalarFamilyCompatible (scalarCoeff b hqN U) := by
  intro e f η ψ hrel
  set B₀ := scalarBasis b hqN with hB₀
  set Ω := contractVolume (basisVolume B₀) (Fin.elim0 : Fin 0 → ComplexModel n) with hΩ
  have hmono (V : Opens (ComplexModel n)) (W : Opens (ComplexModel n)) (hVW : V ≤ W)
      (χ : 𝓓(V, ℝ)) :
      constantTestFormCLM Ω (TestFunction.monoCLM ℝ χ : 𝓓(W, ℝ)) =
        (TestFunction.monoCLM ℝ (constantTestFormCLM Ω χ) : TestForm W (q + 1 + 1)) := by
    apply TestFunction.ext
    intro z
    rw [constantTestFormCLM_apply, testForm_inclusion_apply hVW,
      congrFun (testFunction_inclusion_coe hVW χ) z,
      constantTestFormCLM_apply]
  change nativeChartFunctional _ U e (constantTestFormCLM Ω (TestFunction.monoCLM ℝ η)) =
    nativeChartFunctional _ U f (constantTestFormCLM Ω (TestFunction.monoCLM ℝ ψ))
  rw [hmono _ _ (overlapSource_le e f), hmono _ _ (overlapTarget_le e f)]
  apply (nativeDegreeEquiv (complementDegree_complement n (q + 1 + 1) hqN.le) U).property
  intro z hz w
  rw [constantTestFormCLM_apply, constantTestFormCLM_apply, hrel z hz]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hΩ, contractVolume_apply,
    basisVolume_apply]
  have hcomp : (Sum.elim (Fin.elim0 : Fin 0 → ComplexModel n)
      (fun i => chartTransitionDerivative e f z (w i))) =
      (chartTransitionDerivative e f z) ∘ Sum.elim (Fin.elim0 : Fin 0 → ComplexModel n) w := by
    funext i
    rcases i with i | i
    · exact i.elim0
    · rfl
  rw [hcomp]
  change _ = ψ _ * B₀.det ((chartTransitionDerivative e f z).toLinearMap ∘ _)
  rw [B₀.det_comp, Pending.ThetaPshChartLimitGluing.transitionJac,
    abs_of_nonneg (Pending.GlobalCurrents.chartTransitionDerivative_det_nonneg e f hz)]
  change _ = ψ _ * (ContinuousLinearMap.det (chartTransitionDerivative e f z) * _)
  ring

/-- A transported current has the transported coefficients. -/
theorem coefficients_cast
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k k' : CurrentDegree n} (h : k = k') (T : GlobalCurrent n M k) (e : ComplexChart n M)
    (v : Fin k'.val → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    (h ▸ T : GlobalCurrent n M k').coefficients b e v φ =
      T.coefficients b e (v ∘ Fin.cast (congrArg Fin.val h)) φ := by
  subst h
  rfl

variable {Z Y : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {g : Z → Y}
  (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)

theorem GeometricallyEq.complexTwist' {k : ℕ} {a a' : SmoothRealForm n Y k}
    (h : a.GeometricallyEq a') : (complexTwist a).GeometricallyEq (complexTwist a') := by
  intro e z hz
  simp only [complexTwist_coeff, h e hz]

theorem GeometricallyEq.smul' {k : ℕ} (c : ℝ) {a a' : SmoothRealForm n Y k}
    (h : a.GeometricallyEq a') : (c • a).GeometricallyEq (c • a') := by
  intro e z hz
  change c • a.coeff e z = c • a'.coeff e z
  rw [h e hz]

theorem pullback_smul_geometricallyEq {k : ℕ} (c : ℝ) (a : SmoothRealForm n Y k) :
    (SmoothRealForm.pullback hg (c • a)).GeometricallyEq
      (c • SmoothRealForm.pullback hg a) := by
  intro e z hz
  let d := complexChartAt (n := n) (g (e.val.symm z))
  have hzd : z ∈ coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  change _ = c • (SmoothRealForm.pullback hg a).coeff e z
  rw [SmoothRealForm.pullback_coeff hg _ e d hzd, SmoothRealForm.pullback_coeff hg _ e d hzd]
  rfl

/-- Holomorphic pull-back commutes with `dᶜ`. -/
theorem pullback_dc_geometricallyEq {k : ℕ} (a : SmoothRealForm n Y k) :
    (SmoothRealForm.pullback hg (Pending.XiaoComplexDifferential.dc a)).GeometricallyEq
      (Pending.XiaoComplexDifferential.dc (SmoothRealForm.pullback hg a)) := by
  unfold Pending.XiaoComplexDifferential.dc
  refine (pullback_smul_geometricallyEq hg _ _).trans (GeometricallyEq.smul' _ ?_)
  refine (pullback_complexTwist_geometricallyEq hg _).trans (GeometricallyEq.complexTwist' ?_)
  exact (SmoothRealForm.exteriorDerivative_pullback hg _).symm.trans
    (pullback_complexTwist_geometricallyEq hg a).exteriorDerivative

/-- Holomorphic pull-back commutes with `ddᶜ`. -/
theorem pullback_ddc_geometricallyEq {k : ℕ} (a : SmoothRealForm n Y k) :
    (SmoothRealForm.pullback hg (Pending.XiaoComplexDifferential.ddc a)).GeometricallyEq
      (Pending.XiaoComplexDifferential.ddc (SmoothRealForm.pullback hg a)) :=
  (SmoothRealForm.exteriorDerivative_pullback hg _).symm.trans
    (pullback_dc_geometricallyEq hg a).exteriorDerivative

/-- **Push-forward commutes with `ddᶜ`** on currents: `g_*(ddᶜ V) = ddᶜ(g_* V)`. -/
theorem currentPushforward_ddcCurrentCLM [CompactSpace Z] {q : ℕ}
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (V : GlobalCurrent n Z (complementDegree n (q + 1 + 1) hq)) :
    currentPushforward hg (ddcCurrentCLM q hq V) =
      ddcCurrentCLM q hq (currentPushforward hg V) := by
  apply eq_of_nativeChartFunctional_eq (complementDegree_complement n q (by omega))
  intro e η
  rw [ddcCurrentCLM_chart, nativeChartFunctional_eq_cast, nativeChartFunctional_eq_cast,
    currentPushforward_inChart_cast hg _ e (complementDegree_complement n q (by omega)),
    currentPushforward_inChart_cast hg _ e (complementDegree_complement n (q + 1 + 1) hq)]
  have hpair := ddcCurrentCLM_pairing q hq V
    (SmoothRealForm.pullback hg (testExtension e η))
  unfold pairingInDegree at hpair
  rw [hpair]
  apply pairingLM_cast_congr V (complementDegree_complement n (q + 1 + 1) hq)
  exact (pullback_ddc_geometricallyEq hg _).symm.trans
    (SmoothRealForm.GeometricallyEq.pullback hg
      (Pending.NaturalChartExtensionDifferentials.ddc_testExtension_geometricallyEq e η))

end Global

end SGPT.BDivisor
