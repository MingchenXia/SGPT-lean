import SGPT.Foundations.Analysis.Pending.NaturalGlobalCurrentSmoothDual
import SGPT.Foundations.Analysis.Pending.NaturalGlobalSmoothDualCurrent
import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingGeometricEquality

/-! # The actual complete full native signed current and smooth dual equivalence

Both genuine original producers are calibrated by actual chart tests and
original geometric partitions, yielding internally proved mutual inverses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalFullNativeSmoothDuality

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents ChartPartition ProductTestForms
  NaturalChartTestGeometricExtension NaturalSupportedChartFormExtension
  NaturalGlobalCurrentSmoothDual NaturalGlobalSmoothDualCurrent
  NaturalCompactGeometricFormFrechetModule ActualCompactGlobalPairingCalibration
  ActualCompactGlobalPairingGeometricEquality

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An actual arbitrary full native chart test has exactly its original global current pairing. -/
theorem pairing_testExtension [CompactSpace M] {k : CurrentDegree n}
    (T : GlobalCurrent n M k) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pairingLM T (testExtension e η) = T.inChart e η := by
  classical
  obtain ⟨β, hβ1, -⟩ := exists_testFunction_eq_one_nhds_compact
    η.hasCompactSupport η.tsupport_subset
  let χ : M → ℝ := chartExtend e β
  have hβt : tsupport (β : ComplexModel n → ℝ) ⊆ e.val.target := β.tsupport_subset
  have hβc : IsCompact (tsupport (β : ComplexModel n → ℝ)) := β.hasCompactSupport
  have hC : IsCompact (e.val.symm '' tsupport (β : ComplexModel n → ℝ)) :=
    hβc.image_of_continuousOn (e.val.symm.continuousOn.mono hβt)
  have hsχ : tsupport χ ⊆ e.val.source :=
    (support_chartExtend_subset e).trans (by
      rw [hC.isClosed.closure_eq]
      rintro _ ⟨y, hy, rfl⟩
      exact e.val.map_target (hβt hy))
  have hcχ : IsCompact (tsupport χ) := hC.of_isClosed_subset (isClosed_tsupport χ)
    ((support_chartExtend_subset e).trans (by rw [hC.isClosed.closure_eq]))
  have hχ : ChartSmooth (n := n) χ := chartSmooth_chartExtend e β.contDiff hβc hβt
  have hgeom : (smulFun χ hχ (testExtension e η)).GeometricallyEq (testExtension e η) := by
    intro f z hz
    rw [smulFun_coeff]
    by_cases ho : z ∈ (chartTransition f e).source
    · have hx : f.val.symm z ∈ e.val.source := ho.2
      have hχz : χ (f.val.symm z) = β (chartTransition f e z) := chartExtend_of_mem hx
      change χ (f.val.symm z) • transportedCoeff e f η z = transportedCoeff e f η z
      rw [hχz, transportedCoeff, indicator_of_mem ho]
      by_cases hzero : η (chartTransition f e z) = 0
      · rw [hzero]
        ext v
        change β (chartTransition f e z) * (0 : ℝ) = 0
        exact mul_zero _
      · rw [hβ1.self_of_nhdsSet _ (subset_tsupport _ hzero), one_smul]
    · change χ (f.val.symm z) • transportedCoeff e f η z = transportedCoeff e f η z
      simp only [transportedCoeff, indicator_of_notMem ho, smul_zero]
  obtain ⟨ξ, hξ, -, hp⟩ := exists_testForm_with_pairing T (testExtension e η)
    e χ hχ hcχ hsχ
  have heq : ξ = η := by
    apply TestFunction.ext
    intro z
    rw [hξ]
    by_cases hz : z ∈ e.val.target
    · rw [indicator_of_mem hz]
      rw [show (testExtension e η).coeff e z = η z from
        extend_coeff_self e η η.contDiff η.hasCompactSupport η.tsupport_subset hz]
      have hχz : χ (e.val.symm z) = β z := by
        change chartExtend e β (e.val.symm z) = β z
        rw [chartExtend_of_mem (e.val.map_target hz), e.val.right_inv hz]
      rw [hχz]
      by_cases hzero : η z = 0
      · rw [hzero, smul_zero]
      · rw [hβ1.self_of_nhdsSet _ (subset_tsupport _ hzero), one_smul]
    · rw [indicator_of_notMem hz]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hz (η.tsupport_subset h))).symm
  rw [← pairing_eq_of_geometricallyEq T hgeom]
  exact hp.trans (congrArg (T.inChart e) heq)

section ActualModel

variable [AddCommGroup (GeometricRealForm n M q)] [Module ℝ (GeometricRealForm n M q)]
  [TopologicalSpace (GeometricRealForm n M q)]
  (a : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
  (K : Fin m → Compacts (ComplexModel n))
  (S : Submodule ℝ (Π i : Fin m,
    𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)))
  (E : GeometricRealForm n M q ≃L[ℝ] S)
  (hread : ∀ (α : SmoothRealForm n M q) i z,
    (E (GeometricRealForm.ofRepresentative α)).val i z =
      (a i).val.target.indicator (fun y => χ i ((a i).val.symm y) • α.coeff (a i) y) z)

/-- The actual internally transported module respects the original geometric representative map. -/
def representativeLM : SmoothRealForm n M q →ₗ[ℝ] GeometricRealForm n M q where
  toFun := GeometricRealForm.ofRepresentative
  map_add' α β := by
    apply E.injective
    rw [E.map_add]
    apply Subtype.ext
    funext i
    apply ContDiffMapSupportedIn.ext
    intro z
    change (E (GeometricRealForm.ofRepresentative (α + β))).val i z =
      (E (GeometricRealForm.ofRepresentative α)).val i z +
        (E (GeometricRealForm.ofRepresentative β)).val i z
    rw [hread, hread, hread]
    by_cases hz : z ∈ (a i).val.target
    · simp only [indicator_of_mem hz, coeff_add, smul_add]
    · simp only [indicator_of_notMem hz, zero_add]
  map_smul' r α := by
    apply E.injective
    rw [E.map_smul]
    apply Subtype.ext
    funext i
    apply ContDiffMapSupportedIn.ext
    intro z
    change (E (GeometricRealForm.ofRepresentative (r • α))).val i z =
      r • (E (GeometricRealForm.ofRepresentative α)).val i z
    rw [hread, hread]
    by_cases hz : z ∈ (a i).val.target
    · simp only [coeff_smul, indicator_of_mem hz]
      exact smul_comm _ _ _
    · simp only [indicator_of_notMem hz, smul_zero]

include hread in
/-- Actual geometric partition decomposition, with all original tensor compatibility used internally. -/
theorem geometric_partition_decomposition
    (hs : ∀ i, tsupport (χ i) ⊆ (a i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1)
    (γ : SmoothRealForm n M q) (η : ∀ i, TestForm (chartTarget (a i)) q)
    (hη : ∀ i z, η i z = (a i).val.target.indicator
      (fun y => χ i ((a i).val.symm y) • γ.coeff (a i) y) z) :
    GeometricRealForm.ofRepresentative γ =
      ∑ i, GeometricRealForm.ofRepresentative (testExtension (a i) (η i)) := by
  classical
  have hcoeff (f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ f.val.target)
      (i : Fin m) : (testExtension (a i) (η i)).coeff f z =
        χ i (f.val.symm z) • γ.coeff f z := by
    by_cases hi : f.val.symm z ∈ (a i).val.source
    · have ho : z ∈ (chartTransition f (a i)).source := ⟨hz, hi⟩
      have ht : chartTransition f (a i) z ∈ (a i).val.target := (a i).val.map_source hi
      have hinv : (a i).val.symm (chartTransition f (a i) z) = f.val.symm z :=
        (a i).val.left_inv hi
      change transportedCoeff (a i) f (η i) z = _
      rw [transportedCoeff, indicator_of_mem ho, hη, indicator_of_mem ht, hinv]
      ext v
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.smul_apply, Function.comp_def]
      rw [← γ.compatible f (a i) z ho v]
    · have ho : z ∉ (chartTransition f (a i)).source := fun h => hi h.2
      have hχz : χ i (f.val.symm z) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hi (hs i h))
      change transportedCoeff (a i) f (η i) z = _
      simp only [transportedCoeff, indicator_of_notMem ho, hχz, zero_smul]
  have hg : γ.GeometricallyEq (∑ i, testExtension (a i) (η i)) := by
    intro f z hz
    have hsval := congrFun (congrFun
      (map_sum (coeffAddHom (n := n) (M := M) (k := q))
        (fun i : Fin m => testExtension (a i) (η i)) Finset.univ) f) z
    simp only [coeffAddHom, Finset.sum_apply] at hsval
    change (∑ i, testExtension (a i) (η i)).coeff f z =
      ∑ i, (testExtension (a i) (η i)).coeff f z at hsval
    change γ.coeff f z = (∑ i, testExtension (a i) (η i)).coeff f z
    rw [hsval]
    simp only [hcoeff f z hz, ← Finset.sum_smul, h1, one_smul]
  calc
    GeometricRealForm.ofRepresentative γ =
        GeometricRealForm.ofRepresentative (∑ i, testExtension (a i) (η i)) := Quotient.sound hg
    _ = ∑ i, GeometricRealForm.ofRepresentative (testExtension (a i) (η i)) :=
      map_sum (representativeLM a χ K S E hread) _ _

end ActualModel

section NativeModel

variable {k : CurrentDegree n}
  [AddCommGroup (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [Module ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [TopologicalSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  (a : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
  (hχ : ∀ i, ChartSmooth (n := n) (χ i))
  (hs : ∀ i, tsupport (χ i) ⊆ (a i).val.source)
  (K : Fin m → Compacts (ComplexModel n))
  (hK : ∀ i, (K i : Set (ComplexModel n)) = (a i).val '' tsupport (χ i))
  (h1 : ∀ x, ∑ i, χ i x = 1)
  (S : Submodule ℝ (Π i : Fin m, 𝓓_{K i}(ComplexModel n,
    (ComplexModel n) [⋀^Fin (Module.finrank ℝ (ComplexModel n) - k.val)]→L[ℝ] ℝ)))
  (E : GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) ≃L[ℝ] S)
  (hread : ∀ (α : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) i z,
    (E (GeometricRealForm.ofRepresentative α)).val i z =
      (a i).val.target.indicator (fun y => χ i ((a i).val.symm y) • α.coeff (a i) y) z)

/-- The actual signed native finite pairing on the same full smooth complete model. -/
def nativeFunctionalCLM (T : GlobalCurrent n M k) :
    GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →L[ℝ] ℝ := by
  have hKT (i : Fin m) : (K i : Set (ComplexModel n)) ⊆ (a i).val.target := by
    rw [hK i]
    rintro _ ⟨x, hx, rfl⟩
    exact (a i).val.map_source (hs i hx)
  let sub : S →L[ℝ] (Π i : Fin m, 𝓓_{K i}(ComplexModel n,
      (ComplexModel n) [⋀^Fin (Module.finrank ℝ (ComplexModel n) - k.val)]→L[ℝ] ℝ)) :=
    { toLinearMap := S.subtype, cont := continuous_subtype_val }
  exact (stagePairingCLM T a K hKT).comp (sub.comp E.toContinuousLinearMap)

include hχ h1 hread in
/-- Complete original native global pairing calibration, proved from the actual partition. -/
theorem nativeFunctionalCLM_calibration [CompactSpace M] (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    nativeFunctionalCLM a χ hs K hK S E T (GeometricRealForm.ofRepresentative γ) =
      pairingLM T γ := by
  have hKT (i : Fin m) : (K i : Set (ComplexModel n)) ⊆ (a i).val.target := by
    rw [hK i]
    rintro _ ⟨x, hx, rfl⟩
    exact (a i).val.map_source (hs i hx)
  have hc (i : Fin m) : IsCompact (tsupport (χ i)) := (isClosed_tsupport _).isCompact
  let η (i : Fin m) : TestForm (chartTarget (a i))
      (Module.finrank ℝ (ComplexModel n) - k.val) :=
    TestFunction.ofSupportedIn (hKT i) ((E (GeometricRealForm.ofRepresentative γ)).val i)
  have hη (i : Fin m) (z : ComplexModel n) : η i z = (a i).val.target.indicator
      (fun y => χ i ((a i).val.symm y) • γ.coeff (a i) y) z := hread γ i z
  have hp := pairing_eq_sum T γ m a χ hχ hc hs h1 η hη
  change stagePairingCLM T a K hKT ((E (GeometricRealForm.ofRepresentative γ)).val) = _
  rw [stagePairingCLM_apply]
  exact hp.symm

variable [IsTopologicalAddGroup (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [ContinuousSMul ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [LocallyConvexSpace ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]

include h1 in
/-- The actual full original signed current and continuous smooth dual equivalence. -/
def nativeDuality [CompactSpace M] : GlobalCurrent n M k ≃ₗ[ℝ]
    (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →L[ℝ] ℝ) where
  toFun := nativeFunctionalCLM a χ hs K hK S E
  invFun := dualCurrent a χ hχ hs K hK S E hread
  left_inv T := by
    apply GlobalCurrent.ext
    intro e η
    rw [dualCurrent_inChart, nativeFunctionalCLM_calibration a χ hχ hs K hK h1 S E hread,
      pairing_testExtension]
  right_inv L := by
    apply ContinuousLinearMap.ext
    intro v
    refine Quotient.inductionOn v ?_
    intro γ
    change nativeFunctionalCLM a χ hs K hK S E
      (dualCurrent a χ hχ hs K hK S E hread L) (GeometricRealForm.ofRepresentative γ) =
        L (GeometricRealForm.ofRepresentative γ)
    rw [nativeFunctionalCLM_calibration a χ hχ hs K hK h1 S E hread]
    have hKT (i : Fin m) : (K i : Set (ComplexModel n)) ⊆ (a i).val.target := by
      rw [hK i]
      rintro _ ⟨x, hx, rfl⟩
      exact (a i).val.map_source (hs i hx)
    have hc (i : Fin m) : IsCompact (tsupport (χ i)) := (isClosed_tsupport _).isCompact
    let η (i : Fin m) : TestForm (chartTarget (a i))
        (Module.finrank ℝ (ComplexModel n) - k.val) :=
      TestFunction.ofSupportedIn (hKT i) ((E (GeometricRealForm.ofRepresentative γ)).val i)
    have hη (i : Fin m) (z : ComplexModel n) : η i z = (a i).val.target.indicator
        (fun y => χ i ((a i).val.symm y) • γ.coeff (a i) y) z := hread γ i z
    rw [pairing_eq_sum _ γ m a χ hχ hc hs h1 η hη]
    simp only [dualCurrent_inChart]
    rw [← map_sum,
      ← geometric_partition_decomposition a χ K S E hread hs h1 γ η hη]
  map_add' T U := by
    apply ContinuousLinearMap.ext
    intro v
    simp [nativeFunctionalCLM, stagePairingCLM_apply, Finset.sum_add_distrib]
  map_smul' r T := by
    apply ContinuousLinearMap.ext
    intro v
    simp [nativeFunctionalCLM, stagePairingCLM_apply, Finset.mul_sum]

end NativeModel

/-- Compactness alone supplies genuine complete full native signed-current smooth duality. -/
theorem exists_complete_native_duality [CompactSpace M] (k : CurrentDegree n) :
    ∃ g : AddCommGroup (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
      let _ := g
      ∃ v : Module ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
        let _ := v
        ∃ u : UniformSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
          let _ := u
          CompleteSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          T2Space (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          FirstCountableTopology
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          IsTopologicalAddGroup
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          ContinuousSMul ℝ
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          LocallyConvexSpace ℝ
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          ∃ D : GlobalCurrent n M k ≃ₗ[ℝ]
              (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →L[ℝ] ℝ),
            (∀ T γ, D T (GeometricRealForm.ofRepresentative γ) = pairingLM T γ) ∧
            ∀ L e η, (D.symm L).inChart e η =
              L (GeometricRealForm.ofRepresentative (testExtension e η)) := by
  classical
  obtain ⟨m, a, χ, K, hχ, -, hs, hK, h1, hmodel⟩ :=
    exists_complete_locally_convex_module (n := n) (M := M)
  obtain ⟨S, -, g, v, u, E, hc, ht, hfc, ha, hv, hl, hread⟩ :=
    hmodel (Module.finrank ℝ (ComplexModel n) - k.val)
  let _ := g
  let _ := v
  let _ := u
  let _ := ha
  let _ := hv
  let _ := hl
  refine ⟨g, v, u, hc, ht, hfc, ha, hv, hl,
    nativeDuality a χ hχ hs K hK h1 S E hread, ?_, ?_⟩
  · exact nativeFunctionalCLM_calibration a χ hχ hs K hK h1 S E hread
  · exact dualCurrent_inChart a χ hχ hs K hK S E hread

end SGPT.Foundations.Analysis.Pending.NaturalFullNativeSmoothDuality
