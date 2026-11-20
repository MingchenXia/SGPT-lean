import SGPT.BDivisor.TestFormPullback
import SGPT.Foundations.Analysis.Pending.NaturalFullNativeSmoothDuality
import SGPT.Foundations.Analysis.Pending.NaturalGlobalSmoothDualCurrent
import SGPT.Foundations.Analysis.Pending.NaturalClosedCurrentStokes
import SGPT.Foundations.Analysis.Pending.NaturalChartExtensionDifferentials

/-!
# Push-forward of currents along holomorphic maps from compact manifolds

Let `g : Z → Y` be a holomorphic map between complex manifolds of the same dimension `n`, with
`Z` compact (so `g` is proper). For a current `T` of real degree `k` on `Z` (a
`GlobalCurrent`: a compatible family of continuous chart functionals on test forms), the
**push-forward** `g_* T` is the current on `Y` given in a chart `e` of `Y` by

`(g_* T)_e(η) = ⟨T, g^*(η extended by zero)⟩`,

the global pairing of `T` with the smooth form `g^* η` on the compact manifold `Z`
(Xia, *Foundations of pluripotential theory*, `prop:proper-current-pushforward`; there
`(F_*T)(φ) = T(χ F^*φ)` with a cut-off `χ = 1` near `Supp T ∩ F⁻¹(Supp φ)`, and `χ = 1` is allowed
since `Z` is compact). In SGPT this is the push-forward `π_* S` of currents along modifications
(`prop:nppmassinv`, second identity; `def:DT`; `lma:Siudec_pullpush`) and the push-forward of
classes in `def:bdiv:L38`.

Main declarations:

* `SGPT.BDivisor.currentPushforward` — `g_* T`, a `GlobalCurrent` on `Y`: its chart functionals
  are continuous (`SGPT.BDivisor.TestFormPullback.pullTestCLM`) and compatible on overlaps;
* `SGPT.BDivisor.currentPushforward_inChart` — the defining formula above;
* `SGPT.BDivisor.currentPushforwardLM` — `T ↦ g_* T` is real linear;
* `SGPT.BDivisor.pairingLM_currentPushforward` — for `Y` compact, `⟨g_* T, γ⟩ = ⟨T, g^* γ⟩` for
  every smooth form `γ` on `Y`;
* `SGPT.BDivisor.currentPushforward_id`, `SGPT.BDivisor.currentPushforward_comp` — functoriality
  `id_* = id`, `(g ∘ h)_* = g_* ∘ h_*`;
* `SGPT.BDivisor.isClosed_currentPushforward` — the push-forward of a closed current is closed
  (`d (g_* T) = g_* (d T)`, via global Stokes on `Z`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.Pending.ChartPartition
  SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormChartTests
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingGeometricEquality
  SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension
  SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension
  SGPT.Foundations.Analysis.Pending.NaturalFullNativeSmoothDuality
  SGPT.Foundations.Analysis.Pending.NaturalGlobalSmoothDualCurrent
  SGPT.BDivisor.TestFormPullback

/-- A finite chart partition of unity: finitely many charts with nonnegative chart-smooth weights
of compact support in the chart sources, summing to one. -/
structure ChartPartitionOfUnity (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  /-- The number of pieces. -/
  card : ℕ
  /-- The charts. -/
  chart : Fin card → ComplexChart n M
  /-- The weights. -/
  weight : Fin card → M → ℝ
  smooth : ∀ i, ChartSmooth (n := n) (weight i)
  nonneg : ∀ i x, 0 ≤ weight i x
  subset : ∀ i, tsupport (weight i) ⊆ (chart i).val.source
  compact : ∀ i, IsCompact (tsupport (weight i))
  sum_eq_one : ∀ x, ∑ i, weight i x = 1

namespace ChartPartitionOfUnity

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A compact complex manifold has a finite chart partition of unity. -/
theorem nonempty [CompactSpace M] : Nonempty (ChartPartitionOfUnity n M) := by
  obtain ⟨m, χ, idx, hχ, h0, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  exact ⟨⟨m, fun i => complexChartAt (idx i), χ, hχ, h0, hχs, hχc, hχ1⟩⟩

/-- A fixed chart partition of unity of a compact complex manifold. -/
def choice [CompactSpace M] : ChartPartitionOfUnity n M := Classical.choice nonempty

/-- The global pairing of a current with a smooth form is the sum of the chart pairings of the
weighted pieces, for every chart partition of unity. -/
theorem pairingLM_eq_sum [CompactSpace M] (P : ChartPartitionOfUnity n M) {k : CurrentDegree n}
    (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (η : ∀ i, LocalCurrents.TestForm (chartTarget (P.chart i))
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (hη : ∀ i z, η i z = (P.chart i).val.target.indicator
      (fun y => P.weight i ((P.chart i).val.symm y) • γ.coeff (P.chart i) y) z) :
    pairingLM T γ = ∑ i, T.inChart (P.chart i) (η i) :=
  pairing_eq_sum T γ P.card P.chart P.weight P.smooth P.compact P.subset P.sum_eq_one η hη

end ChartPartitionOfUnity

/-- The global pairing is additive in the current. -/
theorem pairingLM_add {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] {k : CurrentDegree n} (T U : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pairingLM (T + U) γ = pairingLM T γ + pairingLM U γ := by
  let P : ChartPartitionOfUnity n M := ChartPartitionOfUnity.choice
  choose η hη _ using fun i => exists_testForm (P.chart i) γ (P.weight i) (P.smooth i)
    (P.compact i) (P.subset i)
  rw [P.pairingLM_eq_sum (T + U) γ η hη, P.pairingLM_eq_sum T γ η hη,
    P.pairingLM_eq_sum U γ η hη, ← Finset.sum_add_distrib]
  rfl

/-- The global pairing is homogeneous in the current. -/
theorem pairingLM_smul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    {k : CurrentDegree n} (c : ℝ) (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pairingLM (c • T) γ = c * pairingLM T γ := by
  let P : ChartPartitionOfUnity n M := ChartPartitionOfUnity.choice
  choose η hη _ using fun i => exists_testForm (P.chart i) γ (P.weight i) (P.smooth i)
    (P.compact i) (P.subset i)
  rw [P.pairingLM_eq_sum (c • T) γ η hη, P.pairingLM_eq_sum T γ η hη, Finset.mul_sum]
  rfl

variable {n : ℕ} {Z Y : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {g : Z → Y}
  (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {k : CurrentDegree n}

/-- The chart functional of the push-forward, computed with a chart partition of unity of `Z`:
`η ↦ ∑ᵢ Tᵢ(χᵢ · g^*η)`. Each summand is continuous. -/
def pushforwardChart (P : ChartPartitionOfUnity n Z) (T : GlobalCurrent n Z k)
    (e : ComplexChart n Y) : LocalCurrents.LocalCurrent (chartTarget e) k :=
  ∑ i, (T.inChart (P.chart i)).comp
    (pullTestCLM hg (P.chart i) e (P.smooth i) (P.compact i) (P.subset i))

/-- The chart functional of the push-forward is the global pairing of `T` with the pull-back of
the zero extension of the test form; in particular it does not depend on the partition. -/
theorem pushforwardChart_apply [CompactSpace Z] (P : ChartPartitionOfUnity n Z)
    (T : GlobalCurrent n Z k) (e : ComplexChart n Y)
    (η : LocalCurrents.TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pushforwardChart hg P T e η =
      pairingLM T (SmoothRealForm.pullback hg (testExtension e η)) := by
  rw [P.pairingLM_eq_sum T _
    (fun i => pullTestCLM hg (P.chart i) e (P.smooth i) (P.compact i) (P.subset i) η)
    (fun i z => pullTestCLM_apply_eq hg (P.chart i) e (P.smooth i) (P.compact i)
      (P.subset i) η z)]
  simp [pushforwardChart]

/-- The chart functionals of the push-forward are compatible on chart overlaps. -/
theorem pushforwardChart_compatible [CompactSpace Z] (P : ChartPartitionOfUnity n Z)
    (T : GlobalCurrent n Z k) :
    CurrentFamilyCompatible (fun e => pushforwardChart hg P T e) := by
  intro e f η θ hrel
  rw [LocalCurrents.restrictLocalCurrent_apply, LocalCurrents.restrictLocalCurrent_apply,
    pushforwardChart_apply, pushforwardChart_apply]
  apply pairing_eq_of_geometricallyEq
  apply SmoothRealForm.GeometricallyEq.pullback hg
  exact (GeometricRealForm.ofRepresentative_eq_iff _ _).mp
    (related_test_extensions_eq e f η θ hrel)

/-- **Push-forward of currents** along a holomorphic map `g : Z → Y` from a compact manifold:
`(g_* T)_e(η) = ⟨T, g^* η⟩`. -/
def currentPushforward [CompactSpace Z] (T : GlobalCurrent n Z k) : GlobalCurrent n Y k :=
  ⟨fun e => pushforwardChart hg ChartPartitionOfUnity.choice T e,
    pushforwardChart_compatible hg _ T⟩

/-- The defining formula of the push-forward. -/
theorem currentPushforward_inChart [CompactSpace Z] (T : GlobalCurrent n Z k)
    (e : ComplexChart n Y)
    (η : LocalCurrents.TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
    (currentPushforward hg T).inChart e η =
      pairingLM T (SmoothRealForm.pullback hg (testExtension e η)) :=
  pushforwardChart_apply hg _ T e η

/-- The push-forward is real linear in the current. -/
def currentPushforwardLM [CompactSpace Z] : GlobalCurrent n Z k →ₗ[ℝ] GlobalCurrent n Y k where
  toFun := currentPushforward hg
  map_add' T U := GlobalCurrent.ext fun e η => by
    simp only [GlobalCurrent.inChart_add, add_apply, currentPushforward_inChart,
      pairingLM_add]
  map_smul' c T := GlobalCurrent.ext fun e η => by
    simp only [GlobalCurrent.inChart_smul, smul_apply, currentPushforward_inChart,
      pairingLM_smul, RingHom.id_apply, smul_eq_mul]

@[simp] theorem currentPushforwardLM_apply [CompactSpace Z] (T : GlobalCurrent n Z k) :
    currentPushforwardLM (k := k) hg T = currentPushforward hg T := rfl

/-- The coefficients of `g^*` of the zero extensions of the weighted pieces of a form `γ` on `Y`
add up to the coefficients of `g^* γ`. -/
theorem sum_pullback_testExtension_coeff (Q : ChartPartitionOfUnity n Y) {q : ℕ}
    (γ : SmoothRealForm n Y q) (η : ∀ j, LocalCurrents.TestForm (chartTarget (Q.chart j)) q)
    (hη : ∀ j z, η j z = (Q.chart j).val.target.indicator
      (fun y => Q.weight j ((Q.chart j).val.symm y) • γ.coeff (Q.chart j) y) z)
    (f : ComplexChart n Z) {z : ComplexModel n} (hz : z ∈ f.val.target) :
    ∑ j, (SmoothRealForm.pullback hg (testExtension (Q.chart j) (η j))).coeff f z =
      (SmoothRealForm.pullback hg γ).coeff f z := by
  let d := complexChartAt (n := n) (g (f.val.symm z))
  have hzd : z ∈ coordinateDomain g f d := ⟨hz, mem_complexChartAt_source _⟩
  have hwt : coordinateMap g f d z ∈ d.val.target := coordinateMap_mem_target hzd
  have hterm (j : Fin Q.card) (w : ComplexModel n) (hwt : w ∈ d.val.target) :
      (testExtension (Q.chart j) (η j)).coeff d w =
        Q.weight j (d.val.symm w) • γ.coeff d w := by
    change transportedCoeff (Q.chart j) d (η j) w = _
    by_cases hx : d.val.symm w ∈ (Q.chart j).val.source
    · have ho : w ∈ (chartTransition d (Q.chart j)).source := ⟨hwt, hx⟩
      have ht : chartTransition d (Q.chart j) w ∈ (Q.chart j).val.target :=
        (Q.chart j).val.map_source hx
      have hsame : (Q.chart j).val.symm (chartTransition d (Q.chart j) w) = d.val.symm w :=
        (Q.chart j).val.left_inv hx
      rw [transportedCoeff, indicator_of_mem ho, hη, indicator_of_mem ht, hsame]
      ext v
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.smul_apply]
      rw [γ.compatible d (Q.chart j) w ho v]
      rfl
    · have ho : w ∉ (chartTransition d (Q.chart j)).source := fun h => hx h.2
      have h0 : Q.weight j (d.val.symm w) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (Q.subset j h))
      rw [transportedCoeff, indicator_of_notMem ho, h0, zero_smul]
  have hsum : ∑ j, (testExtension (Q.chart j) (η j)).coeff d (coordinateMap g f d z) =
      γ.coeff d (coordinateMap g f d z) := by
    rw [Finset.sum_congr rfl fun j _ => hterm j _ hwt, ← Finset.sum_smul, Q.sum_eq_one,
      one_smul]
  rw [SmoothRealForm.pullback_coeff hg _ f d hzd, ← hsum]
  rw [Finset.sum_congr rfl fun j _ => SmoothRealForm.pullback_coeff hg _ f d hzd]
  have hlin : ∀ A : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ,
      A.compContinuousLinearMap (fderiv ℝ (coordinateMap g f d) z) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM
          (fderiv ℝ (coordinateMap g f d) z) A := fun _ => rfl
  simp only [hlin, map_sum]

/-- **Duality**: for `Y` compact, `⟨g_* T, γ⟩ = ⟨T, g^* γ⟩` for every smooth form `γ` on `Y`. -/
theorem pairingLM_currentPushforward [CompactSpace Z] [CompactSpace Y]
    (T : GlobalCurrent n Z k)
    (γ : SmoothRealForm n Y (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pairingLM (currentPushforward hg T) γ = pairingLM T (SmoothRealForm.pullback hg γ) := by
  let Q : ChartPartitionOfUnity n Y := ChartPartitionOfUnity.choice
  let P : ChartPartitionOfUnity n Z := ChartPartitionOfUnity.choice
  choose η hη _ using fun j => exists_testForm (Q.chart j) γ (Q.weight j) (Q.smooth j)
    (Q.compact j) (Q.subset j)
  rw [Q.pairingLM_eq_sum _ γ η hη]
  let ξ : ∀ i, LocalCurrents.TestForm (chartTarget (P.chart i))
      (Module.finrank ℝ (ComplexModel n) - k.val) := fun i =>
    ∑ j, pullTestCLM hg (P.chart i) (Q.chart j) (P.smooth i) (P.compact i) (P.subset i) (η j)
  have hξ : ∀ i z, ξ i z = (P.chart i).val.target.indicator (fun y => P.weight i
      ((P.chart i).val.symm y) • (SmoothRealForm.pullback hg γ).coeff (P.chart i) y) z := by
    intro i z
    have hj : ∀ j, pullTestCLM hg (P.chart i) (Q.chart j) (P.smooth i) (P.compact i)
        (P.subset i) (η j) z = (P.chart i).val.target.indicator (fun y => P.weight i
          ((P.chart i).val.symm y) • (SmoothRealForm.pullback hg
            (testExtension (Q.chart j) (η j))).coeff (P.chart i) y) z := fun j =>
      pullTestCLM_apply_eq hg (P.chart i) (Q.chart j) (P.smooth i) (P.compact i)
        (P.subset i) (η j) z
    simp only [ξ]
    rw [sum_apply, Finset.sum_congr rfl fun j _ => hj j]
    by_cases hz : z ∈ (P.chart i).val.target
    · simp only [indicator_of_mem hz]
      rw [← Finset.smul_sum, sum_pullback_testExtension_coeff hg Q γ η hη (P.chart i) hz]
    · simp only [indicator_of_notMem hz, Finset.sum_const_zero]
  rw [P.pairingLM_eq_sum T _ ξ hξ]
  change ∑ j, pushforwardChart hg P T (Q.chart j) (η j) = _
  have h1 : ∀ j, pushforwardChart hg P T (Q.chart j) (η j) = ∑ i, T.inChart (P.chart i)
      (pullTestCLM hg (P.chart i) (Q.chart j) (P.smooth i) (P.compact i) (P.subset i)
        (η j)) := fun j => by
    simp only [pushforwardChart]
    exact sum_apply _ _ _
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
  simp only [ξ, map_sum]

/-- `id_* T = T`. -/
theorem currentPushforward_id [CompactSpace Z] (T : GlobalCurrent n Z k) :
    currentPushforward (g := (id : Z → Z))
      (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)) T = T := by
  apply GlobalCurrent.ext
  intro e η
  rw [currentPushforward_inChart, pairing_eq_of_geometricallyEq T
    (SmoothRealForm.pullback_id_geometricallyEq _), pairing_testExtension]

/-- Functoriality `(g ∘ h)_* T = g_* (h_* T)`. -/
theorem currentPushforward_comp {W : Type*} [TopologicalSpace W]
    [ChartedSpace (ComplexModel n) W] [IsComplexManifold n W] [CompactSpace W] [CompactSpace Z]
    {h : W → Z} (hh : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ h)
    (T : GlobalCurrent n W k) :
    currentPushforward (hg.comp hh) T = currentPushforward hg (currentPushforward hh T) := by
  apply GlobalCurrent.ext
  intro e η
  rw [currentPushforward_inChart, currentPushforward_inChart, pairingLM_currentPushforward,
    pairing_eq_of_geometricallyEq T (SmoothRealForm.pullback_comp_geometricallyEq hg hh _)]

/-- The push-forward commutes with the degree identification `▸` of test degrees. -/
theorem currentPushforward_inChart_cast [CompactSpace Z] (T : GlobalCurrent n Z k)
    (e : ComplexChart n Y) {a : ℕ} (h : Module.finrank ℝ (ComplexModel n) - k.val = a)
    (η : LocalCurrents.TestForm (chartTarget e) a) :
    (currentPushforward hg T).inChart e (h.symm ▸ η) =
      pairingLM T (h.symm ▸ SmoothRealForm.pullback hg (testExtension e η)) := by
  subst h
  exact currentPushforward_inChart hg T e η

theorem pairingLM_cast_congr {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] (T : GlobalCurrent n M k) {a : ℕ}
    (h : Module.finrank ℝ (ComplexModel n) - k.val = a) {γ δ : SmoothRealForm n M a}
    (hγδ : γ.GeometricallyEq δ) : pairingLM T (h.symm ▸ γ) = pairingLM T (h.symm ▸ δ) := by
  subst h
  exact pairing_eq_of_geometricallyEq T hγδ

/-- **The push-forward of a closed current is closed.** In every chart of `Y`,
`(g_* T)(dτ) = ⟨T, g^* d(τ extended by zero)⟩ = ⟨T, d g^*(τ extended by zero)⟩ = 0` by Stokes on the
compact manifold `Z`. -/
theorem isClosed_currentPushforward [CompactSpace Z]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {T : GlobalCurrent n Z k} (hT : T.IsClosed b) : (currentPushforward hg T).IsClosed b := by
  by_cases hk : k.val = Module.finrank ℝ (ComplexModel n)
  · exact Pending.NaturalNativeCurrentCoefficientDifferential.isClosed_topDegree b hk _
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, Module.finrank ℝ (ComplexModel n) - k.val = q + 1 :=
      ⟨Module.finrank ℝ (ComplexModel n) - k.val - 1, by omega⟩
    have hq' : q + 1 ≤ Module.finrank ℝ (ComplexModel n) := by omega
    have hkeq : k = Pending.NaturalFullCurrentTranspose.complementDegree n (q + 1) hq' := by
      apply Fin.ext
      simp only [Pending.NaturalFullCurrentTranspose.complementDegree]
      omega
    subst hkeq
    rw [Pending.NaturalClosedCurrentStokes.isClosed_iff_native_chart_exterior_eq_zero b q hq']
    intro e τ
    have hcast : ∀ {a : ℕ} (h : Module.finrank ℝ (ComplexModel n) -
        (Pending.NaturalFullCurrentTranspose.complementDegree n (q + 1) hq').val = a)
        (S : GlobalCurrent n Y
          (Pending.NaturalFullCurrentTranspose.complementDegree n (q + 1) hq'))
        (ξ : LocalCurrents.TestForm (chartTarget e) a),
        Pending.NaturalNativeCurrentDifferentials.nativeChartFunctional h S e ξ =
          S.inChart e (h.symm ▸ ξ) := by
      intro a h
      subst h
      intro S ξ
      rfl
    rw [hcast, currentPushforward_inChart_cast hg T e
      (Pending.NaturalFullCurrentTranspose.complementDegree_complement n (q + 1) hq')]
    have hgeom : (SmoothRealForm.pullback hg
        (testExtension e (Pending.CompactDifferentialTests.exteriorTestCLM τ))).GeometricallyEq
        (SmoothRealForm.pullback hg (testExtension e τ)).exteriorDerivative :=
      (SmoothRealForm.GeometricallyEq.pullback hg
        (Pending.NaturalChartExtensionDifferentials.exterior_testExtension_geometricallyEq
          e τ).symm).trans (SmoothRealForm.exteriorDerivative_pullback hg _).symm
    rw [pairingLM_cast_congr T
      (Pending.NaturalFullCurrentTranspose.complementDegree_complement n (q + 1) hq') hgeom]
    exact Pending.NaturalClosedCurrentStokes.pairing_exteriorDerivative_eq_zero_of_isClosed b T
      (Pending.NaturalFullCurrentTranspose.complementDegree_complement n (q + 1) hq') hT _

end SGPT.BDivisor
