import SGPT.Foundations.Analysis.Pending.XiaoLocalTestHolder
import SGPT.Foundations.Analysis.Pending.XiaoPoissonTraceTranspose
import SGPT.Foundations.Analysis.Pending.ClosedTopCurrents

set_option autoImplicit false

/-! # Actual ordinary coordinate distributions of the continuous Poisson transpose -/

open Set Filter Function MeasureTheory TopologicalSpace
open scoped Topology ContDiff NNReal Distributions

namespace SGPT.Foundations.Analysis.Pending.XiaoPoissonLocalDistribution

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ChartPartition HolderAtlas.HolderMap
  SmoothCurrentClosedness ClosedTopCurrents XiaoLocalTestHolder XiaoPoissonTraceTranspose
  PositiveProductCurrents ProductTestForms TopBidimensionCurrents XiaoComplexDifferential
  XiaoPositiveGauduchonExtension IntegrationCurrent

noncomputable section

section Multiplier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens E}

/-- Multiplication of an actual test by an actual multiplier smooth on its open domain. -/
def smoothLocalTestMultiplier (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g Ω)
    (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨fun x => φ x * g x,
    contDiff_mul_of_tsupport_subset Ω.isOpen φ.contDiff φ.tsupport_subset hg,
    φ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans φ.tsupport_subset⟩

@[simp] theorem smoothLocalTestMultiplier_apply (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g Ω)
    (φ : 𝓓(Ω, ℝ)) (x : E) : smoothLocalTestMultiplier g hg φ x = φ x * g x := rfl

/-- The genuine smooth local multiplier preserves the actual test's support. -/
theorem tsupport_smoothLocalTestMultiplier_subset (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g Ω)
    (φ : 𝓓(Ω, ℝ)) : tsupport (smoothLocalTestMultiplier g hg φ) ⊆ tsupport φ :=
  tsupport_mul_subset_left

variable [FiniteDimensional ℝ E]

/-- The smooth local multiplier is continuous for the genuine test-function LF topology. -/
def smoothLocalTestMultiplierCLM (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g Ω) :
    𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) := by
  refine TestFunction.mkCLM ℝ (smoothLocalTestMultiplier g hg) ?_ ?_ ?_
  · intro φ ψ
    ext x
    change (φ x + ψ x) * g x = φ x * g x + ψ x * g x
    exact add_mul _ _ _
  · intro c φ
    ext x
    change (c * φ x) * g x = c * (φ x * g x)
    exact mul_assoc _ _ _
  · intro K hK
    obtain ⟨β, hβ, hβc, hβΩ, hβ1⟩ :=
      exists_contDiff_eq_one_of_isCompact K.isCompact Ω.isOpen hK
    have hβg : ContDiff ℝ ∞ (fun x => β x * g x) :=
      contDiff_mul_of_tsupport_subset Ω.isOpen hβ hβΩ hg
    let L := (TestFunction.ofSupportedInCLM ℝ hK).comp
      (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hβg)
    refine L.continuous.congr ?_
    intro φ
    ext x
    change φ x * (β x * g x) = φ x * g x
    by_cases hxK : x ∈ K
    · rw [hβ1 x hxK, one_mul]
    · rw [φ.zero_on_compl hxK]
      simp only [Pi.zero_apply, zero_mul]

@[simp] theorem smoothLocalTestMultiplierCLM_apply (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g Ω)
    (φ : 𝓓(Ω, ℝ)) (x : E) : smoothLocalTestMultiplierCLM g hg φ x = φ x * g x := rfl

end Multiplier

section CoordinateDistribution

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] {r : ℝ≥0}

/-- The actual reciprocal Kähler coordinate density is smooth on the chart target. -/
theorem contDiffOn_inv_volDensity (w : KahlerBackground (m + 1) M)
    (e : ComplexChart (m + 1) M) :
    ContDiffOn ℝ ∞ (fun z => (volDensity w e z)⁻¹) (chartTarget e) :=
  (contDiffOn_volDensity w e).inv fun _ hz => (volDensity_pos w e hz).ne'

/-- A genuine ordinary coordinate test, divided by the actual volume density, as a global input. -/
def volumeNormalizedTestCLM (w : KahlerBackground (m + 1) M) (A : HolderAtlas (m + 1) M)
    (hr : r ≤ 1) (e : ComplexChart (m + 1) M) :
    𝓓(chartTarget e, ℝ) →L[ℝ] A.HolderMap 0 r ℝ :=
  (localTestHolderCLM A hr e).comp
    (smoothLocalTestMultiplierCLM (fun z => (volDensity w e z)⁻¹) (contDiffOn_inv_volDensity w e))

@[simp] theorem volumeNormalizedTestCLM_apply (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (e : ComplexChart (m + 1) M)
    (φ : 𝓓(chartTarget e, ℝ)) (x : M) :
    volumeNormalizedTestCLM w A hr e φ x =
      chartExtend e (fun z => φ z / volDensity w e z) x := by
  rw [volumeNormalizedTestCLM, ContinuousLinearMap.comp_apply, localTestHolderCLM_apply]
  rfl

/-- The actual normalized input agrees pointwise with division by the chart volume density. -/
theorem volumeNormalizedTestCLM_apply_of_mem (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (e : ComplexChart (m + 1) M)
    (φ : 𝓓(chartTarget e, ℝ)) {x : M} (hx : x ∈ e.val.source) :
    volumeNormalizedTestCLM w A hr e φ x = φ (e.val x) / volDensity w e (e.val x) := by
  rw [volumeNormalizedTestCLM_apply, chartExtend_of_mem hx]

/-- The actual normalized input vanishes off the actual chart source. -/
theorem volumeNormalizedTestCLM_apply_of_notMem (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (e : ComplexChart (m + 1) M)
    (φ : 𝓓(chartTarget e, ℝ)) {x : M} (hx : x ∉ e.val.source) :
    volumeNormalizedTestCLM w A hr e φ x = 0 := by
  rw [volumeNormalizedTestCLM_apply, chartExtend_of_notMem hx]

/-- Any actual continuous global functional gives an ordinary coordinate distribution. -/
def coordinateDistribution (w : KahlerBackground (m + 1) M) (A : HolderAtlas (m + 1) M)
    (hr : r ≤ 1) (Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ) (e : ComplexChart (m + 1) M) :
    𝓓'(chartTarget e, ℝ) := Ψ.comp (volumeNormalizedTestCLM w A hr e)

@[simp] theorem coordinateDistribution_apply (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr : r ≤ 1) (Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ)
    (e : ComplexChart (m + 1) M) (φ : 𝓓(chartTarget e, ℝ)) :
    coordinateDistribution w A hr Ψ e φ = Ψ (volumeNormalizedTestCLM w A hr e φ) := rfl

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

/-- Actual ordinary coordinate distributions of the genuine Poisson transpose. -/
def poissonCoordinateDistribution (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr0 : 0 < r) (hr1 : r < 1)
    (T : ProductCurrent (m + 1) M m) (hT : IsPositive T) (θ : SmoothRealForm (m + 1) M 2)
    (e : ComplexChart (m + 1) M) : 𝓓'(chartTarget e, ℝ) :=
  coordinateDistribution w A hr1.le (poissonTraceTransposeCLM w A hr0 hr1 T hT θ) e

@[simp] theorem poissonCoordinateDistribution_apply (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr0 : 0 < r) (hr1 : r < 1)
    (T : ProductCurrent (m + 1) M m) (hT : IsPositive T) (θ : SmoothRealForm (m + 1) M 2)
    (e : ComplexChart (m + 1) M) (φ : 𝓓(chartTarget e, ℝ)) :
    poissonCoordinateDistribution w A hr0 hr1 T hT θ e φ =
      poissonTraceTransposeCLM w A hr0 hr1 T hT θ (volumeNormalizedTestCLM w A hr1.le e φ) := rfl

/-- The genuine gap produces an actual positive current, global transpose, and local distributions. -/
theorem exists_gap_positive_current_local_distributions (w B : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr0 : 0 < r) (hr1 : r < 1)
    (hM : 0 < NefMixedMass.slotIntegral w (Fin.cons B.form (fun _ : Fin m => w.form)))
    (hgap : 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral w
      (Fin.cons B.form (fun _ : Fin m => w.form)) < (kahlerVolume w).real univ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ T : ProductCurrent (m + 1) M m, IsPositive T ∧
        ∃ Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ,
          ∃ U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ),
            (∀ e φ, U e φ = Ψ (volumeNormalizedTestCLM w A hr1.le e φ)) ∧
              ∀ G : testSpace (m + 1) M m,
                Ψ (ofChartSmooth (A := A) (k := 0) hr1.le
                  (topRatio w.form.val (ddc (G : SmoothRealForm (m + 1) M (2 * m))))
                  (chartSmooth_topRatio w.isKahler.1 _)) =
                    T G - smoothTestPairing w ((1 - δ) • w.form.val - B.form.val) G := by
  obtain ⟨δ, hδ0, hδ1, T, hT, Ψ, hΨ⟩ :=
    exists_gap_positive_current_continuous_transpose w B A hr0 hr1 hM hgap
  exact ⟨δ, hδ0, hδ1, T, hT, Ψ, coordinateDistribution w A hr1.le Ψ,
    fun _ _ => rfl, hΨ⟩

end CoordinateDistribution

end

end SGPT.Foundations.Analysis.Pending.XiaoPoissonLocalDistribution
