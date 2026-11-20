import SGPT.Foundations.Analysis.Pending.SingularModelEnergySignedFibreIdentification

set_option autoImplicit false

/-!
# Actual finite signed fibre sum represents the defining model energy

Xia SGPT PDF0171's actual representative in (4.29)--(4.30).
Natural chart data comprise genuine joint PSH and Borel potentials,
their actual base/time coordinate expressions, genuine smooth PSD
regularizer slots and actual integrability against the two canonical
regularizer NP measures. No fibre identity, weighted-integrability
conclusion, final energy pairing or affinity is a field.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyFibrePairing

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses GlobalSlotStokes FiniteGeodesicStripCharts
  BedfordTaylorStripCovariance BedfordTaylorFibreSlicing BedfordTaylorTimeSlot BedfordTaylorStripIBP
  MixedDensityRankOneSlot BedfordTaylor MixedNonPluripolar
  NonPluripolarTimeSlotTruncationBalance SingularModelEnergyChartIntegrals
  SingularModelEnergySignedFibreIdentification

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}

/-- Natural actual joint/chart and canonical regularizer data; none of its fields is a fibre-energy or final pairing conclusion. -/
structure SignedChartData (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (U : ℂ → M → EReal) (S : Set ℂ) (hS : IsOpen S)
    (J : SlotChart (fun _ : Fin n => θ) θ) (f : M → ℝ) (ψ ζ : ℂ → ℝ) where
  H : ComplexModel (n + 1) → EReal
  Φ : ComplexModel (n + 1) → EReal
  hH : PlurisubharmonicOn H (stripLift J.domain S hS)
  hΦ : PlurisubharmonicOn Φ (stripLift J.domain S hS)
  hHm : Measurable H
  hΦm : Measurable Φ
  c : ℂ → ℝ
  hHcoord : ∀ τ ∈ S, ∀ y ∈ J.domain, H (fibreMap n τ y) =
    chartFunction (U τ) J.chart y + (J.kahler y : EReal) + (c τ : EReal)
  hΦcoord : ∀ τ ∈ S, ∀ y ∈ J.domain, Φ (fibreMap n τ y) =
    chartFunction φ J.chart y + (J.kahler y : EReal) + (c τ : EReal)
  p : Fin (n + 1) → ComplexModel (n + 1) → ℝ
  hp : ∀ k, IsSmoothPsdOn (stripLift J.domain S hS) (p k)
  hψp : ∀ k, IsSmoothPsdOn (stripLift J.domain S hS) fun q => timeLift n ψ q + p k q
  ha : ∀ k, Integrable (fun q => stripCutoff (chartRead J.chart f) ζ q *
      canonicalERealDiffToReal (H q) (Φ q))
    (mixedTruncationLimitMeasure (stripLift J.domain S hS)
      (Function.update (endpointTimeTuple H Φ k) (Fin.last n)
        fun q => ((timeLift n ψ q + p k q : ℝ) : EReal))
      (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hΦ k) (hψp k)))
  hb : ∀ k, Integrable (fun q => stripCutoff (chartRead J.chart f) ζ q *
      canonicalERealDiffToReal (H q) (Φ q))
    (mixedTruncationLimitMeasure (stripLift J.domain S hS)
      (Function.update (endpointTimeTuple H Φ k) (Fin.last n) fun q => (p k q : EReal))
      (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hΦ k) (hp k)))

/-- The actual difference of the two canonical regularizer NP integrals on one chart-slot. -/
def SignedChartData.defect {U : ℂ → M → EReal} {S : Set ℂ} {hS : IsOpen S}
    {J : SlotChart (fun _ : Fin n => θ) θ} {f : M → ℝ} {ψ ζ : ℂ → ℝ}
    (d : SignedChartData θ φ U S hS J f ψ ζ) (k : Fin (n + 1)) : ℝ :=
  (∫ q, stripCutoff (chartRead J.chart f) ζ q * canonicalERealDiffToReal (d.H q) (d.Φ q)
    ∂mixedTruncationLimitMeasure (stripLift J.domain S hS)
      (Function.update (endpointTimeTuple d.H d.Φ k) (Fin.last n)
        fun q => ((timeLift n ψ q + d.p k q : ℝ) : EReal))
      (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn d.hH d.hΦ k) (d.hψp k))) -
  (∫ q, stripCutoff (chartRead J.chart f) ζ q * canonicalERealDiffToReal (d.H q) (d.Φ q)
    ∂mixedTruncationLimitMeasure (stripLift J.domain S hS)
      (Function.update (endpointTimeTuple d.H d.Φ k) (Fin.last n) fun q => (d.p k q : EReal))
      (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn d.hH d.hΦ k) (d.hp k)))

/-- The genuine finite real defining model-energy family, extended by zero outside the actual time domain. -/
def modelEnergyCurve (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (U : ℂ → M → EReal) (S : Set ℂ) (τ : ℂ) : ℝ := by
  classical
  exact if τ ∈ S then (energy θ φ hφ (U τ)).toReal else 0

variable [ConnectedSpace M] {hφ : IsModelPotential θ φ}

/-- Genuine E1 slice membership and an actual finite base partition identify the pointwise endpoint-curve sum with the defining real model energy. -/
theorem sum_sum_endpointCurveTerm_eq_mul_modelEnergyCurve (omega : KahlerBackground n M)
    (U : ℂ → M → EReal) (S : Set ℂ)
    (hU : ∀ τ ∈ S, RelativeFiniteEnergyPreceq θ φ (U τ) hφ) {m : ℕ}
    (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (fun _ : Fin n => θ) θ)
    (hχs : ∀ a, ChartSmooth (n := n) (χ a)) (hχ0 : ∀ a x, 0 ≤ χ a x)
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M))
    (hχ1 : ∀ x, ∑ a, χ a x = 1) (τ : ℂ) :
    (∑ k : Fin (n + 1), ∑ a : Fin m, endpointCurveTerm θ φ U S hφ.plurisubharmonic
      (fun z hz => (hU z hz).1.plurisubharmonic) (χ a) k τ) =
      ((n : ℝ) + 1) * modelEnergyCurve θ φ hφ U S τ := by
  classical
  by_cases hτ : τ ∈ S
  · have h := sum_sum_chart_endpoint_eq_mul_toReal_energy omega (hU τ hτ) χ J hχs hχ0 hχJ hχ1
    simp_rw [integral_chart_endpoint_eq_global hφ.plurisubharmonic (hU τ hτ).1.plurisubharmonic
      _ _ (hχJ _)] at h
    simpa only [endpointCurveTerm, modelEnergyCurve, dif_pos hτ, if_pos hτ] using h
  · simp only [endpointCurveTerm, modelEnergyCurve, dif_neg hτ, if_neg hτ,
      Finset.sum_const_zero, mul_zero]

/-- Actual joint PSH/coordinate data and natural canonical regularizer integrability produce genuine integrability of the defining energy test and the complete finite signed fibre-energy pairing. -/
theorem integrable_and_sum_defect_eq_model_energy_pairing (omega : KahlerBackground n M)
    (U : ℂ → M → EReal) (S : Set ℂ) (hS : IsOpen S)
    (hU : ∀ τ ∈ S, RelativeFiniteEnergyPreceq θ φ (U τ) hφ) {m : ℕ}
    (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (fun _ : Fin n => θ) θ)
    (hχs : ∀ a, ChartSmooth (n := n) (χ a)) (hχ0 : ∀ a x, 0 ≤ χ a x)
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M))
    (hχc : ∀ a, HasCompactSupport (χ a)) (hχ1 : ∀ x, ∑ a, χ a x = 1)
    {ζ ψ : ℂ → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (hζS : tsupport ζ ⊆ S) (hζ0 : ∀ τ, 0 ≤ ζ τ)
    (hψ : ContDiff ℝ ∞ ψ) (hψS : tsupport ψ ⊆ S)
    (hζψ : ∀ τ ∈ tsupport ψ, ζ τ = 1)
    (d : ∀ a, SignedChartData θ φ U S hS (J a) (χ a) ψ ζ) :
    Integrable (fun τ : ℂ => timeLaplacian ψ τ * modelEnergyCurve θ φ hφ U S τ) ∧
    (∑ k : Fin (n + 1), ∑ a : Fin m, (d a).defect k) =
      (((n : ℝ) + 1) / Real.pi) *
        ∫ τ : ℂ, timeLaplacian ψ τ * modelEnergyCurve θ φ hφ U S τ := by
  classical
  let hpsh : ∀ τ ∈ S, IsThetaPshPotential θ.val (U τ) :=
    fun τ hτ => (hU τ hτ).1.plurisubharmonic
  let F : Fin (n + 1) → Fin m → ℂ → ℝ := fun k a τ =>
    timeLaplacian ψ τ * ζ τ * endpointCurveTerm θ φ U S hφ.plurisubharmonic hpsh (χ a) k τ
  have hslot (k : Fin (n + 1)) (a : Fin m) :
      Integrable (F k a) ∧ (d a).defect k = (∫ τ : ℂ, F k a τ) / Real.pi := by
    exact integral_timeLift_sub_eq_global_endpoint_pairing hφ.plurisubharmonic (J a) hS U hpsh
      (d a).hH (d a).hΦ (d a).hHm (d a).hΦm (d a).c (d a).hHcoord (d a).hΦcoord
      k (hχs a) (hχc a) (hχJ a) (hχ0 a) hζ hζc hζS hζ0 hψ
      ((d a).hp k) ((d a).hψp k) ((d a).ha k) ((d a).hb k)
  have hpoint (τ : ℂ) : (∑ k : Fin (n + 1), ∑ a : Fin m, F k a τ) =
      ((n : ℝ) + 1) * (timeLaplacian ψ τ * modelEnergyCurve θ φ hφ U S τ) := by
    dsimp only [F]
    simp_rw [← Finset.mul_sum]
    rw [sum_sum_endpointCurveTerm_eq_mul_modelEnergyCurve omega U S hU χ J hχs hχ0 hχJ hχ1 τ]
    by_cases hτ : τ ∈ S
    · by_cases hc : timeLaplacian ψ τ = 0
      · simp only [hc, zero_mul, mul_zero]
      · have htest : τ ∈ tsupport ψ := by
          by_contra ht
          exact hc (timeLaplacian_eq_zero_of_notMem_tsupport ht)
        rw [hζψ τ htest]
        ring
    · have htest : τ ∉ tsupport ψ := fun ht => hτ (hψS ht)
      rw [timeLaplacian_eq_zero_of_notMem_tsupport htest]
      simp only [zero_mul, mul_zero]
  have hsum : Integrable (fun τ : ℂ => ∑ k : Fin (n + 1), ∑ a : Fin m, F k a τ) :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun a _ => (hslot k a).1))
  have htimes : Integrable (fun τ : ℂ => ((n : ℝ) + 1) *
      (timeLaplacian ψ τ * modelEnergyCurve θ φ hφ U S τ)) :=
    hsum.congr (Eventually.of_forall hpoint)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hint : Integrable (fun τ : ℂ => timeLaplacian ψ τ * modelEnergyCurve θ φ hφ U S τ) :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hn) _).mp htimes
  refine ⟨hint, ?_⟩
  have hsumI : (∫ τ : ℂ, ∑ k : Fin (n + 1), ∑ a : Fin m, F k a τ) =
      ∑ k : Fin (n + 1), ∑ a : Fin m, ∫ τ : ℂ, F k a τ := by
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun a _ => (hslot k a).1))]
    exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ (fun a _ => (hslot k a).1)
  calc
    (∑ k : Fin (n + 1), ∑ a : Fin m, (d a).defect k) =
        ∑ k : Fin (n + 1), ∑ a : Fin m, (∫ τ : ℂ, F k a τ) / Real.pi :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => (hslot k a).2
    _ = (∑ k : Fin (n + 1), ∑ a : Fin m, ∫ τ : ℂ, F k a τ) / Real.pi := by
      simp_rw [Finset.sum_div]
    _ = (∫ τ : ℂ, ∑ k : Fin (n + 1), ∑ a : Fin m, F k a τ) / Real.pi := by rw [hsumI]
    _ = (((n : ℝ) + 1) * ∫ τ : ℂ,
        timeLaplacian ψ τ * modelEnergyCurve θ φ hφ U S τ) / Real.pi := by
      simp_rw [hpoint]
      rw [integral_const_mul]
    _ = _ := by ring

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyFibrePairing
