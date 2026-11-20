import SGPT.Okounkov.EffectiveDivisorCurrentCompatibility
import SGPT.Okounkov.EffectiveDivisorMetricGeneric
import SGPT.Okounkov.ThetaPotentialCurrentReader
import SGPT.PSH.LocalIntegralGeometricQDivisor
import SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation
import SGPT.Foundations.Analysis.Pending.ActualDivisorCurrentMetricIndependence
import SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration

/-!
# Closed positive currents, their Lelong numbers, and currents of prime divisors

Source: the chapter *Plurisubharmonic functions* of the book, section *The space of currents*
(`def:spaceofcurrents`, `ex:Lelongcurrent`, `def:pshfunctions:L1101` for currents, and the
current of integration `[E]` of `lma:Siudec`).  Throughout `M` is a complex manifold of dimension
`m + 1` (compact where the current of a divisor is needed: its smooth metric is produced by a
partition of unity).

* `IsClosedPositiveCurrent T`: `T` is a closed positive `(1,1)`-current (`𝒵₊(X)`), i.e. a global
  degree-two current which is closed, of type `(1,1)` and positive on every strongly positive test
  form in every chart.
* `currentLelong T hT x`: the Lelong number `ν(T, x)` of `ex:Lelongcurrent`, in the book's
  normalization `ν(log |z|², 0) = 1`: the unique function which, at every point and in every chart,
  is the Lelong number of every local plurisubharmonic potential of `T`.  For `T = θ + ddᶜφ` it is
  `ν(φ, x)` (`currentLelong_eq_of_eq_thetaPotentialCurrent`).
* `currentGenericLelong T hT D`: the generic Lelong number `ν(T, D) = inf_{x ∈ D} ν(T, x)` along a
  prime divisor `D` (an irreducible analytic hypersurface, `SGPT.PSH.GeometricPrimeCarrier`).
* `primeDivisorCurrent D`: the current of integration `[D]`, defined as `Θ + ddᶜ log |s|²_h` for a
  smooth metric `h` on `𝒪(D)` (Lelong–Poincaré); it does not depend on the metric
  (`primeDivisorCurrent_eq_of_isDivisorMetric`), and locally it is `ddᶜ log |f|²` for a reduced
  local equation `f` of `D`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent LelongPoincareDivisor
open SquaredLogLelongSourceNormalization

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- **Closed positive `(1,1)`-currents** (`def:spaceofcurrents`, item 1: the elements of
`𝒵₊(X)`): global degree-two currents which are closed, of type `(1,1)`, and nonnegative on every
strongly positive test form in every chart. -/
def IsClosedPositiveCurrent (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) : Prop :=
  T.IsClosed (canonicalBasis (m + 1)) ∧
    T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive T

/-- The current `θ + ddᶜφ` of a `θ`-psh potential is a closed positive current. -/
theorem isClosedPositiveCurrent_thetaPotentialCurrent (θ : SmoothRealForm (m + 1) M 2)
    (φ : M → EReal) (hφ : IsThetaPshPotential θ φ) :
    IsClosedPositiveCurrent (thetaPotentialCurrent θ φ hφ) :=
  NaturalThetaPshClosedCurrent.thetaPotentialCurrent_closed_type_positive θ φ hφ

set_option linter.style.longLine false in
/-- On a compact manifold every closed positive current is `θ + ddᶜφ` for a closed smooth real
`(1,1)`-form `θ` and a `θ`-psh potential `φ`. -/
theorem IsClosedPositiveCurrent.exists_thetaPotential [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T) :
    ∃ (σ : ClosedRealOneOneForm (m + 1) M) (φ : M → EReal) (hφ : IsThetaPshPotential σ.val φ),
      T = thetaPotentialCurrent σ.val φ hφ := by
  obtain ⟨σ, φ, hφ, heq, -⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T hT.1 hT.2.1 hT.2.2
  exact ⟨σ, φ, hφ, heq⟩

/-! ### Lelong numbers of a closed positive current -/

/-- **The Lelong number `ν(T, x)` of a closed positive current** (`ex:Lelongcurrent`,
`eq:convnuTx`), in the book's normalization: the unique function on `M` which, in every chart and
at every point, equals the (squared-logarithm normalized) Lelong number of every local
plurisubharmonic potential of `T`. -/
def currentLelong (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsClosedPositiveCurrent T) : M → ℝ≥0∞ :=
  Classical.choose
    (SGPT.Okounkov.exists_unique_original_full_positive_current_source_reader T hT.1 hT.2.1 hT.2.2)

theorem isOriginalCurrentSourceReader_currentLelong
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) (hT : IsClosedPositiveCurrent T) :
    SGPT.Okounkov.IsOriginalCurrentSourceReader T (currentLelong T hT) :=
  (Classical.choose_spec
    (SGPT.Okounkov.exists_unique_original_full_positive_current_source_reader
      T hT.1 hT.2.1 hT.2.2)).1

/-- For `T = θ + ddᶜφ`, `ν(T, x) = ν(φ, x)` (`eq:convnuTx`). -/
theorem currentLelong_eq_of_eq_thetaPotentialCurrent
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    {θ : SmoothRealForm (m + 1) M 2} {φ : M → EReal} {hφ : IsThetaPshPotential θ φ}
    (heq : T = thetaPotentialCurrent θ φ hφ) :
    currentLelong T hT = fun x => squaredLogLelongNumber (n := m + 1) φ x := by
  have hμ := isOriginalCurrentSourceReader_currentLelong T hT
  set μ := currentLelong T hT with hμdef
  clear_value μ
  subst heq
  exact SGPT.Okounkov.original_current_source_reader_eq_theta_potential hφ hμ

/-- The Lelong numbers of a closed positive current are finite. -/
theorem currentLelong_ne_top [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (x : M) : currentLelong T hT x ≠ ⊤ := by
  obtain ⟨σ, φ, hφ, heq⟩ := hT.exists_thetaPotential
  rw [currentLelong_eq_of_eq_thetaPotentialCurrent hT heq]
  intro htop
  have htop' : squaredLogLelongNumber (n := m + 1) φ x = ⊤ := htop
  have hfin := LelongNumberFiniteness.lelongNumber_ne_top_of_quasiPsh (Nat.succ_pos m)
    hφ.1.quasiPlurisubharmonic hφ.2 x
  apply hfin
  rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m), htop']
  simp

/-- **The generic Lelong number `ν(T, D)` of a closed positive current along a prime divisor**
(`def:pshfunctions:L1101` via `rmk:qpshtocurrents`): `ν(T, D) = inf_{x ∈ D} ν(T, x)`. -/
def currentGenericLelong (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsClosedPositiveCurrent T) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) : ℝ≥0∞ :=
  ⨅ x ∈ D.val, currentLelong T hT x

theorem currentGenericLelong_le
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) {x : M} (hx : x ∈ D.val) :
    currentGenericLelong T hT D ≤ currentLelong T hT x :=
  iInf₂_le x hx

theorem currentGenericLelong_ne_top [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) : currentGenericLelong T hT D ≠ ⊤ := by
  obtain ⟨x, hx⟩ := D.nonempty
  exact ne_top_of_le_ne_top (currentLelong_ne_top hT x) (currentGenericLelong_le hT D hx)

/-! ### The current of integration of a prime divisor -/

/-- The effective divisor of a prime divisor `D`: its reduced (vanishing) ideal sheaf. -/
abbrev primeEffectiveDivisor (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    EffectiveDivisor (m + 1) M :=
  SGPT.PSH.geometricPrimeCarrierEffectiveDivisor D

/-- **The current of integration `[D]` of a prime divisor** (the current `[E]` of `lma:Siudec`):
`Θ_h + ddᶜ log |s_D|²_h` for a smooth metric `h` on `𝒪(D)`, i.e. locally `ddᶜ log |f|²` for a
reduced local equation `f` of `D` (Lelong–Poincaré).  The metric is chosen; the current does not
depend on it (`primeDivisorCurrent_eq_of_isDivisorMetric`). -/
def primeDivisorCurrent [CompactSpace M] (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)) :=
  integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
    (Classical.choose (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D)))

theorem isDivisorMetric_primeDivisorCurrent_metric [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D)
      (Classical.choose (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))) :=
  (Classical.choose_spec (DivisorMetric.exists_divisorMetric (primeEffectiveDivisor D))).2

/-- `[D]` does not depend on the smooth metric of `𝒪(D)`. -/
theorem primeDivisorCurrent_eq_of_isDivisorMetric [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hE : DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D) E) :
    primeDivisorCurrent D = integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E :=
  ActualDivisorCurrentMetricIndependence.integrationCurrent_eq_of_isDivisorMetric
    (canonicalBasis (m + 1)) (primeEffectiveDivisor D) _ E
    (isDivisorMetric_primeDivisorCurrent_metric D) hE

/-- `[D] = Θ_h + ddᶜ ψ_h` for every smooth metric `h` on `𝒪(D)`, `ψ_h = log |s_D|²_h`. -/
theorem primeDivisorCurrent_eq_thetaPotentialCurrent [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hE : DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D) E) :
    primeDivisorCurrent D = thetaPotentialCurrent E.curvature.val E.weight
      (SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ E hE) :=
  (primeDivisorCurrent_eq_of_isDivisorMetric D E hE).trans
    (SGPT.Okounkov.thetaPotentialCurrent_effectiveDivisorMetric_eq _ E hE).symm

/-- `[D]` is a closed positive `(1,1)`-current. -/
theorem isClosedPositiveCurrent_primeDivisorCurrent [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    IsClosedPositiveCurrent (primeDivisorCurrent D) := by
  rw [primeDivisorCurrent_eq_thetaPotentialCurrent D _
    (isDivisorMetric_primeDivisorCurrent_metric D)]
  exact isClosedPositiveCurrent_thetaPotentialCurrent _ _ _

/-- **`[D]` is the current of integration over `D`** (Lelong–Poincaré).  On the chart domain of
every local presentation `ψ = Σ aᵢ log |gᵢ|² + h` of the weight of a smooth metric on `𝒪(D)`,
the coefficients of `[D]` are `Σ aᵢ [div gᵢ]`, where `[div g]` is integration over the regular
part of `{g = 0}` against the `(2n-2)`-dimensional Hausdorff measure, with multiplicities
(`DivisorIntegrationCurrent.divisorCurrent`). -/
theorem primeDivisorCurrent_restrict_eq_sum_divisorCurrent [CompactSpace M]
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) (E : MeteredEffectiveQDivisor (m + 1) M)
    (hE : DivisorMetric.IsDivisorMetric (primeEffectiveDivisor D) E)
    (P : LocalPresentation E) (e : ComplexChart (m + 1) M) :
    restrictForm ((primeDivisorCurrent D).coefficients (canonicalBasis (m + 1)) e)
        (P.chartDomain_le e) =
      ∑ i, (P.a i : ℝ) •
        DivisorIntegrationCurrent.divisorCurrent (P.differentiableOn_chartG e i)
          (P.frequently_chartG_ne e i) := by
  rw [primeDivisorCurrent_eq_of_isDivisorMetric D E hE,
    (lelongPoincare (canonicalBasis (m + 1)) (Nat.succ_pos m) E).2.2.2.2.2 P e,
    ActualCanonicalComplementaryCurrentCalibration.haarFactor_canonicalBasis]
  simp

end SGPT.Siu
