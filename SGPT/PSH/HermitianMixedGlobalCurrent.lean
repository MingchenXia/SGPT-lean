import SGPT.PSH.HermitianGlobalCurrents
import SGPT.PSH.HermitianProductFactors
import SGPT.Foundations.Analysis.Pending.ActualGlobalBidimensionOneDdc

/-!
# Actual partitioned global Hermitian mixed currents and their derivatives

The background supplies its own finite correction patches and smooth partition.
Every original bounded Hermitian tuple supplies positive local mixed currents.
Their supported finite sum is an actual globally compatible native current,
and its normalized second transpose is a genuine globally compatible top
current. No local positivity, partition, or global-current certificate is an
input. Identifying the sum with the local products requires their separate
holomorphic compatibility theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorCollar
  ActualBorelWeightedPatchGlobalCurrent ActualGlobalBidimensionOneDdc
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

namespace BackgroundPatch

variable {omega : Background (m + 1) M}

/-- The same actual mixed expansion, at its genuine bidimension-one degree. -/
def bidimensionOneCurrent (P : BackgroundPatch omega) (u : Fin m → M → EReal) :
    LocalProductCurrent (m + 1) P.geometry.domain 1 :=
  castLPC (by omega : m + 1 - m = 1) (P.mixedCurrent m (by omega) u)

/-- Positivity is internally produced from original bounded class members. -/
theorem bidimensionOneCurrent_isPositive (P : BackgroundPatch omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    IsPositive (P.bidimensionOneCurrent u) :=
  isPositive_castLPC _ (P.mixedCurrent_isPositive m (by omega) u hu hb)

end BackgroundPatch

/-- Ordinary finite correction and smooth partition data, chosen from the
background independently of every potential and Borel weight. -/
structure MixedCurrentPartition (omega : Background (m + 1) M) where
  count : ℕ
  patch : Fin count → BackgroundPatch omega
  weight : Fin count → M → ℝ
  smooth : ∀ j, ChartSmooth (n := m + 1) (weight j)
  nonneg : ∀ j x, 0 ≤ weight j x
  supported : ∀ j, tsupport (weight j) ⊆ (patch j).geometry.source
  sum_one : ∀ x, ∑ j, weight j x = 1

/-- The compact Hermitian manifold internally supplies all correction
patches and a subordinate smooth partition, including on the empty space. -/
theorem nonempty_mixedCurrentPartition [CompactSpace M]
    (omega : Background (m + 1) M) : Nonempty (MixedCurrentPartition omega) := by
  obtain ⟨C⟩ := nonempty_backgroundFiniteCover omega
  obtain ⟨k, χ, idx, hχ, hnonneg, hsupp, _hc, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := m + 1)
      (fun i => (C.patch i).geometry.source) C.covers
  exact ⟨⟨k, fun j => C.patch (idx j), χ, hχ, hnonneg, hsupp, hsum⟩⟩

variable [MeasurableSpace M] [BorelSpace M]

namespace MixedCurrentPartition

variable {omega : Background (m + 1) M}

/-- The actual original mixed currents give a native globally compatible
signed current, multiplied by the supplied genuine bounded Borel function. -/
def current (D : MixedCurrentPartition omega) (u : Fin m → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    GlobalCurrent (m + 1) M (borelBidimensionOneDegree m) :=
  ∑ j, weightedPatchCurrent (D.patch j).geometry
    ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
    (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j) f hf hfb

/-- The genuine native normalized second derivative; its overlap law is
proved by full compact-test transposition, without a measure assumption. -/
def ddc (D : MixedCurrentPartition omega) (u : Fin m → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    GlobalCurrent (m + 1) M (topDegree (m + 1)) :=
  globalDdc (D.current u hu hb f hf hfb)

/-- The exact entire-chart transpose formula retains all original real
two-form tests and the actual normalized `ddᶜ` test differential. -/
theorem ddc_inChart (D : MixedCurrentPartition omega) (u : Fin m → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (e : ComplexChart (m + 1) M) :
    HEq ((D.ddc u hu hb f hf hfb).inChart e)
      ((bidimensionOneChartFunctional (D.current u hu hb f hf hfb) e).comp
        CompactDifferentialTests.localDdcTestCLM) :=
  globalDdc_inChart (D.current u hu hb f hf hfb) e

end MixedCurrentPartition

end SGPT.PSH.HermitianGlobalProducts
