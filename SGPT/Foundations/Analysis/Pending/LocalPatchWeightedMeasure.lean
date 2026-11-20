import SGPT.Foundations.Analysis.Pending.PatchFormMass
import SGPT.Foundations.Analysis.Pending.ManifoldBorelFoundation
import Mathlib.MeasureTheory.Integral.CompactlySupported

set_option autoImplicit false

/-!
# Local weighted Borel measures on regular patches

The Stokes route needs a local, form-aware replacement for the existing
zero-order `RegularLocusParameterCurrent`.  That object is built from a
countable auxiliary cover of all of `V_reg`; it cannot directly encode a given
finite regular-piece family and its partition of unity.  This module instead
packages the data for **one** regular patch and one measurable parameter piece.

`LocalWeightedPatchMeasure` is an explicit finite ambient Borel measure equal
to the pushforward of `ρ dvol` on that parameter piece.  It gives a genuine
pairing on compactly supported scalar tests, its weighted change-of-variables
formula, and the local identification of a nonnegative top-form density with
the `ENNReal` pairing.  A later finite-family Stokes construction should give
one datum for every partition-of-unity piece and sum these pairings; it needs no
claim that the pieces are the old countable cover or cover all of `V_reg`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal CompactlySupported

namespace SGPT.Foundations.Analysis.Pending.LocalPatchWeightedMeasure

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
open ManifoldBorelFoundation
open PatchFormMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The weighted parameter measure on a prescribed parameter piece. -/
def parameterMeasure (S : Set (ComplexModel V.dim))
    (ρ : ComplexModel V.dim → ℝ≥0∞) : Measure (ComplexModel V.dim) :=
  (volume.restrict S).withDensity ρ

/-- Local data for one regular patch, with an explicit finite Borel measure on
the ambient manifold.  The measure is deliberately supplied as data rather
than extracted from a global current, so it can model one member of an
arbitrary finite partition-of-unity family. -/
structure LocalWeightedPatchMeasure (V : ClosedIrreducibleAnalyticSubvariety n M)
    (P : RegularPatch V) where
  parameterSet : Set (ComplexModel V.dim)
  measurableSet_parameterSet : MeasurableSet parameterSet
  parameterSet_subset_domain : parameterSet ⊆ P.parameterDomain
  density : ComplexModel V.dim → ℝ≥0∞
  density_aemeasurable : AEMeasurable density (volume.restrict parameterSet)
  density_ae_lt_top : ∀ᵐ w ∂volume.restrict parameterSet, density w < ⊤
  measure : @Measure M (manifoldBorel M)
  measure_eq_weightedPushforward :
    measure = @Measure.map (ComplexModel V.dim) M _ (manifoldBorel M) P.toManifold
      (parameterMeasure parameterSet density)
  measure_univ_lt_top : measure Set.univ < ⊤

namespace LocalWeightedPatchMeasure

variable {P : RegularPatch V}

/-- The patch parametrization is measurable on the declared parameter piece. -/
theorem aemeasurable_toManifold_restrict
    (D : LocalWeightedPatchMeasure V P) :
    @AEMeasurable (ComplexModel V.dim) M (manifoldBorel M) _ P.toManifold
      (volume.restrict D.parameterSet) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  exact (FirstPass.RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold P).mono
    D.parameterSet_subset_domain |>.aemeasurable D.measurableSet_parameterSet

/-- The patch parametrization is also measurable for the weighted parameter
measure; this is the input for `Measure.map` change of variables. -/
theorem aemeasurable_toManifold_parameterMeasure
    (D : LocalWeightedPatchMeasure V P) :
    @AEMeasurable (ComplexModel V.dim) M (manifoldBorel M) _ P.toManifold
      (parameterMeasure D.parameterSet D.density) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  exact D.aemeasurable_toManifold_restrict.mono'
    (withDensity_absolutelyContinuous (volume.restrict D.parameterSet) D.density)

/-- The supplied finite Borel measure is finite on compact sets. -/
theorem measure_isFiniteMeasureOnCompacts
    (D : LocalWeightedPatchMeasure V P) :
    @IsFiniteMeasureOnCompacts M (manifoldBorel M) _ D.measure := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  constructor
  intro K _hK
  exact (measure_mono (Set.subset_univ K)).trans_lt D.measure_univ_lt_top

/-- Compactly supported continuous tests are integrable against this local
weighted patch measure. -/
theorem integrable_compactTest
    (D : LocalWeightedPatchMeasure V P) (f : C_c(M, ℝ)) :
    Integrable (fun x => f x) D.measure := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  let _ : IsFiniteMeasureOnCompacts D.measure := D.measure_isFiniteMeasureOnCompacts
  exact CompactlySupportedContinuousMap.integrable f

/-- The local scalar pairing defined by the explicit ambient Borel measure. -/
def pairing (D : LocalWeightedPatchMeasure V P) : C_c(M, ℝ) →ₗ[ℝ] ℝ := by
  let _ : MeasurableSpace M := manifoldBorel M
  exact
    { toFun := fun f => ∫ x, f x ∂D.measure
      map_add' := by
        intro f g
        simpa using integral_add (D.integrable_compactTest f)
          (D.integrable_compactTest g)
      map_smul' := by
        intro c f
        simpa using (D.integrable_compactTest f).integral_smul c }

@[simp]
theorem pairing_apply (D : LocalWeightedPatchMeasure V P) (f : C_c(M, ℝ)) :
    D.pairing f = ∫ x, f x ∂D.measure := rfl

/-- The nonnegative weighted pushforward formula for the local ambient measure. -/
theorem lintegral_eq_weightedParameterIntegral
    (D : LocalWeightedPatchMeasure V P) (g : M → ℝ≥0∞)
    (hg : @Measurable M ℝ≥0∞ (manifoldBorel M) _ g) :
    ∫⁻ x, g x ∂D.measure =
      ∫⁻ w in D.parameterSet, D.density w * g (P.toManifold w) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  rw [D.measure_eq_weightedPushforward]
  change ∫⁻ x, g x ∂Measure.map P.toManifold
      (parameterMeasure D.parameterSet D.density) = _
  rw [lintegral_map' hg.aemeasurable D.aemeasurable_toManifold_parameterMeasure]
  exact lintegral_withDensity_eq_lintegral_mul₀ D.density_aemeasurable
    (hg.aemeasurable.comp_aemeasurable D.aemeasurable_toManifold_restrict)

/-- The real pairing is exactly the weighted parameter integral.  This is the
form suitable for a local Stokes equality once `density` is supplied by the
area/Jacobian calculation. -/
theorem pairing_eq_weightedParameterIntegral
    (D : LocalWeightedPatchMeasure V P) (f : C_c(M, ℝ)) :
    D.pairing f =
      ∫ w in D.parameterSet, (D.density w).toReal * f (P.toManifold w) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  rw [pairing_apply, D.measure_eq_weightedPushforward]
  change ∫ x, f.toContinuousMap x ∂Measure.map P.toManifold
      (parameterMeasure D.parameterSet D.density) = _
  rw [integral_map D.aemeasurable_toManifold_parameterMeasure
    f.continuous.aestronglyMeasurable]
  unfold parameterMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ D.density_aemeasurable
    D.density_ae_lt_top]
  simp only [smul_eq_mul]
  rfl

/-- A nonnegative compact test has nonnegative local pairing. -/
theorem pairing_nonneg
    (D : LocalWeightedPatchMeasure V P) (f : C_c(M, ℝ))
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ D.pairing f := by
  rw [pairing_apply]
  exact integral_nonneg hf

/-- The local pairing is linear over any finite partition-of-unity sum. -/
theorem pairing_finset_sum
    (D : LocalWeightedPatchMeasure V P) {ι : Type*}
    (s : Finset ι) (f : ι → C_c(M, ℝ)) :
    D.pairing (∑ i ∈ s, f i) = ∑ i ∈ s, D.pairing (f i) := by
  exact map_sum D.pairing f s

/-- The density integral used by one regular-piece mass summand. -/
def formDensityIntegral (a : SmoothRealForm n M 2)
    (D : LocalWeightedPatchMeasure V P) : ℝ≥0∞ :=
  ∫⁻ w in D.parameterSet, ENNReal.ofReal (patchFormDensity a P w)

/-- An a.e. density reconstruction identifies one local top-form mass summand
with the nonnegative integral of its ambient compact test.  This is a local
statement: it does not impose a global cover, a common limit, or Stokes. -/
theorem formDensityIntegral_eq_lintegral
    (D : LocalWeightedPatchMeasure V P) (a : SmoothRealForm n M 2)
    (f : C_c(M, ℝ))
    (hdensity : ∀ᵐ w ∂volume.restrict D.parameterSet,
      ENNReal.ofReal (patchFormDensity a P w) =
        D.density w * ENNReal.ofReal (f (P.toManifold w))) :
    D.formDensityIntegral a =
      ∫⁻ x, ENNReal.ofReal (f x) ∂D.measure := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  have hf : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.continuous_ofReal.comp f.continuous |>.measurable
  unfold formDensityIntegral
  calc
    ∫⁻ w in D.parameterSet, ENNReal.ofReal (patchFormDensity a P w) =
        ∫⁻ w in D.parameterSet,
          D.density w * ENNReal.ofReal (f (P.toManifold w)) :=
      lintegral_congr_ae hdensity
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂D.measure :=
      (D.lintegral_eq_weightedParameterIntegral
        (fun x => ENNReal.ofReal (f x)) hf).symm

/-- If the ambient compact test is nonnegative, the local top-form mass is the
`ENNReal.ofReal` of the genuine local pairing.  This is the exact local input a
finite partition-of-unity Stokes telescope can sum. -/
theorem formDensityIntegral_eq_ofReal_pairing
    (D : LocalWeightedPatchMeasure V P) (a : SmoothRealForm n M 2)
    (f : C_c(M, ℝ))
    (hdensity : ∀ᵐ w ∂volume.restrict D.parameterSet,
      ENNReal.ofReal (patchFormDensity a P w) =
        D.density w * ENNReal.ofReal (f (P.toManifold w)))
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    D.formDensityIntegral a = ENNReal.ofReal (D.pairing f) := by
  rw [pairing_apply]
  calc
    D.formDensityIntegral a =
        ∫⁻ x, ENNReal.ofReal (f x) ∂D.measure :=
      D.formDensityIntegral_eq_lintegral a f hdensity
    _ = ENNReal.ofReal (∫ x, f x ∂D.measure) :=
      (ofReal_integral_eq_lintegral_ofReal (D.integrable_compactTest f)
        (Filter.Eventually.of_forall hf_nonneg)).symm

end LocalWeightedPatchMeasure

end

end SGPT.Foundations.Analysis.Pending.LocalPatchWeightedMeasure
