import SGPT.Okounkov.OriginalFlagGeometry
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false

noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

namespace OriginalFlagGeometry

/-- The genuine inherited complex atlas on an original flag component. -/
@[instance_reducible]
def componentCharts {n : ℕ} (F : OriginalFlagGeometry.{u} n) (i : Fin (n + 1)) :
    ChartedSpace (ComplexModel (n - (i : ℕ))) (F.flag i) :=
  SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n i) (F.smooth.2.2 i).2.2

/-- Main's actual flattened atlas supplies its complex manifold structure. -/
theorem componentComplex {n : ℕ} (F : OriginalFlagGeometry.{u} n) (i : Fin (n + 1)) :
    letI := F.componentCharts i
    IsComplexManifold (n - (i : ℕ)) (F.flag i) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.sub_le n i) (F.smooth.2.2 i).2.2

end OriginalFlagGeometry

/-- The actual restriction and corestriction of the original map. -/
def flagComponentMap {n : ℕ} (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (i : Fin (n + 1))
    (hi : MapsTo π (W.flag i) (F.flag i)) : W.flag i → F.flag i :=
  fun z => ⟨π z, hi z.2⟩

/-- Source containment and actual holomorphic geometry produce each
restricted holomorphic map; no holomorphic-restriction field is assumed. -/
theorem contMDiff_flagComponentMap {n : ℕ} (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (i : Fin (n + 1)) (hi : MapsTo π (W.flag i) (F.flag i)) :
    letI := F.componentCharts i
    letI := W.componentCharts i
    ContMDiff 𝓘(ℂ, ComplexModel (n - (i : ℕ)))
      𝓘(ℂ, ComplexModel (n - (i : ℕ))) ∞ (flagComponentMap F W π i hi) := by
  exact SubmanifoldCodRestrict.contMDiff_restrictPreimage
    (Nat.sub_le n i) (F.smooth.2.2 i).2.2
    (Nat.sub_le n i) (W.smooth.2.2 i).2.2 hπ (fun z hz => hi hz)

/-- Original compactness and genuine continuity manufacture properness at
every flag level, rather than requiring properness of those restrictions. -/
theorem isProperMap_flagComponentMap {n : ℕ} (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (i : Fin (n + 1)) (hi : MapsTo π (W.flag i) (F.flag i)) :
    IsProperMap (flagComponentMap F W π i hi) := by
  let : CompactSpace (W.flag i) :=
    isCompact_iff_compactSpace.mp (W.smooth.level_isCompact i)
  exact ((hπ.continuous.comp continuous_subtype_val).subtype_mk
    (fun z => hi z.2)).isProperMap

/-- The original lifting geometry in the actual inherited component atlases:
proper holomorphic maps with genuine inverse data off thin analytic sets.
No correction matrix, reader equality, or trace compatibility is a field. -/
def IsFlagLifting {n : ℕ} (F W : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) : Prop :=
  IsAnalyticModification (n := n) π ∧
    ∀ i : Fin (n + 1), ∃ hi : MapsTo π (W.flag i) (F.flag i),
      letI := F.componentCharts i
      letI := F.componentComplex i
      letI := W.componentCharts i
      letI := W.componentComplex i
      IsAnalyticModification (n := n - (i : ℕ)) (flagComponentMap F W π i hi)

/-- The original geometric lifting condition internally yields the whole
image of every flag component, via main's actual proper-map surjectivity. -/
theorem IsFlagLifting.component_image_eq {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (i : Fin (n + 1)) :
    π '' W.flag i = F.flag i := by
  obtain ⟨hi, hlevel⟩ := hπ.2 i
  let := F.componentCharts i
  let := F.componentComplex i
  let := W.componentCharts i
  let := W.componentComplex i
  have hs := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hlevel
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hi hz
  · intro z hz
    obtain ⟨w, hw⟩ := hs (⟨z, hz⟩ : F.flag i)
    exact ⟨w, w.2, congrArg Subtype.val hw⟩

end SGPT.Okounkov
