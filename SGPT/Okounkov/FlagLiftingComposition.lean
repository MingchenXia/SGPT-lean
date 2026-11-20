import SGPT.Okounkov.FlagCorrection
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending AnalyticModificationLocalDiscrepancy

/-- Compose actual original modifications at every inherited flag level;
no composite containment, atlas or modification certificate is assumed. -/
theorem IsFlagLifting.comp {n : ℕ}
    {F W V : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) :
    IsFlagLifting F V (π ∘ p) := by
  refine ⟨AnalyticModificationComposition.isAnalyticModification_comp hπ.1 hp.1, ?_⟩
  intro i
  obtain ⟨hiπ, hπi⟩ := hπ.2 i
  obtain ⟨hip, hpi⟩ := hp.2 i
  refine ⟨hiπ.comp hip, ?_⟩
  let := F.componentCharts i
  let := F.componentComplex i
  let := W.componentCharts i
  let := W.componentComplex i
  let := V.componentCharts i
  let := V.componentComplex i
  have h := AnalyticModificationComposition.isAnalyticModification_comp hπi hpi
  exact h

/-- The selected original tail restriction of the composite is literally
the composition of the two selected original tail restrictions. -/
theorem IsFlagLifting.tailMap_comp {m : ℕ}
    {F W V : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p) :
    (hπ.comp hp).tailMap = hπ.tailMap ∘ hp.tailMap := by
  funext z
  apply Subtype.ext
  rfl

end SGPT.Okounkov
