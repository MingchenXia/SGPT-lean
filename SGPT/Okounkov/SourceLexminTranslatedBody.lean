import SGPT.Okounkov.SourceLexminNativeDivisorialVolume
import SGPT.AlmostSemigroup.Intersection

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceLexmin
open Set Filter MeasureTheory
open scoped Topology Pointwise ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody SGPT.Okounkov.TranscendentalMain

/-- The original compact convex body's positive actual volume gives its
genuine nonempty interior; no interior certificate is a caller assumption. -/
theorem interior_generalPartialBody_nonempty_of_kahler {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ u) :
    (interior (generalPartialBody F θ u)).Nonempty := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  have hu := isThetaPshPotential_of_isKahlerCurrentPotential hK
  have hpos := volume_generalPartialBody_pos (F := F) hu
    (diagonalPotentialMass_pos_of_isKahlerCurrentPotential hK hu)
  have hconv := (convex_isCompact_generalPartialBody (F := F) hu).1
  by_contra h
  have he : interior (generalPartialBody F θ u) = ∅ := not_nonempty_iff_eq_empty.mp h
  have hs : generalPartialBody F θ u ⊆ frontier (generalPartialBody F θ u) := by
    rw [frontier, he, sdiff_empty]
    exact subset_closure
  exact hpos.ne' (measure_mono_null hs (hconv.addHaar_frontier volume))

/-- Exact full original body translation by any REAL nonnegative multiple
of the original first flag divisor, for any actual Kähler residual. -/
theorem generalPartialBody_eq_divisor_translate_of_kahler {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {β : ClosedRealOneOneForm (m + 1) F.carrier} {v : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential β v)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {c : ℝ} (hc : 0 ≤ c) :
    generalPartialBody F (β + c • E.curvature)
        (fun x => v x + (c : EReal) * E.weight x) =
      (c • flagValuation F E.weight) +ᵥ generalPartialBody F β v := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  have hv := isThetaPshPotential_of_isKahlerCurrentPotential hK
  have hw := TranscendentalLifting.isThetaPshPotential_weight E
  have hcu := isThetaPshPotential_nonneg_smul hw hc
  have hsum := isThetaPshPotential_add_from_positive_sum hv hcu
  have hKsum : IsKahlerCurrentPotential (β + c • E.curvature)
      (fun x => v x + (c : EReal) * E.weight x) := by
    obtain ⟨κ, hκ⟩ := hK
    refine ⟨κ, ?_⟩
    have heq : β + c • E.curvature - κ.form = (β - κ.form) + c • E.curvature := by abel
    rw [heq]
    exact isThetaPshPotential_add_from_positive_sum hκ hcu
  let K := generalPartialBody F (β + c • E.curvature)
    (fun x => v x + (c : EReal) * E.weight x)
  let L := (c • flagValuation F E.weight) +ᵥ generalPartialBody F β v
  have hLK : L ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    have hdiv := SourceCurrentValuation.smul_flagValuation_mem_generalPartialBody_weight F hE hc
    have hadd := generalPartialBody_add_subset hv hcu ⟨y, hy, _, hdiv, rfl⟩
    change c • flagValuation F E.weight + y ∈ generalPartialBody F
      (β + c • E.curvature) (fun x => v x + (c : EReal) * E.weight x)
    simpa only [add_comm] using hadd
  have hKdata := convex_isCompact_generalPartialBody (F := F) hsum
  have hLclosed : IsClosed L := by
    have hcompact : IsCompact L := by
      change IsCompact ((fun y => c • flagValuation F E.weight + y) '' generalPartialBody F β v)
      exact (convex_isCompact_generalPartialBody (F := F) hv).2.image
        (continuous_const.add continuous_id)
    exact hcompact.isClosed
  have hvol : volume K = volume (generalPartialBody F β v) := by
    dsimp only [K]
    rw [volume_generalPartialBody_of_borelSpace hsum, volume_generalPartialBody_of_borelSpace hv,
      iVolume_add_weight F.omega hv E hc]
  have hLvol : volume L = volume (generalPartialBody F β v) := measure_vadd _ _ _
  have hreal : volume.real (K ∩ L) = volume.real K := by
    rw [inter_eq_right.mpr hLK]
    simp only [measureReal_def, hLvol, hvol]
  exact Subset.antisymm
    (SGPT.AlmostSemigroup.Intersection.subset_of_volume_inter_eq hKdata.2 hLclosed hKdata.1
      (interior_generalPartialBody_nonempty_of_kahler F hKsum) hreal) hLK

end SGPT.Okounkov.SourceLexmin
