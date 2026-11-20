import SGPT.Foundations.Analysis.Pending.PolydiskScaledBalayageOrder
import SGPT.Foundations.Analysis.Pending.PolydiskPerronDataComparison
import SGPT.Foundations.Analysis.FirstPass.BTTruncations

set_option autoImplicit false

/-! # Actual Perron order for locally bounded, possibly discontinuous, PSH data -/

open Set TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.SingularBalayageDataOrder

open FirstPass FirstPass.MongeAmpere BedfordTaylor

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- Actual compact bounds and the genuine competitor maximum principle bound the Perron value family. -/
theorem le_perronEnvelope_of_competitor (hn : 0 < n)
    {u w : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    (hw : IsPerronCompetitor u w) {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    w z ≤ perronEnvelope u z := by
  obtain ⟨C, -, hC⟩ :=
    hu.exists_compact_abs_bound (isCompact_closedUnitPolydisk (n := n)) hPΩ
  refine le_ciSup_of_le ⟨C, ?_⟩ ⟨w, hw⟩ le_rfl
  rintro y ⟨v, rfl⟩
  exact v.2.le_of_forall_le (fun x hx => (le_abs_self _).trans (hC x hx)) hz ⟨0, hn⟩

/-- Boundary order of actual locally bounded PSH data gives order of their actual Perron envelopes, without continuity. -/
theorem perronEnvelope_mono (hn : 0 < n)
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    (hle : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, u ζ ≤ v ζ)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    perronEnvelope u z ≤ perronEnvelope v z := by
  have := nonempty_perronCompetitors_of_isLocallyBoundedPshOn hu hPΩ
  exact ciSup_le fun w => le_perronEnvelope_of_competitor hn hv hPΩ
    (w.2.mono_boundary hle) hz

/-- Actual scaled balayages preserve order of locally bounded PSH data on the same actual domain. -/
theorem scaledPolydiskBalayage_mono (hn : 0 < n)
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    (hle : ∀ z ∈ (Ω : Set (ComplexModel n)), u z ≤ v z)
    {z : ComplexModel n} (hz : z ∈ (Ω : Set (ComplexModel n))) :
    scaledPolydiskBalayage c r u z ≤ scaledPolydiskBalayage c r v z := by
  by_cases hzP : z ∈ scaledPolydisk c r
  · rw [scaledPolydiskBalayage_of_mem hr u hzP, scaledPolydiskBalayage_of_mem hr v hzP]
    exact perronEnvelope_mono hn (isLocallyBoundedPshOn_comp_polydiskChart hu c r)
      (isLocallyBoundedPshOn_comp_polydiskChart hv c r)
      (fun w hw => hPΩ ⟨w, hw, rfl⟩)
      (fun w hw => hle _ (hPΩ ⟨w, hw.1, rfl⟩))
      ((mem_scaledPolydisk_iff hr).mp hzP)
  · rw [scaledPolydiskBalayage_eqOn_compl hr u hzP, scaledPolydiskBalayage_eqOn_compl hr v hzP]
    exact hle z hz

/-- Genuine extended-real truncations produce actual decreasing balayages, even at poles of the datum. -/
theorem scaledPolydiskBalayage_truncation_antitone (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {z : ComplexModel n} (hz : z ∈ (Ω : Set (ComplexModel n))) :
    Antitone (fun j => scaledPolydiskBalayage c r (truncationReal u j) z) := by
  intro j l hjl
  exact scaledPolydiskBalayage_mono hn (truncationReal_isLocallyBoundedPshOn hu l)
    (truncationReal_isLocallyBoundedPshOn hu j) hr hPΩ
    (fun w hw => truncationReal_antitone hu hw hjl) hz

end

end SGPT.Foundations.Analysis.Pending.SingularBalayageDataOrder
