import SGPT.PSH.SourceDomainBalayage

/-!
# Canonical ordinary balayage used in coefficient freezing

The replacement is the existing actual Perron envelope on the same
coordinate domain. Monotonicity follows from inclusion of all genuine
competitor families. At a boundary point the canonical PSH representative
has the required upper boundary limit. Coordinate balls supply their own
actual C1 defining functions, so their zero-mass replacement does not need
a boundary-geometry certificate from the caller.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.PSH.SourceDomainBalayageDraft
open scoped Topology ContDiff

variable {n : ℕ}

/-- Actual off-domain order of the data gives order of the entire canonical
Perron envelopes, including their upper regularization. -/
theorem domainPerronEnvelope_mono {Ω D : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ}
    (huv : ∀ z ∈ Ω, z ∉ D → u z ≤ v z) :
    domainPerronEnvelope Ω D u ≤ domainPerronEnvelope Ω D v := by
  apply uscRegularization_mono
  apply sSup_le_sSup
  intro w hw
  exact ⟨hw.1, fun z hz hzD =>
    (hw.2 z hz hzD).trans (EReal.coe_le_coe_iff.mpr (huv z hz hzD))⟩

/-- The real representatives of the actual locally bounded balayages are
monotone on their coordinate domain. -/
theorem domainPerronEnvelope_toReal_mono (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω)
    (huv : ∀ z ∈ Ω, z ∉ D → u z ≤ v z) {z : ComplexModel n} (hz : z ∈ Ω) :
    (domainPerronEnvelope Ω D u z).toReal ≤ (domainPerronEnvelope Ω D v z).toReal := by
  apply EReal.coe_le_coe_iff.mp
  rw [(domainPerronEnvelope_reader hn hu hDc hDΩ).2 z hz,
    (domainPerronEnvelope_reader hn hv hDc hDΩ).2 z hz]
  exact domainPerronEnvelope_mono huv z

/-- The upper boundary condition required for pasting is proved for the
canonical envelope and the actual original datum. -/
theorem domainPerronEnvelope_boundary_limsup_le (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D)
    {x : ComplexModel n} (hx : x ∈ frontier (D : Set (ComplexModel n))) :
    limsup (domainPerronEnvelope Ω D u) (𝓝[(D : Set (ComplexModel n))] x) ≤ (u x : EReal) := by
  have hxΩ : x ∈ Ω := hDΩ hx.1
  have hxD : x ∉ D := by
    simpa only [D.isOpen.interior_eq, SetLike.mem_coe] using hx.2
  have husc := (domainPerronEnvelope_plurisubharmonic hn hu hDc hDΩ x hxΩ).upperSemicontinuousAt
  have hlim := (husc.upperSemicontinuousWithinAt (D : Set (ComplexModel n))).limsup_le
  rw [domainPerronEnvelope_eq_off_domain hn hu hDc hDΩ hBoundary x hxΩ hxD] at hlim
  exact hlim

/-- Every actual coordinate ball has genuine C1 boundary, through the
defining function `‖z-a‖²-r²` and its nonzero normal derivative. -/
theorem ball_hasC1Boundary (a : ComplexModel n) {r : ℝ} (hr : 0 < r) :
    HasC1Boundary (⟨ball a r, isOpen_ball⟩ : Opens (ComplexModel n)) := by
  intro q hq
  have hqnorm : ‖q - a‖ = r := by
    simpa only [mem_sphere, dist_eq_norm] using frontier_ball_subset_sphere hq
  let ρ : ComplexModel n → ℝ := fun z => ‖z - a‖ ^ 2 - r ^ 2
  have hρ : ContDiff ℝ ∞ ρ :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  have hD : fderiv ℝ ρ q = 2 • innerSL ℝ (q - a) := by
    simpa [ρ] using
      ((((hasFDerivAt_id q).sub_const a).norm_sq).sub_const (r ^ 2)).fderiv
  refine ⟨⟨⊤, mem_univ q, ρ, hρ.contDiffOn.of_le (by norm_num), ?_, ?_, ?_⟩⟩
  · simp only [ρ, hqnorm, sub_self]
  · intro hzero
    have hval := congrArg (fun L : ComplexModel n →L[ℝ] ℝ => L (q - a)) hzero
    rw [hD] at hval
    have heval : (2 • innerSL ℝ (q - a)) (q - a) = 2 * ‖q - a‖ ^ 2 := by
      rw [two_smul, add_apply]
      change inner ℝ (q - a) (q - a) + inner ℝ (q - a) (q - a) = 2 * ‖q - a‖ ^ 2
      rw [real_inner_self_eq_norm_sq]
      ring
    rw [heval, hqnorm] at hval
    simp only [zero_apply] at hval
    nlinarith
  · intro z _
    change z ∈ ball a r ↔ ρ z < 0
    simp only [mem_ball, dist_eq_norm, ρ]
    constructor <;> intro hz <;> nlinarith [norm_nonneg (z - a)]

/-- The actual canonical homogeneous balayage on a ball has its actual
produced Bedford--Taylor measure, with zero mass inside the ball. -/
theorem exists_domainPerronEnvelope_ball_measure_zero (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (a : ComplexModel n) {r : ℝ} (hr : 0 < r)
    (hball : closedBall a r ⊆ Ω) :
    ∃ μ : Measure (ComplexModel n),
      IsBTLimit Ω (fun _ => fun z =>
        (domainPerronEnvelope Ω ⟨ball a r, isOpen_ball⟩ u z).toReal) μ ∧ μ (ball a r) = 0 := by
  let D : Opens (ComplexModel n) := ⟨ball a r, isOpen_ball⟩
  have hDc : IsCompact (closure (D : Set (ComplexModel n))) :=
    (isCompact_closedBall a r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω :=
    closure_ball_subset_closedBall.trans hball
  have hreader := domainPerronEnvelope_reader hn hu hDc hDΩ
  obtain ⟨μ, hμ⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (fun _ => hreader.1)
  exact ⟨μ, hμ, domainPerronEnvelope_btMass_zero hn hu hDc hDΩ (ball_hasC1Boundary a hr) hμ⟩

end SGPT.PSH.HermitianBalayage
