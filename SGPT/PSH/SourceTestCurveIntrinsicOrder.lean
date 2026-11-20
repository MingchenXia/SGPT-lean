import SGPT.PSH.SourceTestCurvePositiveMass
import SGPT.PSH.SourceTestCurveClosedness
import SGPT.PSH.SourceTestCurveLegendreCorrespondence
import SGPT.PSH.GlobalPComparison

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ η : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The ORIGINAL intrinsic comparison, allowing different actual backgrounds. -/
structure SourceTestCurvePOrder (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) : Prop where
  cutoff_le : Γ.max ≤ Δ.max
  slice_le : ∀ (r : ℝ) (hr : r < Γ.max),
    SGPT.PSH.GlobalPComparison.sourcePOrder (n := n)
      (Γ.potential ⟨r, hr⟩) (Δ.potential ⟨r, hr.trans_le cutoff_le⟩)

/-- Genuine global-P reflexivity, without an assumed positive-background witness. -/
theorem SourceTestCurvePOrder.refl (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : SourceTestCurvePOrder Γ Γ := by
  refine ⟨le_rfl, fun r hr => ?_⟩
  exact SingularGlobalPOrder.sourcePOrder_refl_of_isThetaPshPotential omega
    (Γ.native_thetaPSH ⟨r, hr⟩)

/-- Cross-background transitivity uses the actual global-P producer. -/
theorem SourceTestCurvePOrder.trans (omega : KahlerBackground n M)
    {Γ : SourceTestCurve θ} {Δ : SourceTestCurve σ} {Ξ : SourceTestCurve η}
    (h : SourceTestCurvePOrder Γ Δ) (k : SourceTestCurvePOrder Δ Ξ) :
    SourceTestCurvePOrder Γ Ξ := by
  refine ⟨h.cutoff_le.trans k.cutoff_le, fun r hr => ?_⟩
  exact SGPT.PSH.GlobalPComparison.sourcePOrder_trans omega
    (h.slice_le r hr) (k.slice_le r (hr.trans_le h.cutoff_le))

/-- Genuine positive slice models identify global P with literal slice order. -/
private theorem slice_globalP_iff (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (r : ℝ) (hr : r < Γ.max) (hs : r < Δ.max) :
    SGPT.PSH.GlobalPComparison.sourcePOrder (n := n)
      (Γ.potential ⟨r, hr⟩) (Δ.potential ⟨r, hs⟩) ↔
      Γ.potential ⟨r, hr⟩ ≤ Δ.potential ⟨r, hs⟩ := by
  let hu := (Γ.slice_model omega ⟨r, hr⟩).toNative
  let hv := (Δ.slice_model omega ⟨r, hs⟩).toNative
  rw [SGPT.PSH.GlobalPComparison.sourcePOrder_iff_positive_background omega
    (atlasClosedFormToNative θ) hu.plurisubharmonic hv.plurisubharmonic
    hu.positive_mass hv.positive_mass]
  change singularityEnvelope (atlasClosedFormToNative θ).val (Γ.potential ⟨r, hr⟩) ≤
    singularityEnvelope (atlasClosedFormToNative θ).val (Δ.potential ⟨r, hs⟩) ↔ _
  rw [← sourceSingularityEnvelope_eq_native, ← sourceSingularityEnvelope_eq_native,
    Γ.fixedPoint, Δ.fixedPoint]

/-- Exact intrinsic comparison in one actual background. -/
theorem sourceTestCurvePOrder_iff (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    SourceTestCurvePOrder Γ Δ ↔ ∃ hcut : Γ.max ≤ Δ.max,
      ∀ (r : ℝ) (hr : r < Γ.max),
        Γ.potential ⟨r, hr⟩ ≤ Δ.potential ⟨r, hr.trans_le hcut⟩ := by
  constructor
  · intro h
    exact ⟨h.cutoff_le, fun r hr =>
      (slice_globalP_iff omega Γ Δ r hr _).mp (h.slice_le r hr)⟩
  · rintro ⟨hcut, h⟩
    exact ⟨hcut, fun r hr => (slice_globalP_iff omega Γ Δ r hr _).mpr (h r hr)⟩

/-- Mutual comparison identifies the ENTIRE actual curve objects. -/
theorem SourceTestCurvePOrder.antisymm (omega : KahlerBackground n M)
    {Γ Δ : SourceTestCurve θ} (h : SourceTestCurvePOrder Γ Δ)
    (k : SourceTestCurvePOrder Δ Γ) : Γ = Δ := by
  apply SourceTestCurve.ext_of_max_potential _ _ (le_antisymm h.cutoff_le k.cutoff_le)
  intro r hr hs
  exact le_antisymm
    ((slice_globalP_iff omega Γ Δ r hr hs).mp (h.slice_le r hr))
    ((slice_globalP_iff omega Δ Γ r hs hr).mp (k.slice_le r hs))

/-- A genuine partial order with EXACTLY the original intrinsic relation. -/
@[instance_reducible]
def sourceTestCurvePartialOrder (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) : PartialOrder (SourceTestCurve θ) where
  le := SourceTestCurvePOrder
  le_refl := SourceTestCurvePOrder.refl omega
  le_trans := fun _ _ _ => SourceTestCurvePOrder.trans omega
  le_antisymm := fun _ _ => SourceTestCurvePOrder.antisymm omega

/-- Original comparison is literal order of ALL actual extension values. -/
theorem sourceTestCurvePOrder_iff_extension (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    SourceTestCurvePOrder Γ Δ ↔ ∀ r : ℝ,
      sourceTestCurveAt Γ.toSourceTestCurvePredata r ≤
        sourceTestCurveAt Δ.toSourceTestCurvePredata r := by
  constructor
  · intro h r x
    obtain ⟨hc, hs⟩ := (sourceTestCurvePOrder_iff omega Γ Δ).mp h
    rcases lt_trichotomy r Γ.max with hr | rfl | hr
    · rw [sourceTestCurveAt_of_lt _ hr, sourceTestCurveAt_of_lt _ (hr.trans_le hc)]
      exact hs r hr x
    · rw [Γ.toSourceTestCurvePredata.at_eq_earlierInf x Γ.max,
        Δ.toSourceTestCurvePredata.at_eq_earlierInf x Γ.max]
      apply iInf_mono
      intro t
      rw [sourceTestCurveAt_of_lt _ t.2,
        sourceTestCurveAt_of_lt _ (t.2.trans_le hc)]
      exact hs t.1 t.2 x
    · rw [sourceTestCurveAt_of_gt _ hr]
      exact bot_le
  · intro h
    have hnon : Nonempty M := by
      by_contra hn
      have hempty : (univ : Set M) = ∅ := by
        ext x
        exact False.elim (hn ⟨x⟩)
      have hm := Γ.positiveLimitMass
      rw [hempty, MeasureTheory.measure_empty] at hm
      exact (lt_irrefl 0) hm
    have hc : Γ.max ≤ Δ.max := by
      by_contra! hh
      obtain ⟨r, hdr, hrg⟩ := exists_between hh
      obtain ⟨x⟩ := hnon
      obtain ⟨y, _, hyn⟩ := (Γ.native_thetaPSH ⟨r, hrg⟩).2 x univ isOpen_univ (mem_univ x)
      have hy := h r y
      rw [sourceTestCurveAt_of_lt _ hrg, sourceTestCurveAt_of_gt _ hdr] at hy
      exact hyn (le_bot_iff.mp hy)
    apply (sourceTestCurvePOrder_iff omega Γ Δ).mpr
    refine ⟨hc, fun r hr x => ?_⟩
    have hx := h r x
    rwa [sourceTestCurveAt_of_lt _ hr, sourceTestCurveAt_of_lt _ (hr.trans_le hc)] at hx

end SGPT.PSH.VariableComplexAtlas
