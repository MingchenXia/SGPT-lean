import SGPT.Foundations.Analysis.Pending.RooftopMetricCompleteness

set_option autoImplicit false
noncomputable section

namespace SGPT.RooftopMetric

open Filter
open scoped Topology

open SGPT.Foundations.Analysis.Pending.RooftopMetricCompleteness

/-- WHOLE original def:rays:L858: the three literal laws of an arbitrary
binary operation. No existing order or nonemptiness is assumed. -/
def SourcePreRooftop {α : Type*} (meet : α → α → α) : Prop :=
  (∀ a b, meet a b = meet b a) ∧
    (∀ a b c, meet (meet a b) c = meet a (meet b c)) ∧
      ∀ a, meet a a = a

/-- The original laws manufacture the native structure for the SAME
operation, rather than requiring a semilattice/order as an extra input. -/
def sourcePreRooftopToNative {α : Type*} {meet : α → α → α}
    (h : SourcePreRooftop meet) : PreRooftopStructure α where
  meet := meet
  meet_comm := h.1
  meet_assoc := h.2.1
  meet_idem := h.2.2

/-- Exact whole-object dictionary: native data use the identical operation. -/
theorem sourcePreRooftop_iff_native {α : Type*} (meet : α → α → α) :
    SourcePreRooftop meet ↔ ∃ R : PreRooftopStructure α, R.meet = meet := by
  constructor
  · intro h
    exact ⟨sourcePreRooftopToNative h, rfl⟩
  · rintro ⟨R, rfl⟩
    exact ⟨R.meet_comm, R.meet_assoc, R.meet_idem⟩

/-- The three ORIGINAL operation laws produce the order and even a genuine
meet semilattice. This is an output, not a source order premise. -/
@[instance_reducible]
def sourceRooftopSemilattice {α : Type*} {meet : α → α → α}
    (h : SourcePreRooftop meet) : SemilatticeInf α :=
  (sourcePreRooftopToNative h).toSemilatticeInf

/-- Exactly the original unlabelled partial-order convention. -/
theorem sourceRooftopOrder_le_iff {α : Type*} {meet : α → α → α}
    (h : SourcePreRooftop meet) (a b : α) :
    letI := sourceRooftopSemilattice h
    a ≤ b ↔ meet a b = a :=
  (sourcePreRooftopToNative h).le_iff_meet_eq_left a b

variable {α : Type*} [MetricSpace α]

/-- WHOLE original def:roof: a metric space with the original three-law
pre-rooftop operation, plus precisely the original one-slot contraction.
The pre-rooftop metric structure alone is SourcePreRooftop on this metric
space; no additional distance property is imposed on that earlier notion. -/
def SourceRooftopMetric (meet : α → α → α) : Prop :=
  SourcePreRooftop meet ∧ ∀ a b c, dist (meet a c) (meet b c) ≤ dist a b

/-- Original data manufacture the actual native rooftop metric structure
without changing the operation, given metric, topology or uniformity. -/
def sourceRooftopMetricToNative {meet : α → α → α}
    (h : SourceRooftopMetric meet) : RooftopMetricStructure α where
  toPreRooftopStructure := sourcePreRooftopToNative h.1
  dist_meet_le := h.2

theorem sourceRooftopMetric_iff_native (meet : α → α → α) :
    SourceRooftopMetric meet ↔ ∃ R : RooftopMetricStructure α, R.meet = meet := by
  constructor
  · intro h
    exact ⟨sourceRooftopMetricToNative h, rfl⟩
  · rintro ⟨R, rfl⟩
    exact ⟨⟨R.meet_comm, R.meet_assoc, R.meet_idem⟩, R.dist_meet_le⟩

/-- WHOLE original lma:landdis, on every original rooftop metric space. -/
theorem sourceRooftop_joint_distance_bound {meet : α → α → α}
    (h : SourceRooftopMetric meet) (a b a' b' : α) :
    dist (meet a b) (meet a' b') ≤ dist a a' + dist b b' :=
  (sourceRooftopMetricToNative h).dist_meet_le_add_dist a b a' b'

/-- The entire printed continuity consequence, for the actual given metric
topology and its actual product topology. -/
theorem sourceRooftop_continuous {meet : α → α → α}
    (h : SourceRooftopMetric meet) : Continuous (fun p : α × α ↦ meet p.1 p.2) :=
  (sourceRooftopMetricToNative h).meet_continuous

/-- WHOLE original prop:rooftopcomp. The source operation internally
produces the order used in BOTH monotone-Cauchy conditions. No external
order, tail-limit or completeness certificate is an additional premise. -/
theorem sourceRooftop_complete_iff_monotone {meet : α → α → α}
    (h : SourceRooftopMetric meet) :
    letI := sourceRooftopSemilattice h.1
    CompleteSpace α ↔
      (∀ u : ℕ → α, Monotone u → CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) ∧
      (∀ u : ℕ → α, Antitone u → CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) :=
  (sourceRooftopMetricToNative h).completeSpace_iff_monotone_cauchySeq_tendsto

end SGPT.RooftopMetric
