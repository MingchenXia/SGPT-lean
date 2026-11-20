import SGPT.Projective.NativeRegularMemberWindow
import SGPT.Foundations.Analysis.Pending.ChartPartition

/-! Actual finite ambient partition retaining WHOLE regular-member window
geometry or off-member disjointness. No test form or local equality input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open DivisorRegularLocus

variable {m N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (s : Fin (N + 1) → HolomorphicSections (n := m + 1) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
  (hl : IsSmoothHypersurfaceMember (m + 1)
    (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- The SAME native submanifold chart structure used by the genuine whole
member window producer. The regularity proof carries no new geometry. -/
@[instance_reducible]
def nativeMemberChartedSpace : ChartedSpace (ComplexModel m)
    (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :=
  SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) (fun _ hx => regularAtDim_member
    _ (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl hx)

/-- The actual native complex structure of that same whole member. -/
theorem nativeMemberComplex :
    let := nativeMemberChartedSpace L s hgen l hl
    IsComplexManifold m (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) (fun _ hx => regularAtDim_member
    _ (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl hx)

/-- Actual ordinary ambient patch data, retaining the entire genuine member
window witnesses or actual disjointness from the WHOLE original member.
There are no current, density, pairing or integral conclusion fields. -/
structure NativeMemberPatch where
  frame : AtlasFrame L
  chart : ComplexChart (m + 1) X
  domain : TopologicalSpace.Opens X
  subset_frame_chart : (domain : Set X) ⊆ frame.val.baseSet ∩ chart.val.source
  window_or_off :
    (let := nativeMemberChartedSpace L s hgen l hl
      ∃ (x : X) (_hx : x ∈ member (sourceNativeFiniteSectionProjectiveMap L s hgen) l)
        (_hxO : x ∈ domain)
        (P : RegularPresentation
          (sectionCoefficient L.Fiber frame.val (linearSection L s l) ∘ chart.val.symm) (chart.val x))
        (e : ComplexChart m (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l)),
        P.m = 1 ∧
        (∀ y : member (sourceNativeFiniteSectionProjectiveMap L s hgen) l,
          y.1 ∈ domain → y ∈ e.val.source ∧ chart.val y.1 ∈ P.U) ∧
        regularLocus (sectionCoefficient L.Fiber frame.val (linearSection L s l) ∘ chart.val.symm) ∩
          (chart.val '' (domain : Set X)) = chart.val ''
            (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l ∩ (domain : Set X))) ∨
      Disjoint (domain : Set X) (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- At every original point a true member window or an actual off-member
frame/chart neighborhood is manufactured, before any smooth test occurs. -/
theorem exists_nativeMemberPatch_at (x : X) :
    ∃ Q : NativeMemberPatch L s hgen l hl, x ∈ Q.domain := by
  classical
  let p := sourceNativeFiniteSectionProjectiveMap L s hgen
  let W := member p l
  by_cases hx : x ∈ W
  · let := nativeMemberChartedSpace L s hgen l hl
    let := nativeMemberComplex L s hgen l hl
    have hex := exists_native_member_window L s hgen l hl
    dsimp only at hex
    obtain ⟨E, c, P, e, hO, hPm, hopen, hxO, hsub, hmem, hlocus⟩ := hex x hx
    refine ⟨{
      frame := E
      chart := c
      domain := ⟨hO, hopen⟩
      subset_frame_chart := hsub
      window_or_off := Or.inl ?_ }, hxO⟩
    exact ⟨x, hx, hxO, P, e, hPm, hmem, hlocus⟩
  · let E : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
    let c := complexChartAt (n := m + 1) x
    have hW : IsClosed W := isClosed_member p
      (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen).continuous l
    let O : TopologicalSpace.Opens X :=
      ⟨(E.val.baseSet ∩ c.val.source) ∩ Wᶜ,
        (E.val.open_baseSet.inter c.val.open_source).inter hW.isOpen_compl⟩
    refine ⟨{
      frame := E
      chart := c
      domain := O
      subset_frame_chart := fun _ hy => hy.1
      window_or_off := Or.inr ?_ }, ?_⟩
    · exact disjoint_left.mpr (fun y hy hyW => hy.2 hyW)
    · exact ⟨⟨mem_baseSet_trivializationAt ℂ L.Fiber x, mem_complexChartAt_source x⟩, hx⟩

/-- An actual finite smooth original partition, with every original patch's
window/off-member geometry retained. No test form has been introduced. -/
structure NativeMemberPartition where
  size : ℕ
  patch : Fin size → NativeMemberPatch L s hgen l hl
  weight : Fin size → X → ℝ
  smooth : ∀ i, ChartSmooth (n := m + 1) (weight i)
  nonnegative : ∀ i x, 0 ≤ weight i x
  support : ∀ i, tsupport (weight i) ⊆ (patch i).domain
  compact : ∀ i, IsCompact (tsupport (weight i))
  sum_one : ∀ x, ∑ i, weight i x = 1

/-- The actual whole-member window producer and actual compact smooth
partition theorem manufacture ALL finite weights and true local geometry.
No local desired current equality or test form is a producer premise. -/
theorem exists_nativeMemberPartition [CompactSpace X] :
    Nonempty (NativeMemberPartition L s hgen l hl) := by
  obtain ⟨r, χ, idx, hχ, hχ0, hs, hc, hsum⟩ := ChartPartition.exists_chartSmooth_partitionOfUnity (n := m + 1)
    (fun Q : NativeMemberPatch L s hgen l hl => Q.domain)
    (exists_nativeMemberPatch_at L s hgen l hl)
  exact ⟨⟨r, idx, χ, hχ, hχ0, hs, hc, hsum⟩⟩

end SGPT.Projective.NumEq.CompleteIntersections
