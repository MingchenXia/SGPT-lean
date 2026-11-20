import SGPT.Trace.TwistedL2SingularFrameLimits

/-!
# Gluing limits of frame coefficients

On overlapping actual frames, both limits come from the same sequence of sections.
Continuity of the fiberwise coordinate change and uniqueness of limits force the
compatibility needed to construct a single holomorphic section.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Glue compatible local limits, with compatibility derived from the same sequence
of sections rather than imposed as an additional hypothesis. -/
theorem exists_holomorphic_section_of_frame_limits
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (D : Set X) (hcover : ∀ x : X, ∃ y ∈ D, x ∈ preferredChartFrameDomain L y)
    (T : ℕ → (x : X) → L.Fiber x) (F : D → ComplexModel n → ℂ)
    (hF : ∀ y : D,
      DifferentiableOn ℂ (F y)
        (chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val)) ∧
      ∀ z ∈ chartFrameDomain L (complexChartAt (n := n) y.val)
          (preferredAtlasFrame L y.val),
        Tendsto (fun j => chartCoeff L (complexChartAt (n := n) y.val)
          (preferredAtlasFrame L y.val) (T j) z) atTop (𝓝 (F y z))) :
    ∃ S : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∀ (y : D) (x : X), x ∈ preferredChartFrameDomain L y.val →
        frameCoeff L (preferredAtlasFrame L y.val) S x =
          F y ((complexChartAt (n := n) y.val).val x)) ∧
      ∀ (G : (x : X) → L.Fiber x) (x : X),
        Tendsto (fun j => ‖G x - T j x‖) atTop (𝓝 ‖G x - S x‖) := by
  classical
  choose p hpD hp using hcover
  let q : X → D := fun x => ⟨p x, hpD x⟩
  let c : D → ComplexChart n X := fun y => complexChartAt (n := n) y.val
  let e : D → AtlasFrame L := fun y => preferredAtlasFrame L y.val
  let S : (x : X) → L.Fiber x := fun x =>
    (e (q x)).val.symm x (F (q x) ((c (q x)).val x))
  have hpoint : ∀ (y : D) (x : X), x ∈ preferredChartFrameDomain L y.val →
      Tendsto (fun j => frameCoeff L (e y) (T j) x) atTop (𝓝 (F y ((c y).val x))) := by
    intro y x hx
    have hz : (c y).val x ∈ chartFrameDomain L (c y) (e y) := by
      refine ⟨(c y).val.map_source hx.1, ?_⟩
      rw [mem_preimage, (c y).val.left_inv hx.1]
      exact hx.2
    have h := (hF y).2 _ hz
    change Tendsto (fun j => chartCoeff L (c y) (e y) (T j) ((c y).val x)) atTop
      (𝓝 (F y ((c y).val x))) at h
    simpa only [chartCoeff, (c y).val.left_inv hx.1] using h
  have hkey : ∀ (y : D) (x : X), x ∈ preferredChartFrameDomain L y.val →
      frameCoeff L (e y) S x = F y ((c y).val x) := by
    intro y x hx
    have hxq : x ∈ preferredChartFrameDomain L (q x).val := hp x
    let := (e y).property
    let := (e (q x)).property
    have hbase : x ∈ (e (q x)).val.baseSet ∩ (e y).val.baseSet := ⟨hxq.2, hx.2⟩
    have hq := hpoint (q x) x hxq
    have hy := hpoint y x hx
    have htrans := ((e (q x)).val.coordChangeL ℂ (e y).val x).continuous.continuousAt.tendsto.comp hq
    have heq : ∀ j, (e (q x)).val.coordChangeL ℂ (e y).val x
        (frameCoeff L (e (q x)) (T j) x) = frameCoeff L (e y) (T j) x := by
      intro j
      rw [Trivialization.coordChangeL_apply (R := ℂ) _ _ hbase]
      simp only [frameCoeff]
      rw [(e (q x)).val.symm_apply_apply_mk hxq.2]
    have htrans' : Tendsto (fun j => frameCoeff L (e y) (T j) x) atTop
        (𝓝 ((e (q x)).val.coordChangeL ℂ (e y).val x (F (q x) ((c (q x)).val x)))) :=
      htrans.congr' (Filter.Eventually.of_forall heq)
    have hlim := tendsto_nhds_unique htrans' hy
    simpa only [S, frameCoeff, Trivialization.coordChangeL_apply (R := ℂ) _ _ hbase] using hlim
  have hnorm : ∀ (G : (x : X) → L.Fiber x) (x : X),
      Tendsto (fun j => ‖G x - T j x‖) atTop (𝓝 ‖G x - S x‖) := by
    intro G x
    let y := q x
    have hx : x ∈ preferredChartFrameDomain L y.val := hp x
    let := (e y).property
    have hcoord := hpoint y x hx
    rw [← hkey y x hx] at hcoord
    have hc : Tendsto (fun _ : ℕ => frameCoeff L (e y) G x) atTop
        (𝓝 (frameCoeff L (e y) G x)) := tendsto_const_nhds
    have ht := (hc.sub hcoord).norm.mul_const (‖(e y).val.symm x 1‖)
    have heq : ∀ P : (x : X) → L.Fiber x,
        ‖G x - P x‖ = ‖frameCoeff L (e y) G x - frameCoeff L (e y) P x‖ *
          ‖(e y).val.symm x 1‖ := by
      intro P
      rw [norm_eq_coord_mul L (e y).val hx.2, coord_sub L (e y).val hx.2]
      rfl
    simpa only [← heq] using ht
  refine ⟨S, ?_, hkey, hnorm⟩
  intro x _
  let y := q x
  have hx : x ∈ preferredChartFrameDomain L y.val := hp x
  let := (e y).property
  have hNo : IsOpen (preferredChartFrameDomain L y.val) :=
    (c y).val.open_source.inter (e y).val.open_baseSet
  have hz : (c y).val x ∈ chartFrameDomain L (c y) (e y) := by
    refine ⟨(c y).val.map_source hx.1, ?_⟩
    rw [mem_preimage, (c y).val.left_inv hx.1]
    exact hx.2
  have hDo : IsOpen (chartFrameDomain L (c y) (e y)) :=
    (c y).val.isOpen_inter_preimage_symm (e y).val.open_baseSet
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n))
    (e y).val S hx.2]
  refine MDifferentiableAt.congr_of_eventuallyEq ?_
    (eventually_of_mem (hNo.mem_nhds hx) fun x' hx' => hkey y x' hx')
  exact (((hF y).1.differentiableAt (hDo.mem_nhds hz)).comp_mdifferentiableAt
    (mdifferentiableAt_atlas (c y).property hx.1))

end SGPT.Trace.TwistedL2
