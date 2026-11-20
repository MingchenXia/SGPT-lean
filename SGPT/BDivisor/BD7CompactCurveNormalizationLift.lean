import Mathlib.Analysis.Complex.RemovableSingularity
import SGPT.Okounkov.TranscendentalWNKeyGeometry
import SGPT.Projective.OriginalNormalizationProjectiveCurve
import SGPT.Foundations.Analysis.Pending.HironakaOneDimensionalCanonicalSuperlevels

set_option autoImplicit false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Metric
open scoped Topology Manifold

/-- A closed projection confines a nearby lift to the union of prescribed neighborhoods
of the points over the center. -/
theorem eventually_lift_mem_of_isClosedMap_bd7
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {π : Y → Z} (hπ : IsClosedMap π)
    {G : ℂ → Z} {u : ℂ → Y} {c : ℂ} (hG : ContinuousAt G c)
    (hu : ∀ᶠ z in 𝓝[≠] c, π (u z) = G z)
    {W : Set Y} (hW : IsOpen W) (hfiber : π ⁻¹' {G c} ⊆ W) :
    ∀ᶠ z in 𝓝[≠] c, u z ∈ W := by
  have hnot : G c ∈ (π '' Wᶜ)ᶜ := by
    rintro ⟨y, hy, h⟩
    exact hy (hfiber (mem_singleton_iff.mpr h))
  have hnear : ∀ᶠ z in 𝓝[≠] c, G z ∈ (π '' Wᶜ)ᶜ :=
    nhdsWithin_le_nhds (hG ((hπ _ hW.isClosed_compl).isOpen_compl.mem_nhds hnot))
  filter_upwards [hu, hnear] with z hz hzn
  by_contra hzu
  exact hzn ⟨u z, hzu, hz⟩

/-- A nonempty connected part of a union of pairwise disjoint open sets lies
in just one of the open sets. -/
theorem exists_subset_open_of_isPreconnected_iUnion_bd7
    {Y ι : Type*} [TopologicalSpace Y] {S : Set Y} (hS : IsPreconnected S)
    (hne : S.Nonempty) (W : ι → Set Y) (hW : ∀ i, IsOpen (W i))
    (hdisj : Pairwise fun i j => Disjoint (W i) (W j)) (hcover : S ⊆ ⋃ i, W i) :
    ∃ i, S ⊆ W i := by
  classical
  obtain ⟨y, hy⟩ := hne
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hy)
  refine ⟨i, hS.subset_left_of_subset_union (v := ⋃ j : {j : ι // j ≠ i}, W j) (hW i) ?_ ?_ ?_ ⟨y, hy, hi⟩⟩
  · exact isOpen_iUnion fun j : {j : ι // j ≠ i} => hW j
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz'
    exact Set.disjoint_left.mp (hdisj j.2.symm) hz hj
  · intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hz)
    by_cases h : j = i
    · exact Or.inl (h ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, h⟩, hj⟩)

/-- In one branch, apply Riemann's theorem to the coordinate of the lift.
The extended coordinate still lies in the chart when the original lift lay
in a closed ball contained in that chart. -/
theorem exists_differentiable_puncturedDisc_extension_bd7
    {c a : ℂ} {r R : ℝ} (hr : 0 < r) {v : ℂ → ℂ}
    (hv : DifferentiableOn ℂ v (ball c r \ {c}))
    (hV : MapsTo v (ball c r \ {c}) (closedBall a R)) :
    ∃ v' : ℂ → ℂ, DifferentiableOn ℂ v' (ball c r) ∧
      EqOn v' v (ball c r \ {c}) ∧ MapsTo v' (ball c r) (closedBall a R) := by
  classical
  let v' := Function.update v c (limUnder (𝓝[≠] c) v)
  have hb : BddAbove (norm ∘ v '' (ball c r \ {c})) := by
    refine ⟨R + ‖a‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    calc
      ‖v z‖ ≤ ‖v z - a‖ + ‖a‖ := by
        simpa only [sub_add_cancel] using norm_add_le (v z - a) a
      _ ≤ R + ‖a‖ := add_le_add_left (by simpa only [mem_closedBall, dist_eq_norm] using hV hz) _
  have hc := ball_mem_nhds c hr
  have hd : DifferentiableOn ℂ v' (ball c r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hc hv hb
  have he : EqOn v' v (ball c r \ {c}) := fun z hz => Function.update_of_ne hz.2 _ _
  refine ⟨v', hd, he, ?_⟩
  intro z hz
  by_cases h : z = c
  · subst z
    have ht : Tendsto v' (𝓝[≠] c) (𝓝 (v' c)) :=
      (hd.continuousOn.continuousAt hc).continuousWithinAt
    exact isClosed_closedBall.mem_of_tendsto ht (by
      have hf : ∀ᶠ z in 𝓝[≠] c, z ∈ ball c r \ {c} :=
        inter_mem (nhdsWithin_le_nhds hc) self_mem_nhdsWithin
      filter_upwards [hf] with z hz
      exact (he hz).symm ▸ hV hz)
  · have hz' : z ∈ ball c r \ {c} := ⟨hz, h⟩
    exact (he hz').symm ▸ hV hz'

/-- Choose a disjoint family of relatively bounded chart neighborhoods of a finite fiber. -/
theorem exists_separated_bounded_charts_of_finite_bd7
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] {S : Set Y} (hS : S.Finite)
    (e : S → OpenPartialHomeomorph Y ℂ) (he : ∀ x : S, x.val ∈ (e x).source) :
    ∃ (W : S → Set Y) (R : S → ℝ),
      (∀ x, IsOpen (W x)) ∧ Pairwise (fun x y => Disjoint (W x) (W y)) ∧
      S ⊆ ⋃ x, W x ∧
      (∀ x, W x ⊆ (e x).source) ∧
      (∀ x, MapsTo (e x) (W x) (closedBall (e x x.val) (R x))) ∧
      ∀ x, closedBall (e x x.val) (R x) ⊆ (e x).target := by
  classical
  obtain ⟨U, hU, hdisj⟩ := hS.t2_separation
  have hball (x : S) : ∃ r > 0, closedBall (e x x.val) r ⊆
      (e x).target ∩ (e x).symm ⁻¹' U x.val := by
    have hx : e x x.val ∈ (e x).target := (e x).map_source (he x)
    have hmem : e x x.val ∈ (e x).target ∩ (e x).symm ⁻¹' U x.val :=
      ⟨hx, by simpa only [mem_preimage, (e x).left_inv (he x)] using (hU x.val).1⟩
    have hopen := (e x).isOpen_inter_preimage_symm (hU x.val).2
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
    exact ⟨r / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hsub⟩
  choose R hR hcoord using hball
  let W : S → Set Y := fun x => (e x).source ∩ e x ⁻¹' ball (e x x.val) (R x)
  have hWU (x : S) : W x ⊆ U x.val := by
    intro y hy
    have h := (hcoord x (ball_subset_closedBall hy.2)).2
    simpa only [mem_preimage, (e x).left_inv hy.1] using h
  refine ⟨W, R, fun x => (e x).isOpen_inter_preimage isOpen_ball, ?_, ?_,
    fun _ _ h => h.1, fun _ _ h => ball_subset_closedBall h.2, fun x _ h => (hcoord x h).1⟩
  · intro x y hxy
    exact (hdisj x.property y.property (fun h => hxy (Subtype.ext h))).mono (hWU x) (hWU y)
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, he ⟨x, hx⟩, mem_ball_self (hR ⟨x, hx⟩)⟩

/-- An exact lift over a punctured disc extends in one of the separated charts of the
fiber over the puncture. The extended map still projects to the given map. -/
theorem exists_chart_lift_across_puncture_bd7
    {Y Z ι : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    {π : Y → Z} (hπ : Continuous π) (hπclosed : IsClosedMap π)
    {G : ℂ → Z} (hG : ContinuousAt G 0)
    {u : ℂ → Y} {r : ℝ} (hr : 0 < r)
    (hu : ContinuousOn u (ball 0 r \ {0}))
    (heq : ∀ z ∈ ball 0 r \ {0}, π (u z) = G z)
    (W : ι → Set Y) (hW : ∀ i, IsOpen (W i))
    (hdisj : Pairwise fun i j => Disjoint (W i) (W j))
    (hfiber : π ⁻¹' {G 0} ⊆ ⋃ i, W i)
    (e : ι → OpenPartialHomeomorph Y ℂ) (a : ι → ℂ) (R : ι → ℝ)
    (hsource : ∀ i, W i ⊆ (e i).source)
    (hcoord : ∀ i, MapsTo (e i) (W i) (closedBall (a i) (R i)))
    (htarget : ∀ i, closedBall (a i) (R i) ⊆ (e i).target)
    (hdiff : ∀ i, DifferentiableOn ℂ (e i ∘ u) ((ball 0 r \ {0}) ∩ u ⁻¹' W i)) :
    ∃ (δ : ℝ) (i : ι) (v : ℂ → ℂ), 0 < δ ∧ δ ≤ r ∧
      DifferentiableOn ℂ v (ball 0 δ) ∧ MapsTo v (ball 0 δ) (e i).target ∧
      EqOn ((e i).symm ∘ v) u (ball 0 δ \ {0}) ∧
      EqOn (π ∘ (e i).symm ∘ v) G (ball 0 δ) := by
  have hpunct (s : ℝ) (hs : 0 < s) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 s \ {0} :=
    inter_mem (nhdsWithin_le_nhds (ball_mem_nhds 0 hs)) self_mem_nhdsWithin
  have huW := eventually_lift_mem_of_isClosedMap_bd7 hπclosed hG
    ((hpunct r hr).mono fun z hz => heq z hz) (isOpen_iUnion hW) hfiber
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp huW)
  let δ := min η r
  have hδ : 0 < δ := lt_min hη hr
  have hδr : δ ≤ r := min_le_right _ _
  let D := ball (0 : ℂ) δ \ {0}
  have hD : D ⊆ ball 0 r \ {0} := sdiff_subset_sdiff (ball_subset_ball hδr) Subset.rfl
  have hnon : D.Nonempty := (hpunct δ hδ).exists
  have hpre : IsPreconnected (u '' D) :=
    SGPT.Okounkov.TranscendentalWN.isPreconnected_ball_diff_zero.image u (hu.mono hD)
  have hcover : u '' D ⊆ ⋃ i, W i := by
    rintro _ ⟨z, hz, rfl⟩
    exact hnear z (ball_subset_ball (min_le_left η r) hz.1) hz.2
  obtain ⟨i, hi⟩ := exists_subset_open_of_isPreconnected_iUnion_bd7 hpre
    (hnon.image u) W hW hdisj hcover
  have hi' : MapsTo u D (W i) := fun _ hz => hi ⟨_, hz, rfl⟩
  obtain ⟨v, hv, hev, hvm⟩ := exists_differentiable_puncturedDisc_extension_bd7 hδ
    ((hdiff i).mono fun _ hz => ⟨hD hz, hi' hz⟩)
    (fun _ hz => hcoord i (hi' hz))
  have hvt : MapsTo v (ball 0 δ) (e i).target := fun _ hz => htarget i (hvm hz)
  have hfix : EqOn ((e i).symm ∘ v) u D := by
    intro z hz
    change (e i).symm (v z) = u z
    rw [hev hz]
    exact (e i).left_inv (hsource i (hi' hz))
  refine ⟨δ, i, v, hδ, hδr, hv, hvt, hfix, ?_⟩
  intro z hz
  by_cases hn : z = 0
  · subst z
    let F := π ∘ (e i).symm ∘ v
    have hF : ContinuousOn F (ball 0 δ) :=
      hπ.continuousOn.comp ((e i).continuousOn_symm.comp hv.continuousOn hvt)
        (mapsTo_univ _ _)
    have hlim : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (F 0)) :=
      (hF.continuousAt (ball_mem_nhds 0 hδ)).continuousWithinAt
    have hlimG : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (G 0)) := hG.continuousWithinAt
    exact tendsto_nhds_unique_of_eventuallyEq hlim hlimG
      ((hpunct δ hδ).mono fun z hz => (congrArg π (hfix hz)).trans (heq z (hD hz)))
  · have hz' : z ∈ D := ⟨hz, hn⟩
    exact (congrArg π (hfix hz')).trans (heq z (hD hz'))


section Curve

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes

/-- The exceptional trace on a connected source curve is discrete as soon as
some source point lies in the good open. -/
theorem isDiscrete_proper_analyticSubset_curve_bd7
    {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    [IsComplexManifold 1 T] [ConnectedSpace T] {A : Set T}
    (hA : IsComplexAnalyticSubset (n := 1) A) (hne : A ≠ univ) :
    IsDiscrete A := by
  apply HironakaOneDimensionalCanonicalSuperlevels.isDiscrete_of_analytic_dimLE_zero hA
  intro x k hk
  have hle := hk.1
  have hne' : k ≠ 1 := by
    intro h
    subst k
    exact hne (hA.eq_univ_of_interior_nonempty ⟨x,
      mem_interior_iff_mem_nhds.mpr (EmbeddedFromResolution.mem_nhds_of_regularAtDim_self hk)⟩)
  omega

/-- The actual finite normalization is identified over the original image with a
smooth projective curve. The latter is an isomorphism on a nonempty algebraic open. -/
theorem exists_canonical_smoothProjective_normalization_curve_bd7
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : let := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ X)
      (_ : IsFinite ρ) (_ : SmoothOfRelativeDimension 1 (ρ ≫ f))
      (_ : ClosedProjectiveEmbedding (ρ ≫ f)),
      (∃ j : originalNormalizationScheme X ≅ Y, j.hom ≫ ρ = originalNormalizationMap X) ∧
      ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (ρ ∣_ U) := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨Y, hY, ρ, hproper, n, hsm, EY, hn, hbir, -, -⟩ :=
    SGPT.Okounkov.OF12.exists_smooth_projective_birational_model E
  have hn' : n = 1 := by exact_mod_cast hn.symm.trans hcurve
  subst n
  let := hY
  let := hproper
  let := hsm
  let := hbir
  let : IsFinite ρ := isFinite_of_smoothProjectiveBirationalCurve f ρ EY
  obtain ⟨U, hU, hIso⟩ := SGPT.BDivisor.BD7.exists_isIso_morphismRestrict_of_isIso_stalkMap ρ
  exact ⟨Y, hY, ρ, inferInstance, hsm, EY, canonicalSmoothCurveModel f ρ, U, hU, hIso⟩

end Curve

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
