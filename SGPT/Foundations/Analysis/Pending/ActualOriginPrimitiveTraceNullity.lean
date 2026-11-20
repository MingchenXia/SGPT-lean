import SGPT.Foundations.Analysis.Pending.ActualLeviBasisTraceDomination
import SGPT.Foundations.Analysis.Pending.ActualOriginPrimitiveUnitaryLeviNullity
import SGPT.Foundations.Analysis.GermPshLeviPositivity

set_option autoImplicit false

/-! # Actual complete local trace nullity from origin-only primitive germs

Actual regular directions, unitary coefficient measures, a common inner ball
and genuine full trace domination are internally produced from natural data.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace Module
open scoped Topology Distributions ContDiff InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.ActualOriginPrimitiveTraceNullity
open FirstPass FirstPass.MongeAmpere DivisorRegularLocus DivisorIntegrationCurrent
  ActualPrimitiveHolomorphicGraphProjection ActualHolomorphicRegularSpanningDirections
  ActualOriginPrimitiveUnitaryLeviNullity ActualLeviBasisTraceDomination
  LocalProductCurrents LocalBedfordTaylorProducts ScalarLeviPositiveCurrent
  LocalPositiveCurrentGluing PositivityLeviLink RegularDirectionDense

variable {m N : ℕ}

private theorem exists_directional_neighborhood
    {v : ComplexModel (m + 1)} (hv : ‖v‖ = 1)
    (f : Fin N → ComplexModel (m + 1) → ℂ) (hprimitive : IsPrimitiveAt f 0)
    (k : Fin N) (haxis : RegularAlong (f k) v)
    (Ω : Opens (ComplexModel (m + 1))) (hΩ : IsPreconnected (Ω : Set (ComplexModel (m + 1))))
    (h0 : (0 : ComplexModel (m + 1)) ∈ Ω) (p : ComplexModel (m + 1) → EReal)
    (hp : PlurisubharmonicOn p Ω) (hne : ∃ a ∈ Ω, p a ≠ ⊥) :
    ∃ (Q : Opens (ComplexModel (m + 1))) (hsub : Q ≤ Ω)
      (hQ : IsPreconnected (Q : Set (ComplexModel (m + 1))))
      (hneQ : ∃ a ∈ Q, p a ≠ ⊥) (μ : Measure (ComplexModel (m + 1))),
      (0 : ComplexModel (m + 1)) ∈ Q ∧
      (∀ K : Set (ComplexModel (m + 1)), IsCompact K → K ⊆ Q → μ K < ⊤) ∧
      (∀ φ : 𝓓(Q, ℝ), (∫ x, φ x ∂μ) =
        distributionalLeviCLM v (pshRegularDistribution (hp.mono hsub) volume hQ hneQ) φ) ∧
      μ {x : ComplexModel (m + 1) | x ∈ Q ∧ ∀ i, f i x = 0} = 0 := by
  obtain ⟨d, hd, ⟨S⟩⟩ := exists_splitting hv
  have hdm : d = m := by
    simp only [ComplexModel, finrank_euclideanSpace_fin] at hd
    exact Nat.add_right_cancel hd
  subst d
  obtain ⟨δ, hδ, ε, hε, hsub, hQ, hneQ, μ, _, hfinite, hrep, hnull⟩ :=
    exists_local_directional_measure_null_origin_primitive_common_zeros
      hv S f hprimitive k haxis Ω hΩ h0 p hp hne
  let Q : Opens (ComplexModel (m + 1)) :=
    ⟨splitHomeomorph hv S '' ((ball (0 : ℂ) ε) ×ˢ (ball (0 : ComplexModel m) δ)),
      (splitHomeomorph hv S).isOpenMap _ (isOpen_ball.prod isOpen_ball)⟩
  refine ⟨Q, hsub, hQ, hneQ, μ, ?_, hfinite, hrep, hnull⟩
  refine ⟨0, ⟨mem_ball_self hε, mem_ball_self hδ⟩, ?_⟩
  rw [splitHomeomorph_apply, map_zero]

private theorem psh_distribution_restrict
    {Q V : Opens (ComplexModel (m + 1))} (hVQ : V ≤ Q)
    {p : ComplexModel (m + 1) → EReal} (hp : PlurisubharmonicOn p Q)
    (hQ : IsPreconnected (Q : Set (ComplexModel (m + 1))))
    (hV : IsPreconnected (V : Set (ComplexModel (m + 1))))
    (hneQ : ∃ a ∈ Q, p a ≠ ⊥) (hneV : ∃ a ∈ V, p a ≠ ⊥) :
    restrictDistribution (pshRegularDistribution hp volume hQ hneQ) hVQ =
      pshRegularDistribution (hp.mono hVQ) volume hV hneV := by
  ext φ
  rw [restrictDistribution_apply, pshRegularDistribution_apply, pshRegularDistribution_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change ((TestFunction.monoCLM ℝ φ : 𝓓(Q, ℝ)) x) * (p x).toReal = φ x * (p x).toReal
    rw [congrFun (testFunction_inclusion_coe hVQ φ) x]

/-- Actual primitive germs at the origin and a noncollapsed unbounded PSH
potential internally produce a ball whose complete current trace kills the
common zeros. No nearby primitivity or trace certificate is supplied. -/
theorem exists_local_trace_null_origin_primitive_common_zeros
    (f : Fin N → ComplexModel (m + 1) → ℂ) (hprimitive : IsPrimitiveAt f 0)
    (k : Fin N) (hk : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), f k x = 0)
    (Ω : Opens (ComplexModel (m + 1))) (hΩ : IsPreconnected (Ω : Set (ComplexModel (m + 1))))
    (h0 : (0 : ComplexModel (m + 1)) ∈ Ω) (p : ComplexModel (m + 1) → EReal)
    (hp : PlurisubharmonicOn p Ω) (hne : ∃ a ∈ Ω, p a ≠ ⊥) :
    ∃ r : ℝ, 0 < r ∧
      let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
      ∃ (hsub : V ≤ Ω) (hV : IsPreconnected (V : Set (ComplexModel (m + 1))))
        (hneV : ∃ a ∈ V, p a ≠ ⊥),
        let T := pshRegularDistribution (hp.mono hsub) volume hV hneV
        let hT : HasNonnegativeDistributionalLevi T :=
          (hp.mono hsub).pshRegularDistribution_hasNonnegativeDistributionalLevi hV hneV
        let hC := isPositive_ddc_scalarTopCurrent hT
        hC.traceMeasure {x : ComplexModel (m + 1) | x ∈ V ∧ ∀ i, f i x = 0} = 0 := by
  classical
  have hf := hprimitive.choose
  have hg : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f k) x := by
    simpa only [add_zero] using hf k
  obtain ⟨b, hb⟩ := exists_unit_regular_basis (f k) hg hk
  have hex (i : Fin (m + 1)) := exists_directional_neighborhood (hb i).1
    f hprimitive k (hb i).2 Ω hΩ h0 p hp hne
  choose Q hQΩ hQc hneQ ν hQ0 hQfin hQrep hQnull using hex
  let W : Set (ComplexModel (m + 1)) := (Ω : Set (ComplexModel (m + 1))) ∩
    ⋂ i, (Q i : Set (ComplexModel (m + 1)))
  have hWo : IsOpen W := Ω.isOpen.inter (isOpen_iInter_of_finite fun i => (Q i).isOpen)
  have h0W : (0 : ComplexModel (m + 1)) ∈ W := ⟨h0, mem_iInter.mpr hQ0⟩
  obtain ⟨ρ, hρ, hρW⟩ := Metric.mem_nhds_iff.mp (hWo.mem_nhds h0W)
  let r : ℝ := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hrρ : r < ρ := by dsimp [r]; linarith
  let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
  have hballW : (V : Set (ComplexModel (m + 1))) ⊆ W :=
    (ball_subset_ball hrρ.le).trans hρW
  have hVΩ : V ≤ Ω := fun _ hx => (hballW hx).1
  have hVQ (i : Fin (m + 1)) : V ≤ Q i :=
    fun _ hx => mem_iInter.mp (hballW hx).2 i
  have hcompact : IsCompact (closedBall (0 : ComplexModel (m + 1)) r) := isCompact_closedBall _ _
  have hclosedQ (i : Fin (m + 1)) : closedBall (0 : ComplexModel (m + 1)) r ⊆ Q i := by
    intro x hx
    have hxρ : x ∈ ball (0 : ComplexModel (m + 1)) ρ :=
      (mem_closedBall.mp hx).trans_lt hrρ
    exact mem_iInter.mp (hρW hxρ).2 i
  have hV : IsPreconnected (V : Set (ComplexModel (m + 1))) := (convex_ball _ _).isPreconnected
  obtain ⟨a, ha, hpa⟩ := OpensRestrictionMeasure.exists_ne_bot_of_isOpen_subset
    hp hΩ hne V.isOpen ⟨0, mem_ball_self hr⟩ hVΩ
  have hneV : ∃ a ∈ V, p a ≠ ⊥ := ⟨a, ha, hpa⟩
  let T := pshRegularDistribution (hp.mono hVΩ) volume hV hneV
  have hT : HasNonnegativeDistributionalLevi T :=
    (hp.mono hVΩ).pshRegularDistribution_hasNonnegativeDistributionalLevi hV hneV
  let hC := isPositive_ddc_scalarTopCurrent hT
  obtain ⟨C, _, μ, hμ, hdom⟩ := exists_basis_measures_dominate_trace T hT b
  let E : Set V := {x | ∀ i, f i x = 0}
  have hμnull (i : Fin (m + 1)) : μ i E = 0 := by
    let νV : Measure V := (ν i).comap Subtype.val
    have hemb : MeasurableEmbedding (Subtype.val : V → ComplexModel (m + 1)) :=
      MeasurableEmbedding.subtype_coe V.isOpen.measurableSet
    have hνVfin : IsFiniteMeasure νV := by
      constructor
      change (ν i).comap Subtype.val univ < ⊤
      rw [hemb.comap_apply]
      simp only [image_univ]
      have hrange : range (Subtype.val : V → ComplexModel (m + 1)) =
          (V : Set (ComplexModel (m + 1))) := by
        ext x
        simp
      rw [hrange]
      exact (measure_mono ball_subset_closedBall).trans_lt (hQfin i _ hcompact (hclosedQ i))
    let : IsFiniteMeasure νV := hνVfin
    let : IsLocallyFiniteMeasure (μ i) := (hμ i).2.1
    have hνVrep (φ : 𝓓(V, ℝ)) :
        (∫ x : V, φ x ∂νV) = distributionalLeviCLM (b i) T φ := by
      have hmap : νV.map (Subtype.val : V → ComplexModel (m + 1)) = (ν i).restrict V := by
        rw [hemb.map_comap, Subtype.range_coe]
      have hint : (∫ x : V, φ x ∂νV) = ∫ x, φ x ∂ν i := by
        rw [← hemb.integral_map, hmap]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
          image_eq_zero_of_notMem_tsupport (fun hs => hx (φ.tsupport_subset hs)))
      rw [hint]
      have hφval : (φ : ComplexModel (m + 1) → ℝ) =
          (TestFunction.monoCLM ℝ φ : 𝓓(Q i, ℝ)) :=
        (testFunction_inclusion_coe (hVQ i) φ).symm
      rw [hφval, hQrep i]
      rw [← distributionalLeviCLM_restrictDistribution
        (pshRegularDistribution (hp.mono (hQΩ i)) volume (hQc i) (hneQ i))
          (hVQ i) (b i) φ]
      rw [psh_distribution_restrict (hVQ i) (hp.mono (hQΩ i)) (hQc i) hV (hneQ i) hneV]
    have heq : μ i = νV := by
      apply SmoothTestMeasureSeparation.Measure.eq_of_testFunction_integral_sub_eq_zero
      intro φ
      rw [(hμ i).2.2 φ, hνVrep φ, sub_self]
    rw [heq]
    change (ν i).comap Subtype.val E = 0
    rw [hemb.comap_apply]
    apply measure_mono_null _ (hQnull i)
    rintro x ⟨y, hy, rfl⟩
    exact ⟨hVQ i y.property, hy⟩
  have htrace : hC.traceMeasureOn E = 0 := by
    apply le_antisymm _ zero_le
    calc
      hC.traceMeasureOn E ≤ (C • ∑ i, μ i) E := hdom E
      _ = 0 := by
        rw [Measure.smul_apply, Measure.finsetSum_apply]
        simp only [hμnull, Finset.sum_const_zero, smul_zero]
  refine ⟨r, hr, hVΩ, hV, hneV, ?_⟩
  change hC.traceMeasure {x : ComplexModel (m + 1) | x ∈ V ∧ ∀ i, f i x = 0} = 0
  rw [IsPositive.traceMeasure,
    (IsPositive.measurableEmbedding_val (U := V)).map_apply]
  have hpre : (Subtype.val : V → ComplexModel (m + 1)) ⁻¹'
      {x : ComplexModel (m + 1) | x ∈ V ∧ ∀ i, f i x = 0} = E := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, x.property, true_and, E]
  rw [hpre]
  exact htrace

end SGPT.Foundations.Analysis.Pending.ActualOriginPrimitiveTraceNullity
