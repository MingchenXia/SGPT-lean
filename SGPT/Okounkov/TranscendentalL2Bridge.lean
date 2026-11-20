import SGPT.Okounkov.TranscendentalL2Statement
import SGPT.Okounkov.TranscendentalRelGen
import SGPT.Okounkov.TranscendentalLifting

/-!
# Bridges from the `L²` generation over a coordinate ball

Plan `tok/RELGEN2/PLAN.md` §0 (blueprint `l2:modification-generation`, `l2:bridge`, chapter
`claude-tok-l2`).

* `modificationL2Generation_of_weaklyPseudoconvex`: RELGEN's statement
  `WeaklyPseudoconvexL2GenerationStatement` implies `ModificationL2GenerationStatement`; the latter
  is the special case used by `tok:relgen` (it is weaker).
* `relativeGlobalGeneration_of_modificationL2Generation`: `ModificationL2GenerationStatement`
  implies RELGEN's `RelativeGlobalGenerationStatement` (`tok:relgen`). The proof is RELGEN's
  `relativeGlobalGeneration_of_l2Generation` verbatim, with `V = π⁻¹(d⁻¹ B(p, r))` replaced by the
  neighbourhood `π⁻¹ U` provided by the statement.
* `pushforwardAnalyticStatement_of_modificationL2Generation`: hence DRWNXZ Lemma 2.8
  (`tok:boucksom-pushforward`), and `liftingInvarianceStatement_of_modificationL2Generation`:
  item 3 of `thm:Okounkovtranmain` (LIFT's `liftingInvarianceStatement_of_pushforwardAnalytic`).

Once `ModificationL2GenerationStatement` is proved (plan steps P5–P9), item 3 is the term
`liftingInvarianceStatement_of_modificationL2Generation modificationL2Generation F`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalRelGen

/-- `ModificationL2GenerationStatement` is weaker than RELGEN's
`WeaklyPseudoconvexL2GenerationStatement`: `V = π⁻¹(d⁻¹ B(p, r))` is weakly pseudoconvex and
`dd^c φ_N ≥ ((N + 1)/c) β` (RELGEN `relgen:weight`), and `U = d⁻¹ B(p, r)` works. -/
theorem modificationL2Generation_of_weaklyPseudoconvex
    (hW : WeaklyPseudoconvexL2GenerationStatement.{u}) : ModificationL2GenerationStatement.{u} := by
  intro n X Z _ _ _ _ _ _ _ π hπ θ β D E c h hc hβ hE hh hheq
  obtain ⟨C, hC, hgen⟩ := hW n Z ⟨β, hβ⟩
  refine ⟨C, hC, fun q N hN d p r ρ hcl hρ z hz f hf => ?_⟩
  have hV := isWeaklyPseudoconvexOpen_preimage_ball hπ.1 hπ.2.1 d hcl
  have hφ := isThetaPshPotentialOn_weight hπ.1 θ β hβ hE hc hh hheq d hρ N hN
  obtain ⟨F, hFd, hFmem, hrest⟩ := hgen q _ hV _ hφ z hz f hf
  exact ⟨d.val.source ∩ d.val ⁻¹' ball p r, d.val.isOpen_inter_preimage isOpen_ball, hz,
    subset_rfl, F, hFd, hFmem, hrest⟩

/-- **Relative global generation** (blueprint `tok:relgen`) from
`ModificationL2GenerationStatement`: RELGEN's assembly
(`relativeGlobalGeneration_of_l2Generation`) with the neighbourhood `π⁻¹ U` of the statement. -/
theorem relativeGlobalGeneration_of_modificationL2Generation
    (hM : ModificationL2GenerationStatement.{u}) : RelativeGlobalGenerationStatement.{u} := by
  have hdiv : L2DivisibilityStatement := l2DivisibilityStatement
  intro n X Z _ _ _ _ _ _ _ π hπ θ β D E c hc hβ hE hclass
  have hrel : ClosedRealOneOneForm.BottChernRel (ClosedRealOneOneForm.pullback hπ.1 θ)
      (β + c • E.curvature) := by
    rw [← RealBottChern.ofRepresentative_eq_iff, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul]
    exact hclass
  obtain ⟨h, hh, hheq⟩ := hrel
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- dimension zero: the constant `1` is a section generating every stalk
    refine ⟨0, fun z => ⟨univ, isOpen_univ, mem_univ _, ?_⟩⟩
    have hone : IsIdealSectionOn (divisorSuccNsmul D 0).ideal (π ⁻¹' univ) (fun _ => (1 : ℂ)) := by
      refine ⟨mdifferentiableOn_const, fun y _ => ?_⟩
      obtain ⟨Vy, hVy, hyVy, g, hg, -, -, -⟩ := exists_localEquation_of_isDivisorMetric hE y
      have hg0 := IsLocalEquationOn.succNsmul hVy hg 0
      -- in dimension zero every point is isolated
      have hiso : IsOpen ({y} : Set Z) := by
        have hsrc := (chartAt (ComplexModel n) y).open_source
        convert hsrc using 1
        ext t
        constructor
        · intro ht
          rw [mem_singleton_iff.mp ht]
          exact mem_chart_source _ y
        · intro ht
          have hinj := (chartAt (ComplexModel n) y).injOn ht (mem_chart_source _ y)
          subst hn0
          exact hinj (Subsingleton.elim _ _)
      obtain ⟨t, ht, hgt⟩ := hg.2.1 {y} hiso (singleton_subset_iff.mpr hyVy) ⟨y, rfl⟩
      rw [mem_singleton_iff.mp ht] at hgt
      have hgyN : g y ^ (0 + 1) ≠ 0 := pow_ne_zero _ hgt
      refine (hg0.2.2 y hyVy _).mpr (isInSpanAt_eq_iff.mpr ⟨holomorphicAt_const 1,
        fun t => (g t ^ (0 + 1))⁻¹, ?_, ?_⟩)
      · exact holomorphicAt_inv_of_ne_zero hVy hg0.1 hyVy hgyN
      · filter_upwards [hiso.mem_nhds rfl] with t ht
        rw [mem_singleton_iff.mp ht, inv_mul_cancel₀ hgyN]
    intro b' hb'
    have hb'hol := holomorphicAt_of_mem_divisorSuccNsmul hE hb'
    exact isInSpanAt_of_eq_mul hone hb'hol hb'hol (Eventually.of_forall fun _ => (mul_one _).symm)
  -- positive dimension
  obtain ⟨C, hC, hgen⟩ := hM n X Z π hπ θ β D E c h hc hβ hE hh hheq
  set K : ℝ := C * ((n : ℝ) + 1) with hK
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K ≤ ((N : ℝ) + 1) / c := by
    refine ⟨⌈K * c⌉₊, ?_⟩
    rw [le_div_iff₀ hc]
    linarith [Nat.le_ceil (K * c)]
  refine ⟨N, fun z => ?_⟩
  set x := π z
  set d := complexChartAt (n := n) x
  have hxd : x ∈ d.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hpW, hρ⟩ := LocalPotentials.hasSmoothLocalPotentials_of_closed_typeOneOne
    θ.val θ.property.1 θ.property.2 d (d.val x) (d.val.map_source hxd)
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 _ hpW
  set p := d.val x
  set r := ε / 2 with hr
  have hr0 : 0 < r := half_pos hε
  have hcl : closedBall p r ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hεW
  have hcl' : closedBall p r ⊆ d.val.target := hcl.trans hρ.2.1
  have hρb : IsSmoothLocalPotential θ.val d (ball p r) ρ :=
    ⟨isOpen_ball, ball_subset_closedBall.trans hcl',
      hρ.2.2.1.mono (ball_subset_closedBall.trans hcl),
      fun w hw => hρ.2.2.2 (hcl (ball_subset_closedBall hw))⟩
  set V := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r) with hVdef
  set a := ((N : ℝ) + 1) / c with ha
  have hzV : z ∈ V := ⟨hxd, mem_ball_self hr0⟩
  have hρc : ContinuousOn ρ (ball p r) := hρb.2.2.1.continuousOn
  obtain ⟨Vz, g, hVz, hzVz, hg, O, b, hO, hzO, hOsub, hb, hpres⟩ :=
    exists_chart_weight_presentation hπ.1.continuous hE d isOpen_ball hρc hh N a hzV
  have hOsub' : O ⊆ (complexChartAt (n := n) z).val.target ∩
      (complexChartAt (n := n) z).val.symm ⁻¹' Vz := fun w hw => ⟨(hOsub hw).1, (hOsub hw).2.1⟩
  have hf := mem_multiplierIdeal_localEquation_pow hVz hzVz hg hO hzO hOsub' hb hpres
  obtain ⟨U, hUo, hzU, hUsub, F, hFd, hFmem, r', hr', -, hint⟩ :=
    hgen n N hN d p r ρ hcl' hρb z hzV (fun t => g t ^ (N + 1)) hf
  refine ⟨U, hUo, hzU, ?_⟩
  set V' := π ⁻¹' U with hV'def
  have hV'o : IsOpen V' := hUo.preimage hπ.1.continuous
  have hV'V : V' ⊆ V := preimage_mono hUsub
  -- `F` is a section of `𝒪(-(N+1)D)` over `V' = π⁻¹ U`
  have hFsec : IsIdealSectionOn (divisorSuccNsmul D N).ideal V' F := by
    refine ⟨hFd, fun y hy => ?_⟩
    obtain ⟨Vy, gy, hVy, hyVy, hgy, Oy, by', hOy, hyOy, hOysub, hby, hpresy⟩ :=
      exists_chart_weight_presentation hπ.1.continuous hE d isOpen_ball hρc hh N a (hV'V hy)
    obtain ⟨A, hA, hAeq⟩ := exists_chart_factor_of_mem_multiplierIdeal hdiv hgy hOy hyOy
      (fun w hw => ⟨(hOysub hw).1, (hOysub hw).2.1⟩) hby hpresy (hFmem y hy)
    have hgyN := IsLocalEquationOn.succNsmul hVy hgy N
    refine (hgyN.2.2 y hyVy F).mpr (isInSpanAt_eq_iff.mpr ⟨?_, fun t => A
      ((complexChartAt (n := n) y).val t), ?_, eventually_eq_mul_of_chart hAeq⟩)
    · exact InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV'o hFd hy
    · exact MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart (x := y)
        (mem_complexChartAt_source y) hA
  -- `F = A g^{N+1}` near `z` with `A(z) = 1`
  obtain ⟨A, hA, hAeq⟩ := exists_chart_factor_of_mem_multiplierIdeal hdiv hg hO hzO hOsub' hb
    hpres (hFmem z hzU)
  have hA1 := eq_one_of_pole_integral hn hg hO hzO hOsub' hb hpres hA hAeq hr' hint
  set ez := complexChartAt (n := n) z
  have hze : z ∈ ez.val.source := mem_complexChartAt_source z
  have hAinv : ∀ᶠ w in 𝓝 (ez.val z), DifferentiableAt ℂ (fun w => (A w)⁻¹) w := by
    filter_upwards [hA, hA.self_of_nhds.continuousAt.eventually_ne (by rw [hA1]; exact one_ne_zero)]
      with w hw hw0
    exact hw.inv hw0
  have hAz : ∀ᶠ t in 𝓝 z, A (ez.val t) ≠ 0 := by
    have hc : ContinuousAt (fun t => A (ez.val t)) z :=
      hA.self_of_nhds.continuousAt.comp (ez.val.continuousAt hze)
    exact hc.eventually_ne (by rw [hA1]; exact one_ne_zero)
  have hFz : ∀ᶠ t in 𝓝 z, F t = A (ez.val t) * g t ^ (N + 1) := eventually_eq_mul_of_chart hAeq
  have hgz := IsLocalEquationOn.succNsmul hVz hg N
  intro b' hb'
  obtain ⟨hb'hol, c', hc', hc'eq⟩ := isInSpanAt_eq_iff.mp ((hgz.2.2 z hzVz b').mp hb')
  have hAinvz : HolomorphicAt n (fun t => (A (ez.val t))⁻¹) z :=
    MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart (x := z) hze hAinv
  refine isInSpanAt_of_eq_mul (s := F) (a := fun t => c' t * (A (ez.val t))⁻¹) hFsec hb'hol
    (hc'.mul hAinvz) ?_
  filter_upwards [hc'eq, hFz, hAz] with t ht hFt hAt
  rw [ht, hFt]
  field_simp


/-- **DRWNXZ Lemma 2.8** (`tok:boucksom-pushforward`) from `ModificationL2GenerationStatement`. -/
theorem pushforwardAnalyticStatement_of_modificationL2Generation
    (hM : ModificationL2GenerationStatement.{u}) : PushforwardAnalyticStatement.{u} :=
  pushforwardAnalyticStatement_of_relativeGlobalGeneration
    (relativeGlobalGeneration_of_modificationL2Generation hM)

/-- **Item 3 of `thm:Okounkovtranmain`** (`tok:lifting-invariance`) from
`ModificationL2GenerationStatement` (LIFT's `liftingInvarianceStatement_of_pushforwardAnalytic`). -/
theorem liftingInvarianceStatement_of_modificationL2Generation {m : ℕ}
    (hM : ModificationL2GenerationStatement.{u})
    (F : OriginalFlagGeometry.{u} (m + 1)) :
    TranscendentalMain.LiftingInvarianceStatement F :=
  TranscendentalLifting.liftingInvarianceStatement_of_pushforwardAnalytic
    (pushforwardAnalyticStatement_of_modificationL2Generation hM) F

end SGPT.Okounkov.TranscendentalL2
