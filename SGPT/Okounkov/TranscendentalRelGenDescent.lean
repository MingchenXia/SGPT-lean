import SGPT.Foundations.Analysis.Pending.AnalyticModificationSingletonFibreInverse

/-!
# Holomorphic functions descend along analytic modifications

Auxiliary for blueprint node `tok:boucksom-pushforward` (chapter `claude-tok-relgen`,
`relgen:descent`). Let `π : Z → X` be an analytic modification (`IsAnalyticModification`: proper
holomorphic, with a holomorphic inverse `s` off nowhere dense closed analytic sets `A = π⁻¹ B`,
`B ⊆ X`) and `U ⊆ X` open. Every holomorphic function `σ` on `π⁻¹ U` is `f ∘ π` for a
holomorphic function `f` on `U` (`exists_holomorphic_descent`).

Proof: `σ ∘ s` is holomorphic on `U \ B`, and bounded near every point of `B ∩ U`, because `σ`
is bounded on the compact set `π⁻¹ K` for a compact neighbourhood `K ⊆ U`; the Riemann extension
theorem across the thin set `B` (`RiemannExtensionThin.exists_local_extension`, in a chart)
extends it near every point of `B`; the extension is `x ↦ lim_{y → x, y ∉ B} σ (s y)`. Finally
`f ∘ π = σ` off the nowhere dense set `A`, hence everywhere on `π⁻¹ U` by continuity.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalRelGen

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

omit [IsComplexManifold n X] in
/-- A point is in the closure of the complement of a set with empty interior, within any
open neighbourhood. -/
theorem mem_closure_inter_compl_of_interior_eq_empty {B : Set X} (hBi : interior B = ∅)
    {O : Set X} (hO : IsOpen O) {x : X} (hx : x ∈ O) : x ∈ closure (O \ B) := by
  rw [mem_closure_iff_nhds]
  intro L hL
  have hopen : IsOpen (interior L ∩ O) := isOpen_interior.inter hO
  have hx' : x ∈ interior L ∩ O := ⟨mem_interior_iff_mem_nhds.mpr hL, hx⟩
  have hnot : ¬ interior L ∩ O ⊆ B := by
    intro hsub
    have hi := interior_maximal hsub hopen hx'
    rw [hBi] at hi
    exact hi
  obtain ⟨w, ⟨hwL, hwO⟩, hwB⟩ := not_subset.mp hnot
  exact ⟨w, interior_subset hwL, hwO, hwB⟩

/-- **Descent of holomorphic functions** along an analytic modification: a holomorphic function
on `π⁻¹ U` is the pullback of a holomorphic function on `U`. -/
theorem exists_holomorphic_descent {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {U : Set X} (hU : IsOpen U) {σ : Z → ℂ}
    (hσ : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) σ (π ⁻¹' U)) :
    ∃ f : X → ℂ, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f U ∧
      ∀ z ∈ π ⁻¹' U, f (π z) = σ z := by
  classical
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨A, B, s, hAc, _, hAi, hBc, hBa, hBi, hpre, hs, hright, hleft⟩ := hπ.2.2
  have hπc : Continuous π := hπ.1.continuous
  have hpreU : IsOpen (π ⁻¹' U) := hU.preimage hπc
  have hσc : ContinuousOn σ (π ⁻¹' U) := hσ.continuousOn
  -- the candidate off `B`
  let g : X → ℂ := fun x => σ (s x)
  have hsA : ∀ x, x ∉ B → s x ∉ A := by
    intro x hx hsx
    apply hx
    have : s x ∈ π ⁻¹' B := by rw [hpre]; exact hsx
    simpa [mem_preimage, hright x hx] using this
  have hsU : ∀ x ∈ U, x ∉ B → s x ∈ π ⁻¹' U := by
    intro x hx hxB
    change π (s x) ∈ U
    rw [hright x hxB]
    exact hx
  have hgd : ∀ x ∈ U, x ∉ B → MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g x := by
    intro x hx hxB
    have hsx : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s x :=
      (hs.contMDiffAt (hBc.isOpen_compl.mem_nhds hxB)).mdifferentiableAt (by simp)
    have hσx : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) σ (s x) :=
      (hσ (s x) (hsU x hx hxB)).mdifferentiableAt (hpreU.mem_nhds (hsU x hx hxB))
    exact hσx.comp x hsx
  -- the extension
  let f : X → ℂ := fun x => if x ∈ B then limUnder (𝓝[Bᶜ] x) g else g x
  -- local extension near a point of `B ∩ U`
  have hloc : ∀ x₀ ∈ U, x₀ ∈ B → ∃ Q : Set X, IsOpen Q ∧ x₀ ∈ Q ∧ Q ⊆ U ∧ ∃ G : X → ℂ,
      ContinuousOn G Q ∧ (∀ x ∈ Q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G x) ∧
        ∀ x ∈ Q, x ∉ B → G x = g x := by
    intro x₀ hx₀U hx₀B
    let d := complexChartAt (n := n) x₀
    let p := d.val x₀
    have hx₀d : x₀ ∈ d.val.source := mem_complexChartAt_source x₀
    have hpdt : p ∈ d.val.target := d.val.map_source hx₀d
    -- a compact neighbourhood of `x₀` in `U`, and a bound for `σ` over it
    obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hx₀U)
    have hKpre : IsCompact (π ⁻¹' K) := hπ.2.1.isCompact_preimage hKc
    obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ π ⁻¹' K, ‖σ z‖ ≤ C := by
      obtain ⟨C, hC⟩ := (hKpre.image_of_continuousOn
        (hσc.mono fun z hz => hKU hz)).isBounded.exists_norm_le
      exact ⟨C, fun z hz => hC _ ⟨z, hz, rfl⟩⟩
    obtain ⟨P⟩ := hBa x₀
    have hgne : ∃ i, ¬ ∀ᶠ w in 𝓝 p, P.generator i w = 0 := by
      by_contra hall
      push Not at hall
      have hzeros : ∀ᶠ w in 𝓝 p, ∀ i, P.generator i w = 0 :=
        Filter.eventually_all.mpr hall
      have hev : ∀ᶠ x in 𝓝 x₀, x ∈ B := by
        have hdc : ContinuousAt d.val x₀ := d.val.continuousAt hx₀d
        filter_upwards [d.val.open_source.mem_nhds hx₀d,
          hdc.eventually (P.isOpen_coordinateNeighborhood.mem_nhds
            P.center_mem_coordinateNeighborhood),
          hdc.eventually hzeros] with x hxd hxP hxzero
        exact (P.zeroLocus hxd hxP).mpr hxzero
      have hi : x₀ ∈ interior B := mem_interior_iff_mem_nhds.mpr hev
      rw [hBi] at hi
      exact hi
    obtain ⟨i, hi⟩ := hgne
    let Kint : Set X := interior K
    have hx₀K : x₀ ∈ Kint := mem_interior_iff_mem_nhds.mpr hKn
    let W : Set (ComplexModel n) :=
      (d.val.target ∩ d.val.symm ⁻¹' Kint) ∩ P.coordinateNeighborhood
    have hWo : IsOpen W :=
      (d.val.isOpen_inter_preimage_symm isOpen_interior).inter P.isOpen_coordinateNeighborhood
    have hpW : p ∈ W :=
      ⟨⟨hpdt, by change d.val.symm (d.val x₀) ∈ Kint; rwa [d.val.left_inv hx₀d]⟩,
        P.center_mem_coordinateNeighborhood⟩
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hWo p hpW
    let T : Set (ComplexModel n) := d.val.target ∩ d.val.symm ⁻¹' B
    have hTh : ∀ w ∈ ball p r, w ∈ T → P.generator i w = 0 := by
      intro w hw hwT
      have hws : d.val.symm w ∈ d.val.source := d.val.map_target (hrW hw).1.1
      have hwP : d.val (d.val.symm w) ∈ P.coordinateNeighborhood := by
        rw [d.val.right_inv (hrW hw).1.1]
        exact (hrW hw).2
      have hzero := (P.zeroLocus hws hwP).mp hwT.2 i
      rwa [d.val.right_inv (hrW hw).1.1] at hzero
    have hUT : IsOpen (ball p r \ T) := by
      have heq : ball p r \ T = ball p r ∩ (d.val.target ∩ d.val.symm ⁻¹' Bᶜ) := by
        ext w
        constructor
        · rintro ⟨hw, hwT⟩
          exact ⟨hw, (hrW hw).1.1, fun hwB => hwT ⟨(hrW hw).1.1, hwB⟩⟩
        · rintro ⟨hw, _, hwB⟩
          exact ⟨hw, fun hwT => hwB hwT.2⟩
      rw [heq]
      exact isOpen_ball.inter (d.val.isOpen_inter_preimage_symm hBc.isOpen_compl)
    let F : ComplexModel n → ℂ := fun w => g (d.val.symm w)
    have hF : DifferentiableOn ℂ F (ball p r \ T) := by
      intro w hw
      have hwdt : w ∈ d.val.target := (hrW hw.1).1.1
      have hwB : d.val.symm w ∉ B := fun hwB => hw.2 ⟨hwdt, hwB⟩
      have hwU : d.val.symm w ∈ U := hKU (interior_subset (hrW hw.1).1.2)
      have hdd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) d.val.symm w :=
        ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
          (d.val.open_target.mem_nhds hwdt)).mdifferentiableAt (by simp)
      have hcomp := (hgd _ hwU hwB).comp w hdd
      exact (mdifferentiableAt_iff_differentiableAt.mp hcomp).differentiableWithinAt
    have hFC : ∀ w ∈ ball p r \ T, ‖F w‖ ≤ C := by
      intro w hw
      have hwB : d.val.symm w ∉ B := fun hwB => hw.2 ⟨(hrW hw.1).1.1, hwB⟩
      apply hC
      change π (s (d.val.symm w)) ∈ K
      rw [hright _ hwB]
      exact interior_subset (hrW hw.1).1.2
    obtain ⟨ρ, hρ, hρr, -, G, hG, hGF⟩ :=
      RiemannExtensionThin.exists_local_extension hUT hF hr subset_rfl
        ((P.generator_holomorphic i).mono fun w hw => (hrW hw).2) hi hTh hFC
    let Q : Set X := d.val.source ∩ d.val ⁻¹' ball p ρ
    have hQo : IsOpen Q := d.val.isOpen_inter_preimage isOpen_ball
    have hx₀Q : x₀ ∈ Q := ⟨hx₀d, mem_ball_self hρ⟩
    have hQball : ∀ x ∈ Q, d.val x ∈ ball p r := fun x hx => ball_subset_ball hρr hx.2
    have hQU : Q ⊆ U := by
      intro x hx
      have h := (hrW (hQball x hx)).1.2
      change d.val.symm (d.val x) ∈ Kint at h
      rw [d.val.left_inv hx.1] at h
      exact hKU (interior_subset h)
    refine ⟨Q, hQo, hx₀Q, hQU, fun x => G (d.val x), ?_, ?_, ?_⟩
    · intro x hx
      have hGc : ContinuousAt G (d.val x) :=
        (hG.differentiableAt (isOpen_ball.mem_nhds hx.2)).continuousAt
      exact (hGc.comp (d.val.continuousAt hx.1)).continuousWithinAt
    · intro x hx
      have hdx : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) d.val x :=
        ((contMDiffOn_chart (n := ∞)).contMDiffAt
          (d.val.open_source.mem_nhds hx.1)).mdifferentiableAt (by simp)
      have hGx : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G (d.val x) :=
        (hG.differentiableAt (isOpen_ball.mem_nhds hx.2)).mdifferentiableAt
      exact hGx.comp x hdx
    · intro x hx hxB
      have hxT : d.val x ∉ T := by
        intro hxT
        apply hxB
        have h := hxT.2
        change d.val.symm (d.val x) ∈ B at h
        rwa [d.val.left_inv hx.1] at h
      have h := hGF (d.val x) ⟨hx.2, hxT⟩
      change G (d.val x) = g (d.val.symm (d.val x)) at h
      change G (d.val x) = g x
      rw [h, d.val.left_inv hx.1]
  -- `f` agrees with every local extension on its domain
  have hfG : ∀ x₀ ∈ U, x₀ ∈ B → ∃ Q : Set X, IsOpen Q ∧ x₀ ∈ Q ∧ Q ⊆ U ∧ ∃ G : X → ℂ,
      (∀ x ∈ Q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G x) ∧ EqOn f G Q := by
    intro x₀ hx₀U hx₀B
    obtain ⟨Q, hQo, hx₀Q, hQU, G, hGc, hGd, hGg⟩ := hloc x₀ hx₀U hx₀B
    refine ⟨Q, hQo, hx₀Q, hQU, G, hGd, ?_⟩
    intro x hx
    by_cases hxB : x ∈ B
    · have hne : (𝓝[Bᶜ] x).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot]
        exact closure_mono (fun y hy => hy.2)
          (mem_closure_inter_compl_of_interior_eq_empty hBi hQo hx)
      have htend : Tendsto g (𝓝[Bᶜ] x) (𝓝 (G x)) := by
        have hGx : Tendsto G (𝓝[Bᶜ] x) (𝓝 (G x)) :=
          ((hGc x hx).continuousAt (hQo.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
        refine hGx.congr' ?_
        filter_upwards [inter_mem_nhdsWithin Bᶜ (hQo.mem_nhds hx)] with y hy
        exact hGg y hy.2 hy.1
      change (if x ∈ B then limUnder (𝓝[Bᶜ] x) g else g x) = G x
      rw [if_pos hxB]
      exact htend.limUnder_eq
    · change (if x ∈ B then limUnder (𝓝[Bᶜ] x) g else g x) = G x
      rw [if_neg hxB]
      exact (hGg x hx hxB).symm
  have hfd : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f U := by
    intro x hx
    apply MDifferentiableAt.mdifferentiableWithinAt
    by_cases hxB : x ∈ B
    · obtain ⟨Q, hQo, hxQ, -, G, hGd, hfG'⟩ := hfG x hx hxB
      have heq : G =ᶠ[𝓝 x] f := by
        filter_upwards [hQo.mem_nhds hxQ] with y hy
        exact (hfG' hy).symm
      exact (hGd x hxQ).congr_of_eventuallyEq heq.symm
    · have heq : g =ᶠ[𝓝 x] f := by
        filter_upwards [hBc.isOpen_compl.mem_nhds hxB] with y hy
        change g y = if y ∈ B then limUnder (𝓝[Bᶜ] y) g else g y
        rw [if_neg hy]
      exact (hgd x hx hxB).congr_of_eventuallyEq heq.symm
  refine ⟨f, hfd, ?_⟩
  -- `f ∘ π = σ` off `A`, hence on `π⁻¹ U`
  have hoff : EqOn (fun z => f (π z)) σ (π ⁻¹' U \ A) := by
    intro z hz
    have hzB : π z ∉ B := by
      intro hB
      apply hz.2
      rw [← hpre]
      exact hB
    change (if π z ∈ B then limUnder (𝓝[Bᶜ] (π z)) g else g (π z)) = σ z
    rw [if_neg hzB]
    change σ (s (π z)) = σ z
    rw [hleft z hz.2]
  have hdense : π ⁻¹' U ⊆ closure (π ⁻¹' U \ A) := fun z hz =>
    mem_closure_inter_compl_of_interior_eq_empty hAi hpreU hz
  have hfπc : ContinuousOn (fun z => f (π z)) (π ⁻¹' U) :=
    hfd.continuousOn.comp hπc.continuousOn fun z hz => hz
  intro z hz
  exact hoff.of_subset_closure hfπc hσc sdiff_subset hdense hz

end SGPT.Okounkov.TranscendentalRelGen
