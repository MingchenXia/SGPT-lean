import SGPT.Okounkov.TranscendentalMainStatement
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSingleGenerator
import SGPT.Foundations.Analysis.Pending.MeteredDivisorWeightBounds
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Okounkov.DivisorResidualGenericZero

/-!
# Classes used by the slice formula

Source: blueprint node `tok:slice-kahler` (chapter `claude-okounkov-transcendental`, sub-lemmas
`tok-slice:pullback-class`, `tok-slice:curvature-class`, `tok-slice:kahler-shift` of
`claude-tok-slice.tex`).

Three facts about Bott--Chern classes enter the corrected item 5 of `thm:Okounkovtranmain`
(`TranscendentalMain.KahlerSliceFormulaStatement`):

* `ofRepresentative_pullback_congr'`: pullback along a holomorphic map between manifolds of
  possibly different dimensions respects Bott--Chern equivalence (`θ' = θ + dd^c h` gives
  `f^*θ' = f^*θ + dd^c (h ∘ f)`); in particular the restriction `(·)|_{Y₁}` to the first
  flag member is well defined on classes (`firstFlagRestriction_class_congr`);
* `ofRepresentative_curvature_eq`: the curvature forms of two unit metrics of the smooth
  divisor `Y₁` (`TranscendentalMain.IsFirstDivisorUnitMetric`) are cohomologous, so the class
  `{Y₁}` does not depend on the metric. Near every point the two weights are
  `log |g|² + h` and `log |u g|² + h'` with a holomorphic unit `u`, so their difference `f` is
  smooth; off `Y₁` the curvatures are `-dd^c` of the weights, and by continuity and density
  `Θ₁ = Θ₂ + dd^c f` everywhere;
* `exists_pos_forall_kahler_sub`: for a Kähler form `κ` and a closed real `(1,1)`-form `η` on
  a compact manifold, `κ - t η` is a Kähler form for all small `t > 0`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalSlice

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending

section Pullback

variable {k n : ℕ}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]

/-- Chart-smooth functions pull back to chart-smooth functions along holomorphic maps between
manifolds of possibly different dimensions. -/
theorem chartSmooth_comp' {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) {h : Y → ℝ}
    (hh : ChartSmooth (n := n) h) : ChartSmooth (n := k) (fun z => h (g z)) := by
  intro e w hw
  set d := complexChartAt (n := n) (g (e.val.symm w))
  have hwd : w ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hw, mem_complexChartAt_source _⟩
  have h1 := HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hwd
  have h2 := (hh d).contDiffAt
    (d.val.open_target.mem_nhds (HolomorphicMaps.coordinateMap_mem_target hwd))
  have h3 := ContDiffAt.comp (g := fun z => h (d.val.symm z)) w h2 h1
  refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen hg e d).mem_nhds hwd] with w' hw'
  show h (g (e.val.symm w')) = h (d.val.symm (d.val (g (e.val.symm w'))))
  rw [d.val.left_inv hw'.2]

/-- **Pullback respects Bott--Chern equivalence** along a holomorphic map between manifolds of
possibly different dimensions: `θ' = θ + dd^c h` gives `g^*θ' = g^*θ + dd^c (h ∘ g)`. -/
theorem ofRepresentative_pullback_congr' {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    {θ θ' : ClosedRealOneOneForm n Y}
    (h : RealBottChern.ofRepresentative θ' = RealBottChern.ofRepresentative θ) :
    RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg θ') =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg θ) := by
  obtain ⟨h, hh, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp h
  refine (RealBottChern.ofRepresentative_eq_iff _ _).mpr
    ⟨fun z => h (g z), chartSmooth_comp' hg hh, fun e z hz => ?_⟩
  set d := complexChartAt (n := n) (g (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hg e d
  have hddc : smoothDDC (fun y => h (g (e.val.symm y))) z =
      (smoothDDC (fun w => h (d.val.symm w))
        (HolomorphicMaps.coordinateMap g e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap g e d) z) := by
    rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
      (HolomorphicMaps.coordinateMap_contDiffOn hg e d) (hh d)
      (fun _ hy => HolomorphicMaps.coordinateMap_mem_target hy) hzd]
    apply smoothDDC_congr
    filter_upwards [hD.mem_nhds hzd] with y hy
    show h (g (e.val.symm y)) = h (d.val.symm (d.val (g (e.val.symm y))))
    rw [d.val.left_inv hy.2]
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hg _ e d hzd, SmoothRealForm.pullback_coeff hg _ e d hzd,
    hddc, heq d _ (HolomorphicMaps.coordinateMap_mem_target hzd)]
  ext v
  simp

end Pullback

/-- **The restriction to `Y₁` is defined on classes**: cohomologous forms have cohomologous
restrictions. -/
theorem firstFlagRestriction_class_congr {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    RealBottChern.ofRepresentative (TranscendentalMain.firstFlagRestriction F θ) =
      RealBottChern.ofRepresentative (TranscendentalMain.firstFlagRestriction F θ') :=
  ofRepresentative_pullback_congr' _ h

section Curvature

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

omit [IsComplexManifold (m + 1) M] in
/-- In a chart, the points off a closed set `W` with empty interior are dense in the chart
target. -/
theorem chart_target_subset_closure {W : Set M} (hW : interior W = ∅)
    (e : ComplexChart (m + 1) M) :
    e.val.target ⊆ closure (e.val.target ∩ e.val.symm ⁻¹' Wᶜ) := by
  intro z hz
  rw [mem_closure_iff]
  intro O hO hzO
  have hopen : IsOpen (e.val.symm '' (O ∩ e.val.target)) :=
    e.val.isOpen_image_symm_of_subset_target (hO.inter e.val.open_target) inter_subset_right
  have hnot : ¬ e.val.symm '' (O ∩ e.val.target) ⊆ W := by
    intro hsub
    have hmem : e.val.symm z ∈ interior W :=
      interior_mono hsub (hopen.mem_nhds ⟨z, ⟨hzO, hz⟩, rfl⟩ |> mem_interior_iff_mem_nhds.mpr)
    rw [hW] at hmem
    exact hmem
  obtain ⟨p, ⟨z', ⟨hz'O, hz't⟩, rfl⟩, hpW⟩ := not_subset.mp hnot
  exact ⟨z', hz'O, hz't, hpW⟩

/-- Two functions continuous at `y` that agree off a set `W` with empty interior, near `y`,
agree at `y`. -/
theorem eq_of_continuousAt_of_eventuallyEq_off {X : Type*} [TopologicalSpace X] {W : Set X}
    (hW : interior W = ∅) {F G : X → ℝ} {y : X} (hF : ContinuousAt F y) (hG : ContinuousAt G y)
    (h : ∀ᶠ z in 𝓝 y, z ∉ W → F z = G z) : F y = G y := by
  have hcl : y ∈ closure Wᶜ := by
    rw [closure_compl, hW]
    exact mem_compl (notMem_empty y)
  have : (𝓝[Wᶜ] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have h1 : Tendsto F (𝓝[Wᶜ] y) (𝓝 (F y)) := hF.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto G (𝓝[Wᶜ] y) (𝓝 (G y)) := hG.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique_of_eventuallyEq h1 h2 ?_
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z hz hzW
  exact hz hzW

/-- `a + G + b = G + c + (a + b - c)` in `EReal`, including `G = ±∞`. -/
theorem ereal_coe_add_add_coe (G : EReal) (a b c : ℝ) :
    (a : EReal) + G + (b : EReal) = G + (c : EReal) + ((a + b - c : ℝ) : EReal) := by
  induction G using EReal.rec with
  | bot => simp
  | top => simp only [EReal.coe_add_top, EReal.top_add_coe]
  | coe G =>
      simp only [← EReal.coe_add]
      congr 1
      ring

/-- **Local form of the difference of two unit weights**: near every point the weights of two
metrics of the same smooth divisor differ by a chart-smooth real function. -/
theorem exists_local_weight_difference {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    {D₁ D₂ : EffectiveDivisor (m + 1) M} (hD : D₁.ideal = D₂.ideal)
    {E₁ E₂ : MeteredEffectiveQDivisor (m + 1) M} (hE₁W : E₁.support = W)
    (h₁ : DivisorMetric.IsDivisorMetric D₁ E₁) (h₂ : DivisorMetric.IsDivisorMetric D₂ E₂)
    (x : M) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ F : M → ℝ,
      (∀ e : ComplexChart (m + 1) M,
        ContDiffOn ℝ ∞ (fun z => F (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
      ∀ y ∈ V, E₂.weight y = E₁.weight y + (F y : EReal) := by
  obtain ⟨V₁, hV₁, hxV₁, g₁, hg₁d, hgen₁, k₁, hk₁, hw₁⟩ := h₁ x
  obtain ⟨V₂, hV₂, hxV₂, g₂, hg₂d, hgen₂, k₂, hk₂, hw₂⟩ := h₂ x
  have hint : interior W = ∅ := SGPT.Okounkov.smooth_divisor_interior_eq_empty hW
  have hg₁nz : ∀ O : Set M, IsOpen O → O ⊆ V₁ → O.Nonempty → ∃ y ∈ O, g₁ y ≠ 0 := by
    intro O hO hOV hne
    have hnot : ¬ O ⊆ W := by
      intro hsub
      obtain ⟨y, hy⟩ := hne
      have : y ∈ interior W := interior_mono hsub (hO.interior_eq.symm ▸ hy)
      rw [hint] at this
      exact this
    obtain ⟨y, hyO, hyW⟩ := not_subset.mp hnot
    refine ⟨y, hyO, fun h0 => hyW ?_⟩
    rw [← hE₁W]
    show E₁.weight y = ⊥
    rw [hw₁ y (hOV hyO)]
    have : generatorLog (fun _ : Fin 1 => g₁) y = ⊥ :=
      (MeteredDivisorSingleGenerator.singleLog_eq_bot_iff g₁ y).mpr h0
    rw [this, EReal.bot_add]
  have hgen₂' : ∀ y ∈ V₂, ∀ f, D₁.ideal.mem y f ↔ IsInSpanAt (n := m + 1) (· = g₂) y f := by
    rw [hD]; exact hgen₂
  obtain ⟨V, u, hV, hxV, hVsub, hud, hu0, hgu⟩ :=
    DivisorMetric.exists_unit_of_generators hV₁ hV₂ hg₁d hg₂d hg₁nz hgen₁ hgen₂' hxV₁ hxV₂
  refine ⟨V, hV, hxV, fun y => Real.log (‖u y‖ ^ 2) + k₂ y - k₁ y, ?_, ?_⟩
  · intro e
    have hudiff : MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) u V :=
      fun y hy => (hud y hy).mdifferentiableWithinAt
    have hU : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hV
    have hlog : ContDiffOn ℝ ∞ (fun z => Real.log (‖u (e.val.symm z)‖ ^ 2))
        (e.val.target ∩ e.val.symm ⁻¹' V) := by
      intro z hz
      have h := MeteredDivisorSmoothOffSupport.contDiffAt_log_normSq hU
        (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hudiff) hz (hu0 _ hz.2)
      refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards with w
      rw [Complex.normSq_eq_norm_sq]
    have hk₁' := (hk₁ e).mono (inter_subset_inter_right _ (preimage_mono
      (hVsub.trans inter_subset_left)))
    have hk₂' := (hk₂ e).mono (inter_subset_inter_right _ (preimage_mono
      (hVsub.trans inter_subset_right)))
    exact (hlog.add hk₂').sub hk₁'
  · intro y hy
    have hy₁ := (hVsub hy).1
    have hy₂ := (hVsub hy).2
    rw [hw₂ y hy₂, hw₁ y hy₁]
    have hprod : generatorLog (fun _ : Fin 1 => g₂) y =
        ((Real.log (‖u y‖ ^ 2) : ℝ) : EReal) + generatorLog (fun _ : Fin 1 => g₁) y := by
      have hval : generatorLog (fun _ : Fin 1 => g₂) y =
          MeteredDivisorSingleGenerator.singleLog (u * g₁) y := by
        show MeteredDivisorSingleGenerator.singleLog g₂ y = _
        rw [MeteredDivisorSingleGenerator.singleLog_eq_log,
          MeteredDivisorSingleGenerator.singleLog_eq_log, hgu y hy]
        rfl
      rw [hval, MeteredDivisorSingleGenerator.singleLog_mul,
        MeteredDivisorSingleGenerator.singleLog]
      congr 1
      exact MeteredDivisorWeightBounds.generatorLog_single_eq_coe (hu0 y hy)
    rw [hprod]
    exact ereal_coe_add_add_coe _ _ _ _

/-- **The two unit weights differ by a global chart-smooth function**: `ψ₂ = ψ₁ + f`. -/
theorem exists_chartSmooth_weight_difference {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    {D₁ D₂ : EffectiveDivisor (m + 1) M} (hD : D₁.ideal = D₂.ideal)
    {E₁ E₂ : MeteredEffectiveQDivisor (m + 1) M} (hE₁W : E₁.support = W)
    (h₁ : DivisorMetric.IsDivisorMetric D₁ E₁) (h₂ : DivisorMetric.IsDivisorMetric D₂ E₂) :
    ∃ f : M → ℝ, ChartSmooth (n := m + 1) f ∧ ∀ x, E₂.weight x = E₁.weight x + (f x : EReal) := by
  classical
  choose V hV hxV F hF hFw using exists_local_weight_difference hW hD hE₁W h₁ h₂
  have hint : interior W = ∅ := SGPT.Okounkov.smooth_divisor_interior_eq_empty hW
  have hcont : ∀ x, ∀ y ∈ V x, ContinuousAt (F x) y := fun x y hy =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (hV x) (hF x) hy
  have hagree : ∀ x, ∀ y ∈ V x, F y y = F x y := by
    intro x y hy
    refine eq_of_continuousAt_of_eventuallyEq_off hint (hcont y y (hxV y)) (hcont x y hy) ?_
    filter_upwards [(hV y).mem_nhds (hxV y), (hV x).mem_nhds hy] with z hz1 hz2 hzW
    have hzE : z ∉ E₁.support := by rw [hE₁W]; exact hzW
    obtain ⟨G, -, hGeq⟩ :=
      MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E₁ hzE
    have hG := Filter.Eventually.self_of_nhds hGeq
    have e1 := hFw y z hz1
    have e2 := hFw x z hz2
    rw [e1, hG, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff] at e2
    linarith
  refine ⟨fun x => F x x, ?_, fun x => by rw [hFw x x (hxV x)]⟩
  intro e
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  refine ⟨e.val.target ∩ e.val.symm ⁻¹' V (e.val.symm z),
    e.val.isOpen_inter_preimage_symm (hV _), ⟨hz, hxV _⟩, ?_⟩
  refine ((hF (e.val.symm z) e).mono inter_subset_right).congr fun w hw => ?_
  exact hagree _ _ hw.2.2

/-- **The class `{Y₁}` does not depend on the unit metric**: the curvature forms of two metrics
of the same smooth divisor are cohomologous (`Θ₁ = Θ₂ + dd^c f`, `f = ψ₂ - ψ₁`). -/
theorem ofRepresentative_curvature_eq_of_divisorMetric {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    {D₁ D₂ : EffectiveDivisor (m + 1) M} (hD : D₁.ideal = D₂.ideal)
    {E₁ E₂ : MeteredEffectiveQDivisor (m + 1) M} (hE₁W : E₁.support = W)
    (hE₂W : E₂.support = W)
    (h₁ : DivisorMetric.IsDivisorMetric D₁ E₁) (h₂ : DivisorMetric.IsDivisorMetric D₂ E₂) :
    RealBottChern.ofRepresentative E₁.curvature = RealBottChern.ofRepresentative E₂.curvature := by
  obtain ⟨f, hf, hfw⟩ := exists_chartSmooth_weight_difference hW hD hE₁W h₁ h₂
  have hint : interior W = ∅ := SGPT.Okounkov.smooth_divisor_interior_eq_empty hW
  refine ((RealBottChern.ofRepresentative_eq_iff _ _).mpr ⟨f, hf, fun e z hz => ?_⟩).symm
  have hoff : EqOn (fun z => E₁.curvature.val.coeff e z)
      (fun z => E₂.curvature.val.coeff e z + smoothDDC (fun y => f (e.val.symm y)) z)
      (e.val.target ∩ e.val.symm ⁻¹' Wᶜ) := by
    rintro z₀ ⟨hz₀, hz₀W⟩
    have hx : e.val.symm z₀ ∈ e.val.source := e.val.map_target hz₀
    have hx₁ : e.val.symm z₀ ∉ E₁.support := by rw [hE₁W]; exact hz₀W
    have hx₂ : e.val.symm z₀ ∉ E₂.support := by rw [hE₂W]; exact hz₀W
    obtain ⟨W₁, hzW₁, hpot₁⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E₁ hx₁ e hx
    obtain ⟨W₂, hzW₂, hpot₂⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E₂ hx₂ e hx
    rw [e.val.right_inv hz₀] at hzW₁ hzW₂
    have hO : IsOpen (W₁ ∩ W₂) := hpot₁.1.inter hpot₂.1
    have hloc : (fun y => f (e.val.symm y)) =ᶠ[𝓝 z₀]
        fun ζ => (E₂.weight (e.val.symm ζ)).toReal - (E₁.weight (e.val.symm ζ)).toReal := by
      filter_upwards [(e.val.isOpen_inter_preimage_symm hW.1.isOpen_compl).mem_nhds
        ⟨hz₀, hz₀W⟩] with ζ hζ
      have hζE : e.val.symm ζ ∉ E₁.support := by rw [hE₁W]; exact hζ.2
      obtain ⟨G, -, hGeq⟩ :=
        MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E₁ hζE
      have hG := Filter.Eventually.self_of_nhds hGeq
      rw [hfw, hG, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
      ring
    have hsub := smoothDDC_sub hO (hpot₂.2.2.1.mono inter_subset_right)
      (hpot₁.2.2.1.mono inter_subset_left) (z := z₀) ⟨hzW₁, hzW₂⟩
    have hd₁ := hpot₁.2.2.2 hzW₁
    have hd₂ := hpot₂.2.2.2 hzW₂
    simp only [ClosedRealOneOneForm.coeff_neg] at hd₁ hd₂
    show E₁.curvature.val.coeff e z₀ =
      E₂.curvature.val.coeff e z₀ + smoothDDC (fun y => f (e.val.symm y)) z₀
    rw [smoothDDC_congr hloc, hsub, hd₁, hd₂]
    abel
  refine hoff.of_subset_closure ((E₁.curvature.val.smooth e).continuousOn)
    (((E₂.curvature.val.smooth e).continuousOn).add
      ((LogWeightFactorization.smoothDDC_contDiffOn e.val.open_target (hf e)).continuousOn))
    inter_subset_left (chart_target_subset_closure hint e) hz

/-- **The class `{Y₁}` does not depend on the unit metric** (`IsFirstDivisorUnitMetric`). -/
theorem ofRepresentative_curvature_eq {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
    {E₁ E₂ : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (h₁ : TranscendentalMain.IsFirstDivisorUnitMetric F E₁)
    (h₂ : TranscendentalMain.IsFirstDivisorUnitMetric F E₂) :
    RealBottChern.ofRepresentative E₁.curvature = RealBottChern.ofRepresentative E₂.curvature := by
  obtain ⟨D₁, hD₁, hE₁W, hm₁⟩ := h₁
  obtain ⟨D₂, hD₂, hE₂W, hm₂⟩ := h₂
  exact ofRepresentative_curvature_eq_of_divisorMetric F.firstDivisor (hD₁.trans hD₂.symm)
    hE₁W hE₂W hm₁ hm₂

end Curvature

end SGPT.Okounkov.TranscendentalSlice

namespace SGPT.Okounkov.TranscendentalSlice

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- **Small perturbations of a Kähler form are Kähler**: for a Kähler form `κ` and a closed
real `(1,1)`-form `η` on a compact manifold there is `t₀ > 0` such that `κ - t η` is a Kähler
form for every `t ∈ (0, t₀)`. -/
theorem exists_pos_forall_kahler_sub {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    (κ : KahlerBackground n M) (η : ClosedRealOneOneForm n M) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t ∈ Ioo 0 t₀, ∃ κ' : KahlerBackground n M, κ'.form = κ.form - t • η := by
  obtain ⟨A, hA, hK⟩ := KahlerDomination.exists_pos_isKahler_add_smul κ (-η)
  refine ⟨1 / (A + 1), by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := ht.1
  have h1 : t * (A + 1) < 1 := (lt_div_iff₀ (by positivity)).mp ht.2
  have hAle : A ≤ t⁻¹ - 1 := by
    have h2 := mul_pos (sub_pos.mpr h1) (inv_pos.mpr ht0)
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
    nlinarith
  have hsemi : (-η + (t⁻¹ - 1) • κ.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_add_smul_mono κ.isSemipositive hAle
      (KahlerBackground.isSemipositive ⟨_, hK⟩)
  have hkah := KahlerDomination.isKahler_add_smul_succ κ hsemi
  refine ⟨KahlerBackground.smul ht0 ⟨_, hkah⟩, ?_⟩
  rw [KahlerBackground.smul_form]
  show t • (-η + (t⁻¹ - 1 + 1) • κ.form) = κ.form - t • η
  rw [sub_add_cancel, smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul, smul_neg]
  abel

end SGPT.Okounkov.TranscendentalSlice
