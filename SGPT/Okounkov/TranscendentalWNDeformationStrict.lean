import SGPT.Okounkov.TranscendentalWNDeformationDivisorClass
import SGPT.Okounkov.TranscendentalWNDeformationBeta

/-!
# The metrics of `𝒪(X')` and `𝒪(Z̃)` on the deformation to the normal cone

Blueprint `tok-wn-def:strict-metric` and `tok-wn-def:z-metric` (`claude-tok-wn-def`); WN21 §1.1
(`{X'} = {X₀} - {ℰ}`, `(π_X μ)^*{Z} = {Z̃} + {ℰ}`), written with explicit weights.

Let `W = |s_Z|²_h N₁ + N₀` (`baseExceptionalWeight`), so that `log W ∘ μ` is the weight of the
metric of `𝒪(ℰ)` (`exists_exceptionalMetric_weight`).

* `strictWeight`: the continuous extension across `ℰ` of `N₀ ∘ π_{ℙ¹} ∘ μ / W ∘ μ`
  (`= |τ|² / (|s_Z|²_h + |τ|²)` off `ℰ ∪ X_∞`).  Near `ℰ`, `τ ∘ μ = b σ` and `W ∘ μ = |σ|² U'`
  give `strictWeight = |b|² N₁ ∘ μ / U'` (`exists_strictWeight_factor`), so it has local
  factorizations `|holomorphic|² · (smooth > 0)` (`strictFactorization`), and
  `log strictWeight` is `-Θ`-psh for the glued form `Θ = ddᶜ log strictWeight`; off the central
  fibre `X₀`, `Θ = -(π_{ℙ¹} μ)^* ω_FS + η_ℰ` (`ddᶜ log N₀ = -ω_FS` off `0`), hence everywhere
  (`strictFactorization_closedForm_coeff`): `log strictWeight` is the weight of a metric of
  `𝒪(X')` with curvature `(π_{ℙ¹} μ)^* ω_FS - η_ℰ`.
* `zStrictWeight`: the continuous extension of `|s_Z|²_h ∘ π_X ∘ μ / W ∘ μ`; near every point
  `g ∘ π_X ∘ μ = a σ` gives `zStrictWeight = |a|² e^{h} / U'`, and its glued form is
  `-(π_X μ)^* η + η_ℰ` (`zStrictFactorization_closedForm_coeff`): `log zStrictWeight` is the
  weight of a metric of `𝒪(Z̃)`, `Z̃` the strict transform of `Z × ℙ¹`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FactorizedWeightForm
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric
open SGPT.Okounkov.TranscendentalMain

/-! ### Generalities -/

/-- A function which, off a set `A` with empty interior, agrees near `y` with a function `G`
continuous near `y` has `limUnder (𝓝[Aᶜ] y) f = G y`. -/
theorem limUnder_nhdsWithin_compl_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [Nonempty Y] {A : Set X} (hA : interior A = ∅) {f G : X → Y} {O : Set X}
    (hO : IsOpen O)
    (hG : ContinuousOn G O) (hfG : ∀ y ∈ O, y ∉ A → f y = G y) {y : X} (hy : y ∈ O) :
    limUnder (𝓝[Aᶜ] y) f = G y := by
  have hcl : y ∈ closure Aᶜ := by
    rw [closure_compl, hA]
    exact notMem_empty y
  have : (𝓝[Aᶜ] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hGt : Tendsto G (𝓝[Aᶜ] y) (𝓝 (G y)) :=
    ((hG y hy).continuousAt (hO.mem_nhds hy)).mono_left nhdsWithin_le_nhds
  have heq : G =ᶠ[𝓝[Aᶜ] y] f := by
    filter_upwards [nhdsWithin_le_nhds (hO.mem_nhds hy), self_mem_nhdsWithin] with z hzO hzA
    exact (hfG z hzO hzA).symm
  exact (hGt.congr' heq).limUnder_eq

section Factorization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A factorized weight is continuous. -/
theorem WeightFactorization.continuousAt {U : M → ℝ} (Fw : WeightFactorization n U) (x : M) :
    ContinuousAt U x := by
  have hs : ContinuousAt (Fw.smoothPart x) x :=
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (Fw.isOpen_domain x)
      (Fw.smooth x) (Fw.mem_domain x)
  have hg : ContinuousAt (Fw.gen x) x :=
    (Fw.gen_mdifferentiable x x (Fw.mem_domain x)).continuousAt
  have h := (Complex.continuous_normSq.continuousAt.comp hg).mul hs
  refine h.congr ?_
  filter_upwards [(Fw.isOpen_domain x).mem_nhds (Fw.mem_domain x)] with y hy
  exact (Fw.factor x y hy).symm

/-- **Where the weight itself is smooth and positive, the glued form is `ddᶜ log U`.** -/
theorem WeightFactorization.closedForm_coeff_eq_of_pos {U : M → ℝ}
    (Fw : WeightFactorization n U) {V : Set M} (hV : IsOpen V)
    (hUs : ∀ e : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun u => U (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' V))
    (hUpos : ∀ y ∈ V, 0 < U y) (e : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (huV : e.val.symm u ∈ V) :
    Fw.closedForm.val.coeff e u = smoothDDC (fun w => Real.log (U (e.val.symm w))) u := by
  set x := e.val.symm u with hx
  rw [(Fw.closedForm_coeff_eventuallyEq x e hu (Fw.mem_domain x)).self_of_nhds]
  set S := e.val.target ∩ e.val.symm ⁻¹' (Fw.domain x ∩ V) with hS_def
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm ((Fw.isOpen_domain x).inter hV)
  have huS : u ∈ S := ⟨hu, Fw.mem_domain x, huV⟩
  have hS1 : S ⊆ e.val.target ∩ e.val.symm ⁻¹' Fw.domain x := fun w hw => ⟨hw.1, hw.2.1⟩
  have hS2 : S ⊆ e.val.target ∩ e.val.symm ⁻¹' V := fun w hw => ⟨hw.1, hw.2.2⟩
  refine LogWeightFactorization.smoothDDC_log_eq_of_normSq_mul_eq hS ((Fw.smooth x e).mono hS1)
    ((hUs e).mono hS2) (fun w hw => Fw.pos x _ hw.2.1) (fun w hw => hUpos _ hw.2.2)
    (h₁ := fun w => Fw.gen x (e.val.symm w)) (h₂ := fun _ => 1)
    (fun w hw => (differentiableAt_comp_chart_symm e hw.1
      (Fw.gen_mdifferentiable x _ hw.2.1)).differentiableWithinAt)
    (differentiableOn_const 1) (fun w hw => ?_) ?_ huS
  · simp only [map_one, one_mul]
    exact (Fw.factor x _ hw.2.1).symm
  · intro w hw
    refine subset_closure ⟨hw, ?_⟩
    exact Fw.gen_ne_zero_of hw.2.1 (hUpos _ hw.2.2).ne'

end Factorization

/-! ### The Fubini--Study form has the local potentials `-log N₀` -/

/-- **`-log N₀` is a local potential of `ω_FS` where `N₀ > 0`**, in every chart of `ℙ¹`. -/
theorem isSmoothLocalPotential_neg_log_projectiveWeight_zero (d : ComplexChart 1 ProjectiveLine) :
    IsSmoothLocalPotential projectiveNativeFSClosedForm.val d
      (d.val.target ∩ {w | 0 < projectiveWeight 0 (d.val.symm w)})
      (fun w => -Real.log (projectiveWeight 0 (d.val.symm w))) := by
  rcases d with ⟨dv, hdv⟩
  obtain ⟨b, rfl⟩ := (mem_projectiveNativeAtlas_iff dv).mp hdv
  have hc : ContDiff ℝ ∞ (fun w => projectiveWeight 0 ((projectiveModelChart b).symm w)) :=
    contDiff_projectiveWeight_chart 0 b
  have hS : IsOpen ((projectiveModelChart b).target ∩
      {w | 0 < projectiveWeight 0 ((projectiveModelChart b).symm w)}) :=
    (projectiveModelChart b).open_target.inter (isOpen_lt continuous_const hc.continuous)
  have hsm : ContDiffOn ℝ ∞ (fun w => -Real.log (projectiveWeight 0
      ((projectiveModelChart b).symm w))) ((projectiveModelChart b).target ∩
        {w | 0 < projectiveWeight 0 ((projectiveModelChart b).symm w)}) :=
    (hc.contDiffOn.log fun w hw => hw.2.ne').neg
  refine ⟨hS, inter_subset_left, hsm, fun w hw => ?_⟩
  change _ = smoothDDC projectiveFSPotential w
  have hN : ∀ v : ComplexModel 1, projectiveWeight 0 ((projectiveModelChart b).symm v) =
      ‖projectiveAffineLift b v 0‖ ^ 2 /
        (‖projectiveAffineLift b v 0‖ ^ 2 + ‖projectiveAffineLift b v 1‖ ^ 2) :=
    projectiveWeight_chart_symm 0 b
  cases b
  · -- the finite chart: `N₀ = |τ|² / (1 + |τ|²)`
    have hlift : ∀ v : ComplexModel 1, projectiveAffineLift false v =
        ![projectiveModelEquiv.symm v, 1] := fun v => by simp [projectiveAffineLift]
    have heq :
        (fun v => -Real.log (projectiveWeight 0 ((projectiveModelChart false).symm v))) =ᶠ[𝓝 w]
          fun v => projectiveFSPotential v -
            Real.log (Complex.normSq (projectiveModelEquiv.symm v)) := by
      filter_upwards [hS.mem_nhds hw] with v hv
      have hv2 := hv.2
      simp only [mem_ofPred_eq, hN, hlift] at hv2 ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_one, one_pow] at hv2 ⊢
      have hne : 0 < ‖projectiveModelEquiv.symm v‖ ^ 2 := by
        by_contra h0
        have h0' : ‖projectiveModelEquiv.symm v‖ ^ 2 = 0 := le_antisymm (not_lt.mp h0) (sq_nonneg _)
        rw [h0', zero_div] at hv2
        exact lt_irrefl 0 hv2
      rw [projectiveFSPotential_eq, ← projectiveModelEquiv_symm_apply, Complex.normSq_eq_norm_sq,
        Real.log_div hne.ne' (by positivity), add_comm (1 : ℝ)]
      ring
    have hw' : w ∈ projectiveModelPunctured := by
      have hv2 := hw.2
      simp only [mem_ofPred_eq, hN, hlift, Matrix.cons_val_zero, Matrix.cons_val_one, norm_one,
        one_pow] at hv2
      intro h0
      rw [h0, norm_zero] at hv2
      simp at hv2
    have hzero :
        smoothDDC (fun v => Real.log (Complex.normSq (projectiveModelEquiv.symm v))) w = 0 :=
      Pending.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
        (Eventually.of_forall fun _ =>
          projectiveModelEquiv.symm.toContinuousLinearMap.differentiableAt) hw'
    rw [smoothDDC_congr heq, PositiveClasses.smoothDDC_sub isOpen_projectiveModelPunctured
      contDiff_projectiveFSPotential.contDiffOn contDiffOn_projectiveModel_logNormSq hw',
      hzero, sub_zero]
  · -- the chart at `∞`: `N₀ = 1 / (1 + |τ⁻¹|²)`
    have hlift : ∀ v : ComplexModel 1, projectiveAffineLift true v =
        ![1, projectiveModelEquiv.symm v] := fun v => by simp [projectiveAffineLift]
    have heq : (fun v => -Real.log (projectiveWeight 0 ((projectiveModelChart true).symm v))) =
        projectiveFSPotential := by
      funext v
      simp only [hN, hlift, Matrix.cons_val_zero, Matrix.cons_val_one, norm_one, one_pow]
      rw [projectiveFSPotential, Complex.normSq_eq_norm_sq, one_div, Real.log_inv, neg_neg]
    rw [heq]

/-- **The pulled-back Fubini--Study form is `-ddᶜ log N₀ ∘ f`** where `N₀ ∘ f > 0`, along any
holomorphic map `f` to `ℙ¹`. -/
theorem pullback_projectiveFS_coeff {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] {f : V → ProjectiveLine}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel 1) ∞ f) (e : ComplexChart k V)
    {u : ComplexModel k} (hu : u ∈ e.val.target) (hN : 0 < projectiveWeight 0 (f (e.val.symm u))) :
    (ClosedRealOneOneForm.pullback hf projectiveNativeFSClosedForm).val.coeff e u =
      smoothDDC (fun w => -Real.log (projectiveWeight 0 (f (e.val.symm w)))) u := by
  set d := complexChartAt (n := 1) (f (e.val.symm u))
  have hzd : u ∈ coordinateDomain f e d :=
    ⟨hu, show f (e.val.symm u) ∈ d.val.source from mem_complexChartAt_source (n := 1) _⟩
  have hpot := isSmoothLocalPotential_neg_log_projectiveWeight_zero d
  have hpull := isSmoothLocalPotential_pullback hf e hpot
  have hzW : u ∈ potentialDomain f e d
      (d.val.target ∩ {w | 0 < projectiveWeight 0 (d.val.symm w)}) := by
    refine ⟨hzd, coordinateMap_mem_target hzd, ?_⟩
    show 0 < projectiveWeight 0 (d.val.symm (d.val (f (e.val.symm u))))
    rw [d.val.left_inv (mem_complexChartAt_source (n := 1) _)]
    exact hN
  have hρ : (fun w => -Real.log (projectiveWeight 0 (d.val.symm w))) ∘ coordinateMap f e d =ᶠ[𝓝 u]
      fun w => -Real.log (projectiveWeight 0 (f (e.val.symm w))) := by
    filter_upwards [(coordinateDomain_isOpen hf e d).mem_nhds hzd] with w hw
    show -Real.log (projectiveWeight 0 (d.val.symm (d.val (f (e.val.symm w))))) = _
    rw [d.val.left_inv hw.2]
  have h1 := hpull.2.2.2 hzW
  rw [smoothDDC_congr hρ] at h1
  rw [ClosedRealOneOneForm.pullback_val, ← h1]

/-! ### Density facts on the deformation -/

section Deformation

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

omit [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem exists_mem_notMem_of_interior_eq_empty {A W : Set 𝒳} (hA : interior A = ∅)
    (hW : IsOpen W) (hne : W.Nonempty) : ∃ y ∈ W, y ∉ A := by
  by_contra h
  push Not at h
  obtain ⟨y, hy⟩ := hne
  have := interior_maximal h hW hy
  rw [hA] at this
  exact this

/-- `X₀ = X' ∪ ℰ` has empty interior. -/
theorem interior_centralFibre (hμ : IsNormalConeDeformation F μ) :
    interior (centralFibre F μ) = ∅ := by
  rw [centralFibre_eq_union F hμ, interior_union_isClosed_of_interior_empty
    (isClosed_strictCentralFibre F) (interior_exceptionalSet F hμ)]
  exact interior_eq_empty_of_regularAtDim (by omega) fun _ hz =>
    regularAtDim_strictCentralFibre F hμ hz

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem isClosed_centralFibre (hμ : IsNormalConeDeformation F μ) :
    IsClosed (centralFibre F μ) :=
  (isClosed_centralBase F).preimage hμ.continuous

omit [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem mem_centralFibre_iff {y : 𝒳} : y ∈ centralFibre F μ ↔ (μ y).2 = projectiveZero :=
  mem_centralBase_iff F

omit [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem notMem_exceptionalSet_of_notMem_centralFibre {y : 𝒳} (hy : y ∉ centralFibre F μ) :
    y ∉ exceptionalSet F μ := fun h => hy (deformationCentre_subset_centralBase F h)

/-- **Every nonempty open subset of `𝒳` contains a point off `X₀` lying over `X \ Z`** (through
the sections `x ↦ μ⁻¹(x, τ)`, `τ ≠ 0`). -/
theorem exists_mem_proj_notMem_firstFlag (hμ : IsNormalConeDeformation F μ) {W : Set 𝒳}
    (hW : IsOpen W) (hne : W.Nonempty) (P : Set F.carrier)
    (hPd : ∀ V : Set F.carrier, IsOpen V → V.Nonempty → (V ∩ P).Nonempty) :
    ∃ y ∈ W, (μ y).1 ∈ P ∧ (μ y).2 ≠ projectiveZero := by
  obtain ⟨z, hzW, hzX⟩ := exists_mem_notMem_of_interior_eq_empty (interior_centralFibre F hμ)
    hW hne
  have hp : (μ z).2 ≠ projectiveZero := fun h => hzX ((mem_centralFibre_iff F).mpr h)
  obtain ⟨s, hs, hμs, -⟩ := exists_fibreSection F hμ hp
  have hzC : μ (s (μ z).1) ∉ deformationCentre F := by
    rw [hμs]
    exact fun h => hp ((mem_deformationCentre_iff F).mp h).2
  have hsz : s (μ z).1 = z := eq_of_map_eq_of_notMem F hμ hzC (by rw [hμs])
  obtain ⟨x, hxW, hxP⟩ := hPd (s ⁻¹' W) (hW.preimage hs.continuous) ⟨(μ z).1, by
    show s (μ z).1 ∈ W
    rw [hsz]
    exact hzW⟩
  refine ⟨s x, hxW, ?_, ?_⟩
  · rw [hμs]; exact hxP
  · rw [hμs]; exact hp

/-- Open sets of `X` meet `X \ Z`. -/
theorem inter_compl_firstFlag_nonempty {V : Set F.carrier} (hV : IsOpen V) (hne : V.Nonempty) :
    (V ∩ (F.flag (1 : Fin (m + 2)))ᶜ).Nonempty := by
  obtain ⟨y, hyV, hyZ⟩ := exists_mem_notMem_of_interior_eq_empty (interior_firstFlag F) hV hne
  exact ⟨y, hyV, hyZ⟩

/-- `μ⁻¹(Z × ℙ¹)` has empty interior. -/
theorem interior_preimage_firstFlag (hμ : IsNormalConeDeformation F μ) :
    interior ((fun y => (μ y).1) ⁻¹' F.flag (1 : Fin (m + 2))) = ∅ := by
  apply subset_empty_iff.mp
  intro y hy
  obtain ⟨z, hz, hzZ, -⟩ := exists_mem_proj_notMem_firstFlag F hμ isOpen_interior ⟨y, hy⟩
    _ (fun V hV hne => inter_compl_firstFlag_nonempty F hV hne)
  exact hzZ (show z ∈ (fun y => (μ y).1) ⁻¹' F.flag (1 : Fin (m + 2)) from interior_subset hz)

end Deformation

/-! ### The weight of the strict transform `X'` -/

section Strict

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **The weight of `𝒪(X')`**: the continuous extension across `ℰ` of `N₀ ∘ π_{ℙ¹} ∘ μ / W ∘ μ`. -/
def strictWeight (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (μ : 𝒳 → F.carrier × ProjectiveLine) (z : 𝒳) : ℝ :=
  limUnder (𝓝[(exceptionalSet F μ)ᶜ] z)
    (fun y => projectiveWeight 0 (μ y).2 / baseExceptionalWeight F E (μ y))

/-- **The weight of `𝒪(Z̃)`**, `Z̃` the strict transform of `Z × ℙ¹`: the continuous extension
across `ℰ` of `|s_Z|²_h ∘ π_X ∘ μ / W ∘ μ`. -/
def zStrictWeight (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (μ : 𝒳 → F.carrier × ProjectiveLine) (z : 𝒳) : ℝ :=
  limUnder (𝓝[(exceptionalSet F μ)ᶜ] z)
    (fun y => (EReal.exp (E.weight (μ y).1)).toReal / baseExceptionalWeight F E (μ y))

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem chartSmooth_continuous {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {h : M → ℝ}
    (hh : ChartSmooth (n := n) h) : Continuous h :=
  continuous_iff_continuousAt.mpr fun x =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn isOpen_univ
      (fun e => (hh e).mono inter_subset_left) (mem_univ x)

variable {F} in
theorem chartSmooth_projectiveWeight_comp (hμ : IsNormalConeDeformation F μ) (i : Fin 2) :
    ChartSmooth (n := m + 1 + 1) (fun y => projectiveWeight i (μ y).2) :=
  ProductTestForms.chartSmooth_comp (contMDiff_deformationProjP1 F hμ.contMDiff)
    (fun e => contDiffOn_projectiveWeight i e)

variable {F} in
theorem chartSmooth_baseExceptionalWeight_comp (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    ChartSmooth (n := m + 1 + 1) (fun y => baseExceptionalWeight F E (μ y)) :=
  ProductTestForms.chartSmooth_comp hμ.contMDiff (chartSmooth_baseExceptionalWeight F hE)

variable {F} in
theorem chartSmooth_exp_weight_comp (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    ChartSmooth (n := m + 1 + 1) (fun y => (EReal.exp (E.weight (μ y).1)).toReal) :=
  ProductTestForms.chartSmooth_comp (contMDiff_deformationProjX F hμ.contMDiff)
    (chartSmooth_exp_weight F hE)

theorem projectiveWeight_zero_pos {p : ProjectiveLine} (hp : p ≠ projectiveZero) :
    0 < projectiveWeight 0 p := by
  have h0 : p.rep 0 ≠ 0 := fun h => hp (eq_projectiveZero_of_rep_zero h)
  exact div_pos (by positivity) (normSq_add_pos _ p.rep_nonzero)

/-- Off `ℰ`, `strictWeight = N₀ ∘ π_{ℙ¹} ∘ μ / W ∘ μ`. -/
theorem strictWeight_eq_of_notMem (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {y : 𝒳} (hy : y ∉ exceptionalSet F μ) :
    strictWeight F E μ y = projectiveWeight 0 (μ y).2 / baseExceptionalWeight F E (μ y) := by
  refine limUnder_nhdsWithin_compl_eq (interior_exceptionalSet F hμ)
    (isClosed_exceptionalSet F hμ).isOpen_compl ?_ (fun _ _ _ => rfl) hy
  exact (chartSmooth_continuous (chartSmooth_projectiveWeight_comp hμ 0)).continuousOn.div
    (chartSmooth_continuous (chartSmooth_baseExceptionalWeight_comp hμ hE)).continuousOn
    fun z hz => (baseExceptionalWeight_pos F hE hz).ne'

/-- Off `ℰ`, `zStrictWeight = |s_Z|²_h ∘ π_X ∘ μ / W ∘ μ`. -/
theorem zStrictWeight_eq_of_notMem (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {y : 𝒳} (hy : y ∉ exceptionalSet F μ) :
    zStrictWeight F E μ y =
      (EReal.exp (E.weight (μ y).1)).toReal / baseExceptionalWeight F E (μ y) := by
  refine limUnder_nhdsWithin_compl_eq (interior_exceptionalSet F hμ)
    (isClosed_exceptionalSet F hμ).isOpen_compl ?_ (fun _ _ _ => rfl) hy
  exact (chartSmooth_continuous (chartSmooth_exp_weight_comp hμ hE)).continuousOn.div
    (chartSmooth_continuous (chartSmooth_baseExceptionalWeight_comp hμ hE)).continuousOn
    fun z hz => (baseExceptionalWeight_pos F hE hz).ne'

/-- **Local factorizations of `strictWeight`**: near `ℰ`, `strictWeight = |b|² N₁ ∘ μ / U'`
with `τ ∘ μ = b σ` and `W ∘ μ = |σ|² U'`; near `μ⁻¹ (X × (ℙ¹ \ 0))` it is smooth and positive. -/
theorem exists_strictWeight_factor (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (p : 𝒳) :
    ∃ O : Set 𝒳, IsOpen O ∧ p ∈ O ∧ ∃ (b : 𝒳 → ℂ) (V : 𝒳 → ℝ),
      (∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) b y) ∧
      (∀ e : ComplexChart (m + 1 + 1) 𝒳,
        ContDiffOn ℝ ∞ (fun z => V (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O)) ∧
      (∀ y ∈ O, 0 < V y) ∧ ∀ y ∈ O, strictWeight F E μ y = Complex.normSq (b y) * V y := by
  have hN := chartSmooth_projectiveWeight_comp hμ
  have hWs := chartSmooth_baseExceptionalWeight_comp hμ hE
  by_cases hp0 : (μ p).2 = projectiveZero
  · -- near the central fibre: the finite chart
    obtain ⟨O₁, hO₁, hpO₁, σ, U', -, hσgen, hU's, hU'pos, hfac⟩ :=
      exists_local_factorization F hμ hE p
    have hτ0 : (μ p).2 ∈ (projectiveModelChart false).source := by
      rw [hp0]; exact projectiveZero_mem_chart_source
    have hv : (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)).mem (μ p)
        (fun q => projectiveAffine q.2) := by
      refine ⟨HolomorphicAt.comp_contMDiff (f := Prod.snd) (holomorphicAt_projectiveAffine hτ0)
        (Eventually.of_forall fun _ => contMDiff_snd.contMDiffAt), ?_⟩
      exact Eventually.of_forall fun q hqC => by
        show projectiveAffine q.2 = 0
        rw [((mem_deformationCentre_iff F).mp hqC).2, projectiveAffine_zero]
    obtain ⟨b, hb, hvb⟩ := exists_eq_mul_of_isInSpanAt
      ((hσgen p hpO₁ _).mp (mem_pullback_of_mem F hμ hv))
    have hsrc : IsOpen (μ ⁻¹' (univ ×ˢ (projectiveModelChart false).source)) :=
      (isOpen_univ.prod (projectiveModelChart false).open_source).preimage hμ.continuous
    have hev : ∀ᶠ y in 𝓝 p, y ∈ O₁ ∧ (μ y).2 ∈ (projectiveModelChart false).source ∧
        projectiveAffine (μ y).2 = b y * σ y ∧
        MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) b y := by
      filter_upwards [hO₁.mem_nhds hpO₁, hsrc.mem_nhds ⟨mem_univ _, hτ0⟩, hvb, hb] with
        y h1 h2 h3 h4
      exact ⟨h1, h2.2, h3, h4⟩
    obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp hev
    have hVs : ∀ e : ComplexChart (m + 1 + 1) 𝒳, ContDiffOn ℝ ∞
        (fun z => projectiveWeight 1 (μ (e.val.symm z)).2 / U' (e.val.symm z))
        (e.val.target ∩ e.val.symm ⁻¹' O) := fun e =>
      ((hN 1 e).mono inter_subset_left).div ((hU's e).mono fun z hz => ⟨hz.1, (hOsub hz.2).1⟩)
        fun z hz => (hU'pos _ (hOsub hz.2).1).ne'
    refine ⟨O, hO, hpO, b, fun y => projectiveWeight 1 (μ y).2 / U' y,
      fun y hy => (hOsub hy).2.2.2, hVs, fun y hy => ?_, fun y hy => ?_⟩
    · exact div_pos (projectiveWeight_one_pos
        (mem_projectiveModelChart_false_source.mp (hOsub hy).2.1)) (hU'pos _ (hOsub hy).1)
    · have hbc : ContinuousOn b O := fun z hz =>
        ((hOsub hz).2.2.2.continuousAt).continuousWithinAt
      have hVc : ContinuousOn (fun y => projectiveWeight 1 (μ y).2 / U' y) O := fun z hz =>
        (MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn hO hVs hz).continuousWithinAt
      refine limUnder_nhdsWithin_compl_eq (interior_exceptionalSet F hμ) hO
        (G := fun y => Complex.normSq (b y) * (projectiveWeight 1 (μ y).2 / U' y))
        ((Complex.continuous_normSq.comp_continuousOn hbc).mul hVc) (fun z hzO hzE => ?_) hy
      obtain ⟨h1, h2, h3, -⟩ := hOsub hzO
      have hrep : (μ z).2.rep 1 ≠ 0 := mem_projectiveModelChart_false_source.mp h2
      have hWpos := baseExceptionalWeight_pos F hE hzE
      have hfz := hfac z h1
      have hσ0 : σ z ≠ 0 := by
        intro h
        rw [h, map_zero, zero_mul] at hfz
        exact hWpos.ne' hfz
      have hU0 := hU'pos z h1
      have hn : Complex.normSq (σ z) ≠ 0 := (Complex.normSq_pos.mpr hσ0).ne'
      rw [projectiveWeight_zero_eq hrep, h3, hfz, norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq,
        ← Complex.normSq_eq_norm_sq]
      field_simp
  · -- off the central fibre
    have hO : IsOpen (μ ⁻¹' (univ ×ˢ {projectiveZero}ᶜ)) :=
      (isOpen_univ.prod isClosed_singleton.isOpen_compl).preimage hμ.continuous
    have hoff : ∀ y ∈ μ ⁻¹' (univ ×ˢ {projectiveZero}ᶜ), μ y ∉ deformationCentre F :=
      fun y hy h => hy.2 ((mem_deformationCentre_iff F).mp h).2
    refine ⟨μ ⁻¹' (univ ×ˢ {projectiveZero}ᶜ), hO, ⟨mem_univ _, hp0⟩, fun _ => 1,
      fun y => projectiveWeight 0 (μ y).2 / baseExceptionalWeight F E (μ y),
      fun y _ => mdifferentiableAt_const, fun e => ?_, fun y hy => ?_, fun y hy => ?_⟩
    · exact ((hN 0 e).mono inter_subset_left).div ((hWs e).mono inter_subset_left)
        fun z hz => (baseExceptionalWeight_pos F hE (hoff _ hz.2)).ne'
    · exact div_pos (projectiveWeight_zero_pos hy.2) (baseExceptionalWeight_pos F hE (hoff y hy))
    · rw [strictWeight_eq_of_notMem F hμ hE (hoff y hy)]
      simp

/-- **Local factorizations of `zStrictWeight`**: `g ∘ π_X ∘ μ = a σ` and `W ∘ μ = |σ|² U'` give
`zStrictWeight = |a|² e^{h ∘ π_X ∘ μ} / U'`. -/
theorem exists_zStrictWeight_factor (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (p : 𝒳) :
    ∃ O : Set 𝒳, IsOpen O ∧ p ∈ O ∧ ∃ (a : 𝒳 → ℂ) (V : 𝒳 → ℝ),
      (∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) a y) ∧
      (∀ e : ComplexChart (m + 1 + 1) 𝒳,
        ContDiffOn ℝ ∞ (fun z => V (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O)) ∧
      (∀ y ∈ O, 0 < V y) ∧ ∀ y ∈ O, zStrictWeight F E μ y = Complex.normSq (a y) * V y := by
  obtain ⟨O₁, hO₁, hpO₁, σ, U', -, hσgen, hU's, hU'pos, hfac⟩ :=
    exists_local_factorization F hμ hE p
  obtain ⟨D, hDid, -, hmet⟩ := id hE
  obtain ⟨V, hV, hxV, g, hg, hgen, h, hh, hw⟩ := hmet (μ p).1
  rw [hDid] at hgen
  have hgV : ∀ x ∈ V, HolomorphicAt (m + 1) g x := fun x hx =>
    (hV.eventually_mem hx).mono fun y hy => (hg y hy).mdifferentiableAt (hV.mem_nhds hy)
  have hgZ : (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem (μ p).1 g :=
    (hgen (μ p).1 hxV g).mpr (isInSpanAt_self (hgV _ hxV))
  have hu : (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)).mem (μ p)
      (fun q => g q.1) := by
    refine ⟨HolomorphicAt.comp_contMDiff (f := Prod.fst) (hgV _ hxV)
      (Eventually.of_forall fun _ => contMDiff_fst.contMDiffAt), ?_⟩
    have h1 : Tendsto Prod.fst (𝓝 (μ p)) (𝓝 (μ p).1) := continuous_fst.continuousAt
    filter_upwards [h1.eventually hgZ.2] with q hq hqC
    exact hq ((mem_deformationCentre_iff F).mp hqC).1
  obtain ⟨a, ha, hua⟩ := exists_eq_mul_of_isInSpanAt
    ((hσgen p hpO₁ _).mp (mem_pullback_of_mem F hμ hu))
  have hpXV : IsOpen ((fun y => (μ y).1) ⁻¹' V) :=
    hV.preimage (continuous_fst.comp hμ.continuous)
  have hev : ∀ᶠ y in 𝓝 p, y ∈ O₁ ∧ (μ y).1 ∈ V ∧ g (μ y).1 = a y * σ y ∧
      MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) a y := by
    filter_upwards [hO₁.mem_nhds hpO₁, hpXV.mem_nhds hxV, hua, ha] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp hev
  have hVs : ∀ e : ComplexChart (m + 1 + 1) 𝒳, ContDiffOn ℝ ∞
      (fun z => Real.exp (h (μ (e.val.symm z)).1) / U' (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' O) := fun e =>
    (((contDiffOn_comp_chart_symm_of_holomorphic (contMDiff_deformationProjX F hμ.contMDiff) hV
      hh e).exp).mono fun z hz => ⟨hz.1, (hOsub hz.2).2.1⟩).div
      ((hU's e).mono fun z hz => ⟨hz.1, (hOsub hz.2).1⟩)
      fun z hz => (hU'pos _ (hOsub hz.2).1).ne'
  refine ⟨O, hO, hpO, a, fun y => Real.exp (h (μ y).1) / U' y,
    fun y hy => (hOsub hy).2.2.2, hVs, fun y hy => div_pos (Real.exp_pos _) (hU'pos _ (hOsub hy).1),
    fun y hy => ?_⟩
  have hac : ContinuousOn a O := fun z hz => ((hOsub hz).2.2.2.continuousAt).continuousWithinAt
  have hVc : ContinuousOn (fun y => Real.exp (h (μ y).1) / U' y) O := fun z hz =>
    (MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn hO hVs hz).continuousWithinAt
  refine limUnder_nhdsWithin_compl_eq (interior_exceptionalSet F hμ) hO
    (G := fun y => Complex.normSq (a y) * (Real.exp (h (μ y).1) / U' y))
    ((Complex.continuous_normSq.comp_continuousOn hac).mul hVc) (fun z hzO hzE => ?_) hy
  obtain ⟨h1, h2, h3, -⟩ := hOsub hzO
  have hWpos := baseExceptionalWeight_pos F hE hzE
  have hfz := hfac z h1
  have hσ0 : σ z ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hfz
    exact hWpos.ne' hfz
  have hU0 := hU'pos z h1
  have hn : Complex.normSq (σ z) ≠ 0 := (Complex.normSq_pos.mpr hσ0).ne'
  rw [exp_weight_toReal_eq F (hw _ h2), h3, hfz, norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  field_simp

/-- **The factorized weight `strictWeight`** (`tok-wn-def:strict-metric`). -/
def strictFactorization (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    WeightFactorization (m + 1 + 1) (strictWeight F E μ) := by
  classical
  choose O hO hpO b V hbd hVs hVpos hfac using exists_strictWeight_factor F hμ hE
  exact
    { domain := O, isOpen_domain := hO, mem_domain := hpO, gen := b, smoothPart := V,
      gen_mdifferentiable := hbd, smooth := hVs, pos := hVpos, factor := hfac,
      nowhereZero := fun W hW hne => by
        obtain ⟨y, hyW, hyX⟩ := exists_mem_notMem_of_interior_eq_empty
          (interior_centralFibre F hμ) hW hne
        refine ⟨y, hyW, ?_⟩
        have hp : (μ y).2 ≠ projectiveZero := fun h => hyX ((mem_centralFibre_iff F).mpr h)
        rw [strictWeight_eq_of_notMem F hμ hE (notMem_exceptionalSet_of_notMem_centralFibre F hyX)]
        exact (div_pos (projectiveWeight_zero_pos hp) (baseExceptionalWeight_pos F hE
          (notMem_exceptionalSet_of_notMem_centralFibre F hyX))).ne' }

/-- **The factorized weight `zStrictWeight`** (`tok-wn-def:z-metric`). -/
def zStrictFactorization (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    WeightFactorization (m + 1 + 1) (zStrictWeight F E μ) := by
  classical
  choose O hO hpO b V hbd hVs hVpos hfac using exists_zStrictWeight_factor F hμ hE
  exact
    { domain := O, isOpen_domain := hO, mem_domain := hpO, gen := b, smoothPart := V,
      gen_mdifferentiable := hbd, smooth := hVs, pos := hVpos, factor := hfac,
      nowhereZero := fun W hW hne => by
        obtain ⟨y, hyW, hyZ, hy0⟩ := exists_mem_proj_notMem_firstFlag F hμ hW hne _
          (fun V hV hne => inter_compl_firstFlag_nonempty F hV hne)
        have hyE : y ∉ exceptionalSet F μ := fun h => hy0 ((mem_deformationCentre_iff F).mp h).2
        refine ⟨y, hyW, ?_⟩
        rw [zStrictWeight_eq_of_notMem F hμ hE hyE]
        exact (div_pos (exp_weight_toReal_pos F hE hyZ)
          (baseExceptionalWeight_pos F hE hyE)).ne' }

/-! ### The curvature forms -/

/-- **The curvature of `𝒪(X')`** (`tok-wn-def:strict-metric`): the glued form `ddᶜ log strictWeight`
is `η_ℰ - (π_{ℙ¹} μ)^* ω_FS`, for the metric `Eℰ` of `𝒪(ℰ)` with weight `log W ∘ μ`. Off the
central fibre `strictWeight = N₀ / W ∘ μ` with `ddᶜ log N₀ = -ω_FS` and `ddᶜ log W ∘ μ = -η_ℰ`;
both sides are smooth and `X₀` has empty interior. -/
theorem strictFactorization_closedForm_coeff (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hweight : ∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z))))
    (hsupp : Eℰ.support = exceptionalSet F μ) (e : ComplexChart (m + 1 + 1) 𝒳)
    {u : ComplexModel (m + 1 + 1)} (hu : u ∈ e.val.target) :
    (strictFactorization F hμ hE).closedForm.val.coeff e u =
      (Eℰ.curvature - ClosedRealOneOneForm.pullback (contMDiff_deformationProjP1 F hμ.contMDiff)
        projectiveNativeFSClosedForm).val.coeff e u := by
  have hN := chartSmooth_projectiveWeight_comp hμ
  have hWs := chartSmooth_baseExceptionalWeight_comp hμ hE
  set X0c := (centralFibre F μ)ᶜ with hX0c_def
  have hX0c : IsOpen X0c := (isClosed_centralFibre F hμ).isOpen_compl
  have hEc : ∀ y ∈ X0c, y ∉ exceptionalSet F μ := fun y hy =>
    notMem_exceptionalSet_of_notMem_centralFibre F hy
  have hp0 : ∀ y ∈ X0c, (μ y).2 ≠ projectiveZero := fun y hy h =>
    hy ((mem_centralFibre_iff F).mpr h)
  have hWpos : ∀ y ∈ X0c, 0 < baseExceptionalWeight F E (μ y) := fun y hy =>
    baseExceptionalWeight_pos F hE (hEc y hy)
  have hsw : ∀ y ∈ X0c, strictWeight F E μ y =
      projectiveWeight 0 (μ y).2 / baseExceptionalWeight F E (μ y) := fun y hy =>
    strictWeight_eq_of_notMem F hμ hE (hEc y hy)
  have hUs : ∀ e : ComplexChart (m + 1 + 1) 𝒳, ContDiffOn ℝ ∞
      (fun u => strictWeight F E μ (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' X0c) :=
    fun e => (((hN 0 e).mono inter_subset_left).div ((hWs e).mono inter_subset_left)
      fun u hu => (hWpos _ hu.2).ne').congr fun u hu => hsw _ hu.2
  have hUpos : ∀ y ∈ X0c, 0 < strictWeight F E μ y := fun y hy => by
    rw [hsw y hy]
    exact div_pos (projectiveWeight_zero_pos (hp0 y hy)) (hWpos y hy)
  have hoff : EqOn (fun u => (strictFactorization F hμ hE).closedForm.val.coeff e u)
      (fun u => (Eℰ.curvature - ClosedRealOneOneForm.pullback
        (contMDiff_deformationProjP1 F hμ.contMDiff) projectiveNativeFSClosedForm).val.coeff e u)
      (e.val.target ∩ e.val.symm ⁻¹' X0c) := by
    rintro u ⟨hu, huX⟩
    simp only
    rw [WeightFactorization.closedForm_coeff_eq_of_pos _ hX0c hUs hUpos e hu huX]
    set S := e.val.target ∩ e.val.symm ⁻¹' X0c with hS_def
    have hS : IsOpen S := e.val.isOpen_inter_preimage_symm hX0c
    have huS : u ∈ S := ⟨hu, huX⟩
    have hlN : ContDiffOn ℝ ∞ (fun w => Real.log (projectiveWeight 0 (μ (e.val.symm w)).2)) S :=
      ((hN 0 e).mono inter_subset_left).log fun w hw =>
        (projectiveWeight_zero_pos (hp0 _ hw.2)).ne'
    have hlW :
        ContDiffOn ℝ ∞ (fun w => Real.log (baseExceptionalWeight F E (μ (e.val.symm w)))) S :=
      ((hWs e).mono inter_subset_left).log fun w hw => (hWpos _ hw.2).ne'
    have heq : (fun w => Real.log (strictWeight F E μ (e.val.symm w))) =ᶠ[𝓝 u]
        fun w => Real.log (projectiveWeight 0 (μ (e.val.symm w)).2) -
          Real.log (baseExceptionalWeight F E (μ (e.val.symm w))) := by
      filter_upwards [hS.mem_nhds huS] with w hw
      rw [hsw _ hw.2, Real.log_div (projectiveWeight_zero_pos (hp0 _ hw.2)).ne'
        (hWpos _ hw.2).ne']
    rw [smoothDDC_congr heq, PositiveClasses.smoothDDC_sub hS hlN hlW huS]
    -- the Fubini--Study part
    have h1 : smoothDDC (fun w => Real.log (projectiveWeight 0 (μ (e.val.symm w)).2)) u =
        -(ClosedRealOneOneForm.pullback (contMDiff_deformationProjP1 F hμ.contMDiff)
          projectiveNativeFSClosedForm).val.coeff e u := by
      rw [pullback_projectiveFS_coeff (contMDiff_deformationProjP1 F hμ.contMDiff) e hu
        (projectiveWeight_zero_pos (hp0 _ huX)), smoothDDC_neg hS hlN huS, neg_neg]
    -- the exceptional part
    have h2 : smoothDDC (fun w => Real.log (baseExceptionalWeight F E (μ (e.val.symm w)))) u =
        -Eℰ.curvature.val.coeff e u := by
      have hyE : e.val.symm u ∉ Eℰ.support := by rw [hsupp]; exact hEc _ huX
      obtain ⟨W₁, hW₁, hpot⟩ :=
        MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature Eℰ hyE e
          (e.val.map_target hu)
      rw [e.val.right_inv hu] at hW₁
      have hcongr : (fun ζ => (Eℰ.weight (e.val.symm ζ)).toReal) =ᶠ[𝓝 u]
          fun w => Real.log (baseExceptionalWeight F E (μ (e.val.symm w))) := by
        filter_upwards [hS.mem_nhds huS] with w hw
        rw [hweight, ENNReal.log_ofReal_of_pos (hWpos _ hw.2)]
        rfl
      have h := hpot.2.2.2 hW₁
      rw [smoothDDC_congr hcongr] at h
      rw [h, ClosedRealOneOneForm.coeff_neg]
    rw [h1, h2, BlowupBigPullback.coeff_sub]
    abel
  exact hoff.of_subset_closure ((strictFactorization F hμ hE).closedForm.val.smooth e).continuousOn
    ((Eℰ.curvature - ClosedRealOneOneForm.pullback (contMDiff_deformationProjP1 F hμ.contMDiff)
      projectiveNativeFSClosedForm).val.smooth e).continuousOn inter_subset_left
    (TranscendentalSlice.chart_target_subset_closure (interior_centralFibre F hμ) e) hu

/-- **The curvature of `𝒪(Z̃)`** (`tok-wn-def:z-metric`): the glued form `ddᶜ log zStrictWeight`
is `η_ℰ - (π_X μ)^* η`, `η` the curvature of `E`. -/
theorem zStrictFactorization_closedForm_coeff (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hweight : ∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z))))
    (hsupp : Eℰ.support = exceptionalSet F μ) (e : ComplexChart (m + 1 + 1) 𝒳)
    {u : ComplexModel (m + 1 + 1)} (hu : u ∈ e.val.target) :
    (zStrictFactorization F hμ hE).closedForm.val.coeff e u =
      (Eℰ.curvature - ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ.contMDiff)
        E.curvature).val.coeff e u := by
  have hr := chartSmooth_exp_weight_comp hμ hE
  have hWs := chartSmooth_baseExceptionalWeight_comp hμ hE
  set Vc := (fun y => (μ y).1) ⁻¹' (F.flag (1 : Fin (m + 2)))ᶜ with hVc_def
  have hVc : IsOpen Vc :=
    F.firstDivisor.1.isOpen_compl.preimage (continuous_fst.comp hμ.continuous)
  have hEc : ∀ y ∈ Vc, y ∉ exceptionalSet F μ := fun y hy h =>
    hy ((mem_deformationCentre_iff F).mp h).1
  have hWpos : ∀ y ∈ Vc, 0 < baseExceptionalWeight F E (μ y) := fun y hy =>
    baseExceptionalWeight_pos F hE (hEc y hy)
  have hrpos : ∀ y ∈ Vc, 0 < (EReal.exp (E.weight (μ y).1)).toReal := fun y hy =>
    exp_weight_toReal_pos F hE hy
  have hzw : ∀ y ∈ Vc, zStrictWeight F E μ y =
      (EReal.exp (E.weight (μ y).1)).toReal / baseExceptionalWeight F E (μ y) := fun y hy =>
    zStrictWeight_eq_of_notMem F hμ hE (hEc y hy)
  have hUs : ∀ e : ComplexChart (m + 1 + 1) 𝒳, ContDiffOn ℝ ∞
      (fun u => zStrictWeight F E μ (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' Vc) :=
    fun e => (((hr e).mono inter_subset_left).div ((hWs e).mono inter_subset_left)
      fun u hu => (hWpos _ hu.2).ne').congr fun u hu => hzw _ hu.2
  have hUpos : ∀ y ∈ Vc, 0 < zStrictWeight F E μ y := fun y hy => by
    rw [hzw y hy]
    exact div_pos (hrpos y hy) (hWpos y hy)
  have hint : interior ((fun y => (μ y).1) ⁻¹' F.flag (1 : Fin (m + 2))) = ∅ :=
    interior_preimage_firstFlag F hμ
  have hoff : EqOn (fun u => (zStrictFactorization F hμ hE).closedForm.val.coeff e u)
      (fun u => (Eℰ.curvature - ClosedRealOneOneForm.pullback
        (contMDiff_deformationProjX F hμ.contMDiff) E.curvature).val.coeff e u)
      (e.val.target ∩ e.val.symm ⁻¹' ((fun y => (μ y).1) ⁻¹' F.flag (1 : Fin (m + 2)))ᶜ) := by
    rintro u ⟨hu, huX⟩
    simp only
    rw [WeightFactorization.closedForm_coeff_eq_of_pos _ hVc hUs hUpos e hu huX]
    set S := e.val.target ∩ e.val.symm ⁻¹' Vc with hS_def
    have hS : IsOpen S := e.val.isOpen_inter_preimage_symm hVc
    have huS : u ∈ S := ⟨hu, huX⟩
    have hlr : ContDiffOn ℝ ∞
        (fun w => Real.log (EReal.exp (E.weight (μ (e.val.symm w)).1)).toReal) S :=
      ((hr e).mono inter_subset_left).log fun w hw => (hrpos _ hw.2).ne'
    have hlW :
        ContDiffOn ℝ ∞ (fun w => Real.log (baseExceptionalWeight F E (μ (e.val.symm w)))) S :=
      ((hWs e).mono inter_subset_left).log fun w hw => (hWpos _ hw.2).ne'
    have heq : (fun w => Real.log (zStrictWeight F E μ (e.val.symm w))) =ᶠ[𝓝 u]
        fun w => Real.log (EReal.exp (E.weight (μ (e.val.symm w)).1)).toReal -
          Real.log (baseExceptionalWeight F E (μ (e.val.symm w))) := by
      filter_upwards [hS.mem_nhds huS] with w hw
      rw [hzw _ hw.2, Real.log_div (hrpos _ hw.2).ne' (hWpos _ hw.2).ne']
    rw [smoothDDC_congr heq, PositiveClasses.smoothDDC_sub hS hlr hlW huS]
    -- the pulled-back part
    have h1 : smoothDDC (fun w => Real.log (EReal.exp (E.weight (μ (e.val.symm w)).1)).toReal) u =
        -(ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ.contMDiff)
          E.curvature).val.coeff e u := by
      have hxE : (μ (e.val.symm u)).1 ∉ E.support := by
        obtain ⟨D, -, hsuppE, -⟩ := id hE
        rw [hsuppE]; exact huX
      rw [pullback_curvature_coeff_of_notMem (contMDiff_deformationProjX F hμ.contMDiff) E e hu hxE,
        neg_neg]
      apply smoothDDC_congr
      filter_upwards [hS.mem_nhds huS] with w hw
      have hne : E.weight (μ (e.val.symm w)).1 ≠ ⊥ := by
        obtain ⟨D, -, hsuppE, -⟩ := id hE
        intro h0
        exact hw.2 (by rw [← hsuppE]; exact h0)
      have hnt := weight_ne_top F hE (μ (e.val.symm w)).1
      rw [← EReal.coe_toReal hnt hne, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le,
        Real.log_exp, EReal.toReal_coe]
    -- the exceptional part
    have h2 : smoothDDC (fun w => Real.log (baseExceptionalWeight F E (μ (e.val.symm w)))) u =
        -Eℰ.curvature.val.coeff e u := by
      have hyE : e.val.symm u ∉ Eℰ.support := by rw [hsupp]; exact hEc _ huX
      obtain ⟨W₁, hW₁, hpot⟩ :=
        MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature Eℰ hyE e
          (e.val.map_target hu)
      rw [e.val.right_inv hu] at hW₁
      have hcongr : (fun ζ => (Eℰ.weight (e.val.symm ζ)).toReal) =ᶠ[𝓝 u]
          fun w => Real.log (baseExceptionalWeight F E (μ (e.val.symm w))) := by
        filter_upwards [hS.mem_nhds huS] with w hw
        rw [hweight, ENNReal.log_ofReal_of_pos (hWpos _ hw.2)]
        rfl
      have h := hpot.2.2.2 hW₁
      rw [smoothDDC_congr hcongr] at h
      rw [h, ClosedRealOneOneForm.coeff_neg]
    rw [h1, h2, BlowupBigPullback.coeff_sub]
    abel
  exact hoff.of_subset_closure ((zStrictFactorization F hμ hE).closedForm.val.smooth e).continuousOn
    ((Eℰ.curvature - ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ.contMDiff)
      E.curvature).val.smooth e).continuousOn inter_subset_left
    (TranscendentalSlice.chart_target_subset_closure hint e) hu

/-! ### Values -/

/-- Over `Z × (ℙ¹ \ 0)`, `strictWeight = 1`. -/
theorem strictWeight_eq_one (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {y : 𝒳} (hyZ : (μ y).1 ∈ F.flag (1 : Fin (m + 2))) (hy0 : (μ y).2 ≠ projectiveZero) :
    strictWeight F E μ y = 1 := by
  have hyE : y ∉ exceptionalSet F μ := fun h => hy0 ((mem_deformationCentre_iff F).mp h).2
  rw [strictWeight_eq_of_notMem F hμ hE hyE, baseExceptionalWeight_eq,
    exp_weight_toReal_eq_zero F hE hyZ, zero_mul, zero_add,
    div_self (projectiveWeight_zero_pos hy0).ne']

/-- Off `X₀`, `strictWeight > 0`. -/
theorem strictWeight_pos (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {y : 𝒳} (hy0 : (μ y).2 ≠ projectiveZero) : 0 < strictWeight F E μ y := by
  have hyE : y ∉ exceptionalSet F μ := fun h => hy0 ((mem_deformationCentre_iff F).mp h).2
  rw [strictWeight_eq_of_notMem F hμ hE hyE]
  exact div_pos (projectiveWeight_zero_pos hy0) (baseExceptionalWeight_pos F hE hyE)

/-- On `X' \ ℰ`, i.e. over `(X \ Z) × {0}`, `zStrictWeight = 1`. -/
theorem zStrictWeight_eq_one (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {y : 𝒳} (hyZ : (μ y).1 ∉ F.flag (1 : Fin (m + 2))) (hy0 : (μ y).2 = projectiveZero) :
    zStrictWeight F E μ y = 1 := by
  have hyE : y ∉ exceptionalSet F μ := fun h => hyZ ((mem_deformationCentre_iff F).mp h).1
  have h1 : projectiveWeight 1 projectiveZero = 1 := by
    linarith [projectiveWeight_add projectiveZero, projectiveWeight_zero_projectiveZero]
  rw [zStrictWeight_eq_of_notMem F hμ hE hyE, baseExceptionalWeight_eq, hy0, h1,
    projectiveWeight_zero_projectiveZero, mul_one, add_zero,
    div_self (exp_weight_toReal_pos F hE hyZ).ne']

/-- Over `X \ Z`, `zStrictWeight > 0`. -/
theorem zStrictWeight_pos (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {y : 𝒳} (hyZ : (μ y).1 ∉ F.flag (1 : Fin (m + 2))) : 0 < zStrictWeight F E μ y := by
  have hyE : y ∉ exceptionalSet F μ := fun h => hyZ ((mem_deformationCentre_iff F).mp h).1
  rw [zStrictWeight_eq_of_notMem F hμ hE hyE]
  exact div_pos (exp_weight_toReal_pos F hE hyZ) (baseExceptionalWeight_pos F hE hyE)

end Strict

end SGPT.Okounkov.TranscendentalWN
