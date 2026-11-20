import SGPT.Okounkov.TranscendentalL2Solution

/-!
# `L²` generation over a coordinate ball of the base of a modification

Plan `tok/RELGEN3` step P9 (blueprint `l2:modification-generation`, chapter `claude-tok-l2`):
the proof of `ModificationL2GenerationStatement` (`modificationL2Generation`).

From the solution `G` on `Ω* = B(x₀, r₁) \ {k = 0}` of `exists_solution_on_complement`:

* `exists_chart_estimate`: by the change of variables along `d ∘ π` and the comparison
  `|J|² e^{-Γ} ≍ 1` (`exists_jacobian_weight_bounds`), `∫ |χ f - G ∘ d ∘ π|² e^{-(φ_N + P)} < ∞`
  over chart pieces of `V' = π⁻¹(d⁻¹ B(x₀, r₁))`, in every preferred chart;
* `not_eventually_zero_comp_coordinateMap`: `k ∘ d ∘ π` vanishes identically near no point;
* `exists_upstairs_extension`: `G ∘ d ∘ π` extends holomorphically to `V'` (`L²` Riemann extension
  in charts, `exists_extension_of_locally_sq_integrable`, glued by continuity);
* membership in `𝓘(φ_N)` and the pole integral (moved to the preferred chart at `z` by
  `multiplierIntegrableAt_chart_of_isOpen` and the Lipschitz bound of the chart change);
* the non-exceptional case `z ∉ A` (`F = f` on a small `π⁻¹ U`, by properness).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter MeasureTheory Metric Complex
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
open SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal
open SGPT.Okounkov.TranscendentalRelGen

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-! ### Back on `V'`: the estimate in charts -/

/-- **The estimate in a chart of `V'`** (blueprint `l2:modification-generation`): the change of
variables along `F = d ∘ π ∘ e⁻¹` and `|J_F|² e^{-ψ_R} ≥ c > 0` turn `∫_{Ω*} |h₀ - G|² e^{-Φ} < ∞`
into `∫ |hZ ∘ e⁻¹ - G ∘ F|² e^{-W ∘ e⁻¹} < ∞` near every point, `Φ = (W + ψ_R) ∘ σ`. -/
theorem exists_chart_estimate {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B)
    (hpre : π ⁻¹' B = A) (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hleft : ∀ y ∉ A, s (π y) = y) {E : MeteredEffectiveQDivisor n Z}
    {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    {d : ComplexChart n X} {x₀ : ComplexModel n} {r₁ : ℝ} {k : ComplexModel n → ℂ}
    (hk : DifferentiableOn ℂ k (ball x₀ r₁))
    (hkzero : ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball x₀ r₁ →
      (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0)
    {hZ : Z → ℂ} {W : Z → ℝ} {G : ComplexModel n → ℂ}
    (hfin : ∫⁻ x in ball x₀ r₁ ∩ {x | k x ≠ 0}, ENNReal.ofReal
      (‖hZ (s (d.val.symm x)) - G x‖ ^ 2 *
        Real.exp (-(W (s (d.val.symm x)) + (ER.weight (s (d.val.symm x))).toReal))) < ⊤)
    (a : Z) {y : Z} (hya : y ∈ (complexChartAt (n := n) a).val.source)
    (hyd : π y ∈ d.val.source) :
    ∃ O : Set (ComplexModel n), IsOpen O ∧ (complexChartAt (n := n) a).val y ∈ O ∧
      O ⊆ coordinateDomain π (complexChartAt (n := n) a) d ∧
      ∫⁻ w in O ∩ coordinateMap π (complexChartAt (n := n) a) d ⁻¹' (ball x₀ r₁ ∩ {x | k x ≠ 0}),
        ENNReal.ofReal (‖hZ ((complexChartAt (n := n) a).val.symm w) -
          G (coordinateMap π (complexChartAt (n := n) a) d w)‖ ^ 2 *
            Real.exp (-W ((complexChartAt (n := n) a).val.symm w))) < ⊤ := by
  set e := complexChartAt (n := n) a with he
  set F := coordinateMap π e d with hF
  set Ω := ball x₀ r₁ ∩ {x | k x ≠ 0} with hΩ
  have hΩo : IsOpen Ω := hk.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  obtain ⟨O, hO, hyO, hOd, cJ, _CJ, hcJ, hbd⟩ := exists_jacobian_weight_bounds hπ hER a d hya hyd
  refine ⟨O, hO, hyO, hOd, ?_⟩
  have hFc : ContinuousOn F (coordinateDomain π e d) :=
    (coordinateMap_contDiffOn hπ.1 e d).continuousOn
  set U := O ∩ F ⁻¹' Ω with hU
  have hUo : IsOpen U := by
    have : U = O ∩ (coordinateDomain π e d ∩ F ⁻¹' Ω) := by
      ext w; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hOd h1, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    rw [this]
    exact hO.inter (hFc.isOpen_inter_preimage (coordinateDomain_isOpen hπ.1 e d) hΩo)
  have hUd : U ⊆ coordinateDomain π e d := fun w hw => hOd hw.1
  set u : ComplexModel n → ℝ≥0∞ := fun x => ENNReal.ofReal
    (‖hZ (s (d.val.symm x)) - G x‖ ^ 2 *
      Real.exp (-(W (s (d.val.symm x)) + (ER.weight (s (d.val.symm x))).toReal))) with hu
  have hcov := lintegral_image_coordinateMap_eq hπ e d hUo hUd u
  have himΩ : F '' U ⊆ Ω := by rintro _ ⟨w, hw, rfl⟩; exact hw.2
  have hfin' : ∫⁻ w in U, ENNReal.ofReal (Complex.normSq (complexJacobian F w)) * u (F w) < ⊤ := by
    rw [← hcov]
    exact (lintegral_mono_set himΩ).trans_lt hfin
  have hpt : ∀ w ∈ U, ENNReal.ofReal (‖hZ (e.val.symm w) - G (F w)‖ ^ 2 *
      Real.exp (-W (e.val.symm w))) ≤
        ENNReal.ofReal cJ⁻¹ * (ENNReal.ofReal (Complex.normSq (complexJacobian F w)) * u (F w)) := by
    intro w hw
    have hwd := hUd hw
    set t := e.val.symm w with ht
    have hFw : F w = d.val (π t) := rfl
    obtain ⟨htA, hst, -⟩ := upstairs_facts hpre hleft hkzero hwd.2
      (by rw [← hFw]; exact hw.2.1) (by rw [← hFw]; exact hw.2.2)
    have hte : t ∈ e.val.source := e.val.map_target hwd.1
    have hJ : complexJacobian F w ≠ 0 := by
      have := complexJacobian_coordinateMap_ne_zero hπ.1 hAc hBc hpre hs hleft e d hte hwd.2 htA
      rwa [e.val.right_inv hwd.1] at this
    obtain ⟨-, hlow, -⟩ := hbd w hw.1 hJ
    have hsF : s (d.val.symm (F w)) = t := by rw [hFw]; exact hst
    simp only [hu]
    rw [hsF, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hcJ.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : Real.exp (-(W t + (ER.weight t).toReal)) =
        Real.exp (-W t) * Real.exp (-(ER.weight t).toReal) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have hA := Real.exp_pos (-W t)
    have hB : 0 ≤ ‖hZ t - G (F w)‖ ^ 2 := sq_nonneg _
    have hkey : 1 ≤ cJ⁻¹ * (Complex.normSq (complexJacobian F w) *
        Real.exp (-(ER.weight t).toReal)) := by
      rw [le_inv_mul_iff₀ hcJ]; simpa using hlow
    calc ‖hZ t - G (F w)‖ ^ 2 * Real.exp (-W t)
        ≤ cJ⁻¹ * (Complex.normSq (complexJacobian F w) * Real.exp (-(ER.weight t).toReal)) *
            (‖hZ t - G (F w)‖ ^ 2 * Real.exp (-W t)) :=
          le_mul_of_one_le_left (by positivity) hkey
      _ = cJ⁻¹ * (Complex.normSq (complexJacobian F w) *
            (‖hZ t - G (F w)‖ ^ 2 * (Real.exp (-W t) * Real.exp (-(ER.weight t).toReal)))) := by
          ring
  calc ∫⁻ w in O ∩ F ⁻¹' Ω, ENNReal.ofReal (‖hZ (e.val.symm w) - G (F w)‖ ^ 2 *
        Real.exp (-W (e.val.symm w)))
      ≤ ∫⁻ w in U, ENNReal.ofReal cJ⁻¹ *
          (ENNReal.ofReal (Complex.normSq (complexJacobian F w)) * u (F w)) :=
        setLIntegral_mono' hUo.measurableSet hpt
    _ = ENNReal.ofReal cJ⁻¹ * ∫⁻ w in U,
          ENNReal.ofReal (Complex.normSq (complexJacobian F w)) * u (F w) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin'

/-! ### `k ∘ d ∘ π` vanishes identically near no point -/

/-- **`k ∘ d ∘ π ∘ e⁻¹` vanishes identically near no point**: near a point off the nowhere dense
exceptional set, `d ∘ π ∘ e⁻¹` has the continuous right inverse `e ∘ s ∘ d⁻¹`, so `k` would vanish
identically near a point of `B(x₀, r₁)`. -/
theorem not_eventually_zero_comp_coordinateMap {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAi : interior A = ∅) (hBc : IsClosed B)
    (hpre : π ⁻¹' B = A) (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hright : ∀ x ∉ B, π (s x) = x) (hleft : ∀ y ∉ A, s (π y) = y)
    {d : ComplexChart n X} {x₀ : ComplexModel n} {r₁ : ℝ} {k : ComplexModel n → ℂ}
    (hkne : ∀ x ∈ ball x₀ r₁, ¬ ∀ᶠ w in 𝓝 x, k w = 0) (e : ComplexChart n Z)
    {w : ComplexModel n} (hwd : w ∈ coordinateDomain π e d)
    (hwb : coordinateMap π e d w ∈ ball x₀ r₁) :
    ¬ ∀ᶠ w' in 𝓝 w, k (coordinateMap π e d w') = 0 := by
  intro hev
  set F := coordinateMap π e d with hF
  have hdomo : IsOpen (coordinateDomain π e d) := coordinateDomain_isOpen hπ e d
  have hFc : ContinuousOn F (coordinateDomain π e d) :=
    (coordinateMap_contDiffOn hπ e d).continuousOn
  have hNo : IsOpen (coordinateDomain π e d ∩ F ⁻¹' ball x₀ r₁) :=
    hFc.isOpen_inter_preimage hdomo isOpen_ball
  obtain ⟨N, hNsub, hNo', hwN⟩ := _root_.mem_nhds_iff.mp
    (hev.and (hNo.mem_nhds ⟨hwd, hwb⟩))
  -- a point of `N` off the exceptional set
  have hN'o : IsOpen (e.val.source ∩ e.val ⁻¹' N) := e.val.isOpen_inter_preimage hNo'
  have hN'ne : (e.val.source ∩ e.val ⁻¹' N).Nonempty :=
    ⟨e.val.symm w, e.val.map_target hwd.1, by rw [mem_preimage, e.val.right_inv hwd.1]; exact hwN⟩
  obtain ⟨t, ⟨hte, htN⟩, htA⟩ : ∃ t ∈ e.val.source ∩ e.val ⁻¹' N, t ∉ A := by
    by_contra hall
    push Not at hall
    have := interior_maximal hall hN'o
    rw [hAi] at this
    exact this hN'ne.some_mem
  have htN' := hNsub htN
  set x'' := F (e.val t) with hx''
  have htd : π t ∈ d.val.source := by
    have := htN'.2.1.2
    rwa [mem_preimage, e.val.left_inv hte] at this
  have hx''eq : x'' = d.val (π t) := by
    simp only [hx'', hF, coordinateMap, Function.comp_apply, e.val.left_inv hte]
  have htB : π t ∉ B := fun h => htA (by rw [← hpre]; exact h)
  have hx''t : x'' ∈ d.val.target := by rw [hx''eq]; exact d.val.map_source htd
  have hx''B : d.val.symm x'' ∉ B := by rw [hx''eq, d.val.left_inv htd]; exact htB
  have hsx'' : s (d.val.symm x'') = t := by rw [hx''eq, d.val.left_inv htd, hleft t htA]
  have hx''σ : x'' ∈ sigmaDomain B s d e :=
    mem_sigmaDomain hx''t hx''B (by rw [hsx'']; exact hte)
  set S := coordinateMap s d e with hS
  have hSc : ContinuousAt S x'' := (contDiffAt_coordinateMap_sigma hBc hs d e hx''σ).continuousAt
  have hSx'' : S x'' = e.val t := by simp only [hS, coordinateMap, Function.comp_apply, hsx'']
  apply hkne x'' (by rw [hx''eq, ← hx''eq]; exact htN'.2.2)
  have hNS : ∀ᶠ x' in 𝓝 x'', S x' ∈ N := hSc.eventually (by rw [hSx'']; exact hNo'.mem_nhds htN)
  filter_upwards [hNS, (isOpen_sigmaDomain hBc hs d e).mem_nhds hx''σ] with x' hx'N hx'σ
  have hFS : F (S x') = x' := by
    simp only [hF, hS, coordinateMap, Function.comp_apply]
    rw [e.val.left_inv hx'σ.1.2, hright _ hx'σ.2, d.val.right_inv hx'σ.1.1]
  have := (hNsub hx'N).1
  rwa [hFS] at this

/-- The zero set of a holomorphic function which vanishes identically near no point of an open set
is null: the open set and its part off the zero set agree almost everywhere. -/
theorem inter_ne_zero_ae_eq {U : Set (ComplexModel n)} (hU : IsOpen U)
    {k' : ComplexModel n → ℂ} (hk' : DifferentiableOn ℂ k' U)
    (hkne : ∀ w ∈ U, ¬ ∀ᶠ w' in 𝓝 w, k' w' = 0) :
    (U ∩ {w | k' w ≠ 0} : Set (ComplexModel n)) =ᵐ[volume] U := by
  have hae := LelongPoincareDivisor.ae_ne_zero hU hk' fun w hw =>
    Filter.not_eventually.mp (hkne w hw)
  rw [ae_restrict_iff' hU.measurableSet] at hae
  rw [ae_eq_set]
  refine ⟨by rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty], ?_⟩
  rw [ae_iff] at hae
  refine measure_mono_null (fun w hw => ?_) hae
  simp only [Set.mem_ofPred_eq]
  intro h
  exact hw.2 ⟨hw.1, h hw.1⟩

/-- **The holomorphic extension upstairs** (blueprint `l2:modification-generation`): `G ∘ d ∘ π`
extends holomorphically from `{k ∘ d ∘ π ≠ 0}` to `V' = π⁻¹(d⁻¹ B(x₀, r₁))`. -/
theorem exists_upstairs_extension {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hAi : interior A = ∅)
    (hBc : IsClosed B) (hpre : π ⁻¹' B = A)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hright : ∀ x ∉ B, π (s x) = x) (hleft : ∀ y ∉ A, s (π y) = y)
    {E : MeteredEffectiveQDivisor n Z} {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    {d : ComplexChart n X} {x₀ : ComplexModel n} {r₁ : ℝ} {k : ComplexModel n → ℂ}
    (hk : DifferentiableOn ℂ k (ball x₀ r₁)) (hkne : ∀ x ∈ ball x₀ r₁, ¬ ∀ᶠ w in 𝓝 x, k w = 0)
    (hkzero : ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball x₀ r₁ →
      (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0)
    {hZ : Z → ℂ} {W : Z → ℝ} {G : ComplexModel n → ℂ}
    (hG : DifferentiableOn ℂ G (ball x₀ r₁ ∩ {x | k x ≠ 0}))
    (hfin : ∫⁻ x in ball x₀ r₁ ∩ {x | k x ≠ 0}, ENNReal.ofReal
      (‖hZ (s (d.val.symm x)) - G x‖ ^ 2 *
        Real.exp (-(W (s (d.val.symm x)) + (ER.weight (s (d.val.symm x))).toReal))) < ⊤)
    {Mh : ℝ} (hMh : ∀ t, ‖hZ t‖ ≤ Mh)
    (hWub : ∀ y ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁), ∃ N ∈ 𝓝 y, ∃ M : ℝ,
      ∀ t ∈ N, E.weight t ≠ ⊥ → W t ≤ M) :
    ∃ F : Z → ℂ, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) F
        (π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁)) ∧
      ∀ t ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁), k (d.val (π t)) ≠ 0 →
        F t = G (d.val (π t)) := by
  classical
  set V' := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁) with hV'
  set Ω := ball x₀ r₁ ∩ {x | k x ≠ 0} with hΩ
  have hV'o : IsOpen V' := (d.val.isOpen_inter_preimage isOpen_ball).preimage hπ.1.continuous
  -- the local extensions
  have hloc : ∀ y ∈ V', ∃ (U : Set (ComplexModel n)) (Gy : ComplexModel n → ℂ), IsOpen U ∧
      (complexChartAt (n := n) y).val y ∈ U ∧
      U ⊆ coordinateDomain π (complexChartAt (n := n) y) d ∧ DifferentiableOn ℂ Gy U ∧
      ∀ w ∈ U, k (coordinateMap π (complexChartAt (n := n) y) d w) ≠ 0 →
        Gy w = G (coordinateMap π (complexChartAt (n := n) y) d w) := by
    intro y hy
    set e := complexChartAt (n := n) y with he
    set F := coordinateMap π e d with hF
    have hye : y ∈ e.val.source := mem_complexChartAt_source y
    obtain ⟨O, hO, hyO, hOd, hI⟩ := exists_chart_estimate hπ hAc hBc hpre hs hleft hER hk
      hkzero hfin y hye hy.1
    obtain ⟨N, hN, M, hM⟩ := hWub y hy
    obtain ⟨N', hN'N, hN'o, hyN'⟩ := _root_.mem_nhds_iff.mp hN
    have hFc : ContinuousOn F (coordinateDomain π e d) :=
      (coordinateMap_contDiffOn hπ.1 e d).continuousOn
    have hU₀ : IsOpen (O ∩ F ⁻¹' ball x₀ r₁ ∩ (e.val.target ∩ e.val.symm ⁻¹' N')) := by
      have : O ∩ F ⁻¹' ball x₀ r₁ = O ∩ (coordinateDomain π e d ∩ F ⁻¹' ball x₀ r₁) := by
        ext w; constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, hOd h1, h2⟩
        · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
      rw [this]
      exact (hO.inter (hFc.isOpen_inter_preimage (coordinateDomain_isOpen hπ.1 e d)
        isOpen_ball)).inter (e.val.isOpen_inter_preimage_symm hN'o)
    have hyU₀ : e.val y ∈ O ∩ F ⁻¹' ball x₀ r₁ ∩ (e.val.target ∩ e.val.symm ⁻¹' N') := by
      refine ⟨⟨hyO, ?_⟩, e.val.map_source hye, ?_⟩
      · have hFy : F (e.val y) = d.val (π y) := coordinateMap_at hye
        rw [mem_preimage, hFy]; exact hy.2
      · rw [mem_preimage, e.val.left_inv hye]; exact hyN'
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU₀ _ hyU₀
    set U := ball (e.val y) ρ with hU
    have hUd : U ⊆ coordinateDomain π e d := fun w hw => hOd (hρU hw).1.1
    have hUb : ∀ w ∈ U, F w ∈ ball x₀ r₁ := fun w hw => (hρU hw).1.2
    have hk' : DifferentiableOn ℂ (fun w => k (F w)) U :=
      hk.comp ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp) |>.mono hUd)
        fun w hw => hUb w hw
    have hkne' : ∀ w ∈ U, ¬ ∀ᶠ w' in 𝓝 w, k (F w') = 0 := fun w hw =>
      not_eventually_zero_comp_coordinateMap hπ.1 hAi hBc hpre hs hright hleft hkne e (hUd hw)
        (hUb w hw)
    have hFe : DifferentiableOn ℂ (fun w => G (F w)) (U ∩ {w | k (F w) ≠ 0}) :=
      hG.comp ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp) |>.mono
        fun w hw => hUd hw.1) fun w hw => ⟨hUb w hw.1, hw.2⟩
    -- square integrability of `G ∘ F` on `U`
    have hUae := inter_ne_zero_ae_eq isOpen_ball hk' hkne'
    have hsq : ∫⁻ w in U, ENNReal.ofReal (‖G (F w)‖ ^ 2) ≠ ⊤ := by
      rw [← setLIntegral_congr hUae]
      have hpt : ∀ w ∈ U ∩ {w | k (F w) ≠ 0}, ENNReal.ofReal (‖G (F w)‖ ^ 2) ≤
          ENNReal.ofReal (2 * Real.exp M) * ENNReal.ofReal (‖hZ (e.val.symm w) - G (F w)‖ ^ 2 *
            Real.exp (-W (e.val.symm w))) + ENNReal.ofReal (2 * Mh ^ 2) := by
        intro w hw
        have hwd := hUd hw.1
        have hFw : F w = d.val (π (e.val.symm w)) := rfl
        obtain ⟨-, -, hE'⟩ := upstairs_facts hpre hleft hkzero hwd.2
          (by rw [← hFw]; exact hUb w hw.1) (by rw [← hFw]; exact hw.2)
        have hWM : W (e.val.symm w) ≤ M := hM _ (hN'N (hρU hw.1).2.2) hE'
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ‖G (F w)‖ ≤ ‖hZ (e.val.symm w) - G (F w)‖ + Mh := by
          have := norm_sub_le (hZ (e.val.symm w)) (hZ (e.val.symm w) - G (F w))
          rw [sub_sub_cancel] at this
          linarith [hMh (e.val.symm w), norm_sub_rev (hZ (e.val.symm w)) (G (F w))]
        have h2 : ‖G (F w)‖ ^ 2 ≤ 2 * ‖hZ (e.val.symm w) - G (F w)‖ ^ 2 + 2 * Mh ^ 2 := by
          have hMh0 : 0 ≤ Mh := (norm_nonneg _).trans (hMh (e.val.symm w))
          nlinarith [sq_nonneg (‖hZ (e.val.symm w) - G (F w)‖ - Mh), norm_nonneg (G (F w))]
        have h3 : 1 ≤ Real.exp M * Real.exp (-W (e.val.symm w)) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
        have h4 : 0 ≤ ‖hZ (e.val.symm w) - G (F w)‖ ^ 2 := sq_nonneg _
        nlinarith
      have hmeas : MeasurableSet (U ∩ {w | k (F w) ≠ 0}) :=
        (hk'.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).measurableSet
      refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' hmeas hpt)
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_, ?_⟩
      · refine ne_top_of_le_ne_top hI.ne (lintegral_mono_set ?_)
        rintro w ⟨hwU, hwk⟩
        exact ⟨(hρU hwU).1.1, hUb w hwU, hwk⟩
      · rw [setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_left))
    obtain ⟨Gy, hGy, hGyeq⟩ := exists_extension_of_locally_sq_integrable isOpen_ball hk' hkne' hFe
      fun w hw => by
        obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp isOpen_ball w hw
        exact ⟨r, hr, hrU, ne_top_of_le_ne_top hsq (lintegral_mono_set hrU)⟩
    exact ⟨U, Gy, isOpen_ball, mem_ball_self hρ, hUd, hGy, fun w hw hkw => hGyeq ⟨hw, hkw⟩⟩
  choose! U Gy hUo hyU hUd hGy hGeq using hloc
  -- the glued function
  set F : Z → ℂ := fun t => Gy t ((complexChartAt (n := n) t).val t) with hFdef
  have hFG : ∀ t ∈ V', k (d.val (π t)) ≠ 0 → F t = G (d.val (π t)) := by
    intro t ht hkt
    have hte := mem_complexChartAt_source (n := n) t
    have hc : coordinateMap π (complexChartAt (n := n) t) d ((complexChartAt (n := n) t).val t) =
        d.val (π t) := coordinateMap_at hte
    have := hGeq t ht _ (hyU t ht) (by rw [hc]; exact hkt)
    rw [hc] at this
    exact this
  -- `k ∘ d ∘ π` does not vanish identically near any point of `V'`
  have hKP : ∀ t ∈ V', ∃ᶠ t' in 𝓝 t, k (d.val (π t')) ≠ 0 := by
    intro t ht
    refine Filter.not_eventually.mp fun hev => ?_
    set e := complexChartAt (n := n) t
    have hte : t ∈ e.val.source := mem_complexChartAt_source t
    have hwd : e.val t ∈ coordinateDomain π e d := mem_coordinateDomain hte ht.1
    apply not_eventually_zero_comp_coordinateMap hπ.1 hAi hBc hpre hs hright hleft hkne e hwd
      (by rw [coordinateMap_at hte]; exact ht.2)
    have hsc : ContinuousAt e.val.symm (e.val t) := e.val.continuousAt_symm (e.val.map_source hte)
    have hev' := hsc.eventually (by rw [e.val.left_inv hte]; exact hev)
    exact hev'
  refine ⟨F, ?_, hFG⟩
  intro y hy
  set e := complexChartAt (n := n) y with he
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  -- near `y`, `F = G_y ∘ e`
  have hFeq : F =ᶠ[𝓝 y] fun t => Gy y (e.val t) := by
    have hN : V' ∩ (e.val.source ∩ e.val ⁻¹' U y) ∈ 𝓝 y :=
      (hV'o.inter (e.val.isOpen_inter_preimage (hUo y hy))).mem_nhds ⟨hy, hye, hyU y hy⟩
    filter_upwards [hN] with t ⟨htV, hte, htU⟩
    set et := complexChartAt (n := n) t
    have htet : t ∈ et.val.source := mem_complexChartAt_source t
    have hc1 : ContinuousAt (fun t' => Gy t (et.val t')) t :=
      ((hGy t htV).continuousOn.continuousAt ((hUo t htV).mem_nhds (hyU t htV))).comp
        (et.val.continuousAt htet)
    have hc2 : ContinuousAt (fun t' => Gy y (e.val t')) t :=
      ((hGy y hy).continuousOn.continuousAt ((hUo y hy).mem_nhds htU)).comp
        (e.val.continuousAt hte)
    by_contra hne
    have hev := (hc1.sub hc2).eventually_ne (sub_ne_zero.mpr hne)
    have hN₁ : V' ∩ (et.val.source ∩ et.val ⁻¹' U t) ∩ (e.val.source ∩ e.val ⁻¹' U y) ∈ 𝓝 t :=
      ((hV'o.inter (et.val.isOpen_inter_preimage (hUo t htV))).inter
        (e.val.isOpen_inter_preimage (hUo y hy))).mem_nhds
        ⟨⟨htV, htet, hyU t htV⟩, hte, htU⟩
    obtain ⟨t', hkt', hne', ⟨ht'V, ht'e, ht'U⟩, ht'e', ht'U'⟩ :=
      ((hKP t htV).and_eventually (hev.and hN₁)).exists
    apply hne'
    have e1 := hGeq t htV _ ht'U (by rw [coordinateMap_at ht'e]; exact hkt')
    have e2 := hGeq y hy _ ht'U' (by rw [coordinateMap_at ht'e']; exact hkt')
    rw [coordinateMap_at ht'e] at e1
    rw [coordinateMap_at ht'e'] at e2
    show Gy t (et.val t') - Gy y (e.val t') = 0
    rw [e1, e2, sub_self]
  have hhol : HolomorphicAt n (fun t => Gy y ((chartAt (ComplexModel n) y) t)) y :=
    MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart (x := y) hye
      (((hUo y hy).eventually_mem (hyU y hy)).mono fun w hw =>
        (hGy y hy).differentiableAt ((hUo y hy).mem_nhds hw))
  exact (hhol.self_of_nhds.congr_of_eventuallyEq hFeq).mdifferentiableWithinAt

/-! ### Membership in the multiplier ideal -/

omit [IsComplexManifold n X] in
/-- **Local upper bound of the weight**: `φ_N` is bounded above near every point of `V`, at the
points where `ψ_E` is finite. -/
theorem exists_realWeight_upper_bound {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {h : Z → ℝ} (hh : ChartSmooth (n := n) h)
    (d : ComplexChart n X) {W : Set (ComplexModel n)} (hW : IsOpen W) {ρ : ComplexModel n → ℝ}
    (hρ : ContinuousOn ρ W) (N : ℕ) {a : ℝ} (ha : 0 ≤ a) {y : Z}
    (hy : y ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' W)) :
    ∃ U ∈ 𝓝 y, ∃ M : ℝ, ∀ t ∈ U, E.weight t ≠ ⊥ → realWeight π E d ρ h N a t ≤ M := by
  obtain ⟨V, hV, hyV, g, hg, K, hK⟩ := exists_local_weight_bounds hE y
  have hgc : ContinuousAt g y := ((hg.1 y hyV).mdifferentiableAt (hV.mem_nhds hyV)).continuousAt
  have hev1 : ∀ᶠ t in 𝓝 y, ‖g t‖ < ‖g y‖ + 1 :=
    hgc.norm.eventually_lt continuousAt_const (lt_add_one _)
  -- the smooth part is continuous at `y`
  have hcont : ContinuousAt (fun t => ρ (d.val (π t)) + h t) y := by
    have h1 : ContinuousAt (fun t => ρ (d.val (π t))) y := by
      refine ContinuousAt.comp (f := fun t => d.val (π t)) ?_ ?_
      · exact hρ.continuousAt (hW.mem_nhds hy.2)
      · exact (d.val.continuousAt hy.1).comp hπ.continuous.continuousAt
    have h2 : ContinuousAt h y := by
      have := TranscendentalRelGen.continuousOn_of_chartSmooth (V := univ) isOpen_univ
        (h := h) (fun e => (hh e).mono inter_subset_left)
      exact this.continuousAt univ_mem
    exact h1.add h2
  have hev2 : ∀ᶠ t in 𝓝 y, ρ (d.val (π t)) + h t < (ρ (d.val (π y)) + h y) + 1 :=
    hcont.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨_, Filter.inter_mem (hev1.and hev2) (hV.mem_nhds hyV),
    ((N : ℝ) + 1) * (K + Real.log ((‖g y‖ + 1) ^ 2)) + a * ((ρ (d.val (π y)) + h y) + 1), ?_⟩
  rintro t ⟨⟨ht1, ht2⟩, htV⟩ hEt
  have hw := hK t htV
  have hwexp : wexp (E.weight t) = Real.exp (E.weight t).toReal := by
    rw [wexp, if_neg hEt]
  have hgpos : 0 < ‖g t‖ ^ 2 := by
    have := hw.1
    rw [hwexp] at hw
    by_contra hle
    push Not at hle
    have h0 : ‖g t‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    have := hw.2
    rw [h0, mul_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  have hle : (E.weight t).toReal ≤ K + Real.log ((‖g y‖ + 1) ^ 2) := by
    have h1 : Real.exp (E.weight t).toReal ≤ Real.exp K * ‖g t‖ ^ 2 := by
      rw [← hwexp]; exact hw.2
    have h2 : (E.weight t).toReal ≤ K + Real.log (‖g t‖ ^ 2) := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp, Real.log_mul (Real.exp_pos K).ne' hgpos.ne', Real.log_exp] at this
    have h3 : Real.log (‖g t‖ ^ 2) ≤ Real.log ((‖g y‖ + 1) ^ 2) :=
      Real.log_le_log hgpos (pow_le_pow_left₀ (norm_nonneg _) ht1.le 2)
    linarith
  have hsm : a * (ρ (d.val (π t)) + h t) ≤ a * ((ρ (d.val (π y)) + h y) + 1) :=
    mul_le_mul_of_nonneg_left ht2.le ha
  unfold realWeight
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hle hN]

/-- **The data is locally `L²` in every preferred chart**: `χ f` with `f ∈ 𝓘(φ)` near the
support of `χ` (read in the chart `e₀`). -/
theorem exists_cutFunction_lintegral_lt_top {φ : Z → EReal} {V : Set Z} (hVo : IsOpen V)
    (husc : ∀ e : ComplexChart n Z,
      UpperSemicontinuousOn (chartFunction φ e) (e.val.target ∩ e.val.symm ⁻¹' V))
    (e₀ : ComplexChart n Z) {w₀ : ComplexModel n} {δ : ℝ}
    (hδt : closedBall w₀ δ ⊆ e₀.val.target)
    {χD : ComplexModel n → ℝ} (hχDb : ∀ w, 0 ≤ χD w ∧ χD w ≤ 1)
    (hχD0 : ∀ w, δ ≤ ‖w - w₀‖ → χD w = 0) {f : Z → ℂ}
    (hfMI : ∀ w ∈ closedBall w₀ δ, MultiplierIntegrableAt (chartFunction φ e₀) 1
      (fun w => f (e₀.val.symm w)) w volume)
    {y : Z} (hyV : y ∈ V) :
    ∃ O : Set (ComplexModel n), IsOpen O ∧ (complexChartAt (n := n) y).val y ∈ O ∧
      ∫⁻ w in O, multiplierDensity (chartFunction φ (complexChartAt (n := n) y)) 1
        (fun w => cutFunction e₀ χD f ((complexChartAt (n := n) y).val.symm w)) w < ⊤ := by
  classical
  set e := complexChartAt (n := n) y with he
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hχ0' : ∀ w ∉ closedBall w₀ δ, ((χD w : ℂ) * f (e₀.val.symm w)) = 0 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    simp [hχD0 w hw.le]
  by_cases hyK : y ∈ e₀.val.symm '' closedBall w₀ δ
  · obtain ⟨w, hwK, rfl⟩ := hyK
    have hwt := hδt hwK
    have hye₀ : e₀.val.symm w ∈ e₀.val.source := e₀.val.map_target hwt
    have hMI := hfMI w hwK
    rw [← e₀.val.right_inv hwt] at hMI
    obtain ⟨-, O, hO, hyO, -, -, hint⟩ := multiplierIntegrableAt_chart_of_isOpen hVo husc
      one_ne_zero (g := f) e e₀ hyV hye hye₀ hMI
    refine ⟨O, hO, hyO, lt_of_le_of_lt (lintegral_mono fun w' => ?_) hint⟩
    simp only [multiplierDensity]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simp only [cutFunction, chartLift]
    split_ifs with h
    · rw [e₀.val.left_inv h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hχDb _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχDb _).2
    · simp
  · have hN : IsOpen (e₀.val.symm '' closedBall w₀ δ)ᶜ :=
      (isClosed_chart_symm_image e₀ (isCompact_closedBall _ _) hδt).isOpen_compl
    refine ⟨e.val.target ∩ e.val.symm ⁻¹' (e₀.val.symm '' closedBall w₀ δ)ᶜ,
      e.val.isOpen_inter_preimage_symm hN,
      ⟨e.val.map_source hye, by rw [mem_preimage, e.val.left_inv hye]; exact hyK⟩, ?_⟩
    have hzero : ∀ w ∈ e.val.target ∩ e.val.symm ⁻¹' (e₀.val.symm '' closedBall w₀ δ)ᶜ,
        multiplierDensity (chartFunction φ e) 1
          (fun w => cutFunction e₀ χD f (e.val.symm w)) w = 0 := by
      intro w hw
      refine multiplierDensity_eq_zero_of_eq_zero _ _ ?_
      exact chartLift_eq_zero e₀ hχ0' hw.2
    rw [setLIntegral_congr_fun ((e.val.isOpen_inter_preimage_symm hN).measurableSet) hzero]
    simp

/-- **Membership of the extension in `𝓘(φ)`** (blueprint `l2:modification-generation`): on
`V' = π⁻¹(d⁻¹ B(x₀, r₁))`, `|F|² ≤ 2 |F - χ f|² + 2 |χ f|²`, the first term is integrable by
`exists_chart_estimate` (`e^{-φ} ≤ e^{M_P} e^{-W}`), the second by
`exists_cutFunction_lintegral_lt_top`. -/
theorem mem_multiplierIdeal_of_estimate {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hAi : interior A = ∅)
    (hBc : IsClosed B) (hpre : π ⁻¹' B = A)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hright : ∀ x ∉ B, π (s x) = x) (hleft : ∀ y ∉ A, s (π y) = y)
    {E : MeteredEffectiveQDivisor n Z} {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    {φ : Z → EReal} {φℝ : Z → ℝ} {V : Set Z}
    (husc : ∀ e : ComplexChart n Z,
      UpperSemicontinuousOn (chartFunction φ e) (e.val.target ∩ e.val.symm ⁻¹' V))
    (hφeq : ∀ t, E.weight t ≠ ⊥ → φ t = (φℝ t : EReal))
    {d : ComplexChart n X} {x₀ : ComplexModel n} {r₁ : ℝ} {k : ComplexModel n → ℂ}
    (hk : DifferentiableOn ℂ k (ball x₀ r₁)) (hkne : ∀ x ∈ ball x₀ r₁, ¬ ∀ᶠ w in 𝓝 x, k w = 0)
    (hkzero : ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball x₀ r₁ →
      (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0)
    (hV'V : π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁) ⊆ V)
    {hZ : Z → ℂ} {W : Z → ℝ} {G : ComplexModel n → ℂ}
    (hfin : ∫⁻ x in ball x₀ r₁ ∩ {x | k x ≠ 0}, ENNReal.ofReal
      (‖hZ (s (d.val.symm x)) - G x‖ ^ 2 *
        Real.exp (-(W (s (d.val.symm x)) + (ER.weight (s (d.val.symm x))).toReal))) < ⊤)
    {MP : ℝ} (hWφ : ∀ t, W t ≤ φℝ t + MP)
    (hZc : ∀ e : ComplexChart n Z, ContinuousOn (fun w => hZ (e.val.symm w)) e.val.target)
    (hWc : ∀ t ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁), k (d.val (π t)) ≠ 0 →
      ∀ e : ComplexChart n Z, t ∈ e.val.source →
        ContinuousAt (fun w => W (e.val.symm w)) (e.val t))
    (hGc : DifferentiableOn ℂ G (ball x₀ r₁ ∩ {x | k x ≠ 0}))
    (hZL2 : ∀ y ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁), ∃ O : Set (ComplexModel n),
      IsOpen O ∧ (complexChartAt (n := n) y).val y ∈ O ∧
      ∫⁻ w in O, multiplierDensity (chartFunction φ (complexChartAt (n := n) y)) 1
        (fun w => hZ ((complexChartAt (n := n) y).val.symm w)) w < ⊤)
    {F : Z → ℂ} (hFd : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) F
      (π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁)))
    (hFG : ∀ t ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁), k (d.val (π t)) ≠ 0 →
      F t = G (d.val (π t)))
    {y : Z} (hy : y ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁)) :
    (multiplierIdeal (n := n) 1 φ).mem y F := by
  set V' := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁) with hV'
  have hV'o : IsOpen V' := (d.val.isOpen_inter_preimage isOpen_ball).preimage hπ.1.continuous
  refine ⟨InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV'o hFd hy, one_pos, ?_⟩
  set e := complexChartAt (n := n) y with he
  set Fe := coordinateMap π e d with hFe
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  obtain ⟨O₁, hO₁, hyO₁, hO₁d, hI⟩ := exists_chart_estimate hπ hAc hBc hpre hs hleft hER hk
    hkzero hfin y hye hy.1
  obtain ⟨O₂, hO₂, hyO₂, hI₂⟩ := hZL2 y hy
  set O₃ := e.val.target ∩ e.val.symm ⁻¹' V' with hO₃
  have hO₃o : IsOpen O₃ := e.val.isOpen_inter_preimage_symm hV'o
  set U := O₁ ∩ O₂ ∩ O₃ with hU
  have hUo : IsOpen U := (hO₁.inter hO₂).inter hO₃o
  have hyU : e.val y ∈ U :=
    ⟨⟨hyO₁, hyO₂⟩, e.val.map_source hye, by rw [mem_preimage, e.val.left_inv hye]; exact hy⟩
  have hUd : U ⊆ coordinateDomain π e d := fun w hw => hO₁d hw.1.1
  have hUb : ∀ w ∈ U, Fe w ∈ ball x₀ r₁ := by
    intro w hw
    have := hw.2.2.2
    exact this
  have hFdiff : DifferentiableOn ℂ (fun w => F (e.val.symm w)) U :=
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hFd).mono fun w hw => hw.2
  have hk' : DifferentiableOn ℂ (fun w => k (Fe w)) U :=
    hk.comp ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp) |>.mono hUd) hUb
  have hkne' : ∀ w ∈ U, ¬ ∀ᶠ w' in 𝓝 w, k (Fe w') = 0 := fun w hw =>
    not_eventually_zero_comp_coordinateMap hπ.1 hAi hBc hpre hs hright hleft hkne e (hUd hw)
      (hUb w hw)
  have hUae := inter_ne_zero_ae_eq hUo hk' hkne'
  refine ⟨U, hUo, hyU, hFdiff, ?_, ?_⟩
  · exact SGPT.Foundations.Analysis.Pending.RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn
      hUo ((husc e).mono fun w hw => ⟨hw.2.1, hV'V hw.2.2⟩) hFdiff.continuousOn one_ne_zero
  · rw [← setLIntegral_congr hUae]
    have hmeas : MeasurableSet (U ∩ {w | k (Fe w) ≠ 0}) :=
      (hk'.continuousOn.isOpen_inter_preimage hUo isOpen_compl_singleton).measurableSet
    have hpt : ∀ w ∈ U ∩ {w | k (Fe w) ≠ 0},
        multiplierDensity (chartFunction φ e) 1 (fun w => F (e.val.symm w)) w ≤
          ENNReal.ofReal (2 * Real.exp MP) * ENNReal.ofReal (‖hZ (e.val.symm w) - G (Fe w)‖ ^ 2 *
            Real.exp (-W (e.val.symm w))) + 2 * multiplierDensity (chartFunction φ e) 1
              (fun w => hZ (e.val.symm w)) w := by
      intro w hw
      have hwd := hUd hw.1
      set t := e.val.symm w with ht
      have hFw : Fe w = d.val (π t) := rfl
      obtain ⟨-, -, hEt⟩ := upstairs_facts hpre hleft hkzero hwd.2
        (by rw [← hFw]; exact hUb w hw.1) (by rw [← hFw]; exact hw.2)
      have htV' : t ∈ V' := hw.1.2.2
      have hFt : F t = G (Fe w) := by rw [hFw]; exact hFG t htV' (by rw [← hFw]; exact hw.2)
      simp only [multiplierDensity, chartFunction]
      rw [← ht, hφeq t hEt, multiplierWeight_coe, one_mul, hFt,
        ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ‖G (Fe w)‖ ^ 2 ≤ 2 * ‖hZ t - G (Fe w)‖ ^ 2 + 2 * ‖hZ t‖ ^ 2 := by
        have h0 := norm_sub_le (hZ t) (hZ t - G (Fe w))
        rw [sub_sub_cancel] at h0
        have h0' : ‖G (Fe w)‖ ^ 2 ≤ (‖hZ t‖ + ‖hZ t - G (Fe w)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖hZ t‖ - ‖hZ t - G (Fe w)‖)]
      have h2 : Real.exp (-φℝ t) ≤ Real.exp MP * Real.exp (-W t) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [hWφ t])
      have hA := Real.exp_pos (-φℝ t)
      have hB : 0 ≤ ‖hZ t - G (Fe w)‖ ^ 2 := sq_nonneg _
      have hC : 0 ≤ ‖hZ t‖ ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h2 hB]
    refine lt_of_le_of_lt (setLIntegral_mono' hmeas hpt) ?_
    set S := U ∩ {w | k (Fe w) ≠ 0} with hS
    have hSo : IsOpen S := hk'.continuousOn.isOpen_inter_preimage hUo isOpen_compl_singleton
    have hXc : ContinuousOn (fun w => ENNReal.ofReal (‖hZ (e.val.symm w) - G (Fe w)‖ ^ 2 *
        Real.exp (-W (e.val.symm w)))) S := by
      intro w hw
      have hwd := hUd hw.1
      have hwt : w ∈ e.val.target := hwd.1
      have hFw : Fe w = d.val (π (e.val.symm w)) := rfl
      have htV' : e.val.symm w ∈ V' := hw.1.2.2
      have hc1 : ContinuousAt (fun w => hZ (e.val.symm w)) w :=
        (hZc e).continuousAt (e.val.open_target.mem_nhds hwt)
      have hc2 : ContinuousAt (fun w => G (Fe w)) w := by
        have hFc : ContinuousAt Fe w :=
          (coordinateMap_contDiffAt hπ.1 e d hwd).continuousAt
        have hΩo : IsOpen (ball x₀ r₁ ∩ {x | k x ≠ 0}) :=
          hk.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
        have hmemΩ : Fe w ∈ ball x₀ r₁ ∩ {x | k x ≠ 0} := ⟨hUb w hw.1, hw.2⟩
        have hGat : ContinuousAt G (Fe w) :=
          (hGc.differentiableAt (hΩo.mem_nhds hmemΩ)).continuousAt
        exact ContinuousAt.comp (f := Fe) hGat hFc
      have hc3 : ContinuousAt (fun w => W (e.val.symm w)) w := by
        have := hWc _ htV' (by rw [← hFw]; exact hw.2) e (e.val.map_target hwt)
        rwa [e.val.right_inv hwt] at this
      exact (ENNReal.continuous_ofReal.continuousAt.comp
        (((hc1.sub hc2).norm.pow 2).mul (Real.continuous_exp.continuousAt.comp hc3.neg))
        ).continuousWithinAt
    have hYm : AEMeasurable (fun w => multiplierDensity (chartFunction φ e) 1
        (fun w => hZ (e.val.symm w)) w) (volume.restrict S) :=
      SGPT.Foundations.Analysis.Pending.RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn
        hSo ((husc e).mono fun w hw => ⟨hw.1.2.1, hV'V hw.1.2.2⟩)
        ((hZc e).mono fun w hw => hw.1.2.1) one_ne_zero
    rw [lintegral_add_left' ((hXc.aemeasurable hmeas).const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ (by simp)]
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_,
      ENNReal.mul_lt_top (by simp) ?_⟩
    · refine lt_of_le_of_lt (lintegral_mono_set ?_) hI
      rintro w ⟨hwU, hwk⟩
      exact ⟨hwU.1.1, hUb w hwU, hwk⟩
    · exact lt_of_le_of_lt (lintegral_mono_set fun w hw => hw.1.1.2) hI₂

/-! ### The pole integral -/

/-- `e^{-(x + c)} = e^{-x} e^{-c}` for `x < ⊤`. -/
theorem multiplierWeight_one_add_coe {x : EReal} (hx : x ≠ ⊤) (c : ℝ) :
    multiplierWeight 1 (x + (c : EReal)) =
      multiplierWeight 1 x * ENNReal.ofReal (Real.exp (-c)) := by
  induction x using EReal.rec with
  | bot =>
      rw [EReal.bot_add, multiplierWeight_bot one_pos, ENNReal.top_mul]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | coe a =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
  | top => exact absurd rfl hx

/-- **The pole integral in another chart** (pure `ℂⁿ` part): if
`∫_O |H|² e^{-x} |τ - τ(w₁)|^{-2q} < ∞` with `τ` a `C¹` map, injective at `w₁`, then
`∫_{B(w₁, r')} |H|² e^{-x} |w - w₁|^{-2q} < ∞` for some `r' > 0` (`|τ w - τ w₁| ≤ L |w - w₁|`). -/
theorem exists_ball_pole_integral {n : ℕ} {τ : ComplexModel n → ComplexModel n}
    {w₁ : ComplexModel n} (hτ : ContDiffAt ℝ 1 τ w₁) {O : Set (ComplexModel n)} (hO : IsOpen O)
    (hw₁ : w₁ ∈ O) (hinj : ∀ w ∈ O, τ w = τ w₁ → w = w₁) {x : ComplexModel n → EReal}
    (hx : ∀ w, x w ≠ ⊤) {H : ComplexModel n → ℂ} (q : ℕ)
    (hint : ∫⁻ w in O, ENNReal.ofReal (‖H w‖ ^ 2) * multiplierWeight 1
      (x w + ((q : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖τ w - τ w₁‖ ^ 2))) < ⊤) :
    ∃ r' : ℝ, 0 < r' ∧ ball w₁ r' ⊆ O ∧
      ∫⁻ w in ball w₁ r', ENNReal.ofReal (‖H w‖ ^ 2) * multiplierWeight 1 (x w) /
        ENNReal.ofReal (‖w - w₁‖ ^ (2 * q)) < ⊤ := by
  obtain ⟨K, t, ht, hLip⟩ := hτ.exists_lipschitzOnWith
  obtain ⟨r', hr', hr'O⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hO.mem_nhds hw₁) ht)
  set L : ℝ := max (K : ℝ) 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL0 : 0 < L := by linarith
  refine ⟨r', hr', fun w hw => (hr'O hw).1, ?_⟩
  have hpt : ∀ w ∈ ball w₁ r', ENNReal.ofReal (‖H w‖ ^ 2) * multiplierWeight 1 (x w) /
      ENNReal.ofReal (‖w - w₁‖ ^ (2 * q)) ≤ ENNReal.ofReal (L ^ (2 * q)) *
        (ENNReal.ofReal (‖H w‖ ^ 2) * multiplierWeight 1
          (x w + ((q : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖τ w - τ w₁‖ ^ 2)))) := by
    intro w hw
    have hwO := (hr'O hw).1
    have hwt := (hr'O hw).2
    by_cases hww : w = w₁
    · subst hww
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        ENNReal.ofReal_zero, ENNReal.log_zero]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · have hq' : (0 : ℝ) < q := by exact_mod_cast hq
        rw [EReal.coe_mul_bot_of_pos hq', EReal.add_bot, multiplierWeight_bot one_pos]
        rw [show 2 * q ≠ 0 by omega |> fun h => (zero_pow h : (0 : ℝ) ^ (2 * q) = 0)]
        rw [ENNReal.ofReal_zero]
        by_cases hH : ENNReal.ofReal (‖H w‖ ^ 2) = 0
        · rw [hH, zero_mul, ENNReal.zero_div]; exact bot_le
        · rw [ENNReal.mul_top hH, ENNReal.mul_top]
          · exact le_top
          · exact (ENNReal.ofReal_pos.mpr (pow_pos hL0 _)).ne'
    · have hτne : τ w ≠ τ w₁ := fun h => hww (hinj w hwO h)
      have hspos : 0 < ‖τ w - τ w₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hτne)
      have hDpos : 0 < ‖w - w₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hww)
      have hlip : ‖τ w - τ w₁‖ ≤ L * ‖w - w₁‖ := by
        have := hLip.dist_le_mul w hwt w₁ (mem_of_mem_nhds ht)
        rw [dist_eq_norm, dist_eq_norm] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      have hlog : ENNReal.log (ENNReal.ofReal (‖τ w - τ w₁‖ ^ 2)) =
          ((Real.log (‖τ w - τ w₁‖ ^ 2) : ℝ) : EReal) :=
        ENNReal.log_ofReal_of_pos (by positivity)
      rw [hlog, ← EReal.coe_mul, multiplierWeight_one_add_coe (hx w)]
      have he : Real.exp (-((q : ℝ) * Real.log (‖τ w - τ w₁‖ ^ 2))) =
          ((‖τ w - τ w₁‖ ^ (2 * q))⁻¹) := by
        rw [Real.exp_neg, ← Real.log_rpow (by positivity), Real.exp_log (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 2
        push_cast; ring
      rw [he]
      set a := ENNReal.ofReal (‖H w‖ ^ 2) * multiplierWeight 1 (x w) with ha
      have hD : 0 < ‖w - w₁‖ ^ (2 * q) := pow_pos hDpos _
      have hS : 0 < ‖τ w - τ w₁‖ ^ (2 * q) := pow_pos hspos _
      have h1 : a / ENNReal.ofReal (‖w - w₁‖ ^ (2 * q)) =
          a * ENNReal.ofReal (‖w - w₁‖ ^ (2 * q))⁻¹ := by
        rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hD, mul_comm]
      have h2 : ENNReal.ofReal (L ^ (2 * q)) * (ENNReal.ofReal (‖H w‖ ^ 2) *
          (multiplierWeight 1 (x w) * ENNReal.ofReal (‖τ w - τ w₁‖ ^ (2 * q))⁻¹)) =
          a * ENNReal.ofReal (L ^ (2 * q) * (‖τ w - τ w₁‖ ^ (2 * q))⁻¹) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hL0.le _), ha]
        ring
      rw [h1, h2]
      refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
      rw [← div_eq_mul_inv, le_div_iff₀ hS, inv_mul_eq_div, div_le_iff₀ hD]
      calc ‖τ w - τ w₁‖ ^ (2 * q) ≤ (L * ‖w - w₁‖) ^ (2 * q) :=
            pow_le_pow_left₀ (norm_nonneg _) hlip _
        _ = L ^ (2 * q) * ‖w - w₁‖ ^ (2 * q) := mul_pow _ _ _
  calc ∫⁻ w in ball w₁ r', ENNReal.ofReal (‖H w‖ ^ 2) * multiplierWeight 1 (x w) /
        ENNReal.ofReal (‖w - w₁‖ ^ (2 * q))
      ≤ ∫⁻ w in ball w₁ r', ENNReal.ofReal (L ^ (2 * q)) *
          (ENNReal.ofReal (‖H w‖ ^ 2) * multiplierWeight 1
            (x w + ((q : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖τ w - τ w₁‖ ^ 2)))) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (L ^ (2 * q)) * ∫⁻ w in ball w₁ r', ENNReal.ofReal (‖H w‖ ^ 2) *
          multiplierWeight 1
            (x w + ((q : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖τ w - τ w₁‖ ^ 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (lintegral_mono_set fun w hw => (hr'O hw).1) hint)

/-- The logarithmic pole `log |e₀ · - w₀|²` on `Z` (extended by `0` off the chart). -/
def poleLog (e₀ : ComplexChart n Z) (w₀ : ComplexModel n) : Z → EReal :=
  chartLift e₀ fun w => ENNReal.log (ENNReal.ofReal (‖w - w₀‖ ^ 2))

omit [IsComplexManifold n Z] in
/-- **The weight with the pole is upper semicontinuous in charts.** -/
theorem upperSemicontinuousOn_chartFunction_add_poleLog {φ : Z → EReal} {V : Set Z}
    (hVo : IsOpen V)
    (husc : ∀ e : ComplexChart n Z,
      UpperSemicontinuousOn (chartFunction φ e) (e.val.target ∩ e.val.symm ⁻¹' V))
    (hφ : ∀ t, φ t ≠ ⊤) (e₀ : ComplexChart n Z) (w₀ : ComplexModel n) (q : ℕ)
    (e : ComplexChart n Z) :
    UpperSemicontinuousOn
      (chartFunction (fun t => φ t + ((q : ℝ) : EReal) * poleLog e₀ w₀ t) e)
      (e.val.target ∩ e.val.symm ⁻¹' (V ∩ e₀.val.source)) := by
  intro w hw
  have hmemV : e.val.target ∩ e.val.symm ⁻¹' V ∈ 𝓝 w :=
    (e.val.isOpen_inter_preimage_symm hVo).mem_nhds ⟨hw.1, hw.2.1⟩
  have h1 : UpperSemicontinuousAt (chartFunction φ e) w := by
    intro y hy
    have := husc e w ⟨hw.1, hw.2.1⟩ y hy
    rwa [nhdsWithin_eq_nhds.mpr hmemV] at this
  have hmem₀ : e.val.target ∩ e.val.symm ⁻¹' e₀.val.source ∈ 𝓝 w :=
    (e.val.isOpen_inter_preimage_symm e₀.val.open_source).mem_nhds ⟨hw.1, hw.2.2⟩
  set L : ComplexModel n → EReal := fun w' =>
    ((q : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (‖e₀.val (e.val.symm w') - w₀‖ ^ 2)) with hL
  have hLeq : (fun w' => ((q : ℝ) : EReal) * poleLog e₀ w₀ (e.val.symm w')) =ᶠ[𝓝 w] L := by
    filter_upwards [hmem₀] with w' hw'
    simp only [poleLog, hL, chartLift_of_mem e₀ _ hw'.2]
  have hLc : ContinuousAt L w := by
    have hc0 : ContinuousAt (fun w' => ENNReal.log (ENNReal.ofReal (‖e₀.val (e.val.symm w') - w₀‖ ^ 2))) w := by
      have hs : ContinuousAt e.val.symm w := e.val.continuousAt_symm hw.1
      have he₀ : ContinuousAt (fun w' => e₀.val (e.val.symm w')) w :=
        ContinuousAt.comp (f := e.val.symm) (e₀.val.continuousAt hw.2.2) hs
      exact ENNReal.continuous_log.continuousAt.comp
        (ENNReal.continuous_ofReal.continuousAt.comp ((he₀.sub continuousAt_const).norm.pow 2))
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · have : L = fun _ => 0 := by funext w'; simp [hL]
      rw [this]; exact continuousAt_const
    · exact (FirstPass.continuous_eReal_const_mul (by exact_mod_cast hq.ne')).continuousAt.comp hc0
  have hLtop : L w ≠ ⊤ := by
    simp only [hL]
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (by exact_mod_cast Nat.cast_nonneg q),
      Or.inl (EReal.coe_ne_top _), Or.inr ?_⟩
    rw [Ne, ENNReal.log_eq_top_iff]; exact ENNReal.ofReal_ne_top
  have h3 : UpperSemicontinuousAt (fun w' => chartFunction φ e w' + L w') w :=
    h1.add' hLc.upperSemicontinuousAt (EReal.continuousAt_add (Or.inl (hφ _)) (Or.inr hLtop))
  have heq : chartFunction (fun t => φ t + ((q : ℝ) : EReal) * poleLog e₀ w₀ t) e =ᶠ[𝓝 w]
      fun w' => chartFunction φ e w' + L w' := by
    filter_upwards [hLeq] with w' hw'
    simp only [chartFunction] at hw' ⊢
    rw [hw']
  have h4 : UpperSemicontinuousAt
      (chartFunction (fun t => φ t + ((q : ℝ) : EReal) * poleLog e₀ w₀ t) e) w := by
    intro y hy
    have hy' : chartFunction φ e w + L w < y := by
      have := heq.self_of_nhds
      simp only at this
      rwa [← this]
    filter_upwards [h3 y hy', heq] with w' hw' hweq
    rwa [hweq]
  exact h4.upperSemicontinuousWithinAt _

/-- **The pole integral at `z` in the preferred chart** (blueprint `l2:modification-generation`):
in the pole chart `e₀`, `F - f = G ∘ d ∘ π - χ f` near `z` and `W = φ + q log |e₀ · - e₀ z|²`, so
`exists_chart_estimate` gives `(F - f) ∈ 𝓘(φ + q log |e₀ · - e₀ z|²)` at `e₀ z`; this is moved to
the preferred chart at `z` (`multiplierIntegrableAt_chart_of_isOpen`) and compared with
`|w - e_z z|^{-2q}` there (`exists_ball_pole_integral`). -/
theorem exists_pole_integral {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hAi : interior A = ∅)
    (hBc : IsClosed B) (hpre : π ⁻¹' B = A)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hright : ∀ x ∉ B, π (s x) = x) (hleft : ∀ y ∉ A, s (π y) = y)
    {E : MeteredEffectiveQDivisor n Z} {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    {φ : Z → EReal} {φℝ : Z → ℝ} {V : Set Z} (hVo : IsOpen V)
    (husc : ∀ e : ComplexChart n Z,
      UpperSemicontinuousOn (chartFunction φ e) (e.val.target ∩ e.val.symm ⁻¹' V))
    (hφtop : ∀ t, φ t ≠ ⊤) (hφeq : ∀ t, E.weight t ≠ ⊥ → φ t = (φℝ t : EReal))
    {d : ComplexChart n X} {x₀ : ComplexModel n} {r₁ : ℝ} {k : ComplexModel n → ℂ}
    (hk : DifferentiableOn ℂ k (ball x₀ r₁)) (hkne : ∀ x ∈ ball x₀ r₁, ¬ ∀ᶠ w in 𝓝 x, k w = 0)
    (hkzero : ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball x₀ r₁ →
      (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0)
    (hV'V : π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁) ⊆ V)
    {hZ : Z → ℂ} {W : Z → ℝ} {G : ComplexModel n → ℂ}
    (hfin : ∫⁻ x in ball x₀ r₁ ∩ {x | k x ≠ 0}, ENNReal.ofReal
      (‖hZ (s (d.val.symm x)) - G x‖ ^ 2 *
        Real.exp (-(W (s (d.val.symm x)) + (ER.weight (s (d.val.symm x))).toReal))) < ⊤)
    {F : Z → ℂ} (hFd : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) F
      (π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁)))
    (hFG : ∀ t ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁), k (d.val (π t)) ≠ 0 →
      F t = G (d.val (π t)))
    (a₀ : Z) {z : Z} (hz₀ : z ∈ (complexChartAt (n := n) a₀).val.source)
    (hzV' : z ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁)) (hkz : k (d.val (π z)) = 0)
    {f : Z → ℂ} {ρf : ℝ} (hρf : 0 < ρf)
    (hfd : DifferentiableOn ℂ (fun w => f ((complexChartAt (n := n) a₀).val.symm w))
      (ball ((complexChartAt (n := n) a₀).val z) ρf))
    (hZf : ∀ w ∈ ball ((complexChartAt (n := n) a₀).val z) ρf,
      hZ ((complexChartAt (n := n) a₀).val.symm w) = f ((complexChartAt (n := n) a₀).val.symm w))
    (q : ℕ)
    (hWlog : ∀ w ∈ ball ((complexChartAt (n := n) a₀).val z) ρf,
      w ≠ (complexChartAt (n := n) a₀).val z →
      E.weight ((complexChartAt (n := n) a₀).val.symm w) ≠ ⊥ →
        W ((complexChartAt (n := n) a₀).val.symm w) =
          φℝ ((complexChartAt (n := n) a₀).val.symm w) +
            q * Real.log (‖w - (complexChartAt (n := n) a₀).val z‖ ^ 2)) :
    ∃ r' : ℝ, 0 < r' ∧
      ball ((complexChartAt (n := n) z).val z) r' ⊆ (complexChartAt (n := n) z).val.target ∧
      (∫⁻ w in ball ((complexChartAt (n := n) z).val z) r',
        multiplierDensity (chartFunction φ (complexChartAt (n := n) z)) 1
          (fun w => F ((complexChartAt (n := n) z).val.symm w) -
            f ((complexChartAt (n := n) z).val.symm w)) w /
          ENNReal.ofReal (‖w - (complexChartAt (n := n) z).val z‖ ^ (2 * q))) < ⊤ := by
  set e₀ := complexChartAt (n := n) a₀ with he₀
  set w₀ := e₀.val z with hw₀
  set V' := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁) with hV'
  have hV'o : IsOpen V' := (d.val.isOpen_inter_preimage isOpen_ball).preimage hπ.1.continuous
  set F₀ := coordinateMap π e₀ d with hF₀
  set uP : Z → EReal := fun t => φ t + ((q : ℝ) : EReal) * poleLog e₀ w₀ t with huP
  obtain ⟨O, hO, hzO, hOd, hI⟩ := exists_chart_estimate hπ hAc hBc hpre hs hleft hER hk hkzero
    hfin a₀ hz₀ hzV'.1
  set U₀ := O ∩ ball w₀ ρf ∩ (e₀.val.target ∩ e₀.val.symm ⁻¹' V') with hU₀
  have hU₀o : IsOpen U₀ := (hO.inter isOpen_ball).inter (e₀.val.isOpen_inter_preimage_symm hV'o)
  have hw₀U₀ : w₀ ∈ U₀ := by
    exact ⟨⟨hzO, mem_ball_self hρf⟩, e₀.val.map_source hz₀, by
      rw [mem_preimage, e₀.val.left_inv hz₀]; exact hzV'⟩
  have hU₀d : U₀ ⊆ coordinateDomain π e₀ d := fun w hw => hOd hw.1.1
  have hU₀b : ∀ w ∈ U₀, F₀ w ∈ ball x₀ r₁ := fun w hw => hw.2.2.2
  have hk' : DifferentiableOn ℂ (fun w => k (F₀ w)) U₀ :=
    hk.comp ((coordinateMap_contDiffOn hπ.1 e₀ d).differentiableOn (by simp) |>.mono hU₀d) hU₀b
  have hkne' : ∀ w ∈ U₀, ¬ ∀ᶠ w' in 𝓝 w, k (F₀ w') = 0 := fun w hw =>
    not_eventually_zero_comp_coordinateMap hπ.1 hAi hBc hpre hs hright hleft hkne e₀ (hU₀d hw)
      (hU₀b w hw)
  have hU₀ae := inter_ne_zero_ae_eq hU₀o hk' hkne'
  have huPusc := upperSemicontinuousOn_chartFunction_add_poleLog hVo husc hφtop e₀ w₀ q
  -- the weighted integrability in the pole chart
  have hdiff : DifferentiableOn ℂ (fun w => F (e₀.val.symm w) - f (e₀.val.symm w)) U₀ :=
    ((MeteredDivisorPositivity.differentiableOn_comp_chartSymm e₀ hFd).mono
      fun w hw => hw.2).sub (hfd.mono fun w hw => hw.1.2)
  have hMI : MultiplierIntegrableAt (chartFunction uP e₀) 1
      (fun w => F (e₀.val.symm w) - f (e₀.val.symm w)) w₀ volume := by
    refine ⟨one_pos, U₀, hU₀o, hw₀U₀, hdiff, ?_, ?_⟩
    · exact SGPT.Foundations.Analysis.Pending.RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn
        hU₀o ((huPusc e₀).mono fun w hw => ⟨hw.2.1, hV'V hw.2.2, e₀.val.map_target hw.2.1⟩)
        hdiff.continuousOn one_ne_zero
    · rw [← setLIntegral_congr hU₀ae]
      refine lt_of_le_of_lt ?_ hI
      have hmeas : MeasurableSet (U₀ ∩ {w | k (F₀ w) ≠ 0}) :=
        (hk'.continuousOn.isOpen_inter_preimage hU₀o isOpen_compl_singleton).measurableSet
      refine (setLIntegral_mono' hmeas fun w hw => le_of_eq ?_).trans
        (lintegral_mono_set fun w hw => ⟨hw.1.1.1, hU₀b w hw.1, hw.2⟩)
      have hwd := hU₀d hw.1
      set t := e₀.val.symm w with ht
      have hFw : F₀ w = d.val (π t) := rfl
      obtain ⟨-, -, hEt⟩ := upstairs_facts hpre hleft hkzero hwd.2
        (by rw [← hFw]; exact hU₀b w hw.1) (by rw [← hFw]; exact hw.2)
      have hww₀ : w ≠ w₀ := by
        rintro rfl
        apply hw.2
        show k (F₀ w₀) = 0
        have hF₀z : F₀ w₀ = d.val (π z) := coordinateMap_at hz₀
        rw [hF₀z]; exact hkz
      have hFt : F t = G (F₀ w) := by rw [hFw]; exact hFG t hw.1.2.2 (by rw [← hFw]; exact hw.2)
      have hft : f t = hZ t := (hZf w hw.1.1.2).symm
      have hpos : 0 < ‖w - w₀‖ ^ 2 := by
        have := norm_pos_iff.mpr (sub_ne_zero.mpr hww₀)
        positivity
      have hpl : poleLog e₀ w₀ t = ((Real.log (‖w - w₀‖ ^ 2) : ℝ) : EReal) := by
        simp only [poleLog, ht]
        rw [chartLift_symm e₀ _ hwd.1, ENNReal.log_ofReal_of_pos hpos]
      have huPt : uP t = ((W t : ℝ) : EReal) := by
        simp only [huP]
        rw [hφeq t hEt, hpl, ← EReal.coe_mul, ← EReal.coe_add, hWlog w hw.1.1.2 hww₀ hEt]
      simp only [multiplierDensity, chartFunction]
      rw [← ht, huPt, multiplierWeight_coe, one_mul, ← ENNReal.ofReal_mul (sq_nonneg _), hFt,
        hft, norm_sub_rev]
  -- transport to the preferred chart at `z`
  set ez := complexChartAt (n := n) z with hez
  have hzez : z ∈ ez.val.source := mem_complexChartAt_source z
  have hMI₀ : MultiplierIntegrableAt (chartFunction uP e₀) 1
      (fun w => (fun t => F t - f t) (e₀.val.symm w)) (e₀.val z) volume := hMI
  obtain ⟨-, Oz, hOz, hzOz, -, -, hintz⟩ := multiplierIntegrableAt_chart_of_isOpen
    (hVo.inter e₀.val.open_source) huPusc one_ne_zero (g := fun t => F t - f t) ez e₀
    ⟨hV'V hzV', hz₀⟩ hzez hz₀ hMI₀
  set Oz' := Oz ∩ (ez.val.target ∩ ez.val.symm ⁻¹' e₀.val.source) with hOz'
  have hOz'o : IsOpen Oz' := hOz.inter (ez.val.isOpen_inter_preimage_symm e₀.val.open_source)
  have hzOz' : ez.val z ∈ Oz' :=
    ⟨hzOz, ez.val.map_source hzez, by rw [mem_preimage, ez.val.left_inv hzez]; exact hz₀⟩
  set τ : ComplexModel n → ComplexModel n := fun w => e₀.val (ez.val.symm w) with hτ
  have hτz : τ (ez.val z) = w₀ := by simp only [hτ, ez.val.left_inv hzez, hw₀]
  have hτsrc : ez.val z ∈ (chartTransition ez e₀).source := by
    simpa [chartTransition, OpenPartialHomeomorph.trans_source, ez.val.left_inv hzez] using
      ⟨ez.val.map_source hzez, hz₀⟩
  have hτc : ContDiffAt ℝ 1 τ (ez.val z) :=
    ((chartTransition_contDiffAt ez e₀ hτsrc).restrict_scalars ℝ).of_le (by simp)
  have hτinj : ∀ w ∈ Oz', τ w = τ (ez.val z) → w = ez.val z := by
    intro w hw hτw
    rw [hτz] at hτw
    have h1 : ez.val.symm w = z := e₀.val.injOn hw.2.2 hz₀ hτw
    rw [← h1, ez.val.right_inv hw.2.1]
  have hint' : ∫⁻ w in Oz', ENNReal.ofReal (‖F (ez.val.symm w) - f (ez.val.symm w)‖ ^ 2) *
      multiplierWeight 1 (φ (ez.val.symm w) + ((q : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (‖τ w - τ (ez.val z)‖ ^ 2))) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt
      (lintegral_mono_set (inter_subset_left : Oz' ⊆ Oz)) hintz)
    refine setLIntegral_congr_fun hOz'o.measurableSet fun w hw => ?_
    simp only [multiplierDensity, chartFunction, poleLog]
    rw [chartLift_of_mem e₀ _ hw.2.2, hτz]
  obtain ⟨r', hr', hr'O, hr'int⟩ := exists_ball_pole_integral hτc hOz'o hzOz' hτinj
    (x := fun w => φ (ez.val.symm w)) (fun w => hφtop _) q hint'
  exact ⟨r', hr', fun w hw => (hr'O hw).2.1, hr'int⟩

/-! ### Regularity of the data and the weight in charts -/

omit [IsComplexManifold n Z] in
/-- The data `χ f` is continuous in every chart. -/
theorem continuousOn_cutFunction [T2Space Z] (e₀ : ComplexChart n Z) {χD : ComplexModel n → ℝ}
    {w₀ : ComplexModel n} {δ : ℝ} (hδt : closedBall w₀ δ ⊆ e₀.val.target)
    (hχD0 : ∀ w, δ ≤ ‖w - w₀‖ → χD w = 0) {f : Z → ℂ}
    (hĥ : Continuous fun w => (χD w : ℂ) * f (e₀.val.symm w)) (e : ComplexChart n Z) :
    ContinuousOn (fun w => cutFunction e₀ χD f (e.val.symm w)) e.val.target := by
  intro w hw
  have hs : ContinuousAt e.val.symm w := e.val.continuousAt_symm hw
  refine ContinuousAt.continuousWithinAt ?_
  by_cases ht : e.val.symm w ∈ e₀.val.source
  · have hev : (fun w' => cutFunction e₀ χD f (e.val.symm w')) =ᶠ[𝓝 w]
        fun w' => (χD (e₀.val (e.val.symm w')) : ℂ) * f (e₀.val.symm (e₀.val (e.val.symm w'))) := by
      filter_upwards [hs.eventually (e₀.val.open_source.mem_nhds ht)] with w' hw'
      exact chartLift_of_mem e₀ _ hw'
    refine ContinuousAt.congr ?_ hev.symm
    exact hĥ.continuousAt.comp (f := fun w' => e₀.val (e.val.symm w'))
      (ContinuousAt.comp (f := e.val.symm) (e₀.val.continuousAt ht) hs)
  · have hN : IsOpen (e₀.val.symm '' closedBall w₀ δ)ᶜ :=
      (isClosed_chart_symm_image e₀ (isCompact_closedBall _ _) hδt).isOpen_compl
    have hzero : ∀ w ∉ closedBall w₀ δ, ((χD w : ℂ) * f (e₀.val.symm w)) = 0 := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm, not_le] at hw
      simp [hχD0 w hw.le]
    have hev : (fun w' => cutFunction e₀ χD f (e.val.symm w')) =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [hs.eventually (hN.mem_nhds (notMem_chart_symm_image hδt ht))] with w' hw'
      exact chartLift_eq_zero e₀ hzero hw'
    exact continuousAt_const.congr hev.symm

omit [IsComplexManifold n Z] in
/-- The data `χ f` is bounded. -/
theorem exists_norm_cutFunction_le (e₀ : ComplexChart n Z) {χD : ComplexModel n → ℝ}
    {w₀ : ComplexModel n} {δ : ℝ} (hχD0 : ∀ w, δ ≤ ‖w - w₀‖ → χD w = 0) {f : Z → ℂ}
    (hĥ : Continuous fun w => (χD w : ℂ) * f (e₀.val.symm w)) :
    ∃ Mh : ℝ, ∀ t, ‖cutFunction e₀ χD f t‖ ≤ Mh := by
  classical
  obtain ⟨M, hM⟩ := (isCompact_closedBall w₀ δ).exists_bound_of_continuousOn hĥ.continuousOn
  refine ⟨max M 0, fun t => ?_⟩
  simp only [cutFunction, chartLift]
  split_ifs with ht
  · by_cases hK : e₀.val t ∈ closedBall w₀ δ
    · exact (hM _ hK).trans (le_max_left _ _)
    · rw [mem_closedBall, dist_eq_norm, not_le] at hK
      rw [hχD0 _ hK.le]; simp
  · simp

omit [IsComplexManifold n X] in
theorem relgenWeight_ne_top {π : Z → X} {D : EffectiveDivisor n Z}
    {E : MeteredEffectiveQDivisor n Z} (hE : DivisorMetric.IsDivisorMetric D E)
    (d : ComplexChart n X) (ρ : ComplexModel n → ℝ) (h : Z → ℝ) (N : ℕ) (a : ℝ) (t : Z) :
    relgenWeight π E d ρ h N a t ≠ ⊤ := by
  have hw := weight_ne_top_of_isDivisorMetric hE t
  unfold relgenWeight
  induction hEt : E.weight t using EReal.rec with
  | bot =>
      rw [EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_add]
      exact bot_ne_top
  | coe x => rw [← EReal.coe_mul, ← EReal.coe_add]; exact EReal.coe_ne_top _
  | top => exact absurd hEt hw

/-- **The weight `φ_N + P` is continuous** at points of `V` off the exceptional set, the divisor and
the pole, in every chart. -/
theorem continuousAt_weight_add_pole {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z)
    (d : ComplexChart n X) {p : ComplexModel n} {r : ℝ} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val d (ball p r) ρ) (N : ℕ)
    (e₀ : ComplexChart n Z) {ε : ℝ} {χP : ComplexModel n → ℝ} (hχP : ContDiff ℝ ∞ χP)
    {w₀ : ComplexModel n} (hεt : closedBall w₀ ε ⊆ e₀.val.target)
    (hχP0 : ∀ w, ε ≤ ‖w‖ → χP w = 0) (q : ℕ)
    {t : Z} (htV : t ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r)) (htE : E.weight t ≠ ⊥)
    (ht₀ : t ∈ e₀.val.source → e₀.val t ≠ w₀) (e : ComplexChart n Z) (hte : t ∈ e.val.source) :
    ContinuousAt (fun w => realWeight π E d ρ h N (((N : ℝ) + 1) / c) (e.val.symm w) +
      poleWeight e₀ χP w₀ q (e.val.symm w)) (e.val t) := by
  have hwt : e.val t ∈ e.val.target := e.val.map_source hte
  have hs : ContinuousAt e.val.symm (e.val t) := e.val.continuousAt_symm hwt
  have hst : e.val.symm (e.val t) = t := e.val.left_inv hte
  obtain ⟨O, hO, hwO, -, hsm, -⟩ := hasLeviLB_realWeight hπ θ β hβ hE hc hh hheq d hρ N htV htE e hte
  have h1 := ((hsm _ hwO).contDiffAt (hO.mem_nhds hwO)).continuousAt
  refine h1.add ?_
  by_cases ht : t ∈ e₀.val.source
  · have hev : (fun w => poleWeight e₀ χP w₀ q (e.val.symm w)) =ᶠ[𝓝 (e.val t)]
        fun w => (q : ℝ) * cutoffPole χP w₀ (e₀.val (e.val.symm w)) := by
      filter_upwards [hs.eventually (by rw [hst]; exact e₀.val.open_source.mem_nhds ht)] with w hw
      exact chartLift_of_mem e₀ _ hw
    refine ContinuousAt.congr ?_ hev.symm
    have hcp : ContinuousAt (cutoffPole χP w₀) (e₀.val t) :=
      (contDiffAt_cutoffPole hχP (ht₀ ht)).continuousAt
    have he₀ : ContinuousAt (fun w => e₀.val (e.val.symm w)) (e.val t) :=
      ContinuousAt.comp (f := e.val.symm) (by rw [hst]; exact e₀.val.continuousAt ht) hs
    have hcp' : ContinuousAt (cutoffPole χP w₀) (e₀.val (e.val.symm (e.val t))) := by
      rw [hst]; exact hcp
    have hcomp : ContinuousAt (fun w => cutoffPole χP w₀ (e₀.val (e.val.symm w))) (e.val t) :=
      ContinuousAt.comp (g := cutoffPole χP w₀) (f := fun w => e₀.val (e.val.symm w)) hcp' he₀
    exact continuousAt_const.mul hcomp
  · have hN : IsOpen (e₀.val.symm '' closedBall w₀ ε)ᶜ :=
      (isClosed_chart_symm_image e₀ (isCompact_closedBall _ _) hεt).isOpen_compl
    have hzero : ∀ w ∉ closedBall w₀ ε, (q : ℝ) * cutoffPole χP w₀ w = 0 := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm, not_le] at hw
      rw [cutoffPole_eq_zero hχP0 hw.le, mul_zero]
    have hev : (fun w => poleWeight e₀ χP w₀ q (e.val.symm w)) =ᶠ[𝓝 (e.val t)] fun _ => 0 := by
      filter_upwards [hs.eventually (by
        rw [hst]; exact hN.mem_nhds (notMem_chart_symm_image hεt ht))] with w hw
      exact chartLift_eq_zero e₀ hzero hw
    exact continuousAt_const.congr hev.symm

/-! ### The non-exceptional case -/

/-- **Points off the exceptional set**: if `z ∉ A`, `π⁻¹(π z) = {z}` and `π` is proper, so
`F = f` works on `π⁻¹ U` for a small `U ∋ π z`. -/
theorem generation_of_not_mem_exceptional {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hpre : π ⁻¹' B = A) (hleft : ∀ y ∉ A, s (π y) = y)
    {φ : Z → EReal} {V : Set Z} (hVo : IsOpen V)
    (husc : ∀ e : ComplexChart n Z,
      UpperSemicontinuousOn (chartFunction φ e) (e.val.target ∩ e.val.symm ⁻¹' V))
    {d : ComplexChart n X} {p : ComplexModel n} {r : ℝ}
    (hV : V = π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r)) {z : Z} (hzV : z ∈ V) (hzA : z ∉ A)
    {f : Z → ℂ} (hf : (multiplierIdeal (n := n) 1 φ).mem z f) (q : ℕ) :
    ∃ U : Set X, IsOpen U ∧ π z ∈ U ∧ U ⊆ d.val.source ∩ d.val ⁻¹' ball p r ∧
      ∃ F : Z → ℂ, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) F (π ⁻¹' U) ∧
        (∀ y ∈ π ⁻¹' U, (multiplierIdeal (n := n) 1 φ).mem y F) ∧
        ∃ r' : ℝ, 0 < r' ∧
          ball ((complexChartAt (n := n) z).val z) r' ⊆ (complexChartAt (n := n) z).val.target ∧
          (∫⁻ w in ball ((complexChartAt (n := n) z).val z) r',
            multiplierDensity (chartFunction φ (complexChartAt (n := n) z)) 1
                (fun w => F ((complexChartAt (n := n) z).val.symm w) -
                  f ((complexChartAt (n := n) z).val.symm w)) w /
              ENNReal.ofReal (‖w - (complexChartAt (n := n) z).val z‖ ^ (2 * q))) < ⊤ := by
  obtain ⟨hhol, -, O, hO, hzO, hdiff, hWL2⟩ := hf
  obtain ⟨H, hHsub, hHo, hzH⟩ := _root_.mem_nhds_iff.mp hhol
  set ez := complexChartAt (n := n) z with hez
  have hzez : z ∈ ez.val.source := mem_complexChartAt_source z
  set Wf := H ∩ V ∩ (ez.val.source ∩ ez.val ⁻¹' O) with hWf
  have hWfo : IsOpen Wf := (hHo.inter hVo).inter (ez.val.isOpen_inter_preimage hO)
  have hzWf : z ∈ Wf := ⟨⟨hzH, hzV⟩, hzez, hzO⟩
  -- membership near `z`
  have hmem : ∀ y ∈ Wf, (multiplierIdeal (n := n) 1 φ).mem y f := by
    intro y hy
    refine ⟨?_, ?_⟩
    · filter_upwards [hHo.mem_nhds hy.1.1] with t ht
      exact hHsub ht
    · exact multiplierIntegrableAt_chart_of_isOpen hVo husc one_ne_zero (g := f)
        (complexChartAt (n := n) y) ez hy.1.2 (mem_complexChartAt_source y) hy.2.1
        ⟨one_pos, O, hO, hy.2.2, hdiff, hWL2⟩
  -- properness
  set U₀ := (π '' Wfᶜ)ᶜ with hU₀
  have hU₀o : IsOpen U₀ := (hπ.2.1.isClosedMap _ hWfo.isClosed_compl).isOpen_compl
  have hzU₀ : π z ∈ U₀ := by
    rintro ⟨y, hy, hyz⟩
    have hzB : π z ∉ B := fun h => hzA (by rw [← hpre]; exact h)
    have hyA : y ∉ A := fun h => hzB (by rw [← hyz]; rw [← hpre] at h; exact h)
    have : y = z := by rw [← hleft y hyA, hyz, hleft z hzA]
    exact hy (this ▸ hzWf)
  have hpre' : ∀ y, π y ∈ U₀ → y ∈ Wf := by
    intro y hy
    by_contra hyW
    exact hy ⟨y, hyW, rfl⟩
  have hzV' := hzV
  rw [hV] at hzV'
  refine ⟨U₀ ∩ (d.val.source ∩ d.val ⁻¹' ball p r), hU₀o.inter (d.val.isOpen_inter_preimage
    isOpen_ball), ⟨hzU₀, hzV'⟩, inter_subset_right, f, ?_, fun y hy => hmem y (hpre' y hy.1), ?_⟩
  · intro y hy
    exact (hHsub (hpre' y hy.1).1.1).mdifferentiableWithinAt
  · obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp ez.val.open_target _ (ez.val.map_source hzez)
    refine ⟨r', hr', hr'sub, ?_⟩
    simp only [sub_self]
    simp [multiplierDensity]

end SGPT.Okounkov.TranscendentalL2
