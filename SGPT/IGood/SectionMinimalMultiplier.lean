import SGPT.Okounkov.AlgebraicSectionBodies
import SGPT.Okounkov.SchemeSectionWeight
import SGPT.Foundations.Analysis.Pending.Envelopes
import SGPT.Foundations.Analysis.Pending.MultiplierIdeals

/-!
# Sections of `L^k` are sections of `L^k ⊗ 𝓘(k V_θ)`

Source `cor:volbigL`, the identity `eq:H0eqH0IVtheta`: for a smooth Hermitian metric `h` on a
line bundle `L` with `θ = c₁(L, h)`,
`H⁰(X, L^k ⊗ 𝓘(k V_θ)) = H⁰(X, L^k)` for every `k > 0` (and trivially for `k = 0`).
The limit assertion of `cor:volbigL` is the case `φ = V_θ` of `thm:DXmain1` and is not covered.

The book's argument: for a nonzero `s ∈ H⁰(X, L^k)` the function `k⁻¹ log |s|²_{h^k}` is
`θ`-psh (Lelong--Poincaré), hence `k⁻¹ log |s|²_{h^k} ⪯ V_θ`; then `s ∈ 𝓘(k V_θ)`. Concretely,
in a local frame `α` with `s = g α^k`,
`|g|² e^{-k V_θ} ≤ e^{kC} |g|² / |s|²_{h^k} = e^{kC} / |α|^{2k}_h`,
which is locally bounded.

## Formal setting

The algebraic setting of the existing section API (`SGPT.Okounkov.AlgebraicSectionBodies`): `X`
is an integral smooth projective complex scheme with analytic point manifold
`SchemeComplexPoint f`, `L : X.Modules` a line bundle with rank-one atlas `b`, `H` a smooth
Hermitian metric on `L` (`SGPT.Okounkov.SchemeLineBundleMetric`) with Chern form
`θ = H.curvature b`, and `V_θ = thetaPshSupremum θ` the pointwise supremum of all nonpositive
`θ`-psh functions. Membership `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` is `SGPT.Okounkov.IsMultiplierSection`.

## Main results

* `SGPT.IGood.isMultiplierSection_thetaPshSupremum`: every nonzero `s ∈ H⁰(X, L^k)` lies in
  `H⁰(X, L^k ⊗ 𝓘(k V_θ))`; with `SGPT.IGood.isMultiplierSection_zero` (the zero section lies in
  every `H⁰(X, L^k ⊗ 𝓘(kφ))`) this gives the identity for all sections,
  `SGPT.IGood.isMultiplierSection_thetaPshSupremum_all`.
* `SGPT.IGood.multiplierSectionSet_thetaPshSupremum`: hence `Γ(θ, V_θ) = Γ(L)`, the convention of
  source `def:Okounkov:L484`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionMinimalTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionMinimalCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance sectionMinimalComplex [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- `(k : EReal) * (k⁻¹ * x) = x` for `k > 0`, including `x = ⊥`. -/
private theorem coe_mul_inv_mul_eq {k : ℝ} (hk : 0 < k) (x : EReal) :
    ((k : ℝ) : EReal) * (((k⁻¹ : ℝ) : EReal) * x) = x := by
  rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hk.ne', EReal.coe_one, one_mul]

variable {f n E}

section Integral

variable [IsIntegral X] {L : X.Modules}

omit [IsIntegral X] in
/-- The local estimate: in the chart at `p` and a frame `α` around `p`, the coefficient `g` of
`s` is in `𝓘(k · k⁻¹ log |s|²_{h^k})`: the weighted density `|g|² e^{-log |s|²}` is bounded by
`|α|^{-2k}_h` near `p`. -/
private theorem multiplierIntegrableAt_sectionLogNormSq (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas L) {k : ℕ} (hk : 0 < k) (s : bundlePowerGlobalSections L k)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    letI := E.isSeparated
    letI := E.quasiCompact
    MultiplierIntegrableAt
      (chartFunction (fun q => (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq b k s q)
        (complexChartAt (n := n) p))
      (k : ℝ)
      (fun z => sectionFrameCoefficient f n E α k s ((complexChartAt (n := n) p).val.symm z))
      ((complexChartAt (n := n) p).val p) volume := by
  let := E.isSeparated
  let := E.quasiCompact
  set e := complexChartAt (n := n) p with he_def
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set G : ComplexModel n → ℂ := fun z => sectionFrameCoefficient f n E α k s (e.val.symm z)
  set F : ComplexModel n → ℝ := fun z => H.frameNormSq α (e.val.symm z)
  set D : Set (ComplexModel n) :=
    e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) with hD_def
  have hDopen : IsOpen D :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hz0D : e.val p ∈ D := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  -- a closed ball around the base point inside the frame domain
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hDopen _ hz0D
  set r' := r / 2
  have hr' : 0 < r' := half_pos hr
  have hcb : closedBall (e.val p) r' ⊆ D := fun z hz =>
    hrD (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hr))
  have hFcont : ContinuousOn F D := (H.smooth α e).continuousOn
  have hFpos : ∀ z ∈ D, 0 < F z := fun z hz => H.positive α _ hz.2
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_closedBall (e.val p) r').exists_isMinOn
    (nonempty_closedBall.mpr hr'.le) (hFcont.mono hcb)
  set m := F zm
  have hm : 0 < m := hFpos zm (hcb hzm)
  -- the density, computed pointwise
  set dens := multiplierDensity
    (chartFunction (fun q => (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq b k s q) e)
    (k : ℝ) G
  have hdens_eq : ∀ z, dens z = ENNReal.ofReal (‖G z‖ ^ 2) *
      (ENNReal.ofReal (H.sectionNormSq b k s (e.val.symm z)))⁻¹ := by
    intro z
    simp only [dens, multiplierDensity, multiplierWeight, chartFunction,
      coe_mul_inv_mul_eq hkR, SchemeLineBundleMetric.sectionLogNormSq, EReal.exp_neg,
      ENNReal.exp_log]
  have hnorm : ∀ z ∈ D, H.sectionNormSq b k s (e.val.symm z) = ‖G z‖ ^ 2 * F z ^ k := by
    intro z hz
    rw [H.sectionNormSq_frame b α k s _ hz.2, Complex.normSq_eq_norm_sq]
    rfl
  have hbound : ∀ z ∈ closedBall (e.val p) r', dens z ≤ ENNReal.ofReal ((m ^ k)⁻¹) := by
    intro z hz
    have hzD := hcb hz
    rw [hdens_eq z, hnorm z hzD]
    by_cases hG : G z = 0
    · simp only [hG, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        ENNReal.ofReal_zero, zero_mul, zero_le]
    · have ha : 0 < ‖G z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hG) 2
      have hb : 0 < F z ^ k := pow_pos (hFpos z hzD) k
      rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (mul_pos ha hb)]
      apply ENNReal.ofReal_le_ofReal
      rw [div_mul_eq_div_div, div_self ha.ne', one_div]
      exact inv_anti₀ (pow_pos hm k) (pow_le_pow_left₀ hm.le (hmin hz) k)
  refine ⟨hkR, ball (e.val p) r', isOpen_ball, mem_ball_self hr', ?_, ?_, ?_⟩
  · -- holomorphy of the coefficient in the chart
    intro z hz
    have hzD : z ∈ D := hcb (ball_subset_closedBall hz)
    exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
      (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).mdifferentiableAt
      ).differentiableWithinAt
  · -- measurability
    have hGc : ContinuousOn G (ball (e.val p) r') := by
      intro z hz
      have hzD : z ∈ D := hcb (ball_subset_closedBall hz)
      exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
        (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).mdifferentiableAt
        ).continuousAt.continuousWithinAt
    have hNc : ContinuousOn (fun z => H.sectionNormSq b k s (e.val.symm z))
        (ball (e.val p) r') :=
      ((H.sectionNormSq_chartSmooth b k s e).continuousOn).mono
        (fun z hz => (hcb (ball_subset_closedBall hz)).1)
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖G z‖ ^ 2))
        (volume.restrict (ball (e.val p) r')) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hGc)).aemeasurable
          measurableSet_ball)
    have h2 : AEMeasurable (fun z => (ENNReal.ofReal (H.sectionNormSq b k s (e.val.symm z)))⁻¹)
        (volume.restrict (ball (e.val p) r')) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (hNc.aemeasurable measurableSet_ball)).inv
    have hfun : dens = fun z => ENNReal.ofReal (‖G z‖ ^ 2) *
        (ENNReal.ofReal (H.sectionNormSq b k s (e.val.symm z)))⁻¹ := funext hdens_eq
    change AEMeasurable dens _
    rw [hfun]
    exact h1.mul h2
  · -- finiteness
    calc (∫⁻ y in ball (e.val p) r', dens y ∂volume)
        ≤ ∫⁻ _ in ball (e.val p) r', ENNReal.ofReal ((m ^ k)⁻¹) ∂volume :=
          setLIntegral_mono measurable_const
            (fun z hz => hbound z (ball_subset_closedBall hz))
      _ = ENNReal.ofReal ((m ^ k)⁻¹) * volume (ball (e.val p) r') := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- Source `cor:volbigL`, identity `eq:H0eqH0IVtheta` (nonzero sections): for a smooth Hermitian
metric `H` on `L` with `θ = c₁(L, H)` and `V_θ` the minimal-singularity potential, every nonzero
`s ∈ H⁰(X, L^k)` lies in `H⁰(X, L^k ⊗ 𝓘(k V_θ))`. -/
theorem isMultiplierSection_thetaPshSupremum (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsMultiplierSection f n E (thetaPshSupremum (H.curvature b).val) k s := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  right
  intro U α p hp
  have : Nonempty (SchemeComplexPoint f) := ⟨p⟩
  set θ := H.curvature b
  set u : SchemeComplexPoint f → EReal :=
    fun q => (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq b k s q
  have hu : IsThetaPshPotential θ.val u :=
    H.isThetaPshPotential_normalized_sectionLogNormSq b k hk s hs
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
      hu.1.hasSmoothLocalPotentials ⟨u, hu⟩
  obtain ⟨C, hC⟩ := SGPT.Foundations.Analysis.Pending.thetaPshSupremum_minimalSingularities
    θ.val θ.2.1 θ.2.2 hu.1.hasSmoothLocalPotentials ⟨u, hu⟩ u hu
  have hpe : p ∈ (complexChartAt (n := n) p).val.source := mem_complexChartAt_source p
  have hz0 := (complexChartAt (n := n) p).val.map_source hpe
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, ?_⟩
  exact multiplierIntegrableAt_of_moreSingularAt
    (hV.1.quasiPlurisubharmonic (complexChartAt (n := n) p) _ hz0)
    ⟨C, Eventually.of_forall fun z => hC _ (mem_univ _)⟩
    (multiplierIntegrableAt_sectionLogNormSq H b hk s α p hp)

omit [IsIntegral X] in
/-- The frame coefficient of the zero section vanishes on the frame domain. -/
theorem sectionFrameCoefficient_zero {U : X.Opens} (α : LocalBundleFrame L U) (k : ℕ)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    sectionFrameCoefficient f n E α k (0 : bundlePowerGlobalSections L k) p = 0 := by
  have h := schemeOpenRegularFunction_add f n E U 0 0 hp
  simp only [add_zero] at h
  unfold sectionFrameCoefficient
  rw [map_zero, map_zero]
  linear_combination -h

omit [IsIntegral X] in
/-- The zero section lies in `H⁰(X, L^k ⊗ 𝓘(kφ))` for every weight `φ`. -/
theorem isMultiplierSection_zero (φ : SchemeComplexPoint f → EReal) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsMultiplierSection f n E φ k (0 : bundlePowerGlobalSections L k) := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  right
  intro U α p hp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hDopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, ?_⟩
  refine (multiplierIntegrableAt_zero (chartFunction φ e) hkR (e.val p) volume).congr
    (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hDopen.mem_nhds hz0D] with z hz
  exact (sectionFrameCoefficient_zero α k hz.2).symm

/-- Source `cor:volbigL`, identity `eq:H0eqH0IVtheta`, for all sections:
`H⁰(X, L^k ⊗ 𝓘(k V_θ)) = H⁰(X, L^k)` for every `k`, with `θ = c₁(L, H)`. -/
theorem isMultiplierSection_thetaPshSupremum_all (H : SchemeLineBundleMetric f n E L)
    (b : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsMultiplierSection f n E (thetaPshSupremum (H.curvature b).val) k s := by
  by_cases hs : s = 0
  · subst hs
    exact isMultiplierSection_zero _ k
  · exact isMultiplierSection_thetaPshSupremum H b k s hs

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- `Γ(θ, V_θ) = Γ(L)` (convention of source `def:Okounkov:L484`, from `eq:H0eqH0IVtheta`): the
multiplier section set of the minimal-singularity potential `V_θ` of `θ = c₁(L, H)` is the whole
section semigroup of `L`. -/
theorem multiplierSectionSet_thetaPshSupremum (H : SchemeLineBundleMetric f n E L)
    (a b : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    multiplierSectionSet f n E Y hY a (thetaPshSupremum (H.curvature b).val) =
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  apply le_antisymm (multiplierSectionSet_subset a _)
  rintro z ⟨k, s, hs, rfl⟩
  exact ⟨k, s, hs, isMultiplierSection_thetaPshSupremum H b k s hs, rfl⟩

end Integral

end SGPT.IGood
