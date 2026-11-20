import SGPT.PSH.RIsoAGermOrder
import SGPT.PSH.LogResFinSNC
import SGPT.PSH.LogResFinModification
import SGPT.PSH.NativeLogIntegralEquation
import SGPT.PSH.NativeLogAnyDimension
import SGPT.PSH.SourceSNCCoordinateOrders
import SGPT.PSH.FiniteCartierGeneratorProduct
import SGPT.Trace.BertiniRestriction
import SGPT.Foundations.Analysis.Pending.LelongNumberFiniteness
import SGPT.Foundations.Analysis.Pending.HolomorphicCoordinateOrders
import SGPT.Foundations.Analysis.Pending.AnalyticModificationJacobianMultiplierGerms

/-!
# Local analysis for the finite log-resolution test of `thm:valuativemulti`

Source: `chapter_pshfunctions.tex`, `thm:valuativemulti`, final clause (finite test on a log
resolution; erratum E07: all components of the resolved polar divisor meeting `π⁻¹(x)`).  This
file collects the local facts about a potential `u` with log singularities along a simple normal
crossing effective `ℚ`-divisor `D` (`NativeHasLogSingularitiesAlong`, `def:pshfunctions:L1393`)
that the finite test needs.

* `multiplierIntegrableAt_of_weight_le_aemeasurable`: a weighted `L²` germ stays weighted `L²`
  for a measurable weight `ψ` with `e^{-cψ} ≤ A e^{-cφ}` near the point.
* `coefficient_le_squaredLogLelongNumber`: at every point `z` of a component `P` of `D`, the
  (book-normalised, squared-log) Lelong number of `u` is at least the coefficient of `P`:
  near `z`, `u = (1/d) log |g|² + O(1)` with `g` a generator of the integral divisor `d · D`
  (`NativeHasLogSingularitiesAlong.exists_original_integral_equation`), and in simple normal
  crossing coordinates `g` is divisible by the `d · coeff(P)`-th power of the coordinate of `P`.
* `exists_weight_lower_bound`: in simple normal crossing coordinates `ζ` at `y`,
  `u ≥ Σ_P coeff(P) log |ζ_{j(P)}|² - C` near `y`, the sum over the components `P` through `y`
  (`j(P)` the coordinate of `P`).

Blueprint: `claude-valmult.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace SGPT.PSH.ValMultLocal

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves BlowupFlatCoordinates NormalCrossings

universe u

/-! ### Comparison of weights -/

/-- If `ψ` is measurable near `z` and `e^{-cψ} ≤ A e^{-cφ}` near `z`, a germ in `𝓘(cφ)_z`
lies in `𝓘(cψ)_z`. -/
theorem multiplierIntegrableAt_of_weight_le_aemeasurable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {φ ψ : E → EReal}
    {c : ℝ} (hc : 0 < c) {f : E → ℂ} {z : E} {U : Set E} (hU : IsOpen U) (hz : z ∈ U)
    (hψ : AEMeasurable ψ (μ.restrict U)) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hw : ∀ y ∈ U, multiplierWeight c (ψ y) ≤ A * multiplierWeight c (φ y))
    (hf : MultiplierIntegrableAt φ c f z μ) : MultiplierIntegrableAt ψ c f z μ := by
  obtain ⟨-, V, hV, hzV, hfV, -, hint⟩ := hf
  have hVU : IsOpen (V ∩ U) := hV.inter hU
  refine ⟨hc, V ∩ U, hVU, ⟨hzV, hz⟩, hfV.mono inter_subset_left, ?_, ?_⟩
  · have h1 : AEMeasurable (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) (μ.restrict (V ∩ U)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn
          (continuous_norm.comp_continuousOn (hfV.continuousOn.mono inter_subset_left))).aemeasurable
          hVU.measurableSet)
    have hψ' : AEMeasurable ψ (μ.restrict (V ∩ U)) :=
      hψ.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    have h2 : AEMeasurable (fun y => multiplierWeight c (ψ y)) (μ.restrict (V ∩ U)) :=
      (multiplierWeight_antitone hc.le).measurable.comp_aemeasurable hψ'
    exact h1.mul h2
  · calc ∫⁻ y in V ∩ U, multiplierDensity ψ c f y ∂μ
        ≤ ∫⁻ y in V ∩ U, A * multiplierDensity φ c f y ∂μ := by
          refine setLIntegral_mono' hVU.measurableSet fun y hy => ?_
          unfold multiplierDensity
          calc ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (ψ y)
              ≤ ENNReal.ofReal (‖f y‖ ^ 2) * (A * multiplierWeight c (φ y)) :=
                mul_le_mul' le_rfl (hw y hy.2)
            _ = A * (ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (φ y)) := by ring
      _ = A * ∫⁻ y in V ∩ U, multiplierDensity φ c f y ∂μ := lintegral_const_mul' _ _ hA
      _ ≤ A * ∫⁻ y in V, multiplierDensity φ c f y ∂μ :=
          mul_le_mul' le_rfl (lintegral_mono_set inter_subset_left)
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hA) hint

/-- An upper semicontinuous function on an open set is measurable for the restricted measure. -/
theorem aemeasurable_restrict_of_upperSemicontinuousOn {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {v : E → EReal} {U : Set E}
    (hU : IsOpen U) (hv : UpperSemicontinuousOn v U) : AEMeasurable v (μ.restrict U) := by
  classical
  let v' : E → EReal := fun y => if y ∈ U then v y else ⊤
  have hv' : UpperSemicontinuous v' := by
    intro y a hya
    by_cases hy : y ∈ U
    · have hua : v y < a := by simpa [v', hy] using hya
      have hlocal := hv y hy a hua
      rw [hU.nhdsWithin_eq hy] at hlocal
      filter_upwards [hlocal, hU.mem_nhds hy] with z hz hzU
      simpa [v', hzU] using hz
    · simp [v', hy] at hya
  apply hv'.measurable.aemeasurable.congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
  simp [v', hy]

/-- `e^{-(t - C)} = e^{C} e^{-t}`. -/
theorem multiplierWeight_one_add_coe (t : EReal) (C : ℝ) :
    multiplierWeight 1 (t + ((-C : ℝ) : EReal)) =
      ENNReal.ofReal (Real.exp C) * multiplierWeight 1 t := by
  have hneg : -(t + ((-C : ℝ) : EReal)) = -t + ((C : ℝ) : EReal) := by
    have hC : -(((-C : ℝ)) : EReal) = ((C : ℝ) : EReal) := by rw [← EReal.coe_neg, neg_neg]
    rw [EReal.neg_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _)),
      sub_eq_add_neg, hC]
  simp only [multiplierWeight, EReal.coe_one, one_mul]
  rw [hneg, EReal.exp_add, EReal.exp_coe, mul_comm]


/-- The real-to-extended-real cast commutes with finite sums. -/
theorem coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

/-- A finite sum of extended reals with one term `⊥` is `⊥`. -/
theorem finset_sum_eq_bot {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → EReal} {i : ι}
    (hi : i ∈ s) (hfi : f i = ⊥) : ∑ k ∈ s, f k = ⊥ := by
  rw [← Finset.add_sum_erase s f hi, hfi, EReal.bot_add]

/-! ### Adapted coordinates -/

section Coordinates

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]

/-- The inverse of adapted coordinates `ζ = Φ(e(w))` at `y` (`e` the preferred chart). -/
def adaptedInv (y : Y) (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y)) :
    ComplexModel n → Y :=
  fun ζ => (chartAt (ComplexModel n) y).symm (Φ.invFun ζ)

theorem zero_mem_target (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0) : (0 : ComplexModel n) ∈ Φ.target := by
  rw [← h0]
  exact Φ.mapsTo_toFun Φ.center_mem_source

theorem tendsto_adaptedInv (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0) :
    Tendsto (adaptedInv y Φ) (𝓝 0) (𝓝 y) := by
  have h0t := zero_mem_target y Φ h0
  have hinv0 : Φ.invFun 0 = (chartAt (ComplexModel n) y) y := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have hc1 : ContinuousAt Φ.invFun 0 :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)).continuousAt
  have hc2 : ContinuousAt (chartAt (ComplexModel n) y).symm (Φ.invFun 0) := by
    rw [hinv0]
    exact (chartAt (ComplexModel n) y).continuousAt_symm
      ((chartAt (ComplexModel n) y).map_source (mem_chart_source _ y))
  have h := (hc2.comp hc1).tendsto
  have hy : (chartAt (ComplexModel n) y).symm (Φ.invFun 0) = y := by
    rw [hinv0]
    exact (chartAt (ComplexModel n) y).left_inv (mem_chart_source _ y)
  simp only [Function.comp_def, hy] at h
  exact h

theorem eventually_flatCoord_adaptedInv (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0) :
    ∀ᶠ ζ in 𝓝 (0 : ComplexModel n), ∀ k, flatCoord Φ k (adaptedInv y Φ ζ) = ζ k := by
  filter_upwards [Φ.isOpen_target.mem_nhds (zero_mem_target y Φ h0)] with ζ hζ k
  have hs : Φ.invFun ζ ∈ Φ.source := Φ.mapsTo_invFun hζ
  simp only [flatCoord, adaptedInv]
  rw [(chartAt (ComplexModel n) y).right_inv (hsrc hs), Φ.right_inv ζ hζ]

end Coordinates

/-! ### Generators of the components in adapted coordinates -/

section Generators

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- Through `y`, the ideal of a component which is the coordinate hyperplane `ζ_j = 0` near `y`
is generated by that coordinate. -/
theorem primeIdeal_mem_iff_flatCoord (P : GeometricPrimeCarrier (m + 1) Y) {y : Y}
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (j : Fin (m + 1))
    (hflat : ∀ {w : Y}, w ∈ (chartAt (ComplexModel (m + 1)) y).source →
      (chartAt (ComplexModel (m + 1)) y) w ∈ Φ.source →
        (w ∈ P.val ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) w) j = 0))
    (h : Y → ℂ) :
    (geometricPrimeCarrierEffectiveDivisor P).ideal.mem y h ↔
      IsInSpanAt (n := m + 1) (· = flatCoord Φ j) y h := by
  rw [geometricPrimeCarrierEffectiveDivisor_ideal]
  exact MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ hflat (mem_flatDomain_self Φ) h

/-- Away from a component its ideal is the unit ideal. -/
theorem primeIdeal_mem_iff_one (P : GeometricPrimeCarrier (m + 1) Y) {y : Y} (hy : y ∉ P.val)
    (h : Y → ℂ) :
    (geometricPrimeCarrierEffectiveDivisor P).ideal.mem y h ↔
      IsInSpanAt (n := m + 1) (· = fun _ => (1 : ℂ)) y h := by
  rw [geometricPrimeCarrierEffectiveDivisor_ideal, MemberPullback.isInSpanAt_one_iff]
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, ?_⟩⟩
  filter_upwards [P.isClosed.isOpen_compl.mem_nhds hy] with w hw hwP
  exact absurd hwP hw

open Classical in
/-- The local generator of a component at `y`: its coordinate if `y` lies on it, `1` otherwise. -/
def componentGenerator (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    {D : EffectiveGeometricQDivisor (m + 1) Y}
    (j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1))
    (P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}) : Y → ℂ :=
  if y ∈ P.val.val then flatCoord Φ (j P) else fun _ => (1 : ℂ)

/-- In adapted coordinates at `y`, the integral divisor `Σ_{P ∈ s} a_P P` has the product of
the component generators as local generator. -/
theorem sum_ideal_mem_iff_prod {D : EffectiveGeometricQDivisor (m + 1) Y} (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1))
    (hflat : ∀ P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}, y ∈ P.val.val →
      ∀ {w : Y}, w ∈ (chartAt (ComplexModel (m + 1)) y).source →
        (chartAt (ComplexModel (m + 1)) y) w ∈ Φ.source →
          (w ∈ P.val.val ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) w) (j P) = 0))
    (s : Finset {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P})
    (a : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → ℕ) (h : Y → ℂ) :
    (∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val).ideal.mem y h ↔
      IsInSpanAt (n := m + 1)
        (· = fun w => ∏ P ∈ s, componentGenerator y Φ j P w ^ a P) y h := by
  classical
  apply finite_cartier_sum_generator_product s (fun P => geometricPrimeCarrierEffectiveDivisor P.val)
    a (componentGenerator y Φ j) y
  · intro P _
    unfold componentGenerator
    split_ifs
    · exact holomorphicAt_flatCoord Φ (j P) (mem_flatDomain_self Φ)
    · exact holomorphicAt_const 1
  · intro P _ h'
    unfold componentGenerator
    split_ifs with hyP
    · exact primeIdeal_mem_iff_flatCoord P.val Φ (j P) (hflat P hyP) h'
    · exact primeIdeal_mem_iff_one P.val hyP h'

theorem holomorphicAt_prod_componentGenerator {D : EffectiveGeometricQDivisor (m + 1) Y} (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1))
    (s : Finset {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P})
    (a : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → ℕ) :
    HolomorphicAt (m + 1) (fun w => ∏ P ∈ s, componentGenerator y Φ j P w ^ a P) y := by
  classical
  apply MonomialPart.holomorphicAt_finset_prod s
  intro P _
  apply CompanionReduction.holomorphicAt_pow_of
  unfold componentGenerator
  split_ifs
  · exact holomorphicAt_flatCoord Φ (j P) (mem_flatDomain_self Φ)
  · exact holomorphicAt_const 1

/-- The adapted coordinate maps: `ζ_j` in coordinates centred at `y` and adapted to the components
of `D` through `y` (simple normal crossing coordinates). -/
theorem exists_adapted_coordinates {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNCComponentwise) (y : Y) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
      (j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1)),
      Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target ∧
      Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0 ∧
      (∀ P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}, y ∈ P.val.val →
        ∀ {w : Y}, w ∈ (chartAt (ComplexModel (m + 1)) y).source →
          (chartAt (ComplexModel (m + 1)) y) w ∈ Φ.source →
            (w ∈ P.val.val ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) w) (j P) = 0)) ∧
      InjOn j {P | y ∈ P.val.val} := by
  classical
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, hinj⟩ := hD y
  have hj : ∀ P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P},
      y ∈ P.val.val → ∃ k, S P = {k} := fun P hP => Finset.card_eq_one.mp (hcard P hP)
  choose! j hjS using hj
  refine ⟨Φ, j, hsrc, h0, ?_, ?_⟩
  · intro P hP w hw hwΦ
    have h := hflat P hP hw hwΦ
    rw [hjS P hP] at h
    simpa only [coordSubspace, Finset.mem_singleton, forall_eq, Set.mem_ofPred_eq,
      complexChartAt] using h
  · intro P hP Q hQ hPQ
    exact hinj hP hQ (by rw [hjS P hP, hjS Q hQ, hPQ])

end Generators

/-! ### The Lelong numbers along the components -/

section Lelong

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] {D : EffectiveGeometricQDivisor (m + 1) Y}

/-- The rational coefficient `1 / d` of the local integral equation, as a real number. -/
private theorem inv_cast_eq (d : ℕ) : (((1 / (d : ℚ) : ℚ)) : ℝ) = 1 / (d : ℝ) := by
  push_cast
  ring

/-- **The Lelong number of `u` along a component is at least its coefficient**: if `u` has log
singularities along the simple normal crossing divisor `D` and `z` lies on the component `P`,
then `ν(u, z) ≥ coeff_D(P)` (book normalisation `ν(log |z|², 0) = 1`). -/
theorem coefficient_le_squaredLogLelongNumber {u : Y → EReal}
    (hu : NativeHasLogSingularitiesAlong D u) (hD : D.IsSNCComponentwise)
    (P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}) {z : Y}
    (hz : z ∈ P.val.val) :
    ENNReal.ofReal (D.coefficient P.val : ℝ) ≤
      SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) u z := by
  classical
  obtain ⟨V, hzV, s, d, a, hs, hd, ha, g, hgen, b, hb, hueq⟩ :=
    hu.exists_original_integral_equation z
  obtain ⟨Φ, j, hsrc, h0, hflat, -⟩ := exists_adapted_coordinates hD z
  let e := chartAt (ComplexModel (m + 1)) z
  have hPs : P ∈ s := (hs P).mpr ⟨z, hz, hzV⟩
  obtain ⟨haP, hcoef⟩ := ha P hPs
  set q : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Y → ℂ :=
    componentGenerator z Φ j with hq
  obtain ⟨hgz, hgenz⟩ := hgen.self_of_nhds
  -- `g` is a multiple of the product of the component generators
  have hgmem : IsInSpanAt (n := m + 1) (· = fun w => ∏ Q ∈ s, q Q w ^ a Q) z g := by
    apply (sum_ideal_mem_iff_prod z Φ j hflat s a g).mp
    exact (hgenz g).mpr (HolomorphicIdealSheaves.isInSpanAt_of_eq_mul rfl hgz
      (holomorphicAt_const 1) (Eventually.of_forall fun w => by simp))
  obtain ⟨-, h, hh, hgeq⟩ := HolomorphicIdealSheaves.isInSpanAt_eq_iff.mp hgmem
  -- bounds on the other factors
  have hqcont : ∀ Q ∈ s.erase P, ∀ᶠ w in 𝓝 z, ‖q Q w‖ ≤ ‖q Q z‖ + 1 := by
    intro Q _
    have hc : ContinuousAt (q Q) z := by
      simp only [hq, componentGenerator]
      split_ifs
      · exact (holomorphicAt_flatCoord Φ (j Q) (mem_flatDomain_self Φ)).continuousAt
      · exact continuousAt_const
    exact (hc.norm.eventually (gt_mem_nhds (lt_add_one ‖q Q z‖))).mono fun _ hw => hw.le
  have hhcont : ∀ᶠ w in 𝓝 z, ‖h w‖ ≤ ‖h z‖ + 1 :=
    (hh.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖h z‖))).mono fun _ hw => hw.le
  -- Lipschitz bound for the coordinates
  have hΦd : DifferentiableAt ℂ Φ.toFun (e z) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  obtain ⟨L₀, hL₀⟩ := hΦd.isBigO_sub.bound
  have hLip : ∀ᶠ w in 𝓝 z, ‖Φ.toFun (e w)‖ ≤ max L₀ 1 * ‖e w - e z‖ := by
    have he : Tendsto e (𝓝 z) (𝓝 (e z)) := (e.continuousAt (mem_chart_source _ z)).tendsto
    filter_upwards [he.eventually hL₀] with w hw
    have h0' : Φ.toFun (e z) = 0 := h0
    rw [h0', sub_zero] at hw
    exact hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hqP : ∀ w, z ∈ P.val.val → q P w = Φ.toFun (e w) (j P) := by
    intro w hzP
    simp only [hq, componentGenerator, if_pos hzP, flatCoord]
    rfl
  obtain ⟨B, -, hB⟩ := hb
  set K : ℝ := (‖h z‖ + 1) * ∏ Q ∈ s.erase P, (‖q Q z‖ + 1) ^ a Q with hK
  have hKpos : 0 < K := by
    apply mul_pos (by positivity)
    exact Finset.prod_pos fun Q _ => pow_pos (by positivity) _
  set L : ℝ := max L₀ 1 with hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  set γ : ℝ≥0 := Real.toNNReal (D.coefficient P.val : ℝ) with hγ
  have hγr : (γ : ℝ) = (a P : ℝ) / d := by
    rw [hγ, Real.coe_toNNReal _ (by exact_mod_cast (D.coefficient_nonneg P.val)), hcoef]
    push_cast
    ring
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set C : ℝ := (2 * Real.log K + 2 * (a P : ℝ) * Real.log L) / d + B with hC
  -- the growth bound off `z`
  have hev : ∀ᶠ w in 𝓝[≠] z, u w ≤ (((γ : ℝ) * Real.log (‖(complexChartAt (n := m + 1) z).val w -
      (complexChartAt (n := m + 1) z).val z‖ ^ 2) + C : ℝ) : EReal) := by
    have hnear : ∀ᶠ w in 𝓝 z, (u w = (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (g w) +
        (b w : EReal)) ∧ g w = h w * ∏ Q ∈ s, q Q w ^ a Q ∧ ‖h w‖ ≤ ‖h z‖ + 1 ∧
        (∀ Q ∈ s.erase P, ‖q Q w‖ ≤ ‖q Q z‖ + 1) ∧ ‖Φ.toFun (e w)‖ ≤ L * ‖e w - e z‖ ∧
        |b w| ≤ B ∧ w ∈ e.source := by
      filter_upwards [hueq, hgeq, hhcont, (Filter.eventually_all_finset _).mpr hqcont, hLip, hB,
        e.open_source.mem_nhds (mem_chart_source _ z)] with w h1 h2 h3 h4 h5 h6 h7
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with w hw hwz
    obtain ⟨hu1, hg1, hh1, hq1, hL1, hb1, hwe⟩ := hw
    have hr : 0 < ‖e w - e z‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro heq
      exact hwz (e.injOn hwe (mem_chart_source _ z) heq)
    change u w ≤ (((γ : ℝ) * Real.log (‖e w - e z‖ ^ 2) + C : ℝ) : EReal)
    rw [hu1]
    by_cases hgw : g w = 0
    · rw [hgw, logNormSq_zero, EReal.coe_mul_bot_of_pos (by rw [inv_cast_eq]; positivity),
        EReal.bot_add]
      exact bot_le
    have hgpos : 0 < ‖g w‖ := norm_pos_iff.mpr hgw
    rw [logNormSq, ENNReal.log_ofReal_of_pos (pow_pos hgpos 2), ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff, inv_cast_eq]
    -- the norm bound `‖g w‖ ≤ K (L ‖e w - e z‖)^{a_P}`
    have hqPw : ‖q P w‖ ≤ L * ‖e w - e z‖ := by
      rw [hqP w hz]
      exact (PiLp.norm_apply_le _ _).trans hL1
    have hprod : ‖∏ Q ∈ s, q Q w ^ a Q‖ ≤
        (L * ‖e w - e z‖) ^ a P * ∏ Q ∈ s.erase P, (‖q Q z‖ + 1) ^ a Q := by
      rw [← Finset.mul_prod_erase s (fun Q => q Q w ^ a Q) hPs, norm_mul, norm_pow,
        norm_prod]
      apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hqPw _) _ (by positivity) (by positivity)
      apply Finset.prod_le_prod (fun Q _ => norm_nonneg _)
      intro Q hQ
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hq1 Q hQ) _
    have hgle : ‖g w‖ ≤ K * (L * ‖e w - e z‖) ^ a P := by
      rw [hg1, norm_mul, hK]
      calc ‖h w‖ * ‖∏ Q ∈ s, q Q w ^ a Q‖ ≤ (‖h z‖ + 1) *
            ((L * ‖e w - e z‖) ^ a P * ∏ Q ∈ s.erase P, (‖q Q z‖ + 1) ^ a Q) :=
          mul_le_mul hh1 hprod (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hlog : Real.log (‖g w‖ ^ 2) ≤
        2 * Real.log K + 2 * (a P : ℝ) * Real.log L + (a P : ℝ) * Real.log (‖e w - e z‖ ^ 2) := by
      have h1 : Real.log (‖g w‖ ^ 2) = 2 * Real.log ‖g w‖ := by
        rw [Real.log_pow]; push_cast; ring
      have h2 : Real.log ‖g w‖ ≤ Real.log (K * (L * ‖e w - e z‖) ^ a P) :=
        Real.log_le_log hgpos hgle
      have h3 : Real.log (K * (L * ‖e w - e z‖) ^ a P) =
          Real.log K + (a P : ℝ) * (Real.log L + Real.log ‖e w - e z‖) := by
        rw [Real.log_mul hKpos.ne' (by positivity), Real.log_pow, Real.log_mul hLpos.ne' hr.ne']
      have h4 : Real.log (‖e w - e z‖ ^ 2) = 2 * Real.log ‖e w - e z‖ := by
        rw [Real.log_pow]; push_cast; ring
      rw [h1, h4]
      rw [h3] at h2
      nlinarith
    have hbw : b w ≤ B := (abs_le.mp hb1).2
    rw [hγr, hC]
    have hdiv : 1 / (d : ℝ) * Real.log (‖g w‖ ^ 2) ≤
        1 / (d : ℝ) * (2 * Real.log K + 2 * (a P : ℝ) * Real.log L +
          (a P : ℝ) * Real.log (‖e w - e z‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have heq : 1 / (d : ℝ) * (2 * Real.log K + 2 * (a P : ℝ) * Real.log L +
          (a P : ℝ) * Real.log (‖e w - e z‖ ^ 2)) =
        (a P : ℝ) / d * Real.log (‖e w - e z‖ ^ 2) +
          (2 * Real.log K + 2 * (a P : ℝ) * Real.log L) / d := by
      field_simp
      ring
    linarith
  rw [SquaredLogLelongSourceNormalization.squaredLogLelongNumber, if_neg (Nat.succ_ne_zero m)]
  exact le_iSup₂_of_le (f := fun (γ' : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] z,
      u y ≤ (((γ' : ℝ) * Real.log (‖(complexChartAt (n := m + 1) z).val y -
        (complexChartAt (n := m + 1) z).val z‖ ^ 2) + C : ℝ) : EReal)) => (γ' : ℝ≥0∞))
    γ ⟨C, hev⟩ le_rfl

/-! ### The lower bound of the weight in adapted coordinates -/

/-- The coefficient of `log |ζ_k|²` in the local model of `u` at `y`: the coefficient of the
component through `y` whose coordinate is `ζ_k` (`0` if there is none). -/
def coordinateCoefficient (j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} →
      Fin (m + 1)) (T : Finset {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P})
    (k : Fin (m + 1)) : ℝ :=
  ∑ P ∈ T, if j P = k then (D.coefficient P.val : ℝ) else 0

theorem coordinateCoefficient_nonneg
    (j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1))
    (T : Finset {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}) (k : Fin (m + 1)) :
    0 ≤ coordinateCoefficient j T k :=
  Finset.sum_nonneg fun P _ => by
    split_ifs
    · exact_mod_cast (D.coefficient_nonneg P.val)
    · exact le_rfl

/-- If `j` is injective on `T`, the coefficient of the coordinate of `P ∈ T` is `coeff_D(P)`. -/
theorem coordinateCoefficient_eq
    {j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1)}
    {T : Finset {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}}
    (hj : InjOn j T) {P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}}
    (hP : P ∈ T) : coordinateCoefficient j T (j P) = (D.coefficient P.val : ℝ) := by
  classical
  unfold coordinateCoefficient
  rw [Finset.sum_eq_single P]
  · simp
  · intro Q hQ hQP
    rw [if_neg]
    exact fun h => hQP (hj hQ hP h)
  · exact fun h => absurd hP h

/-- A coordinate which is not the coordinate of a component in `T` has coefficient `0`. -/
theorem coordinateCoefficient_eq_zero
    {j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1)}
    {T : Finset {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}} {k : Fin (m + 1)}
    (hk : ∀ P ∈ T, j P ≠ k) : coordinateCoefficient j T k = 0 :=
  Finset.sum_eq_zero fun P hP => if_neg (hk P hP)

/-- **Lower bound of the weight in simple normal crossing coordinates.**  If `u` has log
singularities along `D`, then in adapted coordinates `ζ` at `y`,
`u ≥ Σ_k c_k log |ζ_k|² - C` near `y`, where `c_k` is the coefficient of the component through `y`
with coordinate `ζ_k` (`T` = the components through `y`). -/
theorem exists_weight_lower_bound {u : Y → EReal} (hu : NativeHasLogSingularitiesAlong D u)
    (y : Y) (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0)
    (j : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Fin (m + 1))
    (hflat : ∀ P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P}, y ∈ P.val.val →
      ∀ {w : Y}, w ∈ (chartAt (ComplexModel (m + 1)) y).source →
        (chartAt (ComplexModel (m + 1)) y) w ∈ Φ.source →
          (w ∈ P.val.val ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) w) (j P) = 0))
    (T : Finset {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P})
    (hT : ∀ P, P ∈ T ↔ y ∈ P.val.val) :
    ∃ C : ℝ, ∀ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)),
      (∑ k, ((2 * coordinateCoefficient j T k : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal ‖ζ k‖)) + ((-C : ℝ) : EReal) ≤ u (adaptedInv y Φ ζ) := by
  classical
  obtain ⟨V, hyV, s, d, a, hs, hd, ha, g, hgen, b, hb, hueq⟩ :=
    hu.exists_original_integral_equation y
  have hTs : T ⊆ s := fun P hP => (hs P).mpr ⟨y, (hT P).mp hP, hyV⟩
  set q : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} → Y → ℂ :=
    componentGenerator y Φ j with hq
  obtain ⟨hgy, hgeny⟩ := hgen.self_of_nhds
  -- the product of the component generators is a multiple of `g`
  have hPihol := holomorphicAt_prod_componentGenerator y Φ j s a
  have hPimem : IsInSpanAt (n := m + 1) (· = g) y (fun w => ∏ P ∈ s, q P w ^ a P) := by
    apply (hgeny (fun w => ∏ P ∈ s, q P w ^ a P)).mp
    exact (sum_ideal_mem_iff_prod y Φ j hflat s a (fun w => ∏ P ∈ s, q P w ^ a P)).mpr
      (HolomorphicIdealSheaves.isInSpanAt_of_eq_mul rfl hPihol (holomorphicAt_const 1)
        (Eventually.of_forall fun w => (one_mul _).symm))
  obtain ⟨-, h, hh, hPieq⟩ := HolomorphicIdealSheaves.isInSpanAt_eq_iff.mp hPimem
  have hhcont : ∀ᶠ w in 𝓝 y, ‖h w‖ ≤ ‖h y‖ + 1 :=
    (hh.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖h y‖))).mono fun _ hw => hw.le
  obtain ⟨B, -, hB⟩ := hb
  set K : ℝ := ‖h y‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨2 / d * Real.log K + B, ?_⟩
  have hnear : ∀ᶠ w in 𝓝 y, (u w = (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (g w) +
      (b w : EReal)) ∧ (∏ P ∈ s, q P w ^ a P) = h w * g w ∧ ‖h w‖ ≤ K ∧ |b w| ≤ B := by
    filter_upwards [hueq, hPieq, hhcont, hB] with w h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  filter_upwards [(tendsto_adaptedInv y Φ h0).eventually hnear,
    eventually_flatCoord_adaptedInv y Φ hsrc h0] with ζ hw hflatζ
  obtain ⟨hu1, hPi1, hh1, hb1⟩ := hw
  set w := adaptedInv y Φ ζ
  -- the component generators at `w` are the coordinates of `ζ`
  have hqw : ∀ P, q P w = if y ∈ P.val.val then ζ (j P) else 1 := by
    intro P
    simp only [hq, componentGenerator]
    split_ifs
    · exact hflatζ (j P)
    · rfl
  have hPinorm : ‖∏ P ∈ s, q P w ^ a P‖ = ∏ P ∈ T, ‖ζ (j P)‖ ^ a P := by
    rw [norm_prod]
    simp only [norm_pow, hqw]
    rw [← Finset.prod_subset hTs]
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [if_pos ((hT P).mp hP)]
    · intro P _ hPT
      rw [if_neg (fun hyP => hPT ((hT P).mpr hyP)), norm_one, one_pow]
  by_cases hzero : ∃ P ∈ T, ζ (j P) = 0
  · -- some term is `-∞`
    obtain ⟨P, hPT, hζP⟩ := hzero
    have hcpos : 0 < coordinateCoefficient j T (j P) := by
      unfold coordinateCoefficient
      refine Finset.sum_pos' (fun Q _ => ?_) ⟨P, hPT, ?_⟩
      · split_ifs
        · exact_mod_cast (D.coefficient_nonneg _)
        · exact le_rfl
      · simp only [if_true]
        exact_mod_cast P.property
    have hbot : (∑ k, ((2 * coordinateCoefficient j T k : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖ζ k‖)) = ⊥ := by
      apply finset_sum_eq_bot (Finset.mem_univ (j P))
      rw [hζP, norm_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
      exact EReal.coe_mul_bot_of_pos (by positivity)
    rw [hbot, EReal.bot_add]
    exact bot_le
  push Not at hzero
  -- all terms are real
  have hterm : ∀ k, ((2 * coordinateCoefficient j T k : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖ζ k‖) =
        ((2 * coordinateCoefficient j T k * Real.log ‖ζ k‖ : ℝ) : EReal) := by
    intro k
    by_cases hk : ∃ P ∈ T, j P = k
    · obtain ⟨P, hPT, rfl⟩ := hk
      rw [ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr (hzero P hPT)), ← EReal.coe_mul]
    · push Not at hk
      rw [coordinateCoefficient_eq_zero hk]
      simp
  have hsum : (∑ k, ((2 * coordinateCoefficient j T k : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖ζ k‖)) =
        ((∑ k, 2 * coordinateCoefficient j T k * Real.log ‖ζ k‖ : ℝ) : EReal) := by
    rw [coe_finset_sum]
    exact Finset.sum_congr rfl fun k _ => hterm k
  -- reindex the real sum by the components
  have hreal : (∑ k, 2 * coordinateCoefficient j T k * Real.log ‖ζ k‖) =
      ∑ P ∈ T, 2 * (D.coefficient P.val : ℝ) * Real.log ‖ζ (j P)‖ := by
    unfold coordinateCoefficient
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finset.sum_eq_single (j P)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (fun h => hk h.symm)]
      ring
    · exact fun h => absurd (Finset.mem_univ _) h
  -- the norm bound `∏ |ζ_{j(P)}|^{a_P} ≤ K |g(w)|`
  have hPipos : 0 < ∏ P ∈ T, ‖ζ (j P)‖ ^ a P :=
    Finset.prod_pos fun P hP => pow_pos (norm_pos_iff.mpr (hzero P hP)) _
  have hPile : ∏ P ∈ T, ‖ζ (j P)‖ ^ a P ≤ K * ‖g w‖ := by
    rw [← hPinorm, hPi1, norm_mul]
    exact mul_le_mul_of_nonneg_right hh1 (norm_nonneg _)
  have hgpos : 0 < ‖g w‖ := by
    by_contra hng
    have : ‖g w‖ = 0 := le_antisymm (not_lt.mp hng) (norm_nonneg _)
    rw [this, mul_zero] at hPile
    exact absurd hPile (not_le.mpr hPipos)
  have hlogPi : Real.log (∏ P ∈ T, ‖ζ (j P)‖ ^ a P) =
      ∑ P ∈ T, (a P : ℝ) * Real.log ‖ζ (j P)‖ := by
    rw [Real.log_prod (fun P hP => (pow_pos (norm_pos_iff.mpr (hzero P hP)) _).ne')]
    exact Finset.sum_congr rfl fun P _ => Real.log_pow _ _
  have hlogle : ∑ P ∈ T, (a P : ℝ) * Real.log ‖ζ (j P)‖ ≤ Real.log K + Real.log ‖g w‖ := by
    rw [← hlogPi, ← Real.log_mul hKpos.ne' hgpos.ne']
    exact Real.log_le_log hPipos hPile
  have hcoef : ∀ P ∈ T, (D.coefficient P.val : ℝ) = (a P : ℝ) / d := by
    intro P hP
    rw [(ha P (hTs hP)).2]
    push_cast
    ring
  have hreal2 : ∑ P ∈ T, 2 * (D.coefficient P.val : ℝ) * Real.log ‖ζ (j P)‖ =
      2 / d * ∑ P ∈ T, (a P : ℝ) * Real.log ‖ζ (j P)‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hcoef P hP]
    ring
  rw [hsum, hreal, hreal2, hu1, logNormSq, ENNReal.log_ofReal_of_pos (pow_pos hgpos 2),
    ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, inv_cast_eq]
  have hbw : -B ≤ b w := (abs_le.mp hb1).1
  have hlog2 : Real.log (‖g w‖ ^ 2) = 2 * Real.log ‖g w‖ := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog2]
  have h2d : 0 ≤ 2 / (d : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hlogle h2d
  have heq : 1 / (d : ℝ) * (2 * Real.log ‖g w‖) = 2 / d * Real.log ‖g w‖ := by ring
  rw [heq]
  nlinarith

end Lelong

end SGPT.PSH.ValMultLocal
