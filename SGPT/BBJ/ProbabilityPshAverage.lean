import SGPT.Foundations.Analysis.PlurisubharmonicLimits
import Mathlib.MeasureTheory.Integral.Prod

/-! Probability averages of actual extended PSH kernels. The construction
retains infinite deficits. Nondegeneracy and any concrete current identity
are separate conclusions, not premises or claims of this module. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory SGPT.Foundations.Analysis
open scoped Topology ENNReal

variable {A X : Type*} [MeasurableSpace A]

/-- Fatou for the actual within-neighborhood filter proves parameter-integral
lower semicontinuity, without assuming the integral finite. -/
lemma lowerSemicontinuousOn_lintegral [TopologicalSpace X] [FirstCountableTopology X]
    (μ : Measure A) (g : A → X → ℝ≥0∞) (U : Set X)
    (hm : ∀ x, Measurable (fun a => g a x))
    (hl : ∀ a, LowerSemicontinuousOn (g a) U) :
    LowerSemicontinuousOn (fun x => ∫⁻ a, g a x ∂μ) U := by
  intro x hx
  apply lowerSemicontinuousWithinAt_iff_le_liminf.mpr
  exact (lintegral_mono (fun a =>
    lowerSemicontinuousWithinAt_iff_le_liminf.mp (hl a x hx))).trans
    (lintegral_liminf_le (μ := μ) (f := fun y a => g a y) (u := 𝓝[U] x) hm)

/-- The literal probability-average candidate defined through nonnegative
deficits, including bottom when the deficit integral is infinite. -/
def probabilityPshAverage (μ : Measure A) (C : ℝ) (u : A → X → EReal) (x : X) : EReal :=
  (C : EReal) - ((∫⁻ a, ((C : EReal) - u a x).toENNReal ∂μ) : EReal)

lemma probabilityPshAverage_le (μ : Measure A) (C : ℝ) (u : A → X → EReal) (x : X) :
    probabilityPshAverage μ C u x ≤ (C : EReal) := by
  have h := EReal.sub_le_sub (le_refl (C : EReal))
    (EReal.coe_ennreal_nonneg (∫⁻ a, ((C : EReal) - u a x).toENNReal ∂μ))
  simpa only [probabilityPshAverage, sub_zero] using h


private lemma finite_double_deficit (C : ℝ) (G : ℝ≥0∞) :
    ((C : EReal) - ((C : EReal) - (G : EReal))).toENNReal = G := by
  rw [sub_eq_add_neg (C : EReal) (G : EReal), EReal.sub_add_cancel_left,
    neg_neg, EReal.toENNReal_coe]

lemma probabilityPshAverage_deficit_self (μ : Measure A) (C : ℝ)
    (u : A → X → EReal) (x : X) :
    ((C : EReal) - probabilityPshAverage μ C u x).toENNReal =
      ∫⁻ a, ((C : EReal) - u a x).toENNReal ∂μ := by
  exact finite_double_deficit C _

/-- Every larger finite deficit is the actual probability integral of the
corresponding kernel deficits, including infinite deficit integrals. -/
lemma probabilityPshAverage_deficit (μ : Measure A) [IsProbabilityMeasure μ]
    (C B : ℝ) (hCB : C ≤ B) (u : A → X → EReal) (x : X)
    (hu : ∀ a, u a x ≤ (C : EReal)) :
    ((B : EReal) - probabilityPshAverage μ C u x).toENNReal =
      ∫⁻ a, ((B : EReal) - u a x).toENNReal ∂μ := by
  have hBC : C + (B-C) = B := by ring
  have hpos : 0 ≤ B-C := sub_nonneg.mpr hCB
  have hleft := finiteDeficit_add_bound C (B-C) hpos
    (probabilityPshAverage μ C u x) (probabilityPshAverage_le μ C u x)
  rw [hBC, probabilityPshAverage_deficit_self] at hleft
  have hshift (a : A) : ((B : EReal) - u a x).toENNReal =
      ENNReal.ofReal (B-C) + ((C : EReal) - u a x).toENNReal := by
    simpa only [hBC] using finiteDeficit_add_bound C (B-C) hpos (u a x) (hu a)
  rw [hleft]
  simp_rw [hshift]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]


private lemma continuous_finite_sub_ennreal (C : ℝ) :
    Continuous (fun G : ℝ≥0∞ => (C : EReal) - (G : EReal)) := by
  have hp : Continuous (fun G : ℝ≥0∞ => ((C : EReal), -(G : EReal))) :=
    continuous_const.prodMk continuous_coe_ennreal_ereal.neg
  apply continuous_iff_continuousAt.mpr
  intro G
  simpa only [sub_eq_add_neg, Function.comp_def] using!
    (EReal.continuousAt_add (p := ((C : EReal), -(G : EReal)))
      (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).comp
        (f := fun G : ℝ≥0∞ => ((C : EReal), -(G : EReal))) (x := G) hp.continuousAt

lemma upperSemicontinuousOn_probabilityPshAverage [TopologicalSpace X]
    [FirstCountableTopology X] (μ : Measure A) (C : ℝ) (u : A → X → EReal) (U : Set X)
    (hm : ∀ x, Measurable (fun a => ((C : EReal) - u a x).toENNReal))
    (hu : ∀ a, UpperSemicontinuousOn (u a) U) :
    UpperSemicontinuousOn (probabilityPshAverage μ C u) U := by
  have hg : ∀ a, LowerSemicontinuousOn
      (fun x => ((C : EReal) - u a x).toENNReal) U := by
    intro a
    exact (continuous_finiteDeficit C).comp_upperSemicontinuousOn_antitone (hu a)
      (fun x y hxy => EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hxy))
  have hG := lowerSemicontinuousOn_lintegral μ _ U hm hg
  exact (continuous_finite_sub_ennreal C).comp_lowerSemicontinuousOn_antitone hG
    (fun x y hxy => EReal.sub_le_sub le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxy))


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Actual nonnegative Tonelli exchanges the full angular deficit with the
parameter average. No finite-integral premise is introduced. -/
lemma circleDeficit_probabilityPshAverage (μ : Measure A) [IsProbabilityMeasure μ]
    (C B : ℝ) (hCB : C ≤ B) (u : A → E → EReal)
    (hm : Measurable (fun p : A × E => ((C : EReal) - u p.1 p.2).toENNReal))
    (x v : E) (r : ℝ) (hr : 0 ≤ r)
    (hC : ∀ a, ∀ y ∈ affineClosedDisc x v r, u a y ≤ (C : EReal)) :
    circleDeficit (probabilityPshAverage μ C u) x v r B =
      ∫⁻ a, circleDeficit (u a) x v r B ∂μ := by
  let k : A → ℝ → ℝ≥0∞ := fun a t =>
    ((B : EReal) - u a (x + circleMap 0 r t • v)).toENNReal
  have hBC : C + (B-C) = B := by ring
  have hkc : Measurable (Function.uncurry k) := by
    have hc : Continuous (fun t : ℝ => x + circleMap 0 r t • v) := by fun_prop
    have hcm : Measurable (fun p : A × ℝ =>
        ((C : EReal) - u p.1 (x + circleMap 0 r p.2 • v)).toENNReal) :=
      hm.comp (measurable_fst.prodMk (hc.measurable.comp measurable_snd))
    have heq : Function.uncurry k = fun p : A × ℝ => ENNReal.ofReal (B-C) +
        ((C : EReal) - u p.1 (x + circleMap 0 r p.2 • v)).toENNReal := by
      funext p
      have h := finiteDeficit_add_bound C (B-C) (sub_nonneg.mpr hCB)
        (u p.1 (x + circleMap 0 r p.2 • v))
        (hC p.1 _ (circle_mem_affineClosedDisc x v hr p.2))
      simpa only [hBC, k, Function.uncurry] using h
    rw [heq]
    exact measurable_const.add hcm
  unfold circleDeficit
  calc
    _ = ∫⁻ t in Ioc 0 (2*Real.pi), ∫⁻ a, k a t ∂μ := by
      apply lintegral_congr
      intro t
      exact probabilityPshAverage_deficit μ C B hCB u _
        (fun a => hC a _ (circle_mem_affineClosedDisc x v hr t))
    _ = _ := (lintegral_lintegral_swap
      (μ := μ) (ν := volume.restrict (Ioc 0 (2*Real.pi))) hkc.aemeasurable).symm


/-- The genuine full disc criterion for the literal probability average.
Every real upper bound is tested, not only the common kernel bound. -/
lemma discPshOn_probabilityPshAverage (μ : Measure A) [IsProbabilityMeasure μ]
    (C : ℝ) (u : A → E → EReal) (U : Set E)
    (hm : Measurable (fun p : A × E => ((C : EReal) - u p.1 p.2).toENNReal))
    (hC : ∀ a, ∀ y ∈ U, u a y ≤ (C : EReal))
    (hu : ∀ a, DiscPshOn (u a) U) :
    DiscPshOn (probabilityPshAverage μ C u) U := by
  refine ⟨fun x _ => ne_of_lt ((probabilityPshAverage_le μ C u x).trans_lt
    (EReal.coe_lt_top C)), ?_, ?_⟩
  · exact upperSemicontinuousOn_probabilityPshAverage μ C u U
      (fun x => hm.comp (measurable_id.prodMk measurable_const))
      (fun a => (hu a).upperSemicontinuousOn)
  intro x v r hr hD D₀ hD₀
  let shift : ℝ := max 0 (C-D₀)
  have hs : 0 ≤ shift := le_max_left _ _
  have hBC : C ≤ D₀+shift := by
    have h : C-D₀ ≤ shift := le_max_right _ _
    linarith
  have hxU : x ∈ U := hD (center_mem_affineClosedDisc x v hr.le)
  have hCm : Measurable (fun a : A => ((C : EReal) - u a x).toENNReal) :=
    hm.comp (measurable_id.prodMk measurable_const)
  have hcenter : Measurable (fun a : A => ((D₀+shift : ℝ) - u a x).toENNReal) := by
    have heq : (fun a : A => ((D₀+shift : ℝ) - u a x).toENNReal) =
        fun a => ENNReal.ofReal (D₀+shift-C) + ((C : EReal) - u a x).toENNReal := by
      funext a
      have h := finiteDeficit_add_bound C (D₀+shift-C) (sub_nonneg.mpr hBC)
        (u a x) (hC a x hxU)
      simpa only [show C+(D₀+shift-C) = D₀+shift by ring] using h
    rw [heq]
    exact measurable_const.add hCm
  apply (discSubmean_add_bound_iff x v hr.le D₀ shift hs hD₀).mp
  rw [circleDeficit_probabilityPshAverage μ C (D₀+shift) hBC u hm x v r hr.le
    (fun a y hy => hC a y (hD hy))]
  calc
    _ ≤ ∫⁻ a, ENNReal.ofReal (2*Real.pi) *
        (((D₀+shift : ℝ) : EReal) - u a x).toENNReal ∂μ := by
      apply lintegral_mono
      intro a
      exact (hu a).submean x v r hr hD (D₀+shift)
        (fun y hy => (hC a y (hD hy)).trans (EReal.coe_le_coe_iff.mpr hBC))
    _ = ENNReal.ofReal (2*Real.pi) *
        ∫⁻ a, (((D₀+shift : ℝ) : EReal) - u a x).toENNReal ∂μ :=
      lintegral_const_mul _ hcenter
    _ = _ := by rw [probabilityPshAverage_deficit μ C (D₀+shift) hBC u x
      (fun a => hC a x hxU)]

/-- On an open domain the actual average is locally PSH; its possible
identically-bottom branch is retained for later nondegeneracy proofs. -/
lemma plurisubharmonicOn_probabilityPshAverage (μ : Measure A) [IsProbabilityMeasure μ]
    (C : ℝ) (u : A → E → EReal) (U : Set E) (hU : IsOpen U)
    (hm : Measurable (fun p : A × E => ((C : EReal) - u p.1 p.2).toENNReal))
    (hC : ∀ a, ∀ y ∈ U, u a y ≤ (C : EReal))
    (hu : ∀ a, DiscPshOn (u a) U) :
    PlurisubharmonicOn (probabilityPshAverage μ C u) U :=
  (discPshOn_probabilityPshAverage μ C u U hm hC hu).plurisubharmonicOn hU

end SGPT.BBJ
