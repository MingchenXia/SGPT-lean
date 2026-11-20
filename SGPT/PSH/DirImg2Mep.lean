import SGPT.PSH.DirImg2Det
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.Pending.BergmanSupWeight
import SGPT.Foundations.Analysis.PlurisubharmonicPullback

/-!
# The minimal extension property and the plurisubharmonicity of `log det h*`

Blueprint `claude-dirimg2.tex`, nodes `claude-dirimg2:mep`, `claude-dirimg2:core`,
`claude-dirimg2:psh-det`, `claude-dirimg2:pluripolar`.
Source: Step 1.3--1.4 of the proof of `thm:Bert` (`chapter_trace.tex` 828--935) and
`rmk:generalABT`: "Since the Hodge metric `h_𝓗` is positive ([PT18, Thm 3.3.5], [HPS18,
Thm 21.1]), its determinant `det h_𝓗` is also positive ([Rau15, Prop 1.3], [HPS18, Prop 25.1]);
it follows that `Σ₄` is pluripolar."

The positivity of the Hodge metric is obtained in [HPS18, §§20--21] from the **minimal extension
property** given by the optimal Ohsawa--Takegoshi theorem (Błocki, Guan--Zhou). We prove directly,
in a holomorphic frame and without curvature, approximation or determinant theory of singular
metrics, that the minimal extension property makes `log det h*` plurisubharmonic, and hence
that the set of parameters where some fibre vector has infinite norm is pluripolar:

* `HasCircleMEP`: the minimal extension property, in the circle-averaged form produced by the
  Guan--Zhou estimate with the gain `c(s) = e^s 1_{[0,ε]}(s)` (annuli of radii `(ρ', ρ]`, any
  slack `1 + η`): every frame `e` of finite norm at `x` extends holomorphically over discs
  `x + τ w`, `|τ| ≤ s`, for some radius `s ∈ (ρ', ρ]`, with
  `∑ⱼ ∫_θ q(x + s e^{iθ} w, Fⱼ(s e^{iθ})) ≤ (1 + η) 2π ∑ⱼ q(x, eⱼ)`;
* `circleDeficit_add_le` (the core): at one radius, Hadamard-free comparison of `log det h*` with
  `log |det F(τ)|² - ∑ log q(Fⱼ(τ))`, the subharmonicity of `log |det F|²` and `log y ≤ y - 1`;
* `discPshOn_logDetDual`: `log det h*` (`logDetDual`) is plurisubharmonic on `U`
  (radii `s → ρ` by Fatou's lemma and upper semicontinuity);
* `locallyPluripolarOn_infiniteNormSet`: the set of `t ∈ U` such that some vector of `ℂʳ` has
  infinite norm `q t v = ∞` is locally pluripolar in `U` (`U` connected, one finite point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Real

namespace SGPT.PSH.DirImg2

open SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}
  {q : E → (Fin r → ℂ) → ℝ≥0∞} {U : Set E}

/-! ### The minimal extension property -/

/-- **Minimal extension property** of a family of norms `q` in a frame over `U`, in the
circle-averaged form: for every affine disc `x + τ w`, `|τ| ≤ ρ`, in `U`, every frame `e` of
finite norm at `x`, every `ρ' ∈ (0, ρ)` and every slack `η > 0`, there are a radius
`s ∈ (ρ', ρ]` and holomorphic extensions `Fⱼ` of the `eⱼ` over a neighbourhood of `|τ| ≤ s`
whose norms satisfy `∑ⱼ ∫₀^{2π} q(x + s e^{iθ} w, Fⱼ(s e^{iθ})) dθ ≤ (1 + η) 2π ∑ⱼ q(x, eⱼ)`. -/
def HasCircleMEP (q : E → (Fin r → ℂ) → ℝ≥0∞) (U : Set E) : Prop :=
  ∀ (x w : E) (ρ : ℝ), 0 < ρ → affineClosedDisc x w ρ ⊆ U →
    ∀ e : Fin r → Fin r → ℂ, (∀ j, q x (e j) ≠ ⊤) →
      ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ → ∀ η : ℝ, 0 < η →
        ∃ s ∈ Ioc ρ' ρ, ∃ (O : Set ℂ) (F : Fin r → ℂ → Fin r → ℂ),
          IsOpen O ∧ closedBall (0 : ℂ) s ⊆ O ∧ (∀ j, DifferentiableOn ℂ (F j) O) ∧
          (∀ j, F j 0 = e j) ∧
          ∑ j, ∫⁻ θ in Ioc 0 (2 * π), q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ))
            ≤ ENNReal.ofReal ((1 + η) * (2 * π)) * ∑ j, q x (e j)

/-! ### Auxiliary facts -/

/-- `log |g|²` is plurisubharmonic (disc criterion) for `g` holomorphic on an open `O ⊆ ℂ`. -/
theorem discPshOn_logNormSq_comp {g : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O)
    (hg : DifferentiableOn ℂ g O) : DiscPshOn (fun z => logNormSq (g z)) O := by
  let P : FirstPass.ComplexModel 1 →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 1) 0
  let L : ℂ →L[ℂ] FirstPass.ComplexModel 1 :=
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))
  have hPL : ∀ z, P (L z) = z := fun z => by simp [P, L]
  have hD : IsOpen (P ⁻¹' O) := hO.preimage P.continuous
  have hf : DifferentiableOn ℂ (fun p => g (P p)) (P ⁻¹' O) :=
    hg.comp P.differentiableOn fun _ hp => hp
  have h1 := (Pending.BergmanSupWeight.plurisubharmonicOn_logNormSq_comp hD hf).discPshOn
  have h2 := h1.comp_continuousLinearMap L
  have hpre : L ⁻¹' (P ⁻¹' O) = O := by ext z; simp [hPL]
  simpa [hpre, hPL] using h2

/-- The determinant of a holomorphic family of frames is holomorphic. -/
theorem differentiableOn_colDet {F : Fin r → ℂ → Fin r → ℂ} {O : Set ℂ}
    (hF : ∀ j, DifferentiableOn ℂ (F j) O) :
    DifferentiableOn ℂ (fun z => colDet fun j => F j z) O := by
  have heq : (fun z => colDet fun j => F j z) = fun z =>
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, F i z (σ i) := by
    funext z
    simp [colDet, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [heq]
  exact DifferentiableOn.fun_sum fun σ _ => (DifferentiableOn.fun_finsetProd fun i _ =>
    differentiableOn_pi.mp (hF i) (σ i)).const_mul _

/-- The elementary inequality behind the sub-mean value property (`log y ≤ y - 1`), in extended
form: for `d < ∞` and norms `Qⱼ` (with `Qⱼ = 0 ⇒ d = 0`), if `log (d / ∏ Qⱼ) ≤ C`, `log d ≤ C'`
and `C ≤ C'`, then `(C - log (d / ∏ Qⱼ))⁺ + (r + C' - C) ≤ (C' - log d)⁺ + ∑ Qⱼ`. -/
theorem deficit_add_le {d : ℝ≥0∞} (hd : d ≠ ⊤) {Q : Fin r → ℝ≥0∞} (hQ : ∀ j, Q j = 0 → d = 0)
    {C C' : ℝ} (hCC : C ≤ C') (hL : ENNReal.log (d / ∏ j, Q j) ≤ C)
    (ha : ENNReal.log d ≤ C') :
    ((C : EReal) - ENNReal.log (d / ∏ j, Q j)).toENNReal + ENNReal.ofReal (r + (C' - C)) ≤
      ((C' : EReal) - ENNReal.log d).toENNReal + ∑ j, Q j := by
  by_cases htop : ∃ j, Q j = ⊤
  · obtain ⟨j, hj⟩ := htop
    rw [ENNReal.sum_eq_top.mpr ⟨j, Finset.mem_univ j, hj⟩, add_top]
    exact le_top
  push Not at htop
  by_cases hd0 : d = 0
  · rw [hd0, ENNReal.log_zero, EReal.sub_bot (EReal.coe_ne_bot C'), EReal.toENNReal_top, top_add]
    exact le_top
  have hQ0 : ∀ j, Q j ≠ 0 := fun j h => hd0 (hQ j h)
  set d' := d.toReal
  set q' : Fin r → ℝ := fun j => (Q j).toReal
  have hd' : 0 < d' := ENNReal.toReal_pos hd0 hd
  have hq' : ∀ j, 0 < q' j := fun j => ENNReal.toReal_pos (hQ0 j) (htop j)
  have hQe : ∀ j, Q j = ENNReal.ofReal (q' j) := fun j => (ENNReal.ofReal_toReal (htop j)).symm
  have hde : d = ENNReal.ofReal d' := (ENNReal.ofReal_toReal hd).symm
  have hprod : ∏ j, Q j = ENNReal.ofReal (∏ j, q' j) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun j _ => (hq' j).le]
    exact Finset.prod_congr rfl fun j _ => hQe j
  have hPpos : 0 < ∏ j, q' j := Finset.prod_pos fun j _ => hq' j
  have hdiv : d / ∏ j, Q j = ENNReal.ofReal (d' / ∏ j, q' j) := by
    rw [hprod, hde, ENNReal.ofReal_div_of_pos hPpos]
  have hlogL : ENNReal.log (d / ∏ j, Q j) = ((Real.log d' - ∑ j, Real.log (q' j) : ℝ) : EReal) := by
    rw [hdiv, ENNReal.log_ofReal_of_pos (div_pos hd' hPpos), Real.log_div hd'.ne' hPpos.ne',
      Real.log_prod fun j _ => (hq' j).ne']
  have hloga : ENNReal.log d = (Real.log d' : EReal) := by
    rw [hde, ENNReal.log_ofReal_of_pos hd']
  rw [hlogL] at hL ⊢
  rw [hloga] at ha ⊢
  have hL' : Real.log d' - ∑ j, Real.log (q' j) ≤ C := by exact_mod_cast hL
  have ha' : Real.log d' ≤ C' := by exact_mod_cast ha
  have hsum : ∑ j, Q j = ENNReal.ofReal (∑ j, q' j) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => (hq' j).le]
    exact Finset.sum_congr rfl fun j _ => hQe j
  rw [hsum, ← EReal.coe_sub, ← EReal.coe_sub, EReal.real_coe_toENNReal,
    EReal.real_coe_toENNReal, ← ENNReal.ofReal_add (by linarith) (by positivity),
    ← ENNReal.ofReal_add (by linarith) (Finset.sum_nonneg fun j _ => (hq' j).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hlog : ∑ j, Real.log (q' j) ≤ ∑ j, (q' j - 1) :=
    Finset.sum_le_sum fun j _ => Real.log_le_sub_one_of_pos (hq' j)
  rw [Finset.sum_sub_distrib] at hlog
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlog
  linarith

/-- `v ↦ (C - v)⁺` is continuous on `EReal` (for real `C`). -/
theorem continuous_deficit (C : ℝ) : Continuous fun v : EReal => ((C : EReal) - v).toENNReal := by
  refine EReal.continuous_toENNReal.comp (continuous_iff_continuousAt.2 fun v => ?_)
  have h := ContinuousAt.comp (f := fun v : EReal => ((C : EReal), -v)) (x := v)
    (g := fun p : EReal × EReal => p.1 + p.2)
    (EReal.continuousAt_add (p := ((C : EReal), -v)) (Or.inl (EReal.coe_ne_top C))
      (Or.inl (EReal.coe_ne_bot C)))
    ((continuous_const.prodMk (continuous_neg : Continuous fun v : EReal => -v)).continuousAt)
  have heq : (fun p : EReal × EReal => p.1 + p.2) ∘ (fun v : EReal => ((C : EReal), -v)) =
      fun v => (C : EReal) - v := by
    funext v
    simp [sub_eq_add_neg]
  rw [heq] at h
  exact h

/-! ### The core estimate at one radius -/

/-- **The core estimate at one radius.** Let `x + τ w`, `|τ| ≤ s`, be a disc in `U` on which
`log det h* ≤ C`, and let `F` be a holomorphic family of frames over a neighbourhood of `|τ| ≤ s`
with `log |det F| ² ≤ C' (C ≤ C')`. Then
`∫_θ (C - log det h*(x + s e^{iθ} w))⁺ + 2π (r + C' - C)`
`  ≤ 2π (C' - log |det F(0)|²)⁺ + ∑ⱼ ∫_θ q(x + s e^{iθ} w, Fⱼ(s e^{iθ}))`.
Proof: `log det h* ≥ log |det F|² - ∑ log q(Fⱼ)` pointwise (every frame is a competitor),
`log y ≤ y - 1`, and the sub-mean value property of `log |det F|²`. -/
theorem IsSingularNormFamily.circleDeficit_add_le (hq : IsSingularNormFamily q U) {x w : E}
    {s : ℝ} (hs : 0 < s) (hD : affineClosedDisc x w s ⊆ U) {C C' : ℝ} (hCC : C ≤ C')
    (hC : ∀ y ∈ affineClosedDisc x w s, logDetDual q y ≤ C)
    {O : Set ℂ} {F : Fin r → ℂ → Fin r → ℂ} (hO : IsOpen O) (hsO : closedBall (0 : ℂ) s ⊆ O)
    (hF : ∀ j, DifferentiableOn ℂ (F j) O)
    (ha : ∀ z ∈ closedBall (0 : ℂ) s, logNormSq (colDet fun j => F j z) ≤ C') :
    circleDeficit (logDetDual q) x w s C +
        ENNReal.ofReal (2 * π) * ENNReal.ofReal (r + (C' - C)) ≤
      ENNReal.ofReal (2 * π) * ((C' : EReal) - logNormSq (colDet fun j => F j 0)).toENNReal +
        ∑ j, ∫⁻ θ in Ioc 0 (2 * π), q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ)) := by
  set g : ℂ → ℂ := fun z => colDet fun j => F j z with hg
  have hyD : ∀ θ, x + circleMap 0 s θ • w ∈ affineClosedDisc x w s :=
    fun θ => circle_mem_affineClosedDisc x w hs.le θ
  have hτ : ∀ θ, circleMap 0 s θ ∈ closedBall (0 : ℂ) s :=
    fun θ => sphere_subset_closedBall (circleMap_mem_sphere 0 hs.le θ)
  -- pointwise inequality
  have hpt : ∀ θ, ((C : EReal) - logDetDual q (x + circleMap 0 s θ • w)).toENNReal +
      ENNReal.ofReal (r + (C' - C)) ≤
      ((C' : EReal) - logNormSq (g (circleMap 0 s θ))).toENNReal +
        ∑ j, q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ)) := by
    intro θ
    have hratio := hq.detRatio_le_detDual (x + circleMap 0 s θ • w)
      (fun j => F j (circleMap 0 s θ))
    have hL : ENNReal.log (detRatio (q (x + circleMap 0 s θ • w))
        (fun j => F j (circleMap 0 s θ))) ≤ C :=
      (ENNReal.log_le_log hratio).trans (hC _ (hyD θ))
    have hmono : ((C : EReal) - logDetDual q (x + circleMap 0 s θ • w)).toENNReal ≤
        ((C : EReal) - ENNReal.log (detRatio (q (x + circleMap 0 s θ • w))
          (fun j => F j (circleMap 0 s θ)))).toENNReal :=
      EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (ENNReal.log_le_log hratio))
    refine (add_le_add_left hmono _).trans ?_
    refine deficit_add_le ENNReal.ofReal_ne_top (fun j hj => ?_) hCC hL (ha _ (hτ θ))
    by_contra hne
    refine hq.pos _ (hD (hyD θ)) _ (fun h0 => hne ?_) hj
    rw [colDet_eq_zero_of_eq_zero (j := j) h0]
    simp
  -- measurability
  have hgc : ContinuousOn g O := (differentiableOn_colDet hF).continuousOn
  have hma : Measurable fun θ =>
      ((C' : EReal) - logNormSq (g (circleMap 0 s θ))).toENNReal := by
    refine ((continuous_deficit C').comp (continuous_logNormSq.comp ?_)).measurable
    exact hgc.comp_continuous (continuous_circleMap 0 s) fun θ => hsO (hτ θ)
  have hmQ : ∀ j, Measurable fun θ => q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ)) := by
    intro j
    refine LowerSemicontinuous.measurable fun θ => ?_
    have hc : ContinuousAt (fun θ : ℝ => (x + circleMap 0 s θ • w, F j (circleMap 0 s θ))) θ := by
      refine ContinuousAt.prodMk (by fun_prop) ?_
      exact ((hF j).continuousOn.continuousAt (hO.mem_nhds (hsO (hτ θ)))).comp
        (continuous_circleMap 0 s).continuousAt
    exact LowerSemicontinuousAt.comp (f := fun p : E × (Fin r → ℂ) => q p.1 p.2)
      (g := fun θ : ℝ => (x + circleMap 0 s θ • w, F j (circleMap 0 s θ))) (hq.lsc _ (hD (hyD θ)) _) hc
  -- the sub-mean value property of `log |det F|²`
  have hpsh := (discPshOn_logNormSq_comp hO (differentiableOn_colDet hF)).submean
  have hdisc : affineClosedDisc (0 : ℂ) 1 s ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    simpa using hsO hz
  have hsub := hpsh 0 1 s hs hdisc C' (by
    rintro _ ⟨z, hz, rfl⟩
    simpa using ha z hz)
  simp only [circleDeficit, zero_add, smul_eq_mul, mul_one] at hsub
  -- integrate
  calc circleDeficit (logDetDual q) x w s C +
        ENNReal.ofReal (2 * π) * ENNReal.ofReal (r + (C' - C))
      = (∫⁻ θ in Ioc 0 (2 * π),
          ((C : EReal) - logDetDual q (x + circleMap 0 s θ • w)).toENNReal) +
        ∫⁻ _θ in Ioc 0 (2 * π), ENNReal.ofReal (r + (C' - C)) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
        rfl
    _ ≤ ∫⁻ θ in Ioc 0 (2 * π),
          (((C : EReal) - logDetDual q (x + circleMap 0 s θ • w)).toENNReal +
            ENNReal.ofReal (r + (C' - C))) := le_lintegral_add _ _
    _ ≤ ∫⁻ θ in Ioc 0 (2 * π), (((C' : EReal) - logNormSq (g (circleMap 0 s θ))).toENNReal +
          ∑ j, q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ))) := lintegral_mono hpt
    _ = (∫⁻ θ in Ioc 0 (2 * π), ((C' : EReal) - logNormSq (g (circleMap 0 s θ))).toENNReal) +
          ∑ j, ∫⁻ θ in Ioc 0 (2 * π), q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ)) := by
        rw [lintegral_add_left hma, lintegral_finsetSum _ fun j _ => hmQ j]
    _ ≤ _ := add_le_add_left hsub _

/-- The core estimate with the auxiliary constant removed: for a frame `e` normalized at `x`
(`q x (e j) = 1`) and holomorphic extensions with `∑ⱼ ∫ q(Fⱼ) ≤ (1 + η) 2π r` over the circle of
radius `s`, `∫_θ (C - log det h*)⁺ ≤ 2π (C - log |det e|²)⁺ + 2π η r`. -/
theorem IsSingularNormFamily.circleDeficit_le_of_extension (hq : IsSingularNormFamily q U)
    {x w : E} {s : ℝ} (hs : 0 < s) (hD : affineClosedDisc x w s ⊆ U) {C : ℝ}
    (hC : ∀ y ∈ affineClosedDisc x w s, logDetDual q y ≤ C)
    {e : Fin r → Fin r → ℂ} {O : Set ℂ} {F : Fin r → ℂ → Fin r → ℂ} (hO : IsOpen O)
    (hsO : closedBall (0 : ℂ) s ⊆ O) (hF : ∀ j, DifferentiableOn ℂ (F j) O)
    (hF0 : ∀ j, F j 0 = e j) {η : ℝ} (hη : 0 ≤ η)
    (hB : ∑ j, ∫⁻ θ in Ioc 0 (2 * π), q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ)) ≤
      ENNReal.ofReal ((1 + η) * (2 * π)) * r) :
    circleDeficit (logDetDual q) x w s C ≤
      ENNReal.ofReal (2 * π) * ((C : EReal) - logNormSq (colDet e)).toENNReal +
        ENNReal.ofReal (2 * π * η * r) := by
  have hg0 : (colDet fun j => F j 0) = colDet e := by simp only [hF0]
  -- an upper bound for `log |det F|²` on the closed disc
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
    ((differentiableOn_colDet hF).continuousOn.mono hsO)
  set C' : ℝ := max C (Real.log (M ^ 2 + 1))
  have hCC : C ≤ C' := le_max_left _ _
  have ha : ∀ z ∈ closedBall (0 : ℂ) s, logNormSq (colDet fun j => F j z) ≤ C' := by
    intro z hz
    have h1 : ENNReal.ofReal (‖colDet fun j => F j z‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2 + 1) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [hM z hz, norm_nonneg (colDet fun j => F j z)])
    calc logNormSq (colDet fun j => F j z) ≤ ENNReal.log (ENNReal.ofReal (M ^ 2 + 1)) :=
          ENNReal.log_le_log h1
      _ = (Real.log (M ^ 2 + 1) : EReal) := ENNReal.log_ofReal_of_pos (by positivity)
      _ ≤ C' := by exact_mod_cast le_max_right _ _
  have hcore := hq.circleDeficit_add_le hs hD hCC hC hO hsO hF ha
  rw [hg0] at hcore
  -- the case `det e = 0`
  by_cases hbot : logNormSq (colDet e) = ⊥
  · rw [hbot, EReal.sub_bot (EReal.coe_ne_bot C), EReal.toENNReal_top,
      ENNReal.mul_top (by positivity), top_add]
    exact le_top
  set a₀ : ℝ := (logNormSq (colDet e)).toReal
  have ha₀ : logNormSq (colDet e) = (a₀ : EReal) := (EReal.coe_toReal (logNormSq_ne_top _) hbot).symm
  have ha₀C' : a₀ ≤ C' := by
    have := ha 0 (mem_closedBall_self hs.le)
    rw [hg0, ha₀] at this
    exact_mod_cast this
  rw [ha₀] at hcore ⊢
  rw [← EReal.coe_sub, EReal.real_coe_toENNReal] at hcore ⊢
  set c : ℝ := 2 * π * (r + (C' - C))
  have hc : 0 ≤ c := by positivity
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hcore' : circleDeficit (logDetDual q) x w s C + ENNReal.ofReal c ≤
      ENNReal.ofReal (2 * π * (C - a₀) + 2 * π * η * r) + ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_mul h2π] at hcore
    refine hcore.trans ?_
    have hB' : ∑ j, ∫⁻ θ in Ioc 0 (2 * π),
        q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ)) ≤
          ENNReal.ofReal ((1 + η) * (2 * π) * r) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      exact hB
    calc ENNReal.ofReal (2 * π) * ENNReal.ofReal (C' - a₀) + ∑ j, ∫⁻ θ in Ioc 0 (2 * π),
          q (x + circleMap 0 s θ • w) (F j (circleMap 0 s θ))
        ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (C' - a₀) +
            ENNReal.ofReal ((1 + η) * (2 * π) * r) := add_le_add_right hB' _
      _ = ENNReal.ofReal (2 * π * (C' - a₀) + (1 + η) * (2 * π) * r) := by
          rw [← ENNReal.ofReal_mul h2π, ← ENNReal.ofReal_add (by nlinarith) (by positivity)]
      _ ≤ ENNReal.ofReal (2 * π * (C - a₀) + 2 * π * η * r + c) :=
          ENNReal.ofReal_le_ofReal (le_of_eq (by simp only [c]; ring))
      _ ≤ _ := ENNReal.ofReal_add_le
  have := ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hcore'
  refine this.trans ((ENNReal.ofReal_add_le).trans ?_)
  rw [ENNReal.ofReal_mul h2π]

/-- **Fatou's lemma along the circles.** Under the minimal extension property, for a frame `e`
normalized at `x` (`q x (e j) = 1`) and every disc in `U` on which `log det h* ≤ C`,
`∫_θ (C - log det h*(x + ρ e^{iθ} w))⁺ ≤ 2π (C - log |det e|²)⁺`. -/
theorem IsSingularNormFamily.circleDeficit_le_of_mep (hq : IsSingularNormFamily q U)
    (hU : IsOpen U) (hmep : HasCircleMEP q U) {x w : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hD : affineClosedDisc x w ρ ⊆ U) {C : ℝ}
    (hC : ∀ y ∈ affineClosedDisc x w ρ, logDetDual q y ≤ C) {e : Fin r → Fin r → ℂ}
    (he : ∀ j, q x (e j) = 1) :
    circleDeficit (logDetDual q) x w ρ C ≤
      ENNReal.ofReal (2 * π) * ((C : EReal) - logNormSq (colDet e)).toENNReal := by
  set u := logDetDual q
  set K := ENNReal.ofReal (2 * π) * ((C : EReal) - logNormSq (colDet e)).toENNReal
  have hsum : ∑ j, q x (e j) = r := by simp [he]
  have hfin : ∀ j, q x (e j) ≠ ⊤ := fun j => by simp [he j]
  -- radii `s n → ρ` with good extensions
  have hstep : ∀ n : ℕ, ∃ s ∈ Ioc (ρ * (1 - 1 / ((n : ℝ) + 2))) ρ,
      circleDeficit u x w s C ≤ K + ENNReal.ofReal (2 * π * (1 / ((n : ℝ) + 1)) * r) := by
    intro n
    have h1 : 0 < ρ * (1 - 1 / ((n : ℝ) + 2)) := by
      have : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      exact mul_pos hρ (by linarith)
    have h2 : ρ * (1 - 1 / ((n : ℝ) + 2)) < ρ := by
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      nlinarith
    obtain ⟨s, hs, O, F, hO, hsO, hF, hF0, hB⟩ :=
      hmep x w ρ hρ hD e hfin _ h1 h2 (1 / ((n : ℝ) + 1)) (by positivity)
    have hs0 : 0 < s := h1.trans hs.1
    have hDs : affineClosedDisc x w s ⊆ affineClosedDisc x w ρ := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, closedBall_subset_closedBall hs.2 hz, rfl⟩
    refine ⟨s, hs, hq.circleDeficit_le_of_extension hs0 (hDs.trans hD)
      (fun y hy => hC y (hDs hy)) hO hsO hF hF0 (by positivity) ?_⟩
    rwa [hsum] at hB
  choose s hs hbound using hstep
  have hlim : Tendsto s atTop (𝓝 ρ) := by
    have hl : Tendsto (fun n : ℕ => ρ * (1 - 1 / ((n : ℝ) + 2))) atTop (𝓝 ρ) := by
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h' := h.comp (tendsto_add_atTop_nat 1)
        refine h'.congr fun n => ?_
        simp only [Function.comp, Nat.cast_add, Nat.cast_one]
        ring_nf
      simpa using (this.const_sub 1).const_mul ρ
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
      (fun n => (hs n).1.le) fun n => (hs n).2
  -- the deficit function `(C - u)⁺` is lower semicontinuous at the points of `U`
  have hΦ : ∀ y ∈ U, LowerSemicontinuousAt (fun z => ((C : EReal) - u z).toENNReal) y := by
    intro y hy
    have husc : UpperSemicontinuousAt u y := fun b hb => by
      have h := hq.upperSemicontinuousOn_logDetDual y hy b hb
      rwa [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hy)] at h
    exact ContinuousAt.comp_upperSemicontinuousAt_antitone (g := fun v : EReal =>
      ((C : EReal) - v).toENNReal) (continuous_deficit C).continuousAt husc
      fun a b hab => EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hab)
  have hyD : ∀ (t : ℝ) (θ : ℝ), 0 < t → t ≤ ρ → x + circleMap 0 t θ • w ∈ U := by
    intro t θ ht htρ
    refine hD ⟨circleMap 0 t θ, ?_, rfl⟩
    exact closedBall_subset_closedBall htρ (sphere_subset_closedBall
      (circleMap_mem_sphere 0 ht.le θ))
  have hs0 : ∀ n, 0 < s n := fun n => (lt_of_le_of_lt (by
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    exact (mul_pos hρ (by linarith)).le) (hs n).1)
  -- measurability of the deficits
  have hmeas : ∀ n, Measurable fun θ : ℝ =>
      ((C : EReal) - u (x + circleMap 0 (s n) θ • w)).toENNReal := by
    intro n
    refine LowerSemicontinuous.measurable fun θ => ?_
    exact LowerSemicontinuousAt.comp (f := fun z => ((C : EReal) - u z).toENNReal)
      (g := fun θ : ℝ => x + circleMap 0 (s n) θ • w) (hΦ _ (hyD _ θ (hs0 n) (hs n).2))
      (by fun_prop)
  -- pointwise liminf
  have hpt : ∀ θ : ℝ, ((C : EReal) - u (x + circleMap 0 ρ θ • w)).toENNReal ≤
      liminf (fun n => ((C : EReal) - u (x + circleMap 0 (s n) θ • w)).toENNReal) atTop := by
    intro θ
    have ht : Tendsto (fun n => x + circleMap 0 (s n) θ • w) atTop
        (𝓝 (x + circleMap 0 ρ θ • w)) := by
      have hc : Continuous fun t : ℝ => x + circleMap 0 t θ • w := by
        simp only [circleMap, zero_add]
        fun_prop
      exact (hc.tendsto ρ).comp hlim
    refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    exact le_liminf_of_le (by isBoundedDefault)
      ((ht.eventually (hΦ _ (hyD ρ θ hρ le_rfl) b hb)).mono fun n hn => hn.le)
  -- Fatou
  have hK : Tendsto (fun n : ℕ => K + ENNReal.ofReal (2 * π * (1 / ((n : ℝ) + 1)) * r)) atTop
      (𝓝 K) := by
    have h0 : Tendsto (fun n : ℕ => 2 * π * (1 / ((n : ℝ) + 1)) * r) atTop (𝓝 0) := by
      simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2 * π)).mul_const (r : ℝ)
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_ofReal h0)
  calc circleDeficit u x w ρ C
      ≤ ∫⁻ θ in Ioc 0 (2 * π),
          liminf (fun n => ((C : EReal) - u (x + circleMap 0 (s n) θ • w)).toENNReal) atTop :=
        lintegral_mono hpt
    _ ≤ liminf (fun n => circleDeficit u x w (s n) C) atTop :=
        lintegral_liminf_le' fun n => (hmeas n).aemeasurable
    _ ≤ liminf (fun n : ℕ => K + ENNReal.ofReal (2 * π * (1 / ((n : ℝ) + 1)) * r)) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = K := hK.liminf_eq

/-! ### Plurisubharmonicity of `log det h*` and pluripolarity of the infinite-norm set -/

theorem stdFrame_mem_unitFrames :
    (fun j : Fin r => (Pi.single j 1 : Fin r → ℂ)) ∈ unitFrames r := by
  intro j _
  simp [mem_sphere_iff_norm, Pi.norm_single]

theorem colDet_stdFrame : colDet (fun j : Fin r => (Pi.single j 1 : Fin r → ℂ)) = 1 := by
  unfold colDet
  have h : (Matrix.of fun i j => (Pi.single j (1 : ℂ) : Fin r → ℂ) i) = 1 := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply]
  rw [h, Matrix.det_one]

/-- At a parameter where every vector has finite norm, `log det h* > -∞`. -/
theorem IsSingularNormFamily.logDetDual_ne_bot (hq : IsSingularNormFamily q U) (t : E)
    (hfin : ∀ v, q t v ≠ ⊤) : logDetDual q t ≠ ⊥ := by
  simp only [logDetDual, ne_eq, ENNReal.log_eq_bot_iff]
  intro h0
  have hle := hq.detRatio_le_detDual t (fun j => Pi.single j 1)
  rw [h0, nonpos_iff_eq_zero] at hle
  unfold detRatio at hle
  rw [colDet_stdFrame, ENNReal.div_eq_zero_iff] at hle
  rcases hle with h | h
  · simp at h
  · exact ENNReal.prod_ne_top (fun j _ => hfin _) h

/-- **`log det h*` is plurisubharmonic** (`[HPS18, Thm 21.1, Prop 25.1]`, `[Rau15, Prop 1.3]`,
in a holomorphic frame): for a singular norm family on an open set `U` with the minimal
extension property, `log det h*` satisfies the full disc criterion on `U`. -/
theorem IsSingularNormFamily.discPshOn_logDetDual (hq : IsSingularNormFamily q U)
    (hU : IsOpen U) (hmep : HasCircleMEP q U) : DiscPshOn (logDetDual q) U := by
  refine ⟨fun t ht => hq.logDetDual_ne_top ht, hq.upperSemicontinuousOn_logDetDual, ?_⟩
  intro x w ρ hρ hD C hC
  have hx : x ∈ U := hD (center_mem_affineClosedDisc x w hρ.le)
  have h2π : ENNReal.ofReal (2 * π) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsup : logDetDual q x = ⨆ C' : unitFrames r, ENNReal.log (detRatio (q x) C') := by
    rw [logDetDual, detDual, iSup_subtype']
    exact Pending.BergmanSupWeight.log_iSup _
  have : Nonempty (unitFrames r) := ⟨⟨_, stdFrame_mem_unitFrames⟩⟩
  have key : ∀ C' : unitFrames r, circleDeficit (logDetDual q) x w ρ C ≤
      ENNReal.ofReal (2 * π) * ((C : EReal) - ENNReal.log (detRatio (q x) C')).toENNReal := by
    rintro ⟨C', hC'⟩
    by_cases h0 : detRatio (q x) C' = 0
    · rw [h0, ENNReal.log_zero, EReal.sub_bot (EReal.coe_ne_bot C), EReal.toENNReal_top,
        ENNReal.mul_top h2π]
      exact le_top
    have hne0 : ∀ j, q x (C' j) ≠ 0 := fun j => hq.pos x hx _ fun h => by
      have := hC' j (mem_univ j)
      rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this
      exact zero_ne_one this
    have hP : ∏ j, q x (C' j) ≠ ⊤ := fun hP => h0 (by simp [detRatio, hP])
    have hnetop : ∀ j, q x (C' j) ≠ ⊤ := fun j hj => hP (by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), hj]
      exact ENNReal.top_mul (Finset.prod_ne_zero_iff.mpr fun i _ => hne0 i))
    set qj : Fin r → ℝ := fun j => (q x (C' j)).toReal
    have hqj : ∀ j, 0 < qj j := fun j => ENNReal.toReal_pos (hne0 j) (hnetop j)
    set c : Fin r → ℂ := fun j => (((Real.sqrt (qj j))⁻¹ : ℝ) : ℂ)
    have hc : ∀ j, c j ≠ 0 := fun j => by
      simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero', not_le]
      exact hqj j
    set e : Fin r → Fin r → ℂ := fun j => c j • C' j
    have he : ∀ j, q x (e j) = 1 := by
      intro j
      simp only [e]
      rw [hq.smul, ← ENNReal.ofReal_toReal (hnetop j), ← ENNReal.ofReal_mul (by positivity)]
      have hn : ‖c j‖ ^ 2 = (qj j)⁻¹ := by
        simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (hqj j).le]
      rw [hn, inv_mul_cancel₀ (hqj j).ne', ENNReal.ofReal_one]
    have hratio : detRatio (q x) C' = ENNReal.ofReal (‖colDet e‖ ^ 2) := by
      rw [← hq.detRatio_smul x hc C']
      simp [detRatio, e, he]
    rw [hratio]
    exact hq.circleDeficit_le_of_mep hU hmep hρ hD hC he
  calc circleDeficit (logDetDual q) x w ρ C
      ≤ ⨅ C' : unitFrames r,
          ENNReal.ofReal (2 * π) * ((C : EReal) - ENNReal.log (detRatio (q x) C')).toENNReal :=
        le_iInf key
    _ = ENNReal.ofReal (2 * π) *
          ⨅ C' : unitFrames r, ((C : EReal) - ENNReal.log (detRatio (q x) C')).toENNReal :=
        (ENNReal.mul_iInf_of_ne h2π ENNReal.ofReal_ne_top).symm
    _ ≤ ENNReal.ofReal (2 * π) * ((C : EReal) - logDetDual q x).toENNReal := by
        rw [hsup]
        exact mul_le_mul_right (Pending.BergmanSupWeight.iInf_sub_toENNReal_le C _) _

/-- **The infinite-norm set is pluripolar.** Let `q` be a singular norm family in a holomorphic
frame over a connected open set `U` (the Hodge metric of the direct image, `h(α) = ∫_{X_t}
|α|² e^{-φ}`), with the minimal extension property, and finite at one point of `U`. Then the set
of parameters `t ∈ U` such that some vector has infinite norm (some element of the fibre of the
direct image is not fibrewise `L²`) is locally pluripolar in `U`: it lies in the pole set of the
plurisubharmonic function `log det h*`, which is not identically `-∞`. -/
theorem IsSingularNormFamily.locallyPluripolarOn_infiniteNormSet
    (hq : IsSingularNormFamily q U) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hmep : HasCircleMEP q U) (hgood : ∃ t ∈ U, ∀ v, q t v ≠ ⊤) :
    LocallyPluripolarOn {t | ∃ v, q t v = ⊤} U := by
  have hpsh := (hq.discPshOn_logDetDual hU hmep).plurisubharmonicOn hU
  obtain ⟨t, ht, hfin⟩ := hgood
  intro x hx
  exact ⟨U, logDetDual q, hU, hx, hUc, hpsh, ⟨t, ht, hq.logDetDual_ne_bot t hfin⟩,
    fun y hyU hy => hq.logDetDual_eq_bot_of_exists_eq_top hyU hy⟩

end SGPT.PSH.DirImg2
