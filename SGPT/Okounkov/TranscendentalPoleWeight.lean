import SGPT.Okounkov.TranscendentalPoleStatement
import SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential
import SGPT.Foundations.Analysis.PlurisubharmonicLimits
import SGPT.Foundations.Analysis.SmoothPlurisubharmonic
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.Pending.LocalPotentials

/-!
# The logarithm of Demailly--Păun's weight along a submanifold

Source: Demailly--Păun, *Numerical characterization of the Kähler cone*, Lemma 2.1 (the function
`ψ = ½ log ∑_j θ_j² ∑_k |g_{j,k}|²`); Xia, *Foundations of pluripotential theory*,
`lem:global-normal-pole` (the function `log R_Y`, `R_Y = ∑ χ_i² K_i`). Blueprint node
`tok:ext-pole`.

Let `V` be a closed complex submanifold of a compact complex manifold `X`. A *concentration
partition* (`SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential.ConcentrationPartition`)
is a finite family of local generator systems `g_{a,·}` of the vanishing ideal `𝓘_V` with a
chart-smooth partition of unity `θ_a`; its weight is `U = ∑_a θ_a² ∑_i |g_{a,i}|²`. We study the
extended-real function `F = log U` (`concentrationPole`):

* `concentrationPole_eq_bot_iff`, `continuous_concentrationPole`, `smoothOn_compl`,
  `exp_concentrationPole`: `F = -∞` exactly on `V`, `F` is continuous, smooth off `V`, and
  `e^F = U` is smooth;
* `exists_isThetaPshPotential_concentrationPole`: `F ∈ PSH(X, A ω)` for one `A > 0`. Off `V`
  this is Demailly--Păun's Hessian estimate `ddᶜ log U ≥ -A ω`
  (`ConcentrationPartition.exists_pos_levi_log_weight`); across `V` it follows because `F` is
  continuous with values in `[-∞, ∞)` and `-∞` exactly on `V` (`plurisubharmonicOn_of_continuousOn`,
  a decreasing limit of the psh functions `max(F, -j)`);
* `exists_weight_comparable`: near a point `x`, `U` is comparable with `∑ |h_i|²` for every
  finite family `h` generating `𝓘_V` at `x`;
* `hasAnalyticSingularitiesOfType_concentrationPole`: `F` has analytic singularities of type
  `(1, 𝓘_V)`; `localForm_concentrationPole`: `F = log ∑_{i ≥ k} |ζ_i|² + O(1)` in every
  flattening chart `ζ` of `V`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPole

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential
open SGPT.Foundations.Analysis.Pending.IdealWeightComparison

/-! ### Two facts on extended-real plurisubharmonic germs -/

section Psh

variable {n : ℕ}

private theorem iInf_max_neg_nat (a : EReal) :
    (⨅ j : ℕ, max a ((-(j : ℝ) : ℝ) : EReal)) = a := by
  apply le_antisymm
  · by_contra h
    obtain ⟨b, hab, hba⟩ := EReal.exists_rat_btwn_of_lt (lt_of_not_ge h)
    obtain ⟨j, hj⟩ := exists_nat_ge (-(b : ℝ))
    have hn : ((-(j : ℝ) : ℝ) : EReal) ≤ ((b : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by linarith)
    have h := (iInf_le (fun j : ℕ => max a ((-(j : ℝ) : ℝ) : EReal)) j).trans
      (max_le hab.le hn)
    exact not_lt_of_ge h hba
  · exact le_iInf fun _ => le_max_left _ _

/-- A function continuous with values in `[-∞, ∞)` which is plurisubharmonic near each point
where it is finite is plurisubharmonic: it is the decreasing limit of `max(q, -j)`, and
`max(q, -j)` is constant near the poles. -/
theorem plurisubharmonicOn_of_continuousOn {U : Set (ComplexModel n)}
    {q : ComplexModel n → EReal} (hU : IsOpen U) (hq : ContinuousOn q U)
    (hp : PlurisubharmonicOn q {z | z ∈ U ∧ q z ≠ ⊥}) :
    PlurisubharmonicOn q U := by
  have hj : ∀ j : ℕ, PlurisubharmonicOn
      (fun z => max (q z) ((-(j : ℝ) : ℝ) : EReal)) U := by
    intro j z hz
    by_cases hbot : q z = ⊥
    · have he := ((hq z hz).continuousAt (hU.mem_nhds hz)).eventually
        (Iio_mem_nhds (show q z < ((-(j : ℝ) : ℝ) : EReal) by
          rw [hbot]; exact EReal.bot_lt_coe _))
      apply (plurisubharmonicAt_const (((-(j : ℝ) : ℝ) : EReal)) (EReal.coe_ne_top _) z).congr
      filter_upwards [he] with y hy
      exact (max_eq_right hy.le).symm
    · exact (hp z ⟨hz, hbot⟩).max
        (plurisubharmonicAt_const (((-(j : ℝ) : ℝ) : EReal)) (EReal.coe_ne_top _) z)
  have hlim := DiscPshOn.plurisubharmonicOn_iInf_of_antitone hU
    (fun j => (hj j).discPshOn) (fun z _ a b hab => by
      apply max_le_max_left
      exact EReal.coe_le_coe_iff.mpr (by exact_mod_cast neg_le_neg (Nat.cast_le.mpr hab)))
  simpa only [iInf_max_neg_nat] using hlim

/-- A smooth function with semipositive Levi form on an open set is plurisubharmonic there. -/
theorem plurisubharmonicOn_of_contDiffOn_levi {U : Set (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hL : ∀ z ∈ U, ∀ v, 0 ≤ leviForm f z v) :
    PlurisubharmonicOn (fun z => (f z : EReal)) U := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hU hf hx
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp (inter_mem heq (hU.mem_nhds hx))
  have hgL : ∀ y ∈ V, ∀ v, 0 ≤ leviForm g y v := by
    intro y hy v
    have hl : f =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact (hVsub hz).1
    have h2 := (hl.iteratedFDeriv ℝ 2).eq_of_nhds
    simpa only [leviForm, realHessian, h2] using hL y (hVsub hy).2 v
  apply ((plurisubharmonicOn_of_levi_nonneg
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hV hgL) x hxV).congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  exact congrArg ((↑) : ℝ → EReal) (hVsub hy).1.symm

end Psh

/-! ### Logarithms of comparable quantities -/

section Logs

theorem abs_log_sub_log_le {W G c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hG : 0 < G)
    (h1 : c₁ * G ≤ W) (h2 : W ≤ c₂ * G) :
    |Real.log W - Real.log G| ≤ max |Real.log c₁| |Real.log c₂| := by
  have hW : 0 < W := lt_of_lt_of_le (mul_pos hc₁ hG) h1
  have hupper : Real.log W ≤ Real.log c₂ + Real.log G := by
    calc Real.log W ≤ Real.log (c₂ * G) := Real.log_le_log hW h2
      _ = Real.log c₂ + Real.log G := Real.log_mul hc₂.ne' hG.ne'
  have hlower : Real.log c₁ + Real.log G ≤ Real.log W := by
    calc Real.log c₁ + Real.log G = Real.log (c₁ * G) := (Real.log_mul hc₁.ne' hG.ne').symm
      _ ≤ Real.log W := Real.log_le_log (mul_pos hc₁ hG) h1
  have e1 : |Real.log c₁| ≤ max |Real.log c₁| |Real.log c₂| := le_max_left _ _
  have e2 : |Real.log c₂| ≤ max |Real.log c₁| |Real.log c₂| := le_max_right _ _
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log c₁)
    linarith
  · have := le_abs_self (Real.log c₂)
    linarith

/-- `log W = log G + (log W - log G)` as extended reals, including the case `W = G = 0`. -/
theorem log_ofReal_eq_add_of_comparable {W G c₂ : ℝ} (hW : 0 ≤ W) (hG : 0 ≤ G)
    (h1 : 0 < G → 0 < W) (h2 : W ≤ c₂ * G) :
    ENNReal.log (ENNReal.ofReal W) =
      ((((1 : ℚ) : ℝ)) : EReal) * ENNReal.log (ENNReal.ofReal G) +
        ((Real.log W - Real.log G : ℝ) : EReal) := by
  have h1' : (((1 : ℚ) : ℝ) : EReal) = 1 := by norm_num
  rw [h1', one_mul]
  rcases eq_or_lt_of_le hG with hG0 | hGpos
  · have hW0 : W = 0 := le_antisymm (by simpa [← hG0] using h2) hW
    rw [hW0, ← hG0]
    simp
  · have hWpos := h1 hGpos
    rw [ENNReal.log_ofReal_of_pos hWpos, ENNReal.log_ofReal_of_pos hGpos, ← EReal.coe_add]
    congr 1
    ring

end Logs

/-! ### The pole of a concentration partition -/

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

section Pole

variable {V : Set X} {ι : Type*} [Fintype ι] (P : ConcentrationPartition n V ι)

/-- **The pole** `F = log U` of Demailly--Păun's weight `U = ∑_a θ_a² ∑_i |g_{a,i}|²`, with
`log 0 = -∞`. -/
def concentrationPole : X → EReal := fun y => ENNReal.log (ENNReal.ofReal (P.weight y))

theorem concentrationPole_of_pos {y : X} (hy : 0 < P.weight y) :
    concentrationPole P y = (Real.log (P.weight y) : EReal) :=
  ENNReal.log_ofReal_of_pos hy

theorem concentrationPole_eq_bot_iff (hV : IsClosed V) (y : X) :
    concentrationPole P y = ⊥ ↔ y ∈ V := by
  constructor
  · intro h
    by_contra hy
    rw [concentrationPole_of_pos P (P.weight_pos_of_notMem hV hy)] at h
    exact EReal.coe_ne_bot _ h
  · intro hy
    simp [concentrationPole, P.weight_eq_zero_of_mem hy]

theorem concentrationPole_ne_top (y : X) : concentrationPole P y ≠ ⊤ := fun h =>
  ENNReal.ofReal_ne_top (ENNReal.log_eq_top_iff.mp h)

theorem continuous_concentrationPole : Continuous (concentrationPole P) :=
  ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp P.continuous_weight)

theorem exp_concentrationPole (y : X) :
    EReal.exp (concentrationPole P y) = ENNReal.ofReal (P.weight y) :=
  ENNReal.exp_log _

theorem chartSmooth_exp_concentrationPole :
    ChartSmooth (n := n) (fun x => (EReal.exp (concentrationPole P x)).toReal) := by
  have h : (fun x => (EReal.exp (concentrationPole P x)).toReal) = P.weight := by
    funext x
    rw [exp_concentrationPole, ENNReal.toReal_ofReal (P.weight_nonneg x)]
  rw [h]
  exact P.chartSmooth_weight

theorem smoothOn_compl_concentrationPole (hV : IsClosed V) (e : ComplexChart n X) :
    ContDiffOn ℝ ∞ (fun z => (concentrationPole P (e.val.symm z)).toReal)
      (e.val.target ∩ e.val.symm ⁻¹' Vᶜ) := by
  have hlog : ContDiffOn ℝ ∞ (fun z => Real.log (P.weight (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹' Vᶜ) :=
    ((P.chartSmooth_weight e).mono inter_subset_left).log
      fun z hz => (P.weight_pos_of_notMem hV hz.2).ne'
  refine hlog.congr fun z hz => ?_
  rw [concentrationPole_of_pos P (P.weight_pos_of_notMem hV hz.2), EReal.toReal_coe]

/-- **`F ∈ PSH(X, A ω)`** for one constant `A > 0` (Demailly--Păun Lemma 2.1 (ii) off `V`,
continuity across `V`). -/
theorem exists_isThetaPshPotential_concentrationPole [CompactSpace X] (hV : IsClosed V)
    (hVint : interior V = ∅) (omega : KahlerBackground n X) :
    ∃ A : ℝ, 0 < A ∧ IsThetaPshPotential (A • omega.form).val (concentrationPole P) := by
  obtain ⟨A, hA, hlev⟩ := P.exists_pos_levi_log_weight omega
  refine ⟨A, hA, fun e z hz => ?_, ?_⟩
  · obtain ⟨W, ρ, hzW, hρ⟩ :=
      LocalPotentials.closedRealOneOne_hasLocalPotentials (A • omega.form) e z hz
    refine ⟨W, ρ, hzW, hρ, ?_⟩
    have hWt : W ⊆ e.val.target := hρ.2.1
    set S : ComplexModel n → ℝ := fun w => P.weight (e.val.symm w) with hSdef
    have hS : ContDiffOn ℝ ∞ S W := (P.chartSmooth_weight e).mono hWt
    set q : ComplexModel n → EReal :=
      fun w => chartFunction (concentrationPole P) e w + (ρ w : EReal) with hqdef
    -- continuity of `q`
    have hq : ContinuousOn q W := by
      intro w hw
      have hF : ContinuousAt (fun w => concentrationPole P (e.val.symm w)) w :=
        (continuous_concentrationPole P).continuousAt.comp
          (e.val.continuousAt_symm (hWt hw))
      have hρc : ContinuousAt (fun w => (ρ w : EReal)) w :=
        continuous_coe_real_ereal.continuousAt.comp
          ((hρ.2.2.1.continuousOn w hw).continuousAt (hρ.1.mem_nhds hw))
      exact ((EReal.continuousAt_add (p := (concentrationPole P (e.val.symm w), (ρ w : EReal)))
        (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
          (f := fun w => (concentrationPole P (e.val.symm w), (ρ w : EReal)))
          (hF.prodMk hρc)).continuousWithinAt
    -- the smooth part on `{U > 0}`
    set O : Set (ComplexModel n) := {w | w ∈ W ∧ 0 < S w} with hOdef
    have hO : IsOpen O := hS.continuousOn.isOpen_inter_preimage hρ.1 isOpen_Ioi
    set f : ComplexModel n → ℝ := fun w => Real.log (S w) + ρ w with hfdef
    have hf : ContDiffOn ℝ ∞ f O :=
      ((hS.mono fun w hw => hw.1).log fun w hw => hw.2.ne').add
        (hρ.2.2.1.mono fun w hw => hw.1)
    have hL : ∀ w ∈ O, ∀ v, 0 ≤ leviForm f w v := by
      intro w hw v
      have h1 := hlev e w (hWt hw.1) hw.2 v
      have hlog2 : ContDiffAt ℝ 2 (fun w => Real.log (S w)) w :=
        ((((hS.mono fun w hw => hw.1).log fun w hw => hw.2.ne').contDiffAt
          (hO.mem_nhds hw)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      have hρ2 : ContDiffAt ℝ 2 ρ w :=
        ((hρ.2.2.1.contDiffAt (hρ.1.mem_nhds hw.1)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      have hdiag := smoothDDC_complexDiagonal_eq_leviForm hρ2 v
      rw [hρ.2.2.2 hw.1] at hdiag
      simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at hdiag
      have hfun : f = (fun w => Real.log (S w)) + ρ := rfl
      rw [hfun, leviForm_add hlog2 hρ2]
      have hpi := Real.pi_pos
      have hρL : leviForm ρ w v = Real.pi * (A * omega.form.val.coeff e w ![v, Complex.I • v]) := by
        rw [hdiag]
        field_simp
      have hmul := mul_nonneg hpi.le h1
      have hexp : Real.pi * (leviForm (fun w => Real.log (P.weight (e.val.symm w))) w v /
          Real.pi + A * omega.form.val.coeff e w ![v, Complex.I • v]) =
          leviForm (fun w => Real.log (S w)) w v +
            Real.pi * (A * omega.form.val.coeff e w ![v, Complex.I • v]) := by
        field_simp
        rfl
      rw [hρL]
      linarith
    have hfp := plurisubharmonicOn_of_contDiffOn_levi hO hf hL
    have hqp : PlurisubharmonicOn q {w | w ∈ W ∧ q w ≠ ⊥} := by
      intro w hw
      have hSw : 0 < S w := by
        by_contra hn
        have he : S w = 0 := le_antisymm (le_of_not_gt hn) (P.weight_nonneg _)
        apply hw.2
        change concentrationPole P (e.val.symm w) + (ρ w : EReal) = ⊥
        rw [concentrationPole]
        rw [show P.weight (e.val.symm w) = 0 from he]
        simp
      apply (hfp w ⟨hw.1, hSw⟩).congr
      filter_upwards [hO.mem_nhds ⟨hw.1, hSw⟩] with t ht
      change ((Real.log (S t) + ρ t : ℝ) : EReal) =
        concentrationPole P (e.val.symm t) + (ρ t : EReal)
      rw [concentrationPole_of_pos P ht.2, ← EReal.coe_add]
    exact plurisubharmonicOn_of_continuousOn hρ.1 hq hqp
  · intro x U hU hxU
    by_contra hcon
    push Not at hcon
    have hsub : U ⊆ V := fun y hy => (concentrationPole_eq_bot_iff P hV y).mp (hcon y hy)
    have hx : x ∈ interior V := interior_mono hsub (hU.interior_eq.symm ▸ hxU)
    rw [hVint] at hx
    exact hx

/-- Every generator of a piece whose domain contains `x` lies in `𝓘_V` at `x`. -/
theorem gen_mem_vanishingIdeal {x : X} {a : ι} (hxa : x ∈ P.dom a) (j : Fin (P.arity a)) :
    (vanishingIdeal (n := n) V).mem x (P.gen a j) := by
  refine (P.gen_spec a x hxa _).mpr ?_
  refine isInSpanAt_of_eq_mul ⟨j, rfl⟩ ?_ (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => by simp)
  filter_upwards [(P.isOpen_dom a).mem_nhds hxa] with z hz
  exact (P.gen_mdifferentiableOn a j z hz).mdifferentiableAt ((P.isOpen_dom a).mem_nhds hz)

/-- **Domination by the weight**: every finite holomorphic family `h` in `𝓘_V` at `x` satisfies
`∑ |h_i|² ≤ C U` near `x`. -/
theorem exists_generatorNormSq_le_weight_of_mem {x : X} {Q : ℕ} {h : Fin Q → X → ℂ}
    (hmem : ∀ i, (vanishingIdeal (n := n) V).mem x (h i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, generatorNormSq h y ≤ C * P.weight y := by
  obtain ⟨a₀, ha₀⟩ := P.exists_part_pos x
  have hx₀ : x ∈ P.dom a₀ := P.part_tsupport a₀ (subset_tsupport _ ha₀.ne')
  obtain ⟨B₀, hB₀, hB₀y⟩ := exists_nhds_generatorNormSq_le_of_forall_isInSpanAt
    (g := h) (h := P.gen a₀) (x := x) (fun i => (P.gen_spec a₀ x hx₀ _).mp (hmem i))
  obtain ⟨C, hC, hCy⟩ := P.exists_nhds_genNormSq_le_weight x
  refine ⟨B₀ * C, mul_pos hB₀ hC, ?_⟩
  filter_upwards [hB₀y, hCy] with y hy0 hyC
  calc generatorNormSq h y ≤ B₀ * generatorNormSq (P.gen a₀) y := hy0
    _ ≤ B₀ * (C * P.weight y) :=
      mul_le_mul_of_nonneg_left (hyC a₀ (subset_tsupport _ ha₀.ne')) hB₀.le
    _ = B₀ * C * P.weight y := by ring

/-- **Comparability with any local generator system**: if a finite holomorphic family `h`
generates `𝓘_V` at `x`, then `c₁ ∑ |h_i|² ≤ U ≤ c₂ ∑ |h_i|²` near `x`. -/
theorem exists_weight_comparable {x : X} {Q : ℕ} {h : Fin Q → X → ℂ}
    (hhol : ∀ i, HolomorphicAt n (h i) x)
    (hgen : ∀ f, (vanishingIdeal (n := n) V).mem x f ↔ IsInSpanAt (n := n) (· ∈ range h) x f) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ y in 𝓝 x,
      c₁ * generatorNormSq h y ≤ P.weight y ∧ P.weight y ≤ c₂ * generatorNormSq h y := by
  classical
  -- the upper bound, piece by piece
  have key : ∀ a, ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 x,
      P.part a y ^ 2 * P.genNormSq a y ≤ B * generatorNormSq h y := by
    intro a
    by_cases hxa : x ∈ tsupport (P.part a)
    · have hdom := P.part_tsupport a hxa
      obtain ⟨B, hB, hBy⟩ := exists_nhds_generatorNormSq_le_of_forall_isInSpanAt
        (fun j => (hgen _).mp (gen_mem_vanishingIdeal P hdom j))
      refine ⟨B, hB, ?_⟩
      filter_upwards [hBy, (P.isOpen_dom a).mem_nhds hdom] with y hy hyd
      rw [ConcentrationPartition.genNormSq, Set.indicator_of_mem hyd]
      have h1 : P.part a y ^ 2 ≤ 1 := by
        have := P.part_le_one a y
        have := P.part_nonneg a y
        nlinarith
      calc P.part a y ^ 2 * generatorNormSq (P.gen a) y ≤ 1 * generatorNormSq (P.gen a) y :=
            mul_le_mul_of_nonneg_right h1 (generatorNormSq_nonneg _ _)
        _ ≤ B * generatorNormSq h y := by rw [one_mul]; exact hy
    · refine ⟨1, one_pos, ?_⟩
      filter_upwards [(isClosed_tsupport (P.part a)).isOpen_compl.mem_nhds hxa] with y hy
      rw [P.part_eq_zero_of_notMem_tsupport hy]
      simpa using generatorNormSq_nonneg h y
  choose B hB hBy using key
  -- the lower bound, through one piece through `x`
  obtain ⟨a₀, ha₀⟩ := P.exists_part_pos x
  have hx₀ : x ∈ P.dom a₀ := P.part_tsupport a₀ (subset_tsupport _ ha₀.ne')
  obtain ⟨B₀, hB₀, hB₀y⟩ := exists_nhds_generatorNormSq_le_of_forall_isInSpanAt
    (g := h) (h := P.gen a₀) (x := x)
    (fun i => (P.gen_spec a₀ x hx₀ _).mp ((hgen _).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hhol i))))
  obtain ⟨C, hC, hCy⟩ := P.exists_nhds_genNormSq_le_weight x
  have hBs : (0 : ℝ) ≤ ∑ a, B a := Finset.sum_nonneg fun a _ => (hB a).le
  refine ⟨1 / (B₀ * C), ∑ a, B a + 1, by positivity, by linarith, ?_⟩
  filter_upwards [eventually_all.mpr hBy, hB₀y, hCy] with y hyB hy0 hyC
  have hG : 0 ≤ generatorNormSq h y := generatorNormSq_nonneg _ _
  constructor
  · have h1 := hyC a₀ (subset_tsupport _ ha₀.ne')
    have h2 : generatorNormSq h y ≤ B₀ * C * P.weight y := by
      calc generatorNormSq h y ≤ B₀ * generatorNormSq (P.gen a₀) y := hy0
        _ ≤ B₀ * (C * P.weight y) := mul_le_mul_of_nonneg_left h1 hB₀.le
        _ = B₀ * C * P.weight y := by ring
    have hBC : 0 < B₀ * C := mul_pos hB₀ hC
    calc 1 / (B₀ * C) * generatorNormSq h y ≤ 1 / (B₀ * C) * (B₀ * C * P.weight y) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = P.weight y := by field_simp
  · calc P.weight y ≤ ∑ a, B a * generatorNormSq h y := Finset.sum_le_sum fun a _ => hyB a
      _ = (∑ a, B a) * generatorNormSq h y := by rw [Finset.sum_mul]
      _ ≤ (∑ a, B a + 1) * generatorNormSq h y := by nlinarith

/-- **Analytic singularities of type `(1, 𝓘_V)`**: `F = log ∑_i |g_{a₀,i}|² + O(1)` near each
point, for the generators of a piece through it. -/
theorem hasAnalyticSingularitiesOfType_concentrationPole (hV : IsClosedSubmanifold n V) :
    HasAnalyticSingularitiesOfType (n := n) (concentrationPole P) 1 (vanishingIdeal (n := n) V) := by
  refine ⟨one_pos, VanishingIdealCoherent.isCoherent_vanishingIdeal hV, fun x => ?_⟩
  obtain ⟨a₀, ha₀⟩ := P.exists_part_pos x
  have hx₀ : x ∈ P.dom a₀ := P.part_tsupport a₀ (subset_tsupport _ ha₀.ne')
  have hhol : ∀ i, HolomorphicAt n (P.gen a₀ i) x := fun i => by
    filter_upwards [(P.isOpen_dom a₀).mem_nhds hx₀] with z hz
    exact (P.gen_mdifferentiableOn a₀ i z hz).mdifferentiableAt ((P.isOpen_dom a₀).mem_nhds hz)
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ := exists_weight_comparable P hhol (P.gen_spec a₀ x hx₀)
  obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp (hb.and ((P.isOpen_dom a₀).mem_nhds hx₀))
  refine ⟨U, hU, hxU, P.arity a₀, P.gen a₀,
    fun i => (P.gen_mdifferentiableOn a₀ i).mono fun y hy => (hUsub hy).2,
    fun y hy => P.gen_spec a₀ y (hUsub hy).2,
    fun y => Real.log (P.weight y) - Real.log (generatorNormSq (P.gen a₀) y),
    max |Real.log c₁| |Real.log c₂|, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := (hUsub hy).1
    rcases eq_or_lt_of_le (generatorNormSq_nonneg (P.gen a₀) y) with hG | hG
    · have hw : P.weight y = 0 :=
        le_antisymm (by simpa [← hG] using h2) (P.weight_nonneg y)
      show |Real.log (P.weight y) - Real.log (generatorNormSq (P.gen a₀) y)| ≤ _
      rw [hw, ← hG]
      simp only [Real.log_zero, sub_self, abs_zero]
      exact le_trans (abs_nonneg _) (le_max_left _ _)
    · exact abs_log_sub_log_le hc₁ hc₂ hG h1 h2
  · obtain ⟨h1, h2⟩ := (hUsub hy).1
    rw [generatorLog_eq_log_sum]
    exact log_ofReal_eq_add_of_comparable (P.weight_nonneg y) (generatorNormSq_nonneg _ _)
      (fun hG => lt_of_lt_of_le (mul_pos hc₁ hG) h1) h2

omit [IsComplexManifold n X] in
theorem flatNormalWeight_eq_generatorNormSq {x₀ : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)) (k : ℕ) (y : X) :
    flatNormalWeight Φ k y = generatorNormSq (flatGen Φ k) y := by
  unfold flatNormalWeight generatorNormSq flatGen
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · exact Complex.normSq_eq_norm_sq _
  · simp

/-- The normal flat coordinates of a flattening generate `𝓘_V` at the centre. -/
theorem flatGen_generates {x₀ : X}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)} {k : ℕ}
    (hΦ : IsFlatteningOf V Φ k) (f : X → ℂ) :
    (vanishingIdeal (n := n) V).mem x₀ f ↔
      IsInSpanAt (n := n) (· ∈ range (flatGen Φ k)) x₀ f := by
  have hy := mem_flatDomain_self Φ
  constructor
  · intro hf
    obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦ.1 hΦ.2 hy hf
    refine ⟨hf.1, n, flatGen Φ k, b, fun i => ⟨i, rfl⟩, hbhol, ?_⟩
    filter_upwards [hbeq] with y' h1
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hik : k ≤ i.1
    · simp [flatGen, hik]
    · rw [hb0 i (Nat.lt_of_not_le hik)]
      simp
  · refine VanishingIdealCoherent.mem_vanishingIdeal_of_isInSpanAt fun i => ?_
    by_cases hik : k ≤ i.1
    · simpa only [flatGen, hik, if_true] using flatCoord_mem_vanishingIdeal Φ hΦ.2 hik hy
    · simp only [flatGen, hik, if_false]
      exact ⟨holomorphicAt_const 0, Eventually.of_forall fun _ _ => rfl⟩

theorem holomorphicAt_flatGen {x₀ : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)) (k : ℕ) (i : Fin n) :
    HolomorphicAt n (flatGen Φ k i) x₀ := by
  by_cases hik : k ≤ i.1
  · simpa only [flatGen, hik, if_true] using holomorphicAt_flatCoord Φ i (mem_flatDomain_self Φ)
  · simpa only [flatGen, hik, if_false] using holomorphicAt_const (n := n) (M := X) (x := x₀) (0 : ℂ)

/-- **The local form in every flattening chart**: `F = log ∑_{i ≥ k} |ζ_i|² + O(1)` near `x`. -/
theorem localForm_concentrationPole (hV : IsClosed V) {x : X}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)} {k : ℕ}
    (hΦ : IsFlatteningOf V Φ k) :
    ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, y ∉ V →
      |(concentrationPole P y).toReal - Real.log (flatNormalWeight Φ k y)| ≤ C := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ :=
    exists_weight_comparable P (holomorphicAt_flatGen Φ k) (flatGen_generates hΦ)
  refine ⟨_, hb, max |Real.log c₁| |Real.log c₂|, fun y hy hyV => ?_⟩
  obtain ⟨h1, h2⟩ := hy
  have hW := P.weight_pos_of_notMem hV hyV
  have hG : 0 < generatorNormSq (flatGen Φ k) y := by
    by_contra hn
    have h0 : generatorNormSq (flatGen Φ k) y = 0 :=
      le_antisymm (le_of_not_gt hn) (generatorNormSq_nonneg _ _)
    rw [h0, mul_zero] at h2
    linarith
  rw [concentrationPole_of_pos P hW, EReal.toReal_coe, flatNormalWeight_eq_generatorNormSq]
  exact abs_log_sub_log_le hc₁ hc₂ hG h1 h2

end Pole

end SGPT.Okounkov.TranscendentalPole
