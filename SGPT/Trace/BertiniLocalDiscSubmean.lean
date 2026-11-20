import SGPT.PSH.DirImg2Mep
import SGPT.Foundations.Analysis.CircleMeanSecondOrder

/-! Genuine pointwise small-circle submeans imply the full PSH disc criterion. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal Laplacian

namespace SGPT.PSH.DirImg2
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The local radius is chosen after centre/direction, before every tested disc and bound. -/
def HasLocalDiscSubmeanOn (u : E → EReal) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ v : E, ∃ R : ℝ, 0 < R ∧
    ∀ r : ℝ, 0 < r → r ≤ R → affineClosedDisc x v r ⊆ U →
      ∀ C : ℝ, (∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) →
        circleDeficit u x v r C ≤
          ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u x).toENNReal

theorem HasLocalDiscSubmeanOn.le_circleAverage_of_touching_majorant
    {u : ℂ → EReal} {U : Set ℂ} (hu : HasLocalDiscSubmeanOn u U)
    {x : ℂ} (hx : x ∈ U) {g : ℂ → ℝ} (hg : Continuous g)
    {V : Set ℂ} (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ U)
    (heq : u x = (g x : EReal)) (hmajor : ∀ y ∈ V, u y ≤ (g y : EReal)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      g x ≤ Real.circleAverage g x r := by
  obtain ⟨R, hR, hmean⟩ := hu x hx 1
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hV x hxV
  refine ⟨min R (a / 2), lt_min hR (by positivity), ?_⟩
  intro r hr hrR
  have hrR' : r ≤ R := hrR.trans (min_le_left _ _)
  have hra : r < a := lt_of_le_of_lt (hrR.trans (min_le_right _ _)) (by linarith)
  have hDV : closedBall x r ⊆ V := fun y hy =>
    hball (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hra))
  have hline : affineClosedDisc x (1 : ℂ) r = closedBall x r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [dist_eq_norm] using hz
    · intro hy
      exact ⟨y - x, by simpa [dist_eq_norm] using hy, by simp⟩
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall x r).exists_isMaxOn
    (nonempty_closedBall.mpr hr.le) hg.continuousOn
  let C : ℝ := g y
  have hC : ∀ z ∈ closedBall x r, g z ≤ C := hmax
  have hsub := hmean r hr hrR' (hline ▸ (hDV.trans hVU)) C
    (fun z hz => (hmajor z (hDV (hline ▸ hz))).trans
      (EReal.coe_le_coe_iff.mpr (hC z (hline ▸ hz))))
  rw [heq] at hsub
  have hco : circleDeficit (fun z => (g z : EReal)) x 1 r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - (g x : EReal)).toENNReal :=
    (circleDeficit_antitone x 1 r C (fun t =>
      hmajor _ (hDV (hline ▸ circle_mem_affineClosedDisc x 1 hr.le t)))).trans hsub
  have hparam : Continuous (fun t : ℝ => g (x + circleMap 0 r t • (1 : ℂ))) := by
    fun_prop
  have hout := (circleDeficit_coe_le_iff x 1 r C (hparam.intervalIntegrable _ _)
    (fun t => hC _ (hline ▸ circle_mem_affineClosedDisc x 1 hr.le t))
    (hC x (mem_closedBall_self hr.le))).mp hco
  simpa only [smul_eq_mul, mul_one, add_comm x, Real.circleAverage_map_add_const] using hout

theorem HasLocalDiscSubmeanOn.laplacian_nonneg_of_touching_majorant
    {u : ℂ → EReal} {U : Set ℂ} (hu : HasLocalDiscSubmeanOn u U)
    {x : ℂ} (hx : x ∈ U) {g : ℂ → ℝ} (hg : ContDiff ℝ 2 g)
    {V : Set ℂ} (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ U)
    (heq : u x = (g x : EReal)) (hmajor : ∀ y ∈ V, u y ≤ (g y : EReal)) :
    0 ≤ Δ g x := by
  obtain ⟨R, hR, hmean⟩ := hu.le_circleAverage_of_touching_majorant hx hg.continuous
    hV hxV hVU heq hmajor
  exact laplacian_nonneg_of_circleAverage_submean hg x hR
    (fun r hr => hmean r hr.1 hr.2.le)

/-- Local small circles force genuine harmonic comparison on every original closed disc. -/
theorem HasLocalDiscSubmeanOn.le_harmonic_on_closedBall
    {u : ℂ → EReal} {U : Set ℂ} (hu : HasLocalDiscSubmeanOn u U)
    (husc : UpperSemicontinuousOn u U) (htop : ∀ x ∈ U, u x ≠ ⊤)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ U)
    {h : ℂ → ℝ} (hh : HarmonicOnNhd h univ)
    (hbound : ∀ z ∈ sphere c R, u z ≤ (h z : EReal)) :
    ∀ z ∈ closedBall c R, u z ≤ (h z : EReal) := by
  intro q hq
  by_contra hfail
  have hqu : (h q : EReal) < u q := lt_of_not_ge hfail
  have hqbot : u q ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (h q)).trans hqu)
  let a : ℝ := (u q).toReal - h q
  have ha : 0 < a := by
    have hreal : h q < (u q).toReal := by
      rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal (htop q (hD hq)) hqbot]
      exact hqu
    exact sub_pos.mpr hreal
  let ε : ℝ := a / (2 * (R ^ 2 + 1))
  have hε : 0 < ε := div_pos ha (by positivity)
  have hεR : ε * R ^ 2 < a := by
    have heq : ε * (2 * (R ^ 2 + 1)) = a := div_mul_cancel₀ a (by positivity)
    nlinarith [sq_nonneg R]
  let t : ℂ → ℝ := fun z => h z - ε * ‖z - c‖ ^ 2
  let f : ℂ → EReal := fun z => u z - (t z : EReal)
  have hhC : ContDiff ℝ 2 h := contDiffOn_univ.mp hh.contDiffOn
  have hnormC : ContDiff ℝ 2 (fun z : ℂ => ‖z-c‖^2) :=
    (contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const)
  have hscaled : ContDiff ℝ 2 (fun z : ℂ => ε * ‖z-c‖^2) := contDiff_const.mul hnormC
  have htC : ContDiff ℝ 2 t := hhC.sub hscaled
  have hfusc : UpperSemicontinuousOn f (closedBall c R) := by
    have hneg : UpperSemicontinuousOn (fun z : ℂ => ((-t z : ℝ) : EReal))
        (closedBall c R) :=
      (continuous_coe_real_ereal.comp htC.continuous.neg).upperSemicontinuous.upperSemicontinuousOn _
    simpa only [f, sub_eq_add_neg, ← EReal.coe_neg] using
      (husc.mono hD).add' hneg (fun z _ =>
        EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (-t z)))
          (Or.inr (EReal.coe_ne_top (-t z))))
  obtain ⟨y, hy, hmax⟩ := hfusc.exists_isMaxOn ⟨q,hq⟩ (isCompact_closedBall c R)
  have hqbig : ((ε * R ^ 2 : ℝ) : EReal) < f q := by
    rw [show f q = ((a + ε * ‖q - c‖ ^ 2 : ℝ) : EReal) by
      change u q - ((h q - ε * ‖q-c‖^2 : ℝ) : EReal) = _
      rw [← EReal.coe_toReal (htop q (hD hq)) hqbot, ← EReal.coe_sub]
      apply EReal.coe_eq_coe_iff.mpr
      dsimp [a]
      ring]
    apply EReal.coe_lt_coe_iff.mpr
    nlinarith [sq_nonneg ‖q-c‖]
  have hybig : ((ε * R ^ 2 : ℝ) : EReal) < f y := hqbig.trans_le (hmax hq)
  have hytop : f y ≠ ⊤ := by
    change u y + (-(t y : EReal)) ≠ ⊤
    exact EReal.add_ne_top (htop y (hD hy)) (by simp)
  have hybot : f y ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (ε * R ^ 2)).trans hybig)
  let B : ℝ := (f y).toReal
  have hyB : f y = (B : EReal) := (EReal.coe_toReal hytop hybot).symm
  have hyball : y ∈ ball c R := by
    apply mem_ball.mpr
    apply lt_of_le_of_ne (mem_closedBall.mp hy)
    intro heq
    have hys : y ∈ sphere c R := mem_sphere.mpr heq
    have hs : f y ≤ ((ε * R ^ 2 : ℝ) : EReal) := by
      calc
        f y ≤ (h y : EReal) - (t y : EReal) :=
          EReal.sub_le_sub (hbound y hys) le_rfl
        _ = ((ε * R ^ 2 : ℝ) : EReal) := by
          rw [← EReal.coe_sub]
          congr 1
          dsimp [t]
          have hn : ‖y-c‖ = R := by simpa [dist_eq_norm] using heq
          rw [hn]
          ring
    exact (not_lt_of_ge hs) hybig
  let g : ℂ → ℝ := fun z => B + t z
  have hg : ContDiff ℝ 2 g := contDiff_const.add htC
  have hgmajor : ∀ z ∈ ball c R, u z ≤ (g z : EReal) := by
    intro z hz
    have hzmax : u z - (t z : EReal) ≤ (B : EReal) :=
      (hmax (ball_subset_closedBall hz)).trans_eq hyB
    have hout := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot (t z)))
      (Or.inl (EReal.coe_ne_top (t z)))).mp hzmax
    simpa only [g, EReal.coe_add] using hout
  have hgeq : u y = (g y : EReal) := by
    have heq := congrArg (fun v : EReal => v + (t y : EReal)) hyB
    simpa only [f, EReal.sub_add_cancel, ← EReal.coe_add, g] using heq
  have hlap := hu.laplacian_nonneg_of_touching_majorant (hD hy) hg isOpen_ball
    hyball (ball_subset_closedBall.trans hD) hgeq hgmajor
  have hΔh : Δ h y = 0 := (hh y (mem_univ y)).2.self_of_nhds
  have hΔg : Δ g y = - (4 * ε) := by
    have hgfun : g = ((fun _ : ℂ => B) + h) - ε • (fun z : ℂ => ‖z-c‖^2) := by
      funext z
      dsimp [g,t]
      ring
    rw [hgfun]
    rw [ContDiffAt.laplacian_sub (f₁ := (fun _ : ℂ => B) + h)
      (f₂ := ε • (fun z : ℂ => ‖z-c‖^2))
      (contDiff_const.add hhC).contDiffAt (hnormC.const_smul ε).contDiffAt,
      ContDiffAt.laplacian_add (f₁ := fun _ : ℂ => B) (f₂ := h)
        contDiff_const.contDiffAt hhC.contDiffAt, laplacian_const, hΔh,
      laplacian_smul ε hnormC.contDiffAt, laplacian_complex_norm_sub_sq]
    simp [smul_eq_mul, mul_comm]
  rw [hΔg] at hlap
  linarith


/-- Actual continuous boundary majorants obey the center mean inequality. -/
theorem HasLocalDiscSubmeanOn.le_circleAverage_of_continuous_majorant
    {u : ℂ → EReal} {U : Set ℂ} (hu : HasLocalDiscSubmeanOn u U)
    (husc : UpperSemicontinuousOn u U) (htop : ∀ x ∈ U, u x ≠ ⊤)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ U)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgu : ∀ z ∈ sphere c R, u z ≤ (g z : EReal)) :
    u c ≤ ((Real.circleAverage g c R : ℝ) : EReal) := by
  have hctop : u c ≠ ⊤ := htop c (hD (mem_closedBall_self hR.le))
  by_cases hcbot : u c = ⊥
  · simp [hcbot]
  rw [← EReal.coe_toReal hctop hcbot, EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  obtain ⟨h, hh, happ⟩ := hasGlobalHarmonicCircleApproximation c hR.ne' g hg ε hε
  have happ : ∀ z ∈ sphere c R, |h z - g z| < ε := by
    simpa [abs_of_pos hR] using happ
  have hsphere : ∀ z ∈ sphere c R, u z ≤ ((h z + ε : ℝ) : EReal) := by
    intro z hz
    refine (hgu z hz).trans (EReal.coe_le_coe_iff.mpr ?_)
    have := (abs_lt.mp (happ z hz)).1
    linarith
  have hcenter : u c ≤ ((h c + ε : ℝ) : EReal) :=
    hu.le_harmonic_on_closedBall husc htop hR hD
      (hh.add (harmonicOnNhd_const ε)) hsphere c (mem_closedBall_self hR.le)
  have hhclosed : HarmonicOnNhd h (closedBall c |R|) := hh.mono (subset_univ _)
  have hcircle_h : CircleIntegrable h c R :=
    (hhclosed.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have hcircle_g : CircleIntegrable g c R := hg.continuousOn.circleIntegrable'
  have hcircle_const : CircleIntegrable (fun _ : ℂ => ε) c R := circleIntegrable_const ε c R
  have havg : h c ≤ Real.circleAverage g c R + ε := by
    have hmono : Real.circleAverage h c R ≤
        Real.circleAverage (fun z => g z + ε) c R := by
      apply Real.circleAverage_mono hcircle_h (hcircle_g.add hcircle_const)
      intro z hz
      have := (abs_lt.mp (happ z (by simpa [abs_of_pos hR] using hz))).2
      change h z ≤ g z + ε
      linarith
    rw [hhclosed.circleAverage_eq, Real.circleAverage_fun_add hcircle_g hcircle_const,
      Real.circleAverage_const] at hmono
    exact hmono
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal hctop hcbot]
  refine hcenter.trans (EReal.coe_le_coe_iff.mpr ?_)
  dsimp [ε] at havg ⊢
  linarith

/-- Scalar local small-circle inequalities imply the exact full closed-disc deficit. -/
theorem HasLocalDiscSubmeanOn.circleSubmean
    {u : ℂ → EReal} {U : Set ℂ} (hu : HasLocalDiscSubmeanOn u U)
    (husc : UpperSemicontinuousOn u U) (htop : ∀ x ∈ U, u x ≠ ⊤)
    {c : ℂ} {R C : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ U)
    (hC : ∀ z ∈ closedBall c R, u z ≤ (C : EReal)) :
    circleDeficit u c 1 R C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u c).toENNReal := by
  let K : Set ℂ := sphere c R
  have hK : IsCompact K := isCompact_sphere c R
  have hKne : K.Nonempty := by
    exact ⟨c + (R : ℂ), by simp [K, abs_of_pos hR]⟩
  have hKU : K ⊆ U := fun z hz => hD (sphere_subset_closedBall hz)
  have hKusc : UpperSemicontinuousOn u K := husc.mono hKU
  have hKtop : ∀ z ∈ K, u z ≠ ⊤ := fun z hz => htop z (hKU hz)
  have hCK : ∀ z ∈ K, u z ≤ (C : EReal) :=
    fun z hz => hC z (sphere_subset_closedBall hz)
  let g : ℕ → ℂ → ℝ := fun n => uscSupConvolution K u C n
  have hg : ∀ n, Continuous (g n) := fun n =>
    continuous_uscSupConvolution hKne hKtop hCK n
  have hgu : ∀ n z, z ∈ K → u z ≤ (g n z : EReal) := fun n z hz =>
    le_coe_uscSupConvolution hKne hKtop hCK n hz
  have hgC : ∀ n z, g n z ≤ C := fun n z => uscSupConvolution_le hKne hKtop hCK n z
  have hganti : ∀ z, Antitone fun n => g n z := fun z =>
    uscSupConvolution_antitone hKne hKtop hCK z
  have hginf : ∀ z, z ∈ K → (⨅ n : ℕ, (g n z : EReal)) = u z :=
    fun z hz => iInf_coe_uscSupConvolution hKne hKusc hKtop hCK hz
  apply circleSubmean_of_continuous_antitone_majorants c g hg
  · intro n z _
    exact hgC n z
  · intro t m n hmn
    exact EReal.coe_le_coe_iff.mpr (hganti (c + circleMap 0 R t) hmn)
  · intro t
    have hz : c + circleMap 0 R t ∈ K := by
      simpa [K, circleMap] using circleMap_mem_sphere c hR.le t
    exact hginf _ hz
  · intro n
    exact hu.le_circleAverage_of_continuous_majorant husc htop hR hD (hg n)
      (fun z hz => hgu n z hz)

/-- The full affine-disc criterion follows from actual pointwise small-circle deficits. -/
theorem discPshOn_of_local_disc_submean {u : E → EReal} {U : Set E}
    (husc : UpperSemicontinuousOn u U) (htop : ∀ x ∈ U, u x ≠ ⊤)
    (hu : HasLocalDiscSubmeanOn u U) : DiscPshOn u U := by
  refine ⟨htop, husc, ?_⟩
  intro x v r hr hD C hC
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  let A : ℂ → E := fun z => x + L z
  let Ω : Set ℂ := A ⁻¹' U
  let w : ℂ → EReal := fun z => u (A z)
  have hA : Continuous A := by fun_prop
  have hwusc : UpperSemicontinuousOn w Ω :=
    husc.comp hA.continuousOn (fun _ hz => hz)
  have hwtop : ∀ z ∈ Ω, w z ≠ ⊤ := fun z hz => htop (A z) hz
  have hLs : ∀ t b : ℂ, L (t * b) = t • L b := fun t b => by
    simpa only [smul_eq_mul] using L.map_smul t b
  have hwlocal : HasLocalDiscSubmeanOn w Ω := by
    intro z hz b
    obtain ⟨R,hR,hmean⟩ := hu (A z) hz (L b)
    refine ⟨R,hR,?_⟩
    intro s hs hsR hsD B hB
    have hD' : affineClosedDisc (A z) (L b) s ⊆ U := by
      rintro _ ⟨t,ht,rfl⟩
      have hin := hsD (show z + t • b ∈ affineClosedDisc z b s from ⟨t,ht,rfl⟩)
      simpa [Ω,A,map_add,hLs,add_assoc] using hin
    have hB' : ∀ a ∈ affineClosedDisc (A z) (L b) s, u a ≤ (B : EReal) := by
      rintro _ ⟨t,ht,rfl⟩
      have hin := hB (z + t • b) ⟨t,ht,rfl⟩
      simpa [w,A,map_add,hLs,add_assoc] using hin
    have hsub := hmean s hs hsR hD' B hB'
    rw [show w = (fun z => u (x + L z)) by rfl, circleDeficit_comp_affine u L x]
    exact hsub
  have hclosed : closedBall 0 r ⊆ Ω := by
    intro z hz
    exact hD ⟨z,hz,by simp [A,L]⟩
  have hwC : ∀ z ∈ closedBall 0 r, w z ≤ (C : EReal) := by
    intro z hz
    exact hC (A z) ⟨z,hz,by simp [A,L]⟩
  have hsub := hwlocal.circleSubmean hwusc hwtop hr hclosed hwC
  change circleDeficit (fun z => u (x + L z)) 0 1 r C ≤
    ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u (x + L 0)).toENNReal at hsub
  rw [circleDeficit_comp_affine u L x] at hsub
  simpa [L] using hsub

end SGPT.PSH.DirImg2
