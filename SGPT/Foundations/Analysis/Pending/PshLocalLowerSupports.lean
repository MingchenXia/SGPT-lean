import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

/-!
# Touching local plurisubharmonic lower supports

An upper semicontinuous function locally touched from below by actual PSH
functions is itself PSH. The supports propagate a finite maximum across a
closed disc; harmonic comparison and decreasing continuous circle majorants
then give the full deficit criterion. This supplies genuine boundary pasting
without a collar equality or any continuity assumption on the lower branch.
-/

set_option autoImplicit false

open InnerProductSpace Metric Set MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PshLocalLowerSupports

open FirstPass

noncomputable section

/-- Touching local PSH lower supports propagate the closed-disc maximum
principle, including functions with poles. -/
theorem le_const_on_closedBall_of_local_lower_supports
    {u : ℂ → EReal} {Ω : Set ℂ} (husc : UpperSemicontinuousOn u Ω)
    (hsupp : ∀ x ∈ Ω, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ f : ℂ → EReal, PlurisubharmonicOn f V ∧ f x = u x ∧ ∀ y ∈ V, f y ≤ u y)
    {c : ℂ} {R C : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ Ω)
    (hs : ∀ z ∈ sphere c R, u z ≤ (C : EReal)) :
    ∀ z ∈ closedBall c R, u z ≤ (C : EReal) := by
  intro q hq
  by_contra hqC
  have hCq : (C : EReal) < u q := lt_of_not_ge hqC
  obtain ⟨y, hyD, hmax⟩ :=
    (husc.mono hD).exists_isMaxOn
      ⟨q, hq⟩ (isCompact_closedBall c R)
  have hy_top : u y ≠ ⊤ := by
    obtain ⟨V, _, hyV, _, f, hf, heq, _⟩ := hsupp y (hD hyD)
    rw [← heq]
    exact (hf y hyV).ne_top
  have hy_bot : u y ≠ ⊥ := by
    have hy_gt : (C : EReal) < u y := hCq.trans_le (hmax hq)
    intro hy
    rw [hy] at hy_gt
    exact (not_lt_of_ge bot_le) hy_gt
  let B : ℝ := (u y).toReal
  have hyB : u y = (B : EReal) := (EReal.coe_toReal hy_top hy_bot).symm
  have hCB : C < B := by
    rw [← EReal.coe_lt_coe_iff, ← hyB]
    exact hCq.trans_le (hmax hq)
  have hy_ball : y ∈ ball c R := by
    have hyr : dist y c ≤ R := mem_closedBall.mp hyD
    apply mem_ball.mpr
    apply lt_of_le_of_ne hyr
    intro hyr_eq
    have hys : y ∈ sphere c R := mem_sphere.mpr hyr_eq
    have := hs y hys
    rw [hyB, EReal.coe_le_coe_iff] at this
    exact (not_lt_of_ge this) hCB
  let O : Set ℂ := {z | z ∈ ball c R ∧ u z = (B : EReal)}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨W, hW, hzW, _, f, hf, hfz, hfu⟩ :=
      hsupp z (hD (ball_subset_closedBall hz.1))
    have hdisc : DiscPshOn f W := hf.discPshOn
    have hopen : IsOpen (W ∩ ball c R) := hW.inter isOpen_ball
    have hzopen : z ∈ W ∩ ball c R := ⟨hzW, hz.1⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen z hzopen
    have hBW : ball z δ ⊆ W := fun w hw => (hball hw).1
    have hBbound : ∀ w ∈ ball z δ, f w ≤ (B : EReal) := by
      intro w hw
      exact (hfu w (hBW hw)).trans ((hmax (ball_subset_closedBall (hball hw).2)).trans_eq hyB)
    have heq := hdisc.eqOn_ball_of_le_of_eq z hBW hBbound (hfz.trans hz.2)
    refine ⟨δ, hδ, ?_⟩
    intro w hw
    refine ⟨(hball hw).2, le_antisymm ?_ ?_⟩
    · exact (hmax (ball_subset_closedBall (hball hw).2)).trans_eq hyB
    · exact (heq hw).symm.le.trans (hfu w (hBW hw))
  have hK : IsCompact (closedBall c R ∩ u ⁻¹' Ici (B : EReal)) :=
    (husc.mono hD).isCompact_inter_preimage_Ici
      (isCompact_closedBall c R) (B : EReal)
  have hOK : O ⊆ closedBall c R ∩ u ⁻¹' Ici (B : EReal) := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1, by simp [hz.2]⟩
  have hclosure : closure O ∩ closedBall c R ⊆ O := by
    intro z hz
    have hzK := closure_minimal hOK hK.isClosed hz.1
    have hzeq : u z = (B : EReal) := by
      apply le_antisymm
      · exact (hmax hz.2).trans_eq hyB
      · exact hzK.2
    have hzball : z ∈ ball c R := by
      have hzr : dist z c ≤ R := mem_closedBall.mp hz.2
      apply mem_ball.mpr
      apply lt_of_le_of_ne hzr
      intro hzr_eq
      have hzs : z ∈ sphere c R := mem_sphere.mpr hzr_eq
      have hzC := hs z hzs
      rw [hzeq, EReal.coe_le_coe_iff] at hzC
      exact (not_lt_of_ge hzC) hCB
    exact ⟨hzball, hzeq⟩
  have hnonempty : (closedBall c R ∩ O).Nonempty :=
    ⟨y, ball_subset_closedBall hy_ball, hy_ball, hyB⟩
  have hall : closedBall c R ⊆ O :=
    isPreconnected_closedBall.subset_of_closure_inter_subset hO hnonempty hclosure
  let z : ℂ := c + (R : ℂ)
  have hzs : z ∈ sphere c R := by
    simp [z, abs_of_pos hR]
  have hzO := hall (sphere_subset_closedBall hzs)
  exact (not_lt_of_ge (by
    have hzC := hs z hzs
    rw [hzO.2, EReal.coe_le_coe_iff] at hzC
    exact hzC)) hCB


/-- Harmonic comparison for touching local supports implies the center
bound by any continuous boundary majorant. -/
theorem le_circleAverage_of_local_lower_supports
    {u : ℂ → EReal} {Ω : Set ℂ} (husc : UpperSemicontinuousOn u Ω)
    (hsupp : ∀ x ∈ Ω, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ f : ℂ → EReal, PlurisubharmonicOn f V ∧ f x = u x ∧ ∀ y ∈ V, f y ≤ u y)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hD : closedBall c R ⊆ Ω) {g : ℂ → ℝ} (hg : Continuous g)
    (hgu : ∀ z ∈ sphere c R, u z ≤ (g z : EReal)) :
    u c ≤ ((Real.circleAverage g c R : ℝ) : EReal) := by
  have hcΩ : c ∈ Ω := hD (mem_closedBall_self hR.le)
  have hctop : u c ≠ ⊤ := by
    obtain ⟨V, _, hcV, _, f, hf, heq, _⟩ := hsupp c hcΩ
    rw [← heq]
    exact (hf c hcV).ne_top
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
  have hhΩ : HarmonicOnNhd h Ω := hh.mono (subset_univ Ω)
  have hsubusc : UpperSemicontinuousOn (fun z => u z - (h z : EReal)) Ω := by
    have hneg : UpperSemicontinuousOn (fun z : ℂ => ((-h z : ℝ) : EReal)) Ω :=
      (continuous_coe_real_ereal.comp_continuousOn hhΩ.continuousOn.neg).upperSemicontinuousOn
    simp only [sub_eq_add_neg, ← EReal.coe_neg]
    exact husc.add' hneg (fun z _ =>
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (-h z)))
        (Or.inr (EReal.coe_ne_top (-h z))))
  have hsubsupp : ∀ x ∈ Ω, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ f : ℂ → EReal, PlurisubharmonicOn f V ∧
        f x = u x - (h x : EReal) ∧ ∀ y ∈ V, f y ≤ u y - (h y : EReal) := by
    intro x hx
    obtain ⟨V, hV, hxV, hVΩ, f, hf, heq, hfu⟩ := hsupp x hx
    exact ⟨V, hV, hxV, hVΩ, (fun z => f z - (h z : EReal)),
      hf.sub_harmonic (hhΩ.mono hVΩ), by change f x - (h x : EReal) = _; rw [heq],
      fun y hy => EReal.sub_le_sub (hfu y hy) le_rfl⟩
  have hsphere : ∀ z ∈ sphere c R,
      u z - (h z : EReal) ≤ (ε : EReal) := by
    intro z hz
    have hreal : g z - h z ≤ ε := by
      have := (abs_lt.mp (happ z hz)).1
      linarith
    calc
      u z - (h z : EReal) ≤ (g z : EReal) - (h z : EReal) :=
        EReal.sub_le_sub (hgu z hz) le_rfl
      _ = ((g z - h z : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ (ε : EReal) := EReal.coe_le_coe_iff.mpr hreal
  have hcenter_sub : u c - (h c : EReal) ≤ (ε : EReal) :=
    le_const_on_closedBall_of_local_lower_supports hsubusc hsubsupp hR hD hsphere c
      (mem_closedBall_self hR.le)
  have hcenter : u c ≤ ((h c + ε : ℝ) : EReal) := by
    have hle := (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot (h c))) (Or.inl (EReal.coe_ne_top (h c)))).mp
      hcenter_sub
    simpa [← EReal.coe_add, add_comm] using hle
  have hhclosed : HarmonicOnNhd h (closedBall c |R|) :=
    hh.mono (subset_univ _)
  have hcircle_h : CircleIntegrable h c R :=
    (hhclosed.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have hcircle_g : CircleIntegrable g c R :=
    hg.continuousOn.circleIntegrable'
  have hcircle_const : CircleIntegrable (fun _ : ℂ => ε) c R :=
    circleIntegrable_const ε c R
  have havg : h c ≤ Real.circleAverage g c R + ε := by
    have hmono : Real.circleAverage h c R ≤
        Real.circleAverage (fun z => g z + ε) c R := by
      apply Real.circleAverage_mono hcircle_h (hcircle_g.add hcircle_const)
      intro z hz
      have := (abs_lt.mp (happ z (by simpa [abs_of_pos hR] using hz))).2
      change h z ≤ g z + ε
      linarith
    rw [hhclosed.circleAverage_eq,
      Real.circleAverage_fun_add hcircle_g hcircle_const,
      Real.circleAverage_const] at hmono
    exact hmono
  have hreal_center : (u c).toReal ≤ Real.circleAverage g c R + δ := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hctop hcbot]
    refine hcenter.trans ?_
    apply EReal.coe_le_coe_iff.mpr
    dsimp [ε] at havg ⊢
    linarith
  exact hreal_center


/-- Touching local lower supports give the exact extended-real deficit
submean inequality on each closed complex disc. -/
theorem circleSubmean_of_local_lower_supports
    {u : ℂ → EReal} {Ω : Set ℂ} (husc : UpperSemicontinuousOn u Ω)
    (hsupp : ∀ x ∈ Ω, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ f : ℂ → EReal, PlurisubharmonicOn f V ∧ f x = u x ∧ ∀ y ∈ V, f y ≤ u y)
    {c : ℂ} {R C : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ Ω)
    (hC : ∀ z ∈ closedBall c R, u z ≤ (C : EReal)) :
    circleDeficit u c 1 R C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u c).toENNReal := by
  let K : Set ℂ := sphere c R
  have hK : IsCompact K := isCompact_sphere c R
  have hKne : K.Nonempty := by
    let z : ℂ := c + (R : ℂ)
    exact ⟨z, by simp [K, z, abs_of_pos hR]⟩
  have hKΩ : K ⊆ Ω := by
    intro z hz
    exact hD (sphere_subset_closedBall hz)
  have hKusc : UpperSemicontinuousOn u K :=
    husc.mono hKΩ
  have htop : ∀ z ∈ K, u z ≠ ⊤ := by
    intro z hz
    obtain ⟨V, _, hzV, _, f, hf, heq, _⟩ := hsupp z (hKΩ hz)
    rw [← heq]
    exact (hf z hzV).ne_top
  have hCK : ∀ z ∈ K, u z ≤ (C : EReal) :=
    fun z hz => hC z (sphere_subset_closedBall hz)
  let g : ℕ → ℂ → ℝ := fun n => uscSupConvolution K u C n
  have hg : ∀ n, Continuous (g n) := fun n =>
    continuous_uscSupConvolution hKne htop hCK n
  have hgu : ∀ n z, z ∈ K → u z ≤ (g n z : EReal) := fun n z hz =>
    le_coe_uscSupConvolution hKne htop hCK n hz
  have hgC : ∀ n z, g n z ≤ C := fun n z =>
    uscSupConvolution_le hKne htop hCK n z
  have hganti : ∀ z, Antitone fun n => g n z := fun z =>
    uscSupConvolution_antitone hKne htop hCK z
  have hginf : ∀ z, z ∈ K → (⨅ n : ℕ, (g n z : EReal)) = u z :=
    fun z hz => iInf_coe_uscSupConvolution hKne hKusc htop hCK hz
  have hcenter : ∀ n, u c ≤ ((Real.circleAverage (g n) c R : ℝ) : EReal) := by
    intro n
    exact le_circleAverage_of_local_lower_supports husc hsupp hR hD (hg n)
      (fun z hz => hgu n z hz)
  apply circleSubmean_of_continuous_antitone_majorants c g hg
  · intro n z _
    exact hgC n z
  · intro t m n hmn
    apply EReal.coe_le_coe_iff.mpr
    exact hganti (c + circleMap 0 R t) hmn
  · intro t
    have hz : c + circleMap 0 R t ∈ K := by
      simpa [K, circleMap] using circleMap_mem_sphere c hR.le t
    exact hginf _ hz
  · exact hcenter

/-- The full affine-disc criterion follows from upper semicontinuity and
touching local PSH lower supports, in an arbitrary complex normed space. -/
theorem discPshOn_of_local_lower_supports
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} (husc : UpperSemicontinuousOn u U)
    (hsupp : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ f : E → EReal, PlurisubharmonicOn f V ∧ f x = u x ∧ ∀ y ∈ V, f y ≤ u y) :
    DiscPshOn u U := by
  refine ⟨?_, husc, ?_⟩
  · intro x hx
    obtain ⟨V, _, hxV, _, f, hf, heq, _⟩ := hsupp x hx
    rw [← heq]
    exact (hf x hxV).ne_top
  · intro x v r hr hD C hC
    let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
    let A : ℂ → E := fun z => x + L z
    let Ω : Set ℂ := A ⁻¹' U
    let w : ℂ → EReal := fun z => u (A z)
    have hA : Continuous A := by fun_prop
    have hwusc : UpperSemicontinuousOn w Ω :=
      husc.comp hA.continuousOn (fun _ hz => hz)
    have hwsupp : ∀ z ∈ Ω, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
        ∃ f : ℂ → EReal, PlurisubharmonicOn f V ∧
          f z = w z ∧ ∀ y ∈ V, f y ≤ w y := by
      intro z hz
      obtain ⟨V, hV, hzV, hVU, f, hf, heq, hfu⟩ := hsupp (A z) hz
      exact ⟨A ⁻¹' V, hV.preimage hA, hzV, fun y hy => hVU hy,
        (fun y => f (A y)), hf.comp_affine L x, heq, fun y hy => hfu (A y) hy⟩
    have hclosed : closedBall 0 r ⊆ Ω := by
      intro z hz
      apply hD
      exact ⟨z, hz, by simp [A, L]⟩
    have hwC : ∀ z ∈ closedBall 0 r, w z ≤ (C : EReal) := by
      intro z hz
      apply hC
      exact ⟨z, hz, by simp [A, L]⟩
    have hsub := circleSubmean_of_local_lower_supports hwusc hwsupp hr hclosed hwC
    change circleDeficit (fun z => u (x + L z)) 0 1 r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u (x + L 0)).toENNReal at hsub
    rw [circleDeficit_comp_affine u L x] at hsub
    simpa [L] using hsub

/-- An upper semicontinuous function on an open domain is PSH if an actual
local PSH lower support touches it at every point. -/
theorem plurisubharmonicOn_of_local_lower_supports
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → EReal} {U : Set E} (hU : IsOpen U)
    (husc : UpperSemicontinuousOn u U)
    (hsupp : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ f : E → EReal, PlurisubharmonicOn f V ∧ f x = u x ∧ ∀ y ∈ V, f y ≤ u y) :
    PlurisubharmonicOn u U :=
  (discPshOn_of_local_lower_supports husc hsupp).plurisubharmonicOn hU

/-- A dominating replacement by a PSH branch on an open subdomain is PSH
whenever the actual piecewise function is upper semicontinuous. The old
branch supplies touching lower supports at the boundary. -/
theorem plurisubharmonicOn_piecewise_of_upperSemicontinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U V : Set E} [DecidablePred (· ∈ V)] {f g : E → EReal}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hf : PlurisubharmonicOn f V) (hg : PlurisubharmonicOn g U)
    (hgf : ∀ x ∈ V, g x ≤ f x)
    (husc : UpperSemicontinuousOn (V.piecewise f g) U) :
    PlurisubharmonicOn (V.piecewise f g) U := by
  classical
  apply plurisubharmonicOn_of_local_lower_supports hU husc
  intro x hx
  by_cases hxV : x ∈ V
  · refine ⟨V, hV, hxV, hVU, f, hf, ?_, ?_⟩
    · simp [hxV]
    · intro y hy
      simp [hy]
  · refine ⟨U, hU, hx, subset_rfl, g, hg, ?_, ?_⟩
    · simp [hxV]
    · intro y _
      by_cases hy : y ∈ V
      · simpa [hy] using hgf y hy
      · simp [hy]

end

end SGPT.Foundations.Analysis.Pending.PshLocalLowerSupports
