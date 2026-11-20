import SGPT.Foundations.Analysis.Pending.PshBallDeficitComparison
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A uniform `L¹` bound for normalized `θ`-psh functions on a compact connected manifold

Source: Guedj--Zeriahi, *Degenerate complex Monge--Ampère equations*, Proposition 8.5 (the
family of `θ`-psh functions with `sup_X u = 0` is relatively compact in `L¹`); Demailly, CADG I.4
(the Harnack comparison between the mean and the supremum).  TN.4 plan, step B6, finding F6 route
(i), piece (i-2): the potentials `v_ε` of the
currents `R_ε` are normalized and have a weak limit in each chart, which needs this bound.

Let `M` be a compact **connected** complex manifold and `θ` a smooth real two-form with smooth
local potentials.  For every level `c` and every chart ball (`HarnackBall`) there is a constant
`B < ∞` such that every `θ`-psh function `u ≤ 0` with `u(x₀) ≥ -c` at SOME point `x₀ ∈ M` satisfies
`∫_{ball} |u ∘ e⁻¹| dλ ≤ B` (`HarnackBall.exists_lintegral_le`); hence also on every compact set
of a chart (`exists_lintegral_compact_le`).  The normalization point may be anywhere: this is
where connectedness enters.  Without it the statement is false (`u = 0` on one component and
`u = -k` on another).

## The argument

* **Harnack** (`HarnackBall.deficit_le`): in a chart ball `ball z r` with a smooth local potential
  `ρ` of `θ` on `closedBall z (3r)`, `v = u ∘ e⁻¹ + ρ` is psh and `≤ A = max ρ`, so the Harnack
  comparison `PshBallDeficitComparison.deficitInt_le_of_near_center` bounds
  `∫_{ball z r} (A - v)⁺` by `λ(ball 0 2r) (A + c - min ρ)` as soon as `u ≥ -c` at one point of the
  ball.
* **First moment** (`HarnackBall.exists_point`): a bound on that integral gives, in any nonempty
  open `O ⊆ ball z r`, a point where `u ≥ -c'` (`measure_le_laverage_pos`).
* **Transfer** (`HarnackBall.transfer`): if two Harnack balls meet, control in the first gives
  control in the second.
* **Connectedness** (`exists_forall_mem_set_le`): the relation "control near `x` gives control
  near `y`" is transitive and holds for `y` near `x`, hence for all `x, y`
  (`PreconnectedSpace.induction₂'`); compactness makes the constant independent of the
  normalization point.

Poles are allowed throughout (`u` may be `-∞` on a null set; the deficits are `ℝ≥0∞`-valued).
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {θ : SmoothRealForm n M 2}

/-- A chart ball `ball z r` together with a smooth local potential `ρ` of `θ` on an open set `W`
containing `closedBall z (3r)`: the setting of the Harnack comparison. -/
structure HarnackBall (θ : SmoothRealForm n M 2) where
  /-- The chart. -/
  e : ComplexChart n M
  /-- The centre, in chart coordinates. -/
  z : ComplexModel n
  /-- The radius. -/
  r : ℝ
  /-- The domain of the local potential. -/
  W : Set (ComplexModel n)
  /-- The local potential. -/
  ρ : ComplexModel n → ℝ
  r_pos : 0 < r
  potential : IsSmoothLocalPotential θ e W ρ
  closedBall_subset : closedBall z (3 * r) ⊆ W

namespace HarnackBall

variable (H : HarnackBall θ)

/-- The open set of `M` which the chart reads as `ball z r`. -/
def set : Set M := H.e.val.source ∩ H.e.val ⁻¹' ball H.z H.r

theorem isOpen_set : IsOpen H.set :=
  H.e.val.continuousOn.isOpen_inter_preimage H.e.val.open_source isOpen_ball

theorem ball_subset_closedBall : ball H.z H.r ⊆ closedBall H.z (3 * H.r) :=
  Metric.ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [H.r_pos]))

theorem ball_subset_W : ball H.z H.r ⊆ H.W := H.ball_subset_closedBall.trans H.closedBall_subset

theorem ball_subset_target : ball H.z H.r ⊆ H.e.val.target :=
  H.ball_subset_W.trans H.potential.2.1

theorem symm_mem_set {y : ComplexModel n} (hy : y ∈ ball H.z H.r) : H.e.val.symm y ∈ H.set :=
  ⟨H.e.val.map_target (H.ball_subset_target hy), by
    rw [mem_preimage, H.e.val.right_inv (H.ball_subset_target hy)]
    exact hy⟩

theorem set_nonempty : H.set.Nonempty := ⟨_, H.symm_mem_set (mem_ball_self H.r_pos)⟩

/-- The local potential is bounded on `closedBall z (3r)`. -/
theorem exists_bounds :
    ∃ A P : ℝ, ∀ y ∈ closedBall H.z (3 * H.r), P ≤ H.ρ y ∧ H.ρ y ≤ A := by
  have hc : ContinuousOn H.ρ (closedBall H.z (3 * H.r)) :=
    H.potential.2.2.1.continuousOn.mono H.closedBall_subset
  have hne : (closedBall H.z (3 * H.r)).Nonempty :=
    ⟨H.z, mem_closedBall_self (by linarith [H.r_pos])⟩
  obtain ⟨y₁, -, hy₁⟩ := (isCompact_closedBall H.z (3 * H.r)).exists_isMaxOn hne hc
  obtain ⟨y₂, -, hy₂⟩ := (isCompact_closedBall H.z (3 * H.r)).exists_isMinOn hne hc
  exact ⟨H.ρ y₁, H.ρ y₂, fun y hy => ⟨hy₂ hy, hy₁ hy⟩⟩

/-- The corrected chart function `u ∘ e⁻¹ + ρ`, plurisubharmonic on `W`. -/
def corrected (u : M → EReal) : ComplexModel n → EReal :=
  fun y => chartFunction u H.e y + (H.ρ y : EReal)

theorem discPshOn_corrected {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) :
    DiscPshOn (H.corrected u) H.W :=
  (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hu H.e
    H.potential).discPshOn

/-- **The Harnack bound.**  If `u ≤ 0` is `θ`-psh and `u ≥ -c` at one point of the ball, the
deficit `∫_{ball z r} (A - (u ∘ e⁻¹ + ρ))⁺` is at most `λ(ball 0 2r) (A + c - P)`. -/
theorem deficit_le {A P : ℝ} (hAP : ∀ y ∈ closedBall H.z (3 * H.r), P ≤ H.ρ y ∧ H.ρ y ≤ A)
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) (hle : ∀ x, u x ≤ 0) {c : ℝ}
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ ball H.z H.r)
    (hc : ((-c : ℝ) : EReal) ≤ u (H.e.val.symm z₀)) :
    ∫⁻ y in ball H.z H.r, ((A : EReal) - H.corrected u y).toENNReal ≤
      volume (ball (0 : ComplexModel n) (2 * H.r)) * ENNReal.ofReal (A + c - P) := by
  have hball3 : ball H.z (3 * H.r) ⊆ H.W :=
    Metric.ball_subset_closedBall.trans H.closedBall_subset
  have hCu : ∀ w ∈ ball H.z (3 * H.r), H.corrected u w ≤ (A : EReal) := by
    intro w hw
    have hρ := (hAP w (Metric.ball_subset_closedBall hw)).2
    calc H.corrected u w = u (H.e.val.symm w) + (H.ρ w : EReal) := rfl
      _ ≤ 0 + (A : EReal) := add_le_add (hle _) (EReal.coe_le_coe_iff.mpr hρ)
      _ = (A : EReal) := zero_add _
  have hdist : ‖z₀ - H.z‖ ≤ H.r := by
    have := mem_ball.mp hz₀
    rw [dist_eq_norm] at this
    exact this.le
  have hkey := PshBallDeficitComparison.deficitInt_le_of_near_center (μ := volume)
    (u := H.corrected u) (p := H.z) (R := 3 * H.r) ((H.discPshOn_corrected hu).mono hball3) hCu
    (r := H.r) (K := 1) (by linarith) hdist
  rw [one_mul, show ((1 : ℝ) + 1) * H.r = 2 * H.r by ring] at hkey
  refine hkey.trans (mul_le_mul' le_rfl ?_)
  have hρ₀ := (hAP z₀ (H.ball_subset_closedBall hz₀)).1
  have hne : u (H.e.val.symm z₀) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hc
  have hnt : u (H.e.val.symm z₀) ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hle _)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, u (H.e.val.symm z₀) = (t : EReal) :=
    ⟨(u (H.e.val.symm z₀)).toReal, (EReal.coe_toReal hnt hne).symm⟩
  have hct : -c ≤ t := by rw [ht] at hc; exact EReal.coe_le_coe_iff.mp hc
  have hval : (A : EReal) - H.corrected u z₀ = ((A - (t + H.ρ z₀) : ℝ) : EReal) := by
    simp only [corrected, chartFunction, ht]
    push_cast
    rfl
  rw [hval, EReal.real_coe_toENNReal]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Below the ball, `-u ∘ e⁻¹` is at most the deficit `A - (u ∘ e⁻¹ + ρ)`. -/
theorem neg_le_deficit {A : ℝ} (hA : ∀ y ∈ closedBall H.z (3 * H.r), H.ρ y ≤ A)
    (u : M → EReal) {y : ComplexModel n} (hy : y ∈ ball H.z H.r) :
    (-u (H.e.val.symm y)).toENNReal ≤ ((A : EReal) - H.corrected u y).toENNReal := by
  refine EReal.toENNReal_le_toENNReal ?_
  have hρ := hA y (H.ball_subset_closedBall hy)
  simp only [corrected, chartFunction]
  induction u (H.e.val.symm y) using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- **First moment.**  A bound on the deficit integral gives, in any nonempty open subset `O` of
the ball, a point where `u ≥ -c'`, with `c'` depending only on the data and on `c`. -/
theorem exists_point (O : Set (ComplexModel n)) (hO : IsOpen O) (hOne : O.Nonempty)
    (hOsub : O ⊆ ball H.z H.r) (c : ℝ) :
    ∃ c' : ℝ, ∀ u : M → EReal, ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ z₀ ∈ ball H.z H.r, ((-c : ℝ) : EReal) ≤ u (H.e.val.symm z₀)) →
        ∃ y ∈ O, ((-c' : ℝ) : EReal) ≤ u (H.e.val.symm y) := by
  obtain ⟨A, P, hAP⟩ := H.exists_bounds
  set B : ℝ≥0∞ := volume (ball (0 : ComplexModel n) (2 * H.r)) * ENNReal.ofReal (A + c - P)
  have hBlt : B < ⊤ := ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top
  have hOpos : 0 < volume O := hO.measure_pos volume hOne
  have hOfin : volume O < ⊤ :=
    (measure_mono hOsub).trans_lt measure_ball_lt_top
  set κ : ℝ≥0∞ := (volume O)⁻¹ * B
  have hκ : κ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hOpos) hBlt
  refine ⟨κ.toReal, fun u hu hle hex => ?_⟩
  obtain ⟨z₀, hz₀, hc⟩ := hex
  set g : ComplexModel n → ℝ≥0∞ := fun y => ((A : EReal) - H.corrected u y).toENNReal
  set μ : Measure (ComplexModel n) := volume.restrict O
  have hμ : μ ≠ 0 := by
    intro h
    have : μ univ = 0 := by rw [h]; rfl
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at this
    exact hOpos.ne' this
  have hg : AEMeasurable g μ :=
    (H.discPshOn_corrected hu).aemeasurable_deficit_restrict hO.measurableSet
      (hOsub.trans H.ball_subset_W) A volume
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hOfin.ne
  have hpos := measure_le_laverage_pos hμ hg
  have havg : ⨍⁻ y, g y ∂μ ≤ κ := by
    rw [laverage_eq, Measure.restrict_apply MeasurableSet.univ, univ_inter, ENNReal.div_eq_inv_mul]
    refine mul_le_mul' le_rfl ?_
    exact (lintegral_mono_set hOsub).trans (H.deficit_le hAP hu hle hz₀ hc)
  rw [Measure.restrict_apply' hO.measurableSet] at hpos
  obtain ⟨y, hy, hyO⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨y, hyO, ?_⟩
  have hgy : g y ≤ κ := hy.trans havg
  have hρ := (hAP y (H.ball_subset_closedBall (hOsub hyO))).2
  have hκ' : κ ≠ ⊤ := hκ.ne
  simp only [g, corrected, chartFunction] at hgy
  induction hu' : u (H.e.val.symm y) using EReal.rec with
  | bot =>
    rw [hu'] at hgy
    simp at hgy
    exact absurd hgy hκ'
  | top =>
    exact absurd (hu' ▸ hle (H.e.val.symm y)) (by simp)
  | coe t =>
    rw [hu', ← EReal.coe_add, ← EReal.coe_sub, EReal.real_coe_toENNReal,
      ENNReal.ofReal_le_iff_le_toReal hκ'] at hgy
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- **Transfer.**  If two Harnack balls meet, a point of the first where `u ≥ -c` gives a point
of the second where `u ≥ -c'`, with `c'` independent of `u`. -/
theorem transfer (H₁ H₂ : HarnackBall θ) (h : (H₁.set ∩ H₂.set).Nonempty) (c : ℝ) :
    ∃ c' : ℝ, ∀ u : M → EReal, ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ x ∈ H₁.set, ((-c : ℝ) : EReal) ≤ u x) → ∃ x ∈ H₂.set, ((-c' : ℝ) : EReal) ≤ u x := by
  set O := H₁.e.val '' (H₁.set ∩ H₂.set)
  have hO : IsOpen O := H₁.e.val.isOpen_image_of_subset_source
    (H₁.isOpen_set.inter H₂.isOpen_set) (fun x hx => hx.1.1)
  have hOne : O.Nonempty := h.image _
  have hOsub : O ⊆ ball H₁.z H₁.r := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1.2
  obtain ⟨c', hc'⟩ := H₁.exists_point O hO hOne hOsub c
  refine ⟨c', fun u hu hle hex => ?_⟩
  obtain ⟨x, hx, hcx⟩ := hex
  obtain ⟨y, ⟨x', hx', rfl⟩, hy⟩ := hc' u hu hle ⟨H₁.e.val x, hx.2, by
    rw [H₁.e.val.left_inv hx.1]; exact hcx⟩
  rw [H₁.e.val.left_inv hx'.1.1] at hy
  exact ⟨x', hx'.2, hy⟩

end HarnackBall

/-- **Harnack balls exist** at every point of every chart, of any small radius. -/
theorem exists_harnackBall (hθ : HasSmoothLocalPotentials θ) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : HarnackBall θ, H.e = e ∧ H.z = z ∧ H.r < ε := by
  obtain ⟨W, ρ, hzW, hρ⟩ := hθ e z hz
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.mp hρ.1 z hzW
  set r : ℝ := min (R / 4) (ε / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hsub : closedBall z (3 * r) ⊆ W := fun y hy =>
    hRW (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy)
      (by have := min_le_left (R / 4) (ε / 2); linarith)))
  exact ⟨⟨e, z, r, W, ρ, hr, hρ, hsub⟩, rfl, rfl,
    lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩

/-- **The connectedness step.**  On a compact connected manifold, for every Harnack ball `H` and
level `c` there is `c'` such that every `θ`-psh `u ≤ 0` with `u ≥ -c` somewhere has a point of
`H` where `u ≥ -c'`. -/
theorem exists_forall_mem_set_le [CompactSpace M] [ConnectedSpace M]
    (hθ : HasSmoothLocalPotentials θ) (H : HarnackBall θ) (c : ℝ) :
    ∃ c' : ℝ, ∀ u : M → EReal, ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ x₀, ((-c : ℝ) : EReal) ≤ u x₀) → ∃ x ∈ H.set, ((-c' : ℝ) : EReal) ≤ u x := by
  classical
  have hex : ∀ x : M, ∃ Hx : HarnackBall θ, Hx.e = complexChartAt (n := n) x ∧
      Hx.z = (complexChartAt (n := n) x).val x ∧ Hx.r < 1 := fun x =>
    exists_harnackBall hθ _ ((complexChartAt (n := n) x).val.map_source
      (mem_complexChartAt_source x)) one_pos
  choose Hx hHxe hHxz _ using hex
  have hmem : ∀ x, x ∈ (Hx x).set := by
    intro x
    refine ⟨by rw [hHxe]; exact mem_complexChartAt_source x, ?_⟩
    rw [mem_preimage, hHxe, ← hHxz]
    exact mem_ball_self (Hx x).r_pos
  -- control near `x` gives control near `y`
  set Good : M → M → Prop := fun x y => ∀ c : ℝ, ∃ c' : ℝ, ∀ u : M → EReal,
    ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ t ∈ (Hx x).set, ((-c : ℝ) : EReal) ≤ u t) →
        ∃ t ∈ (Hx y).set, ((-c' : ℝ) : EReal) ≤ u t with hGood
  have hloc : ∀ x, ∀ᶠ y in 𝓝 x, Good x y ∧ Good y x := by
    intro x
    filter_upwards [(Hx x).isOpen_set.mem_nhds (hmem x)] with y hy
    exact ⟨fun c => HarnackBall.transfer (Hx x) (Hx y) ⟨y, hy, hmem y⟩ c,
      fun c => HarnackBall.transfer (Hx y) (Hx x) ⟨y, hmem y, hy⟩ c⟩
  have htrans : IsTrans M Good := ⟨fun a b d hab hbd c => by
    obtain ⟨c₁, h₁⟩ := hab c
    obtain ⟨c₂, h₂⟩ := hbd c₁
    exact ⟨c₂, fun u hu hle h => h₂ u hu hle (h₁ u hu hle h)⟩⟩
  have hall : ∀ x y, Good x y := PreconnectedSpace.induction₂' Good hloc htrans
  -- a finite cover by the balls `Hx x`
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (Hx x).set)
    (fun x => (Hx x).isOpen_set) (fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩)
  -- the target point and the uniform level reached near it
  set y : M := H.e.val.symm H.z
  have hyH : y ∈ H.set := H.symm_mem_set (mem_ball_self H.r_pos)
  choose cx hcx using fun x => hall x y c
  set cmax : ℝ := ∑ x ∈ s, |cx x|
  have hcmax : ∀ x ∈ s, cx x ≤ cmax := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (cx i)) hx)
  obtain ⟨c', hc'⟩ := HarnackBall.transfer (Hx y) H ⟨y, hmem y, hyH⟩ cmax
  refine ⟨c', fun u hu hle hx₀ => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hx₀
  obtain ⟨x, hxs, hx₀x⟩ := mem_iUnion₂.mp (hs (mem_univ x₀))
  obtain ⟨t, ht, hct⟩ := hcx x u hu hle ⟨x₀, hx₀x, hx₀⟩
  refine hc' u hu hle ⟨t, ht, le_trans ?_ hct⟩
  exact EReal.coe_le_coe_iff.mpr (by linarith [hcmax x hxs])

/-- **The uniform `L¹` bound on a Harnack ball**: on a compact connected manifold, `θ`-psh
functions `u ≤ 0` with `u ≥ -c` somewhere have `∫_{ball z r} (-u ∘ e⁻¹) dλ ≤ B`, one `B < ∞` for
all of them. -/
theorem HarnackBall.exists_lintegral_le [CompactSpace M] [ConnectedSpace M]
    (hθ : HasSmoothLocalPotentials θ) (H : HarnackBall θ) (c : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ u : M → EReal, ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ x₀, ((-c : ℝ) : EReal) ≤ u x₀) →
        ∫⁻ y in ball H.z H.r, (-u (H.e.val.symm y)).toENNReal ≤ B := by
  obtain ⟨c', hc'⟩ := exists_forall_mem_set_le hθ H c
  obtain ⟨A, P, hAP⟩ := H.exists_bounds
  refine ⟨volume (ball (0 : ComplexModel n) (2 * H.r)) * ENNReal.ofReal (A + c' - P),
    ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top, fun u hu hle hx₀ => ?_⟩
  obtain ⟨x, hx, hcx⟩ := hc' u hu hle hx₀
  have hz : H.e.val x ∈ ball H.z H.r := hx.2
  have hcx' : ((-c' : ℝ) : EReal) ≤ u (H.e.val.symm (H.e.val x)) := by
    rw [H.e.val.left_inv hx.1]; exact hcx
  refine le_trans ?_ (H.deficit_le hAP hu hle hz hcx')
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).mpr
    (Filter.Eventually.of_forall fun y hy => ?_))
  exact H.neg_le_deficit (fun w hw => (hAP w hw).2) u hy

theorem lintegral_biUnion_finset_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (t : ι → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ i ∈ s, t i, f a ∂μ ≤ ∑ i ∈ s, ∫⁻ a in t i, f a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

/-- **The uniform `L¹` bound on compact sets of a chart** (Guedj--Zeriahi, Prop. 8.5): on a
compact connected manifold, for every chart `e`, compact `K ⊆ e.target` and level `c` there is
`B < ∞` with `∫_K (-u ∘ e⁻¹) dλ ≤ B` for every `θ`-psh `u ≤ 0` with `u ≥ -c` somewhere. -/
theorem exists_lintegral_compact_le [CompactSpace M] [ConnectedSpace M]
    (hθ : HasSmoothLocalPotentials θ) (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) (c : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ u : M → EReal, ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ x₀, ((-c : ℝ) : EReal) ≤ u x₀) →
        ∫⁻ y in K, (-u (e.val.symm y)).toENNReal ≤ B := by
  classical
  have hex : ∀ z : K, ∃ Hz : HarnackBall θ, Hz.e = e ∧ Hz.z = z ∧ Hz.r < 1 := fun z =>
    exists_harnackBall hθ e (hKe z.2) one_pos
  choose Hz hHze hHzz _ using hex
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => ball (z : ComplexModel n) (Hz z).r)
    (fun _ => isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (Hz _).r_pos⟩)
  choose B hB hBu using fun z : K => HarnackBall.exists_lintegral_le hθ (Hz z) c
  refine ⟨∑ z ∈ t, B z, ENNReal.sum_lt_top.mpr fun z _ => hB z, fun u hu hle hx₀ => ?_⟩
  calc ∫⁻ y in K, (-u (e.val.symm y)).toENNReal
      ≤ ∫⁻ y in ⋃ z ∈ t, ball (z : ComplexModel n) (Hz z).r, (-u (e.val.symm y)).toENNReal :=
        lintegral_mono_set ht
    _ ≤ ∑ z ∈ t, ∫⁻ y in ball (z : ComplexModel n) (Hz z).r, (-u (e.val.symm y)).toENNReal :=
        lintegral_biUnion_finset_le _ _ _ _
    _ ≤ ∑ z ∈ t, B z := Finset.sum_le_sum fun z _ => by
        have := hBu z u hu hle hx₀
        rw [hHze z, hHzz z] at this
        exact this

end

end SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound
