import SGPT.NPP.Capacity2QuasiContinuity
import SGPT.NPP.CapacityConvergenceSemicon
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Envelopes.SourceRooftopContactMeasures

/-!
# Differentiability of the energy along a rooftop path

Source `lma:Ediff` (chapter `chapter_envelopes.tex`, subsection `subsec:fullmass`): let `X` be a
connected compact Kähler manifold, `θ` a closed real smooth `(1,1)`-form of big class and `ϕ`
a model potential of positive mass.  For `φ, ψ ∈ E^∞(X, θ; ϕ)` put

  `η_t = ((1-t)φ + tψ) ∧ ψ`,   `t ∈ [0,1]`.

Then `t ↦ E_θ^ϕ(η_t)` is differentiable on `[0,1]` (one-sided at the endpoints) with

  `d/dt E_θ^ϕ(η_t) = ∫_X (ψ - min{φ,ψ}) θ_{η_t}^n`.

Formalization: `ediffPath θ φ ψ t = thetaRooftop θ (convexComb t ψ φ) ψ` is the literal rooftop
(`def:rooftop`) of `(1-t)φ + tψ` and `ψ`; the energy is the source `sourceRelativeEnergy`
(`def:MAenergy`), real on `E^∞`; the theorem is `HasDerivWithinAt … (Icc 0 1) t` for every
`t ∈ [0,1]` (`hasDerivAt` at interior points).

Proof (following the source, with the route recorded by lane S30).  Write
`f_t = min((1-t)φ + tψ, ψ) = min(φ,ψ) + t χ`, `χ = ψ - min(φ,ψ) ∈ [0, C]` off the common pole
set.  The paths are increasing in `t` and `η_b ≤ η_a + (b-a)C`.  By `prop:Ediffbdd` (the
`E^∞` endpoint bounds) and `lma:rooftopMA` (`θ_{η_t}^n` lives on the contact set
`{η_t = f_t}`), for `0 ≤ a ≤ b ≤ 1`

  `(b-a) ∫χ θ_{η_b}^n ≤ E(η_b) - E(η_a) ≤ (b-a) ∫χ θ_{η_a}^n`.

The function `g(t) = ∫χ θ_{η_t}^n` is continuous on `[0,1]`: along monotone sequences this is
`thm:semicon` (second part, constant quasi-continuous weight `χ`, `ex:psh_qc`, equal full
masses), and every sequence has a monotone subsequence.  The two-sided squeeze of the slopes
then gives the derivative.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Envelopes.CapacityConsumers

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NPP SGPT.NPP.CapacityConvergence

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The path of `lma:Ediff`: `η_t = ((1-t)φ + tψ) ∧ ψ`, the source rooftop. -/
def ediffPath (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ ψ : M → EReal) (t : ℝ) :
    M → EReal :=
  thetaRooftop θ (ThetaPshConvexCombination.convexComb t ψ φ) ψ

/-- The obstacle `f_t = min((1-t)φ + tψ, ψ)`. -/
def ediffObstacle (φ ψ : M → EReal) (t : ℝ) (x : M) : EReal :=
  min (ThetaPshConvexCombination.convexComb t ψ φ x) (ψ x)

/-- The derivative weight `ψ - min{φ, ψ}` (real form; `0` on the common pole set). -/
def ediffWeight (φ ψ : M → EReal) (x : M) : ℝ :=
  (ψ x).toReal - (min (φ x) (ψ x)).toReal

/-- The coercion `ℝ → EReal` commutes with `min`. -/
theorem coe_min_ereal (a b : ℝ) : ((min a b : ℝ) : EReal) = min (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_min

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- At a point where both functions are finite, the obstacle is `min(φ,ψ) + t χ`. -/
theorem ediffObstacle_coe {φ ψ : M → EReal} {x : M} {p q : ℝ} (hp : φ x = p) (hq : ψ x = q)
    {t : ℝ} (ht1 : t ≤ 1) :
    ediffObstacle φ ψ t x = ((min p q + t * (q - min p q) : ℝ) : EReal) := by
  have hconv : ThetaPshConvexCombination.convexComb t ψ φ x = ((t * q + (1 - t) * p : ℝ) : EReal) := by
    change (t : EReal) * ψ x + ((1 - t : ℝ) : EReal) * φ x = _
    rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  rw [ediffObstacle, hconv, hq, ← coe_min_ereal]
  congr 1
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, min_eq_left (by nlinarith)]
    ring
  · rw [min_eq_right hqp, min_eq_right (by nlinarith)]
    ring

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The weight at a finite point. -/
theorem ediffWeight_coe {φ ψ : M → EReal} {x : M} {p q : ℝ} (hp : φ x = p) (hq : ψ x = q) :
    ediffWeight φ ψ x = q - min p q := by
  rw [ediffWeight, hp, hq, ← coe_min_ereal, EReal.toReal_coe, EReal.toReal_coe]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- At a pole of `ψ` the obstacle is `-∞`. -/
theorem ediffObstacle_of_bot {φ ψ : M → EReal} {x : M} (hq : ψ x = ⊥) (t : ℝ) :
    ediffObstacle φ ψ t x = ⊥ := by
  rw [ediffObstacle, hq, min_bot_right]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The canonical difference is the difference of real parts when the pole sets agree. -/
theorem canonicalERealDiffToReal_eq_toReal_sub {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hab : a = ⊥ ↔ b = ⊥) : canonicalERealDiffToReal a b = a.toReal - b.toReal := by
  by_cases ha' : a = ⊥
  · have hb' := hab.mp ha'
    simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal, ha', hb']
  · have hb' : b ≠ ⊥ := fun h => ha' (hab.mpr h)
    rw [← EReal.coe_toReal ha ha', ← EReal.coe_toReal hb hb', canonicalERealDiffToReal_coe_coe,
      EReal.toReal_coe, EReal.toReal_coe]

section Standing

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ϕ φ ψ : M → EReal}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Same singularity type gives a common real constant `C ≥ 0` and equal pole sets. -/
theorem exists_sameType_const (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, φ x ≤ ψ x + (C : EReal)) ∧ (∀ x, ψ x ≤ φ x + (C : EReal)) := by
  have h : SGPT.PSH.SingularityEquiv φ ψ := SGPT.PSH.singularityEquiv_trans hφ.2 (SGPT.PSH.singularityEquiv_symm hψ.2)
  obtain ⟨⟨C₁, hC₁⟩, ⟨C₂, hC₂⟩⟩ := h
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun x => ?_, fun x => ?_⟩
  · exact (hC₁ x (mem_univ x)).trans (add_le_add le_rfl
      (EReal.coe_le_coe_iff.mpr ((le_max_left _ _).trans (le_max_left _ _))))
  · exact (hC₂ x (mem_univ x)).trans (add_le_add le_rfl
      (EReal.coe_le_coe_iff.mpr ((le_max_right _ _).trans (le_max_left _ _))))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Mutual additive comparison forces equal pole sets. -/
theorem eq_bot_iff_of_le_add {u v : M → EReal} {C : ℝ} (h1 : ∀ x, u x ≤ v x + (C : EReal))
    (h2 : ∀ x, v x ≤ u x + (C : EReal)) (x : M) : u x = ⊥ ↔ v x = ⊥ := by
  constructor
  · intro h
    have := h2 x
    rw [h, EReal.bot_add] at this
    exact le_bot_iff.mp this
  · intro h
    have := h1 x
    rw [h, EReal.bot_add] at this
    exact le_bot_iff.mp this

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Uniform two-sided closeness gives pointwise convergence in `EReal`. -/
theorem tendsto_of_two_sided {u : ℕ → M → EReal} {v : M → EReal} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (hut : ∀ k x, u k x ≠ ⊤) (hvt : ∀ x, v x ≠ ⊤)
    (h1 : ∀ k x, u k x ≤ v x + (c k : EReal)) (h2 : ∀ k x, v x ≤ u k x + (c k : EReal))
    (x : M) : Tendsto (fun k => u k x) atTop (𝓝 (v x)) := by
  by_cases hv : v x = ⊥
  · have hu : ∀ k, u k x = ⊥ := fun k => by
      have := h1 k x
      rw [hv, EReal.bot_add] at this
      exact le_bot_iff.mp this
    simp only [hu, hv]
    exact tendsto_const_nhds
  have hu : ∀ k, u k x ≠ ⊥ := fun k hb => by
    have := h2 k x
    rw [hb, EReal.bot_add] at this
    exact hv (le_bot_iff.mp this)
  have heq : ∀ k, u k x = (((u k x).toReal : ℝ) : EReal) := fun k =>
    (EReal.coe_toReal (hut k x) (hu k)).symm
  rw [show v x = (((v x).toReal : ℝ) : EReal) from (EReal.coe_toReal (hvt x) hv).symm]
  rw [tendsto_congr heq]
  apply EReal.tendsto_coe.mpr
  have hb1 : ∀ k, (u k x).toReal ≤ (v x).toReal + c k := fun k => by
    have := h1 k x
    rw [heq k, ← EReal.coe_toReal (hvt x) hv, ← EReal.coe_add] at this
    exact EReal.coe_le_coe_iff.mp this
  have hb2 : ∀ k, (v x).toReal ≤ (u k x).toReal + c k := fun k => by
    have := h2 k x
    rw [heq k, ← EReal.coe_toReal (hvt x) hv, ← EReal.coe_add] at this
    exact EReal.coe_le_coe_iff.mp this
  have hlo : Tendsto (fun k => (v x).toReal - c k) atTop (𝓝 ((v x).toReal)) := by
    simpa using tendsto_const_nhds.sub hc
  have hhi : Tendsto (fun k => (v x).toReal + c k) atTop (𝓝 ((v x).toReal)) := by
    simpa using tendsto_const_nhds.add hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun k => by linarith [hb2 k])
    (fun k => hb1 k)

variable [ConnectedSpace M]

omit [BorelSpace M] in
/-- The path stays in `E^∞(X, θ; ϕ)` (`prop:relrooftopclosed` for `E^∞`, convexity). -/
theorem ediffPath_mem (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    SourceRelativeEInfinity θ ϕ (ediffPath θ φ ψ t) :=
  sourceRelativeEInfinity_rooftop hϕ (sourceRelativeEInfinity_convexComb hψ hφ ht.1 ht.2) hψ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The rooftop lies below the obstacle `min(·, ψ)`. -/
theorem ediffPath_le_obstacle (t : ℝ) (x : M) :
    ediffPath θ φ ψ t x ≤ ediffObstacle φ ψ t x :=
  le_min (thetaRooftop_le_left θ _ _ x) (thetaRooftop_le_right θ _ _ x)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Every `θ`-psh minorant of the obstacle lies below the path. -/
theorem le_ediffPath_of_le_obstacle {h : M → EReal} (hh : (ofFixedModel n M).IsThetaPSH θ h)
    {t : ℝ} (hle : ∀ x, h x ≤ ediffObstacle φ ψ t x) : h ≤ ediffPath θ φ ψ t :=
  le_thetaRooftop hh (fun x => (hle x).trans (min_le_left _ _))
    (fun x => (hle x).trans (min_le_right _ _))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Monotonicity and Lipschitz bound of the obstacle in `t`. -/
theorem ediffObstacle_bounds {C : ℝ} (hC : 0 ≤ C) (hφt : ∀ x, φ x ≠ ⊤) (hψt : ∀ x, ψ x ≠ ⊤)
    (hpole : ∀ x, φ x = ⊥ ↔ ψ x = ⊥) (hψφ : ∀ x, ψ x ≤ φ x + (C : EReal))
    {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (x : M) :
    ediffObstacle φ ψ a x ≤ ediffObstacle φ ψ b x ∧
      ediffObstacle φ ψ b x ≤ ediffObstacle φ ψ a x + (((b - a) * C : ℝ) : EReal) := by
  by_cases hq : ψ x = ⊥
  · simp only [ediffObstacle_of_bot hq, le_refl, EReal.bot_add, and_self]
  have hp : φ x ≠ ⊥ := fun h => hq ((hpole x).mp h)
  set p := (φ x).toReal
  set q := (ψ x).toReal
  have hpx : φ x = (p : EReal) := (EReal.coe_toReal (hφt x) hp).symm
  have hqx : ψ x = (q : EReal) := (EReal.coe_toReal (hψt x) hq).symm
  rw [ediffObstacle_coe hpx hqx (hab.trans hb),
    ediffObstacle_coe hpx hqx hb, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
  have hqp : q ≤ p + C := by
    have := hψφ x
    rw [hpx, hqx, ← EReal.coe_add] at this
    exact EReal.coe_le_coe_iff.mp this
  have hχ0 : 0 ≤ q - min p q := sub_nonneg.mpr (min_le_right _ _)
  have hχC : q - min p q ≤ C := by
    rcases le_total p q with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  constructor
  · nlinarith
  · nlinarith

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- A source `θ`-psh function is Borel. -/
theorem measurable_of_isThetaPSH [MeasurableSpace M] [BorelSpace M] {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : Measurable u :=
  ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1.quasiPlurisubharmonic.upperSemicontinuous.measurable

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The weight is Borel. -/
theorem measurable_ediffWeight (hφm : Measurable φ) (hψm : Measurable ψ) :
    Measurable (ediffWeight φ ψ) :=
  hψm.ereal_toReal.sub (hφm.min hψm).ereal_toReal

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The weight takes values in `[0, C]`. -/
theorem ediffWeight_mem {C : ℝ} (hC : 0 ≤ C) (hφt : ∀ x, φ x ≠ ⊤) (hψt : ∀ x, ψ x ≠ ⊤)
    (hpole : ∀ x, φ x = ⊥ ↔ ψ x = ⊥) (hψφ : ∀ x, ψ x ≤ φ x + (C : EReal)) (x : M) :
    0 ≤ ediffWeight φ ψ x ∧ ediffWeight φ ψ x ≤ C := by
  by_cases hq : ψ x = ⊥
  · have hp := (hpole x).mpr hq
    simp [ediffWeight, hp, hq, hC]
  have hp : φ x ≠ ⊥ := fun h => hq ((hpole x).mp h)
  have hpx : φ x = ((φ x).toReal : EReal) := (EReal.coe_toReal (hφt x) hp).symm
  have hqx : ψ x = ((ψ x).toReal : EReal) := (EReal.coe_toReal (hψt x) hq).symm
  rw [ediffWeight_coe hpx hqx]
  have hqp : (ψ x).toReal ≤ (φ x).toReal + C := by
    have := hψφ x
    rw [hpx, hqx, ← EReal.coe_add] at this
    exact EReal.coe_le_coe_iff.mp this
  refine ⟨sub_nonneg.mpr (min_le_right _ _), ?_⟩
  rcases le_total (φ x).toReal (ψ x).toReal with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

omit [BorelSpace M] in
/-- Two-sided comparison of the path: for `0 ≤ a ≤ b ≤ 1`,
`η_a ≤ η_b ≤ η_a + (b-a) C`. -/
theorem ediffPath_bounds (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {C : ℝ} (hC : 0 ≤ C)
    (hφψ : ∀ x, φ x ≤ ψ x + (C : EReal)) (hψφ : ∀ x, ψ x ≤ φ x + (C : EReal))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∀ x, ediffPath θ φ ψ a x ≤ ediffPath θ φ ψ b x) ∧
      ∀ x, ediffPath θ φ ψ b x ≤ ediffPath θ φ ψ a x + (((b - a) * C : ℝ) : EReal) := by
  have hpole := eq_bot_iff_of_le_add hφψ hψφ
  have hob := ediffObstacle_bounds hC hφ.1.1 hψ.1.1 hpole hψφ ha hab hb
  have hA := ediffPath_mem hϕ hφ hψ ⟨ha, hab.trans hb⟩
  have hB := ediffPath_mem hϕ hφ hψ ⟨ha.trans hab, hb⟩
  refine ⟨le_ediffPath_of_le_obstacle hA.1 fun x =>
    (ediffPath_le_obstacle a x).trans (hob x).1, ?_⟩
  set c : ℝ := (b - a) * C
  have hsub : (ofFixedModel n M).IsThetaPSH θ (fun x => ediffPath θ φ ψ b x - (c : EReal)) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (((isThetaPSH_iff_nativeThetaPotential θ _).mp hB.1).sub_const c)
  have hle := le_ediffPath_of_le_obstacle hsub (t := a) fun x => by
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).mpr
    exact (ediffPath_le_obstacle b x).trans (hob x).2
  intro x
  exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c))
    (Or.inl (EReal.coe_ne_top c))).mp (hle x)

omit [BorelSpace M] in
/-- Real form of the path increments: equal pole sets, and
`0 ≤ η_b - η_a ≤ (b-a) C` for the real parts, which is also the canonical difference. -/
theorem ediffPath_increment (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {C : ℝ} (hC : 0 ≤ C)
    (hφψ : ∀ x, φ x ≤ ψ x + (C : EReal)) (hψφ : ∀ x, ψ x ≤ φ x + (C : EReal))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (x : M) :
    canonicalERealDiffToReal (ediffPath θ φ ψ b x) (ediffPath θ φ ψ a x) =
        (ediffPath θ φ ψ b x).toReal - (ediffPath θ φ ψ a x).toReal ∧
      0 ≤ (ediffPath θ φ ψ b x).toReal - (ediffPath θ φ ψ a x).toReal ∧
      (ediffPath θ φ ψ b x).toReal - (ediffPath θ φ ψ a x).toReal ≤ (b - a) * C := by
  obtain ⟨h1, h2⟩ := ediffPath_bounds hϕ hφ hψ hC hφψ hψφ ha hab hb
  have hA := ediffPath_mem hϕ hφ hψ ⟨ha, hab.trans hb⟩
  have hB := ediffPath_mem hϕ hφ hψ ⟨ha.trans hab, hb⟩
  have hpole : ediffPath θ φ ψ b x = ⊥ ↔ ediffPath θ φ ψ a x = ⊥ := by
    constructor
    · intro h; exact le_bot_iff.mp (h ▸ h1 x)
    · intro h
      have := h2 x
      rw [h, EReal.bot_add] at this
      exact le_bot_iff.mp this
  refine ⟨canonicalERealDiffToReal_eq_toReal_sub (hB.1.1 x) (hA.1.1 x) hpole, ?_⟩
  by_cases ha' : ediffPath θ φ ψ a x = ⊥
  · have hb' := hpole.mpr ha'
    simp only [ha', hb', EReal.toReal_bot, sub_self, le_refl, true_and]
    exact mul_nonneg (sub_nonneg.mpr hab) hC
  have hb' : ediffPath θ φ ψ b x ≠ ⊥ := fun h => ha' (hpole.mp h)
  have hax := (EReal.coe_toReal (hA.1.1 x) ha').symm
  have hbx := (EReal.coe_toReal (hB.1.1 x) hb').symm
  have e1 := h1 x
  have e2 := h2 x
  rw [hax, hbx, EReal.coe_le_coe_iff] at e1
  rw [hax, hbx, ← EReal.coe_add, EReal.coe_le_coe_iff] at e2
  constructor <;> linarith

omit [ConnectedSpace M] in
/-- Poles of any source `θ`-psh function are null for a source non-pluripolar measure. -/
theorem ae_ne_bot_of_isThetaPSH {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ u hu, v x ≠ ⊥ := by
  apply ae_iff.mpr
  simpa only [not_not, sourceMixedNonPluripolarMeasure_diagonal] using
    sourceMixedNonPluripolarMeasure_pole_null (fun _ : Fin n => hu) hv

/-- `lma:rooftopMA`: `θ_{η_t}^n`-almost everywhere the path touches its obstacle. -/
theorem ae_ediffPath_eq_obstacle (ω : KahlerBackground n M) (hϕ : SourceModelPotential θ ϕ)
    (hφ : SourceRelativeEInfinity θ ϕ φ) (hψ : SourceRelativeEInfinity θ ϕ ψ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ (ediffPath θ φ ψ t)
        (ediffPath_mem hϕ hφ hψ ht).1,
      ediffPath θ φ ψ t x = ediffObstacle φ ψ t x := by
  have hconv := sourceRelativeEInfinity_convexComb hψ hφ ht.1 ht.2
  have h := sourceThetaRooftop_noncontact_null ω hconv.1 hψ.1 (ediffPath_mem hϕ hφ hψ ht).1
  have hae : ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ (ediffPath θ φ ψ t)
      (ediffPath_mem hϕ hφ hψ ht).1,
      ediffPath θ φ ψ t x = ThetaPshConvexCombination.convexComb t ψ φ x ∨
        ediffPath θ φ ψ t x = ψ x := by
    refine ae_iff.mpr (le_antisymm (le_trans (measure_mono ?_) h.le) zero_le)
    intro x hx
    simp only [Set.mem_ofPred_eq, not_or] at hx
    exact hx
  filter_upwards [hae] with x hx
  apply le_antisymm (ediffPath_le_obstacle t x)
  rcases hx with h | h
  · rw [h]; exact min_le_left _ _
  · rw [h]; exact min_le_right _ _

/-- **The energy sandwich.**  For `0 ≤ a ≤ b ≤ 1`,
`(b-a) ∫χ θ_{η_b}^n ≤ E(η_b) - E(η_a) ≤ (b-a) ∫χ θ_{η_a}^n`, `χ = ψ - min(φ,ψ)`. -/
theorem ediff_energy_sandwich (ω : KahlerBackground n M) (hϕ : SourceModelPotential θ ϕ)
    (hφ : SourceRelativeEInfinity θ ϕ φ) (hψ : SourceRelativeEInfinity θ ϕ ψ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * ∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
        (ediffPath θ φ ψ b) (ediffPath_mem hϕ hφ hψ ⟨ha.trans hab, hb⟩).1 ≤
      (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ b) hϕ).toReal -
        (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ a) hϕ).toReal ∧
    (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ b) hϕ).toReal -
        (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ a) hϕ).toReal ≤
      (b - a) * ∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
        (ediffPath θ φ ψ a) (ediffPath_mem hϕ hφ hψ ⟨ha, hab.trans hb⟩).1 := by
  obtain ⟨C, hC, hφψ, hψφ⟩ := exists_sameType_const hφ hψ
  have hpole := eq_bot_iff_of_le_add hφψ hψφ
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have hA := ediffPath_mem hϕ hφ hψ haI
  have hB := ediffPath_mem hϕ hφ hψ hbI
  set μa := sourcePotentialNonPluripolarMeasure θ (ediffPath θ φ ψ a) hA.1
  set μb := sourcePotentialNonPluripolarMeasure θ (ediffPath θ φ ψ b) hB.1
  have : IsFiniteMeasure μa := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure ω
    (fun _ : Fin n => ((isThetaPSH_iff_nativeThetaPotential θ _).mp hA.1).1)
  have : IsFiniteMeasure μb := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure ω
    (fun _ : Fin n => ((isThetaPSH_iff_nativeThetaPotential θ _).mp hB.1).1)
  have hEa : (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ a) hϕ).toReal =
      sourceRelativeEnergyOfMinimalType θ ϕ (ediffPath θ φ ψ a) hϕ.thetaPSH hA.1 := by
    rw [sourceRelativeEnergy_eq_of_eInfinity ω hA, EReal.toReal_coe]
  have hEb : (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ b) hϕ).toReal =
      sourceRelativeEnergyOfMinimalType θ ϕ (ediffPath θ φ ψ b) hϕ.thetaPSH hB.1 := by
    rw [sourceRelativeEnergy_eq_of_eInfinity ω hB, EReal.toReal_coe]
  obtain ⟨hlow, hupp⟩ := sourceRelativeEnergy_endpoint_bounds ω hϕ hB hA
  have hinc := ediffPath_increment hϕ hφ hψ hC hφψ hψφ ha hab hb
  have hcanon : (fun x => canonicalERealDiffToReal (ediffPath θ φ ψ b x) (ediffPath θ φ ψ a x)) =
      fun x => (ediffPath θ φ ψ b x).toReal - (ediffPath θ φ ψ a x).toReal :=
    funext fun x => (hinc x).1
  rw [hcanon] at hlow hupp
  rw [hEa, hEb]
  have hDm : Measurable fun x => (ediffPath θ φ ψ b x).toReal - (ediffPath θ φ ψ a x).toReal :=
    (measurable_of_isThetaPSH hB.1).ereal_toReal.sub (measurable_of_isThetaPSH hA.1).ereal_toReal
  have hχm : Measurable (ediffWeight φ ψ) :=
    measurable_ediffWeight (measurable_of_isThetaPSH hφ.1) (measurable_of_isThetaPSH hψ.1)
  have hχb := ediffWeight_mem hC hφ.1.1 hψ.1.1 hpole hψφ
  have hDint : ∀ μ : Measure M, IsFiniteMeasure μ →
      Integrable (fun x => (ediffPath θ φ ψ b x).toReal - (ediffPath θ φ ψ a x).toReal) μ :=
    fun μ _ => Integrable.of_bound hDm.aestronglyMeasurable ((b - a) * C)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hinc x).2.1]; exact (hinc x).2.2)
  have hχint : ∀ μ : Measure M, IsFiniteMeasure μ → Integrable (ediffWeight φ ψ) μ :=
    fun μ _ => Integrable.of_bound hχm.aestronglyMeasurable C
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχb x).1]; exact (hχb x).2)
  -- pointwise values at a finite point
  have hval : ∀ x, φ x ≠ ⊥ → ψ x ≠ ⊥ → ∀ s, s ≤ 1 →
      ediffObstacle φ ψ s x = (((min (φ x).toReal (ψ x).toReal) + s * ediffWeight φ ψ x : ℝ) :
        EReal) := by
    intro x hp hq s hs
    have hpx : φ x = ((φ x).toReal : EReal) := (EReal.coe_toReal (hφ.1.1 x) hp).symm
    have hqx : ψ x = ((ψ x).toReal : EReal) := (EReal.coe_toReal (hψ.1.1 x) hq).symm
    rw [ediffObstacle_coe hpx hqx hs, ediffWeight_coe hpx hqx]
  constructor
  · -- lower bound against `μb`
    refine le_trans ?_ hlow
    rw [← integral_const_mul]
    refine integral_mono_ae ((hχint μb inferInstance).const_mul _) (hDint μb inferInstance) ?_
    filter_upwards [ae_ne_bot_of_isThetaPSH hB.1 hφ.1, ae_ne_bot_of_isThetaPSH hB.1 hψ.1,
      ae_ne_bot_of_isThetaPSH hB.1 hA.1, ae_ediffPath_eq_obstacle ω hϕ hφ hψ hbI]
      with x hp hq hax hbx
    have hbv : ediffPath θ φ ψ b x =
        (((min (φ x).toReal (ψ x).toReal) + b * ediffWeight φ ψ x : ℝ) : EReal) := by
      rw [hbx, hval x hp hq b hb]
    have hav : (ediffPath θ φ ψ a x).toReal ≤
        (min (φ x).toReal (ψ x).toReal) + a * ediffWeight φ ψ x := by
      have h := ediffPath_le_obstacle (θ := θ) (φ := φ) (ψ := ψ) a x
      rw [hval x hp hq a (hab.trans hb)] at h
      have := EReal.toReal_le_toReal h hax (EReal.coe_ne_top _)
      rwa [EReal.toReal_coe] at this
    rw [hbv, EReal.toReal_coe]
    nlinarith
  · -- upper bound against `μa`
    refine le_trans hupp ?_
    rw [← integral_const_mul]
    refine integral_mono_ae (hDint μa inferInstance) ((hχint μa inferInstance).const_mul _) ?_
    filter_upwards [ae_ne_bot_of_isThetaPSH hA.1 hφ.1, ae_ne_bot_of_isThetaPSH hA.1 hψ.1,
      ae_ediffPath_eq_obstacle ω hϕ hφ hψ haI] with x hp hq hax
    have hav : ediffPath θ φ ψ a x =
        (((min (φ x).toReal (ψ x).toReal) + a * ediffWeight φ ψ x : ℝ) : EReal) := by
      rw [hax, hval x hp hq a (hab.trans hb)]
    have hbne : ediffPath θ φ ψ b x ≠ ⊥ := by
      intro h
      have h1 := (ediffPath_bounds hϕ hφ hψ hC hφψ hψφ ha hab hb).1 x
      rw [h, hav] at h1
      exact EReal.coe_ne_bot _ (le_bot_iff.mp h1)
    have hbv : (ediffPath θ φ ψ b x).toReal ≤
        (min (φ x).toReal (ψ x).toReal) + b * ediffWeight φ ψ x := by
      have h := ediffPath_le_obstacle (θ := θ) (φ := φ) (ψ := ψ) b x
      rw [hval x hp hq b hb] at h
      have := EReal.toReal_le_toReal h hbne (EReal.coe_ne_top _)
      rwa [EReal.toReal_coe] at this
    rw [hav, EReal.toReal_coe]
    nlinarith

omit [ConnectedSpace M] in
/-- The weight `ψ - min(φ,ψ)` is quasi-continuous for `Cap_θ` (`ex:psh_qc`). -/
theorem sourceQuasiContinuousOn_ediffWeight (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ) :
    SourceQuasiContinuousOn θ ⊤ (fun x => (ediffWeight φ ψ x.1 : EReal)) := by
  have hqφ := ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).quasiPshPotential
  have hqψ := ((isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ).quasiPshPotential
  have hχm := measurable_ediffWeight (measurable_of_isThetaPSH hφ) (measurable_of_isThetaPSH hψ)
  refine sourceQuasiContinuousOn_of_forall θ ⊤
    ((measurable_coe_real_ereal.comp hχm).comp measurable_subtype_coe) fun ε hε => ?_
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ :=
    exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hqφ (half_pos hε)
  obtain ⟨H, hHo, hHc, hHf, hHcont⟩ :=
    exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hqψ (half_pos hε)
  refine ⟨G ∪ H, hGo.union hHo, ?_, ediffWeight φ ψ, ?_, fun x _ => rfl⟩
  · calc sourceThetaCapacity θ (G ∪ H)
        ≤ sourceThetaCapacity θ G + sourceThetaCapacity θ H := sourceThetaCapacity_union_le θ G H
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hGc hHc
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  · have hc : ContinuousOn (fun x => (ψ x).toReal - min (φ x).toReal (ψ x).toReal) (G ∪ H)ᶜ :=
      (hHcont.mono (compl_subset_compl.mpr subset_union_right)).sub
        ((hGcont.mono (compl_subset_compl.mpr subset_union_left)).inf
          (hHcont.mono (compl_subset_compl.mpr subset_union_right)))
    refine hc.congr fun x hx => ?_
    have hp := hGf x fun h => hx (Or.inl h)
    have hq := hHf x fun h => hx (Or.inr h)
    exact ediffWeight_coe (EReal.coe_toReal (hφ.1 x) hp).symm (EReal.coe_toReal (hψ.1 x) hq).symm

omit [BorelSpace M] [ConnectedSpace M] in
/-- A constant sequence converges in capacity to itself. -/
theorem sourceTendstoInCapacity_const_real (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {w : M → ℝ} (hw : Measurable w) :
    SourceTendstoInCapacity θc ⊤ (fun (_ : ℕ) (x : (⊤ : Opens M)) => (w x.1 : EReal)) atTop
      (fun x => (w x.1 : EReal)) := by
  have hm : Measurable fun x : (⊤ : Opens M) => (w x.1 : EReal) :=
    (measurable_coe_real_ereal.comp hw).comp measurable_subtype_coe
  refine ⟨fun _ => hm, hm, fun δ hδ => ⟨?_, ?_⟩⟩
  · simp only [sourceCapacityUpperGap_self _ _ hδ.le, sourceThetaCapacity_empty]
    exact tendsto_const_nhds
  · simp only [sourceCapacityLowerGap_self _ _ hδ.le, sourceThetaCapacity_empty]
    exact tendsto_const_nhds

omit [BorelSpace M] in
/-- Two-sided closeness of two points of the path, in either order. -/
theorem ediffPath_close (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {C : ℝ} (hC : 0 ≤ C)
    (hφψ : ∀ x, φ x ≤ ψ x + (C : EReal)) (hψφ : ∀ x, ψ x ≤ φ x + (C : EReal))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (x : M) :
    ediffPath θ φ ψ a x ≤ ediffPath θ φ ψ b x + ((|b - a| * C : ℝ) : EReal) ∧
      ediffPath θ φ ψ b x ≤ ediffPath θ φ ψ a x + ((|b - a| * C : ℝ) : EReal) := by
  have hc0 : 0 ≤ |b - a| * C := mul_nonneg (abs_nonneg _) hC
  have hpos : ∀ u : EReal, u ≤ u + ((|b - a| * C : ℝ) : EReal) := fun u =>
    le_add_of_nonneg_right (EReal.coe_nonneg.mpr hc0)
  rcases le_total a b with hab | hba
  · obtain ⟨h1, h2⟩ := ediffPath_bounds hϕ hφ hψ hC hφψ hψφ ha.1 hab hb.2
    refine ⟨(h1 x).trans (hpos _), (h2 x).trans (add_le_add le_rfl ?_)⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  · obtain ⟨h1, h2⟩ := ediffPath_bounds hϕ hφ hψ hC hφψ hψφ hb.1 hba ha.2
    refine ⟨(h2 x).trans (add_le_add le_rfl ?_), (h1 x).trans (hpos _)⟩
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hba)]

/-- **Continuity along monotone sequences** (`thm:semicon`, second part): if `s_k ∈ [0,1]` is
monotone with limit `t`, then `∫ χ θ_{η_{s_k}}^n → ∫ χ θ_{η_t}^n`. -/
theorem tendsto_ediffWeight_integral_of_monotone (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {s : ℕ → ℝ} {t : ℝ} (hs : ∀ k, s k ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hlim : Tendsto s atTop (𝓝 t)) (hmono : Monotone s ∨ Antitone s) :
    Tendsto (fun k => ∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
        (ediffPath θ φ ψ (s k)) (ediffPath_mem hϕ hφ hψ (hs k)).1) atTop
      (𝓝 (∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
        (ediffPath θ φ ψ t) (ediffPath_mem hϕ hφ hψ ht).1)) := by
  obtain ⟨C, hC, hφψ, hψφ⟩ := exists_sameType_const hφ hψ
  have hpole := eq_bot_iff_of_le_add hφψ hψφ
  have hmem := fun k => ediffPath_mem hϕ hφ hψ (hs k)
  have hmt := ediffPath_mem hϕ hφ hψ ht
  have hclose := fun k x => ediffPath_close hϕ hφ hψ hC hφψ hψφ ht (hs k) x
  have hc : Tendsto (fun k => |s k - t| * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => |s k - t|) atTop (𝓝 0) := by
      have := (hlim.sub_const t).abs
      simpa using this
    simpa using h1.mul_const C
  have hpt : ∀ x, Tendsto (fun k => ediffPath θ φ ψ (s k) x) atTop (𝓝 (ediffPath θ φ ψ t x)) :=
    tendsto_of_two_sided hc (fun k x => (hmem k).1.1 x) (fun x => hmt.1.1 x)
      (fun k x => (hclose k x).2) (fun k x => (hclose k x).1)
  have hslot : SourceMonotoneLimit (n := n) (fun k => ediffPath θ φ ψ (s k))
      (ediffPath θ φ ψ t) := by
    rcases hmono with hm | ha
    · right
      refine ⟨fun x k l hkl => ?_, fun e => ae_of_all _ fun z => hpt _⟩
      exact (ediffPath_bounds hϕ hφ hψ hC hφψ hψφ (hs k).1 (hm hkl) (hs l).2).1 x
    · left
      refine ⟨fun x k l hkl => ?_, hpt⟩
      exact (ediffPath_bounds hϕ hφ hψ hC hφψ hψφ (hs l).1 (ha hkl) (hs k).2).1 x
  have hχm := measurable_ediffWeight (measurable_of_isThetaPSH hφ.1) (measurable_of_isThetaPSH hψ.1)
  have hχb := ediffWeight_mem hC hφ.1.1 hψ.1.1 hpole hψφ
  have hqc := sourceQuasiContinuousOn_ediffWeight ω hbig hφ.1 hψ.1
  have hmass : ∀ k, sourceMixedNonPluripolarMass (fun _ : Fin n => θ)
      (fun _ => ediffPath θ φ ψ (s k)) (fun _ => (hmem k).1) =
      sourceMixedNonPluripolarMass (fun _ : Fin n => θ) (fun _ => ediffPath θ φ ψ t)
        (fun _ => hmt.1) := by
    intro k
    apply le_antisymm
    · exact sourceMixedNonPluripolarMass_mono ω _ _
        (fun _ => ⟨|s k - t| * C, fun x _ => (hclose k x).2⟩)
    · exact sourceMixedNonPluripolarMass_mono ω _ _
        (fun _ => ⟨|s k - t| * C, fun x _ => (hclose k x).1⟩)
  have h := sourceSemicon_tendsto_integral ω θ hbig (fun _ : Fin n => θ)
    (φ := fun k _ => ediffPath θ φ ψ (s k)) (φ₀ := fun _ => ediffPath θ φ ψ t)
    (fun k _ => (hmem k).1) (fun _ => hmt.1) (fun _ => hslot)
    (χ := fun _ => ediffWeight φ ψ) (χ₀ := ediffWeight φ ψ) (C := C)
    (fun _ x => hχb x) hχb (fun _ => hqc) hqc (sourceTendstoInCapacity_const_real θ hχm)
    (by simp only [hmass]; exact tendsto_const_nhds) (ContinuousMap.const M 1)
  simp only [ContinuousMap.const_apply, one_mul] at h
  exact h

/-- The derivative weight `t ↦ ∫ χ θ_{η_t}^n`, extended by `0` outside `[0,1]`. -/
def ediffSlopeWeight (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) (s : ℝ) : ℝ :=
  if h : s ∈ Icc (0 : ℝ) 1 then
    ∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ (ediffPath θ φ ψ s)
      (ediffPath_mem hϕ hφ hψ h).1
  else 0

/-- **Continuity of `t ↦ ∫ χ θ_{η_t}^n` on `[0,1]`**: every sequence has a monotone
subsequence, along which `thm:semicon` applies. -/
theorem tendsto_ediffSlopeWeight (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (ediffSlopeWeight hϕ hφ hψ) (𝓝[Icc (0 : ℝ) 1] t)
      (𝓝 (ediffSlopeWeight hϕ hφ hψ t)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hns' : Tendsto ns atTop (𝓝 t) := hns.mono_right nhdsWithin_le_nhds
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_nhdsWithin_iff.mp hns).2
  obtain ⟨g, hg⟩ := exists_increasing_or_nonincreasing_subseq (· ≤ ·) (fun k => ns (N + k))
  refine ⟨fun k => N + g k, ?_⟩
  have hsubI : ∀ k, ns (N + g k) ∈ Icc (0 : ℝ) 1 := fun k => hN _ (Nat.le_add_right _ _)
  have hsublim : Tendsto (fun k => ns (N + g k)) atTop (𝓝 t) :=
    hns'.comp (tendsto_atTop_mono (fun k => Nat.le_add_left (g k) N) g.strictMono.tendsto_atTop)
  have hmono : Monotone (fun k => ns (N + g k)) ∨ Antitone (fun k => ns (N + g k)) := by
    rcases hg with h | h
    · exact Or.inl (monotone_nat_of_le_succ fun k => h k (k + 1) (Nat.lt_succ_self k))
    · exact Or.inr (antitone_nat_of_succ_le fun k =>
        le_of_lt (not_le.mp (h k (k + 1) (Nat.lt_succ_self k))))
  have h := tendsto_ediffWeight_integral_of_monotone ω hbig hϕ hφ hψ hsubI ht hsublim hmono
  have heq : ∀ k, ediffSlopeWeight hϕ hφ hψ (ns (N + g k)) =
      ∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
        (ediffPath θ φ ψ (ns (N + g k))) (ediffPath_mem hϕ hφ hψ (hsubI k)).1 := fun k =>
    dif_pos (hsubI k)
  rw [show ediffSlopeWeight hϕ hφ hψ t = _ from dif_pos ht]
  exact (tendsto_congr heq).mpr h

/-- **Source `lma:Ediff`.**  For `φ, ψ ∈ E^∞(X, θ; ϕ)` and `η_t = ((1-t)φ + tψ) ∧ ψ`, the
energy `t ↦ E_θ^ϕ(η_t)` has, at every `t ∈ [0,1]`, derivative within `[0,1]` (one-sided at
the endpoints) equal to `∫_X (ψ - min{φ, ψ}) θ_{η_t}^n`. -/
theorem sourceEnergy_ediffPath_hasDerivWithinAt (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ s) hϕ).toReal)
      (∫ x, ((ψ x).toReal - (min (φ x) (ψ x)).toReal) ∂sourcePotentialNonPluripolarMeasure θ
        (ediffPath θ φ ψ t) (ediffPath_mem hϕ hφ hψ ht).1) (Icc (0 : ℝ) 1) t := by
  set E : ℝ → ℝ := fun s => (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ s) hϕ).toReal
  set G := ediffSlopeWeight hϕ hφ hψ
  have hGt : G t = ∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
      (ediffPath θ φ ψ t) (ediffPath_mem hϕ hφ hψ ht).1 := dif_pos ht
  change HasDerivWithinAt E (∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
      (ediffPath θ φ ψ t) (ediffPath_mem hϕ hφ hψ ht).1) (Icc (0 : ℝ) 1) t
  rw [← hGt, hasDerivWithinAt_iff_tendsto_slope]
  have hcont : Tendsto G (𝓝[Icc (0 : ℝ) 1 \ {t}] t) (𝓝 (G t)) :=
    (tendsto_ediffSlopeWeight ω hbig hϕ hφ hψ ht).mono_left (nhdsWithin_mono _ sdiff_subset)
  rw [tendsto_iff_dist_tendsto_zero] at hcont ⊢
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hcont
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsI : s ∈ Icc (0 : ℝ) 1 := hs.1
  have hGs : G s = ∫ x, ediffWeight φ ψ x ∂sourcePotentialNonPluripolarMeasure θ
      (ediffPath θ φ ψ s) (ediffPath_mem hϕ hφ hψ hsI).1 := dif_pos hsI
  rw [slope_def_field, Real.dist_eq, Real.dist_eq]
  rcases lt_or_gt_of_ne (show s ≠ t from hs.2) with hst | hts
  · obtain ⟨h1, h2⟩ := ediff_energy_sandwich ω hϕ hφ hψ hsI.1 hst.le ht.2
    rw [← hGt] at h1
    rw [← hGs] at h2
    have hd : 0 < t - s := sub_pos.mpr hst
    have hq : (E s - E t) / (s - t) = (E t - E s) / (t - s) := by
      rw [← neg_sub (E t), ← neg_sub t, neg_div_neg_eq]
    rw [hq]
    have hlo : G t ≤ (E t - E s) / (t - s) := by
      rw [le_div_iff₀ hd]; linarith
    have hhi : (E t - E s) / (t - s) ≤ G s := by
      rw [div_le_iff₀ hd]; linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonneg (sub_nonneg.mpr (hlo.trans hhi))]
    linarith
  · obtain ⟨h1, h2⟩ := ediff_energy_sandwich ω hϕ hφ hψ ht.1 hts.le hsI.2
    rw [← hGs] at h1
    rw [← hGt] at h2
    have hd : 0 < s - t := sub_pos.mpr hts
    have hlo : G s ≤ (E s - E t) / (s - t) := by
      rw [le_div_iff₀ hd]; linarith
    have hhi : (E s - E t) / (s - t) ≤ G t := by
      rw [div_le_iff₀ hd]; linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hhi), abs_of_nonpos (sub_nonpos.mpr (hlo.trans hhi))]
    linarith

/-- At interior points the derivative of `lma:Ediff` is a genuine two-sided derivative. -/
theorem sourceEnergy_ediffPath_hasDerivAt (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => (sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ s) hϕ).toReal)
      (∫ x, ((ψ x).toReal - (min (φ x) (ψ x)).toReal) ∂sourcePotentialNonPluripolarMeasure θ
        (ediffPath θ φ ψ t) (ediffPath_mem hϕ hφ hψ (Ioo_subset_Icc_self ht)).1) t :=
  (sourceEnergy_ediffPath_hasDerivWithinAt ω hbig hϕ hφ hψ (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- On the path the source energy is finite (the formula `eq:Edefbdd` of `E^∞`). -/
theorem sourceRelativeEnergy_ediffPath_coe (ω : KahlerBackground n M)
    (hϕ : SourceModelPotential θ ϕ) (hφ : SourceRelativeEInfinity θ ϕ φ)
    (hψ : SourceRelativeEInfinity θ ϕ ψ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ t) hϕ =
      (((sourceRelativeEnergy θ ϕ (ediffPath θ φ ψ t) hϕ).toReal : ℝ) : EReal) := by
  rw [sourceRelativeEnergy_eq_of_eInfinity ω (ediffPath_mem hϕ hφ hψ ht), EReal.toReal_coe]

end Standing

end SGPT.Envelopes.CapacityConsumers
