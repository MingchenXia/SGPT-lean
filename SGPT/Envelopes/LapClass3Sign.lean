import SGPT.Envelopes.LapClass3Contact

/-!
# On the contact set the density of `θ_fⁿ` is nonnegative

Lane CZ-LP (`claude-cz-lp`, node `czlp:sign`).  `θ_fⁿ = lapTopMeasure θ f` is the positive part of the
signed measure `(θ + ddᶜf)ⁿ` (as `DNTC11.c11TopMeasure`).  On the contact set `E = {φ = f}` of
`thm:DNTcontact` the signed density is nonnegative almost everywhere
(`ae_hessDensity_nonneg_on_contact`), so there `θ_fⁿ` is the signed measure itself and the identity
`𝟙_E θ_φⁿ = 𝟙_E θ_fⁿ` is the book's.

*Proof.*  With `g = P_{θ + Aω}(f)` as in `diagonalPotentialMeasure_restrict_contact_eq`, the densities of
`f` and `g` agree almost everywhere on `{g = f} ⊇ E` (`ae_density_eq_of_le`).  In a chart, with a
local potential `ψ` of `θ`, `V = max(φ ∘ e⁻¹ + ψ, -c)` is a bounded plurisubharmonic function below
`q = g ∘ e⁻¹ + ψ`, with `V = q` on `e(E)`; the densities of the mollified `V` are nonnegative and
converge on the contact set to that of `q` (`DNTC11.ae_tendsto_smoothDensity_mollified_contact`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp SGPT.Envelopes.DNTC11
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg

/-- **Contact sets of a bounded psh function and an obstacle with bounded density**: the density of
the obstacle has nonnegative determinant almost everywhere on the contact set. -/
theorem ae_hessDensity_nonneg_of_contact {n : ℕ} (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {V q : ComplexModel n → ℝ} {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hV : IsLocallyBoundedPshOn Ω V) (hq : IsBoundedHessianDensityOn q H Ω)
    (hVq : ∀ z ∈ Ω, V z ≤ q z) :
    ∀ᵐ z, z ∈ Ω → V z = q z → 0 ≤ hessDensity H z := by
  refine IsHessianDensityOn.ae_of_forall_ball (U := (Ω : Set (ComplexModel n))) Ω.isOpen
    fun z₀ _ R hR hball => ?_
  have hlim := ae_tendsto_smoothDensity_mollified_contact hn hV hq hVq hR hball
  have hdec := ContactLocal.isDecreasingApproximation_mollified hV hR hball
  have hm := measurableSet_contactBall' (x₀ := z₀) (R := R) hV hq.continuousOn
  filter_upwards [(ae_restrict_iff' hm).mp hlim] with z hz hzB hzV
  have hzΩ : z ∈ (Ω : Set (ComplexModel n)) :=
    hball (ball_subset_closedBall (ball_subset_ball (by linarith) hzB))
  have hzS : z ∈ ContactLocal.contactBall Ω V q z₀ R := ⟨⟨hzΩ, hzV⟩, hzB⟩
  exact ge_of_tendsto (hz hzS)
    (Eventually.of_forall fun j => smoothDensity_nonneg ((hdec.1 j).2.2 z hzB))

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- The densities of two obstacles `g ≤ f` in `C^{1,1̄}(X)` agree almost everywhere on `{g = f}`. -/
theorem ae_density_eq_of_le (w : KahlerBackground (m + 1) Y) {f g : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hg : HasBoundedMetricLaplacian w g)
    (hle : ∀ x, g x ≤ f x) (e : ComplexChart (m + 1) Y) {W : Set (ComplexModel (m + 1))}
    {ψ : ComplexModel (m + 1) → ℝ} (hWt : W ⊆ e.val.target)
    {hF hG : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hhF : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) hF W)
    (hhG : IsHessianDensityOn (fun z => g (e.val.symm z) + ψ z) hG W) :
    ∀ᵐ z, z ∈ W → g (e.val.symm z) = f (e.val.symm z) → hF z = hG z := by
  have hu := hf.sub w hg
  have hu0 : ∀ x, 0 ≤ f x - g x := fun x => sub_nonneg.mpr (hle x)
  have hdiff : IsHessianDensityOn (fun z => f (e.val.symm z) - g (e.val.symm z))
      (fun z => hF z - hG z) W :=
    (hhF.sub hhG).congr_fun (by funext z; ring)
  have hzero := hdiff.ae_eq_zero_of_isLittleO fun z _ => hu0 _
  have hlo := hu.ae_isLittleO w hu0 e
  filter_upwards [hzero, hlo] with z h1 h2 hzW hz0
  have hz0' : f (e.val.symm z) - g (e.val.symm z) = 0 := by rw [hz0, sub_self]
  exact sub_eq_zero.mp (h1 hzW hz0' (h2 (hWt hzW) hz0'))

variable [ConnectedSpace Y]

/-- An obstacle with bounded complex Hessian between `φ` and `f` (the book's `P_{θ + ω}(f)`). -/
theorem exists_bounded_obstacle_between (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    ∃ g : Y → ℝ, HasBoundedMetricLaplacian w g ∧ HasBoundedComplexHessian (n := m + 1) g ∧
      (∀ x, u x ≤ (g x : EReal)) ∧ ∀ x, g x ≤ f x := by
  obtain ⟨A, hA, hK⟩ := KahlerDomination.exists_pos_isKahler_add_smul w θ
  set θ' := θ + A • w.form with hθ'
  set B : KahlerBackground (m + 1) Y := ⟨θ', hK⟩ with hB
  have hu' : IsThetaPshPotential θ'.val u :=
    ⟨NefBoundedMixedMass.thetaPlurisubharmonic_add_of_isSemipositive hu.1
      (NefBoundedMixedMass.isSemipositive_smul w.isSemipositive hA.le), hu.2⟩
  obtain ⟨hreal, hgcls⟩ := envelope_min_hasBoundedMetricLaplacian_gen w B hf hf
  simp only [min_self] at hreal hgcls
  set g : Y → ℝ := envelopeReal B.form f with hgdef
  have hP : IsThetaPshPotential θ'.val (rooftopEnvelope θ'.val fun x => (f x : EReal)) :=
    TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous w θ' hf.1 hu'
  have hgeq : (rooftopEnvelope θ'.val fun x => (f x : EReal)) = fun x => (g x : EReal) :=
    funext hreal
  have hgpsh : IsThetaPshPotential θ'.val (fun x => (g x : EReal)) := hgeq ▸ hP
  refine ⟨g, hgcls, hasBoundedComplexHessian_of_isThetaPshPotential w θ' hgcls hgpsh,
    fun x => ?_, fun x => ?_⟩
  · have := le_rooftopEnvelope hu' (quasiEverywhere_of_forall hle) x
    rwa [hreal x] at this
  · have := TranscendentalWNReg.rooftopEnvelope_le_of_isThetaPshPotential hf.1 hP x
    rw [hreal x] at this
    exact EReal.coe_le_coe_iff.mp this

/-- **On the contact set the density of `θ_fⁿ` is nonnegative**: for `φ ∈ PSH(X, θ)`,
`f ∈ C^{1,1̄}(X)`, `φ ≤ f`, in every chart and for every Hessian density `h` of `f ∘ e⁻¹ + ψ`
(`ψ` a local potential of `θ` on `W`), `(n!/πⁿ) Re det h ≥ 0` almost everywhere on `e({φ = f}) ∩ W`. -/
theorem ae_hessDensity_nonneg_on_contact (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal))
    {e : ComplexChart (m + 1) Y} {W : Set (ComplexModel (m + 1))} {ψ : ComplexModel (m + 1) → ℝ}
    (hψ : IsSmoothLocalPotential θ.val e W ψ)
    {h : ComplexModel (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hh : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W) :
    ∀ᵐ z, z ∈ W → u (e.val.symm z) = (f (e.val.symm z) : EReal) → 0 ≤ hessDensity h z := by
  obtain ⟨g, hgcls, hgB, hug, hgf⟩ := exists_bounded_obstacle_between w θ hu hf hle
  obtain ⟨H, hH⟩ := hgB.exists_density_add e hψ.1 hψ.2.1 hψ.2.2.1
  have heq := ae_density_eq_of_le w hf hgcls hgf e hψ.2.1 hh (isHessianDensityOn_of_bounded hH)
  set q : ComplexModel (m + 1) → ℝ := fun z => g (e.val.symm z) + ψ z with hq
  have hVpsh := plurisubharmonicOn_chartFunction_add_potential hu.1 hψ
  have hloc : ∀ z₀ ∈ W, ∀ R : ℝ, 0 < R → closedBall z₀ (4 * R) ⊆ W →
      ∀ᵐ z, z ∈ ball z₀ (2 * R) → u (e.val.symm z) = (f (e.val.symm z) : EReal) →
        0 ≤ hessDensity H z := by
    intro z₀ _ R hR hball
    obtain ⟨c, hc⟩ := (isCompact_closedBall z₀ (4 * R)).exists_bound_of_continuousOn
      (hH.continuousOn.mono hball)
    set Ω : Opens (ComplexModel (m + 1)) := ⟨ball z₀ (4 * R), isOpen_ball⟩ with hΩ
    have hΩW : (Ω : Set (ComplexModel (m + 1))) ⊆ W := ball_subset_closedBall.trans hball
    set V' : ComplexModel (m + 1) → EReal := fun z => chartFunction u e z + (ψ z : EReal)
    set V : ComplexModel (m + 1) → ℝ := fun z => (max (V' z) ((-(|c| + 1) : ℝ) : EReal)).toReal
    have hV'q : ∀ z ∈ W, V' z ≤ (q z : EReal) := fun z hz => by
      simp only [V', chartFunction, hq, EReal.coe_add]
      exact add_le_add_left (hug _) _
    have hqc : ∀ z ∈ (Ω : Set (ComplexModel (m + 1))), |q z| ≤ |c| := fun z hz => by
      have := hc z (ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self c)
    have hVeq : ∀ z ∈ W, ((V z : ℝ) : EReal) = max (V' z) ((-(|c| + 1) : ℝ) : EReal) := by
      intro z hz
      refine EReal.coe_toReal ?_ ?_
      · exact ne_of_lt (max_lt (lt_of_le_of_lt (hV'q z hz) (EReal.coe_lt_top _))
          (EReal.coe_lt_top _))
      · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (le_max_right _ _))
    have hVpshΩ : IsLocallyBoundedPshOn Ω V := by
      refine ⟨?_, fun z hz => ⟨Ω, hz, le_rfl, |c| + 1, fun y hy => ?_⟩⟩
      · have hmax := (hVpsh.mono hΩW).max (fun x _ => plurisubharmonicAt_const
          ((-(|c| + 1) : ℝ) : EReal) (EReal.coe_ne_top _) x)
        intro x hx
        have h1 : (fun z => ((V z : ℝ) : EReal)) =ᶠ[𝓝 x]
            fun z => max (V' z) ((-(|c| + 1) : ℝ) : EReal) := by
          filter_upwards [isOpen_ball.mem_nhds hx] with y hy
          exact hVeq y (hΩW hy)
        exact (hmax x hx).congr h1.symm
      · have hyW := hΩW hy
        have h1 := hVeq y hyW
        have hup : V y ≤ q y := by
          have : ((V y : ℝ) : EReal) ≤ (q y : EReal) := by
            rw [h1]
            exact max_le (hV'q y hyW) (EReal.coe_le_coe_iff.mpr
              (by linarith [neg_abs_le (q y), abs_nonneg (q y), hqc y hy]))
          exact EReal.coe_le_coe_iff.mp this
        have hlow : -(|c| + 1) ≤ V y := by
          have : (((-(|c| + 1)) : ℝ) : EReal) ≤ ((V y : ℝ) : EReal) := by
            rw [h1]; exact le_max_right _ _
          exact EReal.coe_le_coe_iff.mp this
        rw [abs_le]
        constructor
        · linarith
        · linarith [hqc y hy, le_abs_self (q y)]
    have hVq : ∀ z ∈ Ω, V z ≤ q z := fun z hz => by
      have h1 := hVeq z (hΩW hz)
      have : ((V z : ℝ) : EReal) ≤ (q z : EReal) := by
        rw [h1]
        exact max_le (hV'q z (hΩW hz)) (EReal.coe_le_coe_iff.mpr
          (by linarith [neg_abs_le (q z), abs_nonneg (q z), hqc z hz]))
      exact EReal.coe_le_coe_iff.mp this
    have hnn := ae_hessDensity_nonneg_of_contact (Nat.succ_pos m) hVpshΩ
      (hH.mono isOpen_ball hΩW) hVq
    filter_upwards [hnn] with z hz hzB hzE
    have hzΩ : z ∈ (Ω : Set (ComplexModel (m + 1))) :=
      ball_subset_ball (by linarith) hzB
    refine hz hzΩ ?_
    have hgz : (g (e.val.symm z) : EReal) = f (e.val.symm z) :=
      le_antisymm (EReal.coe_le_coe_iff.mpr (hgf _)) (hzE ▸ hug _)
    have hV'z : V' z = (q z : EReal) := by
      simp only [V', chartFunction, hq, EReal.coe_add, hzE, hgz]
    have h1 := hVeq z (hΩW hzΩ)
    rw [hV'z, max_eq_left (EReal.coe_le_coe_iff.mpr
      (by linarith [neg_abs_le (q z), abs_nonneg (q z), hqc z hzΩ]))] at h1
    exact EReal.coe_eq_coe_iff.mp h1
  have hall := IsHessianDensityOn.ae_of_forall_ball hψ.1 hloc
  filter_upwards [hall, heq] with z hz1 hz2 hzW hzE
  have hgz : g (e.val.symm z) = f (e.val.symm z) :=
    EReal.coe_eq_coe_iff.mp (le_antisymm (EReal.coe_le_coe_iff.mpr (hgf _)) (hzE ▸ hug _))
  rw [hessDensity, hz2 hzW hgz]
  exact hz1 hzW hzE

end SGPT.Envelopes.LapClass3
