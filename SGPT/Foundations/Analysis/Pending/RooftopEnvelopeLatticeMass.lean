import SGPT.Foundations.Analysis.Pending.RooftopPshCriterion
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondEnvelopeMax
import SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier
import SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle

set_option autoImplicit false

/-!
# Xia's Lemma 3.1.2 and the envelope lattice mass reduction

Xia, SGPT, Lemma 3.1.2 (`xia-sgpt:page-0105`--`page-0107`): let `A, B` be
`θ`-PSH with `A ∧ B` a `θ`-PSH potential of positive mass, and let `γ ≤ A`,
`η ≤ B` be `θ`-PSH with `∫ θ^n_γ = ∫ θ^n_A`, `∫ θ^n_η = ∫ θ^n_B`.  Then `γ ∧ η`
is `θ`-PSH and `∫ θ^n_{γ∧η} = ∫ θ^n_{A∧B}`.

Here it is proved in two applications of its Step 1
(`rooftop_mass_eq_of_le_of_mass_eq`): for `ε ∈ (0, 1)` Corollary 2.4.3 gives
`η_ε` of the mass of `A` with `ε η_ε + (1 - ε) A ≤ γ`; Proposition 3.1.5
(`RooftopPshCriterion`) makes `η_ε ∧ (A ∧ B)`, hence `η_ε ∧ B`, `θ`-PSH; the
convex combination `(1 - ε)(A ∧ B) + ε (η_ε ∧ B)` is a competitor for `γ ∧ B`,
so multilinearity gives `∫ θ^n_{γ∧B} ≥ (1 - ε)^n ∫ θ^n_{A∧B}`; let `ε → 0`.
Xia's standing assumption (3.15) (`A`, `B` model potentials) is not used by
this argument and is not assumed.

Consequence (`diagonalPotentialMass_rooftop_singularityEnvelope_eq`): the
rooftop identity of Step 1 of Xia's Theorem 3.1.3,
`∫ θ^n_{P_θ[φ] ∧ P_θ[ψ]} = ∫ θ^n_{φ ∧ ψ}`, and with the maximum identity of
`RooftopMassDiamondEnvelopeMax`, the hypothesis-predicate
`RooftopMassDiamondReduction.EnvelopeLatticeMassReduction` itself
(`envelopeLatticeMassReduction`), on a connected compact Kähler manifold.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopEnvelopeLatticeMass

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.RooftopPshCriterion

noncomputable section

/-- A convex combination of a value with itself is at most that value. -/
theorem convexComb_self_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {b : EReal} (hb : b ≠ ⊤) :
    (t : EReal) * b + ((1 - t : ℝ) : EReal) * b ≤ b := by
  induction b using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos ht0, EReal.coe_mul_bot_of_pos (by linarith), EReal.bot_add]
  | top => exact absurd rfl hb
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith

/-- From `ε e + (1 - ε) a ≤ a` with `a` finite, `e ≤ a`. -/
theorem le_of_convexComb_le {eps : ℝ} (h0 : 0 < eps) {e a : EReal}
    (he : e ≠ ⊤) (ha : a ≠ ⊤) (ha' : a ≠ ⊥)
    (h : (eps : EReal) * e + ((1 - eps : ℝ) : EReal) * a ≤ a) : e ≤ a := by
  induction e using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd rfl he
  | coe s =>
    rw [← EReal.coe_toReal ha ha'] at h ⊢
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff]
    nlinarith

/-- From `a + C ≤ b`, `a ≤ b - C`. -/
theorem le_add_neg_of_add_le {a b : EReal} (C : ℝ) (h : a + (C : EReal) ≤ b) :
    a ≤ b + ((-C : ℝ) : EReal) := by
  calc a = a + (C : EReal) + ((-C : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]; simp
    _ ≤ b + ((-C : ℝ) : EReal) := add_le_add h le_rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The rooftop of `min (u, v)` is that of `min (v, u)`. -/
theorem rooftopEnvelope_min_comm (theta : ClosedRealOneOneForm n M) (u v : M → EReal) :
    rooftopEnvelope theta.val (fun x => min (u x) (v x)) =
      rooftopEnvelope theta.val (fun x => min (v x) (u x)) := by
  congr 1
  funext x
  exact min_comm _ _

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A rooftop lies below both obstacles. -/
theorem rooftopEnvelope_min_le (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v) :
    rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ u ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ v := by
  have heq : (fun x => min (u x) (v x + ((0 : ℝ) : EReal))) = fun x => min (u x) (v x) := by
    funext x; simp
  have hobs := rooftopEnvelope_min_add_const_le_obstacles (θ := theta.val) hu.1 hv.1 0
  rw [heq] at hobs
  exact ⟨hobs.1, fun x => by simpa using hobs.2 x⟩

/-- **Xia, Lemma 3.1.2, Step 1 (`xia-sgpt:page-0106`--`page-0107`).**  If
`A ∧ B` is a `θ`-PSH potential of positive mass and `γ ≤ A` has the mass of `A`,
then `γ ∧ B` is a `θ`-PSH potential with the mass of `A ∧ B`. -/
theorem rooftop_mass_eq_of_le_of_mass_eq [ConnectedSpace M] [Nonempty M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {A B g : M → EReal} (hA : IsThetaPshPotential theta.val A)
    (hB : IsThetaPshPotential theta.val B)
    (hAB : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (A x) (B x))))
    (hpos : 0 < diagonalPotentialMass theta _ hAB)
    (hg : IsThetaPshPotential theta.val g) (hgA : g ≤ A)
    (hmg : diagonalPotentialMass theta g hg = diagonalPotentialMass theta A hA) :
    ∃ hgB : IsThetaPshPotential theta.val
        (rooftopEnvelope theta.val (fun x => min (g x) (B x))),
      diagonalPotentialMass theta _ hgB = diagonalPotentialMass theta _ hAB := by
  classical
  set R := rooftopEnvelope theta.val (fun x => min (A x) (B x)) with hRdef
  obtain ⟨hRA, hRB⟩ := rooftopEnvelope_min_le theta hA hB
  have hfin : ∀ {a : M → EReal} (ha : IsThetaPshPotential theta.val a),
      diagonalPotentialMass theta a ha ≠ ⊤ := fun ha =>
    (MixedMass.globalMixedMass_lt_top omega (fun _ => ha.1)).ne
  have hmRA : diagonalPotentialMass theta R hAB ≤ diagonalPotentialMass theta A hA :=
    diagonalPotentialMass_mono_of_kahler omega hAB hA (MoreSingularOn.of_le fun x _ => hRA x)
  have hmg_pos : 0 < diagonalPotentialMass theta g hg := by
    rw [hmg]; exact lt_of_lt_of_le hpos hmRA
  -- the estimate at every `ε ∈ (0, 1)`
  have key : ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ hgB : IsThetaPshPotential theta.val
          (rooftopEnvelope theta.val (fun x => min (g x) (B x))),
        ENNReal.ofReal ((1 - eps) ^ n) * diagonalPotentialMass theta R hAB ≤
          diagonalPotentialMass theta _ hgB := by
    intro eps h0 h1
    obtain ⟨ea, hea, hmea, hbar⟩ := RelativeFullMassEpsilonBarrier.exists_thetaPsh_epsilonBarrier
      omega theta hA hg hgA hmg_pos hmg h0 h1
    -- the barrier lies below `A`
    have heaA : ea ≤ A := by
      refine RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hea.1 hA.1
        fun e => (hA.quasiPshPotential.ae_finite_chart e).mono fun z hz => ?_
      refine le_of_convexComb_le h0 (hea.1.quasiPlurisubharmonic.ne_top _) hz.1 hz.2 ?_
      exact (hbar (e.val.symm z)).trans (hgA (e.val.symm z))
    -- Proposition 3.1.5 for `ea` and `A ∧ B`
    have hmaxle : diagonalPotentialMass theta (fun x => max (ea x) (R x))
        (IsThetaPshPotential.max hea hAB) ≤ diagonalPotentialMass theta A hA :=
      diagonalPotentialMass_mono_of_kahler omega _ hA
        (MoreSingularOn.of_le fun x _ => max_le (heaA x) (hRA x))
    have hgt : diagonalPotentialMass theta (fun x => max (ea x) (R x))
        (IsThetaPshPotential.max hea hAB) <
        diagonalPotentialMass theta ea hea + diagonalPotentialMass theta R hAB := by
      refine lt_of_le_of_lt hmaxle ?_
      rw [hmea, hmg]
      exact ENNReal.lt_add_right (hfin hA) hpos.ne'
    have heaR := isThetaPshPotential_rooftopEnvelope_min_of_mass_lt omega theta hea hAB hgt
    obtain ⟨heaR_ea, heaR_R⟩ := rooftopEnvelope_min_le theta hea hAB
    obtain ⟨heaB, -, heaB_ea, heaB_B⟩ := rooftop_min_of_lower theta hea hB heaR heaR_ea
      (fun x => (heaR_R x).trans (hRB x))
    -- the competitor `(1 - ε) (A ∧ B) + ε (ea ∧ B)`
    have ht0 : 0 < 1 - eps := by linarith
    have ht1 : 1 - eps < 1 := by linarith
    have hK := isThetaPshPotential_convexComb hAB heaB ht0 ht1
    have hKg : convexComb (1 - eps) R
        (rooftopEnvelope theta.val (fun x => min (ea x) (B x))) ≤ g := by
      intro x
      refine (convexComb_mono ht0.le ht1.le hRA heaB_ea x).trans ?_
      refine le_of_eq_of_le ?_ (hbar x)
      rw [convexComb_apply, convexComb_apply, sub_sub_cancel, add_comm]
    have hKB : convexComb (1 - eps) R
        (rooftopEnvelope theta.val (fun x => min (ea x) (B x))) ≤ B := by
      intro x
      refine (convexComb_mono ht0.le ht1.le hRB heaB_B x).trans ?_
      rw [convexComb_apply]
      exact convexComb_self_le ht0 ht1 (hB.1.quasiPlurisubharmonic.ne_top x)
    obtain ⟨hgB, hKle, -, -⟩ := rooftop_min_of_lower theta hg hB hK hKg hKB
    refine ⟨hgB, ?_⟩
    calc ENNReal.ofReal ((1 - eps) ^ n) * diagonalPotentialMass theta R hAB
        ≤ diagonalPotentialMass theta _ hK :=
          NonPluripolarConvexCombLower.ofReal_pow_smul_diagonalPotentialMeasure_le_convexComb
            theta hAB heaB ht0 ht1 hK univ
      _ ≤ diagonalPotentialMass theta _ hgB :=
          diagonalPotentialMass_mono_of_kahler omega hK hgB (MoreSingularOn.of_le fun x _ => hKle x)
  obtain ⟨hgB, -⟩ := key (1 / 2) (by norm_num) (by norm_num)
  refine ⟨hgB, le_antisymm ?_ ?_⟩
  · refine diagonalPotentialMass_mono_of_kahler omega hgB hAB (MoreSingularOn.of_le fun x _ => ?_)
    exact rooftopEnvelope_mono (fun y => min_le_min (hgA y) le_rfl) x
  · -- let `ε → 0`
    have hbound : ∀ k : ℕ, ENNReal.ofReal ((1 - 1 / ((k : ℝ) + 2)) ^ n) *
        diagonalPotentialMass theta R hAB ≤ diagonalPotentialMass theta _ hgB := by
      intro k
      have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      obtain ⟨hgB', hle⟩ := key (1 / ((k : ℝ) + 2)) (by positivity)
        (by rw [div_lt_one hk]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      exact hle.trans (le_of_eq (diagonalPotentialMass_proof_independent hgB' hgB))
    have hlim0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal ((1 - 1 / ((k : ℝ) + 2)) ^ n) *
        diagonalPotentialMass theta R hAB) atTop
        (𝓝 (ENNReal.ofReal ((1 - 0) ^ n) * diagonalPotentialMass theta R hAB)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr (hfin hAB))
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_const_nhds.sub hlim0).pow n)
    rw [sub_zero, one_pow, ENNReal.ofReal_one, one_mul] at hlim
    exact le_of_tendsto' hlim hbound

/-- **Xia, Lemma 3.1.2 (`xia-sgpt:page-0105`--`page-0107`).**  If `A ∧ B` is a
`θ`-PSH potential of positive mass, and `γ ≤ A`, `η ≤ B` carry the masses of `A`
and `B`, then `γ ∧ η` is a `θ`-PSH potential with the mass of `A ∧ B`. -/
theorem rooftop_mass_eq_of_le_of_mass_eq₂ [ConnectedSpace M] [Nonempty M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {A B g h : M → EReal} (hA : IsThetaPshPotential theta.val A)
    (hB : IsThetaPshPotential theta.val B)
    (hAB : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (A x) (B x))))
    (hpos : 0 < diagonalPotentialMass theta _ hAB)
    (hg : IsThetaPshPotential theta.val g) (hgA : g ≤ A)
    (hmg : diagonalPotentialMass theta g hg = diagonalPotentialMass theta A hA)
    (hh : IsThetaPshPotential theta.val h) (hhB : h ≤ B)
    (hmh : diagonalPotentialMass theta h hh = diagonalPotentialMass theta B hB) :
    ∃ hgh : IsThetaPshPotential theta.val
        (rooftopEnvelope theta.val (fun x => min (g x) (h x))),
      diagonalPotentialMass theta _ hgh = diagonalPotentialMass theta _ hAB := by
  obtain ⟨hgB, hmgB⟩ := rooftop_mass_eq_of_le_of_mass_eq omega theta hA hB hAB hpos hg hgA hmg
  have hBg : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (B x) (g x))) := by
    rw [← rooftopEnvelope_min_comm]; exact hgB
  have hmBg : diagonalPotentialMass theta _ hBg = diagonalPotentialMass theta _ hgB :=
    diagonalPotentialMass_congr (rooftopEnvelope_min_comm theta B g) hBg hgB
  obtain ⟨hhg, hmhg⟩ := rooftop_mass_eq_of_le_of_mass_eq omega theta hB hg hBg
    (by rw [hmBg, hmgB]; exact hpos) hh hhB hmh
  have hgh : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (g x) (h x))) := by
    rw [rooftopEnvelope_min_comm]; exact hhg
  refine ⟨hgh, ?_⟩
  calc diagonalPotentialMass theta _ hgh = diagonalPotentialMass theta _ hhg :=
        diagonalPotentialMass_congr (rooftopEnvelope_min_comm theta g h) hgh hhg
    _ = _ := hmhg
    _ = _ := hmBg
    _ = _ := hmgB

/-- **Xia, Theorem 3.1.3, Step 1, the rooftop identity (`xia-sgpt:page-0108`).**
Replacing two `θ`-PSH potentials by their `P`-envelopes does not change the mass
of their rooftop: `∫ θ^n_{P_θ[φ] ∧ P_θ[ψ]} = ∫ θ^n_{φ ∧ ψ}`.  When the left side
vanishes this is the monotonicity theorem; otherwise it is Lemma 3.1.2 applied
to `A = P_θ[φ]`, `B = P_θ[ψ]` and the translates `φ - c ≤ A`, `ψ - c ≤ B`, which
carry the masses of `A` and `B` by Proposition 3.1.3. -/
theorem diagonalPotentialMass_rooftop_singularityEnvelope_eq [ConnectedSpace M] [Nonempty M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi))
    (hQ : IsThetaPshPotential theta.val (singularityEnvelope theta.val psi))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))))
    (hroofP : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x)))) :
    diagonalPotentialMass theta
        (rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
          (singularityEnvelope theta.val psi x))) hroofP =
      diagonalPotentialMass theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hroof := by
  set R := rooftopEnvelope theta.val (fun x => min (phi x) (psi x)) with hRdef
  set R' := rooftopEnvelope theta.val (fun x => min (singularityEnvelope theta.val phi x)
    (singularityEnvelope theta.val psi x)) with hR'def
  obtain ⟨c₁, hc₁⟩ := moreSingularOn_singularityEnvelope hphi
  obtain ⟨c₂, hc₂⟩ := moreSingularOn_singularityEnvelope hpsi
  set c : ℝ := max c₁ c₂ with hc
  have hφc : ∀ x, phi x ≤ singularityEnvelope theta.val phi x + (c : EReal) := fun x =>
    (hc₁ x (mem_univ x)).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
  have hψc : ∀ x, psi x ≤ singularityEnvelope theta.val psi x + (c : EReal) := fun x =>
    (hc₂ x (mem_univ x)).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))
  obtain ⟨hRphi, hRpsi⟩ := rooftopEnvelope_min_le theta hphi hpsi
  -- the translates
  have hg : IsThetaPshPotential theta.val (fun x => phi x + ((-c : ℝ) : EReal)) :=
    hphi.add_const (-c)
  have hh : IsThetaPshPotential theta.val (fun x => psi x + ((-c : ℝ) : EReal)) :=
    hpsi.add_const (-c)
  have hgA : (fun x => phi x + ((-c : ℝ) : EReal)) ≤ singularityEnvelope theta.val phi :=
    fun x => le_add_neg_of_add_le c (by
      calc phi x + ((-c : ℝ) : EReal) + (c : EReal) = phi x := by
            rw [add_assoc, ← EReal.coe_add]; simp
        _ ≤ singularityEnvelope theta.val phi x + (c : EReal) := hφc x) |>.trans
      (le_of_eq (by rw [add_assoc, ← EReal.coe_add]; simp))
  have hhB : (fun x => psi x + ((-c : ℝ) : EReal)) ≤ singularityEnvelope theta.val psi :=
    fun x => le_add_neg_of_add_le c (by
      calc psi x + ((-c : ℝ) : EReal) + (c : EReal) = psi x := by
            rw [add_assoc, ← EReal.coe_add]; simp
        _ ≤ singularityEnvelope theta.val psi x + (c : EReal) := hψc x) |>.trans
      (le_of_eq (by rw [add_assoc, ← EReal.coe_add]; simp))
  have hmg : diagonalPotentialMass theta _ hg = diagonalPotentialMass theta _ hP := by
    rw [singularityEnvelopeMassPreserving omega theta phi hphi hP]
    exact congrArg (fun μ : Measure M => μ univ)
      (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const theta hphi (-c) hg)
  have hmh : diagonalPotentialMass theta _ hh = diagonalPotentialMass theta _ hQ := by
    rw [singularityEnvelopeMassPreserving omega theta psi hpsi hQ]
    exact congrArg (fun μ : Measure M => μ univ)
      (DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const theta hpsi (-c) hh)
  -- `R ⪯ R'`
  have hRR' : ∀ x, R x ≤ R' x + (c : EReal) := by
    have hcomp : (fun x => R x + ((-c : ℝ) : EReal)) ≤ R' := by
      refine le_rooftopEnvelope (hroof.add_const (-c)) (quasiEverywhere_of_forall fun x => ?_)
      refine le_min ?_ ?_
      · exact (add_le_add (hRphi x) le_rfl).trans (hgA x)
      · exact (add_le_add (hRpsi x) le_rfl).trans (hhB x)
    intro x
    calc R x = R x + ((-c : ℝ) : EReal) + (c : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; simp
      _ ≤ R' x + (c : EReal) := add_le_add (hcomp x) le_rfl
  have hle : diagonalPotentialMass theta R hroof ≤ diagonalPotentialMass theta R' hroofP :=
    diagonalPotentialMass_mono_of_kahler omega hroof hroofP ⟨c, fun x _ => hRR' x⟩
  refine le_antisymm ?_ hle
  by_cases h0 : diagonalPotentialMass theta R' hroofP = 0
  · rw [h0]; exact bot_le
  obtain ⟨hgh, hmgh⟩ := rooftop_mass_eq_of_le_of_mass_eq₂ omega theta hP hQ hroofP
    (pos_iff_ne_zero.mpr h0) hg hgA hmg hh hhB hmh
  rw [← hmgh]
  -- the rooftop of the translates is a translate of `R`
  refine le_of_eq (RooftopPshCriterion.diagonalPotentialMass_eq_of_le_add omega theta hgh hroof
    (c₁ := c) (c₂ := -c) (fun x => ?_) (fun x => ?_))
  · refine le_rooftopEnvelope (hroof.add_const (-c)) (quasiEverywhere_of_forall fun y => ?_) x
    exact le_min (add_le_add (hRphi y) le_rfl) (add_le_add (hRpsi y) le_rfl)
  · obtain ⟨hghg, hghh⟩ := rooftopEnvelope_min_le theta hg hh
    refine le_add_neg_of_add_le c ?_
    refine le_rooftopEnvelope (hgh.add_const c) (quasiEverywhere_of_forall fun y => ?_) x
    refine le_min ?_ ?_
    · calc rooftopEnvelope theta.val (fun x => min (phi x + ((-c : ℝ) : EReal))
            (psi x + ((-c : ℝ) : EReal))) y + (c : EReal)
          ≤ phi y + ((-c : ℝ) : EReal) + (c : EReal) := add_le_add (hghg y) le_rfl
        _ = phi y := by rw [add_assoc, ← EReal.coe_add]; simp
    · calc rooftopEnvelope theta.val (fun x => min (phi x + ((-c : ℝ) : EReal))
            (psi x + ((-c : ℝ) : EReal))) y + (c : EReal)
          ≤ psi y + ((-c : ℝ) : EReal) + (c : EReal) := add_le_add (hghh y) le_rfl
        _ = psi y := by rw [add_assoc, ← EReal.coe_add]; simp

/-- **The envelope lattice mass reduction holds** on a connected compact Kähler
manifold: both identities of Step 1 of Xia's Theorem 3.1.3
(`xia-sgpt:page-0108`).  This discharges the hypothesis-predicate
`RooftopMassDiamondReduction.EnvelopeLatticeMassReduction`. -/
theorem envelopeLatticeMassReduction [ConnectedSpace M] [Nonempty M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M) :
    RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta := by
  intro phi psi hphi hpsi hP hQ hmax hmaxP hroof hroofP
  exact ⟨diagonalPotentialMass_max_singularityEnvelope_eq omega theta hphi hpsi hmax hmaxP,
    diagonalPotentialMass_rooftop_singularityEnvelope_eq omega theta hphi hpsi hP hQ hroof
      hroofP⟩

end

end SGPT.Foundations.Analysis.Pending.RooftopEnvelopeLatticeMass
