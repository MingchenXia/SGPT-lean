import SGPT.Foundations.Analysis.Pending.ThetaCapacity
import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition

set_option autoImplicit false

/-!
# Small capacity forces deep sup-normalized `ω`-PSH functions (Alexander--Taylor type)

On a compact Kähler manifold `(M, ω)` let `Cap_ω = thetaCapacity ω 0` (competitors
`-1 ≤ u ≤ 0`) and `vol = ∫ ω^n` (the mass of the potential `0`).  The basic comparison between
`Cap_ω` and the global extremal functions (Guedj--Zeriahi, *Intrinsic capacities on compact
Kähler manifolds*, J. Geom. Anal. 15 (2005), the Alexander--Taylor inequality) is, in the form
proved here (`exists_rooftopEnvelope_eq_zero_of_thetaCapacity_lt`):

  if `F` is a continuous obstacle with `-T ≤ F ≤ 0`, `F = 0` off a set `G`, and
  `Cap_ω(G) < T^{-n} vol`, then the envelope `P_ω(F)` attains the value `0`.

So `P_ω(F)` is a sup-normalized `ω`-PSH function (`sup = 0`) lying below `F`, in particular
`≤ -T` wherever `F = -T`: a set of small capacity carries deep sup-normalized `ω`-PSH functions.

*Proof.*  If `P_ω(F) < 0` everywhere, then `P_ω(F) < F` off `G`, so the Monge--Ampère measure of
`P_ω(F)` lives on `G` (Xia's Theorem 2.4.4 for a continuous obstacle,
`ContinuousObstacleEnvelopeContact.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous`)
and has the full mass `vol` (`P_ω(F)` is bounded, `-T ≤ P_ω(F) ≤ 0`).  The competitor
`P_ω(F)/T = T^{-1} P_ω(F) + (1 - T^{-1}) 0` of `Cap_ω` has measure `≥ T^{-n} (ω + dd^c P_ω(F))^n`
(`GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le`), so
`Cap_ω(G) ≥ T^{-n} vol`.

This is the first step (C1) of the I-0510 programme (`scratch/tn23-envelopes-i0510-scope-0104.md`,
corrected in run 0111): capacity zero ⇒ pluripolar.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The potential `0` is `ω`-PSH. -/
theorem isThetaPshPotential_zero (omega : KahlerBackground n M) :
    IsThetaPshPotential omega.form.val (fun _ => 0) :=
  (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive

/-- **The Kähler class is big**: `ω` itself, with potential `0`, is a Kähler current
(`ω ≥ ω/2`). -/
theorem isBigClass_kahler (omega : KahlerBackground n M) :
    IsBigClass (RealBottChern.ofRepresentative omega.form) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have heq : omega.form - (KahlerBackground.smul hhalf omega).form =
      (KahlerBackground.smul hhalf omega).form := by
    rw [KahlerBackground.smul_form]
    module
  refine ⟨{ representative := omega.form
            represents := rfl
            potential := fun _ => 0
            lowerBound := KahlerBackground.smul hhalf omega
            strictlyPsh := ?_ }⟩
  rw [heq]
  exact isThetaPshPotential_zero (KahlerBackground.smul hhalf omega)

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Two potentials squeezed between translates of each other have the same mass (the same
statement as `RooftopPshCriterion.diagonalPotentialMass_eq_of_le_add`, proved here from
`Pending.diagonalPotentialMass_mono_of_kahler` so that this module stays
below the domination-principle chain in the import graph). -/
theorem diagonalPotentialMass_eq_of_le_add (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {a b : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    {c₁ c₂ : ℝ} (h₁ : ∀ x, b x + ((-c₁ : ℝ) : EReal) ≤ a x) (h₂ : ∀ x, a x ≤ b x + (c₂ : EReal)) :
    diagonalPotentialMass theta a ha = diagonalPotentialMass theta b hb := by
  refine le_antisymm
    (Pending.diagonalPotentialMass_mono_of_kahler omega ha hb
      ⟨c₂, fun x _ => h₂ x⟩)
    (Pending.diagonalPotentialMass_mono_of_kahler omega hb ha
      ⟨c₁, fun x _ => ?_⟩)
  calc b x = b x + ((-c₁ : ℝ) : EReal) + (c₁ : EReal) := by
        rw [add_assoc, ← EReal.coe_add]; simp
    _ ≤ a x + (c₁ : EReal) := add_le_add (h₁ x) le_rfl

/-- **Small capacity forces the envelope to touch `0`** (Alexander--Taylor type).  For a
continuous obstacle `F` with `-T ≤ F ≤ 0` (`T > 1`) vanishing off `G`, if
`Cap_ω(G) < T^{-n} ∫ ω^n`, then `P_ω(F)` attains `0`. -/
theorem exists_rooftopEnvelope_eq_zero_of_thetaCapacity_lt (hn : 0 < n)
    (omega : KahlerBackground n M) {G : Set M} {F : M → ℝ} (hF : Continuous F) {T : ℝ}
    (hT : 1 < T) (hFT : ∀ x, -T ≤ F x) (hF0 : ∀ x, F x ≤ 0) (hFG : ∀ x ∉ G, F x = 0)
    (hcap : thetaCapacity omega.form (fun _ => 0) G <
      ENNReal.ofReal (T⁻¹ ^ n) *
        diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega)) :
    ∃ x, rooftopEnvelope omega.form.val (fun y => (F y : EReal)) x = 0 := by
  classical
  set θ : ClosedRealOneOneForm n M := omega.form with hθ
  have h0 := isThetaPshPotential_zero omega
  -- an empty manifold has no mass
  by_cases hne : Nonempty M
  swap
  · exfalso
    rw [not_nonempty_iff] at hne
    have hmass : diagonalPotentialMass θ (fun _ => 0) h0 = 0 := by
      rw [diagonalPotentialMass, univ_eq_empty_iff.mpr hne, measure_empty]
    rw [hmass, mul_zero] at hcap
    exact not_lt_zero hcap
  have hbig := isBigClass_kahler omega
  have hw := ContinuousObstacleEnvelopeContact.isThetaPshPotential_rooftopEnvelope_of_continuous
    hn θ hbig hF
  set u : M → EReal := rooftopEnvelope θ.val (fun y => (F y : EReal)) with hudef
  have hle : ∀ x, u x ≤ (F x : EReal) := fun x =>
    ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous hF
      (ContinuousObstacleEnvelopeContact.rooftopCompetitors_nonempty_of_isBigClass hn θ hbig hF)
      hw.1 x
  have hge : ∀ x, (((-T : ℝ)) : EReal) ≤ u x := by
    have hc : IsThetaPshPotential θ.val (fun x => (fun _ => (0 : EReal)) x + ((-T : ℝ) : EReal)) :=
      h0.add_const (-T)
    have := le_rooftopEnvelope hc (quasiEverywhere_of_forall fun x => by
      simp only [zero_add]
      exact EReal.coe_le_coe_iff.mpr (hFT x))
    intro x
    simpa only [zero_add] using this x
  by_contra hcon
  push Not at hcon
  have hneg : ∀ x, u x < 0 := fun x =>
    lt_of_le_of_ne ((hle x).trans (EReal.coe_le_coe_iff.mpr (hF0 x)) |>.trans (le_of_eq rfl))
      (hcon x)
  -- the Monge--Ampère measure of `u` lives on `G`
  have hcompl : diagonalPotentialMeasure θ u hw Gᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (ContinuousObstacleEnvelopeContact.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous
        hn θ hbig hF hw)
    change u x < (F x : EReal)
    rw [hFG x hx]
    exact hneg x
  -- full mass
  have hmass : diagonalPotentialMass θ u hw = diagonalPotentialMass θ (fun _ => 0) h0 :=
    diagonalPotentialMass_eq_of_le_add omega θ hw h0 (c₁ := T) (c₂ := 0)
      (fun x => by simpa only [zero_add] using hge x)
      (fun x => by simpa only [zero_add, EReal.coe_zero] using (hneg x).le)
  have hG : diagonalPotentialMass θ u hw ≤ diagonalPotentialMeasure θ u hw G := by
    calc diagonalPotentialMass θ u hw = diagonalPotentialMeasure θ u hw (G ∪ Gᶜ) := by
          rw [union_compl_self]; rfl
      _ ≤ diagonalPotentialMeasure θ u hw G + diagonalPotentialMeasure θ u hw Gᶜ :=
          measure_union_le _ _
      _ = diagonalPotentialMeasure θ u hw G := by rw [hcompl, add_zero]
  -- the competitor `u / T`
  set t : ℝ := T⁻¹ with htdef
  have ht0 : 0 < t := inv_pos.mpr (by linarith)
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ hT
  have hwt := isThetaPshPotential_convexComb hw h0 ht0 ht1
  have hval : ∀ x, ∃ r : ℝ, u x = (r : EReal) ∧ -T ≤ r ∧ r ≤ 0 := by
    intro x
    have hbot : u x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hge x)
    have htop : u x ≠ ⊤ := ne_top_of_lt (hneg x)
    refine ⟨(u x).toReal, (EReal.coe_toReal htop hbot).symm, ?_, ?_⟩
    · have := hge x
      rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_iff] at this
      exact this
    · have := (hneg x).le
      rw [← EReal.coe_toReal htop hbot] at this
      exact EReal.coe_nonpos.mp this
  have hcomb : ∀ x, ∃ r : ℝ, convexComb t u (fun _ => 0) x = ((t * r : ℝ) : EReal) ∧
      -T ≤ r ∧ r ≤ 0 := by
    intro x
    obtain ⟨r, hr, hr1, hr2⟩ := hval x
    refine ⟨r, ?_, hr1, hr2⟩
    rw [convexComb_apply, hr, mul_zero, add_zero, ← EReal.coe_mul]
  have hc1 : convexComb t u (fun _ => 0) ≤ fun _ => 0 := by
    intro x
    obtain ⟨r, hr, -, hr2⟩ := hcomb x
    rw [hr]
    exact EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos ht0.le hr2)
  have hc2 : ∀ x, (fun _ => (0 : EReal)) x ≤ convexComb t u (fun _ => 0) x + 1 := by
    intro x
    obtain ⟨r, hr, hr1, -⟩ := hcomb x
    rw [hr, ← EReal.coe_one, ← EReal.coe_add]
    refine EReal.coe_nonneg.mpr ?_
    have : t * r ≥ t * (-T) := mul_le_mul_of_nonneg_left hr1 ht0.le
    have htT : t * (-T) = -1 := by rw [htdef, mul_neg, inv_mul_cancel₀ (by linarith)]
    linarith
  have hcapw := diagonalPotentialMeasure_le_thetaCapacity hwt hc1 hc2 G
  have hscale : ENNReal.ofReal (t ^ n) * diagonalPotentialMeasure θ u hw G ≤
      diagonalPotentialMeasure θ (convexComb t u fun _ => 0) hwt G :=
    globalMixedMeasure_diagonal_convexComb_le hw h0 ht0 ht1 G
  have hfinal : ENNReal.ofReal (t ^ n) * diagonalPotentialMass θ (fun _ => 0) h0 ≤
      thetaCapacity θ (fun _ => 0) G := by
    rw [← hmass]
    calc ENNReal.ofReal (t ^ n) * diagonalPotentialMass θ u hw
        ≤ ENNReal.ofReal (t ^ n) * diagonalPotentialMeasure θ u hw G := by gcongr
      _ ≤ _ := hscale
      _ ≤ _ := hcapw
  exact absurd hcap (not_lt.mpr hfinal)

/-- **The capacity bound of a truncated competitor.**  For a function `u ≤ 0` with `max (u, -c)`
`ω`-PSH and
`c > 1`, the Monge--Ampère measure of `max (u, -c)` on any set is at most `c^n Cap_ω`. -/
theorem diagonalPotentialMeasure_max_le_thetaCapacity (omega : KahlerBackground n M)
    {u : M → EReal} (hu0 : ∀ x, u x ≤ 0) {c : ℝ}
    (hc : 1 < c)
    (hmax : IsThetaPshPotential omega.form.val (fun x => max (u x) ((-c : ℝ) : EReal)))
    (S : Set M) :
    diagonalPotentialMeasure omega.form (fun x => max (u x) ((-c : ℝ) : EReal)) hmax S ≤
      ENNReal.ofReal (c ^ n) * thetaCapacity omega.form (fun _ => 0) S := by
  have h0 := isThetaPshPotential_zero omega
  set v : M → EReal := fun x => max (u x) ((-c : ℝ) : EReal) with hvdef
  set t : ℝ := c⁻¹ with htdef
  have hc0 : 0 < c := by linarith
  have ht0 : 0 < t := inv_pos.mpr hc0
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ hc
  have hwt := isThetaPshPotential_convexComb hmax h0 ht0 ht1
  have hval : ∀ x, ∃ r : ℝ, v x = (r : EReal) ∧ -c ≤ r ∧ r ≤ 0 := by
    intro x
    have hge : ((-c : ℝ) : EReal) ≤ v x := le_max_right _ _
    have hle : v x ≤ 0 := max_le (hu0 x) (EReal.coe_nonpos.mpr (by linarith))
    have hbot : v x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hge
    have htop : v x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top hle
    refine ⟨(v x).toReal, (EReal.coe_toReal htop hbot).symm, ?_, ?_⟩
    · rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_iff] at hge
      exact hge
    · rw [← EReal.coe_toReal htop hbot] at hle
      exact EReal.coe_nonpos.mp hle
  have hcomb : ∀ x, ∃ r : ℝ, convexComb t v (fun _ => 0) x = ((t * r : ℝ) : EReal) ∧
      -c ≤ r ∧ r ≤ 0 := by
    intro x
    obtain ⟨r, hr, hr1, hr2⟩ := hval x
    refine ⟨r, ?_, hr1, hr2⟩
    rw [convexComb_apply, hr, mul_zero, add_zero, ← EReal.coe_mul]
  have hc1 : convexComb t v (fun _ => 0) ≤ fun _ => 0 := by
    intro x
    obtain ⟨r, hr, -, hr2⟩ := hcomb x
    rw [hr]
    exact EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos ht0.le hr2)
  have hc2 : ∀ x, (fun _ => (0 : EReal)) x ≤ convexComb t v (fun _ => 0) x + 1 := by
    intro x
    obtain ⟨r, hr, hr1, -⟩ := hcomb x
    rw [hr, ← EReal.coe_one, ← EReal.coe_add]
    refine EReal.coe_nonneg.mpr ?_
    have : t * r ≥ t * (-c) := mul_le_mul_of_nonneg_left hr1 ht0.le
    have htc : t * (-c) = -1 := by rw [htdef, mul_neg, inv_mul_cancel₀ hc0.ne']
    linarith
  have hcapw := diagonalPotentialMeasure_le_thetaCapacity hwt hc1 hc2 S
  have hscale : ENNReal.ofReal (t ^ n) * diagonalPotentialMeasure omega.form v hmax S ≤
      diagonalPotentialMeasure omega.form (convexComb t v fun _ => 0) hwt S :=
    globalMixedMeasure_diagonal_convexComb_le hmax h0 ht0 ht1 S
  have hone : ENNReal.ofReal (c ^ n) * ENNReal.ofReal (t ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, htdef, mul_inv_cancel₀ hc0.ne',
      one_pow, ENNReal.ofReal_one]
  calc diagonalPotentialMeasure omega.form v hmax S
      = ENNReal.ofReal (c ^ n) * (ENNReal.ofReal (t ^ n) *
          diagonalPotentialMeasure omega.form v hmax S) := by rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal (c ^ n) * thetaCapacity omega.form (fun _ => 0) S := by
        gcongr
        exact hscale.trans hcapw

/-- **Layered form of the dichotomy.**  Let `G₀ ⊇ G₁ ⊇ ⋯` be open, and let `F` be a continuous
obstacle with `-j ≤ F ≤ 0` and `F ≥ -k` off `G_k` for every `k`.  If
`∑_{k ≤ j} (k+2)^n Cap_ω(G_k) < ∫ ω^n`, then `P_ω(F)` attains `0`.

The contact set of `P_ω(F)` (which carries its Monge--Ampère measure) is covered by the sets
`G_k ∩ {P_ω(F) > -(k+2)}`, `k ≤ j`, and on each of them the measure is at most
`(k+2)^n Cap_ω(G_k)` (`diagonalPotentialMeasure_max_le_thetaCapacity` through Xia's (2.17),
`MaxMassDecomposition.measure_max_ge`). -/
theorem exists_rooftopEnvelope_eq_zero_of_layers (hn : 0 < n) (omega : KahlerBackground n M)
    {G : ℕ → Set M} (hGo : ∀ k, IsOpen (G k)) (hGanti : Antitone G) {F : M → ℝ}
    (hF : Continuous F) (hF0 : ∀ x, F x ≤ 0) {j : ℕ} (hFj : ∀ x, -(j : ℝ) ≤ F x)
    (hlayer : ∀ k x, x ∉ G k → -(k : ℝ) ≤ F x)
    (hcap : ∑ k ∈ Finset.range (j + 1),
        ENNReal.ofReal (((k : ℝ) + 2) ^ n) * thetaCapacity omega.form (fun _ => 0) (G k) <
      diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega)) :
    ∃ x, rooftopEnvelope omega.form.val (fun y => (F y : EReal)) x = 0 := by
  classical
  set θ : ClosedRealOneOneForm n M := omega.form with hθ
  have h0 := isThetaPshPotential_zero omega
  by_cases hne : Nonempty M
  swap
  · exfalso
    rw [not_nonempty_iff] at hne
    have hmass : diagonalPotentialMass θ (fun _ => 0) h0 = 0 := by
      rw [diagonalPotentialMass, univ_eq_empty_iff.mpr hne, measure_empty]
    rw [hmass] at hcap
    exact not_lt_zero hcap
  have hbig := isBigClass_kahler omega
  have hw := ContinuousObstacleEnvelopeContact.isThetaPshPotential_rooftopEnvelope_of_continuous
    hn θ hbig hF
  set u : M → EReal := rooftopEnvelope θ.val (fun y => (F y : EReal)) with hudef
  have hle : ∀ x, u x ≤ (F x : EReal) := fun x =>
    ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous hF
      (ContinuousObstacleEnvelopeContact.rooftopCompetitors_nonempty_of_isBigClass hn θ hbig hF)
      hw.1 x
  have hge : ∀ x, ((-(j : ℝ) : ℝ) : EReal) ≤ u x := by
    have hc : IsThetaPshPotential θ.val
        (fun x => (fun _ => (0 : EReal)) x + ((-(j : ℝ) : ℝ) : EReal)) := h0.add_const _
    have := le_rooftopEnvelope hc (quasiEverywhere_of_forall fun x => by
      simp only [zero_add]
      exact EReal.coe_le_coe_iff.mpr (hFj x))
    intro x
    simpa only [zero_add] using this x
  have hu0 : ∀ x, u x ≤ 0 := fun x => (hle x).trans (EReal.coe_nonpos.mpr (hF0 x))
  by_contra hcon
  push Not at hcon
  have hneg : ∀ x, u x < 0 := fun x => lt_of_le_of_ne (hu0 x) (hcon x)
  -- the measure of `u` lives on its contact set
  have hnc : diagonalPotentialMeasure θ u hw {x | u x < (F x : EReal)} = 0 :=
    ContinuousObstacleEnvelopeContact.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_continuous
      hn θ hbig hF hw
  have hmass : diagonalPotentialMass θ u hw = diagonalPotentialMass θ (fun _ => 0) h0 :=
    diagonalPotentialMass_eq_of_le_add omega θ hw h0 (c₁ := (j : ℝ))
      (c₂ := 0) (fun x => by simpa only [zero_add] using hge x)
      (fun x => by simpa only [zero_add, EReal.coe_zero] using hu0 x)
  -- the contact set is covered by the layers
  set A : ℕ → Set M := fun k => G k ∩ {x | ((-((k : ℝ) + 2) : ℝ) : EReal) < u x} with hAdef
  have hcover : univ ⊆ {x | u x < (F x : EReal)} ∪ ⋃ k ∈ Finset.range (j + 1), A k := by
    rintro x -
    by_cases hlt : u x < (F x : EReal)
    · exact Or.inl hlt
    right
    have hux : u x = (F x : EReal) := le_antisymm (hle x) (not_lt.mp hlt)
    have hF0x : F x < 0 := by
      have := hneg x
      rw [hux] at this
      exact EReal.coe_lt_coe_iff.mp this
    have hxG0 : x ∈ G 0 := by
      by_contra hx0
      have := hlayer 0 x hx0
      simp only [CharP.cast_eq_zero, neg_zero] at this
      linarith
    simp only [mem_iUnion, Finset.mem_range, exists_prop]
    by_cases hxj : x ∈ G j
    · refine ⟨j, Nat.lt_succ_self j, hxj, ?_⟩
      show ((-((j : ℝ) + 2) : ℝ) : EReal) < u x
      rw [hux, EReal.coe_lt_coe_iff]
      linarith [hFj x]
    · have hex : ∃ k, x ∉ G (k + 1) := by
        rcases j with _ | j
        · exact absurd hxG0 hxj
        · exact ⟨j, hxj⟩
      set k₀ := Nat.find hex with hk₀
      have hk₀spec : x ∉ G (k₀ + 1) := Nat.find_spec hex
      have hxk₀ : x ∈ G k₀ := by
        rcases Nat.eq_zero_or_pos k₀ with h | h
        · rw [h]; exact hxG0
        · have hlt' : k₀ - 1 < k₀ := by omega
          have := Nat.find_min hex hlt'
          push Not at this
          convert this using 2
          omega
      have hk₀j : k₀ < j + 1 := by
        have hle' : k₀ ≤ j := by
          by_contra hcon'
          push Not at hcon'
          exact hxj (hGanti hcon'.le hxk₀)
        omega
      refine ⟨k₀, hk₀j, hxk₀, ?_⟩
      show ((-((k₀ : ℝ) + 2) : ℝ) : EReal) < u x
      rw [hux, EReal.coe_lt_coe_iff]
      have := hlayer (k₀ + 1) x hk₀spec
      push_cast at this
      linarith
  -- each layer is controlled by the capacity
  have hlayerCap : ∀ k, diagonalPotentialMeasure θ u hw (A k) ≤
      ENNReal.ofReal (((k : ℝ) + 2) ^ n) * thetaCapacity θ (fun _ => 0) (G k) := by
    intro k
    have hck : 1 < (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hconst : IsThetaPshPotential θ.val
        (fun x => (fun _ => (0 : EReal)) x + ((-((k : ℝ) + 2) : ℝ) : EReal)) := h0.add_const _
    have hconst' : IsThetaPshPotential θ.val (fun _ => ((-((k : ℝ) + 2) : ℝ) : EReal)) := by
      simpa only [zero_add] using hconst
    have hmax : IsThetaPshPotential θ.val
        (fun x => max (u x) ((-((k : ℝ) + 2) : ℝ) : EReal)) := IsThetaPshPotential.max hw hconst'
    have h1 := MaxMassDecomposition.measure_max_ge omega hw hconst' hmax (hGo k).measurableSet
    have h2 := diagonalPotentialMeasure_max_le_thetaCapacity omega hu0 hck hmax (G k)
    exact (le_add_right le_rfl).trans (h1.trans h2) |>.trans' le_rfl
  have htotal : diagonalPotentialMass θ (fun _ => 0) h0 ≤
      ∑ k ∈ Finset.range (j + 1),
        ENNReal.ofReal (((k : ℝ) + 2) ^ n) * thetaCapacity θ (fun _ => 0) (G k) := by
    rw [← hmass, diagonalPotentialMass]
    calc diagonalPotentialMeasure θ u hw univ
        ≤ diagonalPotentialMeasure θ u hw
            ({x | u x < (F x : EReal)} ∪ ⋃ k ∈ Finset.range (j + 1), A k) := measure_mono hcover
      _ ≤ diagonalPotentialMeasure θ u hw {x | u x < (F x : EReal)} +
            diagonalPotentialMeasure θ u hw (⋃ k ∈ Finset.range (j + 1), A k) :=
          measure_union_le _ _
      _ ≤ 0 + ∑ k ∈ Finset.range (j + 1), diagonalPotentialMeasure θ u hw (A k) := by
          rw [hnc]
          gcongr
          exact measure_biUnion_finset_le _ _
      _ ≤ _ := by
          rw [zero_add]
          exact Finset.sum_le_sum fun k _ => hlayerCap k
  exact absurd hcap (not_lt.mpr htotal)

end

end SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
