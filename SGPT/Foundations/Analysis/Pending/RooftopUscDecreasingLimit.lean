import SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation

set_option autoImplicit false

/-!
# The envelope commutes with a decreasing limit of upper semicontinuous obstacles

`Pending.RooftopUscObstacleApproximation.rooftopEnvelope_eq_iInf_of_antitone`
proves `P_theta(f) = inf_k P_theta(g_k)` for a decreasing family of **real**
obstacles whose envelopes lie below them pointwise, and instantiates it at the
continuous majorants of an upper semicontinuous `f`.  The truncation step of
Xia's Theorem 2.4.4 (`xia-sgpt:page-0080`, the family `f_j = f \/ (-j)`) needs
the same identity for a decreasing family of `EReal`-valued **upper
semicontinuous** obstacles, and that is what this module proves.

The proof is the same as for real families, and it needs nothing new: for an
upper semicontinuous obstacle in a big class the envelope lies below the
obstacle *everywhere* (`rooftopEnvelope_le_of_upperSemicontinuous`) and is a
genuine potential (`isThetaPshPotential_rooftopEnvelope_of_upperSemicontinuous`),
which are exactly the two facts the argument consumed in the real case.

The instance is recorded: for `f` upper semicontinuous and bounded above by `0`
— possibly `-infinity` somewhere — the truncations `f \/ (-k)` are upper
semicontinuous, **bounded**, and

  `P_theta(f) = inf_k P_theta(f \/ (-k))`,   `P_theta(f \/ (-k)) <= f \/ (-k)`.

That is the first half of the truncation step.  The second half — that the
measures `theta^n_{P_theta(f \/ (-k))}`, each carried by its own contact set by
`Pending.RooftopUscEnvelopeConcentration`, pass to the limit — is **not** here,
and is not another application of the local concentration theorem: that theorem
wants a capacity sandwich `V_theta - C <= u_k <= V_theta` with one constant `C`,
and along the truncations the constant is `k` itself.  Recording that is the
point of this module's docstring as much as of its statements.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
open SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M] {theta : ClosedRealOneOneForm n M}

/-! ### The identity for a decreasing family of upper semicontinuous obstacles -/

/-- **`P_theta` commutes with a decreasing infimum of upper semicontinuous
obstacles.**  For a big class, each `P_theta(F k)` lies below `F k` everywhere,
so the infimum of the envelopes is a `theta`-PSH function below `inf_k F k`,
hence a competitor of the limit obstacle; the reverse inequality is
monotonicity. -/
theorem rooftopEnvelope_eq_iInf_of_antitone_usc (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {f : M → EReal} {F : ℕ → M → EReal}
    (hFusc : ∀ k, UpperSemicontinuous (F k)) (hFtop : ∀ k x, F k x ≠ ⊤)
    (hFne : ∀ k, (rooftopCompetitors theta.val (F k)).Nonempty)
    (hFanti : ∀ x, Antitone fun k => F k x)
    (hFinf : ∀ x, (⨅ k : ℕ, F k x) = f x)
    (hne : (rooftopCompetitors theta.val f).Nonempty) (x : M) :
    rooftopEnvelope theta.val f x = ⨅ k : ℕ, rooftopEnvelope theta.val (F k) x := by
  classical
  have hpot : ∀ k, IsThetaPshPotential theta.val (rooftopEnvelope theta.val (F k)) :=
    fun k => isThetaPshPotential_rooftopEnvelope_of_upperSemicontinuous hn theta hbig
      (hFusc k) (hFtop k) (hFne k)
  have hple : ∀ k, rooftopEnvelope theta.val (F k) ≤ F k :=
    fun k => rooftopEnvelope_le_of_upperSemicontinuous hn theta hbig (hFusc k) (hFtop k)
  have hEanti : ∀ y : M, Antitone fun k => rooftopEnvelope theta.val (F k) y := by
    intro y j k hjk
    exact rooftopEnvelope_mono (θ := theta.val) (fun z => hFanti z hjk) y
  set Phi : M → EReal := fun y => ⨅ k : ℕ, rooftopEnvelope theta.val (F k) y with hPhi
  have hPhipsh : ThetaPlurisubharmonic theta.val Phi :=
    thetaPlurisubharmonic_iInf_of_antitone (fun k => (hpot k).1) hEanti
  have hPhile : Phi ≤ f := by
    intro y
    rw [← hFinf y]
    exact le_iInf fun k => (iInf_le _ k).trans (hple k y)
  obtain ⟨v, hv⟩ := hne
  have hvPhi : v ≤ Phi := by
    intro y
    refine le_iInf fun k => ?_
    refine le_rooftopEnvelope hv.1 (hv.2.mono fun z hz => ?_) y
    exact hz.trans ((hFinf z) ▸ iInf_le (fun j : ℕ => F j z) k)
  have hPhipot : IsThetaPshPotential theta.val Phi := ⟨hPhipsh, hv.1.2.mono hvPhi⟩
  refine le_antisymm ?_ (le_rooftopEnvelope hPhipot (quasiEverywhere_of_forall hPhile) x)
  refine le_iInf fun k => ?_
  exact rooftopEnvelope_mono (θ := theta.val)
    (fun z => (hFinf z) ▸ iInf_le (fun j : ℕ => F j z) k) x

/-! ### The truncations `f \/ (-k)` -/

/-- **The truncations of an extended real by `-k` decrease to it.**  This is the
only `EReal` computation of the truncation step: at `-infinity` the values are
the `-k` themselves, whose infimum is `-infinity`; elsewhere the truncation is
eventually the value itself. -/
theorem iInf_max_neg_natCast (a : EReal) :
    (⨅ k : ℕ, max a ((-(k : ℝ) : ℝ) : EReal)) = a := by
  refine le_antisymm ?_ (le_iInf fun k => le_max_left _ _)
  cases a with
  | bot =>
      have hmax : ∀ k : ℕ, max (⊥ : EReal) ((-(k : ℝ) : ℝ) : EReal) =
          ((-(k : ℝ) : ℝ) : EReal) := fun k => max_eq_right bot_le
      simp only [hmax]
      refine le_of_eq (iInf_eq_bot.mpr fun b hb => ?_)
      rcases eq_or_ne b ⊤ with rfl | hbt
      · exact ⟨0, EReal.coe_lt_top _⟩
      · obtain ⟨s, hs⟩ : ∃ s : ℝ, b = (s : EReal) :=
          ⟨b.toReal, (EReal.coe_toReal hbt (ne_of_gt hb)).symm⟩
        obtain ⟨m, hm⟩ := exists_nat_gt (-s)
        exact ⟨m, by rw [hs]; exact EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  | top => exact le_top
  | coe r =>
      obtain ⟨m, hm⟩ := exists_nat_gt (-r)
      exact iInf_le_of_le m
        (max_le (le_refl _) (EReal.coe_le_coe_iff.mpr (by linarith)))

omit [CompactSpace M] [Nonempty M] in
/-- A truncated upper semicontinuous function is upper semicontinuous. -/
theorem upperSemicontinuous_max_const {f : M → EReal} (hf : UpperSemicontinuous f)
    (c : EReal) : UpperSemicontinuous fun x => max (f x) c := by
  intro x y hy
  rw [max_lt_iff] at hy
  filter_upwards [hf x y hy.1] with z hz
  exact max_lt hz hy.2

/-- **The first half of Xia's truncation step** (`xia-sgpt:page-0080`).  For an
upper semicontinuous obstacle bounded above by `0`, possibly `-infinity`
somewhere, the truncations `f \/ (-k)` are upper semicontinuous and **bounded**,
their envelopes lie below them everywhere, and

  `P_theta(f) = inf_k P_theta(f \/ (-k))`.

The second half — that the measures `theta^n_{P_theta(f \/ (-k))}`, each carried
by its own contact set by
`Pending.RooftopUscEnvelopeConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_upperSemicontinuous`,
pass to the limit — is open, and is *not* a further application of the local
concentration theorem: that theorem needs a capacity sandwich
`V_theta - C <= u_k <= V_theta` with a single constant, and along these
truncations the constant is `k`. -/
theorem rooftopEnvelope_eq_iInf_rooftopEnvelope_max_neg (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {f : M → EReal} (hf : UpperSemicontinuous f) (hf0 : ∀ x, f x ≤ 0)
    (hne : (rooftopCompetitors theta.val f).Nonempty) (x : M) :
    rooftopEnvelope theta.val f x =
      ⨅ k : ℕ, rooftopEnvelope theta.val
        (fun y => max (f y) ((-(k : ℝ) : ℝ) : EReal)) x := by
  classical
  have hV0 : ∀ y, thetaPshSupremum theta.val y ≤ (0 : EReal) := fun y => by
    simpa using thetaPshSupremum_le_zero theta.val y
  refine rooftopEnvelope_eq_iInf_of_antitone_usc hn theta hbig
    (F := fun k y => max (f y) ((-(k : ℝ) : ℝ) : EReal))
    (fun k => upperSemicontinuous_max_const hf _) (fun k y => ?_) (fun k => ?_)
    (fun y j k hjk => ?_) (fun y => iInf_max_neg_natCast (f y)) hne x
  · -- never `+infinity`
    refine ne_of_lt (max_lt ?_ (EReal.coe_lt_top _))
    exact lt_of_le_of_lt (hf0 y) (by simp)
  · -- `V_theta - k` is a competitor of the truncation
    refine ⟨fun y => thetaPshSupremum theta.val y + ((-(k : ℝ) : ℝ) : EReal),
      hV.add_const _, quasiEverywhere_of_forall fun y => ?_⟩
    refine le_max_of_le_right ?_
    calc thetaPshSupremum theta.val y + ((-(k : ℝ) : ℝ) : EReal)
        ≤ 0 + ((-(k : ℝ) : ℝ) : EReal) := add_le_add (hV0 y) (le_refl _)
      _ = ((-(k : ℝ) : ℝ) : EReal) := zero_add _
  · -- antitone in `k`
    refine max_le_max (le_refl _) (EReal.coe_le_coe_iff.mpr ?_)
    exact neg_le_neg (Nat.cast_le.mpr hjk)

end

end SGPT.Foundations.Analysis.Pending.RooftopUscDecreasingLimit
