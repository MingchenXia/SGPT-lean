import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicConvexity

set_option autoImplicit false

/-!
# Convexity in time of the Perron finite geodesic

Every Perron competitor is an interior strip subgeodesic, hence its vertical
trace obeys the three-point chord inequality
(`FirstPass.IsSubgeodesicInterior.le_eRealChord_between`).  This file
transports that inequality through the Perron envelope
`finiteGeodesic = sup*` *including the spatial upper-semicontinuous
regularization*, and derives the convexity dichotomy for the vertical trace of
the envelope itself.

The transport is not formal: `finiteGeodesic t` is a regularized supremum, and
a regularization does not in general commute with an affine combination.  What
makes it work is `FirstPass.finiteGeodesic_le_iff`: the regularized supremum
lies below *any* upper semicontinuous majorant of the raw family, and the chord
built from the two regularized values `finiteGeodesic a`, `finiteGeodesic b` is
such a majorant — upper semicontinuous because both are, and finite above
because both lie below the endpoint chord
(`FirstPass.finiteGeodesic_le_eRealChord`).

This is the "convexity in `Re τ` of the slicewise regularization" input named
in the frontier note I-0388 for
`Pending.finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass`
(Xia, Proposition 4.1.3, `xia-sgpt:page-0150`--`xia-sgpt:page-0152`): it is what
upgrades an identity holding for almost every time to one holding for every
time.  Nothing here uses relative full mass, a Kähler background, or
compactness of `M`.

Sources: `xia-sgpt:page-0150`, `xia-sgpt:page-0151`.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- An interior value of the Perron finite geodesic is never `⊤`: it lies
below the chord of the two endpoint bounds, and a `θ`-PSH potential is never
`⊤`. -/
theorem finiteGeodesic_ne_top
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    finiteGeodesic θ u₀ u₁ t x ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (finiteGeodesic_le_eRealChord hu₀ hu₁ ht x)
  exact eRealChord_ne_top (hu₀.1.quasiPlurisubharmonic.ne_top x)
    (hu₁.1.quasiPlurisubharmonic.ne_top x) ht.1.le ht.2.le

/-- **The three-point chord inequality for the Perron finite geodesic.**  The
value at an intermediate interior time lies below the extended-real chord
through the two *regularized* surrounding values.  This is convexity in time
of `sup*` itself, not merely of its competitors. -/
theorem finiteGeodesic_le_eRealChord_between
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {a t b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hat : a < t) (htb : t < b) (x : M) :
    finiteGeodesic θ u₀ u₁ t x ≤
      eRealChord (finiteGeodesic θ u₀ u₁ a x) (finiteGeodesic θ u₀ u₁ b x)
        ((t - a) / (b - a)) := by
  have hab : a < b := hat.trans htb
  have hs : (t - a) / (b - a) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hat) (sub_pos.mpr hab)
    · exact (div_lt_one (sub_pos.mpr hab)).2 (by linarith)
  have hg : UpperSemicontinuous fun y =>
      eRealChord (finiteGeodesic θ u₀ u₁ a y) (finiteGeodesic θ u₀ u₁ b y)
        ((t - a) / (b - a)) :=
    upperSemicontinuous_eRealChord
      (upperSemicontinuous_finiteGeodesic θ u₀ u₁ a)
      (upperSemicontinuous_finiteGeodesic θ u₀ u₁ b)
      (finiteGeodesic_ne_top hu₀ hu₁ ha) (finiteGeodesic_ne_top hu₀ hu₁ hb)
      hs.1.le hs.2.le
  refine (finiteGeodesic_le_iff hg).2 ?_ x
  intro curve hcurve
  have hcompa := competitor_slice_le_finiteGeodesic hcurve a
  have hcompb := competitor_slice_le_finiteGeodesic hcurve b
  obtain ⟨v₀, v₁, -, -, -, -, hsub⟩ := hcurve
  intro y
  exact (hsub.2.2.1.le_eRealChord_between ha ht hb hat htb y).trans
    (eRealChord_mono (hcompa y) (hcompb y) hs.1.le hs.2.le)

/-- If one interior value of a vertical trace of the Perron geodesic is not a
pole, then no interior value of that trace is a pole. -/
theorem finiteGeodesic_ne_bot_of_exists_ne_bot
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (x : M) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (hc_bot : finiteGeodesic θ u₀ u₁ c x ≠ ⊥) :
    ∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x ≠ ⊥ := by
  intro t ht ht_bot
  rcases lt_trichotomy t c with htc | htc | hct
  · -- `t < c`: choose a time beyond `c` and put `c` strictly between.
    obtain ⟨b, hb, hcb⟩ : ∃ b ∈ Ioo (0 : ℝ) 1, c < b :=
      ⟨(c + 1) / 2, ⟨by linarith [hc.1, hc.2], by linarith [hc.2]⟩,
        by linarith [hc.2]⟩
    have hchord :=
      finiteGeodesic_le_eRealChord_between hu₀ hu₁ ht hc hb htc hcb x
    have hs : (c - t) / (b - t) ∈ Ioo (0 : ℝ) 1 := by
      have hab : t < b := htc.trans hcb
      exact ⟨div_pos (sub_pos.mpr htc) (sub_pos.mpr hab),
        (div_lt_one (sub_pos.mpr hab)).2 (by linarith)⟩
    rw [ht_bot] at hchord
    rw [eRealChord, mul_comm, EReal.bot_mul_of_pos
      (EReal.coe_pos.mpr (sub_pos.mpr hs.2)), EReal.bot_add] at hchord
    exact hc_bot (le_antisymm hchord bot_le)
  · exact hc_bot (htc ▸ ht_bot)
  · -- `c < t`: choose a time before `c` and put `c` strictly between.
    obtain ⟨a, ha, hac⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, a < c :=
      ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.1, hc.2]⟩,
        by linarith [hc.1]⟩
    have hchord :=
      finiteGeodesic_le_eRealChord_between hu₀ hu₁ ha hc ht hac hct x
    have hs : (c - a) / (t - a) ∈ Ioo (0 : ℝ) 1 := by
      have hab : a < t := hac.trans hct
      exact ⟨div_pos (sub_pos.mpr hac) (sub_pos.mpr hab),
        (div_lt_one (sub_pos.mpr hab)).2 (by linarith)⟩
    rw [ht_bot] at hchord
    rw [eRealChord, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hs.1),
      EReal.add_bot] at hchord
    exact hc_bot (le_antisymm hchord bot_le)

/-- A vertical trace of the Perron geodesic has uniform pole behaviour
throughout the open time interval. -/
theorem finiteGeodesic_all_bot_or_all_ne_bot
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁) (x : M) :
    (∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x = ⊥) ∨
      (∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x ≠ ⊥) := by
  classical
  by_cases hall : ∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x = ⊥
  · exact Or.inl hall
  · rw [not_forall] at hall
    obtain ⟨c, hc⟩ := hall
    rw [Classical.not_imp] at hc
    exact Or.inr (finiteGeodesic_ne_bot_of_exists_ne_bot hu₀ hu₁ x hc.1 hc.2)

/-- On the non-polar branch, an intermediate value of the Perron geodesic lies
below the ordinary real chord through two surrounding interior values. -/
theorem finiteGeodesic_toReal_le_chord_between
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {a t b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hat : a < t) (htb : t < b) (x : M)
    (hfinite : ∀ s ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ s x ≠ ⊥) :
    (finiteGeodesic θ u₀ u₁ t x).toReal ≤
      (1 - (t - a) / (b - a)) * (finiteGeodesic θ u₀ u₁ a x).toReal +
        ((t - a) / (b - a)) * (finiteGeodesic θ u₀ u₁ b x).toReal := by
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hat, htb.trans hb.2⟩
  have hchord :=
    finiteGeodesic_le_eRealChord_between hu₀ hu₁ ha ht hb hat htb x
  have hrhs :
      eRealChord (finiteGeodesic θ u₀ u₁ a x) (finiteGeodesic θ u₀ u₁ b x)
          ((t - a) / (b - a)) =
        (((1 - (t - a) / (b - a)) * (finiteGeodesic θ u₀ u₁ a x).toReal +
          ((t - a) / (b - a)) * (finiteGeodesic θ u₀ u₁ b x).toReal : ℝ) :
            EReal) := by
    unfold eRealChord
    conv_lhs =>
      rw [← EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ ha x) (hfinite a ha),
        ← EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ hb x) (hfinite b hb),
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  have hcoe : ((finiteGeodesic θ u₀ u₁ t x).toReal : EReal) =
      finiteGeodesic θ u₀ u₁ t x :=
    EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ ht x) (hfinite t ht)
  exact EReal.coe_le_coe_iff.mp (hcoe.trans_le (hchord.trans_eq hrhs))

/-- **Convexity in time of the Perron finite geodesic.**  If a vertical trace
of `sup*` has no pole in the open time interval, its real-valued trace is
convex there. -/
theorem convexOn_toReal_finiteGeodesic_of_forall_ne_bot
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁) (x : M)
    (hfinite : ∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x ≠ ⊥) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) fun t => (finiteGeodesic θ u₀ u₁ t x).toReal := by
  refine LinearOrder.convexOn_of_lt (convex_Ioo (0 : ℝ) 1) ?_
  intro a ha b hb hab α β hα hβ hsum
  set t : ℝ := α • a + β • b with ht_def
  have hαeq : α = 1 - β := by linarith
  have htleft : t = a + β * (b - a) := by
    rw [ht_def, hαeq]; simp only [smul_eq_mul]; ring
  have htright : t = b - α * (b - a) := by
    have hβeq : β = 1 - α := by linarith
    rw [ht_def, hβeq]; simp only [smul_eq_mul]; ring
  have hat : a < t := by
    rw [htleft]; exact lt_add_of_pos_right a (mul_pos hβ (sub_pos.mpr hab))
  have htb : t < b := by
    rw [htright]; exact sub_lt_self b (mul_pos hα (sub_pos.mpr hab))
  have hchord :=
    finiteGeodesic_toReal_le_chord_between hu₀ hu₁ ha hb hat htb x hfinite
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hs : (t - a) / (b - a) = β := by
    have hnum : t - a = β * (b - a) := by rw [htleft]; ring
    rw [hnum]; field_simp
  rw [hs] at hchord
  simpa only [ht_def, hαeq, smul_eq_mul] using hchord

/-- At a fixed spatial point, the Perron finite geodesic is either identically
`⊥` in interior time, or finite throughout with a convex real trace. -/
theorem finiteGeodesic_verticalTrace_convexity_dichotomy
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁) (x : M) :
    (∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x = ⊥) ∨
      ((∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic θ u₀ u₁ t x ≠ ⊤ ∧
          finiteGeodesic θ u₀ u₁ t x ≠ ⊥) ∧
        ConvexOn ℝ (Ioo (0 : ℝ) 1)
          fun t => (finiteGeodesic θ u₀ u₁ t x).toReal) := by
  rcases finiteGeodesic_all_bot_or_all_ne_bot hu₀ hu₁ x with hall | hfinite
  · exact Or.inl hall
  · exact Or.inr ⟨fun t ht => ⟨finiteGeodesic_ne_top hu₀ hu₁ ht x, hfinite t ht⟩,
      convexOn_toReal_finiteGeodesic_of_forall_ne_bot hu₀ hu₁ x hfinite⟩

end

end SGPT.Foundations.Analysis.Pending
