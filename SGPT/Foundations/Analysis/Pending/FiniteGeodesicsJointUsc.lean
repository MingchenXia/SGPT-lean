import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsTimeConvexity
import SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
import SGPT.Foundations.Analysis.Pending.StripSliceRegularization
import Mathlib.Analysis.Convex.Continuous

set_option autoImplicit false

/-!
# Joint upper semicontinuity of the Perron finite geodesic in space and time

Xia's Proposition 4.1.3 (`xia-sgpt:page-0150`--`xia-sgpt:page-0152`) identifies
the *slicewise* spatial regularization defining `finiteGeodesic` with the
*joint* upper-semicontinuous regularization of the corrected competitor family
on a chart strip.  His proof compares both with the raw supremum almost
everywhere (Proposition 1.2.5), then repairs the null set by convexity in time.

This file proves the same identity by a shorter route that uses no measure
theory at all.  Once one knows

* `finiteGeodesic t` is upper semicontinuous in space for every fixed `t`
  (`FirstPass.upperSemicontinuous_finiteGeodesic`), and
* `t ↦ finiteGeodesic t x` is convex on `(0,1)` for every fixed `x`
  (`Pending.convexOn_toReal_finiteGeodesic_of_forall_ne_bot`, the regularization
  included),

joint upper semicontinuity follows directly: the chord inequality bounds
`finiteGeodesic t x` for `t` between `a` and `b` by a chord of two *fixed*
times, at which upper semicontinuity in `x` applies, and a convex function of
one real variable is continuous, so letting `a, b → t₀` recovers the value at
`t₀`.  The two-sided pole dichotomy makes the degenerate branch uniform.

Joint upper semicontinuity is exactly what the interchange needs: the corrected
`finiteGeodesic` already dominates the raw competitor supremum
(`StripSliceRegularization.sSup_image_le_subgeodesicChartFunction_finiteGeodesic`),
so being upper semicontinuous makes it dominate the *joint* regularization too.
Together with the easy half already in `Pending.StripSliceRegularization` this
gives equality.

Sources: `xia-sgpt:page-0150`, `xia-sgpt:page-0151`, `xia-sgpt:page-0152`.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}

/-- **Joint upper semicontinuity of the Perron finite geodesic.**  At an
interior time the Perron envelope `sup*` is upper semicontinuous as a function
of the pair (space point, time).  Nothing beyond `θ`-PSH endpoints is used: no
compactness, no Kähler background, no relative full mass. -/
theorem upperSemicontinuousAt_finiteGeodesic_prod
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (x₀ : M) :
    UpperSemicontinuousAt
      (fun p : M × ℝ => finiteGeodesic θ u₀ u₁ p.2 p.1) (x₀, t₀) := by
  intro c hc
  obtain ⟨r, hvr₀, hrc⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  have hvr : finiteGeodesic θ u₀ u₁ t₀ x₀ < (r : EReal) := hvr₀
  -- A two-sided real bound `K < r` at two surrounding interior times.
  have hkey : ∃ a b K : ℝ, a ∈ Ioo (0 : ℝ) 1 ∧ b ∈ Ioo (0 : ℝ) 1 ∧
      a < t₀ ∧ t₀ < b ∧ K < r ∧
      finiteGeodesic θ u₀ u₁ a x₀ < (K : EReal) ∧
      finiteGeodesic θ u₀ u₁ b x₀ < (K : EReal) := by
    have hδ0 : 0 < min t₀ (1 - t₀) / 2 := by
      have := ht₀.1; have := ht₀.2
      positivity
    rcases finiteGeodesic_all_bot_or_all_ne_bot hu₀ hu₁ x₀ with hbot | hfin
    · -- Polar branch: every interior value is `⊥`, so any `K < r` works.
      have h1 : min t₀ (1 - t₀) ≤ t₀ := min_le_left _ _
      have h2 : min t₀ (1 - t₀) ≤ 1 - t₀ := min_le_right _ _
      have hA : t₀ - min t₀ (1 - t₀) / 2 ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith, by linarith [ht₀.2, hδ0]⟩
      have hB : t₀ + min t₀ (1 - t₀) / 2 ∈ Ioo (0 : ℝ) 1 :=
        ⟨by linarith [ht₀.1, hδ0], by linarith⟩
      refine ⟨t₀ - min t₀ (1 - t₀) / 2, t₀ + min t₀ (1 - t₀) / 2, r - 1,
        hA, hB, by linarith, by linarith, by linarith, ?_, ?_⟩
      · rw [hbot _ hA]; exact EReal.bot_lt_coe _
      · rw [hbot _ hB]; exact EReal.bot_lt_coe _
    · -- Finite branch: the real trace is convex, hence continuous at `t₀`.
      have hconv := convexOn_toReal_finiteGeodesic_of_forall_ne_bot hu₀ hu₁ x₀ hfin
      have hcont : ContinuousAt
          (fun t => (finiteGeodesic θ u₀ u₁ t x₀).toReal) t₀ :=
        (ConvexOn.continuousOn isOpen_Ioo hconv).continuousAt
          (isOpen_Ioo.mem_nhds ht₀)
      set v : ℝ := (finiteGeodesic θ u₀ u₁ t₀ x₀).toReal with hv
      have hvcoe : finiteGeodesic θ u₀ u₁ t₀ x₀ = (v : EReal) :=
        (EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ ht₀ x₀)
          (hfin t₀ ht₀)).symm
      have hvlt : v < r := by
        rw [hvcoe] at hvr; exact EReal.coe_lt_coe_iff.mp hvr
      set K : ℝ := (v + r) / 2 with hK
      have hKr : K < r := by rw [hK]; linarith
      have hvK : v < K := by rw [hK]; linarith
      have hmem : {t : ℝ | (finiteGeodesic θ u₀ u₁ t x₀).toReal < K} ∈ 𝓝 t₀ :=
        hcont (isOpen_Iio.mem_nhds hvK)
      obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.mem_nhds_iff.mp hmem
      set δ : ℝ := min (δ₀ / 2) (min t₀ (1 - t₀) / 2) with hδ
      have hδpos : 0 < δ := lt_min (by linarith) hδ0
      have hδδ₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hδleft : 0 < t₀ - δ := by
        have h1 : δ ≤ min t₀ (1 - t₀) / 2 := min_le_right _ _
        have h2 : min t₀ (1 - t₀) ≤ t₀ := min_le_left _ _
        linarith
      have hδright : t₀ + δ < 1 := by
        have h1 : δ ≤ min t₀ (1 - t₀) / 2 := min_le_right _ _
        have h2 : min t₀ (1 - t₀) ≤ 1 - t₀ := min_le_right _ _
        linarith
      have hmemball : ∀ s : ℝ, |s - t₀| < δ₀ →
          (finiteGeodesic θ u₀ u₁ s x₀).toReal < K := by
        intro s hs
        exact hδ₀ (by simpa [Real.dist_eq] using hs)
      have hIoo : ∀ s : ℝ, 0 < s → s < 1 →
          (finiteGeodesic θ u₀ u₁ s x₀).toReal < K →
          finiteGeodesic θ u₀ u₁ s x₀ < (K : EReal) := by
        intro s hs0 hs1 hlt
        have : finiteGeodesic θ u₀ u₁ s x₀ =
            ((finiteGeodesic θ u₀ u₁ s x₀).toReal : EReal) :=
          (EReal.coe_toReal (finiteGeodesic_ne_top hu₀ hu₁ ⟨hs0, hs1⟩ x₀)
            (hfin s ⟨hs0, hs1⟩)).symm
        rw [this]
        exact EReal.coe_lt_coe_iff.mpr hlt
      refine ⟨t₀ - δ, t₀ + δ, K, ⟨hδleft, by linarith [ht₀.2]⟩,
        ⟨by linarith [ht₀.1], hδright⟩, by linarith, by linarith, hKr, ?_, ?_⟩
      · exact hIoo _ hδleft (by linarith [ht₀.2]) (hmemball _ (by
          rw [abs_of_nonpos (by linarith)]; linarith))
      · exact hIoo _ (by linarith [ht₀.1]) hδright (hmemball _ (by
          rw [abs_of_nonneg (by linarith)]; linarith))
  obtain ⟨a, b, K, ha, hb, hat, htb, hKr, hAa, hBb⟩ := hkey
  have hNa : {x : M | finiteGeodesic θ u₀ u₁ a x < (K : EReal)} ∈ 𝓝 x₀ :=
    upperSemicontinuous_finiteGeodesic θ u₀ u₁ a x₀ (K : EReal) hAa
  have hNb : {x : M | finiteGeodesic θ u₀ u₁ b x < (K : EReal)} ∈ 𝓝 x₀ :=
    upperSemicontinuous_finiteGeodesic θ u₀ u₁ b x₀ (K : EReal) hBb
  have hT : Ioo a b ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ⟨hat, htb⟩
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod (Filter.inter_mem hNa hNb) hT] with p hp
  obtain ⟨⟨hpa, hpb⟩, hpt⟩ := hp
  have hpt' : p.2 ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hpt.1, hpt.2.trans hb.2⟩
  have hs : (p.2 - a) / (b - a) ∈ Ioo (0 : ℝ) 1 := by
    have hab : a < b := hat.trans htb
    exact ⟨div_pos (sub_pos.mpr hpt.1) (sub_pos.mpr hab),
      (div_lt_one (sub_pos.mpr hab)).2 (by linarith [hpt.2])⟩
  have hchord := finiteGeodesic_le_eRealChord_between hu₀ hu₁ ha hpt' hb
    hpt.1 hpt.2 p.1
  have hmono := eRealChord_mono hpa.le hpb.le hs.1.le hs.2.le
  have hconst : ∀ s : ℝ, eRealChord (K : EReal) (K : EReal) s = (K : EReal) := by
    intro s
    unfold eRealChord
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring
  calc finiteGeodesic θ u₀ u₁ p.2 p.1
      ≤ eRealChord (finiteGeodesic θ u₀ u₁ a p.1)
        (finiteGeodesic θ u₀ u₁ b p.1) ((p.2 - a) / (b - a)) := hchord
    _ ≤ eRealChord (K : EReal) (K : EReal) ((p.2 - a) / (b - a)) := hmono
    _ = (K : EReal) := hconst _
    _ < (r : EReal) := EReal.coe_lt_coe_iff.mpr hKr
    _ ≤ c := hrc.le

/-- A regularization is dominated at a point by any majorant that is upper
semicontinuous *there*.  The global statement `FirstPass.uscRegularization_le`
needs upper semicontinuity everywhere; the Perron geodesic only has it at
interior times, so the pointwise form is what the strip argument uses. -/
theorem uscRegularization_apply_le_of_upperSemicontinuousAt {X : Type*}
    [TopologicalSpace X] {f g : X → EReal} (hfg : f ≤ g) {p : X}
    (hg : UpperSemicontinuousAt g p) :
    uscRegularization f p ≤ g p := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy1, hy2⟩ := exists_between hcon
  have hmem : {x : X | g x < y} ∈ 𝓝 p := hg y hy1
  refine absurd ((uscRegularization_le_localSup f hmem).trans ?_) (not_le.mpr hy2)
  exact iSup₂_le fun x hx => (hfg x).trans hx.le

variable {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}

/-- The corrected chart representative of the Perron geodesic is upper
semicontinuous on the chart strip, jointly in the space and complexified time
variables.  This is the joint statement transported through the chart: the
correction `rho` is continuous, and the complexified time enters only through
its real part. -/
theorem upperSemicontinuousAt_subgeodesicChartFunction_finiteGeodesic
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (e : ComplexChart n M) (hrho : IsSmoothLocalPotential θ e W rho)
    {p : ComplexModel n × ℂ} (hp : p ∈ geodesicChartDomain W) :
    UpperSemicontinuousAt
      (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e rho) p := by
  have hpW : p.1 ∈ W := hp.1
  have hptarget : p.1 ∈ e.val.target := hrho.2.1 hpW
  have hsymm : ContinuousAt (fun q : ComplexModel n × ℂ => e.val.symm q.1) p :=
    (e.val.continuousAt_symm hptarget).comp continuousAt_fst
  have hre : ContinuousAt (fun q : ComplexModel n × ℂ => q.2.re) p :=
    Complex.continuous_re.continuousAt.comp continuousAt_snd
  have hPhi : ContinuousAt
      (fun q : ComplexModel n × ℂ => (e.val.symm q.1, q.2.re)) p :=
    hsymm.prodMk hre
  have hbase : UpperSemicontinuousAt
      (fun q : M × ℝ => finiteGeodesic θ u₀ u₁ q.2 q.1)
      (e.val.symm p.1, p.2.re) :=
    upperSemicontinuousAt_finiteGeodesic_prod hu₀ hu₁ ⟨hp.2.1, hp.2.2⟩ _
  have hcomp : UpperSemicontinuousAt
      (fun q : ComplexModel n × ℂ =>
        finiteGeodesic θ u₀ u₁ q.2.re (e.val.symm q.1)) p :=
    UpperSemicontinuousAt.comp
      (f := fun q : M × ℝ => finiteGeodesic θ u₀ u₁ q.2 q.1)
      (g := fun q : ComplexModel n × ℂ => (e.val.symm q.1, q.2.re))
      (c := p) hbase hPhi
  have hrhoc : ContinuousAt (fun q : ComplexModel n × ℂ => rho q.1) p :=
    (((hrho.2.2.1 p.1 hpW).contDiffAt (hrho.1.mem_nhds hpW)).continuousAt).comp
      continuousAt_fst
  exact ThetaPshCodimTwoExtension.upperSemicontinuousAt_add_real hcomp hrhoc

/-- **The hard half of Xia's Proposition 4.1.3.**  The joint upper
semicontinuous regularization of the corrected Perron competitor family on the
chart strip is dominated by the corrected *slicewise* regularization, which is
`finiteGeodesic`.  No almost-everywhere comparison is used: the corrected
`finiteGeodesic` already dominates the raw family, and the previous theorem says
it is upper semicontinuous, so it dominates the regularization as well. -/
theorem strip_envelope_le_subgeodesicChartFunction_finiteGeodesic
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (e : ComplexChart n M) (hrho : IsSmoothLocalPotential θ e W rho)
    {p : ComplexModel n × ℂ} (hp : p ∈ geodesicChartDomain W) :
    uscRegularization (sSup
        ((fun curve => subgeodesicChartFunction curve e rho) ''
          finiteGeodesicCompetitors θ u₀ u₁)) p ≤
      subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e rho p :=
  uscRegularization_apply_le_of_upperSemicontinuousAt
    (StripSliceRegularization.sSup_image_le_subgeodesicChartFunction_finiteGeodesic
      θ u₀ u₁ e rho)
    (upperSemicontinuousAt_subgeodesicChartFunction_finiteGeodesic hu₀ hu₁ e
      hrho hp)

/-- **Xia, Proposition 4.1.3.**  On the chart strip the joint regularization of
the corrected Perron family and the corrected slicewise Perron geodesic are
equal.  The easy half is
`Pending.StripSliceRegularization.subgeodesicChartFunction_finiteGeodesic_le_strip_envelope`. -/
theorem subgeodesicChartFunction_finiteGeodesic_eq_strip_envelope
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (e : ComplexChart n M) (hrho : IsSmoothLocalPotential θ e W rho)
    {p : ComplexModel n × ℂ} (hp : p ∈ geodesicChartDomain W) :
    subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e rho p =
      uscRegularization (sSup
        ((fun curve => subgeodesicChartFunction curve e rho) ''
          finiteGeodesicCompetitors θ u₀ u₁)) p :=
  le_antisymm
    (StripSliceRegularization.subgeodesicChartFunction_finiteGeodesic_le_strip_envelope
      θ u₀ u₁ e hrho hp.1)
    (strip_envelope_le_subgeodesicChartFunction_finiteGeodesic hu₀ hu₁ e hrho hp)

end

end SGPT.Foundations.Analysis.Pending
