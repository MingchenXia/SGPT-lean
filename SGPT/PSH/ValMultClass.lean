import SGPT.PSH.RIsoAGermOrder
import SGPT.Foundations.Analysis.Pending.DivisorialMultiplierOrder
import SGPT.Foundations.Analysis.Pending.UnramifiedNormalOrder
import SGPT.Foundations.Analysis.Pending.CommonStrictUnramifiedPoint
import SGPT.Foundations.Analysis.Pending.RegularAtDimTransport

/-!
# `ord_E(f)` is a class function on prime divisors over `X`

Source: `chapter_pshfunctions.tex`, `thm:valuativemulti` (2), read on prime divisors over `X`
(`def:primdiv`: classes of prime divisors on modifications under common resolutions).  The book's
`ord_E(f)` of a germ `f ∈ 𝒪_{X,x}` along a prime divisor `E ⊆ Y` over `X` (`π : Y → X`) is the
order of vanishing of `π^* f` along `E` at the points of `E` over `x` (`RIsoAGermOrder.germOrdE`).
We prove that it does not depend on the representative of the class of `E`.

* `eventually_vanishingOrderAlong_eq`: **local constancy** of the order of vanishing along a smooth
  hypersurface `E`: if `g = q^k a` near `y` with `q` an equation of `E` and `a|_E ≢ 0` near `y`,
  then by the identity theorem on `E` (`frequently_ne_zero_of_mem_ball`) `a|_E ≢ 0` near every
  nearby point of `E`, so the order is `k` there too.
* `germOrdE_eq_of_commonResolution`: along a common-resolution witness
  (`CommonResolutionGeometry`: `Z → Y₀`, `Z → Y₁` modifications over `X` with the same strict
  transform `W` of `E₀` and `E₁`), `ord_{E₀}(f) = ord_{E₁}(f)`.  For `y₀ ∈ E₀` over `x` pick
  `z₀ ∈ W` over `y₀` (the strict transform maps onto `E₀`), then a point `z ∈ W` near `z₀` at which
  both maps are local biholomorphisms (irreducibility of `W`); there the two orders agree
  (`functionNormalOrder_comp_eq_of_not_exceptional`), and by local constancy they agree with the
  orders at `y₀` and at `y₁ = (Z → Y₁)(z₀) ∈ E₁` over `x`.
* `stalkOrdE_eq_of_commonResolution`, `compactStalkOrdE`: the descent to the classes over compact
  `X` (`RIsoAPrimeOver.PrimeOverCompact`), and `mem_multiplierIdeal_iff_compactBookPrimeBound`:
  `thm:valuativemulti` (1) ⟺ (2) with `E` ranging over prime-divisor CLASSES over compact `X`.

Blueprint: `claude-valmult.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.PSH.ValMultClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences BlowupFlatCoordinates
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder AnalyticModificationLocalDiscrepancy
  CompactPrimeOver CompactPrimeLogDiscrepancy ActualGermValuative RIsoAGermOrder
  HironakaSmoothCentreRealDomainActualSheafStalk

universe u

/-! ### The identity theorem on the hyperplane `{z_last = 0}` -/

section Hyperplane

variable {m : ℕ}

/-- **Identity theorem on the hyperplane.**  If `A` is holomorphic on a ball around a point `p`
of the hyperplane `{z_last = 0}` and does not vanish identically on the hyperplane near `p`, then
it does not vanish identically on the hyperplane near any point of the hyperplane in the ball. -/
theorem frequently_ne_zero_of_mem_ball {p : ComplexModel (m + 1)} (hp : p (Fin.last m) = 0)
    {ε : ℝ} {A : ComplexModel (m + 1) → ℂ} (hA : ∀ z ∈ ball p ε, DifferentiableAt ℂ A z)
    (hne : ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ A z ≠ 0)
    {p' : ComplexModel (m + 1)} (hp' : p' ∈ ball p ε) (hp'l : p' (Fin.last m) = 0) :
    ∃ᶠ z in 𝓝 p', z (Fin.last m) = 0 ∧ A z ≠ 0 := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg hp'
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hvan : ∀ᶠ z in 𝓝 p', z (Fin.last m) = 0 → A z = 0 :=
    hcon.mono fun z hz hzl => by
      by_contra h
      exact hz ⟨hzl, h⟩
  set V : Set (ComplexModel m) := ball (initCoords p) ε with hV
  have hmaps : ∀ w ∈ V, sliceMap m 0 w ∈ ball p ε := fun w hw => by
    rw [mem_ball, dist_eq_norm, DivisorialMultiplierOrder.norm_eq_norm_initCoords (by simp [hp]),
      OTChen.initCoords_sub, initCoords_sliceMap, ← dist_eq_norm]
    exact hw
  have hinV : ∀ z ∈ ball p ε, z (Fin.last m) = 0 → initCoords z ∈ V := fun z hz hzl => by
    rw [hV, mem_ball, dist_eq_norm, ← OTChen.initCoords_sub,
      ← DivisorialMultiplierOrder.norm_eq_norm_initCoords (by simp [hzl, hp]), ← dist_eq_norm]
    exact hz
  have hsl : ∀ z : ComplexModel (m + 1), z (Fin.last m) = 0 → sliceMap m 0 (initCoords z) = z :=
    fun z hzl => by
      have := sliceMap_initCoords z
      rwa [hzl] at this
  set G' : ComplexModel m → ℂ := fun w => A (sliceMap m 0 w) with hG'
  have hG'd : DifferentiableOn ℂ G' V := fun w hw =>
    ((hA _ (hmaps w hw)).comp w ((differentiable_sliceMap 0) w)).differentiableWithinAt
  have hG'a : AnalyticOnNhd ℂ G' V :=
    HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball hG'd
  have hw' : initCoords p' ∈ V := hinV p' hp' hp'l
  have hG'ev : G' =ᶠ[𝓝 (initCoords p')] 0 := by
    have hcont : ContinuousAt (sliceMap m 0) (initCoords p') :=
      (continuous_sliceMap 0).continuousAt
    rw [← hsl p' hp'l] at hvan
    filter_upwards [hcont.eventually hvan] with w hw
    exact hw (sliceMap_last 0 w)
  have hG'0 := hG'a.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hw' hG'ev
  apply (Filter.not_frequently.mpr ?_) hne
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz ⟨hzl, hAz⟩
  have := hG'0 (hinV z hz hzl)
  simp only [hG', Pi.zero_apply, hsl z hzl] at this
  exact hAz this

/-- Points off the hyperplane accumulate at every point. -/
theorem frequently_last_ne_zero (ζ₀ : ComplexModel (m + 1)) :
    ∃ᶠ ζ in 𝓝 ζ₀, ζ (Fin.last m) ≠ 0 := by
  intro hev
  have hev' : ∀ᶠ ζ in 𝓝 ζ₀, ζ (Fin.last m) = 0 := hev.mono fun ζ h => by simpa using h
  have h0 : ζ₀ (Fin.last m) = 0 := hev'.self_of_nhds
  have ht : Tendsto (fun z : ComplexModel (m + 1) => ζ₀ + z) (𝓝 0) (𝓝 ζ₀) := by
    simpa only [add_zero] using ((continuous_const_add ζ₀).tendsto 0)
  apply DivisorialMultiplierOrder.not_eventually_last_eq_zero (m := m)
  filter_upwards [ht.eventually hev'] with z hz
  simpa [h0] using hz

end Hyperplane

/-! ### Local constancy of the order of vanishing along a smooth hypersurface -/

section LocalConstancy

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- Throughout the flat domain of a flattening of `E`, the powers of the vanishing ideal of `E`
are generated by the powers of the flattening equation. -/
theorem idealPow_mem_iff_flatEquation {E : Set Y} {y : Y} (Φ : DivisorFlattening (m := m) E y)
    {y' : Y} (hy' : y' ∈ BlowupFlatCoordinates.flatDomain Φ.Φ) (j : ℕ) (g : Y → ℂ) :
    (IdealWeightPowers.idealPow (vanishingIdeal (n := m + 1) E) j).mem y' g ↔
      IsInSpanAt (n := m + 1) (· = fun w => flatCoord Φ.Φ (Fin.last m) w ^ j) y' g :=
  HironakaSNCComponentCoefficients.idealPow_mem_iff_of_generator
    (holomorphicAt_flatCoord Φ.Φ (Fin.last m) hy')
    (MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ.Φ (fun {w} hw hwΦ => Φ.mem_iff w hw hwΦ)
      hy') j g

/-- The point with the flattening coordinates of a point of the flat domain is that point. -/
theorem tendsto_point_coord {E : Set Y} {y : Y} (Φ : DivisorFlattening (m := m) E y) {w : Y}
    (hw : w ∈ BlowupFlatCoordinates.flatDomain Φ.Φ) :
    Φ.coord w ∈ Φ.Φ.target ∧ Φ.point (Φ.coord w) = w ∧
      Tendsto Φ.point (𝓝 (Φ.coord w)) (𝓝 w) := by
  have hT : Φ.coord w ∈ Φ.Φ.target := Φ.Φ.mapsTo_toFun hw.2
  have hpc : Φ.point (Φ.coord w) = w := by
    change (chartAt (ComplexModel (m + 1)) y).symm
      (Φ.Φ.invFun (Φ.Φ.toFun ((chartAt (ComplexModel (m + 1)) y) w))) = w
    rw [Φ.Φ.left_inv _ hw.2]
    exact (chartAt (ComplexModel (m + 1)) y).left_inv hw.1
  refine ⟨hT, hpc, ?_⟩
  have h := ((Φ.continuousOn_point _ hT).continuousAt (Φ.Φ.isOpen_target.mem_nhds hT)).tendsto
  rwa [hpc] at h

/-- Near a point of the flat domain, the flattening equation does not vanish identically. -/
theorem frequently_flatEquation_ne_zero {E : Set Y} {y : Y} (Φ : DivisorFlattening (m := m) E y)
    {w : Y} (hw : w ∈ BlowupFlatCoordinates.flatDomain Φ.Φ) :
    ∃ᶠ w' in 𝓝 w, flatCoord Φ.Φ (Fin.last m) w' ≠ 0 := by
  obtain ⟨hT, -, ht⟩ := tendsto_point_coord Φ hw
  apply ht.frequently
  have h := (frequently_last_ne_zero (Φ.coord w)).and_eventually
    (Φ.Φ.isOpen_target.mem_nhds hT)
  refine h.mono fun ζ hζ => ?_
  have hc := Φ.coord_point hζ.2
  change (Φ.coord (Φ.point ζ)) (Fin.last m) ≠ 0
  rw [hc]
  exact hζ.1

/-- **Local constancy of the order of vanishing along a smooth hypersurface.**  If `E` is
flattened at `y` and `h` is holomorphic at `y`, the order of vanishing of `h` along `E` at the
points of `E` near `y` equals the order at `y`. -/
theorem eventually_vanishingOrderAlong_eq {E : Set Y} {y : Y} (Φ : DivisorFlattening (m := m) E y)
    {h : Y → ℂ} (hh : HolomorphicAt (m + 1) h y) :
    ∀ᶠ y' in 𝓝 y, y' ∈ E →
      vanishingOrderAlong (m + 1) E y' h = vanishingOrderAlong (m + 1) E y h := by
  classical
  set q : Y → ℂ := flatCoord Φ.Φ (Fin.last m) with hq
  have hy0 : y ∈ BlowupFlatCoordinates.flatDomain Φ.Φ := mem_flatDomain_self Φ.Φ
  have hdom : ∀ᶠ y' in 𝓝 y, y' ∈ BlowupFlatCoordinates.flatDomain Φ.Φ :=
    (isOpen_flatDomain Φ.Φ).mem_nhds hy0
  -- the order as a supremum over the powers of the equation
  have horder : ∀ y' ∈ BlowupFlatCoordinates.flatDomain Φ.Φ,
      vanishingOrderAlong (m + 1) E y' h =
        ⨆ (j : ℕ) (_ : IsInSpanAt (n := m + 1) (· = fun w => q w ^ j) y' h), (j : ℕ∞) := by
    intro y' hy'
    unfold vanishingOrderAlong
    exact iSup_congr fun j => iSup_congr_Prop (idealPow_mem_iff_flatEquation Φ hy' j h)
      fun _ => rfl
  by_cases hne : ∃ᶠ w in 𝓝 y, h w ≠ 0
  swap
  · -- `h` vanishes near `y`: all orders are infinite
    have hzero : ∀ᶠ w in 𝓝 y, h w = 0 := by
      simpa only [Filter.Frequently, not_not, ne_eq] using hne
    have htop : ∀ y' ∈ BlowupFlatCoordinates.flatDomain Φ.Φ, (∀ᶠ w in 𝓝 y', h w = 0) →
        vanishingOrderAlong (m + 1) E y' h = ⊤ := by
      intro y' hy' hz'
      rw [horder y' hy']
      refine (ENat.eq_top_iff_forall_ge).mpr fun j => ?_
      have hh' : HolomorphicAt (m + 1) h y' :=
        (holomorphicAt_const (n := m + 1) (x := y') (0 : ℂ)).congr
          (hz'.mono fun w hw => hw.symm)
      exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : IsInSpanAt (n := m + 1)
          (· = fun w => q w ^ j) y' h) => (j : ℕ∞)) j
        (isInSpanAt_of_eq_mul rfl hh' (holomorphicAt_const 0)
          (hz'.mono fun w hw => by simp [hw])) le_rfl
    filter_upwards [hdom, hzero.eventually_nhds] with y' hy' hz' _
    rw [htop y' hy' hz', htop y hy0 hzero]
  -- the order at `y` is a finite number `k`
  have hfin : vanishingOrderAlong (m + 1) E y h ≠ ⊤ := by
    rw [vanishingOrderAlong_eq_functionNormalOrder Φ h hh]
    exact normalOrder_ne_top Φ (LocalFibreReader.chartTranslatedGerm_ne_zero_of_frequently y h hh hne)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  have hFNO : functionNormalOrder Φ h hh = (k : ℕ∞) := by
    rw [← vanishingOrderAlong_eq_functionNormalOrder Φ h hh, hk]
  have hmemiff : ∀ j : ℕ, (IdealWeightPowers.idealPow (vanishingIdeal (n := m + 1) E) j).mem y h ↔
      (j : ℕ∞) ≤ (k : ℕ∞) := by
    intro j
    rw [IdealPowerNormalOrder.mem_idealPow_iff_equation_pow_dvd Φ j h hh, ← hFNO]
    exact pow_dvd_iff_le_emultiplicity
  have hk1 : ¬ IsInSpanAt (n := m + 1) (· = fun w => q w ^ (k + 1)) y h := fun hin => by
    have := (hmemiff (k + 1)).mp ((idealPow_mem_iff_flatEquation Φ hy0 (k + 1) h).mpr hin)
    exact absurd this (by exact_mod_cast Nat.not_succ_le_self k)
  obtain ⟨-, a, ha, hha⟩ := isInSpanAt_eq_iff.mp
    ((idealPow_mem_iff_flatEquation Φ hy0 k h).mp ((hmemiff k).mpr le_rfl))
  -- `a` does not vanish identically on `E` near `y`, in flattening coordinates
  set aT : ComplexModel (m + 1) → ℂ := fun ζ => a (Φ.point ζ) with haT
  have haTd : ∀ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ aT ζ :=
    SGPT.PSH.SameCoordinateOrder.adapted_holomorphic y Φ.Φ Φ.map_center a ha
  have hqT : ∀ ζ ∈ Φ.Φ.target, q (Φ.point ζ) = ζ (Fin.last m) := fun ζ hζ => by
    change (Φ.coord (Φ.point ζ)) (Fin.last m) = _
    rw [Φ.coord_point hζ]
  have hne0 : ∃ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)), ζ (Fin.last m) = 0 ∧ aT ζ ≠ 0 := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    have hvan : ∀ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)), ζ (Fin.last m) = 0 → aT ζ = 0 :=
      hcon.mono fun ζ hζ hζl => by
        by_contra h'
        exact hζ ⟨hζl, h'⟩
    obtain ⟨c, hc, hcaT⟩ := DivisorialMultiplierOrder.exists_eq_last_mul_of_eq_zero (by simp)
      haTd hvan
    -- then `a` is a multiple of `q` at `y`, and `h` of `q^{k+1}`
    have hspan : IsInSpanAt (n := m + 1) (· ∈ Set.range fun _ : Fin 1 => q) y a := by
      apply (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff y Φ.Φ Φ.map_center
        (fun _ : Fin 1 => q) a).mpr
      refine isInSpanAt_of_eq_mul ⟨0, rfl⟩ (haTd.mono fun _ hz => hz.mdifferentiableAt)
        (hc.mono fun _ hz => hz.mdifferentiableAt) ?_
      filter_upwards [hcaT, Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target] with ζ h1 h2
      change aT ζ = c ζ * q (Φ.point ζ)
      rw [h1, hqT ζ h2, mul_comm]
    have hspan' : IsInSpanAt (n := m + 1) (· = q) y a :=
      hspan.mono fun s hs => by
        obtain ⟨i, rfl⟩ := hs
        rfl
    obtain ⟨-, c', hc', hac'⟩ := isInSpanAt_eq_iff.mp hspan'
    apply hk1
    refine isInSpanAt_of_eq_mul rfl hh hc' ?_
    filter_upwards [hha, hac'] with w h1 h2
    rw [h1, h2, pow_succ]
    ring
  -- a ball of differentiability around `0`
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp haTd
  have hcoord : Tendsto Φ.coord (𝓝 y) (𝓝 0) := by
    have h := Φ.mdifferentiableAt_coord.continuousAt.tendsto
    rwa [Φ.coord_x] at h
  filter_upwards [hdom, hha.eventually_nhds, hh.eventually_nhds, ha.eventually_nhds,
    hcoord.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))] with y' hy' hha' hh' ha' hball' hyE
  replace hh' : HolomorphicAt (m + 1) h y' := hh'
  replace ha' : HolomorphicAt (m + 1) a y' := ha'
  have hlast : (Φ.coord y') (Fin.last m) = 0 := (Φ.mem_iff y' hy'.1 hy'.2).mp hyE
  rw [horder y' hy', ← hk]
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    by_contra hjk
    have hkj : k + 1 ≤ j := by
      have : k < j := by exact_mod_cast not_le.mp hjk
      omega
    -- then `h` is a multiple of `q^{k+1}` at `y'`
    obtain ⟨-, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp hj
    have hqhol : HolomorphicAt (m + 1) q y' := holomorphicAt_flatCoord Φ.Φ (Fin.last m) hy'
    set b' : Y → ℂ := fun w => b w * q w ^ (j - (k + 1)) with hb'
    have hb'hol : HolomorphicAt (m + 1) b' y' := hb.mul (CompanionReduction.holomorphicAt_pow_of hqhol _)
    have hhb' : ∀ᶠ w in 𝓝 y', h w = b' w * q w ^ (k + 1) := by
      filter_upwards [hbeq] with w hw
      rw [hw, hb', mul_assoc, ← pow_add, Nat.sub_add_cancel hkj]
    -- `a - b' q` vanishes near `y'`
    set f : Y → ℂ := fun w => a w - b' w * q w with hf
    have hqk : ∀ᶠ w in 𝓝 y', q w ^ k * f w = 0 := by
      filter_upwards [hha', hhb'] with w h1 h2
      have : a w * q w ^ k = b' w * q w ^ (k + 1) := h1.symm.trans h2
      simp only [hf]
      rw [mul_sub, pow_succ] at *
      linear_combination this
    have hfcont : ∀ᶠ w in 𝓝 y', ContinuousAt f w := by
      filter_upwards [ha'.eventually, hb'hol.eventually, hqhol.eventually] with w h1 h2 h3
      exact h1.continuousAt.sub (h2.continuousAt.mul h3.continuousAt)
    have hdom' : ∀ᶠ w in 𝓝 y', w ∈ BlowupFlatCoordinates.flatDomain Φ.Φ :=
      (isOpen_flatDomain Φ.Φ).mem_nhds hy'
    have hf0 : ∀ᶠ w in 𝓝 y', f w = 0 := by
      filter_upwards [hqk.eventually_nhds, hfcont, hdom'] with w hw hfc hwdom
      by_contra hfw
      have hev : ∀ᶠ w' in 𝓝 w, f w' ≠ 0 := hfc.eventually_ne hfw
      obtain ⟨w', hqw', hfw', hzero⟩ :=
        ((frequently_flatEquation_ne_zero Φ hwdom).and_eventually (hev.and hw)).exists
      exact (mul_ne_zero (pow_ne_zero _ hqw') hfw') hzero
    -- so `a` vanishes on `E` near `y'`
    have haE : ∀ᶠ w in 𝓝 y', w ∈ E → a w = 0 := by
      filter_upwards [hf0, hdom'] with w hw hwdom hwE
      have hqw : q w = 0 := (Φ.mem_iff w hwdom.1 hwdom.2).mp hwE
      have : a w = f w + b' w * q w := by simp only [hf]; ring
      rw [this, hw, hqw, mul_zero, add_zero]
    -- and `aT` vanishes on the hyperplane near the coordinates of `y'`
    obtain ⟨hT', hpc', ht'⟩ := tendsto_point_coord Φ hy'
    have haTvan : ∀ᶠ ζ in 𝓝 (Φ.coord y'), ζ (Fin.last m) = 0 → aT ζ = 0 := by
      have h1 := ht'.eventually haE
      filter_upwards [h1, Φ.Φ.isOpen_target.mem_nhds hT'] with ζ hζ hζT hζl
      exact hζ (Φ.point_mem hζT hζl)
    have hfreq := frequently_ne_zero_of_mem_ball (p := 0) (by simp) (fun z hz => hball hz) hne0
      hball' hlast
    obtain ⟨ζ, ⟨hζl, hζ⟩, hζ'⟩ := (hfreq.and_eventually haTvan).exists
    exact hζ (hζ' hζl)
  · exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : IsInSpanAt (n := m + 1)
        (· = fun w => q w ^ j) y' h) => (j : ℕ∞)) k
      (isInSpanAt_of_eq_mul rfl hh' ha' hha') le_rfl

end LocalConstancy

/-! ### A point of the common strict transform at which both maps are unramified -/

section Generic

variable {n : ℕ} {Y₀ Y₁ Z : Type u}
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Every open set meeting a common strict transform `W` contains a point of `W` at which both
maps are local biholomorphisms (`W` is irreducible and not contained in the union of the two
exceptional loci). -/
theorem exists_unramified_point_mem {g₀ : Z → Y₀} {g₁ : Z → Y₁}
    (hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀)
    (hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁)
    (V₀ : ClosedIrreducibleAnalyticSubvariety n Y₀)
    (V₁ : ClosedIrreducibleAnalyticSubvariety n Y₁)
    (W : ClosedIrreducibleAnalyticSubvariety n Z)
    (hW₀ : W.carrier = strictTransform n g₀ V₀.carrier)
    (hW₁ : W.carrier = strictTransform n g₁ V₁.carrier) {O : Set Z} (hO : IsOpen O)
    (hWO : (W.carrier ∩ O).Nonempty) :
    ∃ z ∈ W.carrier ∩ O, z ∉ exceptionalLocus n g₀ ∧ z ∉ exceptionalLocus n g₁ := by
  by_contra hcon
  push Not at hcon
  have hsub : W.carrier ∩ O ⊆ exceptionalLocus n g₀ ∪ exceptionalLocus n g₁ := by
    intro z hz
    by_cases h0 : z ∈ exceptionalLocus n g₀
    · exact Or.inl h0
    · exact Or.inr (hcon z hz h0)
  have hall := StrictTransformLocus.subset_of_inter_isOpen_subset W
    (ConstantRankImage.IsComplexAnalyticSubset.union
      (HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hg₀)
      (HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hg₁))
    hO hWO hsub
  obtain ⟨z₁, hreg, h₀, h₁⟩ :=
    CommonStrictUnramifiedPoint.exists_common_regular_unramified_point hg₀ hg₁ V₀ V₁ W hW₀ hW₁
  rcases hall hreg.2.1 with h | h
  exacts [h₀ h, h₁ h]

end Generic

/-! ### Invariance of `ord_E(f)` along common-resolution witnesses -/

section Invariance

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- The divisor of a presentation is a smooth connected closed hypersurface. -/
theorem presentation_hypersurface (p : PrimePresentation (m + 1) X) :
    IsClosedConnectedSubmanifold (m + 1) p.divisor m := by
  have hdim : p.divisorDimension = m := by
    have h := p.codimension_one
    omega
  simpa only [hdim] using p.smooth

/-- The reversed common-resolution witness. -/
def commonResolutionSwap {p q : PrimePresentation (m + 1) X}
    (h : CommonResolutionGeometry p q) : CommonResolutionGeometry q p :=
  ⟨h.model, h.right, h.left, h.right_modification, h.left_modification, h.over_base.symm,
    h.strict_equal.symm⟩

/-- The two divisors and their common strict transform as irreducible analytic subvarieties. -/
theorem exists_common_carrier {p q : PrimePresentation (m + 1) X}
    (h : CommonResolutionGeometry p q) :
    ∃ (V₀ : ClosedIrreducibleAnalyticSubvariety (m + 1) p.model)
      (V₁ : ClosedIrreducibleAnalyticSubvariety (m + 1) q.model)
      (W : ClosedIrreducibleAnalyticSubvariety (m + 1) h.model),
      V₀.carrier = p.divisor ∧ V₁.carrier = q.divisor ∧
      W.carrier = strictTransform (m + 1) h.left V₀.carrier ∧
      W.carrier = strictTransform (m + 1) h.right V₁.carrier := by
  obtain ⟨V₀, hV₀, hd₀⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold
      (presentation_hypersurface p)
  obtain ⟨V₁, hV₁, -⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold
      (presentation_hypersurface q)
  obtain ⟨W, hW, -, -, -⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader
      h.left_modification V₀ (by rw [hd₀])
  have hstrict : strictTransform (m + 1) h.left V₀.carrier =
      strictTransform (m + 1) h.right V₁.carrier := by
    simpa only [hV₀, hV₁] using h.strict_equal
  exact ⟨V₀, V₁, W, hV₀, hV₁, hW, hW.trans hstrict⟩

/-- **`ord_E(f)` does not increase from one side of a common-resolution witness to the other.** -/
theorem germOrdE_le_of_commonResolution {p q : PrimePresentation (m + 1) X}
    (h : CommonResolutionGeometry p q) (x : X) {F : X → ℂ} (hF : HolomorphicAt (m + 1) F x) :
    germOrdE (m + 1) q.projection q.divisor x F ≤ germOrdE (m + 1) p.projection p.divisor x F := by
  classical
  obtain ⟨V₀, V₁, W, hV₀, hV₁, hW₀, hW₁⟩ := exists_common_carrier h
  have hEp := presentation_hypersurface p
  have hEq := presentation_hypersurface q
  have hcl₀ : W.carrier ⊆ h.left ⁻¹' p.divisor := by
    rw [hW₀, ← hV₀]
    exact closure_minimal sdiff_subset (V₀.isClosed_carrier.preimage h.left_modification.1.continuous)
  have hcl₁ : W.carrier ⊆ h.right ⁻¹' q.divisor := by
    rw [hW₁, ← hV₁]
    exact closure_minimal sdiff_subset (V₁.isClosed_carrier.preimage h.right_modification.1.continuous)
  have hbase : ∀ z, p.projection (h.left z) = q.projection (h.right z) := fun z =>
    congrFun h.over_base z
  refine le_iInf fun yp => ?_
  obtain ⟨y₀, hy₀E, hy₀x⟩ := yp
  -- a point of the strict transform over `y₀`, and its image `y₁ ∈ E₁` over `x`
  have himage := RawProperStrictTransformLelongReader.image_eq_of_strictTransform
    h.left_modification.1 h.left_modification.2.1 V₀ W hW₀
  have hy₀V : y₀ ∈ h.left '' W.carrier := by
    rw [himage, hV₀]
    exact hy₀E
  obtain ⟨z₀, hz₀W, hz₀y⟩ := hy₀V
  set y₁ := h.right z₀ with hy₁
  have hy₁E : y₁ ∈ q.divisor := hcl₁ hz₀W
  have hy₁x : q.projection y₁ = x := by rw [hy₁, ← hbase z₀, hz₀y, hy₀x]
  have hFp : HolomorphicAt (m + 1) (F ∘ p.projection) y₀ := by
    have hF' : HolomorphicAt (m + 1) F (p.projection y₀) := by rw [hy₀x]; exact hF
    exact hF'.comp_contMDiff (Eventually.of_forall fun _ => p.modification.1.contMDiffAt)
  have hFq : HolomorphicAt (m + 1) (F ∘ q.projection) y₁ := by
    have hF' : HolomorphicAt (m + 1) F (q.projection y₁) := by rw [hy₁x]; exact hF
    exact hF'.comp_contMDiff (Eventually.of_forall fun _ => q.modification.1.contMDiffAt)
  -- local constancy of the two orders near `y₀` and `y₁`
  obtain ⟨Ψ₀⟩ := DivisorFlattening.nonempty_of_regularAtDim (hEp.2.2 y₀ hy₀E)
  obtain ⟨Ψ₁⟩ := DivisorFlattening.nonempty_of_regularAtDim (hEq.2.2 y₁ hy₁E)
  obtain ⟨N₀, hN₀sub, hN₀o, hy₀N₀⟩ :=
    _root_.mem_nhds_iff.mp ((eventually_vanishingOrderAlong_eq Ψ₀ hFp).and hFp.eventually)
  obtain ⟨N₁, hN₁sub, hN₁o, hy₁N₁⟩ :=
    _root_.mem_nhds_iff.mp ((eventually_vanishingOrderAlong_eq Ψ₁ hFq).and hFq.eventually)
  set O : Set h.model := h.left ⁻¹' N₀ ∩ h.right ⁻¹' N₁ with hOdef
  have hOo : IsOpen O := (hN₀o.preimage h.left_modification.1.continuous).inter
    (hN₁o.preimage h.right_modification.1.continuous)
  have hz₀O : z₀ ∈ O := ⟨by change h.left z₀ ∈ N₀; rw [hz₀y]; exact hy₀N₀, hy₁N₁⟩
  -- a point of `W` near `z₀` at which both maps are unramified
  obtain ⟨z, ⟨hzW, hzO⟩, hz₀exc, hz₁exc⟩ := exists_unramified_point_mem
    h.left_modification.1 h.right_modification.1 V₀ V₁ W hW₀ hW₁ hOo ⟨z₀, hz₀W, hz₀O⟩
  have hzl : h.left z ∈ p.divisor := hcl₀ hzW
  have hzr : h.right z ∈ q.divisor := hcl₁ hzW
  obtain ⟨hord₀, hFpz⟩ := hN₀sub hzO.1
  obtain ⟨hord₁, hFqz⟩ := hN₁sub hzO.2
  replace hFpz : HolomorphicAt (m + 1) (F ∘ p.projection) (h.left z) := hFpz
  replace hFqz : HolomorphicAt (m + 1) (F ∘ q.projection) (h.right z) := hFqz
  -- at `z` the two orders agree
  have hO₀ := StrictTransformComposition.isOpen_compl_exceptionalLocus h.left_modification.1
  have hO₁ := StrictTransformComposition.isOpen_compl_exceptionalLocus h.right_modification.1
  have hiff₀ : ∀ w ∈ (exceptionalLocus (m + 1) h.left)ᶜ, w ∈ W.carrier ↔ h.left w ∈ p.divisor := by
    intro w hw
    rw [hW₀, RestrictedVolumePullbackLower.mem_strictTransform_iff
      h.left_modification.1.continuous V₀.isClosed_carrier hw, hV₀]
  have hiff₁ : ∀ w ∈ (exceptionalLocus (m + 1) h.right)ᶜ, w ∈ W.carrier ↔ h.right w ∈ q.divisor := by
    intro w hw
    rw [hW₁, RestrictedVolumePullbackLower.mem_strictTransform_iff
      h.right_modification.1.continuous V₁.isClosed_carrier hw, hV₁]
  have hWreg : RegularAtDim (n := m + 1) W.carrier z m :=
    RegularAtDimTransport.regularAtDim_of_preimage h.left_modification.1 hz₀exc hO₀ hz₀exc hiff₀
      (hEp.2.2 _ hzl)
  obtain ⟨Ω⟩ := DivisorFlattening.nonempty_of_regularAtDim hWreg
  obtain ⟨Φ₀⟩ := DivisorFlattening.nonempty_of_regularAtDim (hEp.2.2 _ hzl)
  obtain ⟨Φ₁⟩ := DivisorFlattening.nonempty_of_regularAtDim (hEq.2.2 _ hzr)
  have hsets₀ : ∀ᶠ w in 𝓝 z, w ∈ W.carrier ↔ h.left w ∈ p.divisor := by
    filter_upwards [hO₀.mem_nhds hz₀exc] with w hw
    exact hiff₀ w hw
  have hsets₁ : ∀ᶠ w in 𝓝 z, w ∈ W.carrier ↔ h.right w ∈ q.divisor := by
    filter_upwards [hO₁.mem_nhds hz₁exc] with w hw
    exact hiff₁ w hw
  have he₀ := UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional
    h.left_modification.1 hz₀exc Φ₀ Ω hsets₀ (F ∘ p.projection) hFpz
  have he₁ := UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional
    h.right_modification.1 hz₁exc Φ₁ Ω hsets₁ (F ∘ q.projection) hFqz
  have hsame : (F ∘ p.projection) ∘ h.left = (F ∘ q.projection) ∘ h.right := by
    funext w
    simp only [Function.comp_apply, hbase w]
  have hcongr := functionNormalOrder_congr Ω
    (hFpz.comp_contMDiff (Eventually.of_forall fun _ => h.left_modification.1.contMDiffAt))
    (hFqz.comp_contMDiff (Eventually.of_forall fun _ => h.right_modification.1.contMDiffAt))
    (Eventually.of_forall (congrFun hsame))
  calc germOrdE (m + 1) q.projection q.divisor x F
      ≤ vanishingOrderAlong (m + 1) q.divisor y₁ (F ∘ q.projection) :=
        iInf_le (fun w : {w // w ∈ q.divisor ∧ q.projection w = x} =>
          vanishingOrderAlong (m + 1) q.divisor w.val (F ∘ q.projection)) ⟨y₁, hy₁E, hy₁x⟩
    _ = vanishingOrderAlong (m + 1) q.divisor (h.right z) (F ∘ q.projection) := (hord₁ hzr).symm
    _ = functionNormalOrder Φ₁ (F ∘ q.projection) hFqz :=
        vanishingOrderAlong_eq_functionNormalOrder Φ₁ _ hFqz
    _ = functionNormalOrder Ω ((F ∘ q.projection) ∘ h.right) _ := he₁.symm
    _ = functionNormalOrder Ω ((F ∘ p.projection) ∘ h.left) _ := hcongr.symm
    _ = functionNormalOrder Φ₀ (F ∘ p.projection) hFpz := he₀
    _ = vanishingOrderAlong (m + 1) p.divisor (h.left z) (F ∘ p.projection) :=
        (vanishingOrderAlong_eq_functionNormalOrder Φ₀ _ hFpz).symm
    _ = vanishingOrderAlong (m + 1) p.divisor y₀ (F ∘ p.projection) := hord₀ hzl

/-- **`ord_E(f)` is invariant along common-resolution witnesses.** -/
theorem germOrdE_eq_of_commonResolution {p q : PrimePresentation (m + 1) X}
    (h : CommonResolutionGeometry p q) (x : X) {F : X → ℂ} (hF : HolomorphicAt (m + 1) F x) :
    germOrdE (m + 1) p.projection p.divisor x F = germOrdE (m + 1) q.projection q.divisor x F :=
  le_antisymm (germOrdE_le_of_commonResolution (commonResolutionSwap h) x hF)
    (germOrdE_le_of_commonResolution h x hF)

end Invariance

/-! ### `ord_E` on prime-divisor classes and `thm:valuativemulti` (2) on classes -/

section Classes

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- `ord_E(g)` of a stalk element is invariant along common-resolution witnesses. -/
theorem stalkOrdE_eq_of_commonResolution {p q : PrimePresentation (m + 1) X}
    (h : CommonResolutionGeometry p q) (x : X) (g : actualComplexStructureStalk (n := m + 1) x) :
    stalkOrdE p x g = stalkOrdE q x g := by
  obtain ⟨F, hF, hFg⟩ := exists_original_representative x g
  rw [(stalkOrdE_eq p x g F hF hFg).1, (stalkOrdE_eq q x g F hF hFg).1]
  exact germOrdE_eq_of_commonResolution h x hF

variable [CompactSpace X]

/-- **`ord_E(g)` on prime divisors over a compact manifold** (classes `PrimeOverCompact`). -/
def compactStalkOrdE (x : X) (g : actualComplexStructureStalk (n := m + 1) x) :
    RIsoAPrimeOver.PrimeOverCompact (m + 1) X → ℕ∞ :=
  Quot.lift (fun p => stalkOrdE p x g) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact stalkOrdE_eq_of_commonResolution h x g)

theorem compactStalkOrdE_mk (x : X) (g : actualComplexStructureStalk (n := m + 1) x)
    (p : PrimePresentation (m + 1) X) :
    compactStalkOrdE x g (Quot.mk commonResolutionRelation p) = stalkOrdE p x g := rfl

/-- **Source `thm:valuativemulti` (2) on prime-divisor classes** (compact `X`): one `ε > 0` with
`ord_E(g) ≥ (1 + ε) ν(φ, E) - A_X(E)` for every prime divisor `E` over `X` whose centre contains
`x`. -/
def CompactBookPrimeBound (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) (g : actualComplexStructureStalk (n := m + 1) x) (ε : ℝ) : Prop :=
  ∀ E : RIsoAPrimeOver.PrimeOverCompact (m + 1) X, x ∈ RIsoAPrimeOver.compactCenter E →
    ENNReal.ofReal (1 + ε) * RIsoAPrimeOver.compactReader φ hφ E ≤
      extendedOrderValue (compactStalkOrdE x g E) + (compactLogDiscrepancy E : ℝ≥0∞)

/-- The condition on classes is the condition on all representatives. -/
theorem compactBookPrimeBound_iff (φ : X → EReal)
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) (ε : ℝ) :
    CompactBookPrimeBound φ hφ x g ε ↔ BookPrimeBound φ x g ε := by
  constructor
  · intro hb p hp
    exact hb (Quot.mk commonResolutionRelation p) hp
  · intro hb E
    induction E using Quot.ind with
    | mk p => exact hb p

/-- **Source `thm:valuativemulti`, (1) ⟺ (2), with prime divisors over `X` as classes**
(compact `X` of positive dimension): `g ∈ 𝓘(φ)_x` iff there is `ε > 0` with
`ord_E(g) ≥ (1 + ε) ν(φ, E) - A_X(E)` for every prime divisor `E` over `X` (a class under common
resolutions) whose centre contains `x`. -/
theorem mem_multiplierIdeal_iff_compactBookPrimeBound {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x ↔
      ∃ ε : ℝ, 0 < ε ∧ CompactBookPrimeBound φ hφ x g ε := by
  simp only [compactBookPrimeBound_iff]
  exact mem_multiplierIdeal_iff_bookPrimeBound hφ x g

end Classes

end SGPT.PSH.ValMultClass
