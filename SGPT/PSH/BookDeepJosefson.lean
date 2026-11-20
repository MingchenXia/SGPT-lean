import SGPT.PSH.Pluripolar
import SGPT.PSH.Components
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.FlatComplexTorus
import SGPT.Foundations.Analysis.Pending.FlatCurveRegularizerPotential
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Josefson's theorem on `ℂⁿ` (`thm:Josefson`)

Source: `thm:Josefson` of the chapter *Plurisubharmonic functions*: if `E ⊆ ℂⁿ` is
pluripolar (`def:pluripolarsets`), there is `φ ∈ PSH(ℂⁿ)` with `φ|_E ≡ -∞`.

The book refers to Guedj–Zeriahi (Cor. 4.41), where the Euclidean statement is deduced from the
global theory on a compact Kähler manifold. We use the same strategy with the flat compact
torus `T = ℂⁿ / Λ` of `SGPT.Foundations.Analysis.Pending.FlatComplexTorus` in place of `ℙⁿ`:

1. for a bounded pluripolar `E`, the set `p(E) ⊆ T` (`p : ℂⁿ → T` the projection) is
   pluripolar: near a point `y` only finitely many lattice translates of `E` meet a small ball,
   and the sum of the translated local witnesses is a local witness for `p⁻¹(p(E))`
   (`manifoldLocallyPluripolar_image_of_bounded`);
2. an arbitrary pluripolar `E ⊆ ℂⁿ` is the countable union of its bounded pieces, so `p(E)` is
   pluripolar by Lelong's countable union theorem on the compact Kähler manifold `T`
   (`PluripolarOuterCapacity.manifoldLocallyPluripolar_iUnion`), and the global capacity theory
   of Bedford–Taylor and Guedj–Zeriahi (`KahlerVolumePositive`) produces an `ω`-psh function `u`
   on `T` with `u = -∞` on `p(E)`;
3. `φ = u ∘ p + π |z|²` is psh on `ℂⁿ`: `π |z|²` is a potential of the flat Kähler form, and
   the translates of the charts of `T` cover `ℂⁿ` (`pshOn_pullback_add_flatPotential`).

Main declarations:

* `SGPT.PSH.BookDeepJosefson.manifoldLocallyPluripolar_image`;
* `SGPT.PSH.BookDeepJosefson.pshOn_pullback_add_flatPotential`;
* `SGPT.PSH.BookDeepJosefson.josefson` — `thm:Josefson`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.BookDeepJosefson

open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FlatComplexTorus
open scoped Topology ContDiff

variable {n : ℕ}

/-! ### Finite sums of plurisubharmonic germs -/

theorem plurisubharmonicAt_finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → ComplexModel n → EReal} {z : ComplexModel n}
    (hf : ∀ i ∈ s, PlurisubharmonicAt (f i) z) :
    PlurisubharmonicAt (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using plurisubharmonicAt_const (0 : EReal) EReal.zero_ne_top z
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem finset_sum_ne_bot {ι : Type*} (s : Finset ι) {f : ι → EReal}
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_bot_iff.mpr ⟨hf i (Finset.mem_insert_self i s),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)⟩

theorem finset_sum_eq_bot {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → EReal} {i : ι}
    (hi : i ∈ s) (hfi : f i = ⊥) : ∑ j ∈ s, f j = ⊥ := by
  rw [← Finset.add_sum_erase s f hi, hfi, EReal.bot_add]

theorem exists_pos_le_finset {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i, 0 < f i) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ i ∈ s, r ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_rfl, fun _ hi => absurd hi (Finset.notMem_empty _)⟩
  | insert i s _ ih =>
    obtain ⟨r, hr, hr1, hrs⟩ := ih
    refine ⟨min r (f i), lt_min hr (hf i), (min_le_left _ _).trans hr1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hrs j hj)

/-! ### Step 1: bounded pluripolar sets descend to the torus -/

/-- The period lattice as a set. -/
abbrev lattice (n : ℕ) : Set (ComplexModel n) :=
  ((periodLattice n : AddSubgroup (ComplexModel n)) : Set (ComplexModel n))

theorem isClosed_lattice : IsClosed (lattice n) := AddSubgroup.isClosed_of_discrete

theorem mem_lattice_of_proj_eq {a b : ComplexModel n} (h : proj n a = proj n b) :
    b - a ∈ lattice n := by
  have := QuotientAddGroup.eq.mp h
  simpa [sub_eq_neg_add] using this

theorem proj_sub_of_mem_lattice {a l : ComplexModel n} (hl : l ∈ lattice n) :
    proj n (a - l) = proj n a := by
  apply QuotientAddGroup.eq.mpr
  have : -(a - l) + a = l := by abel
  rw [this]
  exact hl

/-- Near every point of `ℂⁿ`, the union of the lattice translates of a bounded pluripolar set
is pluripolar: only finitely many translates meet a small ball, and the sum of the translated
witnesses is a witness. -/
theorem locallyPluripolarAt_preimage_image {E : Set (ComplexModel n)}
    (hE : LocallyPluripolarOn E univ) (hb : Bornology.IsBounded E) (y : ComplexModel n) :
    LocallyPluripolarAt (proj n ⁻¹' (proj n '' E)) y := by
  classical
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set F : Set (ComplexModel n) := closedBall 0 (‖y‖ + 1 + R) ∩ lattice n with hFdef
  have hFfin : F.Finite :=
    Metric.finite_isBounded_inter_isClosed (isDiscrete_periodLattice n) isBounded_closedBall
      isClosed_lattice
  set F' : Finset (ComplexModel n) := hFfin.toFinset with hF'def
  -- local witnesses at the points `y - l`
  have hloc : ∀ l : ComplexModel n, LocallyPluripolarAt E (y - l) := fun l => hE _ (mem_univ _)
  choose V u hVo hyV hVc hu hne hp using hloc
  have hrad : ∀ l, ∃ ρ > 0, ball (y - l) ρ ⊆ V l := fun l =>
    Metric.isOpen_iff.mp (hVo l) _ (hyV l)
  choose ρ hρ hρV using hrad
  obtain ⟨r, hr, hr1, hrF⟩ := exists_pos_le_finset F' hρ
  have hball : ∀ l ∈ F', ∀ w ∈ ball y r, w - l ∈ V l := by
    intro l hl w hw
    apply hρV l
    rw [mem_ball, dist_sub_right]
    exact (mem_ball.mp hw).trans_le (hrF l hl)
  set v : ComplexModel n → EReal := fun w => ∑ l ∈ F', u l (w - l) with hvdef
  refine ⟨ball y r, v, isOpen_ball, mem_ball_self hr, (convex_ball y r).isPreconnected,
    ?_, ?_, ?_⟩
  · -- the sum of the translated witnesses is plurisubharmonic
    intro w hw
    apply plurisubharmonicAt_finset_sum
    intro l hl
    have hdiff : DifferentiableOn ℂ (fun z : ComplexModel n => z - l) univ :=
      (differentiable_id.sub_const l).differentiableOn
    exact HolomorphicPullback.plurisubharmonicAt_comp_holomorphic isOpen_univ hdiff
      (mem_univ w) (hu l _ (hball l hl w hw))
  · -- a non-polar point: off the finitely many translated (null) pole sets
    set P : ComplexModel n → Set (ComplexModel n) := fun l =>
      (fun z => z - l) ⁻¹' ({z | u l z = ⊥} ∩ V l) with hPdef
    have hPnull : ∀ l, volume (P l) = 0 := by
      intro l
      have h0 : volume ({z | u l z = ⊥} ∩ V l) = 0 :=
        ((hu l).locallyPluripolarOn_poles (hVo l) (hVc l) (hne l)).measure_inter_eq_zero
          (hVo l) volume
      have : (fun z : ComplexModel n => z - l) = fun z => z + -l := by
        funext z; exact sub_eq_add_neg z l
      simp only [hPdef, this]
      rw [measure_preimage_add_right]
      exact h0
    have hN : volume (⋃ l ∈ F', P l) = 0 :=
      (measure_biUnion_null_iff (Finset.countable_toSet F')).mpr fun l _ => hPnull l
    have hpos : volume (ball y r \ ⋃ l ∈ F', P l) ≠ 0 := by
      rw [measure_sdiff_null hN]
      exact (measure_ball_pos volume y hr).ne'
    obtain ⟨w, hwb, hwN⟩ := nonempty_of_measure_ne_zero hpos
    refine ⟨w, hwb, finset_sum_ne_bot _ fun l hl => ?_⟩
    intro hbot
    exact hwN (mem_biUnion hl ⟨hbot, hball l hl w hwb⟩)
  · -- poles on the translates
    intro w hw hwE
    obtain ⟨e, he, hew⟩ := hwE
    have hl : w - e ∈ lattice n := mem_lattice_of_proj_eq hew
    have hlF : w - e ∈ F' := by
      rw [hF'def, Set.Finite.mem_toFinset]
      refine ⟨?_, hl⟩
      rw [mem_closedBall, dist_zero_right]
      have h1 : ‖e‖ ≤ R := by simpa using hR he
      have h2 : ‖w - y‖ < 1 := by
        rw [← dist_eq_norm]
        exact (mem_ball.mp hw).trans_le hr1
      calc ‖w - e‖ = ‖(w - y) + y - e‖ := by congr 1; abel
        _ ≤ ‖(w - y) + y‖ + ‖e‖ := norm_sub_le _ _
        _ ≤ ‖w - y‖ + ‖y‖ + ‖e‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ‖y‖ + 1 + R := by linarith
    apply finset_sum_eq_bot hlF
    have hwe : w - (w - e) = e := by abel
    rw [hwe]
    exact hp (w - e) e (by simpa [hwe] using hball _ hlF w hw) he

/-- The image in the torus of a bounded pluripolar subset of `ℂⁿ` is pluripolar. -/
theorem manifoldLocallyPluripolar_image_of_bounded {E : Set (ComplexModel n)}
    (hE : LocallyPluripolarOn E univ) (hb : Bornology.IsBounded E) :
    ManifoldLocallyPluripolar (n := n) (proj n '' E) := by
  intro e z _
  refine (locallyPluripolarAt_preimage_image hE hb z).mono ?_
  rintro w ⟨-, hw⟩
  change e.val.symm w ∈ proj n '' E at hw
  rwa [coe_symm_of_mem_atlas e.property] at hw

/-- **Step 2.** The image in the torus of an arbitrary pluripolar subset of `ℂⁿ` is pluripolar
(Lelong's countable union theorem on the compact Kähler torus). -/
theorem manifoldLocallyPluripolar_image (hn : 0 < n) {E : Set (ComplexModel n)}
    (hE : LocallyPluripolarOn E univ) :
    ManifoldLocallyPluripolar (n := n) (proj n '' E) := by
  borelize (Torus n)
  have hU : E = ⋃ k : ℕ, E ∩ closedBall 0 k := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := exists_nat_ge ‖z‖
      exact ⟨k, hz, hk⟩
    · rintro ⟨_, hz, _⟩
      exact hz
  rw [hU, image_iUnion]
  exact PluripolarOuterCapacity.manifoldLocallyPluripolar_iUnion hn (flatKahlerBackground n)
    fun k => manifoldLocallyPluripolar_image_of_bounded (hE.mono_set inter_subset_left)
      (isBounded_closedBall.subset inter_subset_right)

/-! ### Step 3: pulling back torus potentials -/

/-- `π |z - a|²` is a potential of the flat Kähler form, at every point and for every centre. -/
theorem smoothDDC_pi_norm_sub_sq (a w : ComplexModel n) :
    smoothDDC (fun y => Real.pi * ‖y - a‖ ^ 2) w = LocalProductCurrents.kahlerForm n := by
  have hs : ContDiffOn ℝ ∞ (fun y : ComplexModel n => ‖y - a‖ ^ 2) univ :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
  have h := smoothDDC_smul isOpen_univ hs Real.pi (mem_univ w)
  simp only [smul_eq_mul] at h
  rw [h, LocalBedfordTaylorCollar.smoothDDC_norm_sub_sq, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero,
    one_smul]

/-- **Step 3.** If `u` is `ω`-psh on the flat torus, then `u ∘ p + π |z|²` is psh on `ℂⁿ`. -/
theorem pshOn_pullback_add_flatPotential {u : Torus n → EReal}
    (hu : IsThetaPshPotential (flatKahlerBackground n).form.val u) :
    SGPT.PSH.PSHOn (fun z => u (proj n z) + ((Real.pi * ‖z‖ ^ 2 : ℝ) : EReal)) univ := by
  set G : ComplexModel n → EReal := fun z => u (proj n z) + ((Real.pi * ‖z‖ ^ 2 : ℝ) : EReal)
    with hGdef
  have hloc : ∀ z, PlurisubharmonicAt G z := by
    intro z
    set q : Torus n := proj n z
    set c := chartAt (ComplexModel n) q
    have hc : c ∈ atlas (ComplexModel n) (Torus n) := chart_mem_atlas _ q
    set e : ComplexChart n (Torus n) := ⟨c, hc⟩
    have hz' : c q ∈ c.target := mem_chart_target _ q
    have hpz' : proj n (c q) = q := by
      have h := c.left_inv (mem_chart_source _ q)
      rwa [coe_symm_of_mem_atlas hc] at h
    set l : ComplexModel n := z - c q with hldef
    have hl : l ∈ lattice n := mem_lattice_of_proj_eq hpz'
    obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu.1 e (c q) hz'
    have hσ := (FlatCurveRegularizerPotential.isSmoothLocalPotential_flat e).mono hρ.1 hρ.2.1
    have hpsh' :=
      (FirstPass.smoothLocalPotential_psh_iff _ e W ρ _ hρ hσ (chartFunction u e)).mp hpsh
    have hG' : PlurisubharmonicAt G (c q) := by
      refine (hpsh' (c q) hzW).congr (Eventually.of_forall fun y => ?_)
      simp only [hGdef, chartFunction]
      rw [show e.val.symm y = proj n y by
        rw [show e.val = c from rfl, coe_symm_of_mem_atlas hc]]
    have hdiff : DifferentiableOn ℂ (fun w : ComplexModel n => w - l) univ :=
      (differentiable_id.sub_const l).differentiableOn
    have hzl : z - l = c q := by rw [hldef]; abel
    have htr : PlurisubharmonicAt (fun w => G (w - l)) z :=
      HolomorphicPullback.plurisubharmonicAt_comp_holomorphic isOpen_univ hdiff (mem_univ z)
        (by rw [hzl]; exact hG')
    set A : ComplexModel n → ℝ := fun w => Real.pi * ‖w‖ ^ 2 - Real.pi * ‖w - l‖ ^ 2 with hAdef
    have hs : ∀ a : ComplexModel n,
        ContDiffOn ℝ ∞ (fun y : ComplexModel n => Real.pi * ‖y - a‖ ^ 2) univ := fun a =>
      (contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).contDiffOn
    have hAs : ContDiffOn ℝ ∞ A univ := by
      have := (hs 0).sub (hs l)
      simpa only [sub_zero] using this
    have hAddc : ∀ w ∈ univ, smoothDDC A w = 0 := by
      intro w _
      have h := PositiveClasses.smoothDDC_sub isOpen_univ (hs 0) (hs l) (mem_univ w)
      simp only [sub_zero] at h
      rw [hAdef, h, smoothDDC_pi_norm_sub_sq l w]
      have h0 := smoothDDC_pi_norm_sub_sq (0 : ComplexModel n) w
      simp only [sub_zero] at h0
      rw [h0, sub_self]
    have hA : PlurisubharmonicAt (fun w => (A w : EReal)) z :=
      plurisubharmonicOn_coe_of_smoothDDC_eq_zero isOpen_univ hAs hAddc z (mem_univ z)
    refine (htr.add hA).congr (Eventually.of_forall fun w => ?_)
    simp only [hGdef, hAdef]
    rw [proj_sub_of_mem_lattice hl]
    exact corrected_add_sub _ _ _
  refine ⟨SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn fun z _ => hloc z, ?_⟩
  obtain ⟨y, -, hy⟩ := hu.2 0 univ isOpen_univ (mem_univ _)
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨z, mem_univ z, EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot _⟩⟩

/-! ### Josefson's theorem -/

/-- **`thm:Josefson`.** Every pluripolar subset `E` of `ℂⁿ` (in the sense of
`def:pluripolarsets`, for the identity atlas of `ℂⁿ`) is contained in the pole set of a single
`φ ∈ PSH(ℂⁿ)`. -/
theorem josefson {E : Set (ComplexModel n)}
    (hE : (SGPT.PSH.VariableComplexAtlas.identityAtlas n).LocallyPluripolar E) :
    ∃ φ : ComplexModel n → EReal, SGPT.PSH.PSHOn φ univ ∧ ∀ z ∈ E, φ z = ⊥ := by
  have hE' : LocallyPluripolarOn E univ := by
    have h := hE.in_chart ()
    have hset : (SGPT.PSH.VariableComplexAtlas.identityAtlas n).pluripolarChartSet E () = E := by
      ext z
      exact ⟨fun hz => hz.2, fun hz => ⟨mem_univ z, hz⟩⟩
    rw [hset] at h
    exact h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- in dimension zero every pluripolar set is empty
    refine ⟨fun _ => ((0 : ℝ) : EReal), SGPT.PSH.pshOn_real_const 0 univ_nonempty, ?_⟩
    intro z hz
    obtain ⟨V, u, -, hzV, -, -, ⟨a, haV, hua⟩, hp⟩ := hE' z (mem_univ z)
    have ha : a = z := by
      ext i
      exact i.elim0
    exact absurd (hp z hzV hz) (ha ▸ hua)
  · borelize (Torus n)
    obtain ⟨uT, huT, hpoles⟩ :=
      KahlerVolumePositive.exists_isThetaPshPotential_poles_of_outerCapacityZero' hn
        (flatKahlerBackground n)
        (PluripolarOuterCapacity.outerCapacityZero_of_manifoldLocallyPluripolar _
          (manifoldLocallyPluripolar_image hn hE'))
    refine ⟨_, pshOn_pullback_add_flatPotential huT, fun z hz => ?_⟩
    rw [hpoles _ (mem_image_of_mem _ hz), EReal.bot_add]

end SGPT.PSH.BookDeepJosefson
