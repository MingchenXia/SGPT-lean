import SGPT.Okounkov.TranscendentalExtensionThetaOn

/-!
# Gluing local extensions near a submanifold (DRWNXZ Theorem 6.1, Steps 4--5)

Blueprint `tok:ct-extension` (package EXT). Source: DRWNXZ, proof of Theorem 6.1; Xia,
*Foundations of pluripotential theory*, proof of `thm:holder-positive-potential-extension`,
Steps 4 and 5.

* `glue_near` (Step 4): let `T_j` be finitely many open sets, `W'_j ⊆ T_j` covering `Y`, and
  `g_j` `θ`-psh on `T_j`. Put `ψ(x) = max {g_l(x) : x ∈ T_l}` (`localMax`). If at every point `p`
  of `Y` lying on the boundary of `T_l` the branch `g_l` is dominated near `p` by every `g_j`
  with `p ∈ W'_j`, then near every point of `Y` the maximum is taken over the fixed finite set
  of indices `l` with `p ∈ T_l`; hence `ψ` is `θ`-psh on an open neighbourhood `W₀` of `Y`. If
  moreover `g_l ≤ φ` on `Y ∩ T_l` and `g_j = φ` on `Y ∩ W'_j`, then `ψ = φ` on `Y`.
* `glue_global` (Step 5): if `ψ` is `θ`-psh on an open neighbourhood of the closed set `Y` of
  a compact manifold and `F` is a `θ`-psh potential equal to `-∞` on `Y`, finite and continuous
  off `Y`, then for a constant `c` the function `max(ψ, F + c)` near `Y`, `F + c` elsewhere, is a
  `θ`-psh potential on the whole manifold (TN's collar gluing `isThetaPshPotential_gluedMax`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open Classical in
/-- `ψ(x) = max {g_l(x) : x ∈ T_l}` (DRWNXZ (6.3)); `⊥` if no `T_l` contains `x`. -/
def localMax {ι : Type*} [Fintype ι] (T : ι → Set M) (g : ι → M → EReal) (x : M) : EReal :=
  (Finset.univ.filter fun l => x ∈ T l).sup fun l => g l x

/-- **Step 4 of the gluing.** -/
theorem glue_near {ι : Type*} [Fintype ι] (θ : ClosedRealOneOneForm n M) {Y : Set M}
    (T W' : ι → Set M) (g : ι → M → EReal) (φY : M → EReal)
    (hT : ∀ j, IsOpen (T j)) (hW'T : ∀ j, W' j ⊆ T j) (hcover : Y ⊆ ⋃ j, W' j)
    (hg : ∀ j, ThetaPlurisubharmonicOn θ.val (g j) (T j))
    (hedge : ∀ p ∈ Y, ∀ l j, p ∈ frontier (T l) → p ∈ W' j → ∀ᶠ x in 𝓝 p, g l x ≤ g j x)
    (hle : ∀ y ∈ Y, ∀ l, y ∈ T l → g l y ≤ φY y)
    (heq : ∀ y ∈ Y, ∀ j, y ∈ W' j → g j y = φY y) :
    ∃ W₀ : Set M, IsOpen W₀ ∧ Y ⊆ W₀ ∧ ThetaPlurisubharmonicOn θ.val (localMax T g) W₀ ∧
      (∀ y ∈ Y, localMax T g y = φY y) ∧
      ∀ p ∈ W₀, ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∃ J : Finset ι, (∀ j ∈ J, O ⊆ T j) ∧
        ∀ x ∈ O, localMax T g x = J.sup fun j => g j x := by
  classical
  -- the set of points with a good neighbourhood
  let Good : Set M := {p | ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∃ J : Finset ι,
    (∀ j ∈ J, O ⊆ T j) ∧ ∀ x ∈ O, localMax T g x = J.sup fun j => g j x}
  have hGood_open : IsOpen Good := by
    rw [isOpen_iff_forall_mem_open]
    rintro p ⟨O, hO, hpO, J, hJ, hloc⟩
    exact ⟨O, fun x hx => ⟨O, hO, hx, J, hJ, hloc⟩, hO, hpO⟩
  have hYGood : Y ⊆ Good := by
    intro p hp
    obtain ⟨j₀, hj₀⟩ := mem_iUnion.mp (hcover hp)
    let L : Finset ι := Finset.univ.filter fun l => p ∈ T l
    have hj₀L : j₀ ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW'T j₀ hj₀⟩
    have hev : ∀ᶠ x in 𝓝 p, ∀ l, (p ∈ T l → x ∈ T l) ∧ (p ∉ closure (T l) → x ∉ closure (T l)) ∧
        (p ∈ frontier (T l) → g l x ≤ g j₀ x) := by
      refine Filter.eventually_all.2 fun l => ?_
      refine ((?_ : ∀ᶠ x in 𝓝 p, p ∈ T l → x ∈ T l).and
        ((?_ : ∀ᶠ x in 𝓝 p, p ∉ closure (T l) → x ∉ closure (T l)).and
          (?_ : ∀ᶠ x in 𝓝 p, p ∈ frontier (T l) → g l x ≤ g j₀ x)))
      · by_cases hpl : p ∈ T l
        · filter_upwards [(hT l).mem_nhds hpl] with x hx _ using hx
        · exact Eventually.of_forall fun x h => absurd h hpl
      · by_cases hpl : p ∈ closure (T l)
        · exact Eventually.of_forall fun x h => absurd hpl h
        · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hpl] with x hx _ using hx
      · by_cases hpl : p ∈ frontier (T l)
        · filter_upwards [hedge p hp l j₀ hpl hj₀] with x hx _ using hx
        · exact Eventually.of_forall fun x h => absurd h hpl
    obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp hev
    refine ⟨O, hO, hpO, L, fun l hl x hx => ((hOsub hx) l).1 (Finset.mem_filter.mp hl).2, ?_⟩
    intro x hx
    have hxl := hOsub hx
    apply le_antisymm
    · refine Finset.sup_le fun l hl => ?_
      have hxT : x ∈ T l := (Finset.mem_filter.mp hl).2
      by_cases hpT : p ∈ T l
      · exact Finset.le_sup (f := fun l => g l x) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpT⟩)
      · have hpcl : p ∈ closure (T l) := by
          by_contra hpcl
          exact (hxl l).2.1 hpcl (subset_closure hxT)
        have hpfr : p ∈ frontier (T l) := by
          rw [frontier, (hT l).interior_eq]
          exact ⟨hpcl, hpT⟩
        exact ((hxl l).2.2 hpfr).trans (Finset.le_sup (f := fun l => g l x) hj₀L)
    · refine Finset.sup_le fun l hl => ?_
      have hxT : x ∈ T l := (hxl l).1 (Finset.mem_filter.mp hl).2
      exact Finset.le_sup (f := fun l => g l x) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxT⟩)
  refine ⟨Good, hGood_open, hYGood, ?_, ?_, fun p hp => hp⟩
  · refine thetaPlurisubharmonicOn_of_locally_finset_sup (ι := ι) (b := g) θ fun p hp => ?_
    obtain ⟨O, hO, hpO, J, hJ, hloc⟩ := hp
    exact ⟨O, hO, hpO, J, fun j hj => thetaOn_mono (hg j) (hJ j hj), hloc⟩
  · intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hy)
    apply le_antisymm
    · exact Finset.sup_le fun l hl => hle y hy l (Finset.mem_filter.mp hl).2
    · rw [← heq y hy j hj]
      exact Finset.le_sup (f := fun l => g l y)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW'T j hj⟩)

/-- A `θ`-psh function on `univ` is `θ`-psh. -/
theorem thetaPlurisubharmonic_of_thetaOn_univ {θ : SmoothRealForm n M 2} {u : M → EReal}
    (h : ThetaPlurisubharmonicOn θ u univ) : ThetaPlurisubharmonic θ u :=
  fun e z hz => h e z hz (mem_univ _)

/-- A real constant shift of a `θ`-psh potential is a `θ`-psh potential. -/
theorem isThetaPshPotential_add_const {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (c : ℝ) :
    IsThetaPshPotential θ (fun x => u x + (c : EReal)) := by
  refine ⟨thetaPlurisubharmonic_of_thetaOn_univ
    (thetaOn_add_const (thetaOn_of_global hu.1 univ) c), ?_⟩
  intro x U hU hxU
  obtain ⟨y, hyU, hy⟩ := hu.2 x U hU hxU
  exact ⟨y, hyU, EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot c⟩⟩

/-- **Step 5 of the gluing.** -/
theorem glue_global [CompactSpace M] (θ : ClosedRealOneOneForm n M) {Y : Set M}
    (hY : IsClosed Y) {W₀ : Set M} (hW₀ : IsOpen W₀) (hYW₀ : Y ⊆ W₀) {ψ F : M → EReal}
    (hψ : ThetaPlurisubharmonicOn θ.val ψ W₀) (hF : IsThetaPshPotential θ.val F)
    (hFne : ∀ x ∉ Y, F x ≠ ⊥) (hFc : ContinuousOn F Yᶜ) :
    ∃ (U U' : Set M) (c : ℝ), IsOpen U ∧ IsOpen U' ∧ Y ⊆ U' ∧ closure U' ⊆ U ∧ U ⊆ W₀ ∧
      (∀ x ∈ U \ U', ψ x ≤ F x + (c : EReal)) ∧
      IsThetaPshPotential θ.val (gluedMax U ψ (fun x => F x + (c : EReal))) := by
  have hYc : IsCompact Y := hY.isCompact
  obtain ⟨U, hU, hYU, hUW, -⟩ := exists_open_between_and_isCompact_closure hYc hW₀ hYW₀
  obtain ⟨U', hU', hYU', hU'U, -⟩ := exists_open_between_and_isCompact_closure hYc hU hYU
  let K : Set M := closure U \ U'
  have hK : IsCompact K := (isClosed_closure.sdiff hU').isCompact
  have hKW : K ⊆ W₀ := fun x hx => hUW hx.1
  have hKY : K ⊆ Yᶜ := fun x hx hxY => hx.2 (hYU' hxY)
  obtain ⟨B, hB⟩ := thetaOn_exists_le_of_isCompact hψ hK hKW
  -- `F` is bounded below on `K`
  have hlow : ∃ b : ℝ, ∀ x ∈ K, (b : EReal) ≤ F x := by
    rcases K.eq_empty_or_nonempty with hKe | hne
    · exact ⟨0, fun x hx => by rw [hKe] at hx; exact absurd hx (notMem_empty x)⟩
    obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne (hFc.mono hKY)
    have hab : F a ≠ ⊥ := hFne a (hKY ha)
    have hat : F a ≠ ⊤ := hF.1.quasiPlurisubharmonic.ne_top a
    refine ⟨(F a).toReal, fun x hx => ?_⟩
    rw [EReal.coe_toReal hat hab]
    exact hmin hx
  obtain ⟨b, hb⟩ := hlow
  refine ⟨U, U', B - b, hU, hU', hYU', hU'U, hUW.trans' subset_closure, ?_, ?_⟩
  · intro x hx
    have hxK : x ∈ K := ⟨subset_closure hx.1, hx.2⟩
    calc ψ x ≤ (B : EReal) := hB x hxK
      _ = (b : EReal) + ((B - b : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; ring
      _ ≤ F x + ((B - b : ℝ) : EReal) := add_le_add_left (hb x hxK) _
  · refine QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax hU hU'U ?_
      (thetaOn_mono hψ (hUW.trans' subset_closure)) (isThetaPshPotential_add_const hF (B - b))
    intro x hx
    have hxK : x ∈ K := ⟨subset_closure hx.1, hx.2⟩
    calc ψ x ≤ (B : EReal) := hB x hxK
      _ = (b : EReal) + ((B - b : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; ring
      _ ≤ F x + ((B - b : ℝ) : EReal) := add_le_add_left (hb x hxK) _

end SGPT.Okounkov.TranscendentalExtension
