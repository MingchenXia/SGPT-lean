import SGPT.Okounkov.TranscendentalExtensionGluing
import SGPT.Okounkov.TranscendentalExtensionCompare
import SGPT.Okounkov.TranscendentalExtensionPieces
import SGPT.Okounkov.TranscendentalExtensionAnalytic
import SGPT.Foundations.Analysis.Pending.CompactCollarCutoff
import SGPT.Foundations.Analysis.Pending.KahlerCurrentMax

/-!
# Extension of Kähler currents from a submanifold (DRWNXZ Theorem 6.1)

Blueprint `tok:ct-extension` (package EXT); source: the book's `thm:CT-thm-refined'`, DRWNXZ
Theorem 6.1, Xia, *Foundations of pluripotential theory*,
`thm:holder-positive-potential-extension`.

`exists_extension_of_normalPole`: let `X` be a compact complex manifold with a Kähler form `ω`,
`Y ⊆ X` a closed connected submanifold of dimension `k` carrying a normal pole `F`
(`IsNormalPole`, blueprint `tok:ext-pole`), and `φ : Y → [-∞, ∞)` with `ω|_Y + dd^c φ` a Kähler
current and `e^φ` Hölder continuous. Then there are `φ̃` and `ε > 0` with
`φ̃ ∈ PSH(X, (1 - ε) ωX)` (so `ω + dd^c φ̃ ≥ ε ω`), `φ̃|_Y = φ`, `φ̃` finite and continuous on
`X \ Y`, and `φ̃` has analytic singularities when `φ` has.

The proof follows FPT/DRWNXZ: margin `ω|_Y + dd^c φ ≥ δ ω|_Y`; a rational `s` with `2s < α` and
`sB ≤ δ/2` (`B ωX + dd^c F ≥ 0`); at every point `p ∈ Y` a flattening chart `G_p`, a local potential
`ρ_p` of `ω`, and the branch `b_p = max(φ ∘ π_p, sF) + c(ρ_p ∘ π_p - ρ_p)`, `c = 1 - δ`
(`TranscendentalExtensionLocal`), which is `(sB + c) ω`-psh near `p`; nested open sets
`A_p ⋐ T'_p ⋐ T_p` and a cut-off `ρc_p ∈ [-1, 0]` equal to `0` near `A_p` and `-1` off `T'_p`
(TN's `exists_chartSmooth_collar_ddc_lower`); finitely many `A_p` cover `Y`; the branches
`g_p = b_p + η ρc_p` are glued near `Y` (`glue_near`; the edge condition is the comparison
`eventually_max_retr_le`), and the result is globalized with `sF + c₀` (`glue_global`).

The conditional theorems `hasKahlerCurrentExtension_of_normalPole` and
`hasContinuousKahlerCurrentExtension_of_normalPole` assume the pole (package POLE); they are
**conditional** on `IsNormalPole` / `NormalPoleStatement` and are labelled as such.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

/-! ### Small lemmas -/

theorem ereal_add_coe_le {a b : EReal} {v r t : ℝ} (hab : a ≤ b + (v : EReal))
    (h : v + r ≤ t) : a + (r : EReal) ≤ b + (t : EReal) := by
  calc a + (r : EReal) ≤ (b + (v : EReal)) + r := add_le_add_left hab _
    _ = b + ((v + r : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
    _ ≤ b + t := add_le_add_right (EReal.coe_le_coe_iff.mpr h) _

theorem continuousAt_add_coe {Z : Type*} [TopologicalSpace Z] {f : Z → EReal} {h : Z → ℝ}
    {x : Z} (hf : ContinuousAt f x) (hh : ContinuousAt h x) :
    ContinuousAt (fun z => f z + (h z : EReal)) x :=
  (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
    (hf.prodMk (continuous_coe_real_ereal.continuousAt.comp hh))

theorem continuousAt_finset_sup' {Z ι : Type*} [TopologicalSpace Z] (J : Finset ι)
    {g : ι → Z → EReal} {x : Z} (hg : ∀ j ∈ J, ContinuousAt (g j) x) :
    ContinuousAt (fun z => J.sup fun j => g j z) x := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | insert a J ha ih =>
      simp only [Finset.sup_insert]
      exact (hg a (Finset.mem_insert_self a J)).max
        (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem coe_mul_ne_bot {s : ℝ} (hs : 0 < s) {a : EReal} (ha : a ≠ ⊥) : (s : EReal) * a ≠ ⊥ := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top => rw [EReal.coe_mul_top_of_pos hs]; exact top_ne_bot
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Local data at a point of `Y` -/

theorem exists_localData [CompactSpace X] (ωX : KahlerBackground n X) {Y : Set X} {k : ℕ} (hk : k ≤ n)
    (hY : ∀ x ∈ Y, RegularAtDim (n := n) Y x k) (p : X) (hp : p ∈ Y) :
    ∃ (G : FlatData n k X Y) (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
      (A T' T : Set X),
      IsSmoothLocalPotential ωX.form.val G.amb W ρ ∧ IsOpen A ∧ p ∈ A ∧ IsOpen T' ∧ IsOpen T ∧
        closure A ⊆ T' ∧ closure T' ⊆ T ∧ closure T ⊆ localDomain G W ∧
        IsCompact (closure A) := by
  let G := FlatData.ofRegularAtDim (hY p hp)
  have hpG : p ∈ G.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hY p hp)
  obtain ⟨W, ρ, hpW, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials ωX.form G.amb
    (G.amb.val p) (G.amb.val.map_source hpG.1)
  have hΩ : IsOpen (localDomain G W) := isOpen_localDomain G hρ.1
  have hpΩ : p ∈ localDomain G W := mem_localDomain_of_mem hk G hp hpG hpW
  obtain ⟨T, hT, hpT, hTΩ, -⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hΩ (singleton_subset_iff.mpr hpΩ)
  obtain ⟨T', hT', hpT', hT'T, -⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hT hpT
  obtain ⟨A, hA, hpA, hAT', hAc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hT' hpT'
  exact ⟨G, W, ρ, A, T', T, hρ, hA, singleton_subset_iff.mp hpA, hT', hT, hAT', hT'T, hTΩ, hAc⟩

/-! ### The extension -/

/-- **DRWNXZ Theorem 6.1 (conditional on the pole)**: see the module docstring. -/
theorem exists_extension_of_normalPole [CompactSpace X] (ωX : KahlerBackground n X) {Y : Set X}
    {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k) {F : X → EReal}
    (hF : IsNormalPole ωX Y k F) (φ : Y → EReal)
    (hKah : letI := submanifoldCharts hY
      haveI := submanifold_isComplexManifold hY
      IsKahlerCurrentPotential (restrictedKahler ωX hY).form φ)
    (hHol : letI := submanifoldCharts hY
      IsChartHolder (k := k) (expPotential φ)) :
    ∃ φ' : X → EReal, ∃ ε : ℝ, 0 < ε ∧ IsThetaPshPotential ((1 - ε) • ωX.form).val φ' ∧
      (∀ y : Y, φ' y = φ y) ∧ ContinuousOn φ' Yᶜ ∧ (∀ x ∉ Y, φ' x ≠ ⊥) ∧
      ((letI := submanifoldCharts hY
        HasManifoldAnalyticSingularityType (n := k) φ) →
        HasManifoldAnalyticSingularityType (n := n) φ') := by
  classical
  let _ := submanifoldCharts hY
  have _ := submanifold_isComplexManifold hY
  have hk : k ≤ n := le_of_isClosedConnectedSubmanifold hY
  have hreg := hY.2.2
  have _ : CompactSpace Y := isCompact_iff_compactSpace.mp hY.1.isCompact
  -- the margin, the Hölder exponent and the pole constant
  obtain ⟨δ, hδ0, hδ1, hφδ⟩ := exists_margin_of_isKahlerCurrentPotential (restrictedKahler ωX hY) hKah
  obtain ⟨α, hα0, -, hαH⟩ := hHol
  obtain ⟨B, hB0, hFB⟩ := hF.thetaPsh
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℚ, (0 : ℝ) < s ∧ (s : ℝ) < min (α / 2) (δ / (2 * (B + 1))) :=
    exists_rat_btwn (lt_min (by positivity) (by positivity))
  set sR : ℝ := (s : ℝ) with hsR
  have hsα : 2 * sR < α := by linarith [min_le_left (α / 2) (δ / (2 * (B + 1)))]
  have hsB : sR * B ≤ δ / 2 := by
    have h1 : sR < δ / (2 * (B + 1)) := hs.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  set c : ℝ := 1 - δ with hc
  have hc0 : 0 ≤ c := by linarith
  have hφtop : ∀ y, φ y ≠ ⊤ := fun y => hφδ.1.quasiPlurisubharmonic.ne_top y
  have hFtop : ∀ x, F x ≠ ⊤ := fun x => hFB.1.quasiPlurisubharmonic.ne_top x
  have hφc : ThetaPlurisubharmonic
      (c • ClosedRealOneOneForm.pullback (contMDiff_val hk hreg) ωX.form).val φ := hφδ.1
  have hφcont : Continuous φ :=
    continuous_of_continuous_expPotential hφtop (IsChartHolderWith.continuous hα0 hαH)
  -- the scaled pole
  let Fs : X → EReal := fun x => (sR : EReal) * F x
  have hFs : IsThetaPshPotential ((sR * B) • ωX.form).val Fs := by
    have h := isThetaPshPotential_const_mul hFB hs0
    rwa [smul_smul] at h
  have hFsY : ∀ y ∈ Y, Fs y = ⊥ := fun y hy => by
    simp only [Fs, (hF.eq_bot_iff y).mpr hy, EReal.coe_mul_bot_of_pos hs0]
  have hFsne : ∀ x ∉ Y, Fs x ≠ ⊥ := fun x hx =>
    coe_mul_ne_bot hs0 fun h => hx ((hF.eq_bot_iff x).mp h)
  have hFcont : ∀ x ∉ Y, ContinuousAt F x := fun x hx =>
    hF.continuousOn.continuousAt (hY.1.isOpen_compl.mem_nhds hx)
  have hFscont : ∀ x ∉ Y, ContinuousAt Fs x := fun x hx =>
    (continuous_const_mul_ereal hs0).continuousAt.comp (hFcont x hx)
  -- local data at the points of `Y`
  choose G W ρ A T' T hρ hA hpA hT' hT hAT' hT'T hTΩ hAc using
    fun p : Y => exists_localData ωX hk hreg p.1 p.2
  choose ρc hρc hρc_low hρc_up hρc_N hρc_off C hC hsemi using
    fun p : Y => CompactCollarCutoff.exists_chartSmooth_collar_ddc_lower ωX (hAc p) (hT' p)
      (hAT' p)
  -- a finite subcover
  obtain ⟨t, ht⟩ := hY.1.isCompact.elim_finite_subcover (fun p : Y => A p) (fun p => hA p)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hpA ⟨y, hy⟩⟩)
  set Csum : ℝ := ∑ i ∈ t, C i with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun i _ => (hC i).le
  set η : ℝ := δ / 4 / (1 + Csum) with hη
  have hη0 : 0 < η := by positivity
  have hηC : ∀ i : t, η * C i.1 ≤ δ / 4 := by
    intro i
    have hle : C i.1 ≤ 1 + Csum := by
      have := Finset.single_le_sum (f := C) (fun j _ => (hC j).le) i.2
      linarith
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- the branches
  let corr : Y → X → ℝ := fun p => localCorrection (G p) (ρ p) c
  let b : Y → X → EReal := fun p x => max (φ (retr (G p) x)) (Fs x) + (corr p x : EReal)
  let g : t → X → EReal := fun i x => b i.1 x + ((η * ρc i.1 x : ℝ) : EReal)
  have hcorr_cont : ∀ p : Y, ContinuousOn (corr p) (localDomain (G p) (W p)) := fun p =>
    continuousOn_localCorrection (G p) (hρ p).2.2.1.continuousOn c
  have hb : ∀ p : Y, ThetaPlurisubharmonicOn ((sR * B + c) • ωX.form).val (b p)
      (localDomain (G p) (W p)) := by
    intro p
    have h1 := thetaOn_localExt hk hreg ωX.form (G p) (hρ p) c hφc
    have h2 := thetaOn_localCorrection hk hreg ωX.form ωX.isSemipositive (G p) (hρ p) hc0
    have h3 : ThetaPlurisubharmonicOn ((sR * B) • ωX.form).val Fs (localDomain (G p) (W p)) :=
      thetaOn_of_global hFs.1 _
    have h4 := thetaOn_add_smul ωX h3 h2
    have h5 := thetaOn_mono_smul ωX (show c ≤ sR * B + c by nlinarith) h1
    have h6 := thetaOn_max h5 h4
    refine thetaOn_congr (isOpen_localDomain _ (hρ p).1) h6 fun x _ => ?_
    exact max_add_add_right _ _ _
  set θs : ClosedRealOneOneForm n X := (1 - δ / 4) • ωX.form with hθs
  have hg : ∀ i : t, ThetaPlurisubharmonicOn θs.val (g i) (T i.1) := by
    intro i
    have h1 := thetaOn_mono (hb i.1) (subset_closure.trans (hTΩ i.1))
    have h2 : ThetaPlurisubharmonicOn ((η * C i.1) • ωX.form).val
        (fun x => ((η * ρc i.1 x : ℝ) : EReal)) (T i.1) :=
      thetaOn_of_global (IdealFunctionMaxGluing.thetaPlurisubharmonic_const_mul_of_ddc_lower ωX
        (hρc i.1) hη0.le (hsemi i.1)) _
    have h3 := thetaOn_add_smul ωX h1 h2
    exact thetaOn_mono_smul ωX (by linarith [hηC i]) h3
  -- values on `Y`
  have hbY : ∀ p : Y, ∀ y (hy : y ∈ Y), y ∈ localDomain (G p) (W p) → b p y = φ ⟨y, hy⟩ := by
    intro p y hy hyΩ
    simp only [b, corr, retr_of_mem hk (G p) hy hyΩ.1.1, hFsY y hy,
      localCorrection_of_mem hk (G p) (ρ p) c hy hyΩ.1.1, max_bot_right, EReal.coe_zero, add_zero]
  let φY : X → EReal := fun x => if h : x ∈ Y then φ ⟨x, h⟩ else ⊥
  -- gluing near `Y`
  obtain ⟨W₀, hW₀, hYW₀, hψ, hψY, hloc⟩ := glue_near θs (fun i : t => T i.1) (fun i : t => A i.1)
    g φY (fun i => hT i.1) (fun i => subset_closure.trans ((hAT' i.1).trans
      (subset_closure.trans (hT'T i.1))))
    (fun y hy => by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht hy)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩)
    hg
    (by
      -- the edge condition, from the comparison of local extensions
      intro y hy l j hyl hyj
      have hyTl : y ∈ closure (T l.1) := frontier_subset_closure hyl
      have hyΩl : y ∈ localDomain (G l.1) (W l.1) := hTΩ l.1 hyTl
      have hyΩj : y ∈ localDomain (G j.1) (W j.1) :=
        hTΩ j.1 (subset_closure ((hT'T j.1) (subset_closure ((hAT' j.1) (subset_closure hyj)))))
      have hyamb_l : y ∈ (G l.1).ambSource := hyΩl.1.1
      have hyamb_j : y ∈ (G j.1).ambSource := hyΩj.1.1
      obtain ⟨CF, hCF, hlow⟩ := hF.lower (G l.1) y hy hyamb_l
      have hcmp := eventually_max_retr_le hk hreg (G l.1) (G j.1) hy hyamb_l hyamb_j hφtop hαH
        hFtop hCF hlow hs0 hsα (η := η / 4) (by positivity)
      -- the corrections are small near `y`
      have hcl : ContinuousAt (corr l.1) y :=
        (hcorr_cont l.1).continuousAt ((isOpen_localDomain _ (hρ l.1).1).mem_nhds hyΩl)
      have hcj : ContinuousAt (corr j.1) y :=
        (hcorr_cont j.1).continuousAt ((isOpen_localDomain _ (hρ j.1).1).mem_nhds hyΩj)
      have hcl0 : corr l.1 y = 0 := localCorrection_of_mem hk (G l.1) (ρ l.1) c hy hyamb_l
      have hcj0 : corr j.1 y = 0 := localCorrection_of_mem hk (G j.1) (ρ j.1) c hy hyamb_j
      have hsl : ∀ᶠ x in 𝓝 y, corr l.1 x < η / 8 :=
        hcl.eventually (gt_mem_nhds (by rw [hcl0]; positivity))
      have hsj : ∀ᶠ x in 𝓝 y, -(η / 8) < corr j.1 x :=
        hcj.eventually (lt_mem_nhds (by rw [hcj0]; linarith))
      -- the cut-offs near `y`
      have hyT' : y ∉ closure (T' l.1) := fun h => by
        have := (hT'T l.1) h
        rw [frontier, (hT l.1).interior_eq] at hyl
        exact hyl.2 this
      have hρl : ∀ᶠ x in 𝓝 y, ρc l.1 x = -1 := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hyT'] with x hx
        exact hρc_off l.1 x fun h => hx (subset_closure h)
      obtain ⟨N, hN, hAN, hNz⟩ := hρc_N j.1
      have hρj : ∀ᶠ x in 𝓝 y, ρc j.1 x = 0 := by
        filter_upwards [hN.mem_nhds (hAN (subset_closure hyj))] with x hx using hNz x hx
      filter_upwards [hcmp, hsl, hsj, hρl, hρj] with x hx hxl hxj hxρl hxρj
      simp only [g, b, hxρl, hxρj]
      rw [add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add]
      refine ereal_add_coe_le hx ?_
      linarith)
    (by
      intro y hy l hyl
      have hyΩ : y ∈ localDomain (G l.1) (W l.1) := hTΩ l.1 (subset_closure hyl)
      simp only [g, hbY l.1 y hy hyΩ, φY, dif_pos hy]
      have : (η * ρc l.1 y : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hη0.le (hρc_up l.1 y)
      calc φ ⟨y, hy⟩ + ((η * ρc l.1 y : ℝ) : EReal) ≤ φ ⟨y, hy⟩ + ((0 : ℝ) : EReal) :=
            add_le_add_right (EReal.coe_le_coe_iff.mpr this) _
        _ = φ ⟨y, hy⟩ := by rw [EReal.coe_zero, add_zero])
    (by
      intro y hy j hyj
      have hyΩ : y ∈ localDomain (G j.1) (W j.1) :=
        hTΩ j.1 (subset_closure ((hT'T j.1) (subset_closure ((hAT' j.1) (subset_closure hyj)))))
      obtain ⟨N, hN, hAN, hNz⟩ := hρc_N j.1
      simp only [g, hbY j.1 y hy hyΩ, φY, dif_pos hy, hNz y (hAN (subset_closure hyj)),
        mul_zero, EReal.coe_zero, add_zero])
  set ψ := localMax (fun i : t => T i.1) g with hψdef
  -- globalization
  have hFsθ : IsThetaPshPotential θs.val Fs :=
    isThetaPshPotential_mono_smul ωX (by linarith) hFs
  have hFsc : ContinuousOn Fs Yᶜ := fun x hx => (hFscont x hx).continuousWithinAt
  obtain ⟨U, U', c₀, hU, hU', hYU', hU'U, hUW₀, hcollar, hφ'⟩ :=
    glue_global θs hY.1 hW₀ hYW₀ hψ hFsθ hFsne hFsc
  let G' : X → EReal := fun x => Fs x + (c₀ : EReal)
  refine ⟨gluedMax U ψ G', δ / 4, by positivity, hφ', ?_, ?_, ?_, ?_⟩
  · -- the restriction to `Y`
    intro y
    have hyU : (y : X) ∈ U := hU'U (subset_closure (hYU' y.2))
    rw [gluedMax_eq_max hyU, hψY y y.2]
    simp only [G', φY, dif_pos y.2, hFsY y y.2, EReal.bot_add, max_bot_right]
  · -- continuity off `Y`
    -- the branches are continuous off `Y`
    have hgc : ∀ i : t, ∀ x ∈ T i.1, x ∉ Y → ContinuousAt (g i) x := by
      intro i x hxT hxY
      have hxΩ := hTΩ i.1 (subset_closure hxT)
      have hr : ContinuousAt (retr (G i.1)) x :=
        (continuousOn_retr _).continuousAt ((isOpen_retrDomain _).mem_nhds hxΩ.1)
      have h1 : ContinuousAt (fun z => max (φ (retr (G i.1) z)) (Fs z)) x :=
        (hφcont.continuousAt.comp hr).max (hFscont x hxY)
      have h2 := continuousAt_add_coe h1
        ((hcorr_cont i.1).continuousAt ((isOpen_localDomain _ (hρ i.1).1).mem_nhds hxΩ))
      exact continuousAt_add_coe h2
        (continuous_const.mul (KahlerCurrentMax.continuous_of_chartSmooth (hρc i.1))).continuousAt
    have hψc : ∀ x ∈ W₀, x ∉ Y → ContinuousAt ψ x := by
      intro x hx hxY
      obtain ⟨O, hO, hxO, J, hJ, hψO⟩ := hloc x hx
      have h := continuousAt_finset_sup' J fun j hj => hgc j x (hJ j hj hxO) hxY
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [hO.mem_nhds hxO] with z hz
      exact hψO z hz
    have hG'c : ∀ x ∉ Y, ContinuousAt G' x := fun x hx =>
      continuousAt_add_coe (hFscont x hx) continuousAt_const
    intro x hxY
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hxU : x ∈ U
    · have hm : ContinuousAt (fun w => max (ψ w) (G' w)) x :=
        (hψc x (hUW₀ hxU) hxY).max (hG'c x hxY)
      exact hm.congr_of_eventuallyEq (gluedMax_eventually_eq_max hU hxU)
    · exact (hG'c x hxY).congr_of_eventuallyEq (gluedMax_eventually_eq_global hU'U hcollar hxU)
  · -- finiteness off `Y`
    intro x hxY
    have hG'ne : G' x ≠ ⊥ := EReal.add_ne_bot_iff.mpr ⟨hFsne x hxY, EReal.coe_ne_bot _⟩
    by_cases hxU : x ∈ U
    · rw [gluedMax_eq_max hxU]
      exact ne_bot_of_le_ne_bot hG'ne (le_max_right _ _)
    · rw [gluedMax_eq_global hcollar (fun h => hxU (hU'U (subset_closure h)))]
      exact hG'ne
  · -- analytic singularities
    intro hφan e z hz
    set x := e.val.symm z with hxdef
    have hxe : x ∈ e.val.source := e.val.map_target hz
    have hex : e.val x = z := e.val.right_inv hz
    have hcs : ContinuousAt e.val.symm z := e.val.continuousAt_symm hz
    -- the scaled pole and its constant shift
    have hFsan : HasAnalyticSingularityTypeAt (chartFunction Fs e) z :=
      QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul
        (hF.analytic e z hz) (Rat.cast_pos.mp hs0)
    have hG'an : HasAnalyticSingularityTypeAt (chartFunction G' e) z :=
      hasAnalyticSingularityTypeAt_add_continuous hFsan (h := fun _ => c₀) continuousAt_const
    by_cases hxU : x ∈ U
    · obtain ⟨O, hO, hxO, J, hJ, hψO⟩ := hloc x (hUW₀ hxU)
      have hgan : ∀ j ∈ J, HasAnalyticSingularityTypeAt (chartFunction (g j) e) z := by
        intro j hj
        have hxT := hJ j hj hxO
        have hxΩ := hTΩ j.1 (subset_closure hxT)
        have h1 := hasAnalyticSingularityTypeAt_chart_comp_retr hk hreg (G j.1) hφan hxΩ.1 e hxe
        rw [hex] at h1
        have h2 := RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max h1 hFsan
        have hrc : ContinuousAt (fun w => corr j.1 (e.val.symm w) + η * ρc j.1 (e.val.symm w)) z := by
          refine ContinuousAt.add ?_ ?_
          · exact ((hcorr_cont j.1).continuousAt
              ((isOpen_localDomain _ (hρ j.1).1).mem_nhds hxΩ)).comp hcs
          · exact (continuous_const.mul
              (KahlerCurrentMax.continuous_of_chartSmooth (hρc j.1))).continuousAt.comp hcs
        have h3 := hasAnalyticSingularityTypeAt_add_continuous h2 hrc
        refine hasAnalyticSingularityTypeAt_congr h3 (Eventually.of_forall fun w => ?_)
        simp only [chartFunction, g, b]
        rw [add_assoc, ← EReal.coe_add]
      have hsup := hasAnalyticSingularityTypeAt_finset_sup J hgan
      have hmax := RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max hsup hG'an
      refine hasAnalyticSingularityTypeAt_congr hmax ?_
      have hev : gluedMax U ψ G' =ᶠ[𝓝 x] fun w => max (J.sup fun j => g j w) (G' w) := by
        filter_upwards [hU.mem_nhds hxU, hO.mem_nhds hxO] with w hwU hwO
        rw [gluedMax_eq_max hwU, hψO w hwO]
      have hev' := hev.comp_tendsto hcs
      filter_upwards [hev'] with w hw
      simp only [chartFunction, Function.comp_apply] at hw ⊢
      exact hw.symm
    · refine hasAnalyticSingularityTypeAt_congr hG'an ?_
      have hev := (gluedMax_eventually_eq_global hU'U hcollar hxU).comp_tendsto hcs
      filter_upwards [hev] with w hw
      simp only [chartFunction, Function.comp_apply] at hw ⊢
      exact hw.symm

end SGPT.Okounkov.TranscendentalExtension
