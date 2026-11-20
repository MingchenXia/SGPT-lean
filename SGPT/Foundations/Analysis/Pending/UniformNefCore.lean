import SGPT.Foundations.Analysis.Pending.UniformNefCoreSupport
import SGPT.Foundations.Analysis.Pending.BoucksomResolutionAssembly
import SGPT.Foundations.Analysis.Pending.BlowupConnected

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The uniform nef core of Boucksom 4.8

Source: Boucksom, *On the volume of a line bundle*, Lemma 4.10 and the proof of Theorem 4.8
(`bou02-volume:4.10`, `bou02-volume:4.8`); Demailly--Păun, Theorem 2.12 and Proposition 2.6
(`dp04-kahler-cone:2.12`, `dp04-kahler-cone:2.6`).  Blueprint `bou:uniform-diagonal-domination`,
`bou:pushforward-lower-bound`.  TN.4 plan, §1 F6 "(P) GRAPH ROUTE" and "STATUS (run 0157 end)",
step U5.

**Theorem** (`uniformNefCore`).  Let `X` be a compact connected complex manifold of dimension `n > 0`
with a Kähler form `ω`.  For `η > 0` and `C` there is `c > 0` such that for every blowup sequence
`μ : Y → X`, every Kähler form `ω'` on `Y` and every closed real `(1,1)`-form `b` on `Y`, nef, with
`∫_Y bⁿ ≥ η` and `∫_Y bⁱ ∧ (μ^*ω)ⁿ⁻ⁱ ≤ C` (`i ≤ n`), the form `b − c μ^*ω` has a psh potential.
This is `BoucksomResolutionAssembly.UniformNefCore ω`.

*Proof* (graph route; Yau's theorem is the TEMPORARY named input
`YauTheorem.exists_kahler_mongeAmpere_eq_exp`, everything else is proved).  The FIXED concentration
`(f_ε, V_ε, δ)` of TN23 on `X × X` (`exists_diagonal_massConcentration`) is pulled back along
`ν = μ × id : Y × X → X × X` (`ν⁻¹ Δ = Γ_μ`), with the background `W = p₁^*ω_Y + p₂^*ω`,
`ω_Y = μ^*ω + ρω'` for a small `ρ > 0` chosen per `Y` (`UniformNefCoreSupport`).  Yau's theorem in the
Kähler classes `p₁^*(b + ε_k ω_Y) + p₂^*ω` (`b` nef) with the pulled-back targets, Boucksom's
concentration lemma with explicit constant (`ConcentratedCurrent.exists_concentratedCurrent`), TN23's
support theorem on the graph (`Θ ≥ λ [Γ_μ]`), and the limit with the semipositive lower bound
`λ μ^*ω` (`GraphFibrePotentialLimit`) give a `(m b − λ μ^*ω)`-psh potential, `m = n ∫_X ωⁿ`.  Every
constant entering `λ` is bounded in terms of `η`, `C`, `δ`, `n`, `∫_X ωⁿ` only: the product formula
on `Y × X`, background independence of slot integrals and the binomial bound turn them into the
hypotheses `∫ bⁿ ≥ η`, `∫ bⁱ ∧ (μ^*ω)ⁿ⁻ⁱ ≤ C`, up to errors made `≤ 1` by the choice of `ρ` and of
`ε_k ≤ ε_Y`.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal Manifold

universe u

namespace SGPT.Foundations.Analysis.Pending.UniformNefCore

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses FirstPass.BlowupSequences
  StronglyPositiveForms ProductTestForms PositiveProductCurrents IntegrationCurrent
  TopDegreeDensity SmoothCurrentTraceMeasure ManifoldTubePositivity MixedMassClassInvariance
  NefMixedMass GlobalNonPluripolar NefCoreKahlerCurrent UniformNefCoreSupport
  SubmanifoldMassConcentration
open scoped ProductComplexManifold
open ProductComplexManifold

/-! ### Small parameters -/

/-- A property eventually true near `0` holds on some `[0, ρ]` with `0 < ρ ≤ 1`. -/
theorem exists_small_pos {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝 (0 : ℝ), P t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ t ∈ Icc (0 : ℝ) ρ, P t := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, min_le_right _ _, fun t ht => hP ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  exact lt_of_le_of_lt (ht.2.trans (min_le_left _ _)) (half_lt_self hε)

/-! ### Algebra of product forms -/

section Algebra

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (q + 1)) X] [IsComplexManifold (q + 1) X]

theorem prodForm_add_prodForm (a a' : ClosedRealOneOneForm (q + 1) V)
    (c c' : ClosedRealOneOneForm (q + 1) X) :
    prodForm a c + prodForm a' c' = prodForm (a + a') (c + c') := by
  rw [prodForm, prodForm, prodForm, UniformNefCoreSupport.pullback_add,
    UniformNefCoreSupport.pullback_add]
  abel

end Algebra

/-! ### The uniform nef core on one blowup, with explicit constants -/

section Core

variable {q : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel (q + 1)) X] [IsComplexManifold (q + 1) X] [CompactSpace X]

/-- The explicit constant of the uniform nef core: it depends only on `η`, `C`, the concentration
constant `δ`, `n` and `(X, ω)`. -/
def coreConst (w : KahlerBackground (q + 1) X) (δ η C : ℝ) : ℝ :=
  let B : ℝ := ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ)
  let volX : ℝ := (kahlerVolume w).real univ
  let P₀ : ℝ := B * (η / 2) * volX
  let Vol₀ : ℝ := B * (C + 1) * volX
  let M₀ : ℝ := B * (2 ^ (q + 1) * C + 2) * (2 ^ (q + 1) * volX)
  (P₀ / Vol₀ * δ ^ 2 / (4 * 2 ^ (q + 1) * ((q + 1) + (q + 1)).factorial * M₀)) /
    (2 ^ (q + 1) * C + 1) / GraphFibrePotentialLimit.fibreConst w

theorem fibreConst_pos [Nonempty X] (w : KahlerBackground (q + 1) X) :
    0 < GraphFibrePotentialLimit.fibreConst w := by
  have hvol : 0 < ∫ x, topRatio w.form.val (formPow w.form.val (q + 1)) x ∂(kahlerVolume w) := by
    simp_rw [topRatio_formPow w.isKahler.1]
    simpa [integral_const] using kahlerVolume_real_univ_pos w
  exact mul_pos (by positivity)
    (fibreIntegral_pos_of_nef w (nefWithRespectTo_of_isSemipositive w.isSemipositive) hvol)

theorem coreConst_pos [Nonempty X] (w : KahlerBackground (q + 1) X) {δ η C : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) (hC : 0 ≤ C) : 0 < coreConst w δ η C := by
  have hvolX := kahlerVolume_real_univ_pos w
  have hB : (0 : ℝ) < ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hm := fibreConst_pos w
  unfold coreConst
  positivity

/-- **The uniform nef core on one blowup sequence, with the explicit constant `coreConst`** (U5).
The data `(f, V, δ)` are TN23's fixed concentration of mass on the diagonal of `X × X`
(`exists_diagonal_massConcentration`); `C ≥ 0` bounds the mixed integrals. -/
theorem exists_thetaPsh_of_blowup [ConnectedSpace X] (w : KahlerBackground (q + 1) X)
    {f : ℝ → X × X → ℝ} (hf : ∀ ε, ChartSmooth (n := (q + 1) + (q + 1)) (f ε))
    {Vt : ℝ → Set (X × X)} (hVmono : ∀ ε ε', 0 < ε → ε ≤ ε' → Vt ε ⊆ Vt ε')
    (hVΔ : (⋂ ε ∈ Set.Ioc (0 : ℝ) 1, closure (Vt ε)) ⊆ Set.diagonal X)
    (hhalf : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ((1 / 2 : ℝ) • (prodKahlerBackground w w).form +
      ddcClosedForm (f ε) (hf ε)).val.IsSemipositive)
    {δ : ℝ} (hδ : 0 < δ)
    (hδV : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ hpsh : ∀ i, ThetaPlurisubharmonic
        (concentrationSlot (prodKahlerBackground w w) (f ε) (hf ε) (q + 1) i).val (fun _ => 0),
      ENNReal.ofReal δ ≤ globalMixedMeasure
        (concentrationSlot (prodKahlerBackground w w) (f ε) (hf ε) (q + 1)) (fun _ _ => 0) hpsh
        (univ ∩ Vt ε))
    {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel (q + 1)) Y]
    [IsComplexManifold (q + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (μ : Y → X) (hμ : IsBlowupSequence (q + 1) X Y μ) (ω' : KahlerBackground (q + 1) Y)
    (b : ClosedRealOneOneForm (q + 1) Y) (hnef : NefWithRespectTo ω' b)
    (hvol : η ≤ slotIntegral ω' (fun _ => b))
    (hmix : ∀ i : ℕ, i ≤ q + 1 → slotIntegral ω' (fun j : Fin (q + 1) =>
      if (j : ℕ) < i then b else ClosedRealOneOneForm.pullback hμ.contMDiff w.form) ≤ C) :
    ∃ v : Y → EReal, IsThetaPshPotential
      (b - coreConst w δ η C • ClosedRealOneOneForm.pullback hμ.contMDiff w.form).val v := by
  classical
  have : ConnectedSpace Y := BlowupConnected.connectedSpace_of_isBlowupSequence μ hμ
  set hμc := hμ.contMDiff with hμcdef
  set μω : ClosedRealOneOneForm (q + 1) Y := ClosedRealOneOneForm.pullback hμc w.form with hμωdef
  have hμω : μω.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hμc w.isSemipositive
  set B : ℝ := ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) with hBdef
  have hB : 0 < B := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  set volX := (kahlerVolume w).real univ with hvolXdef
  have hvolX : 0 < volX := kahlerVolume_real_univ_pos w
  -- the three `ρ`-dependent quantities at `ρ = 0`
  have hmix0 : slotIntegral ω' (fun _ => μω) ≤ C := by
    have h := hmix 0 (Nat.zero_le _)
    simpa only [Nat.not_lt_zero, if_false] using h
  have hQ1₀ : slotIntegral ω' (fun _ => μω + (0 : ℝ) • ω'.form) < C + 1 := by
    simp only [zero_smul, add_zero]
    linarith
  have hQ2₀ : slotIntegral ω' (fun _ => (μω + b) + (0 : ℝ) • ω'.form) < 2 ^ (q + 1) * C + 1 := by
    have h := slotIntegral_add_le_two_pow ω' b μω hmix
    simp only [zero_smul, add_zero]
    linarith
  have hQ3₀ : slotIntegral ω' (fun _ => (2 : ℝ) • μω + (0 : ℝ) • ω'.form) <
      2 ^ (q + 1) * C + 1 := by
    simp only [zero_smul, add_zero]
    rw [slotIntegral_const_smul]
    have : (2 : ℝ) ^ (q + 1) * slotIntegral ω' (fun _ => μω) ≤ 2 ^ (q + 1) * C :=
      mul_le_mul_of_nonneg_left hmix0 (by positivity)
    linarith
  have hcont : ∀ A : ClosedRealOneOneForm (q + 1) Y,
      Continuous fun t : ℝ => slotIntegral ω' (fun _ => A + t • ω'.form) := fun A =>
    continuous_slotIntegral_add_smul ω' (fun _ => A) (fun _ => ω'.form)
  obtain ⟨ρ, hρ, -, hρP⟩ := exists_small_pos
    ((((hcont μω).tendsto 0).eventually (gt_mem_nhds hQ1₀)).and
      ((((hcont (μω + b)).tendsto 0).eventually (gt_mem_nhds hQ2₀)).and
        (((hcont ((2 : ℝ) • μω)).tendsto 0).eventually (gt_mem_nhds hQ3₀))))
  obtain ⟨hQ1, hQ2, hQ3⟩ := hρP ρ ⟨hρ.le, le_rfl⟩
  -- the Kähler form `ω_Y = μ^*ω + ρ ω'`
  have hωYK : (μω + ρ • ω'.form).val.IsKahler := isKahler_add_smul_of_isSemipositive ω' hμω hρ
  set ωY : KahlerBackground (q + 1) Y := ⟨μω + ρ • ω'.form, hωYK⟩ with hωYdef
  have hωYform : ωY.form = μω + ρ • ω'.form := rfl
  have hsub1 : (ωY.form - μω).val.IsSemipositive := by
    rw [hωYform, add_sub_cancel_left]
    intro e z hz v
    have := (KahlerBackground.isSemipositive ω') e z hz v
    simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hρ.le this
  have hsub2 : (ωY.form - ρ • ω'.form).val.IsSemipositive := by
    rw [hωYform, add_sub_cancel_right]
    exact hμω
  -- the two `ε`-dependent quantities at `ε = 0`
  have hQ4₀ : η / 2 < slotIntegral ω' (fun _ => b + (0 : ℝ) • ωY.form) := by
    simp only [zero_smul, add_zero]
    linarith
  have hbωY : b + ωY.form = (μω + b) + ρ • ω'.form := by
    rw [hωYform]
    abel
  have hG₀ : slotIntegral ω' (fun _ => (b + ωY.form) + (0 : ℝ) • ωY.form) <
      2 ^ (q + 1) * C + 2 := by
    simp only [zero_smul, add_zero]
    rw [hbωY]
    linarith
  have hcontY : ∀ A : ClosedRealOneOneForm (q + 1) Y,
      Continuous fun t : ℝ => slotIntegral ω' (fun _ => A + t • ωY.form) := fun A =>
    continuous_slotIntegral_add_smul ω' (fun _ => A) (fun _ => ωY.form)
  obtain ⟨εY, hεY, hεY1, hεYP⟩ := exists_small_pos
    ((((hcontY b).tendsto 0).eventually (lt_mem_nhds hQ4₀)).and
      (((hcontY (b + ωY.form)).tendsto 0).eventually (gt_mem_nhds hG₀)))
  -- the parameters `ε_k = ε_Y / (k + 1)`
  set εs : ℕ → ℝ := fun k => εY / ((k : ℝ) + 1) with hεsdef
  have hεpos : ∀ k, 0 < εs k := fun k => by positivity
  have hεle : ∀ k, εs k ≤ εY := fun k =>
    div_le_self hεY.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hεle1 : ∀ k, εs k ≤ 1 := fun k => (hεle k).trans hεY1
  have hεanti : ∀ j k, j ≤ k → εs k ≤ εs j := fun j k hjk => by
    simp only [hεsdef]
    apply div_le_div_of_nonneg_left hεY.le (by positivity)
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  have hεmem : ∀ k, εs k ∈ Set.Ioc (0 : ℝ) 1 := fun k => ⟨hεpos k, hεle1 k⟩
  have hεP : ∀ k, η / 2 < slotIntegral ω' (fun _ => b + εs k • ωY.form) ∧
      slotIntegral ω' (fun _ => (b + ωY.form) + εs k • ωY.form) < 2 ^ (q + 1) * C + 2 :=
    fun k => hεYP (εs k) ⟨(hεpos k).le, hεle k⟩
  -- the background `W = p₁^*ω_Y + p₂^*ω` on `Y × X` and `ν = μ × id`
  set W := prodKahlerBackground ωY w with hWdef
  set ν : Y × X → X × X := Prod.map μ (id : X → X) with hνdef
  have hν := contMDiff_prodMap_id (X := X) hμc
  -- the pulled-back concentration potentials
  set fk : ℕ → Y × X → ℝ := fun k z => f (εs k) (ν z) with hfkdef
  have hfk : ∀ k, ChartSmooth (n := (q + 1) + (q + 1)) (fk k) := fun k =>
    chartSmooth_comp hν (hf (εs k))
  have hhalfk : ∀ k, ((1 / 2 : ℝ) • W.form + ddcClosedForm (fk k) (hfk k)).val.IsSemipositive :=
    fun k => isSemipositive_half_add_ddc_comp hμc w ωY hsub1 (hf (εs k)) (hhalf (εs k) (hεmem k))
  have hωk : ∀ k, (W.form + ddcClosedForm (fk k) (hfk k)).val.IsKahler := fun k =>
    ConcentratedCurrent.isKahler_of_half W (hfk k) (hhalfk k)
  -- the nef corrections and Yau's theorem at every level
  have hnefK : ∀ k, ∃ (h : Y → ℝ) (hh : ChartSmooth (n := q + 1) h),
      (b + εs k • ωY.form + ddcClosedForm h hh).val.IsKahler := fun k =>
    exists_isKahler_add_smul_of_nef hnef hρ hsub2 (hεpos k)
  choose hk hhk hKk using hnefK
  have hyau := fun k => exists_yau_prodForm w (b + εs k • ωY.form) (hhk k) (hKk k) ⟨_, hωk k⟩
  choose g hg c hc hαK hMA using hyau
  set A : ℕ → ClosedRealOneOneForm ((q + 1) + (q + 1)) (Y × X) := fun k =>
    prodForm (b + εs k • ωY.form) w.form with hAdef
  have hαpsh : ∀ k, ThetaPlurisubharmonic (A k + ddcClosedForm (g k) (hg k)).val (fun _ => 0) :=
    fun k => (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr
      (KahlerBackground.isSemipositive ⟨_, hαK k⟩)
  -- the concentration on `Y × X`
  have h₁ : ∀ k i, ThetaPlurisubharmonic ((fun i : Fin ((q + 1) + (q + 1)) =>
      if (i : ℕ) < q + 1 then W.form + ddcClosedForm (fk k) (hfk k) else W.form) i).val
        (fun _ => 0) := fun k i =>
    ProductMapMixedMeasure.thetaPlurisubharmonic_zero_of_isSemipositive
      (isSemipositive_concentrationSlot W (hfk k) (hhalfk k) (q + 1) i)
  have hconc : ∀ k, ENNReal.ofReal δ ≤ globalMixedMeasure (fun i : Fin ((q + 1) + (q + 1)) =>
      if (i : ℕ) < q + 1 then W.form + ddcClosedForm (fk k) (hfk k) else W.form) (fun _ _ => 0)
        (h₁ k) (ν ⁻¹' Vt (εs k)) := by
    intro k
    have hX : ∀ i, ThetaPlurisubharmonic (concentrationSlot (prodKahlerBackground w w) (f (εs k))
        (hf (εs k)) (q + 1) i).val (fun _ => 0) := fun i =>
      ProductMapMixedMeasure.thetaPlurisubharmonic_zero_of_isSemipositive
        (isSemipositive_concentrationSlot _ (hf (εs k)) (hhalf (εs k) (hεmem k)) (q + 1) i)
    have h1 := hδV (εs k) (hεmem k) hX
    have h2 := le_globalMixedMeasure_concentrationSlot_comp hμ w ωY hsub1 (hf (εs k))
      (hhalf (εs k) (hεmem k)) (q + 1) (univ ∩ Vt (εs k)) hX (h₁ k)
    simp only [univ_inter] at h1 h2
    exact h1.trans h2
  -- the uniform lower bound on the volumes
  set P₀ : ℝ := B * (η / 2) * volX with hP₀def
  have hvolk : ∀ k, P₀ ≤ slotIntegral W fun _ => A k := by
    intro k
    show P₀ ≤ slotIntegral (prodKahlerBackground ωY w)
      (fun _ => prodForm (b + εs k • ωY.form) w.form)
    rw [slotIntegral_prodForm, slotIntegral_eq_of_background ω' ωY, slotIntegral_form w]
    have h4 := (hεP k).1
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4.le hB.le) hvolX.le
    linarith
  -- the uniform upper bound on the mixed masses
  set M₀ : ℝ := B * (2 ^ (q + 1) * C + 2) * (2 ^ (q + 1) * volX) with hM₀def
  have hM₀ : 0 < M₀ := by positivity
  have hmassk : ∀ k, slotIntegral W (fun i : Fin ((q + 1) + (q + 1)) =>
      if (i : ℕ) < q + 1 then A k else W.form) ≤ M₀ := by
    intro k
    have h0 := slotIntegral_ite_add_ddc W (q + 1) (A k) W.form (hg k) (f := fun _ => (0 : ℝ))
      (fun _ => contDiffOn_const)
    rw [ddcClosedForm_zero, add_zero] at h0
    rw [← h0]
    set α := A k + ddcClosedForm (g k) (hg k) with hαdef
    have hαs : α.val.IsSemipositive := KahlerBackground.isSemipositive ⟨_, hαK k⟩
    have hWs : W.form.val.IsSemipositive := W.isSemipositive
    have hsum : ∀ {a a' : ClosedRealOneOneForm ((q + 1) + (q + 1)) (Y × X)},
        a.val.IsSemipositive → a'.val.IsSemipositive → (a + a').val.IsSemipositive := by
      intro a a' ha ha' e z hz v
      have h1 := ha e z hz v
      have h2 := ha' e z hz v
      simp only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
      linarith
    set θ0 : Fin ((q + 1) + (q + 1)) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (Y × X) :=
      fun i => if (i : ℕ) < q + 1 then α else W.form with hθ0def
    set θ1 : Fin ((q + 1) + (q + 1)) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (Y × X) :=
      fun i => if (i : ℕ) < q + 1 then α else W.form + α with hθ1def
    have hθ0s : ∀ i, (θ0 i).val.IsSemipositive := fun i => by
      simp only [hθ0def]
      split_ifs
      · exact hαs
      · exact hWs
    have hθ1s : ∀ i, (θ1 i).val.IsSemipositive := fun i => by
      simp only [hθ1def]
      split_ifs
      · exact hαs
      · exact hsum hWs hαs
    have hθ2s : ∀ _ : Fin ((q + 1) + (q + 1)), (α + W.form).val.IsSemipositive := fun _ =>
      hsum hαs hWs
    have hp0 := fun i => ProductMapMixedMeasure.thetaPlurisubharmonic_zero_of_isSemipositive
      (hθ0s i)
    have hp1 := fun i => ProductMapMixedMeasure.thetaPlurisubharmonic_zero_of_isSemipositive
      (hθ1s i)
    have hp2 := fun i => ProductMapMixedMeasure.thetaPlurisubharmonic_zero_of_isSemipositive
      (hθ2s i)
    have m1 : globalMixedMeasure θ0 (fun _ _ => 0) hp0 ≤ globalMixedMeasure θ1 (fun _ _ => 0) hp1 :=
      NefBoundedMixedMass.globalMixedMeasure_le_of_add_smul_on
        (Finset.univ.filter fun i : Fin ((q + 1) + (q + 1)) => ¬ (i : ℕ) < q + 1) hαs one_pos
        (fun i => by
          by_cases hi : (i : ℕ) < q + 1
          · have hS : i ∉ Finset.univ.filter fun i : Fin ((q + 1) + (q + 1)) => ¬ (i : ℕ) < q + 1 :=
              fun h => (Finset.mem_filter.mp h).2 hi
            rw [if_neg hS]
            simp only [hθ0def, hθ1def, if_pos hi]
          · have hS : i ∈ Finset.univ.filter fun i : Fin ((q + 1) + (q + 1)) => ¬ (i : ℕ) < q + 1 :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
            rw [if_pos hS]
            simp only [hθ0def, hθ1def, if_neg hi, one_smul])
        hp0 (fun i _ => (LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hθ0s i)) hp1
    have m2 : globalMixedMeasure θ1 (fun _ _ => 0) hp1 ≤
        globalMixedMeasure (fun _ => α + W.form) (fun _ _ => 0) hp2 :=
      NefBoundedMixedMass.globalMixedMeasure_le_of_add_smul_on
        (Finset.univ.filter fun i : Fin ((q + 1) + (q + 1)) => (i : ℕ) < q + 1) hWs one_pos
        (fun i => by
          by_cases hi : (i : ℕ) < q + 1
          · have hS : i ∈ Finset.univ.filter fun i : Fin ((q + 1) + (q + 1)) => (i : ℕ) < q + 1 :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
            rw [if_pos hS]
            simp only [hθ1def, if_pos hi, one_smul]
          · have hS : i ∉ Finset.univ.filter fun i : Fin ((q + 1) + (q + 1)) => (i : ℕ) < q + 1 :=
              fun h => hi (Finset.mem_filter.mp h).2
            rw [if_neg hS]
            simp only [hθ1def, if_neg hi]
            abel)
        hp1 (fun i _ => (LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hθ1s i)) hp2
    have hreal : slotIntegral W θ0 ≤ slotIntegral W (fun _ => α + W.form) := by
      rw [slotIntegral, slotIntegral, ← globalMixedMeasure_real_univ_eq_integral W θ0 hp0,
        ← globalMixedMeasure_real_univ_eq_integral W _ hp2]
      have := ProductMixedMeasure.isFiniteMeasure_globalMixedMeasure hp2
      exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_iff'.mp (m1.trans m2) univ)
    have hcls : slotIntegral W (fun _ => α + W.form) = slotIntegral W (fun _ => A k + W.form) := by
      have := slotIntegral_add_ddc W (fun _ => A k + W.form) (fun _ => g k) (fun _ => hg k)
      rw [← this]
      congr 1
      funext i
      rw [hαdef]
      abel
    have hprod : A k + W.form = prodForm ((b + ωY.form) + εs k • ωY.form) ((2 : ℝ) • w.form) := by
      rw [hAdef, hWdef, prodKahlerBackground_form, prodForm_add_prodForm, two_smul]
      congr 1
      abel
    calc slotIntegral W θ0 ≤ slotIntegral W (fun _ => α + W.form) := hreal
      _ = slotIntegral W (fun _ => A k + W.form) := hcls
      _ = B * slotIntegral ω' (fun _ => (b + ωY.form) + εs k • ωY.form) * (2 ^ (q + 1) * volX) := by
          rw [hprod, hWdef, slotIntegral_prodForm, slotIntegral_eq_of_background ω' ωY,
            slotIntegral_const_smul, slotIntegral_form w]
      _ ≤ M₀ := by
          rw [hM₀def]
          have h5 := (hεP k).2
          have : (0 : ℝ) ≤ 2 ^ (q + 1) * volX := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5.le hB.le) this
  -- the closed sets `F_j = ν⁻¹(closure V_{ε_j} ∪ Δ)`
  set F : ℕ → Set (Y × X) := fun j => ν ⁻¹' (closure (Vt (εs j)) ∪ Set.diagonal X) with hFdef
  have hF : ∀ j, IsClosed (F j) := fun j =>
    (isClosed_closure.union isClosed_diagonal).preimage hν.continuous
  have hFanti : Antitone F := fun j k hjk =>
    preimage_mono (union_subset_union_left _ (closure_mono (hVmono _ _ (hεpos k) (hεanti j k hjk))))
  have hSF : ∀ j k, j ≤ k → ν ⁻¹' Vt (εs k) ⊆ F j := fun j k hjk =>
    preimage_mono ((subset_closure.trans
      (closure_mono (hVmono _ _ (hεpos k) (hεanti j k hjk)))).trans subset_union_left)
  -- the concentrated current `Θ`
  obtain ⟨U, Θ, hΘpos, hUle, hΘc, -, hlim, hlow⟩ :=
    ConcentratedCurrent.exists_concentratedCurrent (d := q + 1) (p := q + 1) W A g hg fk hfk hαK
      hhalfk c hc hMA (fun k => ν ⁻¹' Vt (εs k)) hδ hM₀ h₁ hconc hvolk hmassk hmassk hF hFanti hSF
  have hFΔ : (⋂ j, F j) = {p : Y × X | μ p.1 = p.2} := by
    have hX : (⋂ j, (closure (Vt (εs j)) ∪ Set.diagonal X)) = Set.diagonal X := by
      apply Subset.antisymm
      · intro z hz
        rw [mem_iInter] at hz
        by_cases hzΔ : z ∈ Set.diagonal X
        · exact hzΔ
        · apply hVΔ
          rw [mem_iInter₂]
          intro ε hε
          obtain ⟨j, hj⟩ := exists_nat_gt (εY / ε)
          have hjε : εs j ≤ ε := by
            simp only [hεsdef]
            rw [div_lt_iff₀ hε.1] at hj
            rw [div_le_iff₀ (by positivity)]
            nlinarith [hε.1]
          exact closure_mono (hVmono _ _ (hεpos j) hjε) ((hz j).resolve_right hzΔ)
      · exact subset_iInter fun j => subset_union_right
    simp only [hFdef]
    rw [← preimage_iInter, hX]
    ext p
    simp [hνdef, Set.mem_diagonal_iff]
  rw [hFΔ] at hlow
  -- the graph part: `Θ ≥ λ [Γ_μ]`
  obtain ⟨lam, -, hlamlow, hΘlam⟩ :=
    exists_isPositive_sub_smul_graphCurrent_of_le hμc ωY w hΘpos hΘc hlow
  -- the uniform bounds on `vol W` and `mass[Γ_μ]`
  set Vol₀ : ℝ := B * (C + 1) * volX with hVol₀def
  have hvolW : (kahlerVolume W).real univ ≤ Vol₀ := by
    rw [← slotIntegral_form W, hWdef, prodKahlerBackground_form, slotIntegral_prodForm,
      slotIntegral_eq_of_background ω' ωY, slotIntegral_form w]
    have h1 : slotIntegral ω' (fun _ => ωY.form) < C + 1 := hQ1
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1.le hB.le) hvolX.le
    linarith
  have hvolWpos : 0 < (kahlerVolume W).real univ := by
    rw [← slotIntegral_form W, hWdef, prodKahlerBackground_form, slotIntegral_prodForm,
      slotIntegral_form ωY, slotIntegral_form w]
    exact mul_pos (mul_pos hB (kahlerVolume_real_univ_pos ωY)) hvolX
  have hmassΓ : mass (prodKahlerBackground ωY w) (GraphSupport.graphCurrent (X := X) ωY hμc) ≤
      2 ^ (q + 1) * C + 1 := by
    rw [mass_graphCurrent_eq, slotIntegral_eq_of_background ω' ωY]
    have : ωY.form + ClosedRealOneOneForm.pullback hμc w.form = (2 : ℝ) • μω + ρ • ω'.form := by
      rw [hωYform, two_smul]
      abel
    rw [this]
    exact hQ3.le
  have hmassΓpos : 0 < mass (prodKahlerBackground ωY w)
      (GraphSupport.graphCurrent (X := X) ωY hμc) := by
    rw [mass_graphCurrent_eq]
    set K := GraphFibreIntegration.graphKahler hμc ωY w with hKdef
    calc 0 < (kahlerVolume K).real univ := kahlerVolume_real_univ_pos K
      _ = slotIntegral K (fun _ => K.form) := (slotIntegral_form K).symm
      _ = slotIntegral ωY (fun _ => K.form) := slotIntegral_eq_of_background ωY K _
  -- `λ ≥ λ₀`, uniform
  set δ'₀ : ℝ := P₀ / Vol₀ * δ ^ 2 / (4 * 2 ^ (q + 1) * ((q + 1) + (q + 1)).factorial * M₀)
    with hδ'₀def
  have hδ'₀ : 0 ≤ δ'₀ := by positivity
  have hδ'le : δ'₀ ≤ P₀ / (kahlerVolume W).real univ * δ ^ 2 /
      (4 * 2 ^ (q + 1) * ((q + 1) + (q + 1)).factorial * M₀) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
    exact div_le_div_of_nonneg_left (by positivity) hvolWpos hvolW
  have hlam₀ : δ'₀ / (2 ^ (q + 1) * C + 1) ≤ lam := by
    refine le_trans ?_ hlamlow
    calc δ'₀ / (2 ^ (q + 1) * C + 1)
        ≤ δ'₀ / mass (prodKahlerBackground ωY w) (GraphSupport.graphCurrent (X := X) ωY hμc) :=
          div_le_div_of_nonneg_left hδ'₀ hmassΓpos hmassΓ
      _ ≤ _ := div_le_div_of_nonneg_right hδ'le hmassΓpos.le
  -- the limit (U3): a `(m b − λ μ^*ω)`-psh potential
  have hεIcc : ∀ k, εs k ∈ Icc (0 : ℝ) 1 := fun k => ⟨(hεpos k).le, hεle1 k⟩
  have hε0 : Tendsto εs (U : Filter ℕ) (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul εY
    rw [mul_zero] at h
    exact (h.congr fun k : ℕ => mul_one_div εY ((k : ℝ) + 1)).mono_left hUle
  obtain ⟨u, hu⟩ := GraphFibrePotentialLimit.exists_isThetaPshPotential_of_tendsto_graph ωY w b U
    εs hεIcc hε0 g hg hαpsh hlim hμc hΘlam
  -- scale by `1/m` and lower the constant to `coreConst`
  set m := GraphFibrePotentialLimit.fibreConst w with hmdef
  have hm : 0 < m := fibreConst_pos w
  have hu' := PotentialMassComparison.isThetaPshPotential_smul hu (inv_pos.mpr hm)
  have hform : m⁻¹ • (m • b - lam • ClosedRealOneOneForm.pullback hμc w.form) =
      b - (lam / m) • μω := by
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hm.ne', one_smul, inv_mul_eq_div]
  rw [hform] at hu'
  have hc_le : coreConst w δ η C ≤ lam / m := by
    unfold coreConst
    exact div_le_div_of_nonneg_right hlam₀ hm.le
  have hsemi : ((lam / m - coreConst w δ η C) • μω).val.IsSemipositive := fun e z hz v => by
    have := hμω e z hz v
    simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (sub_nonneg.mpr hc_le) this
  have hfin : IsThetaPshPotential ((b - (lam / m) • μω) + (lam / m - coreConst w δ η C) • μω).val
      (fun x => ((m⁻¹ : ℝ) : EReal) * u x) :=
    ⟨LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hu'.1 hsemi, hu'.2⟩
  have heq : (b - (lam / m) • μω) + (lam / m - coreConst w δ η C) • μω =
      b - coreConst w δ η C • μω := by
    module
  rw [heq] at hfin
  exact ⟨_, hfin⟩

/-- An irreducible analytic `univ` makes the manifold connected. -/
theorem connectedSpace_of_isComplexAnalyticallyIrreducible_univ {N : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M]
    (h : IsComplexAnalyticallyIrreducible (n := N) (univ : Set M)) : ConnectedSpace M := by
  rw [connectedSpace_iff_clopen]
  refine ⟨h.2.1.to_subtype.map Subtype.val |>.elim fun x => ⟨x⟩, fun s hs => ?_⟩
  have han : ∀ t : Set M, IsClopen t → IsComplexAnalyticSubset (n := N) t := fun t ht =>
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq
      (isComplexAnalyticSubset_univ (n := N)) ht.isClosed
      fun y hy => ⟨t, ht.isOpen, hy, by rw [univ_inter, inter_self]⟩
  rcases h.2.2 s sᶜ (han s hs) (han sᶜ hs.compl) (subset_univ _) (subset_univ _)
    (union_compl_self s).symm with h1 | h1
  · exact Or.inr h1.symm
  · left
    rw [← compl_compl s, ← h1, compl_univ]

/-- **The uniform nef core of Boucksom 4.8** (`bou02-volume:4.10`, uniform in the blowup):
`BoucksomResolutionAssembly.UniformNefCore ω` holds on every compact connected Kähler manifold of
positive dimension.  Its only `sorry`-backed input is the TEMPORARY named input Yau's theorem
(`YauTheorem.exists_kahler_mongeAmpere_eq_exp`). -/
theorem uniformNefCore [ConnectedSpace X] (w : KahlerBackground (q + 1) X) :
    BoucksomResolutionAssembly.UniformNefCore w := by
  intro η C hη
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨f, hf, Vt, -, hVmono, hVΔ, hhalf, hconc⟩ := exists_diagonal_massConcentration w x₀
  obtain ⟨δ, hδ, hδV⟩ := hconc univ Filter.univ_mem
  refine ⟨coreConst w δ η (max C 0), coreConst_pos w hδ hη (le_max_right _ _), ?_⟩
  intro Y _ _ _ _ _ _ μ hμ ω' b hnef hvol hmix
  exact exists_thetaPsh_of_blowup w hf hVmono hVΔ hhalf hδ hδV hη (le_max_right _ _) Y μ hμ ω' b
    hnef hvol fun i hi => (hmix i hi).trans (le_max_left _ _)

end Core

/-- **The uniform nef core in positive dimension** (the form consumed by Boucksom 4.8). -/
theorem uniformNefCore_of_pos {n : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    [ConnectedSpace X] (hn : 0 < n) (w : KahlerBackground n X) :
    BoucksomResolutionAssembly.UniformNefCore w := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  exact uniformNefCore w

end SGPT.Foundations.Analysis.Pending.UniformNefCore
