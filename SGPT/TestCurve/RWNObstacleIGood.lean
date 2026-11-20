import SGPT.TestCurve.TestConfFiltrationRay
import SGPT.IGood.DXMainSections
import SGPT.PSH.SourceIGoodOperations
import SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood

/-!
# The obstacle of the test curve of a filtration is `𝓘`-good

Source `ex:RWN` (chapter *Test curves*): *"Note that for each `k ∈ ℤ_{>0}`, `τ ≤ k⁻¹τ_k(𝓕)`, we
know that `k⁻¹Γ^{𝓕,k}_τ` is `𝓘`-good by `prop:Igoodsup`. The family is bounded above by `0`,
so it follows from the same proposition that the obstacle in the definition of `Γ^𝓕_τ` is
`𝓘`-good."*

We follow the book with one simplification: instead of first showing that each
`k⁻¹Γ^{𝓕,k}_τ = usc sup_s k⁻¹ log |s|²_{h^k}` is `𝓘`-good, we apply `prop:Igoodsup`
(`SGPT.PSH.VariableComplexAtlas.sourceIGood_uscSup`) once, to the family of all normalized
section potentials `k⁻¹ log |s|²_{h^k}` (`k > 0`, `0 ≠ s ∈ 𝓕^{kτ}_k`, `|s|²_{h^k} ≤ 1`). Each of
them has analytic singularities (`SGPT.IGood.DXMain.hasManifoldAnalyticSingularityType_normalizedPotential`),
hence is `𝓘`-good (`ex:analyIgood`), and their supremum is the unregularized obstacle
`sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ` because `Γ^{𝓕,k}_τ` is the raw supremum over normalized sections
(`SectionFiltration.sectionPotential_eq_raw`).

## Main results

* `obstacleFamily_iSup`: `sup_{(k,s)} k⁻¹ log |s|²_{h^k} = sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ`;
* **`obstacle_iGood`**: for every `τ` such that `𝓕^{kτ}_k ≠ 0` for some `k > 0` (in particular
  every `τ < τ(𝓕)`, `obstacle_iGood_of_lt_slope`), the obstacle
  `usc sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ` is `𝓘`-good (`def:Igoodpot`).
* `sectionLogNormSq_smul`, `normalizedPotential_le_obstacle`: every section of `𝓕^{kτ}_k`
  has normalized potential `k⁻¹ log |s|²_{h^k} ≤ ` obstacle `+ C`;
* `rawObstacle_eq_of_le_neg_bound`: for `τ, τ' ≤ -C` (`C` the constant of `eq:Flinearlybdd`)
  the obstacles coincide, since then `𝓕^{kτ}_k = H⁰(X, L^k)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance rwnObstTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance rwnObstCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance rwnObstManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

namespace SGPT.TestCurve.RWN

/-- Division of a supremum by a positive real number. -/
theorem EReal.iSup_div_coe {ι : Sort*} (g : ι → EReal) {k : ℝ} (hk : 0 < k) :
    (⨆ i, g i) / (k : EReal) = ⨆ i, g i / (k : EReal) := by
  apply le_antisymm
  · rw [EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hk) (EReal.coe_ne_top k)]
    refine iSup_le fun i => ?_
    exact (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hk) (EReal.coe_ne_top k)).mp
      (le_iSup (fun j => g j / (k : EReal)) i)
  · exact iSup_le fun i =>
      EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hk.le) (le_iSup g i)

/-- `x / k = k⁻¹ * x` in `[-∞, ∞]`. -/
theorem EReal.div_coe_eq_inv_mul (x : EReal) (k : ℝ) :
    x / (k : EReal) = ((k⁻¹ : ℝ) : EReal) * x := by
  rw [div_eq_mul_inv, mul_comm, ← EReal.coe_inv]

end SGPT.TestCurve.RWN

namespace SGPT.LineBundle.SectionFiltration

open SGPT.TestCurve.RWN

variable {L : X.Modules} {a : LineBundleAtlas L}
variable (F : SGPT.LineBundle.SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)

/-- `log |c s|²_{h^k} = log |c|² + log |s|²_{h^k}` for `c ≠ 0`. -/
theorem sectionLogNormSq_smul (k : ℕ) {c : ℂ} (hc : c ≠ 0) (s : SectionSpace f L k)
    (p : SchemeComplexPoint f) :
    H.sectionLogNormSq a k (c • s : SectionSpace f L k) p =
      ((Real.log (Complex.normSq c) : ℝ) : EReal) + H.sectionLogNormSq a k s p := by
  unfold SchemeLineBundleMetric.sectionLogNormSq
  rw [H.sectionNormSq_smul a k c s p, ENNReal.ofReal_mul (Complex.normSq_nonneg c),
    ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Complex.normSq_pos.mpr hc)]

/-- The index set of the normalized section potentials entering the obstacle at `τ`:
`k > 0` and `0 ≠ s ∈ 𝓕^{kτ}_k` with `|s|²_{h^k} ≤ 1`. -/
def ObstacleIndex (τ : ℝ) : Type :=
  {p : Σ k : ℕ, SectionSpace f L k //
    0 < p.1 ∧ p.2 ∈ F.normalizedSections H p.1 τ ∧ p.2 ≠ 0}

/-- The normalized section potential `k⁻¹ log |s|²_{h^k}` of an index `(k, s)`. -/
def obstacleFamily (τ : ℝ) (i : ObstacleIndex F H τ) : SchemeComplexPoint f → EReal :=
  SGPT.IGood.DXMain.normalizedPotential f n E a H i.1.1 i.1.2

/-- `k⁻¹ Γ^{𝓕,k}_τ = sup_{s} k⁻¹ log |s|²_{h^k}` over normalized `s ∈ 𝓕^{kτ}_k`. -/
theorem normalizedPotential_eq_iSup [IsIntegral X] (k : ℕ) (hk : 0 < k) (τ : ℝ)
    (x : SchemeComplexPoint f) :
    F.normalizedPotential H k τ x =
      ⨆ s : F.normalizedSections H k τ, ((((k : ℝ)⁻¹ : ℝ) : EReal) *
        H.sectionLogNormSq a k s.1 x) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold SGPT.LineBundle.SectionFiltration.normalizedPotential
  rw [F.sectionPotential_eq_raw H k τ]
  change (⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x) / ((k : ℝ) : EReal) = _
  rw [EReal.iSup_div_coe _ hkR]
  simp only [EReal.div_coe_eq_inv_mul]

/-- **The obstacle is the supremum of the normalized section potentials**:
`sup_{(k,s)} k⁻¹ log |s|²_{h^k} = sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ` (zero sections only contribute
`-∞`). -/
theorem obstacleFamily_iSup [IsIntegral X] (τ : ℝ) (x : SchemeComplexPoint f) :
    (⨆ i : ObstacleIndex F H τ, obstacleFamily F H τ i x) = F.rawObstacle H τ x := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    obtain ⟨⟨k, s⟩, hk, hs, -⟩ := i
    refine le_trans ?_ (le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential H k τ x) k hk)
    rw [F.normalizedPotential_eq_iSup H k hk τ x]
    exact le_iSup (fun s : F.normalizedSections H k τ => ((((k : ℝ)⁻¹ : ℝ) : EReal) *
      H.sectionLogNormSq a k s.1 x)) ⟨s, hs⟩
  · refine iSup₂_le fun k hk => ?_
    rw [F.normalizedPotential_eq_iSup H k hk τ x]
    refine iSup_le fun s => ?_
    by_cases hs0 : s.1 = 0
    · have hz : H.sectionLogNormSq a k s.1 x = ⊥ := by
        rw [hs0]
        exact congrFun (H.sectionLogNormSq_zero a k) x
      rw [hz, EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (by exact_mod_cast hk)))]
      exact bot_le
    · exact le_iSup (fun i : ObstacleIndex F H τ => obstacleFamily F H τ i x)
        ⟨⟨k, s.1⟩, hk, s.2, hs0⟩

/-- Each normalized section potential lies below the raw obstacle. -/
theorem obstacleFamily_le_rawObstacle [IsIntegral X] (τ : ℝ) (i : ObstacleIndex F H τ)
    (x : SchemeComplexPoint f) : obstacleFamily F H τ i x ≤ F.rawObstacle H τ x := by
  rw [← F.obstacleFamily_iSup H τ x]
  exact le_iSup (fun j : ObstacleIndex F H τ => obstacleFamily F H τ j x) i

/-- The index set is nonempty as soon as `𝓕^{kτ}_k ≠ 0` for some `k > 0`. -/
theorem obstacleIndex_nonempty [IsIntegral X] {τ : ℝ} {k : ℕ} (hk : 0 < k)
    (hne : F.piece ((k : ℝ) * τ) k ≠ ⊥) : Nonempty (ObstacleIndex F H τ) := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, -, hc0, hcle⟩ := H.exists_normalized a k s hs0
  exact ⟨⟨⟨k, c • s⟩, hk, ⟨Submodule.smul_mem _ c hs, hcle⟩, hc0⟩⟩

/-- For `τ < τ(𝓕)` the index set is nonempty. -/
theorem obstacleIndex_nonempty_of_lt_slope [IsIntegral X] {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    Nonempty (ObstacleIndex F H τ) := by
  obtain ⟨m, hm, hjump⟩ := F.exists_degree_jump_of_lt_slope hτ
  have := SectionSpace.finiteDimensional f E a m
  have h1 := hjump 1 one_pos
  simp only [one_mul] at h1
  exact F.obstacleIndex_nonempty H hm ((F.piece_ne_bot_iff _).mpr h1)

section IGood

variable [IsIntegral X] [ConnectedSpace (SchemeComplexPoint f)]

local instance rwnObstMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance rwnObstBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- **Source `ex:RWN`: the obstacle is `𝓘`-good.** If `𝓕^{kτ}_k ≠ 0` for some `k > 0`, then
`usc sup_{k ∈ ℤ_{>0}} k⁻¹ Γ^{𝓕,k}_τ` is `𝓘`-good (`def:Igoodpot`), by `prop:Igoodsup` applied
to the normalized section potentials (each `𝓘`-good by `ex:analyIgood`). -/
theorem obstacle_iGood {τ : ℝ} (hne : Nonempty (ObstacleIndex F H τ)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IGood (n := n) (F.obstacle H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let omega := schemeProjectiveTNKahlerBackground f n E
  have hpshN : ∀ i : ObstacleIndex F H τ,
      IsThetaPshPotential (H.curvature a).val (obstacleFamily F H τ i) := fun i =>
    SGPT.IGood.DXMain.isThetaPshPotential_normalizedPotential f n E a H i.2.1 i.2.2.2
  have hpsh : ∀ i : ObstacleIndex F H τ,
      (ofFixedModel n (SchemeComplexPoint f)).IsThetaPSH
        (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H) (obstacleFamily F H τ i) := by
    intro i
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [SGPT.TestCurve.TestConf.curvatureAtlasForm_native]
    exact hpshN i
  have hgood : ∀ i : ObstacleIndex F H τ, sourceIGood (n := n) (obstacleFamily F H τ i) := by
    intro i
    apply (sourceIGood_iff_native _).mpr
    exact AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type omega
      (hpshN i).quasiPshPotential
      (SGPT.IGood.DXMain.hasManifoldAnalyticSingularityType_normalizedPotential f n E a H
        i.2.2.2)
  have hbdd : LocallyUniformlyBoundedAbove (range (obstacleFamily F H τ)) univ := by
    intro x _
    refine ⟨univ, Filter.univ_mem, 0, ?_⟩
    rintro _ ⟨i, rfl⟩ y -
    exact (F.obstacleFamily_le_rawObstacle H τ i y).trans (F.rawObstacle_le_zero H τ y)
  have h := sourceIGood_uscSup omega (obstacleFamily F H τ) hpsh hgood hbdd
  have heq : (⨆ i, obstacleFamily F H τ i) = F.rawObstacle H τ := by
    funext x
    rw [iSup_apply]
    exact F.obstacleFamily_iSup H τ x
  rw [heq] at h
  exact (sourceIGood_iff_native _).mp h

/-- For `τ < τ(𝓕)` the obstacle `usc sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ` is `𝓘`-good. -/
theorem obstacle_iGood_of_lt_slope {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IGood (n := n) (F.obstacle H τ) :=
  F.obstacle_iGood H (F.obstacleIndex_nonempty_of_lt_slope H hτ)

end IGood

/-! ### Sections and the obstacle -/

/-- Every section `s ∈ 𝓕^{kτ}_k`, `k > 0`, satisfies `k⁻¹ log |s|²_{h^k} ≤ ` obstacle `+ C`. -/
theorem normalizedPotential_singularityLE_obstacle [IsIntegral X] {k : ℕ} (hk : 0 < k) {τ : ℝ}
    {s : SectionSpace f L k} (hs : s ∈ F.piece ((k : ℝ) * τ) k) :
    SGPT.PSH.SingularityLE (SGPT.IGood.DXMain.normalizedPotential f n E a H k s)
      (F.obstacle H τ) := by
  by_cases hs0 : s = 0
  · refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => ?_⟩
    have hz : H.sectionLogNormSq a k s x = ⊥ := by
      rw [hs0]
      exact congrFun (H.sectionLogNormSq_zero a k) x
    change (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq a k s x ≤ _
    rw [hz, EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (by exact_mod_cast hk)))]
    exact bot_le
  obtain ⟨c, hc, hc0, hcle⟩ := H.exists_normalized a k s hs0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    ⟨-((k : ℝ)⁻¹ * Real.log (Complex.normSq c)), fun x => ?_⟩
  have hmem : (c • s : SectionSpace f L k) ∈ F.normalizedSections H k τ :=
    ⟨Submodule.smul_mem _ c hs, hcle⟩
  have hle : (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq a k (c • s : SectionSpace f L k) x ≤
      F.obstacle H τ x := by
    refine le_trans ?_ (le_uscRegularization _ x)
    refine le_trans ?_ (le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential H k τ x) k hk)
    rw [F.normalizedPotential_eq_iSup H k hk τ x]
    exact le_iSup (fun s : F.normalizedSections H k τ => ((((k : ℝ)⁻¹ : ℝ) : EReal) *
      H.sectionLogNormSq a k s.1 x)) ⟨_, hmem⟩
  rw [sectionLogNormSq_smul H k hc s x] at hle
  change (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq a k s x ≤ _
  have hk' : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  have hO0 : F.obstacle H τ x ≤ 0 := F.obstacle_le_zero H τ x
  generalize H.sectionLogNormSq a k s x = A at hle ⊢
  generalize F.obstacle H τ x = O at hle hO0 ⊢
  generalize Real.log (Complex.normSq c) = l at hle ⊢
  induction A using EReal.rec with
  | bot =>
    rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr hk')]
    exact bot_le
  | top =>
    rw [EReal.coe_add_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr hk')] at hle
    exact absurd (top_le_iff.mp (hle.trans hO0)) EReal.zero_ne_top
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_mul] at hle
    induction O using EReal.rec with
    | bot => exact absurd (le_bot_iff.mp hle) (EReal.coe_ne_bot _)
    | top => exact absurd hO0 (by simp)
    | coe o =>
      have hle' : (k : ℝ)⁻¹ * (l + r) ≤ o := EReal.coe_le_coe_iff.mp hle
      rw [← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by nlinarith)

/-- For `τ ≤ -C` (`C` the constant of `eq:Flinearlybdd`) and `k > 0`: `𝓕^{kτ}_k = H⁰(X, L^k)`. -/
theorem piece_eq_top_of_le_neg_bound {τ : ℝ} (hτ : τ ≤ -(F.bound : ℝ)) {k : ℕ} (hk : 0 < k) :
    F.piece ((k : ℝ) * τ) k = ⊤ := by
  apply F.piece_eq_top_of_le hk
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- For `τ, τ' ≤ -C` and `k > 0`, the normalized sections of `𝓕^{kτ}_k` and `𝓕^{kτ'}_k`
coincide. -/
theorem normalizedSections_eq_of_le_neg_bound {τ τ' : ℝ} (hτ : τ ≤ -(F.bound : ℝ))
    (hτ' : τ' ≤ -(F.bound : ℝ)) {k : ℕ} (hk : 0 < k) :
    F.normalizedSections H k τ = F.normalizedSections H k τ' := by
  ext s
  simp only [SGPT.LineBundle.SectionFiltration.normalizedSections, Set.mem_ofPred_eq,
    F.piece_eq_top_of_le_neg_bound hτ hk, F.piece_eq_top_of_le_neg_bound hτ' hk,
    Submodule.mem_top, true_and]

/-- For `τ, τ' ≤ -C` the obstacles of `τ` and `τ'` coincide. -/
theorem rawObstacle_eq_of_le_neg_bound {τ τ' : ℝ} (hτ : τ ≤ -(F.bound : ℝ))
    (hτ' : τ' ≤ -(F.bound : ℝ)) : F.rawObstacle H τ = F.rawObstacle H τ' := by
  funext x
  unfold SGPT.LineBundle.SectionFiltration.rawObstacle
  refine iSup_congr fun k => iSup_congr fun hk => ?_
  unfold SGPT.LineBundle.SectionFiltration.normalizedPotential
    SGPT.LineBundle.SectionFiltration.sectionPotential
  rw [F.normalizedSections_eq_of_le_neg_bound H hτ hτ' hk]

/-- For `τ, τ' ≤ -C`: `Γ^𝓕_τ = Γ^𝓕_{τ'}`. -/
theorem testCurvePotential_eq_of_le_neg_bound {τ τ' : ℝ} (hτ : τ ≤ -(F.bound : ℝ))
    (hτ' : τ' ≤ -(F.bound : ℝ)) : F.testCurvePotential H τ = F.testCurvePotential H τ' := by
  unfold SGPT.LineBundle.SectionFiltration.testCurvePotential
    SGPT.LineBundle.SectionFiltration.obstacle
  rw [F.rawObstacle_eq_of_le_neg_bound H hτ hτ']

end SGPT.LineBundle.SectionFiltration
