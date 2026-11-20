import SGPT.Siu.SiuDecompositionLelong
import SGPT.PSH.SourceGeneralSiuResidual
import SGPT.Foundations.Analysis.Pending.DominatedFullCurrentWeakCompactness
import SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration
import SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue

/-!
# Monotone limits of closed positive currents

Source: the proof of Siu's decomposition `eq:Siudec`; Xia, *Foundations of pluripotential
theory*, `thm:siu-divisorial-decomposition`, Step 2 ("the sequence `(S_N)` converges weakly"):
an increasing net of closed positive `(1,1)`-currents dominated by a closed positive current
converges weakly to a closed positive current.

* `exists_formSpan_coefficient`: every coefficient `β(v, w)` of a real `(1,1)`-form is a reading
  `⟨γ ∧ β⟩` against one constant `(m, m)`-form `γ` in the span of the strongly positive cone
  (finite-dimensional duality, injectivity of the complementary reading).
* `coefficients_eq_chartSpanCurrent`: hence every distribution coefficient of a type-`(1,1)`
  global current is one of its readings on strongly positive test forms.
* `exists_tendsto_of_monotone_dominated`: **monotone dominated limits**.  For a directed family
  `P j` of closed positive currents with `P k - P j` positive for `j ≤ k` and `T - P j` positive,
  there is a closed positive current `S` with `T - S` and `S - P j` positive and
  `P j → S` weakly (in every chart, on every test form).  The limit is produced by the weak
  compactness theorem `DominatedFullCurrentWeakCompactness.exists_tendsto_closedGlobalCurrent`
  along an ultrafilter, and the convergence along the whole net comes from monotonicity of the
  readings on strongly positive tests
  (`SGPT.PSH.sourceLocalCurrent_exists_monotone_dominated_limit`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open LocalProductCurrents StronglyPositiveForms ActualDistributionTwoFormReading
open ActualAnalyticCurrentLocalDensity CanonicalComplementaryCurrentTests
open ActualCanonicalComplementaryCurrentCalibration
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ}

/-! ### Coefficients of `(1,1)`-forms as complementary readings -/

/-- The real `(1,1)`-forms. -/
def oneOneSubmodule (m : ℕ) : Submodule ℝ (RealForm (m + 1) 2) where
  carrier := {β | FirstPass.IsOneOne β}
  zero_mem' := by intro u v; rfl
  add_mem' := by
    intro β β' hβ hβ' u v
    change β _ + β' _ = β _ + β' _
    rw [hβ u v, hβ' u v]
  smul_mem' := by
    intro c β hβ u v
    change c • β _ = c • β _
    rw [hβ u v]

/-- The complementary reading `β ↦ (γ ↦ ⟨γ ∧ β⟩)` of real two-forms. -/
def densityMap (m : ℕ) : RealForm (m + 1) 2 →ₗ[ℝ] Module.Dual ℝ (formSpan (m + 1) m) where
  toFun β := LocalCurrentPullbackDdc.formDensity β
  map_add' β β' := by
    ext γ
    simp only [LocalCurrentPullbackDdc.formDensity_apply, LinearMap.add_apply,
      coordinateWedge_add_right]
    exact TopDegreeDensity.topDensity_add _ _
  map_smul' c β := by
    ext γ
    simp only [LocalCurrentPullbackDdc.formDensity_apply, LinearMap.smul_apply,
      coordinateWedge_smul_right, RingHom.id_apply, smul_eq_mul]
    exact TopDegreeDensity.topDensity_smul _ _

theorem densityMap_restrict_injective (m : ℕ) :
    Function.Injective ((densityMap m).domRestrict (oneOneSubmodule m)) := by
  intro β β' h
  apply Subtype.ext
  apply LocalCurrentDensityMatrix.eq_of_forall_topDensity_eq β.property β'.property
  intro γ
  have := congrArg (fun f : Module.Dual ℝ (formSpan (m + 1) m) => f γ) h
  simpa only [LinearMap.domRestrict_apply, densityMap, LinearMap.coe_mk, AddHom.coe_mk,
    LocalCurrentPullbackDdc.formDensity_apply] using this

/-- **Every coefficient of a real `(1,1)`-form is a complementary reading**: for every pair of
vectors `w` there is `γ` in the span of the strongly positive `(m, m)`-forms with
`β(w) = ⟨γ ∧ β⟩` for every real `(1,1)`-form `β`. -/
theorem exists_formSpan_coefficient (w : Fin 2 → ComplexModel (m + 1)) :
    ∃ γ : formSpan (m + 1) m, ∀ β : RealForm (m + 1) 2, FirstPass.IsOneOne β →
      β w = LocalCurrentPullbackDdc.formDensity β γ := by
  classical
  let f := (densityMap m).domRestrict (oneOneSubmodule m)
  have hker : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (densityMap_restrict_injective m)
  obtain ⟨g, hg⟩ := @LinearMap.exists_leftInverse_of_injective ℝ (oneOneSubmodule m)
    (Module.Dual ℝ (formSpan (m + 1) m)) _ _ _ _ _ f hker
  let ev : oneOneSubmodule m →ₗ[ℝ] ℝ :=
    { toFun := fun β => (β : RealForm (m + 1) 2) w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let φ : Module.Dual ℝ (Module.Dual ℝ (formSpan (m + 1) m)) := ev.comp g
  refine ⟨(Module.evalEquiv ℝ (formSpan (m + 1) m)).symm φ, fun β hβ => ?_⟩
  have h1 : β w = ev ⟨β, hβ⟩ := rfl
  have h2 : ev ⟨β, hβ⟩ = φ (f ⟨β, hβ⟩) := by
    change ev ⟨β, hβ⟩ = ev (g (f ⟨β, hβ⟩))
    rw [← LinearMap.comp_apply g f, hg, LinearMap.id_apply]
  have h3 : φ (f ⟨β, hβ⟩) =
      (Module.evalEquiv ℝ (formSpan (m + 1) m) ((Module.evalEquiv ℝ (formSpan (m + 1) m)).symm φ))
        (f ⟨β, hβ⟩) := by
    rw [LinearEquiv.apply_symm_apply]
  rw [h1, h2, h3, Module.evalEquiv_apply, Module.Dual.eval_apply]
  rfl

theorem testedTwoForm_isOneOne {U : Opens (ComplexModel (m + 1))} {A : DistributionForm U 2}
    (hA : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne A) (φ : 𝓓(U, ℝ)) :
    FirstPass.IsOneOne (testedTwoForm A φ) := by
  intro v w
  rw [testedTwoForm_apply, testedTwoForm_apply]
  exact congrArg (fun T : 𝓓'(U, ℝ) => T φ) (hA v w)

theorem testedTwoForm_tuple {U : Opens (ComplexModel (m + 1))} (A : DistributionForm U 2)
    (φ : 𝓓(U, ℝ)) (v : Fin 2 → ComplexModel (m + 1)) : testedTwoForm A φ v = A v φ := by
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact testedTwoForm_apply A φ _ _

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The distribution coefficients of a type-`(1,1)` global current are its readings on strongly
positive test forms. -/
theorem coefficients_eq_chartSpanCurrent
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hT : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (e : ComplexChart (m + 1) M) {w : Fin 2 → ComplexModel (m + 1)} {γ : formSpan (m + 1) m}
    (hγ : ∀ β : RealForm (m + 1) 2, FirstPass.IsOneOne β →
      β w = LocalCurrentPullbackDdc.formDensity β γ) (φ : 𝓓(chartTarget e, ℝ)) :
    T.coefficients (canonicalBasis (m + 1)) e w φ = chartSpanCurrent T e γ φ := by
  rw [← complementaryRead_coefficients_eq_chartSpanCurrent,
    complementaryRead_apply, ← hγ _ (testedTwoForm_isOneOne (hT e) φ), testedTwoForm_tuple]

theorem chartSpanCurrent_sub (A B : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) :
    chartSpanCurrent (A - B) e = chartSpanCurrent A e - chartSpanCurrent B e := rfl

/-- A global chart reading is a finite combination of coefficient readings, so it converges as
soon as all coefficient readings converge. -/
theorem exists_tendsto_inChart_of_coefficients {ι : Type*} {l : Filter ι}
    (P : ι → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) (e : ComplexChart (m + 1) M)
    (hcoeff : ∀ (v : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(chartTarget e, ℝ)), ∃ c : ℝ,
      Tendsto (fun j => (P j).coefficients (canonicalBasis (m + 1)) e v φ) l (𝓝 c))
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    ∃ c : ℝ, Tendsto (fun j => (P j).inChart e η) l (𝓝 c) := by
  classical
  choose c hc using hcoeff
  have hrep : ∀ j, (P j).inChart e η =
      toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
        ((P j).coefficients (canonicalBasis (m + 1)) e) η := by
    intro j
    simp only [GlobalCurrent.coefficients, CurrentPairing.toLocalCurrent_fromLocalCurrent]
  simp only [hrep, toLocalCurrent, wedgePairing_apply]
  exact ⟨_, tendsto_finsetSum _ fun s _ => (hc _ _).const_smul (Equiv.Perm.sign s.out)⟩

/-! ### Monotone dominated limits -/

/-- **Monotone dominated limits of closed positive currents.**  Let `P j` (`j` in a directed set)
be closed positive `(1,1)`-currents with `P k - P j ≥ 0` for `j ≤ k`, dominated by a closed
positive current `T` (`T - P j ≥ 0`).  Then `P j` converges weakly to a closed positive current
`S` with `T - S ≥ 0` and `S - P j ≥ 0` for every `j`. -/
theorem exists_tendsto_of_monotone_dominated {κ : Type*} [Preorder κ] [IsDirectedOrder κ]
    [Nonempty κ] (P : κ → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hP : ∀ j, IsClosedPositiveCurrent (P j))
    (hmono : ∀ j k, j ≤ k → IsFullPositive (P k - P j))
    (hdom : ∀ j, IsFullPositive (T - P j)) :
    ∃ S : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)),
      IsClosedPositiveCurrent S ∧ IsFullPositive (T - S) ∧ (∀ j, IsFullPositive (S - P j)) ∧
      ∀ (e : ComplexChart (m + 1) M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
        Tendsto (fun j => (P j).inChart e η) atTop (𝓝 (S.inChart e η)) := by
  classical
  let 𝒰 : Ultrafilter κ := Ultrafilter.of atTop
  have h𝒰 : (𝒰 : Filter κ) ≤ atTop := Ultrafilter.of_le atTop
  let κp : formSpan (m + 1) m := kahlerPower (m + 1) m
  have hpos (j : κ) (e : ComplexChart (m + 1) M) : IsPositive (chartSpanCurrent (P j) e) :=
    isPositive_chartSpanCurrent (P j) (hP j).2.2 e
  -- the limit along the ultrafilter
  obtain ⟨S, hSclosed, hSlim⟩ :=
    DominatedFullCurrentWeakCompactness.exists_tendsto_closedGlobalCurrent 𝒰
      (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m)) P (fun j => (hP j).1)
      (fun e j => chartSpanCurrent (P j) e κp)
      (fun e j => (hpos j e).positiveDistribution_trace)
      (by
        intro e χ hχ
        refine ⟨chartSpanCurrent T e κp χ, fun j => ?_⟩
        have h := (isPositive_chartSpanCurrent (T - P j) (hdom j) e).positiveDistribution_trace
          χ hχ
        rw [chartSpanCurrent_sub] at h
        change 0 ≤ chartSpanCurrent T e κp χ - chartSpanCurrent (P j) e κp χ at h
        linarith)
      (by
        intro e v
        obtain ⟨γ, hγ⟩ := exists_formSpan_coefficient (m := m) v
        obtain ⟨C, hC, hCb⟩ :=
          SGPT.PSH.sourceLocalCurrent_exists_uniform_coefficient_bound (U := chartTarget e) γ
        refine ⟨C, hC, fun j φ hφ => ?_⟩
        rw [coefficients_eq_chartSpanCurrent (hP j).2.1 e hγ]
        exact hCb _ (hpos j e) φ hφ)
  -- convergence of the coefficients along the whole net
  have hcoeff (e : ComplexChart (m + 1) M) (v : Fin 2 → ComplexModel (m + 1))
      (φ : 𝓓(chartTarget e, ℝ)) : ∃ c : ℝ,
        Tendsto (fun j => (P j).coefficients (canonicalBasis (m + 1)) e v φ) atTop (𝓝 c) := by
    obtain ⟨γ, hγ⟩ := exists_formSpan_coefficient (m := m) v
    obtain ⟨L, -, -, -, hL⟩ := SGPT.PSH.sourceLocalCurrent_exists_monotone_dominated_limit
      (fun j => chartSpanCurrent (P j) e) (chartSpanCurrent T e) (fun j => hpos j e)
      (fun j k hjk => by
        have h := isPositive_chartSpanCurrent (P k - P j) (hmono j k hjk) e
        rwa [chartSpanCurrent_sub] at h)
      (fun j => by
        have h := isPositive_chartSpanCurrent (T - P j) (hdom j) e
        rwa [chartSpanCurrent_sub] at h)
    refine ⟨L γ φ, ?_⟩
    simp only [coefficients_eq_chartSpanCurrent (hP _).2.1 e hγ]
    exact hL γ φ
  have hlim (e : ComplexChart (m + 1) M)
      (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
      Tendsto (fun j => (P j).inChart e η) atTop (𝓝 (S.inChart e η)) := by
    obtain ⟨c, hc⟩ := exists_tendsto_inChart_of_coefficients P e (hcoeff e) η
    have hcS : c = S.inChart e η := tendsto_nhds_unique (hc.mono_left h𝒰) (hSlim e η)
    rwa [hcS] at hc
  have hlimC (e : ComplexChart (m + 1) M) (v : Fin 2 → ComplexModel (m + 1))
      (φ : 𝓓(chartTarget e, ℝ)) :
      Tendsto (fun j => (P j).coefficients (canonicalBasis (m + 1)) e v φ) atTop
        (𝓝 (S.coefficients (canonicalBasis (m + 1)) e v φ)) := by
    exact hlim e _
  -- type `(1,1)`
  have h11 : S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) := by
    intro e v w
    apply ContinuousLinearMap.ext
    intro φ
    have h1 := hlimC e ![Complex.I • v, Complex.I • w] φ
    have h2 := hlimC e ![v, w] φ
    have heq : (fun j => (P j).coefficients (canonicalBasis (m + 1)) e
        ![Complex.I • v, Complex.I • w] φ) =
        fun j => (P j).coefficients (canonicalBasis (m + 1)) e ![v, w] φ := by
      funext j
      exact congrArg (fun T : 𝓓'(chartTarget e, ℝ) => T φ) ((hP j).2.1 e v w)
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  -- positivity statements
  have hcast : 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2 := by
    rw [complexModel_real_finrank]; omega
  have hSpos : IsFullPositive S := by
    intro e α hα
    exact ge_of_tendsto (hlim e _) (Eventually.of_forall fun j => (hP j).2.2 e α hα)
  have hTS : IsFullPositive (T - S) := by
    intro e α hα
    have h := (tendsto_const_nhds (x := T.inChart e (castTestDegree hcast α))).sub
      (hlim e (castTestDegree hcast α))
    exact ge_of_tendsto h (Eventually.of_forall fun j => hdom j e α hα)
  have hSP : ∀ j, IsFullPositive (S - P j) := by
    intro j e α hα
    have h := (hlim e (castTestDegree hcast α)).sub
      (tendsto_const_nhds (x := (P j).inChart e (castTestDegree hcast α)))
    exact ge_of_tendsto h ((eventually_ge_atTop j).mono fun k hjk => hmono j k hjk e α hα)
  exact ⟨S, ⟨hSclosed, h11, hSpos⟩, hTS, hSP, hlim⟩

end SGPT.Siu
