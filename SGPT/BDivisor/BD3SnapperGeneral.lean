import SGPT.BDivisor.BD3SnapperKleiman
import SGPT.Projective.OriginalMetricLineTensorGeometry
import SGPT.Hodge.SourceSmoothMixedCohomology
import SGPT.Foundations.Schemes.BundleDualSheaf

/-!
# Snapper's theorem and Snapper–Kleiman numbers of all line bundles (EP-free)

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  For `X` smooth projective of dimension
`n = k + 1` over `ℂ`:

* `originalMixedEulerDifference_eq_zero_bd3` (**Snapper's theorem**): every `(n+1)`-fold (or longer)
  mixed difference `Δ_{A₀} ⋯ Δ_{Aₙ} χ(B)` of line bundles vanishes.  From the ample case
  (`BD3SnapperVanishing`) by twisting each non-ample direction `A` by a positive `B` with `A ⊗ B`
  positive (Codex's EP-free `OriginalMetricLine.exists_positive_tensor_twist`) and using dual line
  bundles (`IntrinsicLineBundle.dual`, `bundleDualEvaluationIso`) to reach every base.
* `originalMixedEulerDifference_base_independent_bd3`: the top differences do not depend on `B`.
* `snapperKleiman_general_eq_slotIntegral_bd3`: for ALL line bundles `L₀, …, L_k` with ANY smooth
  hermitian metrics `hᵢ`, the Snapper–Kleiman number `(L₀ ⋯ L_k) = Δ_{L₀} ⋯ Δ_{L_k} χ(B)` equals
  `∫_{X(ℂ)} c₁(L₀, h₀) ∧ ⋯ ∧ c₁(L_k, h_k)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open scoped BigOperators

local instance bd3GenTopology {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd3GenCharts {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd3GenManifold {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X : Scheme.{0}} (k : ℕ) (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

/-- Every line bundle `Y` is `(Y ⊗ L^∨) ⊗ L`. -/
def dualShiftIso_bd3 (Y L : IntrinsicLineBundle X) :
    (originalLineTensor (originalLineTensor Y L.dual) L).sheaf ≅ Y.sheaf :=
  originalLineTensorAssociatorIso Y.atlas L.atlas.dual L.atlas ≪≫
    bundleTensorIso (Iso.refl Y.sheaf) (bundleDualEvaluationIso L.sheaf L.atlas) ≪≫
      bundleTensorRightUnitIso Y.sheaf

/-- A positive metric line is a positive (ample) original line. -/
def OriginalMetricLine.toPositive_bd3 (A : OriginalMetricLine f (k + 1) E) (h : A.Positive) :
    OriginalPositiveLine f (k + 1) E :=
  ⟨A.sheaf, A.atlas, A.metric, h⟩

/-- The twisting identity `Δ_{A⊗B} = T_B Δ_A + Δ_B` on the base side:
`(X ⊗ B') ⊗ A ≅ X ⊗ (U ⊗ (A ⊗ B))` for `B' = U ⊗ B`, `U` the structure sheaf. -/
def twistIso_bd3 (Y A : IntrinsicLineBundle X) (Bs : X.Modules) (b : LineBundleAtlas Bs) :
    (originalLineTensor (originalLineTensor Y ⟨bundleTensorPower Bs 1, b.tensorPower 1⟩) A).sheaf ≅
      (originalLineTensor Y ⟨bundleTensorPower (bundleTensor A.sheaf Bs) 1,
        (A.atlas.tensor b).tensorPower 1⟩).sheaf :=
  originalLineTensorAssociatorIso Y.atlas (b.tensorPower 1) A.atlas ≪≫
    bundleTensorIso (Iso.refl Y.sheaf)
      (originalLineTensorAssociatorIso (LineBundleAtlas.tensorPower b 0) b A.atlas ≪≫
        bundleTensorIso (Iso.refl _) (originalLineTensorCommutorIso b A.atlas))

omit [IsSeparated f] [QuasiCompact f] in
/-- One descending step: vanishing with `p + 1` ample powers implies vanishing with `p`. -/
theorem originalMixedEulerDifference_eq_zero_step_bd3 (p : ℕ) (hpk : p + 1 ≤ k)
    (ih : ∀ (Ps : List (OriginalPositiveLine f (k + 1) E × ℕ)) (As : List (IntrinsicLineBundle X)),
      p + 1 ≤ Ps.length → k + 2 ≤ Ps.length + As.length → ∀ B : IntrinsicLineBundle X,
        originalMixedEulerDifference f E (Ps.map (pl_bd3 k f E) ++ As) B = 0)
    (Ps : List (OriginalPositiveLine f (k + 1) E × ℕ)) (As : List (IntrinsicLineBundle X))
    (hp : p ≤ Ps.length) (hlen : k + 2 ≤ Ps.length + As.length) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (Ps.map (pl_bd3 k f E) ++ As) B = 0 := by
  by_cases hP : p + 1 ≤ Ps.length
  · exact ih Ps As hP hlen B
  cases As with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons A As' =>
    simp only [List.length_cons] at hlen
    let Am : OriginalMetricLine f (k + 1) E :=
      ⟨A.sheaf, A.atlas, schemeLineBundleMetric f (k + 1) E A.atlas⟩
    obtain ⟨Bm, hB, hQ⟩ := Am.exists_positive_tensor_twist
    let PB := Bm.toPositive_bd3 k f E hB
    let PQ := (Am.tensor Bm).toPositive_bd3 k f E hQ
    let R := Ps.map (pl_bd3 k f E) ++ As'
    have hQv : ∀ Y, originalMixedEulerDifference f E (originalPositivePowerLine_bd3 PQ 1 :: R) Y = 0 :=
      fun Y => ih ((PQ, 1) :: Ps) As' (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega) Y
    have hBv : ∀ Y, originalMixedEulerDifference f E (originalPositivePowerLine_bd3 PB 1 :: R) Y = 0 :=
      fun Y => ih ((PB, 1) :: Ps) As' (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega) Y
    have hkey : ∀ Y, originalMixedEulerDifference f E (A :: R)
        (originalLineTensor Y (originalPositivePowerLine_bd3 PB 1)) = 0 := by
      intro Y
      have h1 := hQv Y
      have h2 := hBv Y
      rw [originalMixedEulerDifference_cons_bd3] at h1 h2 ⊢
      have hinv : originalMixedEulerDifference f E R
          (originalLineTensor (originalLineTensor Y (originalPositivePowerLine_bd3 PB 1)) A) =
          originalMixedEulerDifference f E R
            (originalLineTensor Y (originalPositivePowerLine_bd3 PQ 1)) :=
        originalMixedEulerDifference_invariant f E R (twistIso_bd3 Y A Bm.sheaf Bm.atlas)
      linarith
    have hall : ∀ Y, originalMixedEulerDifference f E (A :: R) Y = 0 := by
      intro Y
      rw [← originalMixedEulerDifference_invariant f E (A :: R)
        (dualShiftIso_bd3 Y (originalPositivePowerLine_bd3 PB 1))]
      exact hkey _
    rw [originalMixedEulerDifference_perm_bd3 f E (List.perm_middle (l₁ := Ps.map (pl_bd3 k f E))
      (a := A) (l₂ := As')) B]
    exact hall B

/-- Vanishing with at least `p` ample powers, for every `p ≤ k`, by descending induction. -/
theorem originalMixedEulerDifference_eq_zero_of_count_bd3 :
    ∀ (j p : ℕ), p + j = k → ∀ (Ps : List (OriginalPositiveLine f (k + 1) E × ℕ))
      (As : List (IntrinsicLineBundle X)), p ≤ Ps.length → k + 2 ≤ Ps.length + As.length →
        ∀ B : IntrinsicLineBundle X,
          originalMixedEulerDifference f E (Ps.map (pl_bd3 k f E) ++ As) B = 0 := by
  intro j
  induction j with
  | zero =>
    intro p hp Ps As hPs hlen B
    exact originalMixedEulerDifference_eq_zero_of_positive_bd3 k f E Ps As (by omega) hlen B
  | succ j ih =>
    intro p hp
    exact originalMixedEulerDifference_eq_zero_step_bd3 k f E p (by omega) (ih (p + 1) (by omega))

/-- **Snapper's theorem (EP-free).**  On a smooth projective scheme of dimension `k + 1` over `ℂ`,
every mixed Euler difference with at least `k + 2` directions vanishes, for ARBITRARY line
bundles. -/
theorem originalMixedEulerDifference_eq_zero_bd3 (As : List (IntrinsicLineBundle X))
    (h : k + 2 ≤ As.length) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E As B = 0 :=
  originalMixedEulerDifference_eq_zero_of_count_bd3 k f E k 0 (Nat.zero_add k) [] As
    (Nat.zero_le _) (by simpa using h) B

/-- The top mixed differences do not depend on the base line bundle. -/
theorem originalMixedEulerDifference_base_independent_bd3 (As : List (IntrinsicLineBundle X))
    (h : As.length = k + 1) (B B' : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E As B' = originalMixedEulerDifference f E As B := by
  let Y := originalLineTensor B' B.dual
  have hz := originalMixedEulerDifference_eq_zero_bd3 k f E (Y :: As)
    (by simp only [List.length_cons]; omega) B
  rw [originalMixedEulerDifference_cons_bd3, sub_eq_zero] at hz
  rw [← hz]
  have e : B'.sheaf ≅ (originalLineTensor B Y).sheaf :=
    (dualShiftIso_bd3 B' B).symm ≪≫ originalLineTensorCommutorIso Y.atlas B.atlas
  exact originalMixedEulerDifference_invariant f E As e

/-- Additivity in the head direction: `(A ⊗ B') · R = A · R + B' · R` for top differences. -/
theorem originalMixedEulerDifference_head_add_bd3 (A Bl : IntrinsicLineBundle X)
    (R : List (IntrinsicLineBundle X)) (hR : R.length = k) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (originalLineTensor A Bl :: R) B =
      originalMixedEulerDifference f E (A :: R) B + originalMixedEulerDifference f E (Bl :: R) B := by
  have hind := originalMixedEulerDifference_base_independent_bd3 k f E (A :: R)
    (by simp only [List.length_cons]; omega) B (originalLineTensor B Bl)
  simp only [originalMixedEulerDifference_cons_bd3] at hind ⊢
  have hiso : (originalLineTensor (originalLineTensor B Bl) A).sheaf ≅
      (originalLineTensor B (originalLineTensor A Bl)).sheaf :=
    originalLineTensorAssociatorIso B.atlas Bl.atlas A.atlas ≪≫
      bundleTensorIso (Iso.refl _) (originalLineTensorCommutorIso Bl.atlas A.atlas)
  rw [originalMixedEulerDifference_invariant f E R hiso] at hind
  linarith

/-- **Snapper–Kleiman numbers of arbitrary line bundles are Chern integrals (EP-free).**  For `X`
smooth projective of dimension `k + 1` over `ℂ`, ANY line bundles `L₀, …, L_k` with ANY smooth
hermitian metrics (`OriginalMetricLine`) and ANY base `B`:
`Δ_{L₀} ⋯ Δ_{L_k} χ(B) = ∫_{X(ℂ)} c₁(L₀, h₀) ∧ ⋯ ∧ c₁(L_k, h_k)`. -/
theorem snapperKleiman_general_eq_slotIntegral_bd3 (B : IntrinsicLineBundle X)
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    ∀ A : Fin (k + 1) → OriginalMetricLine f (k + 1) E,
      (originalMixedEulerDifference f E (List.ofFn (fun i => (A i).toIntrinsic)) B : ℝ) =
        slotIntegral κ (fun i => (A i).curvature) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  dsimp only
  -- `G j`: the formula when all slots of index `≥ j` are positive.
  suffices hG : ∀ j : ℕ, ∀ A : Fin (k + 1) → OriginalMetricLine f (k + 1) E,
      (∀ i : Fin (k + 1), j ≤ i.val → (A i).Positive) →
      (originalMixedEulerDifference f E (List.ofFn (fun i => (A i).toIntrinsic)) B : ℝ) =
        slotIntegral κ (fun i => (A i).curvature) by
    intro A
    exact hG (k + 1) A (fun i hi => absurd i.isLt (by omega))
  intro j
  induction j with
  | zero =>
    intro A hA
    have h := snapperKleiman_eq_slotIntegral_bd3 k f E
      (fun i => (A i).toPositive_bd3 k f E (hA i (Nat.zero_le _))) B (fun i => (A i).metric) κ
    dsimp only at h
    exact h
  | succ j ih =>
    intro A hA
    by_cases hj : j < k + 1
    swap
    · exact ih A (fun i hi => absurd i.isLt (by omega))
    let jj : Fin (k + 1) := ⟨j, hj⟩
    obtain ⟨Bm, hB, hQ⟩ := (A jj).exists_positive_tensor_twist
    let AQ := Function.update A jj ((A jj).tensor Bm)
    let AB := Function.update A jj Bm
    have hpos (Z : OriginalMetricLine f (k + 1) E) (hZ : Z.Positive) :
        ∀ i : Fin (k + 1), j ≤ i.val → (Function.update A jj Z i).Positive := by
      intro i hi
      by_cases hij : i = jj
      · subst hij
        simpa only [Function.update_self] using hZ
      · rw [Function.update_of_ne hij]
        refine hA i ?_
        have : i.val ≠ j := fun h => hij (Fin.ext h)
        omega
    have hQ' := ih AQ (hpos _ hQ)
    have hB' := ih AB (hpos _ hB)
    -- algebraic side: additivity in the slot `jj`, through the swap `0 ↔ jj`
    let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 jj
    have hlist : ∀ Z : OriginalMetricLine f (k + 1) E,
        originalMixedEulerDifference f E
          (List.ofFn (fun i => (Function.update A jj Z i).toIntrinsic)) B =
        originalMixedEulerDifference f E
          (Z.toIntrinsic :: List.ofFn (fun i : Fin k => (A (σ i.succ)).toIntrinsic)) B := by
      intro Z
      have h0 : (fun i => (Function.update A jj Z i).toIntrinsic) ∘ σ =
          Fin.cons Z.toIntrinsic (fun i : Fin k => (A (σ i.succ)).toIntrinsic) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [σ]
        · simp only [Function.comp_apply, Fin.cons_succ]
          rw [Function.update_of_ne]
          intro h
          apply Fin.succ_ne_zero i
          apply σ.injective
          rw [h]
          simp [σ]
      rw [← originalMixedEulerDifference_perm_bd3 f E
        (σ.ofFn_comp_perm (fun i => (Function.update A jj Z i).toIntrinsic)) B, h0, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hadd := originalMixedEulerDifference_head_add_bd3 k f E (A jj).toIntrinsic Bm.toIntrinsic
      (List.ofFn (fun i : Fin k => (A (σ i.succ)).toIntrinsic)) (by simp) B
    have hAQ := hlist ((A jj).tensor Bm)
    have hAB := hlist Bm
    have hAA := hlist (A jj)
    rw [Function.update_eq_self] at hAA
    change originalMixedEulerDifference f E
      (List.ofFn (fun i => (AQ i).toIntrinsic)) B = _ at hAQ
    change originalMixedEulerDifference f E
      (List.ofFn (fun i => (AB i).toIntrinsic)) B = _ at hAB
    -- analytic side: additivity of the slot integral in the slot `jj`
    have hθ : slotIntegral κ (fun i => (AQ i).curvature) =
        slotIntegral κ (fun i => (A i).curvature) + slotIntegral κ (fun i => (AB i).curvature) := by
      have hcomp : ∀ Z : OriginalMetricLine f (k + 1) E,
          (fun i => (Function.update A jj Z i).curvature) =
            Function.update (fun i => (A i).curvature) jj Z.curvature := by
        intro Z
        funext i
        by_cases hij : i = jj
        · subst hij; simp
        · simp [Function.update_of_ne hij]
      have hgeo : slotIntegral κ (fun i => (AQ i).curvature) =
          slotIntegral κ (Function.update (fun i => (A i).curvature) jj
            ((A jj).curvature + Bm.curvature)) := by
        rw [show (fun i => (AQ i).curvature) = _ from hcomp _]
        apply SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_eq_of_bottChernRel
        intro i
        by_cases hij : i = jj
        · subst hij
          simp only [Function.update_self]
          exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
            ((A jj).tensor_curvature Bm)
        · simp only [Function.update_of_ne hij]
          exact ClosedRealOneOneForm.BottChernRel.refl _
      rw [hgeo, SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_update_add,
        show (fun i => (AB i).curvature) = _ from hcomp _]
      congr 1
      exact congrArg (slotIntegral κ) (Function.update_eq_self jj _)
    have hsum : (originalMixedEulerDifference f E (List.ofFn (fun i => (AQ i).toIntrinsic)) B : ℝ) =
        (originalMixedEulerDifference f E (List.ofFn (fun i => (A i).toIntrinsic)) B : ℝ) +
          (originalMixedEulerDifference f E (List.ofFn (fun i => (AB i).toIntrinsic)) B : ℝ) := by
      rw [hAQ, hAA, hAB]
      exact_mod_cast hadd
    linarith

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
