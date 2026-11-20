import SGPT.BDivisor.BD3SnapperVanishing

/-!
# Snapper–Kleiman intersection numbers of ample line bundles are Chern integrals

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749): "our transcendental intersection theory
coincides with [Dang–Favre's] in the algebraic setting".  Dang–Favre's intersection numbers of
Cartier classes on a model are the algebraic (Snapper–Kleiman) numbers
`(L₁ ⋯ Lₙ) = Δ_{L₁} ⋯ Δ_{Lₙ} χ(B) = ∑_{I ⊆ {1..n}} (-1)^{n-|I|} χ(X, B ⊗ ⊗_{i∈I} Lᵢ)`
(Kleiman's definition; by Snapper's theorem it is independent of `B` and equal to the coefficient
of `m₁ ⋯ mₙ` in `χ(⊗ Lᵢ^{mᵢ})`).  Here, EP-free, for `X` smooth projective of dimension `n = k+1`
over `ℂ`:

* `originalMixedEulerDifference_powerLine_cons_bd3`: the top differences are multiplicative in the
  power of an ample direction (`Δ_{P^m} = m Δ_P` in top degree);
* `originalMixedEulerDifference_ample_eq_slotIntegral_bd3`: for ample `P₁, …, P_k`, ANY line bundle
  `A` and ANY base `B`, and any smooth hermitian metrics,
  `Δ_{P₁} ⋯ Δ_{P_k} Δ_A χ(B) = ∫_{X(ℂ)} c₁(A) ∧ c₁(P₁) ∧ ⋯ ∧ c₁(P_k)`;
* `snapperKleiman_eq_slotIntegral_bd3`: for ample `L₁, …, Lₙ`,
  `(L₁ ⋯ Lₙ) = ∫_{X(ℂ)} c₁(L₁, h₁) ∧ ⋯ ∧ c₁(Lₙ, hₙ)`, for every base `B`
  (`snapperKleiman_independent_base_bd3`).

The proof removes the cutting powers of the EP-free complete-intersection chain
(`WholeOriginalCITower.mixedEuler_eq_power_product_of_metrics_bd3`) using the Snapper vanishing of
`BD3SnapperVanishing`.
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

local instance bd3SKTopology {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd3SKCharts {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd3SKManifold {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-- `Forall₂` of sheaf isomorphisms along `List.ofFn`. -/
theorem forall₂_iso_ofFn_bd3 {Y : Scheme.{0}} (k : ℕ) (As Cs : Fin k → IntrinsicLineBundle Y)
    (e : ∀ i, (As i).sheaf ≅ (Cs i).sheaf) :
    List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) (List.ofFn As) (List.ofFn Cs) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons ⟨e 0⟩ (ih (fun i => As i.succ) (fun i => Cs i.succ) (fun i => e i.succ))

variable {X : Scheme.{0}} (k : ℕ) (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

/-- The `m`-th power of the line underlying a positive line, as a mixed-difference direction. -/
abbrev pl_bd3 (p : OriginalPositiveLine f (k + 1) E × ℕ) : IntrinsicLineBundle X :=
  originalPositivePowerLine_bd3 p.1 p.2

/-- **Top differences are multiplicative in ample powers**: for `X` of dimension `k+1` and a
direction list with at least `k - 2` further ample powers, `Δ_{P^m} = m Δ_P` in the top difference. -/
theorem originalMixedEulerDifference_powerLine_cons_bd3 (P : OriginalPositiveLine f (k + 1) E)
    (Ps : List (OriginalPositiveLine f (k + 1) E × ℕ)) (As : List (IntrinsicLineBundle X))
    (h₁ : k ≤ Ps.length + 2) (h₂ : k ≤ Ps.length + As.length) (m : ℕ) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (originalPositivePowerLine_bd3 P m :: (Ps.map (pl_bd3 k f E) ++ As)) B =
      (m : ℤ) * originalMixedEulerDifference f E
        (originalPositivePowerLine_bd3 P 1 :: (Ps.map (pl_bd3 k f E) ++ As)) B := by
  set Rest := Ps.map (pl_bd3 k f E) ++ As with hRest
  have hconst : ∀ (e : ℕ) (B' : IntrinsicLineBundle X),
      originalMixedEulerDifference f E (originalPositivePowerLine_bd3 P 1 :: Rest)
        (originalLineTensor B' (originalPositivePowerLine_bd3 P e)) =
      originalMixedEulerDifference f E (originalPositivePowerLine_bd3 P 1 :: Rest) B' := by
    intro e B'
    have h := originalMixedEulerDifference_eq_zero_of_positive_bd3 k f E
      ((P, e) :: (P, 1) :: Ps) As (by simp only [List.length_cons]; omega)
      (by simp only [List.length_cons]; omega) B'
    exact sub_eq_zero.mp h
  induction m generalizing B with
  | zero =>
    rw [originalMixedEulerDifference_cons_bd3,
      originalMixedEulerDifference_invariant f E Rest (bundleTensorRightUnitIso B.sheaf)]
    simp
  | succ m ih =>
    have hstep : originalMixedEulerDifference f E Rest
        (originalLineTensor B (originalPositivePowerLine_bd3 P (m + 1))) -
        originalMixedEulerDifference f E Rest (originalLineTensor B (originalPositivePowerLine_bd3 P m)) =
        originalMixedEulerDifference f E (originalPositivePowerLine_bd3 P 1 :: Rest) B := by
      rw [← hconst m B, originalMixedEulerDifference_cons_bd3,
        originalMixedEulerDifference_invariant f E Rest (powerLineSuccIso_bd3 f E P m B)]
      congr 1
      exact (originalMixedEulerDifference_invariant f E Rest
        (bundleTensorIso (Iso.refl _) (bundleTensorLeftUnitIso P.sheaf))).symm
    have hm := ih B
    rw [originalMixedEulerDifference_cons_bd3] at hm ⊢
    push_cast
    linarith

/-- Power removal in all ample slots: a top difference in directions `Pᵢ^{mᵢ}` (and the powers-one
directions `Qⱼ` and one arbitrary direction `A`) is `∏ mᵢ` times the power-one difference. -/
theorem originalMixedEulerDifference_powerLines_bd3 (A : IntrinsicLineBundle X) (B : IntrinsicLineBundle X) :
    ∀ (Ps : List (OriginalPositiveLine f (k + 1) E × ℕ)) (Qs : List (OriginalPositiveLine f (k + 1) E)),
      Ps.length + Qs.length = k →
      originalMixedEulerDifference f E
          (Ps.map (pl_bd3 k f E) ++ (Qs.map (fun Q => originalPositivePowerLine_bd3 Q 1) ++ [A])) B =
        ((Ps.map Prod.snd).prod : ℤ) * originalMixedEulerDifference f E
          ((Ps.map Prod.fst ++ Qs).map (fun Q => originalPositivePowerLine_bd3 Q 1) ++ [A]) B := by
  intro Ps
  induction Ps with
  | nil =>
    intro Qs _
    simp
  | cons p Ps ih =>
    intro Qs hlen
    obtain ⟨P, m⟩ := p
    simp only [List.length_cons] at hlen
    have hM := originalMixedEulerDifference_powerLine_cons_bd3 k f E P
      (Ps ++ Qs.map (fun Q => (Q, 1))) [A]
      (by simp only [List.length_append, List.length_map]; omega)
      (by simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]; omega) m B
    have hlist : (Ps ++ Qs.map (fun Q => (Q, 1))).map (pl_bd3 k f E) ++ [A] =
        Ps.map (pl_bd3 k f E) ++ (Qs.map (fun Q => originalPositivePowerLine_bd3 Q 1) ++ [A]) := by
      simp [List.map_append, List.map_map, Function.comp_def, pl_bd3]
    rw [hlist] at hM
    change originalMixedEulerDifference f E (originalPositivePowerLine_bd3 P m ::
      (Ps.map (pl_bd3 k f E) ++ (Qs.map (fun Q => originalPositivePowerLine_bd3 Q 1) ++ [A]))) B = _
    have hp1 : (originalPositivePowerLine_bd3 P 1 :: (Ps.map (pl_bd3 k f E) ++
        (Qs.map (fun Q => originalPositivePowerLine_bd3 Q 1) ++ [A]))).Perm
        (Ps.map (pl_bd3 k f E) ++ (originalPositivePowerLine_bd3 P 1 ::
          (Qs.map (fun Q => originalPositivePowerLine_bd3 Q 1) ++ [A]))) :=
      List.perm_middle.symm
    rw [hM, originalMixedEulerDifference_perm_bd3 f E hp1 B]
    have hih := ih (P :: Qs) (by simp only [List.length_cons]; omega)
    simp only [List.map_cons, List.cons_append] at hih
    rw [hih]
    have hperm : ((Ps.map Prod.fst ++ P :: Qs).map (fun Q => originalPositivePowerLine_bd3 Q 1) ++
        [A]).Perm ((P :: (Ps.map Prod.fst ++ Qs)).map (fun Q => originalPositivePowerLine_bd3 Q 1) ++
          [A]) :=
      List.Perm.append_right [A] (List.Perm.map _ List.perm_middle)
    rw [originalMixedEulerDifference_perm_bd3 f E hperm B]
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul, List.cons_append]
    ring

/-- **Mixed Snapper–Kleiman differences in ample directions are Chern integrals (EP-free).**
For `X` smooth projective of dimension `k + 1` over `ℂ`, ample (positively curved) line bundles
`P₁, …, P_k`, an ARBITRARY line bundle `A`, an arbitrary base `B` and ARBITRARY smooth hermitian
metrics `H` on `A` and `Kᵢ` on `Pᵢ`:
`Δ_{P₁} ⋯ Δ_{P_k} Δ_A χ(B) = ∫_{X(ℂ)} c₁(A, H) ∧ c₁(P₁, K₁) ∧ ⋯ ∧ c₁(P_k, K_k)`. -/
theorem originalMixedEulerDifference_ample_eq_slotIntegral_bd3
    (P : Fin k → OriginalPositiveLine f (k + 1) E) (A B : IntrinsicLineBundle X)
    (H : SchemeLineBundleMetric f (k + 1) E A.sheaf)
    (K : ∀ i, SchemeLineBundleMetric f (k + 1) E (P i).sheaf)
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    (originalMixedEulerDifference f E
        (List.ofFn (fun i => originalPositivePowerLine_bd3 (P i) 1) ++ [A]) B : ℝ) =
      slotIntegral κ (Fin.cons (H.curvature A.atlas) (fun i => (K i).curvature (P i).atlas)) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  obtain ⟨T⟩ := exists_wholeOriginalCITower k f E P
  have hchain := WholeOriginalCITower.mixedEuler_eq_power_product_of_metrics_bd3 k f E P T A B H K
    (genericPoint _) κ
  have hPR := originalMixedEulerDifference_powerLines_bd3 k f E A B
    (List.ofFn (fun i => (P i, WholeOriginalCITower.powers k T i))) []
    (by simp only [List.length_ofFn, List.length_nil, add_zero])
  simp only [List.map_nil, List.nil_append, List.append_nil, List.map_ofFn] at hPR
  have hdirs : originalCITowerCuttingDirections_bd3 k P T =
      List.ofFn (pl_bd3 k f E ∘ fun i => (P i, WholeOriginalCITower.powers k T i)) := rfl
  have hprodN : (List.ofFn (Prod.snd ∘ fun i => (P i, WholeOriginalCITower.powers k T i))).prod =
      ∏ i, WholeOriginalCITower.powers k T i := by
    rw [List.prod_ofFn]
    rfl
  have hpos : (0 : ℝ) < ∏ i, (WholeOriginalCITower.powers k T i : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast WholeOriginalCITower.powers_pos k T i
  dsimp only at hchain
  rw [hdirs, hPR, hprodN] at hchain
  push_cast at hchain
  exact mul_left_cancel₀ hpos.ne' hchain

/-- The line bundle underlying a positive line. -/
abbrev positiveLine_bd3 (P : OriginalPositiveLine f (k + 1) E) : IntrinsicLineBundle X :=
  ⟨P.sheaf, P.atlas⟩

/-- **Snapper–Kleiman = Chern integral for ample line bundles (EP-free).**  For `X` smooth
projective of dimension `n = k + 1` over `ℂ`, ample (positively curved) line bundles
`L₁, …, Lₙ`, ANY base line bundle `B` and ANY smooth hermitian metrics `hᵢ` on `Lᵢ`:
`Δ_{L₁} ⋯ Δ_{Lₙ} χ(B) = ∫_{X(ℂ)} c₁(L₁, h₁) ∧ ⋯ ∧ c₁(Lₙ, hₙ)`. -/
theorem snapperKleiman_eq_slotIntegral_bd3 (P : Fin (k + 1) → OriginalPositiveLine f (k + 1) E)
    (B : IntrinsicLineBundle X) (K : ∀ i, SchemeLineBundleMetric f (k + 1) E (P i).sheaf)
    (κ : KahlerBackground (k + 1) (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : MeasurableSpace (SchemeComplexPoint f) := borel _
    let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    (originalMixedEulerDifference f E (List.ofFn (fun i => positiveLine_bd3 k f E (P i))) B : ℝ) =
      slotIntegral κ (fun i => (K i).curvature (P i).atlas) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have h := originalMixedEulerDifference_ample_eq_slotIntegral_bd3 k f E (fun i => P i.succ)
    (positiveLine_bd3 k f E (P 0)) B (K 0) (fun i => K i.succ) κ
  have hcons : (Fin.cons ((K 0).curvature (P 0).atlas) (fun i => (K i.succ).curvature (P i.succ).atlas) :
      Fin (k + 1) → ClosedRealOneOneForm (k + 1) (SchemeComplexPoint f)) =
      fun i => (K i).curvature (P i).atlas :=
    Fin.cons_self_tail (fun i => (K i).curvature (P i).atlas)
  dsimp only at h ⊢
  rw [hcons] at h
  rw [← h]
  congr 1
  rw [List.ofFn_succ]
  refine (originalMixedEulerDifference_perm_bd3 f E (List.perm_append_singleton _ _).symm B).trans ?_
  apply originalMixedEulerDifference_congr_lines_bd3
  refine forall₂_iso_append_bd3 ?_ (forall₂_iso_refl_bd3 _)
  exact forall₂_iso_ofFn_bd3 k _ _ (fun i => (bundleTensorLeftUnitIso (P i.succ).sheaf).symm)

/-- The Snapper–Kleiman number of ample line bundles does not depend on the base line bundle. -/
theorem snapperKleiman_independent_base_bd3 (P : Fin (k + 1) → OriginalPositiveLine f (k + 1) E)
    (B B' : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (List.ofFn (fun i => positiveLine_bd3 k f E (P i))) B =
      originalMixedEulerDifference f E (List.ofFn (fun i => positiveLine_bd3 k f E (P i))) B' := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  let Q := originalHyperplanePositiveLine f (k + 1) E
  let κ : KahlerBackground (k + 1) (SchemeComplexPoint f) := ⟨Q.curvature, Q.positive⟩
  have h := (snapperKleiman_eq_slotIntegral_bd3 k f E P B (fun i => (P i).metric) κ).trans
    (snapperKleiman_eq_slotIntegral_bd3 k f E P B' (fun i => (P i).metric) κ).symm
  exact_mod_cast h

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
