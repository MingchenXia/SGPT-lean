import SGPT.Okounkov.FlagValuationGlobalPolynomialZeros

/-!
# Whole original flags are determined by equivalent original field valuations

On the SAME original smooth projective scheme, genuine native flag field
valuations determine every literal original smooth flag member. Prefix
signs on identical actual algebraic polynomial coefficients give the
global homogeneous equations, and the existing actual Chow theorem
reconstructs the entire analytic carriers.

No arbitrary-valuation flag presentation, common resolution or independence
across different birational models/current-value readers is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos

/-- Actual analytic projective subsets are reconstructed from the actual
homogeneous polynomials vanishing on them, using genuine Chow zero loci. -/
theorem analytic_subset_eq_of_global_homogeneous_polynomials {n N : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [CompactSpace M] {Ψ : M → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {C D : Set M}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D)
    (hpoly : ∀ (d : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ), P.IsHomogeneous d →
      ((∀ y ∈ C, MvPolynomial.eval (Ψ y).rep P = 0) ↔
        ∀ y ∈ D, MvPolynomial.eval (Ψ y).rep P = 0)) : C = D := by
  have hsub : ∀ {A B : Set M}, IsComplexAnalyticSubset (n := n) A →
      (∀ (d : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ), P.IsHomogeneous d →
        (∀ y ∈ A, MvPolynomial.eval (Ψ y).rep P = 0) →
          ∀ y ∈ B, MvPolynomial.eval (Ψ y).rep P = 0) → B ⊆ A := by
    intro A B hA hAB
    obtain ⟨d₀, hd₀⟩ := chow_image hΨ hA
    obtain ⟨μ, _, P, hP, -, hzero⟩ := hd₀ d₀ le_rfl
    intro y hy
    have hImg : Ψ y ∈ Ψ '' A := by
      rw [hzero]
      intro j
      apply hAB d₀ (P j) (hP j) ?_ y hy
      intro z hz
      have hmem : Ψ z ∈ Ψ '' A := ⟨z, hz, rfl⟩
      rw [hzero] at hmem
      exact hmem j
    obtain ⟨z, hz, heq⟩ := hImg
    exact (hΨ.injective heq) ▸ hz
  exact Subset.antisymm (hsub hD (fun d P hP => (hpoly d P hP).mpr))
    (hsub hC (fun d P hP => (hpoly d P hP).mp))

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance flagChoiceTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance flagChoiceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance flagChoiceManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The actual original field-prefix value of an original algebraic Chow
coefficient detects GLOBAL vanishing on the actual original flag member. -/
theorem schemeOriginalFlagPrefix_polyCoef_pos_iff_global_zero (E : ClosedProjectiveEmbedding f)
    (omega : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (k : ℕ) (hk : k ≤ n) (i : Fin (E.ambientDimension + 1))
    (hi : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val ∈ coordOpen E i)
    {d : ℕ} (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) (hP : P.IsHomogeneous d) :
    (0 < ValCurr.prefixValuation hk (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY)
      (algebraMap _ X.functionField
        (X.presheaf.germ (coordOpen E i)
          (schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val)
          hi (polyCoef E i P))) ↔
      ∀ y ∈ Y ⟨k, Nat.lt_succ_of_le hk⟩,
        MvPolynomial.eval (projectivePoint f E n y).rep P = 0) := by
  exact (schemeOriginalFlagPrefix_polyCoef_pos_iff f E n omega Y hY k hk i hi P).trans
    (originalFlag_genFun_mem_iff_global_polynomial_zero
      (schemeProjectiveOriginalFlagGeometry f n E omega Y hY)
      (schemeProjectiveOriginalFlagPoint f n E omega Y hY)
      (projectivePoint f E n) (isHolomorphicEmbedding_projectivePoint f E n)
      k hk i ((projectivePoint_mem_source_iff f E n i _).mpr hi) hP)

/-- Equivalent actual native field valuations have identical GLOBAL
homogeneous polynomial equations on every original analytic flag member. -/
theorem schemeOriginalFlags_global_polynomial_zero_iff_of_lexEquivalent (E : ClosedProjectiveEmbedding f)
    (omega omega' : KahlerBackground n (SchemeComplexPoint f))
    (Y Z : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) (hZ : IsSmoothFlag Z)
    (h : ValCurr.ValuationsLexEquivalent
      (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY)
      (schemeOriginalFlagFunctionFieldValuation f n E omega' Z hZ))
    (k : ℕ) (hk : k ≤ n) {d : ℕ}
    (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) (hP : P.IsHomogeneous d) :
    (∀ y ∈ Y ⟨k, Nat.lt_succ_of_le hk⟩, MvPolynomial.eval (projectivePoint f E n y).rep P = 0) ↔
      ∀ y ∈ Z ⟨k, Nat.lt_succ_of_le hk⟩, MvPolynomial.eval (projectivePoint f E n y).rep P = 0 := by
  let pY := (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val
  let pZ := (schemeProjectiveOriginalFlagPoint f n E omega' Z hZ).val
  have hpoints : pY = pZ := schemeComplexPointImage_injective f
    (schemeOriginalFlagEndpoint_eq_of_lexEquivalent f n E omega omega' Y Z hY hZ h)
  let i := frameIndex f E pY
  have hiY : schemeComplexPointImage f pY ∈ coordOpen E i := mem_coordOpen_frameIndex f E pY
  have hiZ : schemeComplexPointImage f pZ ∈ coordOpen E i := by rw [← hpoints]; exact hiY
  let qY : X.functionField := algebraMap _ X.functionField
    (X.presheaf.germ (coordOpen E i) (schemeComplexPointImage f pY) hiY (polyCoef E i P))
  let qZ : X.functionField := algebraMap _ X.functionField
    (X.presheaf.germ (coordOpen E i) (schemeComplexPointImage f pZ) hiZ (polyCoef E i P))
  have hq : qY = qZ := by
    change (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
      ((X.presheaf.germ (coordOpen E i) (schemeComplexPointImage f pY) hiY).hom (polyCoef E i P)) =
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
      ((X.presheaf.germ (coordOpen E i) (schemeComplexPointImage f pZ) hiZ).hom (polyCoef E i P))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes,
      ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hsign :
      0 < ValCurr.prefixValuation hk (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY) qY ↔
        0 < ValCurr.prefixValuation hk (schemeOriginalFlagFunctionFieldValuation f n E omega' Z hZ) qZ := by
    rw [← hq]
    obtain ⟨G, hG, hmap⟩ := h
    rw [hmap]
    exact (ValCurr.prefixValuation_pos_lexMap_iff hk hG _ qY).symm
  exact (schemeOriginalFlagPrefix_polyCoef_pos_iff_global_zero f n E omega Y hY k hk i hiY P hP).symm.trans
    (hsign.trans (schemeOriginalFlagPrefix_polyCoef_pos_iff_global_zero f n E omega' Z hZ k hk i hiZ P hP))

/-- On the SAME original smooth projective scheme, equivalent actual full
native flag field valuations determine ALL literal original flag members,
with no flag or centre equality supplied as a hypothesis. -/
theorem schemeOriginalFlags_eq_of_lexEquivalent (E : ClosedProjectiveEmbedding f)
    (omega omega' : KahlerBackground n (SchemeComplexPoint f))
    (Y Z : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) (hZ : IsSmoothFlag Z)
    (h : ValCurr.ValuationsLexEquivalent
      (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY)
      (schemeOriginalFlagFunctionFieldValuation f n E omega' Z hZ)) : Y = Z := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  funext j
  apply analytic_subset_eq_of_global_homogeneous_polynomials
    (isHolomorphicEmbedding_projectivePoint f E n)
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (show IsClosedSubmanifold n (Y j) from
        ⟨(hY.2.2 j).1, fun x hx => ⟨n - (j : ℕ), (hY.2.2 j).2.2 x hx⟩⟩))
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (show IsClosedSubmanifold n (Z j) from
        ⟨(hZ.2.2 j).1, fun x hx => ⟨n - (j : ℕ), (hZ.2.2 j).2.2 x hx⟩⟩))
  intro d P hP
  exact schemeOriginalFlags_global_polynomial_zero_iff_of_lexEquivalent f n E omega omega'
    Y Z hY hZ h j.val (Nat.le_of_lt_succ j.isLt) P hP

end Scheme

end SGPT.Okounkov
