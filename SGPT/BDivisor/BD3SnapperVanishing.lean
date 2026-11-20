import SGPT.BDivisor.BD3RegularCutPower
import SGPT.BDivisor.BD3MixedEulerChernPeriod

/-!
# Snapper vanishing in ample directions, without the earlier envelope formalization

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749): the book's intersection numbers agree with
Dang–Favre's algebraic (Snapper–Kleiman) ones.  The algebraic numbers are the top mixed differences
`Δ_{A₁} ⋯ Δ_{Aₙ} χ(B) = ∑_{I ⊆ {1..n}} (-1)^{n-|I|} χ(B ⊗ ⊗_{i∈I} Aᵢ)` of Euler characteristics
(`originalMixedEulerDifference`, Čech Euler characteristics of line bundles on a smooth projective
scheme over `ℂ`); Snapper's theorem says that `(n+1)`-fold differences vanish on an `n`-dimensional
scheme, so that the top differences are multilinear and independent of `B`.

This file proves the vanishing EP-free whenever at least `n - 1` of the `n + 1` directions are
tensor powers of ample (positively curved) line bundles
(`originalMixedEulerDifference_eq_zero_of_positive_bd3`), by induction on the dimension:
* dimension one: Riemann–Roch on smooth projective curves (`…_curve_two_cons_bd3`);
* induction step: cut by smooth members of `|P^d|` and `|P^(d+1)|` for two CONSECUTIVE powers
  (`exists_originalRegularCut_power_ge`, from Siu's uniform generation in every large power); the cut
  exact sequence (`originalCICut_mixedEuler_restriction_bd3`) and the inductive hypothesis on the cut
  give periodicity of the remaining difference under `P^d` and `P^(d+1)`, hence under `P`.

Also proved: permutation invariance of the mixed differences (`originalMixedEulerDifference_perm_bd3`;
Codex's version is on the EP side).
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass

local instance bd3VanishingTopology {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd3VanishingCharts {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd3VanishingManifold {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

section Algebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

/-- The defining recursion of the mixed differences: the head direction is the outer difference. -/
theorem originalMixedEulerDifference_cons_bd3 (A : IntrinsicLineBundle X)
    (As : List (IntrinsicLineBundle X)) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E (A :: As) B =
      originalMixedEulerDifference f E As (originalLineTensor B A) -
        originalMixedEulerDifference f E As B :=
  rfl

/-- The mixed Euler differences are invariant under arbitrary permutations of the directions
(EP-free: adjacent swaps by the original tensor swap isomorphism). -/
theorem originalMixedEulerDifference_perm_bd3 {As Cs : List (IntrinsicLineBundle X)}
    (h : As.Perm Cs) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E As B = originalMixedEulerDifference f E Cs B := by
  induction h generalizing B with
  | nil => rfl
  | cons x _ ih =>
    rw [originalMixedEulerDifference_cons_bd3, originalMixedEulerDifference_cons_bd3, ih, ih]
  | swap x y l => exact originalMixedEulerDifference_swap f E y x l B
  | trans _ _ ih₁ ih₂ => exact (ih₁ B).trans (ih₂ B)

/-- `Forall₂` of sheaf isomorphisms is compatible with concatenation. -/
theorem forall₂_iso_append_bd3 {Y : Scheme.{0}} {l₁ l₂ l₃ l₄ : List (IntrinsicLineBundle Y)}
    (h₁ : List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) l₁ l₂)
    (h₂ : List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) l₃ l₄) :
    List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) (l₁ ++ l₃) (l₂ ++ l₄) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

/-- Pointwise sheaf isomorphisms give `Forall₂` along mapped lists. -/
theorem forall₂_iso_map_bd3 {Y : Scheme.{0}} {α : Type*} (l : List α)
    (g h : α → IntrinsicLineBundle Y) (e : ∀ a, Nonempty ((g a).sheaf ≅ (h a).sheaf)) :
    List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) (l.map g) (l.map h) := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (e a) ih

/-- Reflexivity of `Forall₂` of sheaf isomorphisms. -/
theorem forall₂_iso_refl_bd3 {Y : Scheme.{0}} (l : List (IntrinsicLineBundle Y)) :
    List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons ⟨Iso.refl _⟩ ih

variable {n : ℕ} [SmoothOfRelativeDimension n f]

/-- `B ⊗ P^(q+1) ≅ (B ⊗ P^q) ⊗ P`. -/
def powerLineSuccIso_bd3 (P : OriginalPositiveLine f n E) (q : ℕ) (B : IntrinsicLineBundle X) :
    (originalLineTensor B (originalPositivePowerLine_bd3 P (q + 1))).sheaf ≅
      (originalLineTensor (originalLineTensor B (originalPositivePowerLine_bd3 P q))
        ⟨P.sheaf, P.atlas⟩).sheaf :=
  (originalLineTensorAssociatorIso B.atlas (P.atlas.tensorPower q) P.atlas).symm

/-- `(B ⊗ P) ⊗ P^d ≅ B ⊗ P^(d+1)`. -/
def powerLineShiftIso_bd3 (P : OriginalPositiveLine f n E) (d : ℕ) (B : IntrinsicLineBundle X) :
    (originalLineTensor (originalLineTensor B ⟨P.sheaf, P.atlas⟩)
        (originalPositivePowerLine_bd3 P d)).sheaf ≅
      (originalLineTensor B (originalPositivePowerLine_bd3 P (d + 1))).sheaf :=
  originalLineTensorAssociatorIso B.atlas P.atlas (P.atlas.tensorPower d) ≪≫
    bundleTensorIso (Iso.refl B.sheaf) (originalLineTensorCommutorIso P.atlas (P.atlas.tensorPower d))

/-- A function of the base line which is invariant under `⊗ P^d` and `⊗ P^(d+1)` is invariant
under every `⊗ P^q`. -/
theorem originalMixedEulerDifference_powerPeriodic_bd3 (P : OriginalPositiveLine f n E)
    (As : List (IntrinsicLineBundle X)) (d : ℕ)
    (h₁ : ∀ B, originalMixedEulerDifference f E As
      (originalLineTensor B (originalPositivePowerLine_bd3 P d)) = originalMixedEulerDifference f E As B)
    (h₂ : ∀ B, originalMixedEulerDifference f E As
      (originalLineTensor B (originalPositivePowerLine_bd3 P (d + 1))) =
        originalMixedEulerDifference f E As B)
    (q : ℕ) (B : IntrinsicLineBundle X) :
    originalMixedEulerDifference f E As (originalLineTensor B (originalPositivePowerLine_bd3 P q)) =
      originalMixedEulerDifference f E As B := by
  have hP : ∀ B : IntrinsicLineBundle X, originalMixedEulerDifference f E As
      (originalLineTensor B ⟨P.sheaf, P.atlas⟩) = originalMixedEulerDifference f E As B := by
    intro B
    rw [← h₁ (originalLineTensor B ⟨P.sheaf, P.atlas⟩),
      originalMixedEulerDifference_invariant f E As (powerLineShiftIso_bd3 f E P d B), h₂ B]
  induction q generalizing B with
  | zero =>
    exact originalMixedEulerDifference_invariant f E As (bundleTensorRightUnitIso B.sheaf)
  | succ q ih =>
    rw [originalMixedEulerDifference_invariant f E As (powerLineSuccIso_bd3 f E P q B), hP, ih]

end Algebra

/-- **Snapper vanishing in ample directions (EP-free).**  Let `X` be smooth projective of
dimension `k + 1` over `ℂ` (closed projective embedding `E`).  Every `(k+2)`-fold (or longer) mixed
Euler difference of line bundles vanishes as soon as at least `k` of its directions are tensor
powers `P^m` of positive (ample) line bundles; the other directions are arbitrary line bundles. -/
theorem originalMixedEulerDifference_eq_zero_of_positive_bd3 (k : ℕ) :
    ∀ {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension (k + 1) f]
      [IsSeparated f] [QuasiCompact f] (E : ClosedProjectiveEmbedding f)
      (Ps : List (OriginalPositiveLine f (k + 1) E × ℕ)) (As : List (IntrinsicLineBundle X)),
      k ≤ Ps.length → k + 2 ≤ Ps.length + As.length → ∀ B : IntrinsicLineBundle X,
        originalMixedEulerDifference f E
          (Ps.map (fun p => originalPositivePowerLine_bd3 p.1 p.2) ++ As) B = 0 := by
  induction k with
  | zero =>
    intro X f _ _ _ E Ps As _ hlen B
    have : SmoothOfRelativeDimension 1 f := ‹SmoothOfRelativeDimension (0 + 1) f›
    have hl : 2 ≤ (Ps.map (fun p => originalPositivePowerLine_bd3 p.1 p.2) ++ As).length := by
      simp only [List.length_append, List.length_map]
      omega
    generalize Ps.map (fun p => originalPositivePowerLine_bd3 p.1 p.2) ++ As = L at hl ⊢
    match L, hl with
    | [], h => simp at h
    | [_], h => simp at h
    | A :: C :: Cs, _ =>
      exact originalMixedEulerDifference_curve_two_cons_bd3 f E A C Cs B (genericPoint _)
  | succ k ih =>
    intro X f _ _ _ E Ps As hPs hlen B
    cases Ps with
    | nil => simp at hPs
    | cons p Ps' =>
      obtain ⟨P, m⟩ := p
      simp only [List.length_cons] at hPs hlen
      let pl : OriginalPositiveLine f (k + 1 + 1) E × ℕ → IntrinsicLineBundle X :=
        fun p => originalPositivePowerLine_bd3 p.1 p.2
      change originalMixedEulerDifference f E
        (originalPositivePowerLine_bd3 P m :: (Ps'.map pl ++ As)) B = 0
      -- every regular cut of `P` makes the tail difference periodic
      have hcut : ∀ (C : OriginalRegularCut f (k + 1) E P) (B' : IntrinsicLineBundle X),
          originalMixedEulerDifference f E
            (originalCICutLine_bd3 f E (k + 1) P C :: (Ps'.map pl ++ As)) B' = 0 := by
        intro C B'
        rw [originalCICut_mixedEuler_restriction_bd3 f E (k + 1) P C (Ps'.map pl ++ As) B']
        have h := ih (C.inclusion ≫ f) C.embedding
          (Ps'.map (fun p => (C.restrictLine p.1, p.2))) (As.map (originalLinePullback C.inclusion))
          (by simp only [List.length_map]; omega) (by simp only [List.length_map]; omega)
          (originalLinePullback C.inclusion
            (originalLineTensor B' (originalCICutLine_bd3 f E (k + 1) P C)))
        rw [← h]
        apply originalMixedEulerDifference_congr_lines_bd3
        rw [List.map_append, List.map_map, List.map_map]
        refine forall₂_iso_append_bd3 ?_ (forall₂_iso_refl_bd3 _)
        exact forall₂_iso_map_bd3 Ps' _ _ (fun p =>
          ⟨originalLinePullbackPowerIso C.inclusion p.1.atlas p.2⟩)
      have hper : ∀ (d : ℕ) (C : OriginalRegularCut f (k + 1) E P), C.nativeCut.power = d →
          ∀ B' : IntrinsicLineBundle X, originalMixedEulerDifference f E (Ps'.map pl ++ As)
            (originalLineTensor B' (originalPositivePowerLine_bd3 P d)) =
              originalMixedEulerDifference f E (Ps'.map pl ++ As) B' := by
        intro d C hC B'
        have h := hcut C B'
        rw [originalMixedEulerDifference_cons_bd3, sub_eq_zero] at h
        subst hC
        exact h
      obtain ⟨d₀, hd₀⟩ := exists_originalRegularCut_power_ge f (k + 1) E P
      obtain ⟨C₁, hC₁⟩ := hd₀ d₀ le_rfl
      obtain ⟨C₂, hC₂⟩ := hd₀ (d₀ + 1) (Nat.le_succ _)
      rw [originalMixedEulerDifference_cons_bd3, sub_eq_zero]
      exact originalMixedEulerDifference_powerPeriodic_bd3 f E P (Ps'.map pl ++ As) d₀
        (hper d₀ C₁ hC₁) (hper (d₀ + 1) C₂ hC₂) m B

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
