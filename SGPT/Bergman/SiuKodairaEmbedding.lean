import SGPT.Bergman.SiuKodairaSeparation
import SGPT.Bergman.SiuKodairaProjectiveImmersion
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass

/-!
# Kodaira embedding of the original compact complex manifold

A positive original Hermitian holomorphic line bundle supplies one actual
positive power whose actual native global sections define a closed
holomorphic projective embedding, with injective original differential.
All dimensions and the empty manifold are included.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:embedding`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Compactness makes the actual injective native section map a closed embedding. -/
theorem nativeBasisSectionMap_isClosedEmbedding [CompactSpace X]
    (E : HermitianHolomorphicLineBundle.{0, 0} n X) {N : ℕ}
    (b : Module.Basis (Fin (N + 1)) ℂ (HolomorphicSections (n := n) E.Fiber))
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), b j x ≠ 0)
    (hsep : ∀ p q : X, p ≠ q → ∃ s : HolomorphicSections (n := n) E.Fiber,
      s p = 0 ∧ s q ≠ 0) :
    Topology.IsClosedEmbedding (sourceNativeFiniteSectionProjectiveMap E b hgen) :=
  (sourceNativeFiniteSectionProjectiveMap_contMDiff E b hgen).continuous.isClosedEmbedding
    (nativeBasisSectionMap_injective E b hgen hsep)

/-- The positive-dimensional Kodaira embedding is constructed from the actual
positive-power separating sections and a genuine full H0 basis. -/
theorem kodairaEmbedding_pos [CompactSpace X] [Nonempty X] (hn : 0 < n)
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (N : ℕ)
      (s : Fin (N + 1) → HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber)
      (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      Topology.IsClosedEmbedding
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) p) := by
  obtain ⟨d, hd, hbase, hpoint, hjet⟩ := exists_positivePower_point_tangent_separation hn G hG θG hθG hKah
  obtain ⟨N, b, hgen⟩ := exists_finite_basis_generating (positivePower G (d - 1)) hbase
  exact ⟨d, hd, N, b, hgen, sourceNativeFiniteSectionProjectiveMap_contMDiff _ b hgen,
    nativeBasisSectionMap_isClosedEmbedding _ b hgen hpoint,
    nativeBasisSectionMap_mfderiv_injective _ b hgen hjet⟩

/-- The empty original manifold has its literal section map into the actual
projective point; its actual section family is the single zero section. -/
theorem kodairaEmbedding_empty [CompactSpace X] [IsEmpty X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (N : ℕ)
      (s : Fin (N + 1) → HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber)
      (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      Topology.IsClosedEmbedding
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) p) := by
  let s : Fin 1 → HolomorphicSections (n := n) G.Fiber := fun _ => 0
  have hgen : ∀ x : X, ∃ j : Fin 1, s j x ≠ 0 := fun x => isEmptyElim x
  have hi : Function.Injective (sourceNativeFiniteSectionProjectiveMap G s hgen) := by
    intro x
    exact isEmptyElim x
  refine ⟨1, one_pos, 0, s, hgen, sourceNativeFiniteSectionProjectiveMap_contMDiff G s hgen,
    (sourceNativeFiniteSectionProjectiveMap_contMDiff G s hgen).continuous.isClosedEmbedding hi, ?_⟩
  exact fun p => isEmptyElim p

/-- In dimension zero, actual point-supported fibre sections give the genuine
projective embedding; no positive-dimensional jet hypothesis is introduced. -/
theorem kodairaEmbedding_zero {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
    [IsComplexManifold 0 X] [CompactSpace X] [Nonempty X]
    (G : HermitianHolomorphicLineBundle.{0, 0} 0 X) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (N : ℕ)
      (s : Fin (N + 1) → HolomorphicSections (n := 0) (positivePower G (d - 1)).Fiber)
      (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0),
      ContMDiff 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ComplexModel N) ∞
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      Topology.IsClosedEmbedding
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ComplexModel N)
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) p) := by
  classical
  let _ : DiscreteTopology X := (ZeroDimensionalGlobalMixedMass.compact_zero_dim_finite_discrete (M := X)).1
  let spike (p : X) : HolomorphicSections (n := 0) G.Fiber := {
    toFun := Function.update (fun _ => 0) p ((prefFrame G p).val.symm p 1)
    contMDiff_toFun := contMDiff_of_discreteTopology }
  have hspike : ∀ p : X, spike p p ≠ 0 := by
    intro p
    change Function.update (fun _ => 0) p ((prefFrame G p).val.symm p 1) p ≠ 0
    rw [Function.update_self]
    let e := prefFrame G p
    let := e.property
    have hp : p ∈ e.val.baseSet := mem_prefFrame G p
    have hcoef : e.val.continuousLinearMapAt ℂ p (e.val.symm p 1) = 1 := trivialization_coef_frame e.val hp
    intro hz
    rw [hz, map_zero] at hcoef
    exact zero_ne_one hcoef
  have hbase : ∀ p : X, ∃ s : HolomorphicSections (n := 0) G.Fiber, s p ≠ 0 :=
    fun p => ⟨spike p, hspike p⟩
  have hpoint : ∀ p q : X, p ≠ q → ∃ s : HolomorphicSections (n := 0) G.Fiber,
      s p = 0 ∧ s q ≠ 0 := by
    intro p q hpq
    refine ⟨spike q, ?_, hspike q⟩
    change Function.update (fun _ => 0) q ((prefFrame G q).val.symm q 1) p = 0
    rw [Function.update_of_ne hpq]
  obtain ⟨N, b, hgen⟩ := exists_finite_basis_generating G hbase
  refine ⟨1, one_pos, N, b, hgen, sourceNativeFiniteSectionProjectiveMap_contMDiff G b hgen,
    nativeBasisSectionMap_isClosedEmbedding G b hgen hpoint, ?_⟩
  intro p v w _
  exact @Subsingleton.elim (ComplexModel 0) inferInstance v w

/-- Kodaira embedding from the original compact complex manifold and original
positive Hermitian line bundle, for every dimension and without added output
certificates. The projective map is defined by actual sections of one fixed
literal positive tensor power of that original bundle. -/
theorem kodairaEmbedding [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (N : ℕ)
      (s : Fin (N + 1) → HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber)
      (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      Topology.IsClosedEmbedding
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) p) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · let _ : IsEmpty X := hX
    exact kodairaEmbedding_empty G
  · let _ : Nonempty X := hX
    by_cases hn : n = 0
    · subst n
      exact kodairaEmbedding_zero G
    · exact kodairaEmbedding_pos (Nat.pos_of_ne_zero hn) G hG θG hθG hKah

end SGPT.Bergman.SiuKodaira
