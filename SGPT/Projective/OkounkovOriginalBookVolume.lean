import SGPT.Projective.OkounkovOriginalAllDimensions

/-! Entire cor:Okounvol for SAME original arbitrary surjective valuation, ALL dimensions.
Blueprint: okounkov-original-book-volume.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

include E in
/-- Actual original independent smooth flag, including dimension zero, manufactured from SAME embedding. -/
theorem exists_original_smoothFlag_allDimensions :
    ∃ Y : Fin (n+1) → Set (SchemeComplexPoint f), IsSmoothFlag Y := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  exact SGPT.GAGA.SmoothFlags.exists_isSmoothFlag_of_injective (SGPT.GAGA.H0S.projectivePoint f E n)
    (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding
      (SGPT.GAGA.H0S.isHolomorphicEmbedding_projectivePoint f E n))
    (SGPT.GAGA.H0S.injective_projectivePoint f E n)

variable {L : X.Modules} (a : LineBundleAtlas L) (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
  (hv : Function.Surjective v) (c : X)
include E hbig hv

/-- Actual SAME original section dimensions converge to SAME original body volume, without cone premise. -/
theorem tendsto_normalized_h0_okounkovBody_allDimensions :
    Tendsto (fun k : ℕ => (k:ℝ)⁻¹^n * (SGPT.LineBundle.h0 f L k : ℝ)) atTop
      (𝓝 (volume.real (okounkovBody v c a))) := by
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  obtain ⟨C,hC,hG⟩ := exists_original_admissibleCone_allDimensions f a n E hbig v hv c
  exact ValGen.tendsto_normalized_h0_okounkovBody f E Y hY a c v hC hG

/-- Existing original line volume, factorial and SAME original generated body, ALL dimensions. -/
theorem volume_eq_factorial_mul_okounkovBody_allDimensions :
    SGPT.LineBundle.volume f L n = ENNReal.ofReal ((n.factorial:ℝ) * volume.real (okounkovBody v c a)) :=
  SGPT.LineBundle.volume_eq_of_tendsto
    (tendsto_normalized_h0_okounkovBody_allDimensions f n E a hbig v hv c)

/-- Literal entire source cor:Okounvol, SAME original extended volume, no cone/flag/generation premise. -/
theorem volume_okounkovBody_eq_volume_div_factorial_allDimensions :
    volume (okounkovBody v c a) = SGPT.LineBundle.volume f L n / (n.factorial:ℝ≥0∞) := by
  obtain ⟨C,hC,hG⟩ := exists_original_admissibleCone_allDimensions f a n E hbig v hv c
  have hfinite : volume (okounkovBody v c a) ≠ ⊤ :=
    (isCompact_body C _ hC (nonempty_of_generatedGroup_eq_top _ hG)).measure_lt_top.ne
  have heq := volume_eq_factorial_mul_okounkovBody_allDimensions f n E a hbig v hv c
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n.factorial),measureReal_def,
    ENNReal.ofReal_toReal hfinite] at heq
  have hcast : ENNReal.ofReal (n.factorial:ℝ) = (n.factorial:ℝ≥0∞) := by simp
  rw [hcast] at heq
  exact (ENNReal.eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n) (by simp)).mpr heq.symm

end SGPT.Okounkov.OriginalBook
