import SGPT.Foundations.Analysis.FirstPass.Subgeodesics
import SGPT.Foundations.Analysis.FirstPass.FiniteVaryingTranslation
import SGPT.Foundations.Analysis.FirstPass.PshRealConvexity

set_option autoImplicit false

/-!
# Affine vertical translations of subgeodesics

Adding `A t + B` to a subgeodesic preserves its interior strip-PSH
condition.  The complexified correction is the pluriharmonic function
`A * re τ + B` pulled back from the strip coordinate.
-/

open Filter Set

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Add the real affine function `A t + B` vertically to a curve of
extended-real potentials. -/
def affineTranslatedCurve (curve : ℝ → M → EReal) (A B : ℝ) :
    ℝ → M → EReal :=
  fun t x => curve t x + ((A * t + B : ℝ) : EReal)

omit [TopologicalSpace M] in
@[simp] theorem affineTranslatedCurve_apply
    (curve : ℝ → M → EReal) (A B t : ℝ) (x : M) :
    affineTranslatedCurve curve A B t x =
      curve t x + ((A * t + B : ℝ) : EReal) := rfl

omit [TopologicalSpace M] in
/-- Successive affine translations add their slopes and intercepts. -/
@[simp] theorem affineTranslatedCurve_affineTranslatedCurve
    (curve : ℝ → M → EReal) (A B C D : ℝ) :
    affineTranslatedCurve (affineTranslatedCurve curve A B) C D =
      affineTranslatedCurve curve (A + C) (B + D) := by
  funext t x
  change (curve t x + ((A * t + B : ℝ) : EReal)) +
      ((C * t + D : ℝ) : EReal) =
    curve t x + ((((A + C) * t + (B + D) : ℝ)) : EReal)
  rw [add_assoc, ← EReal.coe_add]
  congr 1
  ring_nf

omit [TopologicalSpace M] in
/-- The zero affine translation is the identity. -/
@[simp] theorem affineTranslatedCurve_zero (curve : ℝ → M → EReal) :
    affineTranslatedCurve curve 0 0 = curve := by
  funext t x
  simp [affineTranslatedCurve]

omit [TopologicalSpace M] in
/-- Translation by the opposite affine function is the inverse operation. -/
@[simp] theorem affineTranslatedCurve_inverse
    (curve : ℝ → M → EReal) (A B : ℝ) :
    affineTranslatedCurve (affineTranslatedCurve curve A B) (-A) (-B) = curve := by
  rw [affineTranslatedCurve_affineTranslatedCurve]
  funext t x
  simp [affineTranslatedCurve]

omit [TopologicalSpace M] in
/-- The same inverse identity with the opposite translation written first. -/
@[simp] theorem affineTranslatedCurve_inverse_left
    (curve : ℝ → M → EReal) (A B : ℝ) :
    affineTranslatedCurve (affineTranslatedCurve curve (-A) (-B)) A B = curve := by
  simp

/-- The strip-PSH condition is invariant under vertical translation by a
real affine function of time. -/
theorem IsSubgeodesicInterior.affineTranslated
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior θ curve) (A B : ℝ) :
    IsSubgeodesicInterior θ (affineTranslatedCurve curve A B) := by
  constructor
  · intro t ht
    exact (h.thetaPshPotential ht).add_const (A * t + B)
  · intro e z hz
    rcases h.complexified_psh e hz with ⟨W, ρ, hzW, hρ, hpsh⟩
    refine ⟨W, ρ, hzW, hρ, ?_⟩
    let temporalProjection :
        ComplexModel n × ℂ →L[ℂ] ℂ :=
      ContinuousLinearMap.snd ℂ (ComplexModel n) ℂ
    have haffine : PlurisubharmonicOn
        (fun p : ComplexModel n × ℂ =>
          (((A * p.2.re + B : ℝ)) : EReal)) Set.univ := by
      have hpull :=
        (plurisubharmonicOn_coe_affine_re A B Set.univ).comp_continuousLinearMap
          temporalProjection
      simpa [temporalProjection] using hpull
    have hsum := hpsh.add (haffine.mono (Set.subset_univ _))
    change PlurisubharmonicOn
      (fun p => (chartFunction (curve p.2.re) e p.1 +
        (((A * p.2.re + B : ℝ)) : EReal)) + (ρ p.1 : EReal))
      (geodesicChartDomain W)
    change PlurisubharmonicOn
      (fun p => (chartFunction (curve p.2.re) e p.1 + (ρ p.1 : EReal)) +
        (((A * p.2.re + B : ℝ)) : EReal))
      (geodesicChartDomain W) at hsum
    convert hsum using 1
    funext p
    ac_rfl

/-- A vertical affine translation carries a subgeodesic with endpoints
`u₀,u₁` to one with endpoints `u₀+B,u₁+A+B`. -/
theorem IsSubgeodesicFrom.affineTranslated
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom θ curve u₀ u₁)
    (A B : ℝ) :
    IsSubgeodesicFrom θ (affineTranslatedCurve curve A B)
      (fun x => u₀ x + (B : EReal))
      (fun x => u₁ x + ((A + B : ℝ) : EReal)) := by
  refine ⟨h.left_endpoint.add_const B,
    h.right_endpoint.add_const (A + B), h.interior.affineTranslated A B,
    ?_, ?_⟩
  · apply h.tendsto_left.add_tendsto_const
    have hcont : Continuous (fun t : ℝ => A * t + B) := by fun_prop
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto (0 : ℝ))
  · apply h.tendsto_right.add_tendsto_const
    have hcont : Continuous (fun t : ℝ => A * t + B) := by fun_prop
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto (1 : ℝ))

end

end SGPT.Foundations.Analysis.FirstPass
