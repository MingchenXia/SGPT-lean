import SGPT.Foundations.Analysis.Pending.HironakaActualNativeAdaptedPullbackSquare
import SGPT.Foundations.Analysis.Pending.HironakaActualPointNormalizedSaturation
import SGPT.Foundations.Analysis.Pending.HironakaActualPointBlowupCoordinates
import SGPT.Unibranch.HironakaG10PointCentreStrictIdealSaturation

/-! A supplied native point-centre blowup square transports the full, possibly
nonreduced, coherent ideal pullback into the actual point-chart saturation.
The second theorem constructs this square for a genuine manifold blowup at a
regular zero-dimensional centre. Neither statement identifies a geometric
strict transform on an arbitrary singular ringed space. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace SGPT.Unibranch.HironakaG10NativePointCentreSaturation
noncomputable section
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves HolGerm BlowupFlatCoordinates
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaActualNativeAdaptedPullbackSquare HironakaActualAnalyticBlowupTaylor
  HironakaActualAnalyticStrictGenerators HironakaActualPointNormalizedSaturation
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetMonomialSpan
  HironakaActualPointBlowupCoordinates FirstPass.BlowupSequences
  SGPT.Unibranch.HironakaG10PointCentreStrictIdealSaturation

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (0+n)) X] [IsComplexManifold (0+n) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (0+n)) Y] [IsComplexManifold (0+n) Y]

/-- Given the actual adapted point-chart square, the normalized member ideal
of the original coherent stalk is exactly the full pivot saturation of the
native pulled-back ideal in the same adapted target chart. -/
theorem native_point_normalized_iff_pullback_saturation
    (I : GermIdeal (0+n) X) (hI : I.IsCoherent) (π : Y → X)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (0+n)) 𝓘(ℂ, ComplexModel (0+n)) ∞ π)
    (y : Y) (j : Fin n) (b : Fin (0+n) → ℂ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (0+n)) (π y) (π y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel (0+n)) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (0+n)) (π y) (π y)) = 0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (0+n)) y y))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel (0+n)) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel (0+n)) y y) = 0)
    (hSquare : ∀ z : Y, z ∈ (chartAt (ComplexModel (0+n)) y).source →
      chartAt (ComplexModel (0+n)) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel (0+n)) (π y) (π z)) =
        actualAnalyticBlowupMap (actualTangentCentreVariables 0 n) (j.natAdd 0) b
          (Θ.toFun (chartAt (ComplexModel (0+n)) y z))) :
    let J := adaptedIdeal I (π y) Φ hΦ0
    let N := actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n)
      (j.natAdd 0) b
    let T := adaptedIdeal (GermIdeal.pullback (m := 0+n) π I) y Θ hΘ0
    (∀ g, g ∈ N ↔ ∃ q : ℕ, (coordinateGerm (j.natAdd 0)) ^ q * g ∈ T) ∧
    (∀ g, coordinateGerm (j.natAdd 0) * g ∈ N ↔ g ∈ N) ∧
    (∃ D : ℕ, T.colon {coordinateGerm (j.natAdd 0) ^ D} = N) ∧
    IsRegular (Ideal.Quotient.mk N (coordinateGerm (j.natAdd 0))) := by
  dsimp only
  rw [actual_native_adapted_pullback_square I hI π hπ y
    (actualTangentCentreVariables 0 n) (j.natAdd 0) b
    Φ hΦsrc hΦ0 Θ hΘsrc hΘ0 hSquare]
  have h := actual_point_normalized_member_iff_total_saturation
    (adaptedIdeal I (π y) Φ hΦ0) j b
  have hregular := point_centre_strict_quotient_pivot_regular (adaptedIdeal I (π y) Φ hΦ0) j b
  dsimp only at hregular
  rw [analytic_strictIdeal_eq_normalized] at hregular
  exact ⟨h.1, h.2.1, h.2.2, hregular⟩


/-- For a genuine manifold blowup at a regular zero-dimensional centre, the
point coordinates and the entire nonreduced saturation are produced internally.
This is a statement in a smooth manifold chart, not an identification with an
arbitrary singular ringed-space blowup. -/
theorem exists_native_point_centre_saturation
    (I : GermIdeal (0+n) X) (hI : I.IsCoherent) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong (0+n) C π) (y : Y)
    (hCy : RegularAtDim (n := 0+n) C (π y) 0) :
    ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (0+n)) (π y) (π y)))
      (j : Fin n) (b : Fin (0+n) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (0+n)) y y))
      (hΦ0 : Φ.toFun (chartAt (ComplexModel (0+n)) (π y) (π y)) = 0)
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (0+n)) y y) = 0),
      Φ.source ⊆ (chartAt (ComplexModel (0+n)) (π y)).target ∧
      Θ.source ⊆ (chartAt (ComplexModel (0+n)) y).target ∧ b (j.natAdd 0) = 0 ∧
      (∀ z : Y, z ∈ (chartAt (ComplexModel (0+n)) y).source →
        chartAt (ComplexModel (0+n)) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel (0+n)) (π y) (π z)) =
          actualAnalyticBlowupMap (actualTangentCentreVariables 0 n) (j.natAdd 0) b
            (Θ.toFun (chartAt (ComplexModel (0+n)) y z))) ∧
      let J := adaptedIdeal I (π y) Φ hΦ0
      let N := actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n)
        (j.natAdd 0) b
      let T := adaptedIdeal (GermIdeal.pullback (m := 0+n) π I) y Θ hΘ0
      (∀ g, g ∈ N ↔ ∃ q : ℕ, (coordinateGerm (j.natAdd 0)) ^ q * g ∈ T) ∧
      (∀ g, coordinateGerm (j.natAdd 0) * g ∈ N ↔ g ∈ N) ∧
      (∃ D : ℕ, T.colon {coordinateGerm (j.natAdd 0) ^ D} = N) ∧
      IsRegular (Ideal.Quotient.mk N (coordinateGerm (j.natAdd 0))) := by
  obtain ⟨Φ,j₀,b,Θ,hΦsrc,hΦ0,hΘsrc,hΘ0,hb,hSquare⟩ :=
    exists_actual_point_blowup_coordinates hπ y hCy
  let j : Fin n := Fin.cast (Nat.zero_add n) j₀
  have hA : actualTangentCentreVariables 0 n = univ := by
    ext i
    simp only [actualTangentCentreVariables,mem_range,mem_univ,iff_true]
    exact ⟨Fin.cast (Nat.zero_add n) i,Fin.ext (by simp)⟩
  have hj : j.natAdd 0 = j₀ := Fin.ext (by simp [j])
  have hSquare' : ∀ z : Y, z ∈ (chartAt (ComplexModel (0+n)) y).source →
      chartAt (ComplexModel (0+n)) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel (0+n)) (π y) (π z)) =
        actualAnalyticBlowupMap (actualTangentCentreVariables 0 n) (j.natAdd 0) b
          (Θ.toFun (chartAt (ComplexModel (0+n)) y z)) := by
    simpa only [hA,hj] using hSquare
  exact ⟨Φ,j,b,Θ,hΦ0,hΘ0,hΦsrc,hΘsrc,(by simpa only [hj] using hb),hSquare',
    native_point_normalized_iff_pullback_saturation I hI π hπ.contMDiff y j b
      Φ hΦsrc hΦ0 Θ hΘsrc hΘ0 hSquare'⟩

end
end SGPT.Unibranch.HironakaG10NativePointCentreSaturation
