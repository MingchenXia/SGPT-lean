import SGPT.Unibranch.HironakaG10NativePointCentreSaturation
import SGPT.Unibranch.HironakaG10AdaptedStalkIdeal
import SGPT.Unibranch.HironakaG10NativeStalkSaturationTransport
import SGPT.Unibranch.HironakaG10ActualExceptionalStalkPivot

/-! The actual whole pullback stalk ideal at a genuine smooth-manifold point
blowup is saturated in the very same internally produced point chart. Arbitrary
nonreduced coherent original ideals are allowed. This does not identify the
result with an independently defined geometric strict transform or with an
arbitrary singular native ringed-space blowup. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
open Set Filter
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.HironakaG10ActualPointCentreExceptionalSaturation
noncomputable section
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences HolGerm BlowupFlatCoordinates
  BlowupExceptionalDivisor HironakaActualPointBlowupCoordinates
  HironakaActualHistoricalMovingCentreChart
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetMonomialSpan
  HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Unibranch.HironakaG10NativePointCentreSaturation
  SGPT.Unibranch.HironakaG10AdaptedStalkIdeal
  SGPT.Unibranch.HironakaG10NativeStalkSaturationTransport
  SGPT.Unibranch.HironakaG10ActualExceptionalStalkPivot

variable {n : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (0+n)) X] [IsComplexManifold (0+n) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (0+n)) Y] [IsComplexManifold (0+n) Y]

/-- The genuine point-blowup charts, actual pullback stalk ideal, full native
pivot saturation and quotient regularity are produced together. -/
theorem exists_actual_point_centre_exceptional_stalk_saturation
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
      (∀ {x : X}, x ∈ (chartAt (ComplexModel (0+n)) (π y)).source →
        chartAt (ComplexModel (0+n)) (π y) x ∈ Φ.source →
        (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel (0+n)) (π y) x) ∈
          complexCoordinatePlane (0+n) 0)) ∧
      (∀ z : Y, z ∈ (chartAt (ComplexModel (0+n)) y).source →
        chartAt (ComplexModel (0+n)) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel (0+n)) (π y) (π z)) =
          actualAnalyticBlowupMap (actualTangentCentreVariables 0 n) (j.natAdd 0) b
            (Θ.toFun (chartAt (ComplexModel (0+n)) y z))) ∧
      let E := adaptedStalkEquiv y Θ hΘ0
      let t := E.symm (coordinateGerm (j.natAdd 0))
      let Ip := actualWholeSheafStalkIdeal (GermIdeal.pullback (m := 0+n) π I) y
      let T := adaptedIdeal (GermIdeal.pullback (m := 0+n) π I) y Θ hΘ0
      let J₀ := adaptedIdeal I (π y) Φ hΦ0
      let N := actualAnalyticNormalizedMemberIdeal J₀ (actualTangentCentreVariables 0 n) (j.natAdd 0) b
      let J := N.comap E.toRingHom
      E t = coordinateGerm (j.natAdd 0) ∧
      actualWholeSheafStalkIdeal (exceptionalDivisor hπ).ideal y = Ideal.span {t} ∧
      Ideal.map E.toRingHom Ip = T ∧
      Ideal.map E.toRingHom J = N ∧
      (∀ v, v ∈ J ↔ ∃ q : ℕ, t^q * v ∈ Ip) ∧
      (∀ v, t*v ∈ J ↔ v ∈ J) ∧
      IsRegular (Ideal.Quotient.mk J t) ∧
      (∃ D : ℕ, T.colon {coordinateGerm (j.natAdd 0)^D} = N) := by
  obtain ⟨Φ,j₀,b,Θ,hΦsrc,hΦ0,hFlat,hΘsrc,hΘ0,hb,hSquare⟩ :=
    exists_actual_point_blowup_coordinates_with_flattening hπ y hCy
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
  have hFlat' : ∀ {x : X}, x ∈ (chartAt (ComplexModel (0+n)) (π y)).source →
      chartAt (ComplexModel (0+n)) (π y) x ∈ Φ.source →
      (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel (0+n)) (π y) x) ∈
        coordinateSubsetPlane (actualTangentCentreVariables 0 n)) := by
    intro x hx hxΦ
    simpa [hA, complexCoordinatePlane, coordinateSubsetPlane] using hFlat hx hxΦ
  have hExceptional := actual_exceptional_stalk_ideal_eq_span_transported_pivot
    hπ y (actualTangentCentreVariables 0 n) (j.natAdd 0) (by simp [hA]) b
    Φ hFlat' Θ hΘsrc hΘ0 hSquare'
  have hSat := native_point_normalized_iff_pullback_saturation I hI π hπ.contMDiff y j b
    Φ hΦsrc hΦ0 Θ hΘsrc hΘ0 hSquare'
  obtain ⟨hwhole,_hpivot,hcolon,_hregular⟩ := hSat
  let E := adaptedStalkEquiv y Θ hΘ0
  let t := E.symm (coordinateGerm (j.natAdd 0))
  let Ip := actualWholeSheafStalkIdeal (GermIdeal.pullback (m := 0+n) π I) y
  let T := adaptedIdeal (GermIdeal.pullback (m := 0+n) π I) y Θ hΘ0
  let J₀ := adaptedIdeal I (π y) Φ hΦ0
  let N := actualAnalyticNormalizedMemberIdeal J₀ (actualTangentCentreVariables 0 n) (j.natAdd 0) b
  have hmap : Ideal.map E.toRingHom Ip = T :=
    map_actualWholeSheafStalkIdeal_adapted (GermIdeal.pullback (m := 0+n) π I) y Θ hΘsrc hΘ0
  have hN : ∀ g, g ∈ N ↔ ∃ q : ℕ, (E t)^q*g ∈ T := by
    simpa only [t, RingEquiv.apply_symm_apply] using hwhole
  have htransport := actual_structure_stalk_saturation_quotient_regular y E Ip T N t hmap hN
  exact ⟨Φ,j,b,Θ,hΦ0,hΘ0,hΦsrc,hΘsrc,(by simpa only [hj] using hb),hFlat,hSquare',
    E.apply_symm_apply _, hExceptional.2, hmap,htransport.1,htransport.2.1,
    htransport.2.2.1,htransport.2.2.2,hcolon⟩
end
end SGPT.Unibranch.HironakaG10ActualPointCentreExceptionalSaturation
