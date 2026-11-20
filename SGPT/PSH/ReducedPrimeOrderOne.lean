import SGPT.PSH.OriginalPrimeComponent
import SGPT.Foundations.Analysis.Pending.MemberPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending DivisorExponent IdealWeightPowers
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Actual original regularity internally supplies a flat-coordinate ideal
member with nonzero first derivative, forcing the SAME reduced ideal order one. -/
theorem geometricPrimeCarrier_order_one_at_regular (P : GeometricPrimeCarrier (m + 1) M)
    {x : M} (hx : RegularAtDim (n := m + 1) P.val x m) :
    divExp (m + 1) (geometricPrimeCarrierEffectiveDivisor P).ideal P.val x = 1 := by
  let D := geometricPrimeCarrierEffectiveDivisor P
  have hxP : x ∈ P.val := hx.2.1
  have hxD : x ∈ D.support := by rwa [geometricPrimeCarrierEffectiveDivisor_support]
  have hpos := cartierOrder_pos_of_mem_support D hxD
  rw [geometricPrimeCarrierEffectiveDivisor_support] at hpos
  obtain ⟨_hle, _hxP, Φ, _hsrc, _hcenter, hflat⟩ := hx
  let q := BlowupFlatCoordinates.flatCoord Φ (Fin.last m)
  have hqm : D.ideal.mem x q := by
    rw [geometricPrimeCarrierEffectiveDivisor_ideal]
    exact BlowupFlatCoordinates.flatCoord_mem_vanishingIdeal Φ hflat (by simp)
      (BlowupFlatCoordinates.mem_flatDomain_self Φ)
  obtain ⟨v, hv⟩ := MemberPullback.exists_chartDeriv_flatCoord_ne_zero Φ (Fin.last m)
    (BlowupFlatCoordinates.mem_flatDomain_self Φ)
  have hnot : ¬IsDivNear (m + 1) D.ideal P.val 2 x := by
    intro hdiv
    have hq2 := OrderTaylor.mem_idealPow_of_vanishesToOrderOn_univ
      ((hdiv.self_of_nhds hxP).2 q hqm)
    have hdz := OrderTaylor.iterChartDeriv_eq_zero_of_mem_idealPow
      (e := complexChartAt (n := m + 1) x) (mem_complexChartAt_source x) hq2 [v] (by simp)
    change DerivativeIdeal.chartDeriv (complexChartAt (n := m + 1) x) v q x = 0 at hdz
    exact hv hdz
  have hhol : ∀ y g, D.ideal.mem y g → HolomorphicAt (m + 1) g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsInvertible.holomorphicAt_mem D.isInvertible hg
  have hnotle : ¬2 ≤ divExp (m + 1) D.ideal P.val x :=
    fun hle => hnot ((isDivNear_iff_le_divExp hhol hxP
      (HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible x)).mpr hle)
  change divExp (m + 1) D.ideal P.val x = 1
  omega

/-- From the original prime ALONE, its genuine reduced Cartier global
coefficient on the SAME internally produced component is exactly one. -/
theorem geometricPrimeCarrierComponent_order_one (P : GeometricPrimeCarrier (m + 1) M) :
    regularComponentOrder (geometricPrimeCarrierEffectiveDivisor P)
      (geometricPrimeCarrierEffectiveDivisor P).support (geometricPrimeCarrierComponent P) = 1 := by
  obtain ⟨x, _hxP, hxreg⟩ := P.subvariety.exists_regular_point
  have hdim : P.subvariety.dim = m := by have h := P.subvariety_codimension; omega
  have hx : RegularAtDim (n := m + 1) P.val x m := by
    simpa only [P.subvariety_carrier, hdim] using hxreg
  have hxD : RegularAtDim (n := m + 1) (geometricPrimeCarrierEffectiveDivisor P).support x m := by
    rwa [geometricPrimeCarrierEffectiveDivisor_support]
  have hB : (geometricPrimeCarrierComponent P).val =
      closure (RegularLocusComponent.component (n := m + 1)
        (geometricPrimeCarrierEffectiveDivisor P).support x) := by
    change P.val = _
    rw [geometricPrimeCarrierEffectiveDivisor_support]
    apply StrictTransformSubvariety.eq_closure_component _ hx
    rw [← P.subvariety_carrier]
    exact P.subvariety.irreducible_carrier
  rw [regularComponentOrder_eq (geometricPrimeCarrierEffectiveDivisor P)
    (geometricPrimeCarrierEffectiveDivisor P).support (geometricPrimeCarrierComponent P) hxD hB,
    geometricPrimeCarrierEffectiveDivisor_support]
  exact geometricPrimeCarrier_order_one_at_regular P hx

end SGPT.PSH
