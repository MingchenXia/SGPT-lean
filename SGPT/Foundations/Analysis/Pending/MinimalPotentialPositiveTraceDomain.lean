import SGPT.Foundations.Analysis.Pending.PositiveOrdinaryRestrictionTraceDomain
import SGPT.Foundations.Analysis.Pending.MinimalPotentialRestrictionPositiveSeed
import SGPT.Foundations.Analysis.Pending.IdealOrderGenericLelongZero

set_option autoImplicit false

/-! # Actual positive trace domain of every positive moving minimal potential -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialPositiveTraceDomain

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.IEnvelope DiagonalMass
  PositiveNormalizedTrace PositiveOrdinaryRestrictionTraceDomain

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Original generic zero and actual map geometry supply every ordinary
and full trace field of the positive moving minimum internally. -/
theorem hasPositiveTraceRepresentativeAlong_minimal_add_smul
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0)
    {e : ℝ} (he : 0 < e) :
    HasPositiveTraceRepresentativeAlong omega omegaV hι (θ + e • omega.form)
      (thetaPshSupremum (θ + e • omega.form).val) := by
  let : Nonempty M := Nonempty.map ι inferInstance
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hplus := PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
    omega θ hV he
  have hW := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
    (θ + e • omega.form) hplus
  have hVenlarge : IsThetaPshPotential (θ + e • omega.form).val (thetaPshSupremum θ.val) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hV
      (KahlerDomination.isSemipositive_smul omega.isSemipositive he.le)
  have hle : thetaPshSupremum θ.val ≤ thetaPshSupremum (θ + e • omega.form).val :=
    le_thetaPshSupremum hVenlarge (thetaPshSupremum_le_zero θ.val)
  have hI : IOrderOnManifold (n := n) (thetaPshSupremum θ.val)
      (thetaPshSupremum (θ + e • omega.form).val) :=
    iOrderOnManifold_of_le hW.1.quasiPlurisubharmonic hle
  have hgenericW := IdealOrderGenericLelongZero.generic_lelong_inf_eq_zero_of_iOrder
    hV.1 hI ι hgeneric
  obtain ⟨a, U, happ⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation
      omega (θ + e • omega.form) hW
  obtain ⟨hw, hwpos⟩ :=
    MinimalPotentialRestrictionPositiveSeed.exists_positive_ordinary_restriction_minimal_add_smul
      omega hι hpull θ hbig hgeneric he
  exact hasPositiveTraceRepresentativeAlong_of_positive_ordinary_restriction
    omega omegaV hι hpull happ (thetaPshSupremum_le_zero _) hgenericW hw hwpos

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialPositiveTraceDomain
