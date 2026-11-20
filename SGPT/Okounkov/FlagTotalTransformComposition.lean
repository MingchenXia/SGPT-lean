import SGPT.Okounkov.FlagLiftingComposition
import SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Actual coherent ideal pullback functoriality identifies the whole
effective Cartier objects, including all exceptional supported coefficients. -/
theorem effectiveDivisor_totalTransform_comp {n : ℕ}
    {F W V : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hp : IsFlagLifting W V p)
    (D : EffectiveDivisor n F.carrier) :
    GermIdealTotalTransform.EffectiveDivisor.totalTransform
        (hπ.comp hp).1.1 (hπ.comp hp).interior_exceptional_eq_empty D =
      GermIdealTotalTransform.EffectiveDivisor.totalTransform
        hp.1.1 hp.interior_exceptional_eq_empty
        (GermIdealTotalTransform.EffectiveDivisor.totalTransform
          hπ.1.1 hπ.interior_exceptional_eq_empty D) := by
  have hI := GermIdealTotalTransform.pullback_comp hπ.1.1 hp.1.1
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
  generalize hcomp : GermIdealTotalTransform.EffectiveDivisor.totalTransform
      (hπ.comp hp).1.1 (hπ.comp hp).interior_exceptional_eq_empty D = DC
  generalize hiter : GermIdealTotalTransform.EffectiveDivisor.totalTransform
      hp.1.1 hp.interior_exceptional_eq_empty
      (GermIdealTotalTransform.EffectiveDivisor.totalTransform
        hπ.1.1 hπ.interior_exceptional_eq_empty D) = DI
  have hDI : DC.ideal = DI.ideal := by
    rw [← hcomp, ← hiter]
    exact hI
  cases DC
  cases DI
  cases hDI
  rfl

end SGPT.Okounkov
