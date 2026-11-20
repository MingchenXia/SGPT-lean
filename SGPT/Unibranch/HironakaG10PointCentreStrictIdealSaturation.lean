import SGPT.Foundations.Analysis.Pending.HironakaActualPointNormalizedSaturation
import SGPT.Foundations.Analysis.Pending.HironakaG10ChowArtinReesCentre
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set
namespace SGPT.Unibranch.HironakaG10PointCentreStrictIdealSaturation
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HolGerm HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualPointNormalizedSaturation HironakaActualCoefficientPresentationCentrePower
  HironakaHolomorphicJetMonomialSpan
  HironakaG10ChowArtinReesCentre
noncomputable section

/-- For the actual analytic coordinate polynomial map, strictIdeal is the
entire normalized-member ideal, including nonreduced original ideals. -/
theorem analytic_strictIdeal_eq_normalized
    {n : ℕ} (J : Ideal (HolGerm (ComplexModel n)))
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    strictIdeal (actualAnalyticBlowupPullback A e b).toRingHom J
      (actualAnalyticCoordinateIdeal A) (coordinateGerm e) =
      actualAnalyticNormalizedMemberIdeal J A e b := by
  unfold strictIdeal actualAnalyticNormalizedMemberIdeal
  congr 1
  ext h
  constructor
  · rintro ⟨q,g,hg,heq⟩
    exact ⟨q,g,hg.1,hg.2,heq.symm⟩
  · rintro ⟨q,g,hg,hpow,heq⟩
    exact ⟨q,g,⟨hg,hpow⟩,heq.symm⟩

/-- For an arbitrary (possibly nonreduced) original ideal at a smooth point,
the actual point-centre strict ideal is the whole pivot saturation. -/
theorem point_centre_strictIdeal_pivot_saturated
    {n : ℕ} (J : Ideal (HolGerm (ComplexModel (0+n))))
    (j : Fin n) (b : Fin (0+n) → ℂ) :
    let A := actualTangentCentreVariables 0 n
    let e := j.natAdd 0
    let N := strictIdeal (actualAnalyticBlowupPullback A e b).toRingHom J
      (actualAnalyticCoordinateIdeal A) (coordinateGerm e)
    let T := Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom J
    (∀ g, g ∈ N ↔ ∃ q : ℕ, (coordinateGerm e)^q * g ∈ T) ∧
    (∀ g, coordinateGerm e * g ∈ N ↔ g ∈ N) := by
  dsimp only
  rw [analytic_strictIdeal_eq_normalized]
  have h := actual_point_normalized_member_iff_total_saturation J j b
  exact ⟨h.1,h.2.1⟩

/-- The transformed ideal retains the full ideal structure; its quotient pivot is regular. -/
theorem point_centre_strict_quotient_pivot_regular
    {n : ℕ} (J : Ideal (HolGerm (ComplexModel (0+n))))
    (j : Fin n) (b : Fin (0+n) → ℂ) :
    let A := actualTangentCentreVariables 0 n
    let e := j.natAdd 0
    let N := strictIdeal (actualAnalyticBlowupPullback A e b).toRingHom J
      (actualAnalyticCoordinateIdeal A) (coordinateGerm e)
    IsRegular (Ideal.Quotient.mk N (coordinateGerm e)) := by
  dsimp only
  let N := strictIdeal (actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b).toRingHom J
    (actualAnalyticCoordinateIdeal (actualTangentCentreVariables 0 n)) (coordinateGerm (j.natAdd 0))
  have hsat : ∀ g, coordinateGerm (j.natAdd 0) * g ∈ N → g ∈ N :=
    fun g hg => ((point_centre_strictIdeal_pivot_saturated J j b).2 g).mp hg
  change IsRegular (Ideal.Quotient.mk N (coordinateGerm (j.natAdd 0)))
  rw [isRegular_iff_eq_zero_of_mul]
  have h : ∀ x : HolGerm (ComplexModel (0+n)) ⧸ N,
      Ideal.Quotient.mk N (coordinateGerm (j.natAdd 0)) * x = 0 → x = 0 := by
    intro x hx
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hsat x hx
  exact ⟨h, fun x hx => h x (by rw [mul_comm]; exact hx)⟩
end
end SGPT.Unibranch.HironakaG10PointCentreStrictIdealSaturation
