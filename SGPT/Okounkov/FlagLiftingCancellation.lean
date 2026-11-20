import SGPT.Okounkov.FlagCorrection
import SGPT.Okounkov.FlagLiftingStrictTransform
import SGPT.Okounkov.FlagCorrectionComposition
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination

set_option autoImplicit false

noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- The two original liftings manufacture every level containment for the
actual intervening holomorphic map. No lifting for that map is a premise. -/
theorem flagLifting_containment_of_comp :
    ∀ (n : ℕ) (F W V : OriginalFlagGeometry.{u} n)
      (π : W.carrier → F.carrier) (p : V.carrier → W.carrier)
      (_hπ : IsFlagLifting F W π) (_hq : IsFlagLifting F V (π ∘ p))
      (_hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ p)
      (i : Fin (n + 1)), MapsTo p (V.flag i) (W.flag i) := by
  intro n
  induction n with
  | zero =>
      intro F W V π p hπ hq hp i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      rw [W.smooth.1]
      exact mapsTo_univ _ _
  | succ m ih =>
      intro F W V π p hπ hq hp
      have h1 : MapsTo p (V.flag (1 : Fin (m + 2)))
          (W.flag (1 : Fin (m + 2))) := by
        have he : V.flag (1 : Fin (m + 2)) =
            strictTransform (m + 1) p (W.flag (1 : Fin (m + 2))) := by
          rw [hq.first_carrier_eq_strictTransform,
            StrictTransformComposition.strictTransform_comp hπ.1.1 hp,
            ← hπ.first_carrier_eq_strictTransform]
        have hclosed : IsClosed (p ⁻¹' W.flag (1 : Fin (m + 2))) :=
          W.firstDivisor.1.preimage hp.continuous
        have hsub : strictTransform (m + 1) p (W.flag (1 : Fin (m + 2))) ⊆
            p ⁻¹' W.flag (1 : Fin (m + 2)) :=
          closure_minimal sdiff_subset hclosed
        intro z hz
        exact hsub (he ▸ hz)
      let p1 : V.tail.carrier → W.tail.carrier :=
        flagComponentMap W V p (1 : Fin (m + 2)) h1
      have hp1 : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ p1 := by
        have h := contMDiff_flagComponentMap W V p hp (1 : Fin (m + 2)) h1
        simp only [Fin.val_one] at h
        exact h
      have he : hq.tailMap = hπ.tailMap ∘ p1 := by
        funext z
        apply Subtype.ext
        rfl
      have hq1 : IsFlagLifting F.tail V.tail (hπ.tailMap ∘ p1) := by
        rw [← he]
        exact hq.tailMap_isFlagLifting
      have ht := ih F.tail W.tail V.tail hπ.tailMap p1
        hπ.tailMap_isFlagLifting hq1 hp1
      intro i
      refine Fin.cases ?_ ?_ i
      · rw [W.smooth.1]
        exact mapsTo_univ _ _
      · intro j z hz
        have hz1 : z ∈ V.flag (1 : Fin (m + 2)) :=
          V.smooth.2.1 (show (1 : Fin (m + 2)) ≤ j.succ from
            Nat.succ_le_succ (Nat.zero_le (j : ℕ))) hz
        exact ht j (x := ⟨z, hz1⟩) hz

/-- Every original component is a genuine commuting holomorphic factor
between the two given modifications. The parent constructs its geometry. -/
theorem IsFlagLifting.of_comp {n : ℕ} {F W V : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} {p : V.carrier → W.carrier}
    (hπ : IsFlagLifting F W π) (hq : IsFlagLifting F V (π ∘ p))
    (hp : IsAnalyticModification (n := n) p) : IsFlagLifting W V p := by
  refine ⟨hp, ?_⟩
  intro i
  have hi := flagLifting_containment_of_comp n F W V π p hπ hq hp.1 i
  refine ⟨hi, ?_⟩
  obtain ⟨hπi, hmodπ⟩ := hπ.2 i
  obtain ⟨hqi, hmodq⟩ := hq.2 i
  let := F.componentCharts i
  let := F.componentComplex i
  let := W.componentCharts i
  let := W.componentComplex i
  let := V.componentCharts i
  let := V.componentComplex i
  have hhol := contMDiff_flagComponentMap W V p hp.1 i hi
  have hsquare : flagComponentMap F W π i hπi ∘ flagComponentMap W V p i hi =
      flagComponentMap F V (π ∘ p) i hqi := by
    funext z
    apply Subtype.ext
    rfl
  exact PrescribedBlowupDomination.isAnalyticModification_of_commuting_factor
    hmodπ hmodq hhol hsquare

/-- The original two lifting premises give the literal right-row matrix
product; the intermediate lifting is produced internally. -/
theorem flagLiftingCorrectionMatrix_of_comp {n : ℕ}
    (F W V : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (p : V.carrier → W.carrier)
    (hπ : IsFlagLifting F W π) (hq : IsFlagLifting F V (π ∘ p))
    (hp : IsAnalyticModification (n := n) p) :
    flagLiftingCorrectionMatrix n F V (π ∘ p) hq =
      flagLiftingCorrectionMatrix n F W π hπ *
        flagLiftingCorrectionMatrix n W V p (hπ.of_comp hq hp) :=
  flagLiftingCorrectionMatrix_comp n F W V π p hπ (hπ.of_comp hq hp)

/-- The printed correction composition has precisely the source premises
and the original first-π-then-p row-vector convention. -/
theorem flagLiftingCorrection_of_comp {n : ℕ}
    (F W V : OriginalFlagGeometry.{u} n)
    (π : W.carrier → F.carrier) (p : V.carrier → W.carrier)
    (hπ : IsFlagLifting F W π) (hq : IsFlagLifting F V (π ∘ p))
    (hp : IsAnalyticModification (n := n) p) :
    flagLiftingCorrection n F V (π ∘ p) hq =
      (flagLiftingCorrection n F W π hπ).trans
        (flagLiftingCorrection n W V p (hπ.of_comp hq hp)) :=
  flagLiftingCorrection_comp F W V π p hπ (hπ.of_comp hq hp)

end SGPT.Okounkov
