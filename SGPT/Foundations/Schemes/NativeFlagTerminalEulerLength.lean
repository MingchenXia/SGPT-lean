import SGPT.Foundations.Schemes.NativeFlagPowerEulerGlobal
import SGPT.Foundations.Schemes.ArtinianGlobalLineLengthSum
import SGPT.Foundations.Schemes.NativeFlagEulerDifferences

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped BigOperators
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The genuine geometric sum of the ACTUAL full local stalk-ring lengths.
Its finiteness is proved separately, without a Hilbert-coefficient definition. -/
def NativeClosedProjectiveStratum.artinianStalkLengthSum {N : ℕ}
    (T : NativeClosedProjectiveStratum N) [IsArtinianScheme T.val.left] : ℕ∞ :=
  letI : Fintype T.val.left := Fintype.ofFinite T.val.left
  ∑ x : T.val.left, Module.length (T.val.left.presheaf.stalk x) (T.val.left.presheaf.stalk x)

/-- The actual global-line comparison produces finiteness of the genuine
stalk-length sum, including empty and nonreduced projective strata. -/
theorem NativeClosedProjectiveStratum.artinianStalkLengthSum_ne_top {N : ℕ}
    (T : NativeClosedProjectiveStratum N) [IsArtinianScheme T.val.left] :
    T.artinianStalkLengthSum ≠ ⊤ := by
  have h := T.embedding.artinian_globalLine_finrank_eq_stalk_length_sum
    (((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1).tensorPower 0)
  change (_ : ℕ∞) = T.artinianStalkLengthSum at h
  rw [← h]
  exact ENat.natCast_ne_top _

/-- Actual projective vanishing and actual global/local length comparison
give the eventual chosen-cover Euler value without a supplied value. -/
theorem NativeClosedProjectiveStratum.artinian_powerEuler_eventually_eq_stalk_length_sum
    {N : ℕ} (T : NativeClosedProjectiveStratum N) [IsArtinianScheme T.val.left] :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      T.powerEuler m = (T.artinianStalkLengthSum.toNat : ℤ) := by
  obtain ⟨b, hb⟩ := T.powerEuler_eventually_eq_global_finrank
  refine ⟨b, fun m hm ↦ ?_⟩
  have h := T.embedding.artinian_globalLine_finrank_eq_stalk_length_sum
    (((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1).tensorPower m)
  change (Module.finrank ℂ (actualSchemeModuleBaseGlobalSections (T.powerSheaf m)
    (schemeGlobalConstants (T.val.hom ≫ polynomialProjStructureMap ℂ N))) : ℕ∞) =
      T.artinianStalkLengthSum at h
  rw [hb m hm, ← h]
  rfl

/-- The original Fano geometry produces the actual Artinian terminal Euler
value as its genuine finite local-ring length sum, including n=0. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_terminal_euler_length_sum
    {n : ℕ} (F : SmoothProjectiveFano n) :
    let := F.nativeRegularProjectiveFlag_terminal_isArtinian
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      (F.nativeRegularProjectiveFlag n).powerEuler m =
        ((F.nativeRegularProjectiveFlag n).artinianStalkLengthSum.toNat : ℤ) := by
  let := F.nativeRegularProjectiveFlag_terminal_isArtinian
  exact (F.nativeRegularProjectiveFlag n).artinian_powerEuler_eventually_eq_stalk_length_sum

/-- Genuine Euler iteration reaches that SAME terminal local-length sum;
the original index shift is retained rather than suppressed. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_fwdDiff_euler_length_sum
    {n : ℕ} (F : SmoothProjectiveFano n) :
    let := F.nativeRegularProjectiveFlag_terminal_isArtinian
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      ((fwdDiff (1 : ℕ))^[n] (F.nativeRegularProjectiveFlag 0).powerEuler) m =
        ((F.nativeRegularProjectiveFlag n).artinianStalkLengthSum.toNat : ℤ) := by
  let := F.nativeRegularProjectiveFlag_terminal_isArtinian
  obtain ⟨b, hb⟩ := F.nativeRegularProjectiveFlag_terminal_euler_length_sum
  refine ⟨b, fun m hm ↦ ?_⟩
  rw [F.nativeRegularProjectiveFlag_terminal_euler_difference]
  exact hb (m + n) (hm.trans (Nat.le_add_right m n))

end
end SGPT.Foundations.Schemes
