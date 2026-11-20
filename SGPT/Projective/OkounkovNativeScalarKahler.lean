import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Okounkov.TranscendentalLiftingExtension

/-! Actual compact native form domination produces left scalar Kähler-current neighborhoods.
Blueprint: okounkov-native-scalar-kahler.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.NativeScalarKahler
open Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

omit [CompactSpace M] in
private theorem thetaPsh_of_semipositive_difference {θ η : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hsemi : (η-θ).val.IsSemipositive) :
    IsThetaPshPotential η.val φ := by
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hsemi
  rwa [add_sub_cancel] at h

/-- Genuine scalar positivity around one, supplied by actual current and actual compact form domination. -/
theorem exists_left_scalar_kahler_neighborhood {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ r₀ : ℝ, 0<r₀ ∧ r₀<1 ∧
      IsThetaPshPotential θ.val (fun x => (r₀:EReal)*φ x) ∧
      ∀ r : ℝ, r₀<r → r≤1 → IsKahlerCurrentPotential θ (fun x => (r:EReal)*φ x) := by
  obtain ⟨κ,hκ⟩ := hφ
  obtain ⟨A,hA,hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ θ
  let r₀ : ℝ := A/(A+1)
  have hA1 : 0<A+1 := by linarith
  have hr₀ : 0<r₀ := div_pos hA hA1
  have hr₁ : r₀<1 := (div_lt_one hA1).mpr (by linarith)
  have hAr : (1-r₀)*A=r₀ := by
    dsimp only [r₀]
    field_simp
    ring
  have hbase : IsThetaPshPotential θ.val (fun x => (r₀:EReal)*φ x) := by
    apply thetaPsh_of_semipositive_difference (isThetaPshPotential_nonneg_smul hκ hr₀.le)
    have he : θ-r₀•(θ-κ.form)=(1-r₀)•(θ+A•κ.form) := by
      calc
        _ = (1-r₀)•θ+r₀•κ.form := by module
        _ = _ := by rw [smul_add,smul_smul,hAr]
    rw [he]
    exact KahlerDomination.isSemipositive_smul hdom (by linarith)
  refine ⟨r₀,hr₀,hr₁,hbase,?_⟩
  intro r hr hr1
  let b : ℝ := r-A*(1-r)
  have hb : 0<b := by
    have h : A<r*(A+1) := (div_lt_iff₀ hA1).mp hr
    dsimp only [b]
    nlinarith
  let κr := kahlerSmul κ hb
  refine ⟨κr,?_⟩
  apply thetaPsh_of_semipositive_difference
    (isThetaPshPotential_nonneg_smul hκ (hr₀.trans hr).le)
  have he : θ-κr.form-r•(θ-κ.form)=(1-r)•(θ+A•κ.form) := by
    dsimp only [κr,kahlerSmul,b]
    module
  rw [he]
  exact KahlerDomination.isSemipositive_smul hdom (by linarith)

end SGPT.Okounkov.NativeScalarKahler
