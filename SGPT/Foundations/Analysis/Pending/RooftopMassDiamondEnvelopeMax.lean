import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondReduction
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness

set_option autoImplicit false

/-!
# The maximum half of Xia's Step 1 for the rooftop mass diamond

`RooftopMassDiamondReduction.EnvelopeLatticeMassReduction` packages two mass
identities from Step 1 of the proof of Xia's Theorem 3.1.3
(`xia-sgpt:page-0108`).  This module proves the first one, for every pair of
`theta`-PSH potentials and with no positivity assumption:

  `∫ θ^n_{P_θ[φ] ∨ P_θ[ψ]} = ∫ θ^n_{φ ∨ ψ}`
  (`diagonalPotentialMass_max_singularityEnvelope_eq`).

The source argument is followed exactly.  By (3.4),
`P_θ[φ] = sup*_j (φ + a_0 + j) ∧ V_θ` (`singularityEnvelope_eq_uscRegularization_iSup_truncated`),
and the upper-semicontinuous regularization commutes with a binary maximum
(`uscRegularization_max`), so `P_θ[φ] ∨ P_θ[ψ]` is the regularized limit of
the increasing sequence `w_j = ((φ + a_0 + j) ∧ V_θ) ∨ ((ψ + a_0 + j) ∧ V_θ)`.
Each `w_j` is at most `φ ∨ ψ + a_0 + j`, so Corollary 2.4.1 in the form
`IncreasingLimitMass.diagonalPotentialMass_le_iSup_of_monotone` and the
monotonicity theorem give `≤`; the reverse inequality is the monotonicity
theorem applied to `φ ⪯ P_θ[φ]`, `ψ ⪯ P_θ[ψ]`.

The second identity of `EnvelopeLatticeMassReduction` (rooftops; Xia's
Lemma 3.1.2) is not proved here.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open FirstPass FirstPass.PositiveClasses
open DiagonalMass

noncomputable section

/-- The upper-semicontinuous regularization commutes with a binary maximum. -/
theorem uscRegularization_max {X : Type*} [TopologicalSpace X] (f g : X → EReal) :
    uscRegularization (fun x => max (f x) (g x)) =
      fun x => max (uscRegularization f x) (uscRegularization g x) := by
  funext x
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    obtain ⟨hf, hg⟩ := max_lt_iff.mp hc
    obtain ⟨U₁, hU₁⟩ := iInf_lt_iff.mp hf
    obtain ⟨hU₁n, hU₁c⟩ := iInf_lt_iff.mp hU₁
    obtain ⟨U₂, hU₂⟩ := iInf_lt_iff.mp hg
    obtain ⟨hU₂n, hU₂c⟩ := iInf_lt_iff.mp hU₂
    refine (uscRegularization_le_localSup _ (inter_mem hU₁n hU₂n)).trans ?_
    refine iSup₂_le fun y hy => max_le ?_ ?_
    · exact (le_iSup₂_of_le (f := fun y (_ : y ∈ U₁) => f y) y hy.1 le_rfl).trans hU₁c.le
    · exact (le_iSup₂_of_le (f := fun y (_ : y ∈ U₂) => g y) y hy.2 le_rfl).trans hU₂c.le
  · exact max_le (uscRegularization_mono (fun y => le_max_left (f y) (g y)) x)
      (uscRegularization_mono (fun y => le_max_right (f y) (g y)) x)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- **Xia, Theorem 3.1.3, Step 1, the maximum identity (`xia-sgpt:page-0108`).**
On a compact Kähler manifold, replacing two `theta`-PSH potentials by their
`P`-envelopes does not change the mass of their maximum. -/
theorem diagonalPotentialMass_max_singularityEnvelope_eq
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hpsi : IsThetaPshPotential theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hmaxP : IsThetaPshPotential theta.val
      (fun x => max (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x))) :
    diagonalPotentialMass theta
        (fun x => max (singularityEnvelope theta.val phi x)
          (singularityEnvelope theta.val psi x)) hmaxP =
      diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax := by
  refine le_antisymm ?_ ?_
  · obtain ⟨C₁, hC₁⟩ := hphi.exists_normalized_sub_const
    obtain ⟨C₂, hC₂⟩ := hpsi.exists_normalized_sub_const
    set a₀ : ℝ := max (-C₁) (-C₂) with ha₀
    have hlev₁ : ∀ j : ℕ, -C₁ ≤ a₀ + j := fun j =>
      (le_max_left _ _).trans (le_add_of_nonneg_right j.cast_nonneg)
    have hlev₂ : ∀ j : ℕ, -C₂ ≤ a₀ + j := fun j =>
      (le_max_right _ _).trans (le_add_of_nonneg_right j.cast_nonneg)
    have hu : ∀ j : ℕ, IsThetaPshPotential theta.val
        (truncatedSingularityEnvelope theta.val phi (a₀ + j)) := fun j =>
      truncatedSingularityEnvelope_isThetaPshPotential hphi.1.hasSmoothLocalPotentials
        ⟨_, sub_const_mem_truncatedSingularityCompetitors hC₁ (hlev₁ j)⟩
    have hv : ∀ j : ℕ, IsThetaPshPotential theta.val
        (truncatedSingularityEnvelope theta.val psi (a₀ + j)) := fun j =>
      truncatedSingularityEnvelope_isThetaPshPotential hpsi.1.hasSmoothLocalPotentials
        ⟨_, sub_const_mem_truncatedSingularityCompetitors hC₂ (hlev₂ j)⟩
    set w : ℕ → M → EReal := fun j x =>
      max (truncatedSingularityEnvelope theta.val phi (a₀ + j) x)
        (truncatedSingularityEnvelope theta.val psi (a₀ + j) x) with hwdef
    have hw : ∀ j, IsThetaPshPotential theta.val (w j) := fun j =>
      IsThetaPshPotential.max (hu j) (hv j)
    have hwmono : Monotone w := by
      intro i j hij x
      have hij' : a₀ + (i : ℝ) ≤ a₀ + j := by
        have : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
      exact max_le_max (truncatedSingularityEnvelope_mono _ _ hij' x)
        (truncatedSingularityEnvelope_mono _ _ hij' x)
    have hsup : (⨆ j, w j) = fun x =>
        max ((⨆ j : ℕ, truncatedSingularityEnvelope theta.val phi (a₀ + j)) x)
          ((⨆ j : ℕ, truncatedSingularityEnvelope theta.val psi (a₀ + j)) x) := by
      funext x
      simp only [hwdef, iSup_apply]
      exact iSup_sup_eq
    have heq : (fun x => max (singularityEnvelope theta.val phi x)
        (singularityEnvelope theta.val psi x)) = uscRegularization (⨆ j, w j) := by
      rw [hsup, uscRegularization_max,
        ← singularityEnvelope_eq_uscRegularization_iSup_truncated theta.val phi a₀,
        ← singularityEnvelope_eq_uscRegularization_iSup_truncated theta.val psi a₀]
    have hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, w j)) := heq ▸ hmaxP
    calc diagonalPotentialMass theta
          (fun x => max (singularityEnvelope theta.val phi x)
            (singularityEnvelope theta.val psi x)) hmaxP
        = diagonalPotentialMass theta (uscRegularization (⨆ j, w j)) hU :=
          diagonalPotentialMass_congr heq hmaxP hU
      _ ≤ ⨆ j, diagonalPotentialMass theta (w j) (hw j) :=
          IncreasingLimitMass.diagonalPotentialMass_le_iSup_of_monotone w hw hwmono hU
      _ ≤ diagonalPotentialMass theta (fun x => max (phi x) (psi x)) hmax := by
          refine iSup_le fun j => diagonalPotentialMass_mono_of_kahler omega (hw j) hmax
            ⟨a₀ + j, fun x _ => max_le ?_ ?_⟩
          · exact (truncatedSingularityEnvelope_le_add hphi.1.quasiPlurisubharmonic
              theta.val (a₀ + j) x).trans (add_le_add (le_max_left _ _) le_rfl)
          · exact (truncatedSingularityEnvelope_le_add hpsi.1.quasiPlurisubharmonic
              theta.val (a₀ + j) x).trans (add_le_add (le_max_right _ _) le_rfl)
  · obtain ⟨D₁, hD₁⟩ := moreSingularOn_singularityEnvelope hphi
    obtain ⟨D₂, hD₂⟩ := moreSingularOn_singularityEnvelope hpsi
    refine diagonalPotentialMass_mono_of_kahler omega hmax hmaxP
      ⟨max D₁ D₂, fun x _ => max_le ?_ ?_⟩
    · exact (hD₁ x (mem_univ x)).trans (add_le_add (le_max_left _ _)
        (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
    · exact (hD₂ x (mem_univ x)).trans (add_le_add (le_max_right _ _)
        (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))

end

end SGPT.Foundations.Analysis.Pending
