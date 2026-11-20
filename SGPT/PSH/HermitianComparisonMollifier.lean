import SGPT.PSH.HermitianComparisonStrict

/-!
# Actual mollifiers supply the bounded one-factor regularization

The distinguished potentials are given only as locally bounded PSH
functions on an outer coordinate domain. The genuine decreasing radial
mollifier producer and one supported extension construct all smooth
approximations and uniform bounds needed by strict one-factor comparison.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonMollifier

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.PSH.HermitianComparisonOneFactor SGPT.PSH.HermitianComparisonCutoff
  SGPT.PSH.HermitianComparisonStrict
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- The native radial mollifier approximation admits globally smooth
representatives on a relatively compact inner domain, with the monotonicity,
pointwise limit and uniform bound all produced from local boundedness. -/
theorem exists_bounded_global_smooth_approximation (hUV : RelativelyCompactIn U V)
    {a : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn V a) :
    ∃ (f : ℕ → ComplexModel n → ℝ) (M : ℝ),
      (∀ j, ContDiff ℝ ∞ (f j)) ∧
      (∀ j, PlurisubharmonicOn (fun z => (f j z : EReal)) U) ∧
      (∀ z ∈ U, Antitone fun j => f j z) ∧
      (∀ z ∈ U, Tendsto (fun j => f j z) atTop (𝓝 (a z))) ∧
      ∀ j z, z ∈ U → |f j z| ≤ M := by
  obtain ⟨A, hAo, hKA, hAclV, hAc⟩ :=
    exists_open_between_and_isCompact_closure hUV.1 V.isOpen hUV.2
  let A' : Opens (ComplexModel n) := ⟨A, hAo⟩
  have hUA : (U : Set (ComplexModel n)) ⊆ A := subset_closure.trans hKA
  obtain ⟨f, hfs, hanti, hlim⟩ :=
    HolomorphicPullback.exists_decreasingMollifierApproximation ha
      (show RelativelyCompactIn A' V from ⟨hAc, hAclV⟩)
  obtain ⟨ρ, hρs, hρ1, hρA⟩ := exists_cutoff hUV.1 hAo hKA
  let g : ℕ → ComplexModel n → ℝ := fun j z => ρ z * f j z
  have hgs : ∀ j, ContDiff ℝ ∞ (g j) := fun j =>
    contDiff_mul_of_tsupport_subset hAo hρs hρA (hfs j).1
  have hgf : ∀ j z, z ∈ U → g j z = f j z := by
    intro j z hz
    dsimp [g]
    have hρz : ρ z = 1 := (hρ1 z (subset_closure hz)).eq_of_nhds
    rw [hρz, one_mul]
  have hgp : ∀ j, PlurisubharmonicOn (fun z => (g j z : EReal)) U := by
    intro j z hz
    obtain ⟨W, hWo, hzW, hW⟩ := (hfs j).2.1 z (hUA hz)
    refine ⟨W ∩ U, hWo.inter U.isOpen, ⟨hzW, hz⟩,
      (hW.mono inter_subset_left).congr ?_⟩
    intro y hy
    change (f j y : EReal) = (g j y : EReal)
    rw [hgf j y hy.2]
  obtain ⟨M₁, _hM₁, haM⟩ := ha.exists_compact_abs_bound hUV.1 hUV.2
  obtain ⟨M₂, hfM⟩ := hUV.1.exists_bound_of_continuousOn ((hfs 0).1.continuousOn.mono hKA)
  refine ⟨g, max M₁ M₂, hgs, hgp, ?_, ?_, ?_⟩
  · intro z hz i j hij
    change g j z ≤ g i z
    rw [hgf j z hz, hgf i z hz]
    exact hanti z (hUA hz) hij
  · intro z hz
    simpa only [hgf _ z hz] using hlim z (hUA hz)
  · intro j z hz
    rw [hgf j z hz]
    have hbelow : a z ≤ f j z :=
      (hanti z (hUA hz)).le_of_tendsto (hlim z (hUA hz)) j
    have habove : f j z ≤ f 0 z := hanti z (hUA hz) (Nat.zero_le j)
    have haB := haM z (subset_closure hz)
    have hfB : |f 0 z| ≤ M₂ := by
      simpa only [Real.norm_eq_abs] using hfM z (subset_closure hz)
    apply abs_le.mpr
    constructor
    · linarith [(abs_le.mp haB).1, le_max_left M₁ M₂]
    · linarith [(abs_le.mp hfB).2, le_max_right M₁ M₂]

/-- Bounded local one-factor comparison from the original distinguished PSH
potentials. The genuine radial mollifier constructs the approximations;
no regularizing sequences or weighted convergence certificates are inputs. -/
theorem strict_local_onefactor_of_locallyBoundedPsh {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (hS : IsPositive (mixedCurrent D))
    (hUV : RelativelyCompactIn U V)
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn V a)
    (hb : IsLocallyBoundedPshOn V b)
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z) (η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1) :
    weightedDifference D a b strictIndicator scalarUnit χ ≤
      localizedDerivativeWeight D χ η (fun z => max (b z - a z) 0) := by
  obtain ⟨f, A, hfs, hfp, hfanti, hflim, hfbound⟩ :=
    exists_bounded_global_smooth_approximation hUV ha
  obtain ⟨g, B, hgs, hgp, hganti, hglim, hgbound⟩ :=
    exists_bounded_global_smooth_approximation hUV hb
  have hUV' : U ≤ V := subset_closure.trans hUV.2
  exact strict_local_onefactor D hS χ hχ η hη f g a b hfs hgs hfp hgp
    (isLocallyBoundedPshOn_mono ha hUV') (isLocallyBoundedPshOn_mono hb hUV')
    hfanti hganti hflim hglim
    (fun j z hz => (hfbound j z hz).trans (le_max_left A B))
    (fun j z hz => (hgbound j z hz).trans (le_max_right A B))

end SGPT.PSH.HermitianComparisonMollifier
