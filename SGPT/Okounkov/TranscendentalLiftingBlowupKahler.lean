import SGPT.Okounkov.TranscendentalLiftingExtension
import SGPT.Foundations.Analysis.Pending.ResidualNef
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# Kähler currents on blow-up sequences

Source: blueprint node `tok:ext-blowup-kahler` (chapter `claude-okounkov-transcendental`), i.e.
Demailly--Păun, *Numerical characterization of the Kähler cone*, proof of Theorem 3.5, as used
in DRWNXZ Proposition 4.4; and the Kähler half of the book's `lma:logsingrem`.

* `exists_exceptional_kahler_perturbation` (`tok:ext-blowup-kahler`): for a finite sequence of
  blow-ups with smooth centres `p : Z' → Z` of a compact Kähler manifold `(Z, ω)` there is an
  effective `ℚ`-divisor `E` supported in the exceptional locus, with a smooth metric of curvature
  `η = Θ_E ∈ {E}`, such that for every Kähler current `T = θ + dd^c φ` on `Z` there is `ε₀ > 0`
  with `p^*T - ε η` a Kähler current for `0 < ε ≤ ε₀`, i.e. `φ ∘ p` is the potential of a Kähler
  current in the class `{p^*θ - ε η}`. The divisor is TN's exceptional metric
  (`ExceptionalMetricProof.exists_exceptionalMetric`, built inductively from the Blanchard forms
  `q^*β + ε Θ_U` of the single blow-ups, with `Θ_U` identified with `-q Θ_{div U}`): `p^*ω - η`
  is Kähler. The class of the Blanchard form is thus represented by a metered exceptional
  divisor (`ExceptionalMetricProof.ofWeightFactorization`: weight `q log U`, curvature
  `-q dd^c log U`).
* `exists_kahlerForm_of_logSingularities` (book `lma:logsingrem`, Kähler half): if `θ + dd^c φ` is
  a Kähler current and `φ = ψ_D + O(1)` has log singularities along a metered effective
  `ℚ`-divisor `D`, then `{θ} - {D}` contains a Kähler form `θ - Θ_D + dd^c h`. This is TN's
  `ResidualNef.exists_chartSmooth_isKahler_sub_curvature` (removable singularities across
  `Supp D` and Demailly's smoothing of a bounded potential, both proved in TN).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalLifting

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending

section Forms

variable {k n : ℕ} {V M : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Pullback of closed forms commutes with scalar multiplication. -/
theorem pullback_smul' {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) (t : ℝ)
    (a : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (t • a) = t • ClosedRealOneOneForm.pullback hf a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- Pullback of closed forms commutes with subtraction of a multiple. -/
theorem pullback_sub_smul' {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) (t : ℝ)
    (a b : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (a - t • b) =
      ClosedRealOneOneForm.pullback hf a - t • ClosedRealOneOneForm.pullback hf b := by
  rw [BoucksomResolutionStep.pullback_sub, pullback_smul']

end Forms

section BlowupKahler

variable {n : ℕ} {Z Z' : Type u}
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  [TopologicalSpace Z'] [ChartedSpace (ComplexModel n) Z'] [IsComplexManifold n Z']

/-- `κ ≥ δ ω` for two Kähler forms on a compact manifold. -/
theorem exists_pos_isSemipositive_sub_smul [CompactSpace Z] (κ omega : KahlerBackground n Z) :
    ∃ δ : ℝ, 0 < δ ∧ (κ.form - δ • omega.form).val.IsSemipositive := by
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-omega.form)
  refine ⟨A⁻¹, inv_pos.mpr hA, ?_⟩
  have h := KahlerDomination.isSemipositive_smul hsemi (inv_pos.mpr hA).le
  have heq : A⁻¹ • (-omega.form + A • κ.form) = κ.form - A⁻¹ • omega.form := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
    abel
  rwa [heq] at h

/-- **Kähler currents on blow-up sequences** (blueprint `tok:ext-blowup-kahler`; Demailly--Păun,
proof of Theorem 3.5). Let `p : Z' → Z` be a finite sequence of blow-ups with smooth centres of
a compact Kähler manifold `(Z, ω)`. There is an effective `ℚ`-divisor `E` on `Z'` supported in the
exceptional locus of `p`, with a smooth metric of curvature `η = Θ_E ∈ {E}`, such that `p^*ω - η`
is Kähler and for every Kähler current `θ + dd^c φ` on `Z` there is `ε₀ > 0` such that, for
`0 < ε ≤ ε₀`, `p^*θ - ε η + dd^c (φ ∘ p)` is a Kähler current, i.e. `p^*T - ε η` is a Kähler
current. -/
theorem exists_exceptional_kahler_perturbation [CompactSpace Z] (omega : KahlerBackground n Z)
    {p : Z' → Z} (hp : IsBlowupSequence n Z Z' p) :
    ∃ E : MeteredEffectiveQDivisor n Z', E.support ⊆ exceptionalLocus n p ∧
      (ClosedRealOneOneForm.pullback hp.contMDiff omega.form - E.curvature).val.IsKahler ∧
      ∀ (θ : ClosedRealOneOneForm n Z) (φ : Z → EReal), IsKahlerCurrentPotential θ φ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          IsKahlerCurrentPotential
            (ClosedRealOneOneForm.pullback hp.contMDiff θ - ε • E.curvature)
            (fun z => φ (p z)) := by
  obtain ⟨E, hEsupp, hK, -⟩ := ExceptionalMetricProof.exists_exceptionalMetric omega p hp
  refine ⟨E, hEsupp, hK, fun θ φ hφ => ?_⟩
  obtain ⟨κ, hκ⟩ := hφ
  obtain ⟨δ, hδ, hsemi⟩ := exists_pos_isSemipositive_sub_smul κ omega
  have hmod : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) p :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hp
  -- `φ` is `(θ - δ ω)`-psh, so `φ ∘ p` is `(p^*θ - δ p^*ω)`-psh
  have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive hκ hsemi
  have h1' : IsThetaPshPotential (θ - δ • omega.form).val φ := by
    have heq : θ - κ.form + (κ.form - δ • omega.form) = θ - δ • omega.form := by abel
    rwa [heq] at h1
  have h2 := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hmod _ h1'
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  set P := ClosedRealOneOneForm.pullback hp.contMDiff omega.form with hP
  have hPsemi : P.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hp.contMDiff omega.isSemipositive
  have h3 := LocalPotentials.isThetaPshPotential_add_of_semipositive h2
    (KahlerDomination.isSemipositive_smul hPsemi (sub_nonneg.mpr hεδ))
  refine ⟨kahlerSmul ⟨P - E.curvature, hK⟩ hε, ?_⟩
  have hform : ClosedRealOneOneForm.pullback hmod.1 (θ - δ • omega.form) + (δ - ε) • P =
      ClosedRealOneOneForm.pullback hp.contMDiff θ - ε • E.curvature -
        (kahlerSmul ⟨P - E.curvature, hK⟩ hε).form := by
    rw [kahlerSmul_form]
    change ClosedRealOneOneForm.pullback hp.contMDiff (θ - δ • omega.form) + (δ - ε) • P = _
    rw [pullback_sub_smul', ← hP, sub_smul, smul_sub]
    abel
  rwa [hform] at h3

/-- **The Kähler half of the book's `lma:logsingrem`**: if `θ + dd^c φ` is a Kähler current and
`φ = ψ_D + O(1)` has log singularities along the metered effective `ℚ`-divisor `D`, then the class
`{θ} - {D}` contains the Kähler form `θ - Θ_D + dd^c h` for a smooth `h` (the residual current
`θ + dd^c φ - [D]` is a Kähler current with bounded potentials). TN's
`ResidualNef.exists_chartSmooth_isKahler_sub_curvature`. -/
theorem exists_kahlerForm_of_logSingularities {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
    {θ : ClosedRealOneOneForm n M} {D : MeteredEffectiveQDivisor n M} {φ : M → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) (L : ResidualNefReduction.HasLogSingularitiesAlong D φ) :
    ∃ (h : M → ℝ) (hh : ChartSmooth (n := n) h),
      ((θ - D.curvature) + ManifoldTubePositivity.ddcClosedForm h hh).val.IsKahler := by
  have : Nonempty M := ConnectedSpace.toNonempty
  exact ResidualNef.exists_chartSmooth_isKahler_sub_curvature hφ L

end BlowupKahler

end SGPT.Okounkov.TranscendentalLifting
