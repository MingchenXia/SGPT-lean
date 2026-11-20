import SGPT.Foundations.Analysis.Pending.RestrictedVolumePushforwardFatou
import SGPT.Foundations.Analysis.Pending.ExceptionalMetric
import SGPT.Foundations.Analysis.Pending.PushforwardPotentialRegularization
import SGPT.Foundations.Analysis.Pending.StrictTransformLocus
import SGPT.Foundations.Analysis.Pending.ExceptionalImageAnalytic
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePushforwardMass

set_option autoImplicit false

/-!
# CT22 Lemma 4.3: the modification is discharged; only the regularization is named

`Pending.ExceptionalPushforwardMass.acTopMass_le_restrictedMassEnvelope_of_exceptionalCorrection`
states steps 2 and 3 of CT22's Lemma 4.3 — push `S = T' − ε₀Θ_E` forward across the centre,
regularize the pushforward, and compare masses.  This module proves that statement from ONE
named input, and that input mentions no modification at all.

What is proved here and in the three modules below it:

* **Step 2, the pushforward across the centre**
  (`Pending.ExceptionalPushforwardPotential.exists_thetaPshPotential_pushforward`): the
  potential `u` of the `ε₀`-admissible presentation upstairs is `ψ ∘ g + h_Z − ε₀ψ_E` off
  `Exc g` for a `(θ + ε₀ω)`-PSH `ψ` downstairs.  This is `T = g_*S ∈ α` with `T ≥ −ε₀ω`,
  in potentials.
* **Step 3's geometry, the identification of the densities**
  (`Pending.ExceptionalPushforwardDensity.patchDensity_eq_potentialPatchDensity_pushforward`):
  at a parameter off `Exc g` and off the pole set,
  `patchDensity q Q v' = potentialPatchDensity (θ + ε₀ω) ψ P v`.  The two exceptional
  corrections cancel EXACTLY: `ω̃ = g^*ω − Θ_E` and `ddᶜψ_E = −Θ_E` off the support, so
  there is no loss in `ε₀`.
* the smooth germ the `ddᶜ` chain rule needs
  (`Pending.ExceptionalPushforwardSmooth.eventually_contDiffAt_chartFunction_of_comp`);
* `¬ W ⊆ P(ψ)`, from irreducibility of the strict transform: `Exc g` and `P(q.potential)`
  are analytic, `W̃` lies in neither, hence not in their union, and the image of a point
  outside both is a point of `W` where `ψ` is finite;
* the Fatou comparison across the centre
  (`Pending.RestrictedVolumePushforwardFatou`), with exactly CT22's hypothesis
  `W ⊄ g(Exc g)`.

What is NOT proved is the analytic half of step 3, isolated as
`Pending.PushforwardPotentialRegularization.exists_regularization_of_thetaPshPotential`:
Demailly regularization of a `(θ + ε₀ω)`-PSH potential on a compact Kähler manifold, with
the density clause read only where the chart expression of `ψ` is smooth (which is where the
consumer asks for it, and the only place where `smoothDDC` carries information).

The `liminf` in the density clause is kept in its honest form.  `T` has no analytic
singularities, so the project's `acTopMass` is not defined for it, and no fixed Demailly
regularization dominates its absolutely continuous density pointwise; CT22 regularizes and
applies Fatou.  Per I-0460 the gluing makes the densities EVENTUALLY EQUAL on the smooth
locus, so the clause in fact holds with an eventually constant sequence.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardFatouReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
  FirstPass.AdmissibleCurrentFormPositivity

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **CT22 Lemma 4.3, steps 2 and 3, modulo the regularization of the pushed-down potential
alone.**  The statement is unchanged; it is now PROVED from the single named input
`Pending.PushforwardPotentialRegularization.exists_regularization_of_thetaPshPotential`,
which speaks only of a compact Kähler manifold and a quasi-plurisubharmonic potential on
it.

The modification-theoretic content is discharged: `S = T' − ε₀Θ_E` pushes forward to
`T = θ + ddᶜψ ∈ α` with `T + ε₀ω ≥ 0` (`Pending.ExceptionalPushforwardPotential`), and at
every parameter off `Exc g` and off the pole set of `T'` the upstairs parameter density
EQUALS the downstairs parameter density of `T + ε₀ω`
(`Pending.ExceptionalPushforwardDensity`) — with no loss in `ε₀`, because
`ω̃ = g^*ω − Θ_E` and `ddᶜψ_E = −Θ_E` off the support cancel exactly.  The pole clause is
`ψ(g z) ≠ −∞` at a good `z`, from the same identity. -/
theorem exists_pushforwardRegularization [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y)
    (E : MeteredEffectiveQDivisor n Z) (hE : E.support ⊆ exceptionalLocus n g)
    (omegaTilde : KahlerBackground n Z)
    (hcorr : omegaTilde.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omega.form - E.curvature)
    (ε₀ ε : PositiveError) (hε : 2 * (ε₀ : ℝ) ≤ (ε : ℝ))
    (q : AdmissibleRestrictedCurrentPresentation omegaTilde
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
      (Wt.withDim W.dim hdim) ε₀) :
    ∃ p : ℕ → AdmissibleRestrictedCurrentPresentation omega
        (RealBottChern.ofRepresentative θ) W ε,
      (∀ z ∈ (exceptionalLocus n g)ᶜ, z ∉ poleSet q.potential →
        ∀ m, g z ∉ poleSet (p m).potential) ∧
      (∀ (P : RegularPatch W) (Q : RegularPatch (Wt.withDim W.dim hdim))
        (v v' : ComplexModel W.dim), v ∈ P.parameterDomain → v' ∈ Q.parameterDomain →
        Q.toManifold v' ∉ exceptionalLocus n g → g (Q.toManifold v') = P.toManifold v →
        Q.toManifold v' ∉ poleSet q.potential →
        (∀ β : ClosedRealOneOneForm n Y,
          ((ClosedRealOneOneForm.pullback hg.contMDiff β).val.coeff
              (complexChartAt (n := n) Q.center)
              (Q.coordinateParametrization v')).compContinuousLinearMap
            (fderiv ℝ Q.coordinateParametrization v') =
          (β.val.coeff (complexChartAt (n := n) P.center)
              (P.coordinateParametrization v)).compContinuousLinearMap
            (fderiv ℝ P.coordinateParametrization v)) →
        (∀ u : Y → ℝ,
          (∀ᶠ y in 𝓝 (P.coordinateParametrization v),
            ContDiffAt ℝ ∞ (fun y => u ((complexChartAt (n := n) P.center).val.symm y)) y) →
          (smoothDDC (fun y => u (g ((complexChartAt (n := n) Q.center).val.symm y)))
              (Q.coordinateParametrization v')).compContinuousLinearMap
            (fderiv ℝ Q.coordinateParametrization v') =
          (smoothDDC (fun y => u ((complexChartAt (n := n) P.center).val.symm y))
              (P.coordinateParametrization v)).compContinuousLinearMap
            (fderiv ℝ P.coordinateParametrization v)) →
        ENNReal.ofReal (patchDensity q Q v') ≤
          liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop) := by
  classical
  -- STEP 2 (proved): push the exceptionally corrected current across the centre
  obtain ⟨psi, hpsi, hZ, hhZ, heqZ, hid⟩ :=
    ExceptionalPushforwardPotential.exists_thetaPshPotential_pushforward θ hg omega E hE
      omegaTilde hcorr q.representative q.represents q.potential q.potential_psh
  -- off `Exc g` and off the poles of `q`, the pushed-down potential is finite
  have hpsine : ∀ z, z ∉ exceptionalLocus n g → z ∉ poleSet q.potential → psi (g z) ≠ ⊥ := by
    intro z hzExc hzpole
    have hbot : q.potential z ≠ ⊥ := hzpole
    have htop : q.potential z ≠ ⊤ :=
      BlowupNonKahlerLocusEq.ThetaPlurisubharmonic.ne_top q.potential_psh.1 z
    rw [hid z hzExc, ← EReal.coe_toReal htop hbot, ← EReal.coe_sub, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  -- `ψ` is not identically `-∞` on `W`
  have hWpsi : ¬ W.carrier ⊆ poleSet psi := by
    have hExcAn : IsComplexAnalyticSubset (n := n) (exceptionalLocus n g) :=
      RestrictedVolumePushforwardMass.isComplexAnalyticSubset_exceptionalLocus hg
    have hPoleAn : IsComplexAnalyticSubset (n := n) (poleSet q.potential) :=
      StrictTransformLocus.isComplexAnalyticSubset_poleSet_of_smoothOffPole
        q.smoothAnalyticSingularities
    have hWtcarrier : (Wt.withDim W.dim hdim).carrier = strictTransform n g W.carrier := hWt
    -- the strict transform is not contained in the union of the two analytic sets
    have hnotsub : ¬ (Wt.withDim W.dim hdim).carrier ⊆
        poleSet q.potential ∪ exceptionalLocus n g := by
      intro hsub
      have hcov : (Wt.withDim W.dim hdim).carrier =
          ((Wt.withDim W.dim hdim).carrier ∩ poleSet q.potential) ∪
            ((Wt.withDim W.dim hdim).carrier ∩ exceptionalLocus n g) := by
        rw [← Set.inter_union_distrib_left]
        exact (Set.inter_eq_left.mpr hsub).symm
      rcases (Wt.withDim W.dim hdim).irreducible_carrier.2.2 _ _
        ((Wt.withDim W.dim hdim).analytic.inter hPoleAn)
        ((Wt.withDim W.dim hdim).analytic.inter hExcAn)
        Set.inter_subset_left Set.inter_subset_left hcov with hleft | hright
      · exact q.not_carrier_subset_poleSet (by rw [hleft]; exact Set.inter_subset_right)
      · refine StrictTransformLocus.not_strictTransform_subset_preimage hg W hW
          (ExceptionalImageAnalytic.isComplexAnalyticSubset_image_exceptionalLocus hg) hW ?_
        rw [← hWtcarrier, hright]
        exact fun x hx => Set.subset_preimage_image g _ hx.2
    obtain ⟨z, hzW, hznot⟩ := Set.not_subset.mp hnotsub
    have hzpole : z ∉ poleSet q.potential := fun h => hznot (Or.inl h)
    have hzExc : z ∉ exceptionalLocus n g := fun h => hznot (Or.inr h)
    -- its image lies on `W`
    have hgzW : g z ∈ W.carrier := by
      have hz' : z ∈ closure (g ⁻¹' W.carrier) := by
        rw [hWtcarrier] at hzW
        exact closure_mono (fun x hx => hx.1) hzW
      rwa [(W.isClosed_carrier.preimage hg.contMDiff.continuous).closure_eq] at hz'
    exact Set.not_subset.mpr ⟨g z, hgzW, hpsine z hzExc hzpole⟩
  -- STEP 3 (the one remaining analytic input): regularize `ψ` downstairs
  obtain ⟨p, hpole, hdens⟩ :=
    PushforwardPotentialRegularization.exists_regularization_of_thetaPshPotential θ hbig
      omega W hdim_pos ε₀ ε hε psi hpsi hWpsi
  refine ⟨p, fun z hzExc hzpole m => hpole (g z) (hpsine z hzExc hzpole) m, ?_⟩
  intro P Q v v' hv hv' hQexc hgQ hQpole hform hddc
  have hPpole : P.toManifold v ∉ poleSet psi := by
    rw [← hgQ]; exact hpsine _ hQexc hQpole
  have hζT : P.coordinateParametrization v ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hv)
  have hPsrc : P.toManifold v ∈ (complexChartAt (n := n) P.center).val.source :=
    (complexChartAt (n := n) P.center).val.map_target hζT
  have hζ'T : Q.coordinateParametrization v' ∈ (complexChartAt (n := n) Q.center).val.target :=
    Q.source_subset (Q.flattening.mapsTo_invFun hv')
  have hQsrc : Q.toManifold v' ∈ (complexChartAt (n := n) Q.center).val.source :=
    (complexChartAt (n := n) Q.center).val.map_target hζ'T
  have hsmooth := ExceptionalPushforwardDensity.eventually_contDiffAt_chartFunction_pushforward
    θ hg omega E hE omegaTilde hcorr (ε₀ : ℝ) q.representative hhZ heqZ
    (AdmissibleCurrentFormPositivity.SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
      q.smoothAnalyticSingularities)
    hid hQexc hQpole (complexChartAt (n := n) Q.center) hQsrc
    (complexChartAt (n := n) P.center) (by rw [hgQ]; exact hPsrc)
  rw [hgQ] at hsmooth
  have hPchart : (complexChartAt (n := n) P.center).val (P.toManifold v)
      = P.coordinateParametrization v :=
    (complexChartAt (n := n) P.center).val.right_inv hζT
  rw [hPchart] at hsmooth
  rw [ExceptionalPushforwardDensity.patchDensity_eq_potentialPatchDensity_pushforward θ hg
    omega E hE omegaTilde hcorr hdim q hhZ heqZ hid P Q hv hv' hQexc hQpole hgQ hform hddc]
  exact hdens P v hv hPpole hsmooth


/-- **CT22 Lemma 4.3, steps 2 and 3, modulo the regularization alone.**  The statement is
that of
`Pending.ExceptionalPushforwardMass.acTopMass_le_restrictedMassEnvelope_of_exceptionalCorrection`,
proved from `exists_pushforwardRegularization` together with the Fatou comparison across
the centre.  Every piece of geometry and of measure theory in the obligation — the
analyticity of the exceptional locus, injectivity of `g` off it, the strict transform off
it, the covering of the upstairs pieces, the null set of parameters over the centre, the
translation of parameters, Fatou on each piece — is discharged. -/
theorem acTopMass_le_restrictedMassEnvelope_of_exceptionalCorrection [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y)
    (E : MeteredEffectiveQDivisor n Z) (hE : E.support ⊆ exceptionalLocus n g)
    (omegaTilde : KahlerBackground n Z)
    (hcorr : omegaTilde.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omega.form - E.curvature)
    (ε₀ ε : PositiveError) (hε : 2 * (ε₀ : ℝ) ≤ (ε : ℝ))
    (q : AdmissibleRestrictedCurrentPresentation omegaTilde
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
      (Wt.withDim W.dim hdim) ε₀) :
    acTopMass q ≤
      restrictedMassEnvelope (acTopMassData omega) (RealBottChern.ofRepresentative θ) W ε := by
  obtain ⟨p, hpoles, hdens⟩ := exists_pushforwardRegularization θ hbig hg W hdim_pos hW Wt hWt
    hdim omega E hE omegaTilde hcorr ε₀ ε hε q
  refine le_trans
    (RestrictedVolumePushforwardFatou.acTopMass_le_liminf_of_patchDensity_liminf_le_of_isBlowupAlong
      hg W hW Wt hWt hdim p q hpoles hdens) ?_
  have hmem : ∀ m, acTopMass (p m) ≤
      restrictedMassEnvelope (acTopMassData omega)
        (RealBottChern.ofRepresentative θ) W ε := fun m =>
    le_iSup (fun p' : AdmissibleRestrictedCurrentPresentation omega
      (RealBottChern.ofRepresentative θ) W ε => acTopMass p') (p m)
  calc liminf (fun m => acTopMass (p m)) atTop
      ≤ liminf (fun _ : ℕ => restrictedMassEnvelope (acTopMassData omega)
          (RealBottChern.ofRepresentative θ) W ε) atTop :=
        liminf_le_liminf (Eventually.of_forall hmem)
    _ = _ := liminf_const _

end

end SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardFatouReduction
