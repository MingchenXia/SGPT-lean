import SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardSmooth
import SGPT.Foundations.Analysis.Pending.BlowupNonKahlerLocusEq
import SGPT.Foundations.Analysis.FirstPass.SmoothOffPole

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# CT22 Lemma 4.3: the upstairs parameter density IS the downstairs one

Upstairs the corrected current is `T' + ε₀ω̃`; downstairs the pushforward is
`T + ε₀ω = θ + ε₀ω + ddᶜψ`, with `ψ` the potential of
`Pending.ExceptionalPushforwardPotential`.  At a parameter whose point is off `Exc g` and
off the pole set, the two coordinate two-forms correspond under `g`:

    `(rep + ε₀ω̃)|_{φ_Q} + ddᶜ u = g^*(θ + ε₀ω)|_{φ_Q} + ddᶜ (ψ ∘ g)`,

because `u = ψ ∘ g + h_Z - ε₀ψ_E` there and `ddᶜψ_E = -Θ_E` off the support
(`Pending.MeteredDivisorSmoothOffSupport`).  Composing with the differential of the patch
parametrization and using the two chain-rule identities of
`Pending.RegularPatchPushforward` turns this into an equality of parameter densities.

`potentialPatchDensity` is the parameter density of `a + ddᶜψ` for an arbitrary closed
real `(1,1)`-form `a` and an arbitrary extended-real potential `ψ`; `patchDensity` of a
presentation is the case `a = θ + εω`, `ψ = ` its potential, definitionally.
-/

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardDensity

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.BlowupSequences FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.HolomorphicMaps
  FirstPass.AdmissibleCurrentFormPositivity

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- The parameter density of `a + ddᶜψ` along a regular patch, for an arbitrary closed
real `(1,1)`-form and an arbitrary extended-real potential.  For an admissible
presentation `p` this is `patchDensity p` with `a = perturbedRepresentative p`. -/
def potentialPatchDensity {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (a : ClosedRealOneOneForm n M) (psi : M → EReal)
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V)
    (v : ComplexModel V.dim) : ℝ :=
  MongeAmpere.actualTopPowerDensity
    ((a.val.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization v)
        + smoothDDC (fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
            (P.coordinateParametrization v)).compContinuousLinearMap
      (fderiv ℝ P.coordinateParametrization v))

theorem patchDensity_eq_potentialPatchDensity {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (v : ComplexModel V.dim) :
    patchDensity p P v = potentialPatchDensity (perturbedRepresentative p) p.potential P v :=
  rfl

/-- **The coordinate two-form of the corrected current upstairs is the pullback of the one
downstairs**, at a chart point off `Exc g` and off the pole set of `u`, together with the
open neighbourhood on which the chart expression of `ψ ∘ g` is smooth. -/
theorem exists_open_pushforwardGerm
    (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (omega : KahlerBackground n Y)
    (E : MeteredEffectiveQDivisor n Z) (hE : E.support ⊆ exceptionalLocus n g)
    (omegaTilde : KahlerBackground n Z)
    (hcorr : omegaTilde.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omega.form - E.curvature)
    (ε₀ : ℝ) (rep : ClosedRealOneOneForm n Z)
    {hZ : Z → ℝ} (hhZ : ChartSmooth (n := n) hZ)
    (heqZ : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e z =
        rep.val.coeff e z + smoothDDC (fun y => hZ (e.val.symm y)) z)
    {u : Z → EReal} (husmooth : SmoothOffPoleSet (n := n) u)
    {psi : Y → EReal}
    (hid : ∀ z ∉ exceptionalLocus n g,
      psi (g z) = u z - (hZ z : EReal) + ((ε₀ * (E.weight z).toReal : ℝ) : EReal))
    (e : ComplexChart n Z) {ζ : ComplexModel n} (hζ : ζ ∈ e.val.target)
    (hzExc : e.val.symm ζ ∉ exceptionalLocus n g)
    (hzpole : e.val.symm ζ ∉ poleSet u) :
    ∃ S : Set (ComplexModel n), IsOpen S ∧ ζ ∈ S ∧ S ⊆ e.val.target ∧
      ContDiffOn ℝ ∞ (fun y => (psi (g (e.val.symm y))).toReal) S ∧
      ((rep + ε₀ • omegaTilde.form).val.coeff e ζ
          + smoothDDC (fun y => (u (e.val.symm y)).toReal) ζ
        = (ClosedRealOneOneForm.pullback hg.contMDiff (θ + ε₀ • omega.form)).val.coeff e ζ
          + smoothDDC (fun y => (psi (g (e.val.symm y))).toReal) ζ) := by
  classical
  -- the smooth germ of `u` off its poles
  obtain ⟨u₀, hu₀smooth, hu₀eq⟩ := husmooth e ζ hζ hzpole
  obtain ⟨S₁, hS₁sub, hS₁open, hS₁mem⟩ := mem_nhds_iff.mp (hu₀smooth.and hu₀eq)
  -- the smooth local potential of `-Θ_E` off the support
  have hzsupp : e.val.symm ζ ∉ E.support := fun hmem => hzExc (hE hmem)
  obtain ⟨S₂, hS₂mem, hS₂pot⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hzsupp
      (e := e) (e.val.map_target hζ)
  have hζsymm : e.val (e.val.symm ζ) = ζ := e.val.right_inv hζ
  rw [hζsymm] at hS₂mem
  -- the open set on which every germ is good
  have hExcopen : IsOpen ((exceptionalLocus n g)ᶜ) :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hg.contMDiff
  set W : Set (ComplexModel n) := (S₁ ∩ S₂) ∩
    (e.val.target ∩ e.val.symm ⁻¹' (exceptionalLocus n g)ᶜ) with hW
  have hWopen : IsOpen W :=
    (hS₁open.inter hS₂pot.1).inter (e.val.isOpen_inter_preimage_symm hExcopen)
  have hζW : ζ ∈ W := ⟨⟨hS₁mem, hS₂mem⟩, hζ, hzExc⟩
  have hWe : W ⊆ e.val.target := fun y hy => hy.2.1
  -- the three smooth germs on `W`
  have huC : ContDiffOn ℝ ∞ (fun y => (u (e.val.symm y)).toReal) W := by
    intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    refine ((hS₁sub hy.1.1).1).congr_of_eventuallyEq ?_
    filter_upwards [hS₁open.mem_nhds hy.1.1] with y' hy'
    rw [show u (e.val.symm y') = ((u₀ y' : ℝ) : EReal) from (hS₁sub hy').2]
    simp
  have hhC : ContDiffOn ℝ ∞ (fun y => hZ (e.val.symm y)) W :=
    ((hhZ e).mono (fun y hy => hy.2.1))
  have hwC : ContDiffOn ℝ ∞ (fun y => (E.weight (e.val.symm y)).toReal) W :=
    hS₂pot.2.2.1.mono (fun y hy => hy.1.2)
  have hwsC : ContDiffOn ℝ ∞ (fun y => ε₀ • (E.weight (e.val.symm y)).toReal) W :=
    hwC.const_smul _
  -- the pushed-down germ is the combination of the three
  have hAC : ContDiffOn ℝ ∞
      (fun y => (u (e.val.symm y)).toReal - hZ (e.val.symm y)
        + ε₀ • (E.weight (e.val.symm y)).toReal) W := (huC.sub hhC).add hwsC
  have hAeq : EqOn (fun y => (psi (g (e.val.symm y))).toReal)
      (fun y => (u (e.val.symm y)).toReal - hZ (e.val.symm y)
        + ε₀ • (E.weight (e.val.symm y)).toReal) W := by
    intro y hy
    show (psi (g (e.val.symm y))).toReal
      = (u (e.val.symm y)).toReal - hZ (e.val.symm y)
        + ε₀ • (E.weight (e.val.symm y)).toReal
    have hz' : e.val.symm y ∉ exceptionalLocus n g := hy.2.2
    have hune : u (e.val.symm y) = ((u₀ y : ℝ) : EReal) := (hS₁sub hy.1.1).2
    rw [hid _ hz', hune, ← EReal.coe_sub, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe,
      smul_eq_mul]
  -- `ddᶜ` of the combination
  have hddcA : smoothDDC (fun y => (u (e.val.symm y)).toReal - hZ (e.val.symm y)
        + ε₀ • (E.weight (e.val.symm y)).toReal) ζ
      = smoothDDC (fun y => (u (e.val.symm y)).toReal) ζ
        - smoothDDC (fun y => hZ (e.val.symm y)) ζ
        + ε₀ • smoothDDC (fun y => (E.weight (e.val.symm y)).toReal) ζ := by
    rw [smoothDDC_add hWopen (huC.sub hhC) hwsC hζW,
      smoothDDC_sub hWopen huC hhC hζW, smoothDDC_smul hWopen hwC ε₀ hζW]
  have hddcpsi : smoothDDC (fun y => (psi (g (e.val.symm y))).toReal) ζ
      = smoothDDC (fun y => (u (e.val.symm y)).toReal - hZ (e.val.symm y)
          + ε₀ • (E.weight (e.val.symm y)).toReal) ζ :=
    smoothDDC_congr (Filter.eventuallyEq_of_mem (hWopen.mem_nhds hζW) hAeq)
  have hweightddc : smoothDDC (fun y => (E.weight (e.val.symm y)).toReal) ζ
      = -(E.curvature.val.coeff e ζ) := by
    have := hS₂pot.2.2.2 hζW.1.2
    rwa [ClosedRealOneOneForm.coeff_neg] at this
  -- the geometric identities of the forms
  have hpull : (ClosedRealOneOneForm.pullback hg.contMDiff (θ + ε₀ • omega.form)).val.coeff e ζ
      = (ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e ζ
        + ε₀ • (ClosedRealOneOneForm.pullback hg.contMDiff omega.form).val.coeff e ζ := by
    have h1 := ExceptionalPushforwardPotential.pullback_add_geometricallyEq hg.contMDiff θ
      (ε₀ • omega.form) e hζ
    have h2 := BlowupPushforward.pullback_smul_geometricallyEq hg.contMDiff ε₀ omega.form e hζ
    rw [h1, ClosedRealOneOneForm.coeff_add, h2, ClosedRealOneOneForm.coeff_smul]
  refine ⟨W, hWopen, hζW, hWe, hAC.congr hAeq, ?_⟩
  rw [hddcpsi, hddcA, hweightddc, hpull, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, hcorr, BlowupBigPullback.coeff_sub,
    heqZ e ζ hζ]
  ext v
  simp [smul_sub]
  ring

/-- `compContinuousLinearMap` is additive in the form. -/
theorem compContinuousLinearMap_add {k : ℕ} (A B : MongeAmpere.CoordinateRealTwoForm n)
    (L : ComplexModel k →L[ℝ] ComplexModel n) :
    (A + B).compContinuousLinearMap L
      = A.compContinuousLinearMap L + B.compContinuousLinearMap L := by
  ext v; simp

/-- The chart expression of `ψ ∘ g` is smooth near the parameter point of a regular patch
whose point is off `Exc g` and off the pole set of `u`. -/
theorem eventually_contDiffAt_comp_pushforwardGerm
    (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (omega : KahlerBackground n Y)
    (E : MeteredEffectiveQDivisor n Z) (hE : E.support ⊆ exceptionalLocus n g)
    (omegaTilde : KahlerBackground n Z)
    (hcorr : omegaTilde.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omega.form - E.curvature)
    (ε₀ : ℝ) (rep : ClosedRealOneOneForm n Z)
    {hZ : Z → ℝ} (hhZ : ChartSmooth (n := n) hZ)
    (heqZ : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e z =
        rep.val.coeff e z + smoothDDC (fun y => hZ (e.val.symm y)) z)
    {u : Z → EReal} (husmooth : SmoothOffPoleSet (n := n) u)
    {psi : Y → EReal}
    (hid : ∀ z ∉ exceptionalLocus n g,
      psi (g z) = u z - (hZ z : EReal) + ((ε₀ * (E.weight z).toReal : ℝ) : EReal))
    (e : ComplexChart n Z) {ζ : ComplexModel n} (hζ : ζ ∈ e.val.target)
    (hzExc : e.val.symm ζ ∉ exceptionalLocus n g)
    (hzpole : e.val.symm ζ ∉ poleSet u) :
    ∀ᶠ y in 𝓝 ζ, ContDiffAt ℝ ∞ (fun y' => (psi (g (e.val.symm y'))).toReal) y := by
  obtain ⟨S, hSopen, hζS, -, hSC, -⟩ :=
    exists_open_pushforwardGerm θ hg omega E hE omegaTilde hcorr ε₀ rep hhZ heqZ husmooth hid
      e hζ hzExc hzpole
  filter_upwards [hSopen.mem_nhds hζS] with y hy
  exact (hSC y hy).contDiffAt (hSopen.mem_nhds hy)


/-- **The chart expression of the pushed-down potential is smooth at the image of a good
point.**  `eventually_contDiffAt_comp_pushforwardGerm` upstairs, transported by
`Pending.ExceptionalPushforwardSmooth`. -/
theorem eventually_contDiffAt_chartFunction_pushforward
    (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (omega : KahlerBackground n Y)
    (E : MeteredEffectiveQDivisor n Z) (hE : E.support ⊆ exceptionalLocus n g)
    (omegaTilde : KahlerBackground n Z)
    (hcorr : omegaTilde.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omega.form - E.curvature)
    (ε₀ : ℝ) (rep : ClosedRealOneOneForm n Z)
    {hZ : Z → ℝ} (hhZ : ChartSmooth (n := n) hZ)
    (heqZ : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e z =
        rep.val.coeff e z + smoothDDC (fun y => hZ (e.val.symm y)) z)
    {u : Z → EReal} (husmooth : SmoothOffPoleSet (n := n) u)
    {psi : Y → EReal}
    (hid : ∀ z ∉ exceptionalLocus n g,
      psi (g z) = u z - (hZ z : EReal) + ((ε₀ * (E.weight z).toReal : ℝ) : EReal))
    {z : Z} (hzExc : z ∉ exceptionalLocus n g) (hzpole : z ∉ poleSet u)
    (e : ComplexChart n Z) (hze : z ∈ e.val.source)
    (d : ComplexChart n Y) (hgz : g z ∈ d.val.source) :
    ∀ᶠ y in 𝓝 (d.val (g z)),
      ContDiffAt ℝ ∞ (fun y' => (psi (d.val.symm y')).toReal) y := by
  have hζ : e.val z ∈ e.val.target := e.val.map_source hze
  have hsymm : e.val.symm (e.val z) = z := e.val.left_inv hze
  have hgerm := eventually_contDiffAt_comp_pushforwardGerm θ hg omega E hE omegaTilde hcorr
    ε₀ rep hhZ heqZ husmooth hid e hζ (by rw [hsymm]; exact hzExc) (by rw [hsymm]; exact hzpole)
  exact ExceptionalPushforwardSmooth.eventually_contDiffAt_chartFunction_of_comp
    hg.contMDiff hzExc e hze hgerm d hgz

/-- **CT22 Lemma 4.3, step 3: the parameter density upstairs IS the parameter density of the
pushforward downstairs.**  At a parameter whose point is off `Exc g` and off the pole set,
for a pair of regular patches related by the chain-rule identities of
`Pending.RegularPatchPushforward`. -/
theorem patchDensity_eq_potentialPatchDensity_pushforward
    (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (omega : KahlerBackground n Y)
    (E : MeteredEffectiveQDivisor n Z) (hE : E.support ⊆ exceptionalLocus n g)
    (omegaTilde : KahlerBackground n Z)
    (hcorr : omegaTilde.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omega.form - E.curvature)
    {ε₀ : PositiveError}
    {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    (q : AdmissibleRestrictedCurrentPresentation omegaTilde
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
      (Wt.withDim W.dim hdim) ε₀)
    {psi : Y → EReal} {hZ : Z → ℝ} (hhZ : ChartSmooth (n := n) hZ)
    (heqZ : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e z =
        q.representative.val.coeff e z + smoothDDC (fun y => hZ (e.val.symm y)) z)
    (hid : ∀ z ∉ exceptionalLocus n g,
      psi (g z) = q.potential z - (hZ z : EReal)
        + (((ε₀ : ℝ) * (E.weight z).toReal : ℝ) : EReal))
    (P : RegularPatch W) (Q : RegularPatch (Wt.withDim W.dim hdim))
    {v v' : ComplexModel W.dim}
    (hv : v ∈ P.parameterDomain) (hv' : v' ∈ Q.parameterDomain)
    (hQexc : Q.toManifold v' ∉ exceptionalLocus n g)
    (hQpole : Q.toManifold v' ∉ poleSet q.potential)
    (hgQ : g (Q.toManifold v') = P.toManifold v)
    (hform : ∀ β : ClosedRealOneOneForm n Y,
      ((ClosedRealOneOneForm.pullback hg.contMDiff β).val.coeff
          (complexChartAt (n := n) Q.center)
          (Q.coordinateParametrization v')).compContinuousLinearMap
        (fderiv ℝ Q.coordinateParametrization v') =
      (β.val.coeff (complexChartAt (n := n) P.center)
          (P.coordinateParametrization v)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization v))
    (hddc : ∀ w : Y → ℝ,
      (∀ᶠ y in 𝓝 (P.coordinateParametrization v),
        ContDiffAt ℝ ∞ (fun y => w ((complexChartAt (n := n) P.center).val.symm y)) y) →
      (smoothDDC (fun y => w (g ((complexChartAt (n := n) Q.center).val.symm y)))
          (Q.coordinateParametrization v')).compContinuousLinearMap
        (fderiv ℝ Q.coordinateParametrization v') =
      (smoothDDC (fun y => w ((complexChartAt (n := n) P.center).val.symm y))
          (P.coordinateParametrization v)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization v)) :
    patchDensity q Q v' = potentialPatchDensity (θ + (ε₀ : ℝ) • omega.form) psi P v := by
  classical
  have hζ'T : Q.coordinateParametrization v' ∈ (complexChartAt (n := n) Q.center).val.target :=
    Q.source_subset (Q.flattening.mapsTo_invFun hv')
  have hζT : P.coordinateParametrization v ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hv)
  have hQsrc : Q.toManifold v' ∈ (complexChartAt (n := n) Q.center).val.source :=
    (complexChartAt (n := n) Q.center).val.map_target hζ'T
  have hQchart : (complexChartAt (n := n) Q.center).val (Q.toManifold v')
      = Q.coordinateParametrization v' :=
    (complexChartAt (n := n) Q.center).val.right_inv hζ'T
  have hPsrc : P.toManifold v ∈ (complexChartAt (n := n) P.center).val.source :=
    (complexChartAt (n := n) P.center).val.map_target hζT
  have hPchart : (complexChartAt (n := n) P.center).val (P.toManifold v)
      = P.coordinateParametrization v :=
    (complexChartAt (n := n) P.center).val.right_inv hζT
  -- the smooth germ of the pushed-down potential at the downstairs parameter point
  have hsmoothdown := eventually_contDiffAt_chartFunction_pushforward θ hg omega E hE
    omegaTilde hcorr (ε₀ : ℝ) q.representative hhZ heqZ
    (AdmissibleCurrentFormPositivity.SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
      q.smoothAnalyticSingularities)
    hid hQexc hQpole (complexChartAt (n := n) Q.center) hQsrc
    (complexChartAt (n := n) P.center) (by rw [hgQ]; exact hPsrc)
  rw [hgQ, hPchart] at hsmoothdown
  -- the coordinate form identity
  obtain ⟨-, -, -, -, -, hkey⟩ :=
    exists_open_pushforwardGerm θ hg omega E hE omegaTilde hcorr (ε₀ : ℝ) q.representative
      hhZ heqZ
      (AdmissibleCurrentFormPositivity.SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
        q.smoothAnalyticSingularities)
      hid (complexChartAt (n := n) Q.center) hζ'T hQexc hQpole
  have hcc : coordinateCurrentForm q (complexChartAt (n := n) Q.center)
      (Q.coordinateParametrization v')
      = (ClosedRealOneOneForm.pullback hg.contMDiff (θ + (ε₀ : ℝ) • omega.form)).val.coeff
          (complexChartAt (n := n) Q.center) (Q.coordinateParametrization v')
        + smoothDDC (fun y => (psi (g ((complexChartAt (n := n) Q.center).val.symm y))).toReal)
            (Q.coordinateParametrization v') := hkey
  have hcomp := congrArg
    (fun A : MongeAmpere.CoordinateRealTwoForm n => A.compContinuousLinearMap
      (fderiv ℝ Q.coordinateParametrization v')) hcc
  rw [compContinuousLinearMap_add, hform (θ + (ε₀ : ℝ) • omega.form),
    hddc (fun y => (psi y).toReal) hsmoothdown] at hcomp
  show MongeAmpere.actualTopPowerDensity
      ((coordinateCurrentForm q (complexChartAt (n := n) Q.center)
        (Q.coordinateParametrization v')).compContinuousLinearMap
        (fderiv ℝ Q.coordinateParametrization v'))
    = MongeAmpere.actualTopPowerDensity
      (((θ + (ε₀ : ℝ) • omega.form).val.coeff (complexChartAt (n := n) P.center)
          (P.coordinateParametrization v)
        + smoothDDC (fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
          (P.coordinateParametrization v)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization v))
  rw [compContinuousLinearMap_add]
  exact congrArg MongeAmpere.actualTopPowerDensity hcomp

end

end SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardDensity
