import SGPT.Foundations.Analysis.Pending.SubmanifoldPatchTransport
import SGPT.Foundations.Analysis.Pending.SubmanifoldMassCalculus
import SGPT.Foundations.Analysis.Pending.AdmissiblePresentationPullback

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restriction of an admissible presentation to the complex manifold `↥V`

Route F, `F-b` step P1 (plan §8 of `scratch/tn23-envelopes-qea-plan-0117.md`; blueprint
`pc:f-restricted-volume-le`).  Let `p` be an admissible presentation of a class along `V` at error
`ε` (representative `θ_p`, potential `u_p` with analytic singularities smooth off its poles,
`V ⊄ {u_p = -∞}`).  On the compact connected complex manifold `↥V` with the Kähler form `ω|_V`:

* `restrictPresentation p` — the presentation of the whole of `↥V` with representative `θ_p|_V`
  and potential `u_p|_V` (nondegenerate by the identity principle on the connected `↥V`;
  analytic singularities pull back, `hasManifoldAnalyticSingularitiesSmoothOffPole_comp`, the
  dimension-general form of `AdmissiblePresentationPullback`'s lemma);
* `patchDensity_targetPatch` — **the restricted density is the same in the two descriptions**: on
  the target patch of `SubmanifoldPatchTransport` (`targetPatch(w) = P(w + v₀)`),
  `patchDensity (p|_V) (targetPatch) w = patchDensity p P (w + v₀)` off the poles.  Chain rule for
  the pulled-back form (`SmoothRealForm.pullback_coeff`) and for `ddᶜ` of the potential, smooth off
  its poles, under the holomorphic inclusion (`HolomorphicDDC.smoothDDC_comp`).

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.SubmanifoldRestrictedPresentation

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume SubmanifoldChartedSpace SubmanifoldPatchTransport

/-! ### Analytic singularities pull back along holomorphic maps (any dimensions) -/

section Comp

variable {k n : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Analytic singularities in the bounded-remainder convention pull back along a holomorphic map** between
manifolds of possibly different dimensions (the proof of
`AdmissiblePresentationPullback.hasManifoldAnalyticSingularitiesSmoothOffPole_comp`, which is
stated for equal dimensions). -/
theorem hasManifoldAnalyticSingularitiesSmoothOffPole_comp {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) {v : Y → EReal}
    (hv : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) v) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := k) (fun z => v (g z)) := by
  intro e z hz
  set d := complexChartAt (n := n) (g (e.val.symm z))
  set F := HolomorphicMaps.coordinateMap g e d
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hg e d
  have hFc : ContDiffOn ℂ ∞ F (HolomorphicMaps.coordinateDomain g e d) :=
    HolomorphicMaps.coordinateMap_contDiffOn hg e d
  have hFz : ContinuousAt F z :=
    (HolomorphicMaps.coordinateMap_contDiffAt hg e d hzd).continuousAt
  obtain ⟨c, m, f, hc, ⟨U, hU, hwU, hfU⟩, b, hbdd, hb, heq⟩ :=
    hv d (F z) (HolomorphicMaps.coordinateMap_mem_target hzd)
  refine ⟨c, m, fun j y => f j (F y), hc, ⟨HolomorphicMaps.coordinateDomain g e d ∩ F ⁻¹' U,
    hFc.continuousOn.isOpen_inter_preimage hD hU, ⟨hzd, hwU⟩, fun j => ?_⟩,
    fun y => b (F y), hbdd.comp_continuousAt hFz, ?_, ?_⟩
  · exact (hfU j).comp ((hFc.differentiableOn (by simp)).mono inter_subset_left)
      (fun y hy => hy.2)
  · filter_upwards [hD.mem_nhds hzd, hFz.eventually hb] with y hy hby hne
    have hne' : generatorNormSq f (F y) ≠ 0 := hne
    exact (hby hne').comp y (HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hy)
  · filter_upwards [hD.mem_nhds hzd, hFz.eventually heq] with y hy hey
    have hleft : chartFunction (fun z => v (g z)) e y = chartFunction v d (F y) := by
      show v (g (e.val.symm y)) = v (d.val.symm (d.val (g (e.val.symm y))))
      rw [d.val.left_inv hy.2]
    rw [hleft, hey]
    rfl

end Comp

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {V : ClosedIrreducibleAnalyticSubvariety n X}

/-! ### The restricted presentation -/

section Presentation

variable (hk : V.dim ≤ n) (hW : ∀ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x V.dim)
  [ConnectedSpace V.carrier] [Nonempty V.carrier]

/-- The restriction of a potential with analytic singularities that is finite somewhere on `V` is a
potential of the restricted background on the connected `↥V`. -/
theorem isThetaPshPotential_restrict {θ : ClosedRealOneOneForm n X} {u : X → EReal}
    (hu : ThetaPlurisubharmonic θ.val u) {x : X} (hxV : x ∈ V.carrier) (hx : u x ≠ ⊥) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) θ).val
      (fun y : V.carrier => u y.1) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hpsh := GlobalPotentialPullback.thetaPlurisubharmonic_comp (contMDiff_val hk hW) hu
  exact ⟨hpsh, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh
    ⟨⟨x, hxV⟩, hx⟩⟩

variable {omega : KahlerBackground n X} {alpha : RealBottChern n X} {ε : PositiveError}

theorem exists_mem_ne_bot (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    ∃ x ∈ V.carrier, p.potential x ≠ ⊥ := by
  obtain ⟨x, hxV, hx⟩ := not_subset.mp p.not_carrier_subset_poleSet
  exact ⟨x, hxV, hx⟩

/-- **The restriction of an admissible presentation to `↥V`**: representative `θ_p|_V`, potential
`u_p|_V`, Kähler form `ω|_V`, as a presentation of the whole complex manifold `↥V`. -/
def restrictPresentation (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    AdmissibleRestrictedCurrentPresentation
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW omega)
      (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) p.representative))
      (DominationBigRestriction.univSubvariety (k := V.dim) (Z := V.carrier)) ε :=
  letI := chartedSpace hk hW
  haveI := isComplexManifold_chartedSpace hk hW
  { representative := ClosedRealOneOneForm.pullback (contMDiff_val hk hW) p.representative
    represents := rfl
    potential := fun y => p.potential y.1
    potential_psh := by
      obtain ⟨x, hxV, hx⟩ := exists_mem_ne_bot p
      exact (SubmanifoldMassCalculus.isThetaPshPotential_pullback_add_smul_iff hk hW
        p.representative omega.form (ε : ℝ) _).mp
        (isThetaPshPotential_restrict hk hW p.potential_psh.1 hxV hx)
    smoothAnalyticSingularities :=
      hasManifoldAnalyticSingularitiesSmoothOffPole_comp (contMDiff_val hk hW)
        p.smoothAnalyticSingularities
    not_carrier_subset_poleSet := by
      obtain ⟨x, hxV, hx⟩ := exists_mem_ne_bot p
      exact fun h => hx (h (mem_univ (⟨x, hxV⟩ : V.carrier))) }

theorem restrictPresentation_potential (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε)
    (y : V.carrier) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (restrictPresentation hk hW p).potential y = p.potential y.1 := rfl

theorem restrictPresentation_representative
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (restrictPresentation hk hW p).representative =
      ClosedRealOneOneForm.pullback (contMDiff_val hk hW) p.representative := rfl

end Presentation

/-! ### The restricted density in the two descriptions -/

section Density

variable (hk : V.dim ≤ n) (hW : ∀ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x V.dim)
  [ConnectedSpace V.carrier] [Nonempty V.carrier]
  {omega : KahlerBackground n X} {alpha : RealBottChern n X} {ε : PositiveError}

theorem add_mem_parameterDomain_of_mem_targetPatch (P : RegularPatch V) {v₀ : ComplexModel V.dim}
    (hv₀ : v₀ ∈ P.parameterDomain) {w : ComplexModel V.dim}
    (hw : letI := chartedSpace hk hW
      haveI := isComplexManifold_chartedSpace hk hW
      w ∈ (targetPatch hk hW P hv₀).parameterDomain) :
    w + v₀ ∈ P.parameterDomain := by
  have h := (mem_targetPatch_parameterDomain_iff hk hW P hv₀ w).mp hw
  rw [transition_target] at h
  exact h.1

/-- **The restricted density is intrinsic.**  On the target patch (`targetPatch(w) = P(w + v₀)`), the
density of the restricted presentation `p|_V` is the density of `p` on `P`, at every parameter whose
point is not a pole of `p`. -/
theorem patchDensity_targetPatch (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε)
    (P : RegularPatch V) {v₀ : ComplexModel V.dim} (hv₀ : v₀ ∈ P.parameterDomain)
    {w : ComplexModel V.dim}
    (hw : letI := chartedSpace hk hW
      haveI := isComplexManifold_chartedSpace hk hW
      w ∈ (targetPatch hk hW P hv₀).parameterDomain)
    (hpole : P.toManifold (w + v₀) ∉ poleSet p.potential) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    patchDensity (restrictPresentation hk hW p) (targetPatch hk hW P hv₀) w =
      patchDensity p P (w + v₀) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hval := contMDiff_val hk hW
  set P' := targetPatch hk hW P hv₀ with hP'
  set E : ComplexChart V.dim V.carrier := complexChartAt (n := V.dim) P'.center with hE
  set e : ComplexChart n X := complexChartAt (n := n) P.center with he
  set H := HolomorphicMaps.coordinateMap (Subtype.val : V.carrier → X) E e with hH
  have hdom : ∀ w' : ComplexModel V.dim, w' ∈ P'.parameterDomain →
      P'.coordinateParametrization w' ∈ HolomorphicMaps.coordinateDomain Subtype.val E e := by
    intro w' hw'
    refine ⟨P'.source_subset (P'.flattening.mapsTo_invFun hw'), ?_⟩
    change ((P'.toManifold w' : V.carrier) : X) ∈ e.val.source
    rw [val_targetPatch_toManifold hk hW P hv₀ hw']
    exact RegularPatchNeighborhood.RegularPatch.toManifold_mem_chart_source P
      (add_mem_parameterDomain_of_mem_targetPatch hk hW P hv₀ hw')
  have hHcp : ∀ w' : ComplexModel V.dim, w' ∈ P'.parameterDomain →
      H (P'.coordinateParametrization w') = P.coordinateParametrization (w' + v₀) := by
    intro w' hw'
    change e.val ((P'.toManifold w' : V.carrier) : X) = _
    rw [val_targetPatch_toManifold hk hW P hv₀ hw']
    exact RegularPatchNeighborhood.RegularPatch.chart_toManifold P
      (add_mem_parameterDomain_of_mem_targetPatch hk hW P hv₀ hw')
  set z := P'.coordinateParametrization w with hzdef
  have hz : z ∈ HolomorphicMaps.coordinateDomain Subtype.val E e := hdom w hw
  have hHz : H z = P.coordinateParametrization (w + v₀) := hHcp w hw
  have hPopen : IsOpen P'.parameterDomain :=
    AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P'
  have hHdiff : DifferentiableAt ℝ H z :=
    (HolomorphicMaps.coordinateMap_contDiffAt_real hval E e hz).differentiableAt (by simp)
  have hcpdiff : DifferentiableAt ℝ P'.coordinateParametrization w :=
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      P' hw).restrictScalars ℝ
  -- the chain rule for the parametrizations
  set cp' : ComplexModel V.dim → ComplexModel V.dim := P'.coordinateParametrization with hcp'
  have hfd : fderiv ℝ P.coordinateParametrization (w + v₀) =
      (fderiv ℝ H z).comp (fderiv ℝ cp' w) := by
    have hmem : ∀ᶠ x in 𝓝 (w + v₀), x - v₀ ∈ P'.parameterDomain := by
      have hc : Tendsto (fun x : ComplexModel V.dim => x - v₀) (𝓝 (w + v₀)) (𝓝 w) := by
        have := ((continuous_sub_right v₀).tendsto (w + v₀))
        rwa [add_sub_cancel_right] at this
      exact hc.eventually (hPopen.mem_nhds hw)
    have heq : P.coordinateParametrization =ᶠ[𝓝 (w + v₀)] fun x => H (cp' (x - v₀)) := by
      filter_upwards [hmem] with x hx
      rw [hcp', hHcp (x - v₀) hx, sub_add_cancel]
    have hcpd : DifferentiableAt ℝ cp' ((w + v₀) - v₀) := by
      rw [add_sub_cancel_right]; exact hcpdiff
    have hsub : DifferentiableAt ℝ (fun x => cp' (x - v₀)) (w + v₀) :=
      (differentiableAt_comp_sub v₀).mpr hcpd
    have hH' : DifferentiableAt ℝ H (cp' ((w + v₀) - v₀)) := by
      rw [add_sub_cancel_right]; exact hHdiff
    have hcomp : fderiv ℝ (fun x => H (cp' (x - v₀))) (w + v₀) =
        (fderiv ℝ H (cp' ((w + v₀) - v₀))).comp (fderiv ℝ (fun x => cp' (x - v₀)) (w + v₀)) :=
      fderiv_comp (w + v₀) (g := H) (f := fun x => cp' (x - v₀)) hH' hsub
    rw [heq.fderiv_eq, hcomp, fderiv_comp_sub v₀, add_sub_cancel_right]
  -- the form part
  have hform : (perturbedRepresentative (restrictPresentation hk hW p)).val.coeff E z =
      ((perturbedRepresentative p).val.coeff e (H z)).compContinuousLinearMap (fderiv ℝ H z) := by
    simp only [perturbedRepresentative, restrictPresentation_representative,
      SubmanifoldKahlerRestriction.kahlerBackground_form, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.pullback_val,
      SmoothRealForm.pullback_coeff hval _ E e hz]
    ext v
    simp [hH]
  -- the `ddᶜ` part
  have hsmooth : AdmissibleCurrentFormPositivity.SmoothOffPoleSet (n := n) p.potential :=
    AdmissibleCurrentFormPositivity.SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
      p.smoothAnalyticSingularities
  have hHzt : H z ∈ e.val.target := HolomorphicMaps.coordinateMap_mem_target hz
  have hpole' : e.val.symm (H z) ∉ poleSet p.potential := by
    rw [hHz]
    exact hpole
  obtain ⟨g, hg, hpg⟩ := hsmooth e (H z) hHzt hpole'
  set ρ : ComplexModel n → ℝ := fun y => (p.potential (e.val.symm y)).toReal with hρ
  have hρg : ρ =ᶠ[𝓝 (H z)] g := by
    filter_upwards [hpg] with y hy
    change (chartFunction p.potential e y).toReal = g y
    rw [hy, EReal.toReal_coe]
  obtain ⟨t, ht, htopen, hHzt'⟩ := eventually_nhds_iff.mp hg
  have hgt : ContDiffOn ℝ ∞ g t := fun y hy => (ht y hy).contDiffWithinAt
  set U := HolomorphicMaps.coordinateDomain (Subtype.val : V.carrier → X) E e ∩ H ⁻¹' t with hU
  have hUo : IsOpen U :=
    (HolomorphicMaps.coordinateMap_contDiffOn hval E e).continuousOn.isOpen_inter_preimage
      (HolomorphicMaps.coordinateDomain_isOpen hval E e) htopen
  have hzU : z ∈ U := ⟨hz, hHzt'⟩
  have hcomp := HolomorphicDDC.smoothDDC_comp hUo htopen
    ((HolomorphicMaps.coordinateMap_contDiffOn hval E e).mono inter_subset_left) hgt
    (fun y hy => hy.2) hzU
  rw [← hH] at hcomp
  have hddc : smoothDDC
      (fun y => ((restrictPresentation hk hW p).potential (E.val.symm y)).toReal) z =
      (smoothDDC ρ (H z)).compContinuousLinearMap (fderiv ℝ H z) := by
    rw [smoothDDC_congr hρg, ← hcomp]
    apply smoothDDC_congr
    have hHc : ContinuousAt H z := hHdiff.continuousAt
    filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen hval E e).mem_nhds hz,
      hHc.eventually hρg] with y hy hyρ
    rw [← hyρ]
    show (p.potential ((E.val.symm y : V.carrier) : X)).toReal =
      (p.potential (e.val.symm (e.val ((E.val.symm y : V.carrier) : X)))).toReal
    rw [e.val.left_inv hy.2]
  -- assemble
  have hA : coordinateCurrentForm (restrictPresentation hk hW p) E z =
      (coordinateCurrentForm p e (H z)).compContinuousLinearMap (fderiv ℝ H z) := by
    unfold coordinateCurrentForm
    rw [hform, hddc]
    ext v
    simp [hρ]
  unfold patchDensity
  change MongeAmpere.actualTopPowerDensity
      ((coordinateCurrentForm (restrictPresentation hk hW p) E z).compContinuousLinearMap
        (fderiv ℝ cp' w)) = _
  rw [hA, ← RegularPatchPullback.compContinuousLinearMap_comp', ← hfd, hHz, he]

end Density

end

end SGPT.Foundations.Analysis.Pending.SubmanifoldRestrictedPresentation
