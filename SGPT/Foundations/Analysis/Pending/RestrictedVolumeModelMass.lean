import SGPT.Foundations.Analysis.Pending.SubmanifoldACTopMass
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePositivity
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance
import SGPT.Foundations.Analysis.Pending.Envelopes

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Route F, `F-b` step P1: the restricted volume is at most the restricted masses of the model potentials

Plan §8 of `scratch/tn23-envelopes-qea-plan-0117.md`, blueprint `pc:f-restricted-volume-le`
(Copy-4 `sec:trace-approx`; CT22 Remark 2.2, the easy half).  Let `V` be a closed connected
submanifold of the compact Kähler manifold `X`, `γ = θ|_V`, `ω_V = ω|_V`, and for `ε > 0` let
`V_ε = V_{θ+εω}` be the model potential of `θ + εω`.  Then

    h = ⟨{θ}^k⟩_{X|V} ≤ h_ε := ∫_V ⟨(γ + εω_V)_{V_ε|_V}^k⟩      (`numericalRestrictedVolume_le_restrictedModelMass`)

and, when `h > 0`, `V_ε|_V` is a `(γ + εω_V)`-psh potential for every `ε > 0`
(`isThetaPshPotential_restrictedModel`).

Proof, for one admissible presentation `p` at error `ε` (representative `θ_p`, potential `u_p`):
* `acTopMass p ≤ ∫_V ⟨(θ_p|_V + εω_V)_{u_p|_V}^k⟩` (`SubmanifoldACTopMass`);
* change of representative: `θ = θ_p + ddᶜh` (Bott–Chern), so `θ|_V = θ_p|_V + ddᶜ(h|_V)` and the
  measure of `(θ_p|_V + εω_V, u_p|_V)` is that of `(γ + εω_V, (u_p - h)|_V)`
  (`GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative`);
* `u_p - h` is a `(θ + εω)`-psh potential on `X`, so `u_p - h - C ≤ V_ε`, and monotonicity of the
  mass in the singularity type on `V` gives `≤ h_ε`.
The envelope over presentations and the limit `ε ↓ 0` (an infimum, `RestrictedVolumePositivity`)
finish.  Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumeModelMass

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
  FirstPass.BlowupSequences SubmanifoldChartedSpace SubmanifoldRestrictedPresentation
  SubmanifoldACTopMass DiagonalMass

/-! ### Bott–Chern relations restrict to submanifolds (any dimensions) -/

section Pullback

variable {k n : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- Chart-smooth functions pull back to chart-smooth functions along holomorphic maps (any
dimensions; `AdmissiblePresentationPullback.chartSmooth_comp` is the equal-dimensional case). -/
theorem chartSmooth_comp {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) {h : Y → ℝ}
    (hh : ChartSmooth (n := n) h) : ChartSmooth (n := k) (fun z => h (g z)) := by
  intro e u hu
  set d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hu, mem_complexChartAt_source _⟩
  have h1 := HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hud
  have h2 := (hh d).contDiffAt
    (d.val.open_target.mem_nhds (HolomorphicMaps.coordinateMap_mem_target hud))
  have h3 := ContDiffAt.comp (g := fun z => h (d.val.symm z)) u h2 h1
  refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen hg e d).mem_nhds hud] with u' hu'
  show h (g (e.val.symm u')) = h (d.val.symm (d.val (g (e.val.symm u'))))
  rw [d.val.left_inv hu'.2]

/-- **`b = a + ddᶜh` restricts**: `g^*b = g^*a + ddᶜ(h ∘ g)` in every chart. -/
theorem pullback_coeff_eq_add_smoothDDC {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    {a b : ClosedRealOneOneForm n Y} {h : Y → ℝ} (hh : ChartSmooth (n := n) h)
    (heq : ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      b.val.coeff e z = a.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    (e : ComplexChart k Z) {z : ComplexModel k} (hz : z ∈ e.val.target) :
    (ClosedRealOneOneForm.pullback hg b).val.coeff e z =
      (ClosedRealOneOneForm.pullback hg a).val.coeff e z +
        smoothDDC (fun y => h (g (e.val.symm y))) z := by
  set d := complexChartAt (n := n) (g (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hg e d
  have hddc : smoothDDC (fun y => h (g (e.val.symm y))) z =
      (smoothDDC (fun w => h (d.val.symm w))
        (HolomorphicMaps.coordinateMap g e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap g e d) z) := by
    rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
      (HolomorphicMaps.coordinateMap_contDiffOn hg e d) (hh d)
      (fun _ hy => HolomorphicMaps.coordinateMap_mem_target hy) hzd]
    apply smoothDDC_congr
    filter_upwards [hD.mem_nhds hzd] with y hy
    show h (g (e.val.symm y)) = h (d.val.symm (d.val (g (e.val.symm y))))
    rw [d.val.left_inv hy.2]
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hg _ e d hzd, SmoothRealForm.pullback_coeff hg _ e d hzd,
    hddc, heq d _ (HolomorphicMaps.coordinateMap_mem_target hzd)]
  ext v
  simp

end Pullback

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- The potential `V_{θ+εω}|_V`. -/
def restrictedModel (θ omegaForm : ClosedRealOneOneForm n X) (ε : ℝ) {W : Set X} :
    W → EReal :=
  fun y => thetaPshSupremum (θ + ε • omegaForm).val y.1

/-- **One presentation.**  For an admissible presentation `p` of `{θ}` along `V` at error `ε` and any
proof that `V_ε|_V` is a `(γ + εω_V)`-potential, `acTopMass p ≤ ∫_V ⟨(γ + εω_V)_{V_ε|_V}^k⟩`. -/
theorem acTopMass_le_restrictedModelMass (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) {ε : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) V ε)
    (hVε : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          (ε : ℝ) • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
        (restrictedModel θ omega.form ε (W := V.carrier))) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV.1
    acTopMass p ≤ diagonalPotentialMass
      (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
        (ε : ℝ) • (SubmanifoldKahlerRestriction.kahlerBackground
          (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form)
      (restrictedModel θ omega.form ε (W := V.carrier)) hVε := by
  set hk := le_of_isClosedConnectedSubmanifold hV
  set hW := hV.2.2
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV.1
  have : ConnectedSpace V.carrier :=
    SubmanifoldMassCalculus.connectedSpace_of_isClosedConnectedSubmanifold hV
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  have : Nonempty X := ⟨(Classical.choice (inferInstance : Nonempty V.carrier)).1⟩
  have hval := contMDiff_val hk hW
  set ωV := SubmanifoldKahlerRestriction.kahlerBackground hk hW omega with hωV
  -- the Bott–Chern correction `θ = θ_p + ddᶜh`
  obtain ⟨h, hh, hθ⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp p.represents
  -- step 1: the bridge
  have h1 := acTopMass_le_diagonalPotentialMass_restrict hk hW hV.1 p
  -- step 2: change of representative on `V`
  have hθη : ∀ (e : ComplexChart V.dim V.carrier) (z : ComplexModel V.dim), z ∈ e.val.target →
      (ClosedRealOneOneForm.pullback hval θ + (ε : ℝ) • ωV.form).val.coeff e z =
        (ClosedRealOneOneForm.pullback hval p.representative + (ε : ℝ) • ωV.form).val.coeff e z +
          smoothDDC (fun y => (fun x : V.carrier => h x.1) (e.val.symm y)) z := by
    intro e z hz
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add,
      pullback_coeff_eq_add_smoothDDC hval hh hθ e hz]
    abel
  have hhV : ChartSmooth (n := V.dim) (fun x : V.carrier => h x.1) := chartSmooth_comp hval hh
  have hpshp := (restrictPresentation hk hW p).potential_psh
  have hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hval θ + (ε : ℝ) • ωV.form).val
      (fun x : V.carrier => p.potential x.1 - (h x.1 : EReal)) :=
    PositiveClasses.thetaPshPotential_sub_smooth hhV hθη hpshp
  have h2 : diagonalPotentialMass
      (ClosedRealOneOneForm.pullback hval p.representative + (ε : ℝ) • ωV.form)
      (fun y : V.carrier => p.potential y.1) hpshp =
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hval θ + (ε : ℝ) • ωV.form)
        (fun x : V.carrier => p.potential x.1 - (h x.1 : EReal)) hw := by
    have hinv := GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
      (θ := fun _ : Fin V.dim =>
        ClosedRealOneOneForm.pullback hval p.representative + (ε : ℝ) • ωV.form)
      (η := fun _ : Fin V.dim => ClosedRealOneOneForm.pullback hval θ + (ε : ℝ) • ωV.form)
      (u := fun _ : Fin V.dim => fun y : V.carrier => p.potential y.1)
      (f := fun _ : Fin V.dim => fun x : V.carrier => h x.1) (fun _ => hhV) (fun _ => hθη)
      (fun _ => hpshp.1)
    exact (congrArg (fun μ : Measure V.carrier => μ univ) hinv).symm
  -- step 3: `u_p - h - C ≤ V_ε` on `X`, monotonicity on `V`
  have hθηX : ∀ (e : ComplexChart n X) (z : ComplexModel n), z ∈ e.val.target →
      (θ + (ε : ℝ) • omega.form).val.coeff e z =
        (p.representative + (ε : ℝ) • omega.form).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z := by
    intro e z hz
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, hθ e z hz]
    abel
  have hU : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val
      (fun x => p.potential x - (h x : EReal)) :=
    PositiveClasses.thetaPshPotential_sub_smooth hh hθηX p.potential_psh
  obtain ⟨C, hC⟩ := hU.exists_global_upper_bound
  have hle : (fun x => (fun x => p.potential x - (h x : EReal)) x - (C : EReal)) ≤
      thetaPshSupremum (θ + (ε : ℝ) • omega.form).val :=
    le_thetaPshSupremum (hU.sub_const C) (sub_const_nonpositive_of_le hC)
  have hmore : MoreSingularOn (fun x : V.carrier => p.potential x.1 - (h x.1 : EReal))
      (restrictedModel θ omega.form ε (W := V.carrier)) univ := by
    refine ⟨C, fun x _ => ?_⟩
    have hx := hle x.1
    have hcancel : p.potential x.1 - (h x.1 : EReal) =
        (p.potential x.1 - (h x.1 : EReal) - (C : EReal)) + (C : EReal) :=
      (EReal.sub_add_cancel).symm
    calc p.potential x.1 - (h x.1 : EReal)
        = (p.potential x.1 - (h x.1 : EReal) - (C : EReal)) + (C : EReal) := hcancel
      _ ≤ thetaPshSupremum (θ + (ε : ℝ) • omega.form).val x.1 + (C : EReal) := by gcongr
  have h3 := diagonalPotentialMass_mono_of_kahler ωV hw hVε hmore
  calc acTopMass p ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3

/-- **P1: the restricted volume is at most the restricted mass of every model potential.**  For
`ε > 0`, if `V_ε|_V` is a `(γ + εω_V)`-psh potential, then `h = ⟨{θ}^k⟩_{X|V} ≤ h_ε`. -/
theorem numericalRestrictedVolume_le_restrictedModelMass (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) {ε : ℝ} (hε : 0 < ε)
    (hVε : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
        (restrictedModel θ omega.form ε (W := V.carrier))) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV.1
    numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V ≤ diagonalPotentialMass
      (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
        ε • (SubmanifoldKahlerRestriction.kahlerBackground
          (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form)
      (restrictedModel θ omega.form ε (W := V.carrier)) hVε := by
  by_cases hnn : V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)
  · rw [numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus _ _ _ hnn]
    exact zero_le
  · rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega _ V hnn]
    refine (iInf_le _ (⟨ε, hε⟩ : PositiveError)).trans ?_
    refine iSup_le fun p => ?_
    exact acTopMass_le_restrictedModelMass omega θ V hV p hVε

/-- **Positive restricted volume gives presentations at every error.** -/
theorem nonempty_presentation_of_pos (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hpos : 0 < numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V)
    (ε : PositiveError) :
    Nonempty (AdmissibleRestrictedCurrentPresentation omega
      (RealBottChern.ofRepresentative θ) V ε) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hnn : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ) := fun h => by
    rw [numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus _ _ _ h] at hpos
    exact lt_irrefl _ hpos
  rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega _ V hnn] at hpos
  have hle := iInf_le (fun ε : PositiveError =>
    restrictedMassEnvelope (acTopMassData omega) (RealBottChern.ofRepresentative θ) V ε) ε
  have h0 : restrictedMassEnvelope (acTopMassData omega) (RealBottChern.ofRepresentative θ) V ε = 0 :=
    iSup_of_empty _
  rw [h0] at hle
  exact lt_irrefl _ (hpos.trans_le hle)

/-- **`V_ε|_V` is a potential** as soon as there is an admissible presentation at error `ε`: the
corrected potential `u_p - h` of the presentation is a competitor for `V_ε` on `X`, finite at a
point of `V`. -/
theorem isThetaPshPotential_restrictedModel (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) {ε : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) V ε) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    IsThetaPshPotential
      (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
        (ε : ℝ) • (SubmanifoldKahlerRestriction.kahlerBackground
          (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
      (restrictedModel θ omega.form ε (W := V.carrier)) := by
  set hk := le_of_isClosedConnectedSubmanifold hV
  set hW := hV.2.2
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have : ConnectedSpace V.carrier :=
    SubmanifoldMassCalculus.connectedSpace_of_isClosedConnectedSubmanifold hV
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  have : Nonempty X := ⟨(Classical.choice (inferInstance : Nonempty V.carrier)).1⟩
  obtain ⟨h, hh, hθ⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp p.represents
  have hθηX : ∀ (e : ComplexChart n X) (z : ComplexModel n), z ∈ e.val.target →
      (θ + (ε : ℝ) • omega.form).val.coeff e z =
        (p.representative + (ε : ℝ) • omega.form).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z := by
    intro e z hz
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, hθ e z hz]
    abel
  have hU : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val
      (fun x => p.potential x - (h x : EReal)) :=
    PositiveClasses.thetaPshPotential_sub_smooth hh hθηX p.potential_psh
  have hVX : IsThetaPshPotential (θ + (ε : ℝ) • omega.form).val
      (thetaPshSupremum (θ + (ε : ℝ) • omega.form).val) :=
    thetaPshSupremum_isThetaPshPotential _ (θ + (ε : ℝ) • omega.form).2.1
      (θ + (ε : ℝ) • omega.form).2.2 hU.1.hasSmoothLocalPotentials ⟨_, hU⟩
  obtain ⟨C, hC⟩ := hU.exists_global_upper_bound
  have hle : (fun x => (fun x => p.potential x - (h x : EReal)) x - (C : EReal)) ≤
      thetaPshSupremum (θ + (ε : ℝ) • omega.form).val :=
    le_thetaPshSupremum (hU.sub_const C) (sub_const_nonpositive_of_le hC)
  obtain ⟨x, hxV, hx⟩ := exists_mem_ne_bot p
  have hfin : thetaPshSupremum (θ + (ε : ℝ) • omega.form).val x ≠ ⊥ := by
    intro hbot
    have h1 := hle x
    rw [hbot, le_bot_iff] at h1
    have h2 : p.potential x - (h x : EReal) - (C : EReal) ≠ ⊥ := by
      induction hpx : p.potential x using EReal.rec with
      | bot => exact absurd hpx hx
      | top => simp
      | coe r => rw [← EReal.coe_sub, ← EReal.coe_sub]; exact EReal.coe_ne_bot _
    exact h2 h1
  exact (SubmanifoldMassCalculus.isThetaPshPotential_pullback_add_smul_iff hk hW θ omega.form
    (ε : ℝ) _).mp (isThetaPshPotential_restrict hk hW hVX.1 hxV hfin)

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumeModelMass
