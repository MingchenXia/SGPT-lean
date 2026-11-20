import SGPT.Okounkov.TranscendentalVolumeConcavityStatement
import SGPT.Okounkov.TranscendentalCoreRepresentative
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.ModificationInputs
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.Envelopes
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSetBounded
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.AmbientConvexCurrent
import SGPT.PSH.SourceGentleApproximation

/-!
# The restricted volume: well-definedness and bounds

Source: blueprint node `tok:restricted-volume` (DRWNXZ §2, before Theorem 2.10): for a
connected closed submanifold `Z ⊆ X` of dimension `d` and a class `ξ`,
`vol_{X|Z}(ξ) = sup ∫_Z ⟨(T|_Z)^d⟩` over `T ∈ Ω(ξ)` whose potential is not identically `-∞`
on `Z` (`restrictedVolume`, published in `TranscendentalVolumeConcavityStatement`).

* `restrictedVolume_eq_of_class_eq`: the restricted volume depends only on the class `ξ = {θ}`
  (replacing `θ` by `θ + dd^c g` replaces `φ` by `φ - g`, which preserves `Ω`, and the restricted
  current `ι^*(θ + dd^c g) + dd^c((φ - g) ∘ ι) = ι^*θ + dd^c(φ ∘ ι)` has the same non-pluripolar
  mass); `classRestrictedVolume` is the class-level quantity;
* `restrictedVolume_le_restrictedMinimalMass`: **upper bound** `vol_{X|Z}(ξ) ≤ ∫_Z ⟨(θ|_Z +
  dd^c V_θ|_Z)^d⟩` (`φ ≤ V_θ + C`, monotonicity on `Z`), and `restrictedVolume_lt_top`;
* `restrictedVolume_pos`: **lower bound** — if `ι^*w` is Kähler (e.g. `Z` a submanifold) and
  some `T ∈ Ω(ξ)` has potential not identically `-∞` on `Z`, then `vol_{X|Z}(ξ) > 0` (`T ≥ cω`
  gives `T|_Z ≥ c ω|_Z`, whose top mass is at least `c^d ∫_Z ω|_Z^d`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalVolumeConcavity

open Set Filter MeasureTheory
open scoped ENNReal Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass

section Basic

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

/-! ### Pullback of a `dd^c`-change of representative -/

include hι in
/-- `ι^*(θ + dd^c g) = ι^*θ + dd^c (g ∘ ι)` in every chart of `V`. -/
theorem pullback_coeff_add_ddc {θ θ' : ClosedRealOneOneForm n X} {g : X → ℝ}
    (hg : ChartSmooth (n := n) g)
    (heq : ∀ (e : ComplexChart n X) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z) :
    ∀ (e : ComplexChart k V) (z : ComplexModel k), z ∈ e.val.target →
      (ClosedRealOneOneForm.pullback hι θ').val.coeff e z =
        (ClosedRealOneOneForm.pullback hι θ).val.coeff e z +
          smoothDDC (fun y => g (ι (e.val.symm y))) z := by
  intro e z hz
  set d := complexChartAt (n := n) (ι (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain ι e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hι e d
  have hddc : smoothDDC (fun y => g (ι (e.val.symm y))) z =
      (smoothDDC (fun w => g (d.val.symm w))
        (HolomorphicMaps.coordinateMap ι e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap ι e d) z) := by
    rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
      (HolomorphicMaps.coordinateMap_contDiffOn hι e d) (hg d)
      (fun _ hy => HolomorphicMaps.coordinateMap_mem_target hy) hzd]
    apply smoothDDC_congr
    filter_upwards [hD.mem_nhds hzd] with y hy
    show g (ι (e.val.symm y)) = g (d.val.symm (d.val (ι (e.val.symm y))))
    rw [d.val.left_inv hy.2]
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hι _ e d hzd, SmoothRealForm.pullback_coeff hι _ e d hzd,
    hddc, heq d _ (HolomorphicMaps.coordinateMap_mem_target hzd)]
  ext v
  simp

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

/-! ### Well-definedness -/

include hι in
/-- One inequality of the representative independence. -/
theorem restrictedVolume_le_of_bottChernRel {θ θ' : ClosedRealOneOneForm n X}
    (hrel : ClosedRealOneOneForm.BottChernRel θ θ') :
    restrictedVolume ι hι θ ≤ restrictedVolume ι hι θ' := by
  obtain ⟨g, hg, heq⟩ := hrel
  unfold restrictedVolume
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hw => ?_
  have hφ' := TranscendentalCore.sub_mem_gentleKahlerCurrents hg heq hφ
  have hpull := pullback_coeff_add_ddc hι hg heq
  have hgι := ProductTestForms.chartSmooth_comp hι hg
  have hw' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ').val
      (fun y => φ (ι y) - (g (ι y) : EReal)) :=
    PositiveClasses.thetaPshPotential_sub_smooth hgι hpull hw
  have hmass := GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
    (θ := fun _ : Fin k => ClosedRealOneOneForm.pullback hι θ)
    (η := fun _ => ClosedRealOneOneForm.pullback hι θ')
    (u := fun _ => fun y => φ (ι y)) (f := fun _ => fun y => g (ι y))
    (fun _ => hgι) (fun _ => hpull) (fun _ => hw.1)
  refine le_iSup_of_le (fun x => φ x - (g x : EReal)) (le_iSup_of_le hφ' (le_iSup_of_le hw' ?_))
  exact (congrArg (fun μ : Measure V => μ univ) hmass).ge

include hι in
/-- **`tok:restricted-volume`, well-definedness**: `vol_{X|Z}(ξ)` depends only on the class
`ξ = {θ}`. -/
theorem restrictedVolume_eq_of_class_eq {θ θ' : ClosedRealOneOneForm n X}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    restrictedVolume ι hι θ = restrictedVolume ι hι θ' := by
  have hrel := (RealBottChern.ofRepresentative_eq_iff θ θ').mp h
  exact le_antisymm (restrictedVolume_le_of_bottChernRel hι hrel)
    (restrictedVolume_le_of_bottChernRel hι (ClosedRealOneOneForm.BottChernRel.symm hrel))

/-- **`tok:restricted-volume`**: the restricted volume `vol_{X|Z}(ξ)` of a class, computed with
any representative (`restrictedVolume_eq_classRestrictedVolume`). -/
def classRestrictedVolume (ι : V → X)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (ξ : RealBottChern n X) : ℝ≥0∞ :=
  restrictedVolume ι hι (Quotient.out ξ)

include hι in
/-- The class-level restricted volume is the restricted volume of every representative. -/
theorem restrictedVolume_eq_classRestrictedVolume (θ : ClosedRealOneOneForm n X) :
    restrictedVolume ι hι θ =
      classRestrictedVolume ι hι (RealBottChern.ofRepresentative θ) :=
  restrictedVolume_eq_of_class_eq hι (Quotient.out_eq (RealBottChern.ofRepresentative θ)).symm

/-! ### Bounds -/

variable [CompactSpace X] [Nonempty X]

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
include hι in
/-- If some potential of `PSH(X, θ)` restricts to a genuine `ι^*θ`-psh potential, so does `V_θ`
(`φ ≤ V_θ + C`). -/
theorem isThetaPshPotential_comp_thetaPshSupremum {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y))) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => thetaPshSupremum θ.val (ι y)) := by
  have hV := FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
    hφ.1.hasSmoothLocalPotentials ⟨_, hφ⟩
  obtain ⟨C, hC⟩ := FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    hφ.1.hasSmoothLocalPotentials ⟨_, hφ⟩ φ hφ
  refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hV.1, ?_⟩
  intro y U hU hyU
  obtain ⟨z, hzU, hz⟩ := hw.2 y U hU hyU
  refine ⟨z, hzU, fun hbot => hz ?_⟩
  have h := hC (ι z) (mem_univ _)
  simp only at hbot
  rw [hbot, EReal.bot_add] at h
  exact le_bot_iff.mp h

include hι in
/-- **`tok:restricted-volume`, upper bound**: `vol_{X|Z}(ξ) ≤ ∫_Z ⟨(θ|_Z + dd^c V_θ|_Z)^d⟩`. -/
theorem restrictedVolume_le_restrictedMinimalMass (ωV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n X)
    (hV : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => thetaPshSupremum θ.val (ι y))) :
    restrictedVolume ι hι θ ≤
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
        (fun y => thetaPshSupremum θ.val (ι y)) hV := by
  unfold restrictedVolume
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hw => ?_
  have hφ' : IsThetaPshPotential θ.val φ := hφ.1.1
  obtain ⟨C, hC⟩ := FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    hφ'.1.hasSmoothLocalPotentials ⟨_, hφ'⟩ φ hφ'
  exact diagonalPotentialMass_mono_of_kahler ωV hw hV
    ⟨C, fun y _ => hC (ι y) (mem_univ _)⟩

include hι in
/-- **`tok:restricted-volume`, finiteness**: `vol_{X|Z}(ξ) < ∞`. -/
theorem restrictedVolume_lt_top (ωV : KahlerBackground k V) (θ : ClosedRealOneOneForm n X) :
    restrictedVolume ι hι θ < ⊤ := by
  by_cases h : ∃ φ ∈ TranscendentalCore.gentleKahlerCurrents θ,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y))
  · obtain ⟨φ, hφ, hw⟩ := h
    have hV := isThetaPshPotential_comp_thetaPshSupremum hι hφ.1.1 hw
    exact (restrictedVolume_le_restrictedMinimalMass hι ωV θ hV).trans_lt
      (MixedMass.globalMixedMass_lt_top ωV _)
  · have h0 : restrictedVolume ι hι θ = 0 := by
      apply le_antisymm _ bot_le
      unfold restrictedVolume
      exact iSup_le fun φ => iSup_le fun hφ => iSup_le fun hw => absurd ⟨φ, hφ, hw⟩ h
    rw [h0]
    exact ENNReal.zero_lt_top

omit [Nonempty X] in
include hι in
/-- **`tok:restricted-volume`, positivity**: if `ι^*w` is Kähler and some `T = θ + dd^c φ ∈ Ω(ξ)`
has potential not identically `-∞` on `Z`, then `vol_{X|Z}(ξ) > 0`. -/
theorem restrictedVolume_pos [Nonempty V] (w : KahlerBackground n X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : φ ∈ TranscendentalCore.gentleKahlerCurrents θ)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y))) :
    0 < restrictedVolume ι hι θ := by
  obtain ⟨κ, hκ⟩ := hφ.2
  obtain ⟨A, hA, hAsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-w.form)
  set c : ℝ := A⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr hA
  have hsemi : (κ.form - c • w.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hAsemi hc0.le
    have he : c • (-w.form + A • κ.form) = κ.form - c • w.form := by
      rw [smul_add, smul_smul, hc, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rwa [he] at h
  have hpsh := LocalPotentials.isThetaPshPotential_add_of_semipositive hκ hsemi
  have he : θ - κ.form + (κ.form - c • w.form) = θ + (-c) • w.form := by
    rw [neg_smul]
    abel
  rw [he] at hpsh
  -- restriction to `V`
  have hres : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hι θ + (-c) • ClosedRealOneOneForm.pullback hι w.form).val
      (fun y => φ (ι y)) :=
    ((ModificationInputs.pullback_add_smul_geometricallyEq hι θ w.form (-c)).thetaPlurisubharmonic_iff
      _).mp (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hpsh.1)
  let ωV : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι w.form, hpull⟩
  have hu₀ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ - c • ωV.form).val
      (fun y => φ (ι y)) := by
    refine ⟨?_, hw.2⟩
    have hf : ClosedRealOneOneForm.pullback hι θ - c • ωV.form =
        ClosedRealOneOneForm.pullback hι θ + (-c) • ClosedRealOneOneForm.pullback hι w.form := by
      rw [neg_smul, sub_eq_add_neg]
    rw [hf]
    exact hres
  have hpos := RestrictedApproximantMass.diagonalPotentialMass_pos_of_sub_smul ωV hc0 hu₀ hw
  refine hpos.trans_le ?_
  unfold restrictedVolume
  exact le_iSup_of_le φ (le_iSup_of_le hφ (le_iSup_of_le hw le_rfl))


end Basic

/-! ### Identification with the restricted mass of `V_θ` -/

section Identification

variable {m k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [Nonempty X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ι)

include hι in
/-- **`tok:restricted-volume`, identification** (DRWNXZ §2; the book's `prop:restvol_voltrace`,
second equality, for the DRWNXZ definition): if `ξ = {θ}` is big, `ι^*w` is Kähler and `Z`
meets the ample locus `X \ E_nK(ξ)`, then `V_θ|_Z` is a `θ|_Z`-psh potential and
`vol_{X|Z}(ξ) = ∫_Z ⟨(θ|_Z + dd^c V_θ|_Z)^d⟩`.

Proof: `≤` is `restrictedVolume_le_restrictedMinimalMass`. For `≥`, take Boucksom's Kähler
current `θ + dd^c ψ ≥ c w` with analytic singularities and polar locus `E_nK(ξ)`; for
`s ∈ (0, 1)`, `u = sV_θ + (1 - s)ψ ∈ PSH(X, θ - (1 - s)c w)`; a gentle quasi-equisingular
approximation `v_j ≥ u` of `u` lies in `Ω(ξ)` for large `j`, and on `Z`,
`∫ ⟨(θ|_Z + dd^c v_j|_Z)^d⟩ ≥ ∫ ⟨(θ|_Z + dd^c u|_Z)^d⟩ ≥ s^d ∫ ⟨(θ|_Z + dd^c V_θ|_Z)^d⟩`;
let `s → 1`. -/
theorem restrictedVolume_eq_restrictedMinimalMass (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : NonKahlerLocus.IsBigClass (RealBottChern.ofRepresentative θ))
    (hZ : ∃ y : V, ι y ∉ NonKahlerLocus.nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    ∃ hV : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
        (fun y => thetaPshSupremum θ.val (ι y)),
      restrictedVolume ι hι θ =
        diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
          (fun y => thetaPshSupremum θ.val (ι y)) hV := by
  classical
  obtain ⟨y₀, hy₀⟩ := hZ
  obtain ⟨K, -, hKpole⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      (Nat.succ_pos m) (RealBottChern.ofRepresentative θ) hbig
  obtain ⟨f, hf, hfeq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp K.represents
  set ψ : X → EReal := fun x => K.potential x - (f x : EReal) with hψdef
  -- `ψ ∈ PSH(X, θ - κ)` for the Kähler lower bound `κ` of `K`
  have hψκ : IsThetaPshPotential (θ - K.lowerBound.form).val ψ := by
    refine PositiveClasses.thetaPshPotential_sub_smooth hf ?_ K.strictlyPsh
    intro e z hz
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      hfeq e z hz]
    abel
  -- `κ ≥ c w`
  obtain ⟨A, hA, hAsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul K.lowerBound (-w.form)
  set c : ℝ := A⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr hA
  have hκc : (K.lowerBound.form - c • w.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hAsemi hc0.le
    have he : c • (-w.form + A • K.lowerBound.form) = K.lowerBound.form - c • w.form := by
      rw [smul_add, smul_smul, hc, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rwa [he] at h
  have hψ : IsThetaPshPotential (θ - c • w.form).val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψκ hκc
    have he : θ - K.lowerBound.form + (K.lowerBound.form - c • w.form) = θ - c • w.form := by
      abel
    rwa [he] at h
  have hψθ : IsThetaPshPotential θ.val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ
      (KahlerDomination.isSemipositive_smul w.isSemipositive hc0.le)
    rwa [sub_add_cancel] at h
  -- `ψ` is finite at `ι y₀`
  have hψy : ψ (ι y₀) ≠ ⊥ := by
    have hK : K.potential (ι y₀) ≠ ⊥ := by
      intro hbot
      apply hy₀
      rw [← hKpole]
      exact hbot
    simp only [hψdef]
    intro hbot
    rw [sub_eq_add_neg, EReal.add_eq_bot_iff] at hbot
    rcases hbot with h | h
    · exact hK h
    · rw [← EReal.coe_neg] at h
      exact EReal.coe_ne_bot _ h
  -- `V_θ`
  have hV := FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
    hψθ.1.hasSmoothLocalPotentials ⟨_, hψθ⟩
  obtain ⟨C, hC⟩ := FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    hψθ.1.hasSmoothLocalPotentials ⟨_, hψθ⟩ ψ hψθ
  have hVy : thetaPshSupremum θ.val (ι y₀) ≠ ⊥ := by
    intro hbot
    have h := hC (ι y₀) (mem_univ _)
    rw [hbot, EReal.bot_add] at h
    exact hψy (le_bot_iff.mp h)
  have hVι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => thetaPshSupremum θ.val (ι y)) :=
    ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hV.1,
      ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
        (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hV.1) ⟨y₀, hVy⟩⟩
  have hψι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => ψ (ι y)) :=
    ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hψθ.1,
      ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
        (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hψθ.1) ⟨y₀, hψy⟩⟩
  let ωV : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι w.form, hpull⟩
  refine ⟨hVι, le_antisymm (restrictedVolume_le_restrictedMinimalMass hι ωV θ hVι) ?_⟩
  -- the lower bound for each `s ∈ (0, 1)`
  have hbound : ∀ s : ℝ, 0 < s → s < 1 →
      ENNReal.ofReal (s ^ k) * diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
        (fun y => thetaPshSupremum θ.val (ι y)) hVι ≤ restrictedVolume ι hι θ := by
    intro s hs0 hs1
    set u : X → EReal := ThetaPshConvexCombination.convexComb s (thetaPshSupremum θ.val) ψ
      with hudef
    set d : ℝ := (1 - s) * c with hd
    have hd0 : 0 < d := mul_pos (sub_pos.mpr hs1) hc0
    have hV0 : IsThetaPshPotential (θ - (0 : ℝ) • w.form).val (thetaPshSupremum θ.val) := by
      rwa [zero_smul, sub_zero]
    have hu : IsThetaPshPotential (θ - d • w.form).val u := by
      have h := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul w hs0 hs1 hV0 hψ
      rwa [mul_zero, zero_add] at h
    obtain ⟨v, hqea, hgentle⟩ :=
      SGPT.PSH.exists_sourceGentleQuasiEquisingularApproximation w (θ - d • w.form) hu
    obtain ⟨-, -, hdec, ⟨w', ε, hε, hterm⟩, -⟩ := hqea
    obtain ⟨A', hA', hA'semi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w (-w'.form)
    have hεlim : Tendsto (fun j => ε j * A') atTop (𝓝 0) := by
      simpa only [zero_mul] using hε.2.2.mul_const A'
    obtain ⟨j, hj⟩ := (hεlim.eventually (eventually_le_nhds (half_pos hd0))).exists
    have hvj : IsThetaPshPotential (θ - (d / 2) • w.form).val (v j) := by
      have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive (hterm j)
        (KahlerDomination.isSemipositive_smul hA'semi (hε.1 j))
      have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive h1
        (KahlerDomination.isSemipositive_smul w.isSemipositive (sub_nonneg.mpr hj))
      have he : θ - d • w.form + ε j • w'.form + ε j • (-w'.form + A' • w.form) +
          (d / 2 - ε j * A') • w.form = θ - (d / 2) • w.form := by
        rw [smul_add, smul_neg, smul_smul, sub_smul]
        module
      rwa [he] at h2
    have hvjθ : IsThetaPshPotential θ.val (v j) := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hvj
        (KahlerDomination.isSemipositive_smul w.isSemipositive (half_pos hd0).le)
      rwa [sub_add_cancel] at h
    have hmem : v j ∈ TranscendentalCore.gentleKahlerCurrents θ := by
      refine ⟨⟨hvjθ, _, _, hgentle j⟩, KahlerBackground.smul (half_pos hd0) w, ?_⟩
      rwa [KahlerBackground.smul_form]
    have hge : ∀ x, u x ≤ v j x := fun x => (hdec.1 x).le_of_tendsto (hdec.2 x) j
    have huι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
        (fun y => u (ι y)) :=
      ThetaPshConvexCombination.isThetaPshPotential_convexComb hVι hψι hs0 hs1
    have hvjι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
        (fun y => v j (ι y)) := by
      refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hvjθ.1, ?_⟩
      intro y U hU hyU
      obtain ⟨z, hzU, hz⟩ := huι.2 y U hU hyU
      exact ⟨z, hzU, fun hbot => hz (le_bot_iff.mp (hbot ▸ hge (ι z)))⟩
    have hconv := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
      hVι hψι hs0 hs1 univ
    calc ENNReal.ofReal (s ^ k) * diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
          (fun y => thetaPshSupremum θ.val (ι y)) hVι
        ≤ diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ) (fun y => u (ι y)) huι :=
          hconv
      _ ≤ diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ) (fun y => v j (ι y)) hvjι :=
          diagonalPotentialMass_mono_of_kahler ωV huι hvjι
            (MoreSingularOn.of_le fun y _ => hge (ι y))
      _ ≤ restrictedVolume ι hι θ := by
          unfold restrictedVolume
          exact le_iSup_of_le (v j) (le_iSup_of_le hmem (le_iSup_of_le hvjι le_rfl))
  -- `s → 1`
  have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ k) *
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
        (fun y => thetaPshSupremum θ.val (ι y)) hVι) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ k) *
        diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
          (fun y => thetaPshSupremum θ.val (ι y)) hVι)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr (MixedMass.globalMixedMass_lt_top ωV _).ne)
    exact ((ENNReal.continuous_ofReal.comp (continuous_pow k)).tendsto 1).mono_left
      nhdsWithin_le_nhds
  rw [one_pow, ENNReal.ofReal_one, one_mul] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
  exact hbound s hs.1 hs.2

end Identification

end SGPT.Okounkov.TranscendentalVolumeConcavity
