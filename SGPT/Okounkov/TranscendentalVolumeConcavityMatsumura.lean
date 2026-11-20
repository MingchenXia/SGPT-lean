import SGPT.Okounkov.TranscendentalVolumeConcavityRestricted
import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Trace.TraceMass
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance

/-!
# Matsumura's and Collins--Tosatti's restricted volumes

Source: `chapter_trace.tex`, Section *Relation to the classical restricted volumes*:
`eq:rest_vol_Mat_def` (Matsumura's restricted volume), `eq:rest_vol_CT_def` (the
Collins--Tosatti extension), `prop:restvol_voltrace` and `thm:rest_volume_tr_volume`.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1`, `Y` a connected
submanifold of dimension `k` (formally: a compact connected complex manifold `V` of
dimension `k` with a holomorphic map `ι : V → X` such that `ι^*ω` is Kähler, as in
`SGPT.Trace`), `α = {θ}` big.

* `matsumuraRestrictedVolume` (`eq:rest_vol_Mat_def`):
  `vol_{X|Y}(α) = sup_φ ∫_Y (θ|_Y + dd^c φ|_Y)^k` over `φ ∈ PSH(X, θ)` with analytic
  singularities (`TranscendentalCore.analyticCurrents`, the book's `def:neatanasing`) such
  that `φ|_Y ≢ -∞` (formally: `φ ∘ ι` is a genuine `ι^*θ`-psh potential; for connected `Y`
  this is `φ|_Y ≢ -∞`, `isThetaPshPotential_comp_iff_exists_ne_bot`). It is independent of
  `θ` (`matsumuraRestrictedVolume_eq_of_class_eq`).
* `collinsTosattiRestrictedVolume` (`eq:rest_vol_CT_def`):
  `vol_{X|Y}(α) = lim_{ε ↘ 0} sup_φ ∫_Y (θ|_Y + εω|_Y + dd^c φ|_Y)^k`, `φ ∈ PSH(X, θ + εω)`; the
  limit exists (`tendsto_collinsTosattiRestrictedVolume`: the supremum is monotone in `ε`) and
  is independent of `θ`.
* `restvol_voltrace` (**`prop:restvol_voltrace`**, both equalities): if `Y ⊄ nK(α)`,
  `vol_{X|Y}(α) = ∫_Y (θ|_Y + dd^c Tr^θ_Y(V_θ))^k = ∫_Y (θ|_Y + dd^c V_θ|_Y)^k`.
  The new point is the first equality; the second is `SGPT.Trace.sourceTraceMass_minimal_eq_restriction_mass`.
  Proof of the first: `≤` by `φ ≤ V_θ + C` and monotonicity on `Y`; `≥` because the DRWNXZ
  restricted volume (over `Ω(α) ⊆ 𝒜(α)`) already equals `∫_Y ⟨(θ|_Y + dd^c V_θ|_Y)^k⟩`
  (`restrictedVolume_eq_restrictedMinimalMass`). In particular Matsumura's continuity
  `[Mat13, Cor. 4.11]`, cited by the book's proof, is not used.
* `rest_volume_tr_volume` (**`thm:rest_volume_tr_volume`**): if `Y ⊄ nn(α)`, the
  Collins--Tosatti restricted volume equals `∫_Y (θ|_Y + dd^c Tr^θ_Y(V_θ))^k`; together with
  `SGPT.Trace.tendsto_restriction_minimal_mass` and
  `SGPT.Trace.tendsto_sourceTraceMass_minimal_add_smul_right` all four terms of the theorem
  agree.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalVolumeConcavity

open Set Filter MeasureTheory
open scoped ENNReal Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass

section Basic

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

/-- **Source `eq:rest_vol_Mat_def`** (Matsumura's restricted volume `vol_{X|Y}(α)`, `α = {θ}`):
the supremum of `∫_Y (θ|_Y + dd^c φ|_Y)^k` over `φ ∈ PSH(X, θ)` with analytic singularities
whose restriction to `Y` is not identically `-∞`. -/
def matsumuraRestrictedVolume (ι : V → X)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n X) : ℝ≥0∞ :=
  ⨆ (φ : X → EReal) (_ : φ ∈ TranscendentalCore.analyticCurrents θ)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y))),
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ) (fun y => φ (ι y)) hw

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
include hι in
/-- For a connected `Y`, the index condition "`φ ∘ ι` is a genuine `ι^*θ`-psh potential" is the
book's `φ|_Y ≢ -∞`. -/
theorem isThetaPshPotential_comp_iff_exists_ne_bot [ConnectedSpace V]
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y)) ↔
      ∃ y : V, φ (ι y) ≠ ⊥ := by
  constructor
  · intro h
    obtain ⟨y⟩ := (inferInstance : Nonempty V)
    obtain ⟨z, -, hz⟩ := h.2 y univ isOpen_univ (mem_univ y)
    exact ⟨z, hz⟩
  · intro h
    exact ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1,
      ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
        (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1) h⟩

include hι in
/-- One inequality of the representative independence of `eq:rest_vol_Mat_def`. -/
theorem matsumuraRestrictedVolume_le_of_bottChernRel {θ θ' : ClosedRealOneOneForm n X}
    (hrel : ClosedRealOneOneForm.BottChernRel θ θ') :
    matsumuraRestrictedVolume ι hι θ ≤ matsumuraRestrictedVolume ι hι θ' := by
  obtain ⟨g, hg, heq⟩ := hrel
  unfold matsumuraRestrictedVolume
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hw => ?_
  have hφ' := TranscendentalCore.sub_mem_analyticCurrents hg heq hφ
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
/-- **`eq:rest_vol_Mat_def`, well-definedness**: Matsumura's restricted volume is independent
of the choice of `θ` in `α`. -/
theorem matsumuraRestrictedVolume_eq_of_class_eq {θ θ' : ClosedRealOneOneForm n X}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    matsumuraRestrictedVolume ι hι θ = matsumuraRestrictedVolume ι hι θ' := by
  have hrel := (RealBottChern.ofRepresentative_eq_iff θ θ').mp h
  exact le_antisymm (matsumuraRestrictedVolume_le_of_bottChernRel hι hrel)
    (matsumuraRestrictedVolume_le_of_bottChernRel hι (ClosedRealOneOneForm.BottChernRel.symm hrel))

omit [BorelSpace V] in
include hι in
/-- The DRWNXZ restricted volume (over `Ω(α)`) is at most Matsumura's (over `𝒜(α) ⊇ Ω(α)`). -/
theorem restrictedVolume_le_matsumuraRestrictedVolume (θ : ClosedRealOneOneForm n X) :
    restrictedVolume ι hι θ ≤ matsumuraRestrictedVolume ι hι θ := by
  unfold restrictedVolume matsumuraRestrictedVolume
  exact iSup_le fun φ => iSup_le fun hφ => iSup_le fun hw =>
    le_iSup_of_le φ (le_iSup_of_le (TranscendentalCore.gentleCurrents_subset_analyticCurrents θ
      hφ.1) (le_iSup_of_le hw le_rfl))

include hι in
/-- Matsumura's restricted volume is at most `∫_Y (θ|_Y + dd^c V_θ|_Y)^k`. -/
theorem matsumuraRestrictedVolume_le_restrictedMinimalMass [CompactSpace X] [Nonempty X]
    (ωV : KahlerBackground k V) (θ : ClosedRealOneOneForm n X)
    (hV : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => thetaPshSupremum θ.val (ι y))) :
    matsumuraRestrictedVolume ι hι θ ≤
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
        (fun y => thetaPshSupremum θ.val (ι y)) hV := by
  unfold matsumuraRestrictedVolume
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hw => ?_
  have hφ' : IsThetaPshPotential θ.val φ := hφ.1
  obtain ⟨C, hC⟩ := FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    hφ'.1.hasSmoothLocalPotentials ⟨_, hφ'⟩ φ hφ'
  exact diagonalPotentialMass_mono_of_kahler ωV hw hV ⟨C, fun y _ => hC (ι y) (mem_univ _)⟩

/-! ### Monotonicity in `ε` and the Collins--Tosatti limit -/

include hι in
/-- `ε ↦ vol^{Mat}_{X|Y}(θ + εω)` is monotone. -/
theorem monotone_matsumuraRestrictedVolume_add_smul [CompactSpace X]
    (w : KahlerBackground n X) (θ : ClosedRealOneOneForm n X) :
    Monotone (fun ε : ℝ => matsumuraRestrictedVolume ι hι (θ + ε • w.form)) := by
  intro ε ε' hεε'
  rcases hεε'.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hc : 0 < ε' - ε := sub_pos.mpr hlt
  have hform : θ + ε • w.form + (ε' - ε) • w.form = θ + ε' • w.form := by module
  simp only
  unfold matsumuraRestrictedVolume
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hw => ?_
  have hφ' : φ ∈ TranscendentalCore.analyticCurrents (θ + ε' • w.form) := by
    refine ⟨?_, hφ.2⟩
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ.1
      (KahlerDomination.isSemipositive_smul w.isSemipositive hc.le)
    rwa [hform] at h
  have hgeo := ModificationInputs.pullback_add_smul_geometricallyEq hι (θ + ε • w.form) w.form
    (ε' - ε)
  rw [hform] at hgeo
  have hw' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + ε' • w.form)).val
      (fun y => φ (ι y)) :=
    ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ'.1.1, hw.2⟩
  have hw'' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + ε • w.form) +
      (ε' - ε) • ClosedRealOneOneForm.pullback hι w.form).val (fun y => φ (ι y)) :=
    ⟨(hgeo.thetaPlurisubharmonic_iff _).mp hw'.1, hw.2⟩
  have hbg := AmbientMassBackgroundMonotone.globalMixedMeasure_diagonal_le_add_smul
    (ClosedRealOneOneForm.pullback_isSemipositive hι w.isSemipositive) hc hw hw''.1
  have hcongr := ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq
    hgeo hw' hw''
  refine le_iSup_of_le φ (le_iSup_of_le hφ' (le_iSup_of_le hw' ?_))
  rw [hcongr]
  exact Measure.le_iff'.mp hbg univ

/-- **Source `eq:rest_vol_CT_def`** (the Collins--Tosatti restricted volume):
`vol_{X|Y}(α) = lim_{ε ↘ 0} vol^{Mat}_{X|Y}(α + ε{ω})`, i.e. the limit of
`sup_φ ∫_Y (θ|_Y + εω|_Y + dd^c φ|_Y)^k` over `φ ∈ PSH(X, θ + εω)` with analytic singularities and
`φ|_Y ≢ -∞`. The limit exists (`tendsto_collinsTosattiRestrictedVolume`). -/
def collinsTosattiRestrictedVolume (w : KahlerBackground n X) (ι : V → X)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n X) : ℝ≥0∞ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => matsumuraRestrictedVolume ι hι (θ + ε • w.form))

include hι in
/-- **`eq:rest_vol_CT_def`, existence of the limit.** -/
theorem tendsto_collinsTosattiRestrictedVolume [CompactSpace X] (w : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) :
    Tendsto (fun ε : ℝ => matsumuraRestrictedVolume ι hι (θ + ε • w.form)) (𝓝[>] 0)
      (𝓝 (collinsTosattiRestrictedVolume w ι hι θ)) := by
  have h := (monotone_matsumuraRestrictedVolume_add_smul hι w θ).tendsto_nhdsGT 0
  unfold collinsTosattiRestrictedVolume
  rwa [h.limUnder_eq]

include hι in
/-- **`eq:rest_vol_CT_def`, well-definedness**: independence of the choice of `θ`. -/
theorem collinsTosattiRestrictedVolume_eq_of_class_eq (w : KahlerBackground n X)
    {θ θ' : ClosedRealOneOneForm n X}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    collinsTosattiRestrictedVolume w ι hι θ = collinsTosattiRestrictedVolume w ι hι θ' := by
  unfold collinsTosattiRestrictedVolume
  congr 1
  funext ε
  apply matsumuraRestrictedVolume_eq_of_class_eq hι
  rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_add, h]

end Basic

/-! ### The book's comparison theorems -/

section Comparison

variable {m k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ι)

include hι in
/-- Matsumura's restricted volume of a big class is `∫_Y (θ|_Y + dd^c V_θ|_Y)^k` when
`Y ⊄ nK(α)`. -/
theorem matsumuraRestrictedVolume_eq_restrictedMinimalMass (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    ∃ hV : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
        (fun y => thetaPshSupremum θ.val (ι y)),
      matsumuraRestrictedVolume ι hι θ =
        diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
          (fun y => thetaPshSupremum θ.val (ι y)) hV := by
  obtain ⟨hV, heq⟩ := restrictedVolume_eq_restrictedMinimalMass hι w hpull θ hbig hZ
  refine ⟨hV, le_antisymm
    (matsumuraRestrictedVolume_le_restrictedMinimalMass hι ⟨_, hpull⟩ θ hV) ?_⟩
  rw [← heq]
  exact restrictedVolume_le_matsumuraRestrictedVolume hι θ

include hι in
/-- **Source `prop:restvol_voltrace`** (both equalities): for a big class `α = {θ}` and a
connected submanifold `Y ⊄ nK(α)`, `Tr^θ_Y(V_θ)` is defined and
`vol_{X|Y}(α) = ∫_Y (θ|_Y + dd^c Tr^θ_Y(V_θ))^k = ∫_Y (θ|_Y + dd^c V_θ|_Y)^k`, with Matsumura's
restricted volume `vol_{X|Y}` (`eq:rest_vol_Mat_def`). -/
theorem restvol_voltrace (hk : k ≤ m + 1) (omega : KahlerBackground (m + 1) X)
    (omegaV : KahlerBackground k V)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hx : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    Trace.HasPositiveSourceTraceAlong omega omegaV hι θ (thetaPshSupremum θ.val) ∧
      ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
          (fun y => thetaPshSupremum θ.val (ι y)),
        matsumuraRestrictedVolume ι hι θ =
            Trace.sourceTraceMass omega omegaV hι θ (thetaPshSupremum θ.val) ∧
          Trace.sourceTraceMass omega omegaV hι θ (thetaPshSupremum θ.val) =
            diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
              (fun y => thetaPshSupremum θ.val (ι y)) hw := by
  obtain ⟨hdef, hw, htr⟩ := Trace.sourceTraceMass_minimal_eq_restriction_mass hk
    (Nat.succ_ne_zero m) omega omegaV hι hpull θ hx
  obtain ⟨hV, hmat⟩ := matsumuraRestrictedVolume_eq_restrictedMinimalMass hι omega hpull θ hbig hx
  exact ⟨hdef, hw, hmat.trans htr.symm, htr⟩

include hι in
/-- **Source `thm:rest_volume_tr_volume`**, first term: for a big class `α = {θ}` and a connected
submanifold `Y ⊄ nn(α)`, for every `ε > 0` the Collins--Tosatti supremum at `ε` equals
`∫_Y (θ|_Y + εω|_Y + dd^c Tr^{θ+εω}_Y(V_{θ+εω}))^k`, and the Collins--Tosatti restricted volume
(`eq:rest_vol_CT_def`) equals `∫_Y (θ|_Y + dd^c Tr^θ_Y(V_θ))^k` (the limit of the latter
quantities, `SGPT.Trace.tendsto_sourceTraceMass_minimal_add_smul_right`; the second term is
`SGPT.Trace.tendsto_restriction_minimal_mass`). -/
theorem rest_volume_tr_volume [MeasurableSpace X] [BorelSpace X] (hk : k ≤ m + 1) (omega : KahlerBackground (m + 1) X)
    (omegaV : KahlerBackground k V)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hx : ∃ y : V, ι y ∉ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    (∀ ε : ℝ, 0 < ε → matsumuraRestrictedVolume ι hι (θ + ε • omega.form) =
        Trace.sourceTraceMass omega omegaV hι (θ + ε • omega.form)
          (thetaPshSupremum (θ + ε • omega.form).val)) ∧
      collinsTosattiRestrictedVolume omega ι hι θ =
        Trace.sourceTraceMass omega omegaV hι θ (thetaPshSupremum θ.val) := by
  obtain ⟨y, hy⟩ := hx
  have hpoint : ∀ ε : ℝ, 0 < ε → matsumuraRestrictedVolume ι hι (θ + ε • omega.form) =
      Trace.sourceTraceMass omega omegaV hι (θ + ε • omega.form)
        (thetaPshSupremum (θ + ε • omega.form).val) := by
    intro ε hε
    obtain ⟨K⟩ := hbig
    have hbigε : IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)) := by
      rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
      exact ⟨K.addSmulKahler omega hε⟩
    have hyε : ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative (θ + ε • omega.form)) := by
      intro hmem
      apply hy
      rw [mem_nonNefLocus]
      refine ⟨⟨ε, hε⟩, ?_⟩
      rwa [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul] at hmem
    obtain ⟨-, -, h1, -⟩ := restvol_voltrace hι hk omega omegaV hpull (θ + ε • omega.form)
      hbigε ⟨y, hyε⟩
    exact h1
  refine ⟨hpoint, ?_⟩
  have hlim := Trace.tendsto_sourceTraceMass_minimal_add_smul_right hk (Nat.succ_ne_zero m)
    omega omegaV hι hpull θ hbig ⟨y, hy⟩
  have hlim' : Tendsto (fun ε : ℝ => matsumuraRestrictedVolume ι hι (θ + ε • omega.form))
      (𝓝[>] 0) (𝓝 (Trace.sourceTraceMass omega omegaV hι θ (thetaPshSupremum θ.val))) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hpoint ε hε).symm
  exact tendsto_nhds_unique (tendsto_collinsTosattiRestrictedVolume hι omega θ) hlim'

end Comparison

end SGPT.Okounkov.TranscendentalVolumeConcavity
