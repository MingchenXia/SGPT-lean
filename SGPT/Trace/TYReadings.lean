import SGPT.Trace.TYDescentInterface

/-!
# Pluripotential notions on the normalization `Ỹ`, and their readings on resolutions

Source: `appendix_unibranch.tex`, `def:unibranch:L105` (`θ`-psh functions on complex spaces),
`cor:PSH`, Section `sec:unib_ext` ("The non-pluripolar products can be defined exactly as in
`chap:npp` ... The definition of the `P`-envelope remains unchanged", and `def:unibranch:L212` for
the `𝓘`-envelope), used on the normalization `Ỹ` of `Y` by `chapter_trace.tex`.

For `T : TildeY Y` (the normalization `Ỹ`):

* `IsQPSH`: `QPSH(Ỹ)`, intrinsic (`def:unibranch:L105`).
* `pEnvelope θ̃ ψ`: the `P`-envelope `P_θ̃[ψ]` on `Ỹ`, by the same formula as on manifolds (the
  upper semicontinuous regularization of the supremum of the `θ̃`-psh `u ≤ 0` with `u ≤ ψ + C`),
  intrinsic. With `cor:PSH` its reading on a resolution is the `P`-envelope there
  (`pEnvelope_comp`), and it is `θ|_Ỹ`-psh.
* `IsIEnvelope θ ψ ψ'`: `def:unibranch:L212` for `θ|_Ỹ`: `ψ'` is `θ|_Ỹ`-psh and
  `ν^*ψ' = P_{ν^*θ}[ν^*ψ]_𝓘` for every resolution `ν` of `Ỹ`.
* `mass θ ψ = ∫_Ỹ (θ|_Ỹ + dd^c ψ)^{dim Y}`: the non-pluripolar mass, read on a resolution (the
  non-pluripolar product on `Ỹ` is that of a resolution); independent of the resolution
  (`mass_eq`).
* `POrder`, `PEquivalent`, `IGood`: `⪯_P`, `∼_P` and `𝓘`-goodness on `Ỹ`, read on every
  resolution of `Ỹ` (these notions are defined from envelopes and non-pluripolar masses, hence
  are those of a resolution; they are bimeromorphically invariant, `lma:Ipartorderinv`).
* `DistTendstoZero`, `TendstoDS`: `d_S`-convergence on `Ỹ`, read on every resolution, for every
  big background containing the readings (`d_S` on `Ỹ` is defined from non-pluripolar masses).
* `IsTraceOn N φ τ`: the trace predicate read on the resolution `N` (`def:traceop` on a
  resolution target, `IsSourceTraceRepresentativeAlong`); `transfer` moves it between
  resolutions of `Ỹ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
  SGPT.Trace.Trace2Resolution SGPT.Unibranch

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

namespace TildeY

variable {T : TildeY Y}

/-! ### Quasi-psh functions on `Ỹ` -/

/-- `QPSH(Ỹ)` (`def:unibranch:L105`): `ψ` is `θ̃`-psh for some smooth closed real `(1,1)`-form
`θ̃` on `Ỹ`. -/
def IsQPSH (T : TildeY Y) (ψ : T.space.obj.left → EReal) : Prop :=
  ∃ θ : SpaceForm T.space 2, θ.IsClosed ∧ θ.IsOneOne ∧ T.space.IsThetaPSH θ ψ

theorem isQPSH_of_isThetaPSH {θ : ClosedRealOneOneForm n X} {ψ : T.space.obj.left → EReal}
    (h : T.space.IsThetaPSH (T.restrict θ) ψ) : T.IsQPSH ψ :=
  ⟨T.restrict θ, T.restrict_isClosed θ, T.restrict_isOneOne θ, h⟩

/-- `cor:PSH`, forward direction, as a reading statement. -/
theorem CorPSH.comp {N : T.Resolution} (h : T.CorPSH N) {θ : ClosedRealOneOneForm n X}
    {ψ : T.space.obj.left → EReal} (hψ : T.space.IsThetaPSH (T.restrict θ) ψ) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν) :=
  (h θ).1 ψ hψ

/-- `cor:PSH`, descent. -/
theorem CorPSH.descend {N : T.Resolution} (h : T.CorPSH N) {θ : ClosedRealOneOneForm n X}
    {w : N.R.V → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val w) :
    ∃ ψ : T.space.obj.left → EReal, T.space.IsThetaPSH (T.restrict θ) ψ ∧ ψ ∘ N.ν = w :=
  (h θ).2 w hw

/-! ### Upper semicontinuity descends along a resolution -/

/-- If `w ∘ ν` is upper semicontinuous for a resolution `ν : V → Ỹ`, so is `w` (`ν` is a
continuous closed surjection from a compact space). -/
theorem Resolution.upperSemicontinuous_of_comp (N : T.Resolution)
    {w : T.space.obj.left → EReal} (h : UpperSemicontinuous (w ∘ N.ν)) :
    UpperSemicontinuous w := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  have hc : IsClosed ((w ∘ N.ν) ⁻¹' Ici c) := h.isClosed_preimage c
  have himage : w ⁻¹' Ici c = N.ν '' ((w ∘ N.ν) ⁻¹' Ici c) := by
    ext y
    constructor
    · intro hy
      obtain ⟨v, rfl⟩ := N.surjective y
      exact ⟨v, hy, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [himage]
  exact (hc.isCompact.image N.continuous).isClosed

/-! ### The `P`-envelope on `Ỹ` -/

/-- **The `P`-envelope on `Ỹ`** (`sec:unib_ext`: "the definition of the `P`-envelope remains
unchanged"): `P_θ̃[ψ]` is the upper semicontinuous regularization of the supremum of the `θ̃`-psh
functions `u ≤ 0` on `Ỹ` with `u ≤ ψ + C` for some constant `C` (the formula of
`singularityEnvelope`). -/
def pEnvelope (T : TildeY Y) (θ : SpaceForm T.space 2) (ψ : T.space.obj.left → EReal) :
    T.space.obj.left → EReal :=
  uscRegularization (sSup {u | T.space.IsThetaPSH θ u ∧ u ≤ 0 ∧ MoreSingularOn u ψ univ})

/-- **The `P`-envelope on `Ỹ` read on a resolution** (`cor:PSH`): for `ψ` on `Ỹ` whose reading
`ψ ∘ ν` is `ι^*θ`-psh, `P_{θ|_Ỹ}[ψ] ∘ ν = P_{ι^*θ}[ψ ∘ ν]`, and `P_{θ|_Ỹ}[ψ]` is `θ|_Ỹ`-psh. -/
theorem pEnvelope_comp {N : T.Resolution} (hcor : T.CorPSH N) (θ : ClosedRealOneOneForm n X)
    {ψ : T.space.obj.left → EReal}
    (hψ : IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν)) :
    T.pEnvelope (T.restrict θ) ψ ∘ N.ν =
        singularityEnvelope (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν) ∧
      T.space.IsThetaPSH (T.restrict θ) (T.pEnvelope (T.restrict θ) ψ) := by
  set η := ClosedRealOneOneForm.pullback N.R.contMDiff θ with hη
  have hP : IsThetaPshPotential η.val (singularityEnvelope η.val (ψ ∘ N.ν)) :=
    FirstPass.singularityEnvelope_isThetaPshPotential η.val η.property.1 η.property.2
      hψ.1.hasSmoothLocalPotentials _ hψ
  obtain ⟨w, hw, hwν⟩ := hcor.descend hP
  have hwusc : UpperSemicontinuous w := by
    apply N.upperSemicontinuous_of_comp
    rw [hwν]
    exact upperSemicontinuous_uscRegularization _
  have hle : T.pEnvelope (T.restrict θ) ψ ≤ w := by
    apply uscRegularization_le hwusc
    refine sSup_le fun u hu => ?_
    obtain ⟨hu, hu0, C, hC⟩ := hu
    apply N.le_of_comp_le
    intro v
    have huν : IsThetaPshPotential η.val (u ∘ N.ν) := hcor.comp hu
    have hmem : u ∘ N.ν ∈ singularityCompetitors η.val (ψ ∘ N.ν) :=
      ⟨⟨huν, fun v => hu0 (N.ν v)⟩, C, fun v _ => hC (N.ν v) trivial⟩
    have h1 : u ∘ N.ν ≤ singularitySupremum η.val (ψ ∘ N.ν) := le_sSup hmem
    have h2 := le_uscRegularization (singularitySupremum η.val (ψ ∘ N.ν))
    have h3 : (w ∘ N.ν) v = singularityEnvelope η.val (ψ ∘ N.ν) v := congrFun hwν v
    calc u (N.ν v) = (u ∘ N.ν) v := rfl
      _ ≤ uscRegularization (singularitySupremum η.val (ψ ∘ N.ν)) v := (h1.trans h2) v
      _ = w (N.ν v) := h3.symm
  have hge : w ≤ T.pEnvelope (T.restrict θ) ψ := by
    apply N.le_of_comp_le
    have hg : UpperSemicontinuous (T.pEnvelope (T.restrict θ) ψ ∘ N.ν) :=
      (upperSemicontinuous_uscRegularization _).comp N.continuous
    have hbound : singularityEnvelope η.val (ψ ∘ N.ν) ≤ T.pEnvelope (T.restrict θ) ψ ∘ N.ν := by
      apply uscRegularization_le hg
      refine sSup_le fun u' hu' => ?_
      obtain ⟨⟨hu', hu'0⟩, C, hC⟩ := hu'
      obtain ⟨u, hu, rfl⟩ := hcor.descend hu'
      have hu0 : u ≤ 0 := N.le_of_comp_le fun v => hu'0 v
      have hmem : u ∈ {u | T.space.IsThetaPSH (T.restrict θ) u ∧ u ≤ 0 ∧
          MoreSingularOn u ψ univ} := by
        refine ⟨hu, hu0, C, fun y _ => ?_⟩
        obtain ⟨v, rfl⟩ := N.surjective y
        exact hC v trivial
      intro v
      exact ((le_sSup hmem).trans (le_uscRegularization _)) (N.ν v)
    intro v
    have h3 : (w ∘ N.ν) v = singularityEnvelope η.val (ψ ∘ N.ν) v := congrFun hwν v
    calc w (N.ν v) = singularityEnvelope η.val (ψ ∘ N.ν) v := h3
      _ ≤ (T.pEnvelope (T.restrict θ) ψ ∘ N.ν) v := hbound v
  have heq : T.pEnvelope (T.restrict θ) ψ = w := le_antisymm hle hge
  rw [heq]
  exact ⟨hwν, hw⟩

/-- **The `𝓘`-envelope on `Ỹ`** (`def:unibranch:L212` for the background `θ|_Ỹ`): `ψ'` is
`θ|_Ỹ`-psh and its reading on every resolution `ν : V → Ỹ` is the `𝓘`-envelope
`P_{ι^*θ}[ψ ∘ ν]_𝓘` of the reading of `ψ`. -/
def IsIEnvelope (T : TildeY Y) (θ : ClosedRealOneOneForm n X)
    (ψ ψ' : T.space.obj.left → EReal) : Prop :=
  T.space.IsThetaPSH (T.restrict θ) ψ' ∧
    ∀ N : T.Resolution, ψ' ∘ N.ν =
      IEnvelope.iSingularityEnvelope (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val
        (ψ ∘ N.ν)

/-- The `𝓘`-envelope on `Ỹ` is unique. -/
theorem IsIEnvelope.unique {θ : ClosedRealOneOneForm n X} {ψ ψ₁ ψ₂ : T.space.obj.left → EReal}
    (h₁ : T.IsIEnvelope θ ψ ψ₁) (h₂ : T.IsIEnvelope θ ψ ψ₂) : ψ₁ = ψ₂ := by
  obtain ⟨N⟩ := T.nonempty_resolution
  exact N.comp_injective ((h₁.2 N).trans (h₂.2 N).symm)

/-! ### Comparing two resolutions -/

section Compare

variable [CompactSpace X]

omit [CompactSpace X] in
private theorem pullback_dominates_geometricallyEq (R₁ R₂ : ResolutionTarget Y)
    {p : R₂.V → R₁.V} (hp : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel Y.dim) ∞ p)
    (hcomm : ∀ w, R₂.ι w = R₁.ι (p w)) (θ : ClosedRealOneOneForm n X) :
    (ClosedRealOneOneForm.pullback hp
      (ClosedRealOneOneForm.pullback R₁.contMDiff θ)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback R₂.contMDiff θ).val := by
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    ClosedRealOneOneForm.pullback_val]
  have h₁ := SGPT.Okounkov.TranscendentalVolId.pullback_comp_geometricallyEq' R₁.contMDiff hp θ.val
  have hf : R₁.ι ∘ p = R₂.ι := funext fun w => (hcomm w).symm
  have h₃ : ∀ (f g : R₂.V → X), f = g →
      ∀ (hf' : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) ∞ f)
        (hg' : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) ∞ g),
      (SmoothRealForm.pullback hf' θ.val).GeometricallyEq (SmoothRealForm.pullback hg' θ.val) := by
    rintro f g rfl hf' hg'
    exact SmoothRealForm.GeometricallyEq.refl _
  exact h₁.symm.trans (h₃ _ _ hf _ R₂.contMDiff)

omit [CompactSpace X] in
private theorem mass_congr {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] [MeasurableSpace V] [CompactSpace V]
    {η : ClosedRealOneOneForm k V} {a b : V → EReal}
    (ha : IsThetaPshPotential η.val a) (hb : IsThetaPshPotential η.val b) (hab : a = b) :
    diagonalPotentialMass η a ha = diagonalPotentialMass η b hb := by
  subst hab
  rfl

omit [CompactSpace X] in
/-- Reading along a dominating resolution: if `p : V₂ → V₁` is a modification with
`ι₂ = ι₁ ∘ p` and `w` is `ι₁^*θ`-psh, then `w ∘ p` is `ι₂^*θ`-psh with the same mass. -/
private theorem reading_comp (R₁ R₂ : ResolutionTarget Y) {p : R₂.V → R₁.V}
    (hp : IsAnalyticModification (n := Y.dim) p) (hcomm : ∀ w, R₂.ι w = R₁.ι (p w))
    (θ : ClosedRealOneOneForm n X) {w : R₁.V → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback R₁.contMDiff θ).val w) :
    ∃ hw₂ : IsThetaPshPotential (ClosedRealOneOneForm.pullback R₂.contMDiff θ).val (w ∘ p),
      diagonalPotentialMass (ClosedRealOneOneForm.pullback R₂.contMDiff θ) (w ∘ p) hw₂ =
        diagonalPotentialMass (ClosedRealOneOneForm.pullback R₁.contMDiff θ) w hw := by
  have hgeo := pullback_dominates_geometricallyEq R₁ R₂ hp.1 hcomm θ
  have hwp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hp (ClosedRealOneOneForm.pullback R₁.contMDiff θ) hw
  have hw₂ : IsThetaPshPotential (ClosedRealOneOneForm.pullback R₂.contMDiff θ).val (w ∘ p) :=
    (hgeo.thetaPshPotential_iff _).mp hwp
  exact ⟨hw₂,
    (ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hgeo hwp hw₂).symm.trans
      (AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification hp _
        hw)⟩

omit [CompactSpace X] in
/-- **The mass read on two resolutions of `Ỹ` agrees.** -/
theorem mass_reading_eq (N₁ N₂ : T.Resolution) (θ : ClosedRealOneOneForm n X)
    {ψ : T.space.obj.left → EReal}
    (h₁ : IsThetaPshPotential (ClosedRealOneOneForm.pullback N₁.R.contMDiff θ).val (ψ ∘ N₁.ν))
    (h₂ : IsThetaPshPotential (ClosedRealOneOneForm.pullback N₂.R.contMDiff θ).val (ψ ∘ N₂.ν)) :
    diagonalPotentialMass (ClosedRealOneOneForm.pullback N₁.R.contMDiff θ) (ψ ∘ N₁.ν) h₁ =
      diagonalPotentialMass (ClosedRealOneOneForm.pullback N₂.R.contMDiff θ) (ψ ∘ N₂.ν) h₂ := by
  obtain ⟨N₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂, hν₁, hν₂⟩ := Resolution.exists_common N₁ N₂
  obtain ⟨h₃, hm₁⟩ := reading_comp N₁.R N₃.R hp₁ hc₁ θ h₁
  obtain ⟨h₃', hm₂⟩ := reading_comp N₂.R N₃.R hp₂ hc₂ θ h₂
  have heq : (ψ ∘ N₁.ν) ∘ p₁ = (ψ ∘ N₂.ν) ∘ p₂ := by
    rw [Function.comp_assoc, Function.comp_assoc, ← hν₁, ← hν₂]
  rw [← hm₁, ← hm₂]
  exact mass_congr h₃ h₃' heq

omit [CompactSpace X] in
/-- **The forward half of `cor:PSH` for one resolution of `Ỹ` gives it for every resolution**
(common resolutions, pull-back along modifications and `prop:PSHpullbij` for manifolds). -/
theorem CorPSHForward.of_resolution {N₀ : T.Resolution} (h₀ : T.CorPSHForward N₀)
    (N : T.Resolution) : T.CorPSHForward N := by
  intro θ ψ hψ
  obtain ⟨N₃, p₀, p, hp₀, hp, hc₀, hc, hν₀, hν⟩ := Resolution.exists_common N₀ N
  have hsurj : Function.Surjective p :=
    SGPT.PSH.RIsoACommonModel.surjective_of_isAnalyticModification hp
  obtain ⟨h₃, -⟩ := reading_comp N₀.R N₃.R hp₀ hc₀ θ (h₀ θ ψ hψ)
  have heq : (ψ ∘ N₀.ν) ∘ p₀ = (ψ ∘ N.ν) ∘ p := by
    rw [Function.comp_assoc, Function.comp_assoc, ← hν₀, ← hν]
  rw [heq] at h₃
  have hgeo := pullback_dominates_geometricallyEq N.R N₃.R hp.1 hc θ
  have h₃' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hp.1
      (ClosedRealOneOneForm.pullback N.R.contMDiff θ)).val ((ψ ∘ N.ν) ∘ p) :=
    (hgeo.thetaPshPotential_iff _).mpr h₃
  obtain ⟨w, hw, hwp⟩ :=
    AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hp
      (ClosedRealOneOneForm.pullback N.R.contMDiff θ) h₃'
  have hwψ : w = ψ ∘ N.ν := hsurj.injective_comp_right (funext hwp)
  rw [← hwψ]
  exact hw

/-- **`cor:PSH` for one resolution of `Ỹ` gives it for every resolution of `Ỹ`** (common
resolutions, and `cor:PSH` for modifications of manifolds, `prop:PSHpullbij`). -/
theorem CorPSH.of_resolution {N₀ : T.Resolution} (h₀ : T.CorPSH N₀) (N : T.Resolution) :
    T.CorPSH N := by
  intro θ
  obtain ⟨N₃, p₀, p, hp₀, hp, hc₀, hc, hν₀, hν⟩ := Resolution.exists_common N₀ N
  have hsurj : Function.Surjective p := SGPT.PSH.RIsoACommonModel.surjective_of_isAnalyticModification hp
  constructor
  · intro ψ hψ
    obtain ⟨h₃, -⟩ := reading_comp N₀.R N₃.R hp₀ hc₀ θ (h₀.comp hψ)
    have heq : (ψ ∘ N₀.ν) ∘ p₀ = (ψ ∘ N.ν) ∘ p := by
      rw [Function.comp_assoc, Function.comp_assoc, ← hν₀, ← hν]
    rw [heq] at h₃
    have hgeo := pullback_dominates_geometricallyEq N.R N₃.R hp.1 hc θ
    have h₃' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hp.1
        (ClosedRealOneOneForm.pullback N.R.contMDiff θ)).val ((ψ ∘ N.ν) ∘ p) :=
      (hgeo.thetaPshPotential_iff _).mpr h₃
    obtain ⟨w, hw, hwp⟩ :=
      AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hp
        (ClosedRealOneOneForm.pullback N.R.contMDiff θ) h₃'
    have hwψ : w = ψ ∘ N.ν := hsurj.injective_comp_right (funext hwp)
    rw [← hwψ]
    exact hw
  · intro w hw
    obtain ⟨h₃, -⟩ := reading_comp N.R N₃.R hp hc θ hw
    have hgeo₀ := pullback_dominates_geometricallyEq N₀.R N₃.R hp₀.1 hc₀ θ
    have h₃' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hp₀.1
        (ClosedRealOneOneForm.pullback N₀.R.contMDiff θ)).val (w ∘ p) :=
      (hgeo₀.thetaPshPotential_iff _).mpr h₃
    obtain ⟨w₀, hw₀, hw₀p⟩ :=
      AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hp₀
        (ClosedRealOneOneForm.pullback N₀.R.contMDiff θ) h₃'
    obtain ⟨ψ, hψ, hψw₀⟩ := h₀.descend hw₀
    refine ⟨ψ, hψ, hsurj.injective_comp_right ?_⟩
    change ψ ∘ N.ν ∘ p = w ∘ p
    rw [← hν, hν₀]
    funext y
    change (ψ ∘ N₀.ν) (p₀ y) = w (p y)
    rw [hψw₀]
    exact hw₀p y

/-- `cor:PSH` for one resolution of `Ỹ`, for all of them. -/
theorem corPSH_forall_of_one {N₀ : T.Resolution} (h₀ : T.CorPSH N₀) :
    ∀ N : T.Resolution, T.CorPSH N :=
  fun N => h₀.of_resolution N

end Compare

/-! ### Non-pluripolar masses on `Ỹ` -/

/-- **The non-pluripolar mass `∫_Ỹ (θ|_Ỹ + dd^c ψ)^{dim Y}`** (`sec:unib_ext`, `chap:npp` on
`Ỹ`), read on the resolutions of `Ỹ` on which `ψ` reads as an `ι^*θ`-psh function (by
`mass_eq` all these readings agree; `0` if there is none). -/
def mass (T : TildeY Y) (θ : ClosedRealOneOneForm n X) (ψ : T.space.obj.left → EReal) :
    ℝ≥0∞ :=
  ⨆ (N : T.Resolution)
    (h : IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν)),
    diagonalPotentialMass (ClosedRealOneOneForm.pullback N.R.contMDiff θ) (ψ ∘ N.ν) h

/-- **The mass on `Ỹ` is the mass of the reading on any resolution.** -/
theorem mass_eq [CompactSpace X] (N : T.Resolution) (θ : ClosedRealOneOneForm n X)
    {ψ : T.space.obj.left → EReal}
    (h : IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν)) :
    T.mass θ ψ = diagonalPotentialMass (ClosedRealOneOneForm.pullback N.R.contMDiff θ) (ψ ∘ N.ν) h := by
  refine le_antisymm ?_ (le_iSup₂ (f := fun (N : T.Resolution)
    (h : IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν)) =>
    diagonalPotentialMass (ClosedRealOneOneForm.pullback N.R.contMDiff θ) (ψ ∘ N.ν) h) N h)
  refine iSup₂_le fun N' h' => ?_
  exact (mass_reading_eq N' N θ h' h).le

/-- `ψ ∈ PSH(Ỹ, θ|_Ỹ)_{>0}`: `ψ` is `θ|_Ỹ`-psh with positive non-pluripolar mass. -/
def IsPositive (T : TildeY Y) (θ : ClosedRealOneOneForm n X) (ψ : T.space.obj.left → EReal) :
    Prop :=
  T.space.IsThetaPSH (T.restrict θ) ψ ∧ 0 < T.mass θ ψ

/-! ### Orders and `𝓘`-goodness on `Ỹ` -/

/-- `u ⪯_P v` on `Ỹ`, read on every resolution of `Ỹ`. -/
def POrder (T : TildeY Y) (u v : T.space.obj.left → EReal) : Prop :=
  ∀ N : T.Resolution, SourcePOrder (n := Y.dim) (u ∘ N.ν) (v ∘ N.ν)

/-- `u ∼_P v` on `Ỹ`. -/
def PEquivalent (T : TildeY Y) (u v : T.space.obj.left → EReal) : Prop :=
  T.POrder u v ∧ T.POrder v u

/-- `𝓘`-goodness on `Ỹ` (`chap:Igood` on `Ỹ`), read on every resolution of `Ỹ`. -/
def IGood (T : TildeY Y) (u : T.space.obj.left → EReal) : Prop :=
  ∀ N : T.Resolution, SGPT.Foundations.Analysis.Pending.IGood (n := Y.dim) (u ∘ N.ν)

/-- **The `P`-order on `Ỹ` does not depend on the resolution** (`lma:Ipartorderinv` and common
resolutions): for `u`, `v` whose readings are quasi-psh, `u ⪯_P v` on `Ỹ` as soon as the readings
on ONE resolution satisfy it. -/
theorem pOrder_iff_exists {u v : T.space.obj.left → EReal}
    (hu : ∀ N : T.Resolution,
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel Y.dim N.R.V).IsQPSH (u ∘ N.ν))
    (hv : ∀ N : T.Resolution,
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel Y.dim N.R.V).IsQPSH (v ∘ N.ν)) :
    T.POrder u v ↔ ∃ N : T.Resolution, SourcePOrder (n := Y.dim) (u ∘ N.ν) (v ∘ N.ν) := by
  constructor
  · intro h
    obtain ⟨N⟩ := T.nonempty_resolution
    exact ⟨N, h N⟩
  · rintro ⟨N₁, h₁⟩ N
    obtain ⟨N₃, p₁, p, hp₁, hp, -, -, hν₁, hν⟩ := Resolution.exists_common N₁ N
    have h₃ := (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff N₁.R.kahler
      N₃.R.kahler hp₁ (hu N₁) (hv N₁)).mp h₁
    have e : ∀ w : T.space.obj.left → EReal, (w ∘ N₁.ν) ∘ p₁ = (w ∘ N.ν) ∘ p := by
      intro w
      rw [Function.comp_assoc, Function.comp_assoc, ← hν₁, ← hν]
    rw [e u, e v] at h₃
    exact (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff N.R.kahler
      N₃.R.kahler hp (hu N) (hv N)).mpr h₃

/-- Readings of `θ|_Ỹ`-psh functions are quasi-psh (forward half of `cor:PSH`). -/
theorem CorPSHForward.isQPSH_comp {N : T.Resolution} (h : T.CorPSHForward N)
    {θ : ClosedRealOneOneForm n X}
    {ψ : T.space.obj.left → EReal} (hψ : T.space.IsThetaPSH (T.restrict θ) ψ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel Y.dim N.R.V).IsQPSH (ψ ∘ N.ν) :=
  ⟨SGPT.PSH.VariableComplexAtlas.nativeClosedFormToAtlas
      (ClosedRealOneOneForm.pullback N.R.contMDiff θ),
    (SGPT.PSH.VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential _ _).mpr
      (by rw [SGPT.PSH.VariableComplexAtlas.sourceNativeAtlasForm_roundTrip]; exact h θ ψ hψ)⟩

/-! ### `d_S` on `Ỹ` -/

/-- `d_S(a_j, b_j) → 0` on `Ỹ`: for every resolution `ν` of `Ỹ` and every closed real
`(1,1)`-form `η` of big class on it with `a_j ∘ ν, b_j ∘ ν ∈ PSH(V, η)`,
`d_{S,η}(a_j ∘ ν, b_j ∘ ν) → 0`. -/
def DistTendstoZero [CompactSpace X] (T : TildeY Y) (a b : ℕ → T.space.obj.left → EReal) : Prop :=
  ∀ (N : T.Resolution) (η : ClosedRealOneOneForm Y.dim N.R.V)
    (hbig : IsBigClass (RealBottChern.ofRepresentative η)),
    (∀ j, IsThetaPshPotential η.val (a j ∘ N.ν)) → (∀ j, IsThetaPshPotential η.val (b j ∘ N.ν)) →
      Tendsto (fun j => singularityDistance N.R.kahler η hbig (a j ∘ N.ν) (b j ∘ N.ν)) atTop
        (𝓝 0)

/-- `u_i → u` in `d_S` on `Ỹ` along the filter `L`: for every resolution `ν` of `Ỹ` and every
closed real `(1,1)`-form `η` of big class on it containing all the readings, the readings converge
in `d_{S,η}`. -/
def TendstoDS (T : TildeY Y) {I : Type*} (L : Filter I) (ui : I → T.space.obj.left → EReal)
    (w : T.space.obj.left → EReal) : Prop :=
  ∀ (N : T.Resolution) (η : ClosedRealOneOneForm Y.dim N.R.V)
    (hbig : IsBigClass (RealBottChern.ofRepresentative η))
    (hui : ∀ i, IsThetaPshPotential η.val (ui i ∘ N.ν)) (hw : IsThetaPshPotential η.val (w ∘ N.ν)),
    Tendsto (fun i => (⟨ui i ∘ N.ν, hui i⟩ : ThetaPshL1 η.val)) L
      (@nhds (ThetaPshL1 η.val)
        (singularityPseudoMetricSpace N.R.kahler η hbig).toUniformSpace.toTopologicalSpace
        ⟨w ∘ N.ν, hw⟩)

/-! ### The trace predicate read on a resolution -/

/-- The trace predicate (`def:traceop`) read on the resolution `N` of `Ỹ`: `τ` is a trace
operator of `φ` along the resolution target `(V, ι)` of `Y` (for some auxiliary Kähler forms;
by `Trace2Resolution.trace_independent_of_qea` the condition does not depend on them). -/
def IsTraceOn (N : T.Resolution) (φ : X → EReal) (τ : N.R.V → EReal) : Prop :=
  ∃ (om : KahlerBackground n X) (omV : KahlerBackground Y.dim N.R.V),
    IsSourceTraceRepresentativeAlong om omV N.R.contMDiff φ τ

/-- **The trace predicate does not depend on the auxiliary Kähler forms**: a trace operator read
on a resolution for some auxiliary Kähler forms `ω` on `X` and `ωV` on `V` is one for every
choice (all trace operators are `P`-equivalent, `prop:traceunique`, and the trace predicate is
closed under `P`-equivalence, `prop:ds0char`). -/
theorem IsTraceOn.retarget [CompactSpace X] {N : T.Resolution} {φ : X → EReal}
    {τ : N.R.V → EReal} (h : IsTraceOn N φ τ) (om' : KahlerBackground n X)
    (omV' : KahlerBackground Y.dim N.R.V) :
    IsSourceTraceRepresentativeAlong om' omV' N.R.contMDiff φ τ := by
  obtain ⟨om, omV, ht⟩ := h
  have hφ : IsGlobalQuasiPshPotential (n := n) φ := by
    obtain ⟨-, θ, ε, U, happ, -⟩ := ht
    exact happ.1.quasiPshPotential
  obtain ⟨τ', ht'⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential Y.dim_le
    om' omV' hφ N.R.contMDiff ht.1
  have hP := SGPT.Okounkov.sourcePEquivalent_of_sourceTraceRepresentatives Y.dim_le omV' omV
    N.R.contMDiff ht' ht
  obtain ⟨-, θ, ε, U, -, β, -, hτ, -⟩ := ht
  exact SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent
    N.R.contMDiff om' omV' ht' hτ hP

section Transfer

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-- **Traces read on two resolutions of `Ỹ`.** If the reading of `ψ` on `N₁` is a trace operator
of `φ`, and the reading of `ψ` on `N₂` is quasi-psh, then the reading of `ψ` on `N₂` is a trace
operator of `φ`. (Pull both back to a common resolution `N₃`, compare with a trace operator read
on `N₂`, and descend the `P`-equivalence along `N₃ → N₂`, `lma:Ipartorderinv`.) -/
theorem transfer (N₁ N₂ : T.Resolution) {φ : X → EReal} {ψ : T.space.obj.left → EReal}
    (h₁ : IsTraceOn N₁ φ (ψ ∘ N₁.ν)) {σ : ClosedRealOneOneForm Y.dim N₂.R.V}
    (hσ : IsThetaPshPotential σ.val (ψ ∘ N₂.ν)) : IsTraceOn N₂ φ (ψ ∘ N₂.ν) := by
  obtain ⟨om, omV, ht₁⟩ := h₁
  obtain ⟨N₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂, hν₁, hν₂⟩ := Resolution.exists_common N₁ N₂
  have hφ : IsGlobalQuasiPshPotential (n := n) φ := by
    obtain ⟨-, θ, ε, U, happ, -⟩ := ht₁
    exact happ.1.quasiPshPotential
  have hgen := sourceGenericLelong_eq_zero_of_trace N₁.R ht₁
  obtain ⟨τ₂, hτ₂⟩ := exists_trace N₂.R om hφ hgen
  have d₁ := trace_comp_of_dominates N₁.R N₃.R hp₁ hc₁ om ht₁
  have d₂ := trace_comp_of_dominates N₂.R N₃.R hp₂ hc₂ om hτ₂
  obtain ⟨κ, hκ⟩ := d₂.1
  have hP := d₁.2 κ N₃.R.kahler _ hκ
  have heq : (ψ ∘ N₁.ν) ∘ p₁ = (ψ ∘ N₂.ν) ∘ p₂ := by
    rw [Function.comp_assoc, Function.comp_assoc, ← hν₁, ← hν₂]
  rw [heq] at hP
  have hq₁ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel Y.dim N₂.R.V).IsQPSH (ψ ∘ N₂.ν) :=
    ⟨SGPT.PSH.VariableComplexAtlas.nativeClosedFormToAtlas σ,
      (SGPT.PSH.VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential _ _).mpr
        (by rwa [SGPT.PSH.VariableComplexAtlas.sourceNativeAtlasForm_roundTrip])⟩
  have hq₂ := SGPT.NAPotential.NATrace.isQPSH_of_sourceTrace N₂.R.contMDiff hτ₂
  have e₁ := (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff N₂.R.kahler
    N₃.R.kahler hp₂ hq₂ hq₁).mpr hP.2
  have e₂ := (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff N₂.R.kahler
    N₃.R.kahler hp₂ hq₁ hq₂).mpr hP.1
  exact ⟨om, N₂.R.kahler,
    SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent
      N₂.R.contMDiff om N₂.R.kahler hτ₂ hσ ⟨e₁, e₂⟩⟩

end Transfer

end TildeY

end SGPT.Trace.TY
