import SGPT.Trace.RIsoBTraceResolutionMass
import SGPT.Trace.BertiniGeneralMember
import SGPT.Trace.DecreasingNetTrace
import Mathlib.Geometry.Euclidean.Volume.Measure
import SGPT.NAPotential.NATraceSmooth
import SGPT.PSH.SourceModificationOrders
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent

/-!
# Multiplicity of an analytic set at a point and moving Seshadri constants

Source `rmk:movingSes` (`chapter_trace.tex`): *the trace operator allows us to introduce the
following extension of the moving Seshadri constant. For `T ∈ 𝒵₊(X, α)` and `x ∈ X`, define*
`ε(T, x) := inf_{V ∋ x} (vol Tr_V^{α|_Ṽ} T / mult_x V)^{1/dim V}`, *where
`vol Tr_V^{α|_Ṽ} T = 0` if `Tr_V^{α|_Ṽ} T` is not defined. Here `V` runs over all
positive-dimensional closed irreducible analytic subsets of `X` containing `x`.* (The rest of the
remark is historical: "these moving Seshadri constants seem to be new ... I will not study these
objects in this book".)

## The multiplicity `mult_x V`

The book uses the classical multiplicity of an analytic set at a point without defining it. We
take the classical definition through the Lelong number of the integration current
(Lelong 1957; Demailly, *Complex analytic and differential geometry*, III (7.6)–(7.7)): for an
analytic set `A` of pure dimension `p` and `x ∈ A`, in local coordinates `z` centred at `x`,
`mult_x A = ν([A], x) = lim_{r → 0} σ_{[A]}(B(x, r)) / (π^p r^{2p} / p!)`, where the trace measure
`σ_{[A]} = [A] ∧ (dd^c|z|²)^p / p!` of the integration current is the `2p`-dimensional Euclidean
area of `A` (Wirtinger; the singular locus has zero `2p`-dimensional measure) and `π^p r^{2p}/p!`
is the volume of the `2p`-dimensional ball of radius `r`. By Thie's theorem this is the sheet
number of a generic linear projection `(A, x) → (ℂ^p, 0)` (Demailly III (7.6)–(7.7)), i.e. the
Hilbert–Samuel multiplicity of `𝒪_{A,x}`.

Formally (`analyticDensityRatio`, `analyticMultiplicity`): in the atlas chart `e` at `x`, with
Mathlib's `2p`-dimensional Euclidean Hausdorff measure `μHE[2p]`,
`mult_x A = liminf_{r → 0+} μHE[2p](e(A ∩ dom e) ∩ B(e x, r)) / vol(B_{ℂ^p}(0, r))`.
(The ratio is nondecreasing in `r` by Lelong's monotonicity theorem, so the lower limit is the
limit; neither this nor the independence of the chart nor Thie's theorem is formalized here.)
`subvarietyMultiplicity V x := analyticMultiplicity V.carrier (dim V) x`.
Sanity check: `analyticMultiplicity_univ` (`mult_x X = 1`).

## The volume of the trace

For an irreducible `V`, `vol Tr_V^{α|_Ṽ} T` is the mass `∫ (θ|_Ṽ + dd^c Tr^θ_V(φ))^{dim V}` of the
normalized trace `Tr^θ_V(φ)` (`def:traceop2`, `ex:tracedefinedposmass`; `0` if undefined), where
`T = θ + dd^c φ`, `α = {θ}`. It is read on a resolution target `(V', ι)` of `V`
(`Trace2Resolution.ResolutionTarget`; the book reads it on the normalization `Ṽ`):
`resolutionTraceVolume = SGPT.Trace.sourceTraceMass` on `V'`. It does not depend on the
auxiliary Kähler forms (`resolutionTraceVolume_eq_of_choices`) nor on the potential of `T`
(`sourceTraceMass_eq_of_iEquivalent`: `𝓘`-equivalent potentials, in particular two potentials of
the same current, `TraceCurrent.iEquivalentOnManifold_of_isPresentation`, have the same trace
volume).

## Main definitions

* `movingSeshadri omega₀ R θ φ x`: the book's `ε(T, x)` for `T = θ + dd^c φ`, the traces of the
  subsets `V` being read on the resolution targets `R V`; `movingSeshadriChosen`: the same with
  chosen resolution targets (they exist by `Trace2Resolution.exists_resolutionTarget`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.TraceRes

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder

/-! ### The multiplicity of an analytic set at a point -/

section Multiplicity

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- The **density ratio** of a set `A ⊆ X` in (complex) dimension `p` at `x`, at radius `r`: in
the atlas chart `e` at `x`, the `2p`-dimensional Euclidean area of `e(A) ∩ B(e x, r)` divided by
the volume of the `2p`-dimensional ball of radius `r`. For an analytic set `A` of pure dimension
`p` this is `σ_{[A]}(B(x, r)) / (π^p r^{2p} / p!)`, the Lelong ratio of the integration current
`[A]`. -/
def analyticDensityRatio (A : Set X) (p : ℕ) (x : X) (r : ℝ) : ℝ≥0∞ :=
  (μHE[2 * p] : Measure (ComplexModel n))
      ((complexChartAt (n := n) x).val '' (A ∩ (complexChartAt (n := n) x).val.source) ∩
        Metric.ball ((complexChartAt (n := n) x).val x) r) /
    volume (Metric.ball (0 : ComplexModel p) r)

/-- **The multiplicity `mult_x A` of an analytic set `A` of pure dimension `p` at `x`**: the
Lelong number `ν([A], x)` of the integration current `[A]`, i.e. the lower limit as `r → 0+` of
the density ratio (`analyticDensityRatio`). By Lelong's monotonicity theorem the limit exists, and
by Thie's theorem it is the sheet number of a generic linear projection of `(A, x)`
(Demailly, *Complex analytic and differential geometry*, III (7.6)–(7.7)). -/
def analyticMultiplicity (A : Set X) (p : ℕ) (x : X) : ℝ≥0∞ :=
  liminf (analyticDensityRatio (n := n) A p x) (𝓝[>] 0)

/-- `mult_x V` for a closed irreducible analytic subset `V` (of dimension `dim V`). -/
def subvarietyMultiplicity [IsComplexManifold n X] (V : ClosedIrreducibleAnalyticSubvariety n X)
    (x : X) : ℝ≥0∞ :=
  analyticMultiplicity (n := n) V.carrier V.dim x

private theorem finrank_complexModel (n : ℕ) : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexModel n), Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]

/-- **Sanity check: `mult_x X = 1`.** The whole manifold has multiplicity one at every point (the
density ratio is `1` for every radius small enough that the ball lies in the chart). -/
theorem analyticMultiplicity_univ (x : X) :
    analyticMultiplicity (n := n) (univ : Set X) n x = 1 := by
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x)
    (e.map_source (mem_complexChartAt_source x))
  have hvol : (μHE[2 * n] : Measure (ComplexModel n)) = volume := by
    rw [← finrank_complexModel n]
    exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), analyticDensityRatio (n := n) (univ : Set X) n x r = 1 := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    unfold analyticDensityRatio
    rw [← he, univ_inter, e.image_source_eq_target,
      inter_eq_right.mpr ((Metric.ball_subset_ball hr.2.le).trans hball), hvol,
      Measure.addHaar_ball_center]
    exact ENNReal.div_self (Metric.measure_ball_pos volume _ hr.1).ne' measure_ball_lt_top.ne
  unfold analyticMultiplicity
  rw [liminf_congr hev, liminf_const]

end Multiplicity

/-! ### Trace volumes are invariant under `𝓘`-equivalence of the potential -/

section TraceVolume

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

private theorem sourceTraceMass_eq_of_iEquivalent_aux (hk : k ≤ n)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) {β β' : ClosedRealOneOneForm n M} {u u' : M → EReal}
    (hu : IsThetaPshPotential β.val u) (hu' : IsThetaPshPotential β'.val u')
    (h₁ : IEnvelope.IOrderOnManifold (n := n) u u')
    (hd : HasPositiveSourceTraceAlong omega omegaV hι θ u)
    (h₂ : IEnvelope.IOrderOnManifold (n := n) u' u) :
    sourceTraceMass omega omegaV hι θ u' = sourceTraceMass omega omegaV hι θ u := by
  obtain ⟨τ, hT, hτ, hpos⟩ := hd
  have hg : sourceGenericLelongNumber (n := n) ι u' = 0 :=
    SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder hu h₁ hT.1
  obtain ⟨τ', hT'⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omega
    omegaV hu'.quasiPshPotential hι hg
  have hP₁ := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hT hT' h₁
  have hP₂ := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hT' hT h₂
  have hT'' : IsSourceTraceRepresentativeAlong omega omegaV hι u' τ :=
    SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent hι omega omegaV
      hT' hτ ⟨hP₂, hP₁⟩
  rw [sourceTraceMass_eq_of_trace hk omegaV omegaV hι θ u' hT'' hτ hpos,
    sourceTraceMass_eq_of_trace hk omegaV omegaV hι θ u hT hτ hpos]

/-- **The trace volume depends only on the `𝓘`-class of the potential.** If `u` and `u'` are
`𝓘`-equivalent quasi-psh functions on `X` (for instance two potentials of the same closed positive
current, `TraceCurrent.iEquivalentOnManifold_of_isPresentation`), then
`vol Tr^θ_Y(u) = vol Tr^θ_Y(u')` (both `0` if undefined). -/
theorem sourceTraceMass_eq_of_iEquivalent (hk : k ≤ n)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) {β β' : ClosedRealOneOneForm n M} {u u' : M → EReal}
    (hu : IsThetaPshPotential β.val u) (hu' : IsThetaPshPotential β'.val u')
    (h₁ : IEnvelope.IOrderOnManifold (n := n) u u')
    (h₂ : IEnvelope.IOrderOnManifold (n := n) u' u) :
    sourceTraceMass omega omegaV hι θ u = sourceTraceMass omega omegaV hι θ u' := by
  classical
  by_cases hd : HasPositiveSourceTraceAlong omega omegaV hι θ u
  · exact (sourceTraceMass_eq_of_iEquivalent_aux hk omega omegaV hι θ hu hu' h₁ hd h₂).symm
  by_cases hd' : HasPositiveSourceTraceAlong omega omegaV hι θ u'
  · exact sourceTraceMass_eq_of_iEquivalent_aux hk omega omegaV hι θ hu' hu h₂ hd' h₁
  unfold sourceTraceMass
  rw [dif_neg hd, dif_neg hd']

end TraceVolume

/-! ### The moving Seshadri constant -/

section MovingSeshadri

open SGPT.Trace.Trace2Resolution

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- `vol Tr_V^{θ|_V}(φ)`, read on the resolution target `R` of `V`: the mass
`∫_{V'} (θ|_{V'} + dd^c Tr^θ_V(φ))^{dim V}` of the normalized trace (`def:traceop2`), `0` if the
normalized trace is not defined (the convention of `ex:tracedefinedposmass` and
`rmk:movingSes`). -/
def resolutionTraceVolume (omega₀ : KahlerBackground n X)
    {V : ClosedIrreducibleAnalyticSubvariety n X} (R : ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) : ℝ≥0∞ :=
  sourceTraceMass omega₀ R.kahler R.contMDiff θ φ

/-- The trace volume does not depend on the auxiliary Kähler forms of `X` and of the
resolution. -/
theorem resolutionTraceVolume_eq_of_choices (omega₀ omega₁ : KahlerBackground n X)
    {V : ClosedIrreducibleAnalyticSubvariety n X} (R : ResolutionTarget V)
    (omegaV : KahlerBackground V.dim R.V) (θ : ClosedRealOneOneForm n X) (φ : X → EReal) :
    resolutionTraceVolume omega₀ R θ φ = sourceTraceMass omega₁ omegaV R.contMDiff θ φ :=
  sourceTraceMass_eq_of_choices V.dim_le omega₀ omega₁ R.kahler omegaV R.contMDiff θ φ

/-- **Source `rmk:movingSes`: the moving Seshadri constant** `ε(T, x)` of
`T = θ + dd^c φ ∈ 𝒵₊(X, {θ})` at `x ∈ X`:
`ε(T, x) = inf_{V ∋ x} (vol Tr_V^{θ|_V} T / mult_x V)^{1/dim V}`, the infimum over all
positive-dimensional closed irreducible analytic subsets `V ⊆ X` containing `x`, with
`vol Tr_V^{θ|_V} T = 0` if the normalized trace is not defined. The trace volume of each `V` is
read on the resolution target `R V` (`resolutionTraceVolume`) and `mult_x V` is
`subvarietyMultiplicity` (the Lelong number of `[V]` at `x`). Values in `[0, ∞]`. -/
def movingSeshadri (omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) (x : X) : ℝ≥0∞ :=
  ⨅ (V : ClosedIrreducibleAnalyticSubvariety n X) (_ : x ∈ V.carrier) (_ : 0 < V.dim),
    (resolutionTraceVolume omega₀ (R V) θ φ / subvarietyMultiplicity V x) ^ ((V.dim : ℝ)⁻¹)

/-- The moving Seshadri constant with chosen resolution targets (they exist,
`Trace2Resolution.exists_resolutionTarget`). -/
def movingSeshadriChosen (omega₀ : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (φ : X → EReal) (x : X) : ℝ≥0∞ :=
  movingSeshadri omega₀ (fun V => (exists_resolutionTarget omega₀ V).some) θ φ x

omit [CompactSpace X] in
/-- `ε(T, x) ≤ (vol Tr_V T / mult_x V)^{1/dim V}` for every admissible `V`. -/
theorem movingSeshadri_le (omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) {x : X}
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hx : x ∈ V.carrier) (hV : 0 < V.dim) :
    movingSeshadri omega₀ R θ φ x ≤
      (resolutionTraceVolume omega₀ (R V) θ φ / subvarietyMultiplicity V x) ^ ((V.dim : ℝ)⁻¹) :=
  (iInf_le _ V).trans ((iInf_le _ hx).trans (iInf_le _ hV))

omit [CompactSpace X] in
/-- `ε(T, x)` is the greatest lower bound of the quantities of `rmk:movingSes`. -/
theorem le_movingSeshadri_iff (omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) (x : X) (c : ℝ≥0∞) :
    c ≤ movingSeshadri omega₀ R θ φ x ↔
      ∀ V : ClosedIrreducibleAnalyticSubvariety n X, x ∈ V.carrier → 0 < V.dim →
        c ≤ (resolutionTraceVolume omega₀ (R V) θ φ / subvarietyMultiplicity V x) ^
          ((V.dim : ℝ)⁻¹) := by
  simp only [movingSeshadri, le_iInf_iff]

/-- `ε(T, x)` does not depend on the auxiliary Kähler form of `X`. -/
theorem movingSeshadri_eq_of_omega (omega₀ omega₁ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) (x : X) :
    movingSeshadri omega₀ R θ φ x = movingSeshadri omega₁ R θ φ x := by
  unfold movingSeshadri
  refine iInf_congr fun V => ?_
  rw [resolutionTraceVolume_eq_of_choices omega₀ omega₁ (R V) (R V).kahler θ φ]
  rfl

/-- `ε(T, x)` does not depend on the Kähler forms carried by the resolution targets. -/
theorem movingSeshadri_eq_of_kahler (omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (κ : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, KahlerBackground V.dim (R V).V)
    (θ : ClosedRealOneOneForm n X) (φ : X → EReal) (x : X) :
    movingSeshadri omega₀ (fun V => { R V with kahler := κ V }) θ φ x =
      movingSeshadri omega₀ R θ φ x := by
  unfold movingSeshadri
  refine iInf_congr fun V => ?_
  have h : resolutionTraceVolume omega₀ { R V with kahler := κ V } θ φ =
      resolutionTraceVolume omega₀ (R V) θ φ :=
    (resolutionTraceVolume_eq_of_choices omega₀ omega₀ (R V) (κ V) θ φ).symm
  dsimp only
  rw [h]

/-- **`ε(T, x)` depends only on the current `T`**: `𝓘`-equivalent potentials (in particular two
potentials `φ`, `φ'` of the same closed positive current,
`TraceCurrent.iEquivalentOnManifold_of_isPresentation`)
give the same moving Seshadri constant. -/
theorem movingSeshadri_eq_of_iEquivalent (omega₀ : KahlerBackground n X)
    (R : ∀ V : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget V)
    (θ : ClosedRealOneOneForm n X) {β β' : ClosedRealOneOneForm n X} {φ φ' : X → EReal}
    (hφ : IsThetaPshPotential β.val φ) (hφ' : IsThetaPshPotential β'.val φ')
    (h₁ : IEnvelope.IOrderOnManifold (n := n) φ φ')
    (h₂ : IEnvelope.IOrderOnManifold (n := n) φ' φ) (x : X) :
    movingSeshadri omega₀ R θ φ x = movingSeshadri omega₀ R θ φ' x := by
  unfold movingSeshadri resolutionTraceVolume
  refine iInf_congr fun V => ?_
  rw [sourceTraceMass_eq_of_iEquivalent V.dim_le omega₀ (R V).kahler (R V).contMDiff θ hφ hφ' h₁
    h₂]

end MovingSeshadri


/-! ### Trace volumes read on two resolutions, one dominating the other -/

section Dominates

open SGPT.Trace.Trace2Resolution SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {V : ClosedIrreducibleAnalyticSubvariety n X}

omit [CompactSpace X] in
private theorem pullback_dominates_geometricallyEq (R₁ R₂ : ResolutionTarget V)
    {p : R₂.V → R₁.V} (hp : ContMDiff 𝓘(ℂ, ComplexModel V.dim) 𝓘(ℂ, ComplexModel V.dim) ∞ p)
    (hcomm : ∀ w, R₂.ι w = R₁.ι (p w)) (θ : ClosedRealOneOneForm n X) :
    (ClosedRealOneOneForm.pullback hp
      (ClosedRealOneOneForm.pullback R₁.contMDiff θ)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback R₂.contMDiff θ).val := by
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    ClosedRealOneOneForm.pullback_val]
  have h₁ := SGPT.Okounkov.TranscendentalVolId.pullback_comp_geometricallyEq' R₁.contMDiff hp θ.val
  have hf : R₁.ι ∘ p = R₂.ι := funext fun w => (hcomm w).symm
  have h₃ : ∀ (f g : R₂.V → X), f = g →
      ∀ (hf' : ContMDiff 𝓘(ℂ, ComplexModel V.dim) 𝓘(ℂ, ComplexModel n) ∞ f)
        (hg' : ContMDiff 𝓘(ℂ, ComplexModel V.dim) 𝓘(ℂ, ComplexModel n) ∞ g),
      (SmoothRealForm.pullback hf' θ.val).GeometricallyEq (SmoothRealForm.pullback hg' θ.val) := by
    rintro f g rfl hf' hg'
    exact SmoothRealForm.GeometricallyEq.refl _
  exact h₁.symm.trans (h₃ _ _ hf _ R₂.contMDiff)

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

private theorem sourceTraceMass_dominates_of_pos (omega₀ : KahlerBackground n X)
    (R₁ R₂ : ResolutionTarget V) {p : R₂.V → R₁.V} (hp : IsAnalyticModification (n := V.dim) p)
    (hcomm : ∀ w, R₂.ι w = R₁.ι (p w)) (θ : ClosedRealOneOneForm n X) (φ : X → EReal)
    (hd : HasPositiveSourceTraceAlong omega₀ R₁.kahler R₁.contMDiff θ φ) :
    sourceTraceMass omega₀ R₂.kahler R₂.contMDiff θ φ =
      sourceTraceMass omega₀ R₁.kahler R₁.contMDiff θ φ := by
  obtain ⟨τ, hT, hτ, hpos⟩ := hd
  obtain ⟨⟨κ, hT₂⟩, -⟩ := trace_comp_of_dominates R₁ R₂ hp hcomm omega₀ hT
  have hgeo := pullback_dominates_geometricallyEq R₁ R₂ hp.1 hcomm θ
  have hτp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hp (ClosedRealOneOneForm.pullback R₁.contMDiff θ) hτ
  have hτ₂ : IsThetaPshPotential (ClosedRealOneOneForm.pullback R₂.contMDiff θ).val (τ ∘ p) :=
    (hgeo.thetaPshPotential_iff _).mp hτp
  have hm : DiagonalMass.diagonalPotentialMass (ClosedRealOneOneForm.pullback R₂.contMDiff θ)
      (τ ∘ p) hτ₂ =
      DiagonalMass.diagonalPotentialMass (ClosedRealOneOneForm.pullback R₁.contMDiff θ) τ hτ :=
    (ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hgeo hτp hτ₂).symm.trans
      (AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification hp _
        hτ)
  have hpos₂ : DiagonalMass.HasPositivePotentialMass (ClosedRealOneOneForm.pullback R₂.contMDiff θ)
      (τ ∘ p) hτ₂ := by
    unfold DiagonalMass.HasPositivePotentialMass at hpos ⊢
    rw [hm]
    exact hpos
  rw [sourceTraceMass_eq_of_trace V.dim_le R₂.kahler R₂.kahler R₂.contMDiff θ φ hT₂ hτ₂ hpos₂,
    sourceTraceMass_eq_of_trace V.dim_le R₁.kahler R₁.kahler R₁.contMDiff θ φ hT hτ hpos, hm]

private theorem hasPositiveSourceTraceAlong_of_dominates (omega₀ : KahlerBackground n X)
    (R₁ R₂ : ResolutionTarget V) {p : R₂.V → R₁.V} (hp : IsAnalyticModification (n := V.dim) p)
    (hcomm : ∀ w, R₂.ι w = R₁.ι (p w)) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hd : HasPositiveSourceTraceAlong omega₀ R₂.kahler R₂.contMDiff θ φ) :
    HasPositiveSourceTraceAlong omega₀ R₁.kahler R₁.contMDiff θ φ := by
  obtain ⟨σ, hT₂, hσ, hpos⟩ := hd
  have hgeo := pullback_dominates_geometricallyEq R₁ R₂ hp.1 hcomm θ
  have hσp : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hp.1 (ClosedRealOneOneForm.pullback R₁.contMDiff θ)).val σ :=
    (hgeo.thetaPshPotential_iff _).mpr hσ
  obtain ⟨ψ, hψ, hψσ⟩ :=
    AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hp
      (ClosedRealOneOneForm.pullback R₁.contMDiff θ) hσp
  have hσeq : (fun y => ψ (p y)) = σ := funext hψσ
  subst hσeq
  have hg₁ : sourceGenericLelongNumber (n := n) R₁.ι φ = 0 := by
    rw [sourceGenericLelongNumber_eq_sourceGenericLelong R₁.isResolutionOf.range_eq,
      ← sourceGenericLelongNumber_eq_sourceGenericLelong R₂.isResolutionOf.range_eq]
    exact hT₂.1
  obtain ⟨τ₁, hT₁⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential V.dim_le
    omega₀ R₁.kahler hφ.quasiPshPotential R₁.contMDiff hg₁
  obtain ⟨-, hP⟩ := trace_comp_of_dominates R₁ R₂ hp hcomm omega₀ hT₁
  have hPe := hP omega₀ R₂.kahler _ hT₂
  have hqτ₁ := SGPT.NAPotential.NATrace.isQPSH_of_sourceTrace R₁.contMDiff hT₁
  have hqψ : (ofFixedModel V.dim R₁.V).IsQPSH ψ :=
    ⟨nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback R₁.contMDiff θ),
      (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by rwa [sourceNativeAtlasForm_roundTrip])⟩
  have e1 := (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff R₁.kahler R₂.kahler
    hp hqτ₁ hqψ).mpr hPe.1
  have e2 := (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff R₁.kahler R₂.kahler
    hp hqψ hqτ₁).mpr hPe.2
  have hTψ : IsSourceTraceRepresentativeAlong omega₀ R₁.kahler R₁.contMDiff φ ψ :=
    SGPT.Trace.BertiniGeneral.isSourceTraceRepresentativeAlong_of_sourcePEquivalent R₁.contMDiff
      omega₀ R₁.kahler hT₁ hψ ⟨e1, e2⟩
  refine ⟨ψ, hTψ, hψ, ?_⟩
  have hψp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hp (ClosedRealOneOneForm.pullback R₁.contMDiff θ) hψ
  have hm := AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification
    hp (ClosedRealOneOneForm.pullback R₁.contMDiff θ) hψ
  have hm2 := ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hgeo hψp hσ
  unfold DiagonalMass.HasPositivePotentialMass at hpos ⊢
  rw [← hm, hm2]
  exact hpos

/-- **The trace volume does not depend on the resolution, up to a dominating one.** If
`p : V'₂ → V'₁` is a modification between two resolution targets of `V` with `ι₂ = ι₁ ∘ p`, then
for `φ ∈ PSH(X, θ)` the volumes `vol Tr_V^{θ|_V}(φ)` read on `V'₁` and on `V'₂` agree (both `0` if
the normalized trace is undefined). -/
theorem resolutionTraceVolume_dominates (omega₀ : KahlerBackground n X)
    (R₁ R₂ : ResolutionTarget V) {p : R₂.V → R₁.V} (hp : IsAnalyticModification (n := V.dim) p)
    (hcomm : ∀ w, R₂.ι w = R₁.ι (p w)) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    resolutionTraceVolume omega₀ R₂ θ φ = resolutionTraceVolume omega₀ R₁ θ φ := by
  classical
  unfold resolutionTraceVolume
  by_cases hd : HasPositiveSourceTraceAlong omega₀ R₁.kahler R₁.contMDiff θ φ
  · exact sourceTraceMass_dominates_of_pos omega₀ R₁ R₂ hp hcomm θ φ hd
  · have hd' : ¬ HasPositiveSourceTraceAlong omega₀ R₂.kahler R₂.contMDiff θ φ := fun h =>
      hd (hasPositiveSourceTraceAlong_of_dominates omega₀ R₁ R₂ hp hcomm θ hφ h)
    unfold sourceTraceMass
    rw [dif_neg hd, dif_neg hd']

/-- `ε(T, x)` is unchanged when every resolution target is replaced by a dominating one. -/
theorem movingSeshadri_eq_of_dominates (omega₀ : KahlerBackground n X)
    (R R' : ∀ W : ClosedIrreducibleAnalyticSubvariety n X, ResolutionTarget W)
    (hdom : ∀ W, ∃ p : (R' W).V → (R W).V, IsAnalyticModification (n := W.dim) p ∧
      ∀ w, (R' W).ι w = (R W).ι (p w))
    (θ : ClosedRealOneOneForm n X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) (x : X) :
    movingSeshadri omega₀ R' θ φ x = movingSeshadri omega₀ R θ φ x := by
  unfold movingSeshadri
  refine iInf_congr fun W => ?_
  obtain ⟨p, hp, hcomm⟩ := hdom W
  rw [resolutionTraceVolume_dominates omega₀ (R W) (R' W) hp hcomm θ hφ]

end Dominates

end SGPT.Trace.TraceRes

end
