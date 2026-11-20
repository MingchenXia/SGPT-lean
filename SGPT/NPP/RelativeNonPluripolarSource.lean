import SGPT.NPP.RelativeNonPluripolarSourceOpens
import SGPT.NPP.RelativeNonPluripolarCounterexample

/-! Body-preserving consolidation PLAN ONLY. Fresh proper-name checking is
required; private flat objects are provenance, never providers for this file. -/

-- Exact frozen body: PositiveCurrentOpensAnyDraft
section OriginalFragment_01

/-! The genuine original open-current restriction in EVERY ambient dimension,
including n=0. Induced charts are the same actual subtype-restricted originals. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalBedfordTaylorProducts
open LocalBedfordTaylorLocality LocalBedfordTaylorCalculus LocalCurrentPullback
open LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent
variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

section Charts
variable (U : Opens M)
omit [ChartedSpace (ComplexModel n) M] in
/-- The target of the restriction of a chart of `M` to `U` is the coordinate expression of `U`. -/
private theorem inducedSubtypeRestr_target_eq (f : OpenPartialHomeomorph M (ComplexModel n))
    (hU : Nonempty U) : (f.subtypeRestr hU).target = f.target ∩ f.symm ⁻¹' U := by
  simp only [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
    Opens.openPartialHomeomorphSubtypeCoe_target]

/-- **Every atlas chart of the open submanifold `U` is the restriction of the preferred chart of
`M` at some point of `U`** (mathlib's induced atlas). -/
private theorem inducedExists_eq_subtypeRestr (e : ComplexChart n U) :
    ∃ x : U, e.val = (chartAt (ComplexModel n) (x : M)).subtypeRestr ⟨x⟩ := by
  obtain ⟨_, ⟨x, rfl⟩, he⟩ := e.property
  exact ⟨x, mem_singleton_iff.mp he⟩

/-- A point of `U` whose preferred chart restricts to `e`. -/
private def inducedAmbientPoint (e : ComplexChart n U) : U := (inducedExists_eq_subtypeRestr U e).choose

/-- The ambient atlas chart of `M` whose restriction to `U` is the chart `e` of `U`. -/
def inducedAmbientChart (e : ComplexChart n U) : ComplexChart n M :=
  complexChartAt ((inducedAmbientPoint U e : U) : M)

private theorem inducedAmbientChart_spec (e : ComplexChart n U) :
    e.val = (inducedAmbientChart U e).val.subtypeRestr ⟨inducedAmbientPoint U e⟩ :=
  (inducedExists_eq_subtypeRestr U e).choose_spec

/-- The coordinate domain of a chart of `U` is the coordinate expression of `U` in the ambient
chart. -/
private theorem inducedChartTarget_eq_chartDomain (e : ComplexChart n U) :
    chartTarget e = chartDomain (inducedAmbientChart U e) U := by
  ext z
  change z ∈ e.val.target ↔
    z ∈ (inducedAmbientChart U e).val.target ∩ (inducedAmbientChart U e).val.symm ⁻¹' U
  rw [inducedAmbientChart_spec U e, inducedSubtypeRestr_target_eq]

private theorem inducedTarget_eq_ambient (e : ComplexChart n U) :
    e.val.target = (inducedAmbientChart U e).val.target ∩ (inducedAmbientChart U e).val.symm ⁻¹' U := by
  rw [inducedAmbientChart_spec U e, inducedSubtypeRestr_target_eq]

private theorem inducedChartTarget_le_ambient (e : ComplexChart n U) :
    chartTarget e ≤ chartTarget (inducedAmbientChart U e) := by
  rw [inducedChartTarget_eq_chartDomain U e]
  exact chartDomain_le _ U

/-- On its coordinate domain, the inverse of a chart of `U` is the inverse of the ambient chart. -/
private theorem inducedCoe_symm_eq_ambient (e : ComplexChart n U) {z : ComplexModel n}
    (hz : z ∈ e.val.target) : ((e.val.symm z : U) : M) = (inducedAmbientChart U e).val.symm z := by
  have h := inducedAmbientChart_spec U e
  rw [h] at hz
  have := OpenPartialHomeomorph.subtypeRestr_symm_apply (inducedAmbientChart U e).val ⟨inducedAmbientPoint U e⟩ hz
  rw [← this, ← h]
  rfl

private theorem inducedMem_ambientChart_source (e : ComplexChart n U) {x : U} (hx : x ∈ e.val.source) :
    (x : M) ∈ (inducedAmbientChart U e).val.source := by
  rw [inducedAmbientChart_spec U e, OpenPartialHomeomorph.subtypeRestr_source] at hx
  exact hx

private theorem inducedApply_eq_ambient (e : ComplexChart n U) (x : U) :
    e.val x = (inducedAmbientChart U e).val x := by
  rw [inducedAmbientChart_spec U e, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The preferred chart of `U` at `x` is the restriction of the preferred chart of `M`. -/
private theorem inducedComplexChartAt_opens_val (x : U) :
    (complexChartAt (n := n) x).val =
      (complexChartAt (n := n) (x : M)).val.subtypeRestr ⟨x⟩ := rfl

end Charts

variable [IsManifold (𝓘(ℂ,ComplexModel n)) ∞ M]

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
private theorem opens_transition_eq_ambient (U : Opens M)
    (e f : ComplexChart n U) {x : ComplexModel n} (hx : x ∈ overlapSource e f) :
    chartTransition e f x = chartTransition (inducedAmbientChart U e) (inducedAmbientChart U f) x := by
  change f.val (e.val.symm x) = (inducedAmbientChart U f).val ((inducedAmbientChart U e).val.symm x)
  rw [inducedApply_eq_ambient U f,inducedCoe_symm_eq_ambient U e (overlapSource_le e f hx)]

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
private theorem opens_inverse_transition_eq_ambient (U : Opens M)
    (e f : ComplexChart n U) {y : ComplexModel n} (hy : y ∈ overlapTarget e f) :
    (chartTransition e f).symm y = (chartTransition (inducedAmbientChart U e) (inducedAmbientChart U f)).symm y := by
  change e.val (f.val.symm y) = (inducedAmbientChart U e).val ((inducedAmbientChart U f).val.symm y)
  rw [inducedApply_eq_ambient U e,inducedCoe_symm_eq_ambient U f (overlapTarget_le e f hy)]

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
private theorem opens_overlapSource_le_ambient (U : Opens M) (e f : ComplexChart n U) :
    overlapSource e f ≤ overlapSource (inducedAmbientChart U e) (inducedAmbientChart U f) := by
  intro x hx
  have hx' : x ∈ (chartTransition e f).source := hx
  simp only [chartTransition,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
    mem_inter_iff,mem_preimage] at hx'
  change x ∈ (inducedAmbientChart U e).val.target ∧
    (inducedAmbientChart U e).val.symm x ∈ (inducedAmbientChart U f).val.source
  have hs := inducedMem_ambientChart_source U f hx'.2
  rw [inducedCoe_symm_eq_ambient U e hx'.1] at hs
  exact ⟨inducedChartTarget_le_ambient U e hx'.1,hs⟩

/-- The SAME original positive current on the genuine open submanifold U.
All induced-chart compatibility is manufactured from original base overlap. -/
def positiveCurrentOnOpensAny (B : PositiveCurrent n M q) (U : Opens M) :
    PositiveCurrent n U q where
  inChart e := restrict (inducedChartTarget_le_ambient U e) (B.inChart (inducedAmbientChart U e))
  isPositive e := isPositive_restrict (B.isPositive (inducedAmbientChart U e)) (inducedChartTarget_le_ambient U e)
  compatible e f := by
    let E := inducedAmbientChart U e
    let F := inducedAmbientChart U f
    let h₀ := chartTransition_isBiholomorphicPair E F
    let hO := chartTransition_isBiholomorphicPair e f
    have hAA : overlapSource e f ≤ overlapSource E F := opens_overlapSource_le_ambient U e f
    have hBB : overlapTarget e f ≤ overlapTarget E F := by
      exact opens_overlapSource_le_ambient U f e
    have hsub : IsBiholomorphicPair (overlapSource e f) (overlapTarget e f)
        (chartTransition E F) (chartTransition E F).symm := {
      holo := h₀.holo.mono hAA
      holo_inv := h₀.holo_inv.mono hBB
      mapsTo := fun x hx => by
        rw [← opens_transition_eq_ambient U e f hx]
        exact hO.mapsTo hx
      mapsTo_inv := fun y hy => by
        rw [← opens_inverse_transition_eq_ambient U e f hy]
        exact hO.mapsTo_inv hy
      left_inv := fun x hx => h₀.left_inv x (hAA hx)
      right_inv := fun y hy => h₀.right_inv y (hBB hy) }
    calc
      restrict (overlapSource_le e f) (restrict (inducedChartTarget_le_ambient U e) (B.inChart E)) =
        restrict hAA (restrict (overlapSource_le E F) (B.inChart E)) := by
          simp only [restrict_restrict]
      _ = restrict hAA (pullback h₀ (isPositive_restrict (B.isPositive F) (overlapTarget_le E F))) :=
        congrArg (restrict hAA) (B.compatible E F)
      _ = pullback hsub (isPositive_restrict
          (isPositive_restrict (B.isPositive F) (overlapTarget_le E F)) hBB) :=
        (pullback_restrict_of_subpair h₀ hsub hAA hBB
          (isPositive_restrict (B.isPositive F) (overlapTarget_le E F))).symm
      _ = pullback hsub (isPositive_restrict
          (isPositive_restrict (B.isPositive F) (inducedChartTarget_le_ambient U f)) (overlapTarget_le e f)) :=
        pullback_congr_current hsub _ _ (by simp only [restrict_restrict])
      _ = pullback hO (isPositive_restrict
          (isPositive_restrict (B.isPositive F) (inducedChartTarget_le_ambient U f)) (overlapTarget_le e f)) :=
        (pullback_eq_of_inverse_eqOn hO hsub _
          (fun y hy => opens_inverse_transition_eq_ambient U e f hy)).symm

/-- EVERY induced chart retains its exact ORIGINAL ambient scalar/tensor values. -/
theorem positiveCurrentOnOpensAny_inChart (B : PositiveCurrent n M q) (U : Opens M)
    (e : ComplexChart n U) :
    (positiveCurrentOnOpensAny B U).inChart e =
      restrict (inducedChartTarget_le_ambient U e) (B.inChart (inducedAmbientChart U e)) := rfl

/-- Original global closedness survives arbitrary open restriction in every degree. -/
theorem isClosed_positiveCurrentOnOpensAny (B : PositiveCurrent n M q) (hBc : B.IsClosed)
    (U : Opens M) : (positiveCurrentOnOpensAny B U).IsClosed := fun e =>
  isClosedAny_restrict (hBc (inducedAmbientChart U e)) (inducedChartTarget_le_ambient U e)

/-- On positive dimensions this is EXACTLY the already checked original
open-current restriction; no alternative source base model is introduced. -/
theorem positiveCurrentOnOpensAny_succ {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsManifold (𝓘(ℂ,ComplexModel (m + 1))) ∞ X]
    (B : PositiveCurrent (m + 1) X q) (O : Opens X) :
    positiveCurrentOnOpensAny B O = positiveCurrentOnOpens B O := by
  ext1 e
  rfl

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.inducedAmbientChart
#check @SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpensAny
#check @SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpensAny_inChart
#check @SGPT.NPP.RelativeNonPluripolar.isClosed_positiveCurrentOnOpensAny
#check @SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpensAny_succ
#print axioms SGPT.NPP.RelativeNonPluripolar.inducedAmbientChart
#print axioms SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpensAny
#print axioms SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpensAny_inChart
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_positiveCurrentOnOpensAny
#print axioms SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpensAny_succ

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_01

-- Exact frozen body: RelativeEmptySourceDraft
section OriginalFragment_02

/-! ORIGINAL empty-factor relative products in EVERY ambient dimension,
including n=0, with actual source mass and actual induced-open readback. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus
open SGPT.NPP.NonPluripolarCurrent

variable {n r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ,ComplexModel n)) ∞ M]

/-- The ORIGINAL arbitrary closed positive base manufactures actual empty-
factor mass in every ambient dimension, including ZERO; no mass is supplied. -/
theorem hasFiniteGlobalRelativeMass_empty
    (B : PositiveCurrent n M (r + 0)) (hBc : B.IsClosed) (φ : Fin 0 → M → EReal)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) :
    HasFiniteGlobalRelativeMass (p := 0) B hBc φ hφ := by
  intro e
  let u : Fin 0 → ComplexModel n → ℝ := fun i => Fin.elim0 i
  have hu : ∀ i, IsLocallyBoundedPshOn (chartTarget e) (u i) := fun i => Fin.elim0 i
  have hm := hasFiniteRelativeMass_of_isLocallyBoundedPshOn (p := 0) (r := r)
    (B.inChart e) (B.isPositive e) (hBc e) u hu
  exact (relative_mass_product_congr (B.inChart e) (B.isPositive e) (hBc e)
    (fun i x => (u i x : EReal)) (fun i z => φ i (e.val.symm z))
    (fun i => (hu i).1) (chartPlurisubharmonicOn hφ e) (fun i => Fin.elim0 i)).1.mp hm

/-- The genuine empty relative current is EXACTLY the SAME original base B,
in every dimension and output degree, retaining all original current values. -/
theorem globalRelativeNonPluripolarProduct_empty
    (B : PositiveCurrent n M (r + 0)) (hBc : B.IsClosed) (φ : Fin 0 → M → EReal)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass (p := 0) B hBc φ hφ) :
    globalRelativeNonPluripolarProduct (p := 0) B hBc φ hφ hm = B := by
  ext1 e
  let u : Fin 0 → ComplexModel n → ℝ := fun i => Fin.elim0 i
  have hu : ∀ i, IsLocallyBoundedPshOn (chartTarget e) (u i) := fun i => Fin.elim0 i
  have hmB := hasFiniteRelativeMass_of_isLocallyBoundedPshOn (p := 0) (r := r)
    (B.inChart e) (B.isPositive e) (hBc e) u hu
  exact ((relative_mass_product_congr (B.inChart e) (B.isPositive e) (hBc e)
    (fun i z => φ i (e.val.symm z)) (fun i x => (u i x : EReal))
    (chartPlurisubharmonicOn hφ e) (fun i => (hu i).1) (fun i => Fin.elim0 i)).2 (hm e) hmB).trans
    (relativeNonPluripolarProduct_of_isLocallyBoundedPshOn (p := 0) (r := r)
      (B.inChart e) (B.isPositive e) (hBc e) u hu)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- ORIGINAL BASE DATA ALONE produces the full literal empty-factor source
condition and the SAME actual current, including ambient dimension n=0. -/
theorem exists_empty_relative_source_product
    (B : PositiveCurrent n M (r + 0)) (hBc : B.IsClosed) :
    ∃ (φ : Fin 0 → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)),
      ∃ hSource : IsRelativeWellDefinedOnGlobalOpens (p := 0) B hBc φ hφ,
        globalRelativeNonPluripolarProduct (p := 0) B hBc φ hφ
          ((relative_global_source_mass_iff B hBc hφ).mp hSource) = B := by
  let φ : Fin 0 → M → EReal := fun i => Fin.elim0 i
  have hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i) := fun i => Fin.elim0 i
  have hSource := (relative_global_source_mass_iff B hBc hφ).mpr
    (hasFiniteGlobalRelativeMass_empty B hBc φ hφ)
  exact ⟨φ,hφ,hSource,globalRelativeNonPluripolarProduct_empty B hBc φ hφ _⟩

/-- EVERY original open domain gets actual full source mass and the exact
induced-manifold current readback for empty factors, in ALL ambient dimensions.
There is no supplied local mass, current, compatibility or limit certificate. -/
theorem globalRelativeNonPluripolarProduct_empty_opens
    (B : PositiveCurrent n M (r + 0)) (hBc : B.IsClosed) (φ : Fin 0 → M → EReal)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass (p := 0) B hBc φ hφ) (O : Opens M) :
    ∃ (hφO : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (fun x : O => φ i x))
      (hSourceO : IsRelativeWellDefinedOnGlobalOpens (p := 0) (positiveCurrentOnOpensAny B O)
        (isClosed_positiveCurrentOnOpensAny B hBc O) (fun i (x : O) => φ i x) hφO),
      positiveCurrentOnOpensAny (globalRelativeNonPluripolarProduct (p := 0) B hBc φ hφ hm) O =
        globalRelativeNonPluripolarProduct (p := 0) (positiveCurrentOnOpensAny B O)
          (isClosed_positiveCurrentOnOpensAny B hBc O) (fun i (x : O) => φ i x) hφO
          ((relative_global_source_mass_iff (positiveCurrentOnOpensAny B O)
            (isClosed_positiveCurrentOnOpensAny B hBc O) hφO).mp hSourceO) := by
  have hφO : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (fun x : O => φ i x) := fun i => Fin.elim0 i
  have hSourceO := (relative_global_source_mass_iff (positiveCurrentOnOpensAny B O)
    (isClosed_positiveCurrentOnOpensAny B hBc O) hφO).mpr
    (hasFiniteGlobalRelativeMass_empty (positiveCurrentOnOpensAny B O)
      (isClosed_positiveCurrentOnOpensAny B hBc O) (fun i (x : O) => φ i x) hφO)
  refine ⟨hφO,hSourceO,?_⟩
  exact (congrArg (fun S : PositiveCurrent n M r => positiveCurrentOnOpensAny S O)
    (globalRelativeNonPluripolarProduct_empty B hBc φ hφ hm)).trans
      (globalRelativeNonPluripolarProduct_empty (positiveCurrentOnOpensAny B O)
        (isClosed_positiveCurrentOnOpensAny B hBc O) (fun i (x : O) => φ i x) hφO _).symm

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.hasFiniteGlobalRelativeMass_empty
#check @SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_empty
#check @SGPT.NPP.RelativeNonPluripolar.exists_empty_relative_source_product
#check @SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_empty_opens
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteGlobalRelativeMass_empty
#print axioms SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_empty
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_empty_relative_source_product
#print axioms SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_empty_opens

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_02

-- Exact frozen body: RelativeLiteralSourceReadbackDraft
section OriginalFragment_03

/-! Literal original local potentials live on the induced open manifold
itself; the actual source-defined relative current reads back there exactly. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalCurrentL1Ddc

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ,ComplexModel (m + 1))) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- EVERY original tuple on the actual induced open manifold, satisfying
only the original PSH/current equations, gets the full original source mass
and EXACT actual readback of the SAME source-defined global relative current. -/
theorem relativeCurrentProductOfSourceOpens_restrict_actual
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m)
    (hSource : IsRelativeCurrentProductSourceWellDefined B hBc T) (O : Opens M)
    (ψ : Fin p → O → EReal) (hψ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (ψ i))
    (hddc : ∀ i, positiveCurrentOnOpens (T i) O = ddcCurrent m (ψ i) (hψ i)) :
    ∃ hm : IsRelativeWellDefinedOnGlobalOpens (positiveCurrentOnOpens B O)
        (isClosed_positiveCurrentOnOpens B hBc O) ψ hψ,
      positiveCurrentOnOpens (relativeCurrentProductOfSourceOpens B hBc T hSource) O =
        globalRelativeNonPluripolarProduct (positiveCurrentOnOpens B O)
          (isClosed_positiveCurrentOnOpens B hBc O) ψ hψ
          ((relative_global_source_mass_iff (positiveCurrentOnOpens B O)
            (isClosed_positiveCurrentOnOpens B hBc O) hψ).mp hm) := by
  let φ : Fin p → M → EReal := fun i => extendOpens O (ψ i)
  have hφψ : (fun i (x : O) => φ i x) = ψ := funext fun i => extendOpens_comp_val O (ψ i)
  have key : ∀ (ψ' : Fin p → O → EReal)
      (hψ' : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (ψ' i)),
      ψ' = (fun i (x : O) => φ i x) →
      (∀ i, positiveCurrentOnOpens (T i) O = ddcCurrent m (ψ' i) (hψ' i)) →
      ∃ hm : IsRelativeWellDefinedOnGlobalOpens (positiveCurrentOnOpens B O)
          (isClosed_positiveCurrentOnOpens B hBc O) ψ' hψ',
        positiveCurrentOnOpens (relativeCurrentProductOfSourceOpens B hBc T hSource) O =
          globalRelativeNonPluripolarProduct (positiveCurrentOnOpens B O)
            (isClosed_positiveCurrentOnOpens B hBc O) ψ' hψ'
            ((relative_global_source_mass_iff (positiveCurrentOnOpens B O)
              (isClosed_positiveCurrentOnOpens B hBc O) hψ').mp hm) := by
    rintro ψ' hψ' rfl hddc'
    have hpot := (isLocalPotential_iff_actual_opens (T := T) (O := O)).mpr ⟨hψ',hddc'⟩
    exact relativeCurrentProduct_restrict_opens B hBc T
      ((isRelativeCurrentProductWellDefined_iff_sourceOpens B hBc T).mpr hSource) hpot
  exact key ψ hψ hφψ.symm hddc

/-- Genuine current-factor ordering also preserves the LITERAL induced-open
source criterion and the SAME actual source-defined global relative current. -/
theorem relativeCurrentProductOfSourceOpens_comp_perm
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m)
    (hSource : IsRelativeCurrentProductSourceWellDefined B hBc T) (σ : Equiv.Perm (Fin p)) :
    ∃ hSourceσ : IsRelativeCurrentProductSourceWellDefined B hBc (T ∘ σ),
      relativeCurrentProductOfSourceOpens B hBc (T ∘ σ) hSourceσ =
        relativeCurrentProductOfSourceOpens B hBc T hSource := by
  have hW := (isRelativeCurrentProductWellDefined_iff_sourceOpens B hBc T).mpr hSource
  have hWσ := isRelativeCurrentProductWellDefined_comp_perm B hBc T hW σ
  have hs := (isRelativeCurrentProductWellDefined_iff_sourceOpens B hBc (T ∘ σ)).mp hWσ
  exact ⟨hs,relativeCurrentProduct_comp_perm B hBc T σ hW _⟩

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.relativeCurrentProductOfSourceOpens_restrict_actual
#check @SGPT.NPP.RelativeNonPluripolar.relativeCurrentProductOfSourceOpens_comp_perm
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeCurrentProductOfSourceOpens_restrict_actual
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeCurrentProductOfSourceOpens_comp_perm

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_03

-- Exact frozen body: RelativeGlobalFactorReadbackDraft
section OriginalFragment_04

/-! Global original potentials give the SAME literal source current-factor
product, with the original cover, mass and current comparison manufactured. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ,ComplexModel (m + 1))) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- ORIGINAL global PSH functions and actual relative mass manufacture the
literal source potential cover and identify its SAME actual intrinsic current.
Neither a current-factor source-domain certificate nor an output equality is input. -/
theorem exists_relative_source_product_of_global_potentials
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i))
    (hm : HasFiniteGlobalRelativeMass B hBc φ hφ) :
    ∃ hs : IsRelativeCurrentProductSourceWellDefined B hBc
        (fun i => ddcCurrent m (φ i) (hφ i)),
      relativeCurrentProductOfSourceOpens B hBc (fun i => ddcCurrent m (φ i) (hφ i)) hs =
        globalRelativeNonPluripolarProduct B hBc φ hφ hm := by
  let T := fun i => ddcCurrent m (φ i) (hφ i)
  let hp : IsLocalPotential T (⊤ : Opens M) φ := isLocalPotential_ddcCurrent hφ ⊤
  have hmO : HasFiniteRelativeMassOn B hBc φ ⊤ hp.psh := by
    intro e
    exact hasFiniteRelativeMass_restrict (B.inChart e) (B.isPositive e) (hBc e)
      (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)
      (chartDomain_le e ⊤)
  have hW : IsRelativeCurrentProductWellDefined B hBc T := by
    refine ⟨{⊤},fun x => ⟨⊤,mem_singleton _,trivial⟩,?_⟩
    intro O hO
    have he : O = ⊤ := mem_singleton_iff.mp hO
    subst O
    exact ⟨φ,hp,hmO⟩
  have hs := (isRelativeCurrentProductWellDefined_iff_sourceOpens B hBc T).mp hW
  refine ⟨hs,?_⟩
  symm
  apply eq_relativeCurrentProduct B hBc T hW
    (C := ({⊤} : Set (Opens M))) (fun x => ⟨⊤,mem_singleton _,trivial⟩)
    (fun _ => φ)
    (fun O => by have he : O.1 = ⊤ := mem_singleton_iff.mp O.2; simpa only [he] using hp)
    (fun O => by have he : O.1 = ⊤ := mem_singleton_iff.mp O.2; simpa only [he] using hmO)
  intro O e
  have hread := restrict_relativeNonPluripolarProduct (B.inChart e) (B.isPositive e) (hBc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)
    (chartDomain_le e O.1)
  exact hread

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.exists_relative_source_product_of_global_potentials
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_relative_source_product_of_global_potentials

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_04

-- Exact frozen body: RelativeCoordinateSourceGeometryDraft
section OriginalFragment_05

/-! The genuine coordinate-ball manifold and its original source PSH/current
expressions. The induced atlas is the actual restriction of identity charts. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalCurrentL1Ddc LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

def coordinateBallChart : ComplexChart 2 coordinateBall :=
  complexChartAt ⟨0, by change (0 : ComplexModel 2) ∈ ball 0 1; simp⟩

theorem coordinateBall_chart_unique (e : ComplexChart 2 coordinateBall) : e = coordinateBallChart := by
  apply Subtype.ext
  obtain ⟨x,hx⟩ := exists_eq_subtypeRestr coordinateBall e
  rw [hx]
  rfl

theorem coordinateBall_chartTarget (e : ComplexChart 2 coordinateBall) : chartTarget e = coordinateBall := by
  rw [chartTarget_eq_chartDomain coordinateBall e]
  ext z
  change z ∈ (ambientChart coordinateBall e).val.target ∩
    (ambientChart coordinateBall e).val.symm ⁻¹' coordinateBall ↔ z ∈ coordinateBall
  change z ∈ (Set.univ : Set (ComplexModel 2)) ∩ id ⁻¹' coordinateBall ↔ z ∈ coordinateBall
  simp only [univ_inter]
  rfl

theorem coordinateBall_chart_symm (e : ComplexChart 2 coordinateBall) {z : ComplexModel 2}
    (hz : z ∈ chartTarget e) : ((e.val.symm z : coordinateBall) : ComplexModel 2) = z := by
  rw [coe_symm_eq_ambient coordinateBall e hz]
  rfl

private theorem coordinateBall_chart_apply (e : ComplexChart 2 coordinateBall) (x : coordinateBall) :
    e.val x = (x : ComplexModel 2) := by
  rw [apply_eq_ambient coordinateBall e x]
  rfl

private theorem coordinateBall_chart_source (e : ComplexChart 2 coordinateBall) (x : coordinateBall) :
    x ∈ e.val.source := by
  have he : e = complexChartAt x :=
    (coordinateBall_chart_unique e).trans (coordinateBall_chart_unique (complexChartAt x)).symm
  rw [he]
  exact mem_complexChartAt_source x

/-- Original L1-PSH on the actual unit ball gives the original source PSH
function on the genuine induced ball manifold, with finite points produced. -/
theorem coordinateBall_manifoldPSH {u : ComplexModel 2 → EReal}
    (hu : IsL1PshOn coordinateBall u) :
    SGPT.PSH.ManifoldPSH (n := 2) (fun x : coordinateBall => u x) := by
  intro x
  refine ⟨coordinateBallChart,coordinateBall_chart_source _ x,
    coordinateBall,coordinateBall.isOpen,isConnected_ball (by norm_num : 0 < (1 : ℝ)),
    ?_,?_,?_⟩
  · change (coordinateBall : Set (ComplexModel 2)) ⊆ (chartTarget coordinateBallChart : Set _)
    rw [coordinateBall_chartTarget]
  · rw [coordinateBall_chart_apply]
    exact x.2
  · have hEq : EqOn u (chartFunction (fun x : coordinateBall => u x) coordinateBallChart)
        coordinateBall := by
      intro z hz
      change u z = u ((coordinateBallChart.val.symm z : coordinateBall) : ComplexModel 2)
      rw [coordinateBall_chart_symm coordinateBallChart (by rwa [coordinateBall_chartTarget])]
    refine ⟨hu.psh.discPshOn.congr hEq,?_⟩
    have hfreq := (hu.frequently_ne_bot (x : ComplexModel 2) x.2).and_eventually
      (coordinateBall.isOpen.mem_nhds x.2)
    obtain ⟨z,hzu,hz⟩ := hfreq.exists
    exact ⟨z,hz,by rwa [← hEq hz]⟩

/-- Exact actual current expression of the SAME original ddc current on the
ball manifold; every coefficient remains the original restricted ddcL1. -/
theorem coordinateBall_ddc_inChart {u : ComplexModel 2 → EReal}
    (hu : IsL1PshOn coordinateBall u) (e : ComplexChart 2 coordinateBall) :
    (ddcCurrent 1 (fun x : coordinateBall => u x) (coordinateBall_manifoldPSH hu)).inChart e =
      restrict (show chartTarget e ≤ coordinateBall by rw [coordinateBall_chartTarget])
        (ddcL1 coordinateBall u) := by
  rw [ddcCurrent_inChart, restrict_ddcL1 _ hu.locallyIntegrableOn]
  exact ddcL1_congr (isL1PshOn_chart (coordinateBall_manifoldPSH hu) e).locallyIntegrableOn
    (hu.mono (by rw [coordinateBall_chartTarget])).locallyIntegrableOn
    (fun z hz => congrArg u (coordinateBall_chart_symm e hz))

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.coordinateBallChart
#check @SGPT.NPP.RelativeNonPluripolar.coordinateBall_chart_unique
#check @SGPT.NPP.RelativeNonPluripolar.coordinateBall_chartTarget
#check @SGPT.NPP.RelativeNonPluripolar.coordinateBall_chart_symm
#check @SGPT.NPP.RelativeNonPluripolar.coordinateBall_manifoldPSH
#check @SGPT.NPP.RelativeNonPluripolar.coordinateBall_ddc_inChart
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateBallChart
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateBall_chart_unique
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateBall_chartTarget
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateBall_chart_symm
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateBall_manifoldPSH
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateBall_ddc_inChart

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_05

-- Exact frozen body: RelativeCoordinateIntrinsicDraft
section OriginalFragment_06

/-! Exact source current-factor readback of the genuine coordinate example.
The original divisor base is the actual ddc current on the induced unit ball. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalCurrentL1Ddc
open LocalBedfordTaylorLocality LocalBedfordTaylorProducts
open SGPT.NPP.NonPluripolarCurrent

def coordinateSourceBase : PositiveCurrent 2 coordinateBall 1 :=
  ddcCurrent 1 (fun x : coordinateBall => coordinateLog x)
    (coordinateBall_manifoldPSH coordinateLog_isL1Psh)

theorem isClosed_coordinateSourceBase : coordinateSourceBase.IsClosed :=
  isClosed_ddcCurrent (coordinateBall_manifoldPSH coordinateLog_isL1Psh)

/-- Exact actual integration-current readback of the ORIGINAL global base. -/
theorem coordinateSourceBase_inChart (e : ComplexChart 2 coordinateBall) :
    coordinateSourceBase.inChart e =
      restrict (show chartTarget e ≤ coordinateBall by rw [coordinateBall_chartTarget])
        coordinateDivisorCurrent := coordinateBall_ddc_inChart coordinateLog_isL1Psh e

private theorem coordinate_relative_chart_mass_readback
    (u : ComplexModel 2 → EReal) (hu : IsL1PshOn coordinateBall u)
    (hm : HasFiniteRelativeMass (p := 1) (r := 0) coordinateDivisorCurrent
      isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => u) (fun _ => hu.psh)) (e : ComplexChart 2 coordinateBall) :
    ∃ hmE : HasFiniteRelativeMass (p := 1) (r := 0)
        (coordinateSourceBase.inChart e) (coordinateSourceBase.isPositive e)
        (isClosed_coordinateSourceBase e)
        (fun _ : Fin 1 => fun z => u ((e.val.symm z : coordinateBall) : ComplexModel 2))
        (chartPlurisubharmonicOn (fun _ : Fin 1 => coordinateBall_manifoldPSH hu) e),
      (relativeNonPluripolarProduct (p := 1) (r := 0)
        (coordinateSourceBase.inChart e) (coordinateSourceBase.isPositive e)
        (isClosed_coordinateSourceBase e)
        (fun _ : Fin 1 => fun z => u ((e.val.symm z : coordinateBall) : ComplexModel 2))
        (chartPlurisubharmonicOn (fun _ : Fin 1 => coordinateBall_manifoldPSH hu) e) hmE).val =
      restrict (show chartTarget e ≤ coordinateBall by rw [coordinateBall_chartTarget])
        (relativeNonPluripolarProduct (p := 1) (r := 0) coordinateDivisorCurrent
          isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
          (fun _ : Fin 1 => u) (fun _ => hu.psh) hm).val := by
  let hle : chartTarget e ≤ coordinateBall := by rw [coordinateBall_chartTarget]
  have key : ∀ (R : LocalProductCurrent 2 (chartTarget e) 1)
      (hR : IsPositive R) (hRc : IsClosedAny 1 R),
      R = restrict hle coordinateDivisorCurrent →
      ∃ hmE : HasFiniteRelativeMass (p := 1) (r := 0) R hR hRc
          (fun _ : Fin 1 => fun z => u ((e.val.symm z : coordinateBall) : ComplexModel 2))
          (chartPlurisubharmonicOn (fun _ : Fin 1 => coordinateBall_manifoldPSH hu) e),
        (relativeNonPluripolarProduct (p := 1) (r := 0) R hR hRc
          (fun _ : Fin 1 => fun z => u ((e.val.symm z : coordinateBall) : ComplexModel 2))
          (chartPlurisubharmonicOn (fun _ : Fin 1 => coordinateBall_manifoldPSH hu) e) hmE).val =
        restrict hle (relativeNonPluripolarProduct (p := 1) (r := 0)
          coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
          (fun _ : Fin 1 => u) (fun _ => hu.psh) hm).val := by
    rintro R hR hRc rfl
    have hmR := hasFiniteRelativeMass_restrict (p := 1) (r := 0) coordinateDivisorCurrent
      isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => u) (fun _ => hu.psh) hm hle
    have hc := relative_mass_product_congr (p := 1) (r := 0) (restrict hle coordinateDivisorCurrent) hR hRc
      (fun _ : Fin 1 => u)
      (fun _ : Fin 1 => fun z => u ((e.val.symm z : coordinateBall) : ComplexModel 2))
      (fun _ => hu.psh.mono hle)
      (chartPlurisubharmonicOn (fun _ : Fin 1 => coordinateBall_manifoldPSH hu) e)
      (fun _ z hz => congrArg u (coordinateBall_chart_symm e hz).symm)
    have hmE := hc.1.mp hmR
    exact ⟨hmE,(hc.2 hmR hmE).symm.trans
      (restrict_relativeNonPluripolarProduct (p := 1) (r := 0) coordinateDivisorCurrent
        isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
        (fun _ : Fin 1 => u) (fun _ => hu.psh) hm hle).symm⟩
  exact key _ _ _ (coordinateSourceBase_inChart e)

/-- Actual local trace mass manufactures the FULL original source cover
criterion, and its SAME intrinsic current retains the original coordinate
relative current against the SAME actual integration-current base. -/
theorem exists_coordinate_intrinsic_source_readback
    (u : ComplexModel 2 → EReal) (hu : IsL1PshOn coordinateBall u)
    (hm : HasFiniteRelativeMass (p := 1) (r := 0) coordinateDivisorCurrent
      isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => u) (fun _ => hu.psh)) :
    ∃ hs : IsRelativeCurrentProductSourceWellDefined (m := 1) (p := 1) (r := 0)
        coordinateSourceBase isClosed_coordinateSourceBase
        (fun _ : Fin 1 => ddcCurrent 1 (fun x : coordinateBall => u x) (coordinateBall_manifoldPSH hu)),
      ∀ e : ComplexChart 2 coordinateBall,
        (relativeCurrentProductOfSourceOpens (m := 1) (p := 1) (r := 0) coordinateSourceBase isClosed_coordinateSourceBase
          (fun _ : Fin 1 => ddcCurrent 1 (fun x : coordinateBall => u x) (coordinateBall_manifoldPSH hu))
          hs).inChart e =
        restrict (show chartTarget e ≤ coordinateBall by rw [coordinateBall_chartTarget])
          (relativeNonPluripolarProduct (p := 1) (r := 0) coordinateDivisorCurrent
            isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
            (fun _ : Fin 1 => u) (fun _ => hu.psh) hm).val := by
  have hchart := coordinate_relative_chart_mass_readback u hu hm
  have hglobal : HasFiniteGlobalRelativeMass (p := 1) (r := 0)
      coordinateSourceBase isClosed_coordinateSourceBase
      (fun _ : Fin 1 => fun x : coordinateBall => u x)
      (fun _ => coordinateBall_manifoldPSH hu) := fun e => (hchart e).choose
  obtain ⟨hs,heq⟩ := exists_relative_source_product_of_global_potentials (m := 1) (p := 1) (r := 0)
    coordinateSourceBase isClosed_coordinateSourceBase
    (fun _ : Fin 1 => fun x : coordinateBall => u x) (fun _ => coordinateBall_manifoldPSH hu) hglobal
  refine ⟨hs,fun e => ?_⟩
  rw [heq]
  exact (hchart e).choose_spec

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.coordinateSourceBase
#check @SGPT.NPP.RelativeNonPluripolar.isClosed_coordinateSourceBase
#check @SGPT.NPP.RelativeNonPluripolar.coordinateSourceBase_inChart
#check @SGPT.NPP.RelativeNonPluripolar.exists_coordinate_intrinsic_source_readback
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSourceBase
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_coordinateSourceBase
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSourceBase_inChart
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_coordinate_intrinsic_source_readback

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_06

-- Exact frozen body: RelativeIntrinsicNonlinearityDraft
section OriginalFragment_07

/-! A ZERO-INPUT failure of addition of the SAME intrinsic source current-factor
relative product. Every source domain and current is manufactured from the
actual unit-ball divisor example, and the original compact test is retained. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalCurrentL1Ddc
open LocalBedfordTaylorLocality LocalBedfordTaylorProducts
open SGPT.NPP.NonPluripolarCurrent

/-- Read the actual identity coordinate of the original ball-manifold current
on its SAME original unit-ball domain, without a new current model. -/
def coordinateSourceReading {q : ℕ} (S : PositiveCurrent 2 coordinateBall q) :
    LocalProductCurrent 2 coordinateBall q :=
  restrict (show coordinateBall ≤ chartTarget coordinateBallChart by rw [coordinateBall_chartTarget])
    (S.inChart coordinateBallChart)

private theorem restrict_current_self {n q : ℕ} {U : Opens (ComplexModel n)}
    (S : LocalProductCurrent n U q) : restrict (le_refl U) S = S := by
  ext γ φ
  change S γ (extTest (le_refl U) φ) = S γ φ
  have he : extTest (le_refl U) φ = φ := by
    ext x
    exact extTest_apply (le_refl U) φ x
  rw [he]

private theorem coordinateSourceReading_of_inChart {q : ℕ}
    (S : PositiveCurrent 2 coordinateBall q) (R : LocalProductCurrent 2 coordinateBall q)
    (h : S.inChart coordinateBallChart =
      restrict (show chartTarget coordinateBallChart ≤ coordinateBall by rw [coordinateBall_chartTarget]) R) :
    coordinateSourceReading S = R := by
  unfold coordinateSourceReading
  rw [h, restrict_restrict]
  exact restrict_current_self R

def coordinateSourceSmoothFactor : PositiveCurrent 2 coordinateBall 1 :=
  ddcCurrent 1 (fun x : coordinateBall => (coordinateSmoothPotential x : EReal))
    (coordinateBall_manifoldPSH coordinateSmoothPotential_isL1Psh)

def coordinateSourceSumFactor : PositiveCurrent 2 coordinateBall 1 :=
  ddcCurrent 1 (fun x : coordinateBall => coordinateSumPotential x)
    (coordinateBall_manifoldPSH coordinateSumPotential_isL1Psh)

/-- Actual factor-current addition in EVERY original chart, hence on all
original tensor coefficients and compact tests, not a scalar surrogate. -/
theorem coordinateSourceFactors_actual_add (e : ComplexChart 2 coordinateBall) :
    coordinateSourceSumFactor.inChart e =
      coordinateSourceBase.inChart e + coordinateSourceSmoothFactor.inChart e := by
  rw [coordinateSourceBase_inChart]
  change (ddcCurrent 1 _ (coordinateBall_manifoldPSH coordinateSumPotential_isL1Psh)).inChart e =
    LocalBedfordTaylorLocality.restrict (show chartTarget e ≤ coordinateBall by rw [coordinateBall_chartTarget]) coordinateDivisorCurrent +
      (ddcCurrent 1 _ (coordinateBall_manifoldPSH coordinateSmoothPotential_isL1Psh)).inChart e
  rw [coordinateBall_ddc_inChart coordinateSumPotential_isL1Psh e,
    coordinateBall_ddc_inChart coordinateSmoothPotential_isL1Psh e]
  rw [coordinate_source_current_add]
  rfl

/-- The source potential-cover domain is internally produced from actual
relative mass of the original coordinate current, not a comparison premise. -/
theorem coordinateIntrinsicSourceDomain (u : ComplexModel 2 → EReal)
    (hu : IsL1PshOn coordinateBall u)
    (hm : HasFiniteRelativeMass (p := 1) (r := 0) coordinateDivisorCurrent
      isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => u) (fun _ => hu.psh)) :
    IsRelativeCurrentProductSourceWellDefined (m := 1) (p := 1) (r := 0)
      coordinateSourceBase isClosed_coordinateSourceBase
      (fun _ : Fin 1 => ddcCurrent 1 (fun x : coordinateBall => u x) (coordinateBall_manifoldPSH hu)) :=
  (exists_coordinate_intrinsic_source_readback u hu hm).choose

/-- EXACTLY the same intrinsic source-defined current-factor product. -/
def coordinateIntrinsicRelativeProduct (u : ComplexModel 2 → EReal)
    (hu : IsL1PshOn coordinateBall u)
    (hm : HasFiniteRelativeMass (p := 1) (r := 0) coordinateDivisorCurrent
      isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => u) (fun _ => hu.psh)) : PositiveCurrent 2 coordinateBall 0 :=
  relativeCurrentProductOfSourceOpens (m := 1) (p := 1) (r := 0)
    coordinateSourceBase isClosed_coordinateSourceBase
    (fun _ : Fin 1 => ddcCurrent 1 (fun x : coordinateBall => u x) (coordinateBall_manifoldPSH hu))
    (coordinateIntrinsicSourceDomain u hu hm)

/-- The SAME intrinsic source product reads back to the frozen original
coordinate relative product against its actual integration-current base. -/
theorem coordinateIntrinsicRelativeProduct_readback (u : ComplexModel 2 → EReal)
    (hu : IsL1PshOn coordinateBall u)
    (hm : HasFiniteRelativeMass (p := 1) (r := 0) coordinateDivisorCurrent
      isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
      (fun _ : Fin 1 => u) (fun _ => hu.psh)) :
    coordinateSourceReading (coordinateIntrinsicRelativeProduct u hu hm) =
      (relativeNonPluripolarProduct (p := 1) (r := 0) coordinateDivisorCurrent
        isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
        (fun _ : Fin 1 => u) (fun _ => hu.psh) hm).val := by
  exact coordinateSourceReading_of_inChart _ _
    ((exists_coordinate_intrinsic_source_readback u hu hm).choose_spec coordinateBallChart)

/-- No original domain, current, compatibility, nonzero coefficient or test
certificate is an input: actual source products of the genuine original
factor currents fail addition on an internally produced compact test. -/
theorem coordinate_intrinsic_source_actual_nonadditivity :
    coordinateSourceBase.IsClosed ∧ coordinateSourceSmoothFactor.IsClosed ∧
      coordinateSourceSumFactor.IsClosed ∧
      (∀ e : ComplexChart 2 coordinateBall,
        coordinateSourceSumFactor.inChart e =
          coordinateSourceBase.inChart e + coordinateSourceSmoothFactor.inChart e) ∧
      ∃ φ : 𝓓(coordinateBall, ℝ),
        coordinateSourceReading (coordinateIntrinsicRelativeProduct coordinateSumPotential
          coordinateSumPotential_isL1Psh coordinateSum_relative_mass) (kahlerPower 2 0) φ ≠
        coordinateSourceReading (coordinateIntrinsicRelativeProduct coordinateLog
          coordinateLog_isL1Psh coordinateLog_relative_mass) (kahlerPower 2 0) φ +
        coordinateSourceReading (coordinateIntrinsicRelativeProduct
          (fun x => (coordinateSmoothPotential x : EReal)) coordinateSmoothPotential_isL1Psh
          (hasFiniteRelativeMass_of_isLocallyBoundedPshOn (p := 1) (r := 0)
            coordinateDivisorCurrent isPositive_coordinateDivisorCurrent isClosed_coordinateDivisorCurrent
            (fun _ : Fin 1 => coordinateSmoothPotential)
            (fun _ => coordinateSmoothPotential_locallyBoundedPsh))) (kahlerPower 2 0) φ := by
  refine ⟨isClosed_coordinateSourceBase,
    isClosed_ddcCurrent (coordinateBall_manifoldPSH coordinateSmoothPotential_isL1Psh),
    isClosed_ddcCurrent (coordinateBall_manifoldPSH coordinateSumPotential_isL1Psh),
    coordinateSourceFactors_actual_add,?_⟩
  obtain ⟨φ,hφ⟩ := coordinate_actual_relative_nonadditivity.2.2.2.2.2
  refine ⟨φ,?_⟩
  rw [coordinateIntrinsicRelativeProduct_readback,coordinateIntrinsicRelativeProduct_readback,
    coordinateIntrinsicRelativeProduct_readback]
  exact hφ

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.coordinateSourceReading
#check @SGPT.NPP.RelativeNonPluripolar.coordinateSourceSmoothFactor
#check @SGPT.NPP.RelativeNonPluripolar.coordinateSourceSumFactor
#check @SGPT.NPP.RelativeNonPluripolar.coordinateSourceFactors_actual_add
#check @SGPT.NPP.RelativeNonPluripolar.coordinateIntrinsicSourceDomain
#check @SGPT.NPP.RelativeNonPluripolar.coordinateIntrinsicRelativeProduct
#check @SGPT.NPP.RelativeNonPluripolar.coordinateIntrinsicRelativeProduct_readback
#check @SGPT.NPP.RelativeNonPluripolar.coordinate_intrinsic_source_actual_nonadditivity
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSourceReading
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSourceSmoothFactor
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSourceSumFactor
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateSourceFactors_actual_add
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateIntrinsicSourceDomain
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateIntrinsicRelativeProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinateIntrinsicRelativeProduct_readback
#print axioms SGPT.NPP.RelativeNonPluripolar.coordinate_intrinsic_source_actual_nonadditivity

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_07
