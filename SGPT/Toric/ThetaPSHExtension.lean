import SGPT.PSH.GlobalQPSH
import SGPT.PSH.GrauertRemmertBounded
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- The source universal local-potential condition on the original actual
open subset. Values of its ambient representative outside it are unrestricted. -/
def IsThetaPSHOn (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) (U : Set X) : Prop :=
  (∀ x ∈ U, u x ≠ ⊤) ∧ ∀ (V : Set X) (g : X → ℝ), V ⊆ U →
    A.IsAtlasLocalPotential θ V g → A.IsPSHOn (fun x ↦ u x + (g x : EReal)) V

/-- Genuine local smooth potentials retain their full form identity on an
actual smaller open domain. -/
theorem IsAtlasLocalPotential.mono {θ : AtlasClosedRealOneOneForm A}
    {U V : Set X} {g : X → ℝ} (hg : A.IsAtlasLocalPotential θ U g)
    (hV : IsOpen V) (hVU : V ⊆ U) : A.IsAtlasLocalPotential θ V g := by
  refine ⟨hV, ?_, ?_⟩
  · intro i
    exact (hg.2.1 i).mono (fun _ hz ↦ ⟨hz.1, hVU hz.2⟩)
  · intro i z hz
    exact hg.2.2 i ⟨hz.1, hVU hz.2⟩

/-- A genuine global original theta-PSH function passes every relative test. -/
theorem IsThetaPSH.isThetaPSHOn {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : A.IsThetaPSH θ u) (U : Set X) : A.IsThetaPSHOn θ u U :=
  ⟨fun x _ ↦ hu.1 x, fun V g _ hg ↦ hu.2 V g hg⟩

/-- Actual canonical filling commutes pointwise with finite continuous
corrections, reusing the genuine whole upper-regularization covariance. -/
theorem analyticExtension_add_coe_apply (Z : Set X) (u : X → EReal)
    {g : X → ℝ} {x : X} (hg : ContinuousAt g x) :
    analyticExtension Z (fun y ↦ u y + (g y : EReal)) x =
      analyticExtension Z u x + (g x : EReal) := by
  have heq : (fun y ↦ if y ∈ Z then (⊥ : EReal) else u y + (g y : EReal)) =
      (fun y ↦ (if y ∈ Z then (⊥ : EReal) else u y) + (g y : EReal)) := by
    funext y
    by_cases hy : y ∈ Z <;> simp [hy]
  rw [analyticExtension, heq, uscRegularization_add_coe_continuousAt_apply _ hg]
  rfl

/-- Each actual local potential yields genuine original off-boundary PSH,
without supplying a corrected-PSH certificate as an additional premise. -/
theorem IsThetaPSHOn.corrected_off {θ : AtlasClosedRealOneOneForm A}
    {Z U : Set X} {u : X → EReal} (hu : A.IsThetaPSHOn θ u Zᶜ)
    (hZ : IsClosed Z) {g : X → ℝ} (hg : A.IsAtlasLocalPotential θ U g) :
    A.IsPSHOn (fun x ↦ u x + (g x : EReal)) (U \ Z) := by
  exact hu.2 (U \ Z) g (fun _ hz ↦ hz.2)
    (hg.mono (hg.1.sdiff hZ) sdiff_subset)


/-- Finite correction covariance in the actual chart identifies the genuine
corrected fill with the same canonical manifold fill. -/
theorem coordinate_analyticExtension_add_coe (Z : Set X) (u : X → EReal)
    (i : A.Index) {g : X → ℝ} {z : ComplexModel (A.dimension i)}
    (hz : z ∈ (A.chart i).target) (hg : ContinuousAt (g ∘ (A.chart i).symm) z) :
    A.coordinate (analyticExtension Z u) i z + (g ((A.chart i).symm z) : EReal) =
      Pending.PshCodimTwoExtension.extension ((A.chart i).symm ⁻¹' Z)
        (A.coordinate (fun x ↦ u x + (g x : EReal)) i) z := by
  rw [A.coordinate_analyticExtension Z u i hz]
  exact (analyticExtension_add_coe_apply ((A.chart i).symm ⁻¹' Z)
    (A.coordinate u i) hg).symm

/-- Genuine original local potentials identify the canonical off-set
values without any assumed upper semicontinuity of the uncorrected function. -/
theorem IsThetaPSHOn.analyticExtension_eq_off {θ : AtlasClosedRealOneOneForm A}
    {Z : Set X} {u : X → EReal} (hu : A.IsThetaPSHOn θ u Zᶜ)
    (hZ : IsClosed Z) {x : X} (hx : x ∉ Z) : analyticExtension Z u x = u x := by
  obtain ⟨U, g, hxU, hg⟩ := exists_atlas_local_potential θ x
  obtain ⟨i, hi⟩ := A.cover x
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
  let S := (A.chart i).symm ⁻¹' Z
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hg.1
  have hDS : IsOpen (D \ S) := by
    simpa only [D, S, sdiff_eq, preimage_compl, preimage_inter, inter_assoc] using
      (A.chart i).isOpen_inter_preimage_symm (hg.1.sdiff hZ)
  have hp : PlurisubharmonicOn
      (A.coordinate (fun y ↦ u y + (g y : EReal)) i) (D \ S) := by
    intro z hz
    exact (hu.corrected_off hZ hg).chartPlurisubharmonic i z ⟨hz.1.1, hz.1.2, hz.2⟩
  have hz : A.chart i x ∈ D := ⟨(A.chart i).map_source hi,
    by simpa only [mem_preimage, (A.chart i).left_inv hi] using hxU⟩
  have hzS : A.chart i x ∉ S := by
    simpa only [S, mem_preimage, (A.chart i).left_inv hi] using hx
  have hc : ContinuousAt (g ∘ (A.chart i).symm) (A.chart i x) :=
    ((hg.2.1 i).continuousOn _ hz).continuousAt (hD.mem_nhds hz)
  have he := (coordinate_analyticExtension_add_coe Z u i hz.1 hc).trans
    (Pending.PshCodimTwoExtension.extension_eq hp hDS ⟨hz, hzS⟩)
  change analyticExtension Z u ((A.chart i).symm (A.chart i x)) +
      (g ((A.chart i).symm (A.chart i x)) : EReal) =
    u ((A.chart i).symm (A.chart i x)) +
      (g ((A.chart i).symm (A.chart i x)) : EReal) at he
  rw [(A.chart i).left_inv hi] at he
  exact le_antisymm
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp he.le)
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp he.ge)

/-- Actual local finite bounds exclude top in the independently constructed
canonical fill, including zero-dimensional charts. -/
theorem analyticExtension_ne_top_of_locallyBounded {Z : Set X} {u : X → EReal}
    (hb : LocallyBoundedAboveOff Z u) (x : X) : analyticExtension Z u x ≠ ⊤ := by
  obtain ⟨U, hU, C, hC⟩ := hb x
  have hle : analyticExtension Z u x ≤ (C : EReal) := by
    apply (uscRegularization_le_localSup
      (fun y ↦ if y ∈ Z then (⊥ : EReal) else u y) hU).trans
    refine iSup₂_le fun y hy ↦ ?_
    by_cases hyZ : y ∈ Z
    · simp [hyZ]
    · simpa only [if_neg hyZ] using hC y hy hyZ
  exact ne_of_lt (hle.trans_lt (EReal.coe_lt_top C))


/-- Each original genuine local potential has an actually PSH corrected
fill in every true chart, by existing analytic removability and finite covariance. -/
theorem IsThetaPSHOn.chart_corrected_analyticExtension
    {θ : AtlasClosedRealOneOneForm A} {Z : Set X} {u : X → EReal}
    (hu : A.IsThetaPSHOn θ u Zᶜ) (hZ : IsClosed Z)
    (hEq : A.HasAnalyticChartEquations Z) (hb : LocallyBoundedAboveOff Z u)
    {U : Set X} {g : X → ℝ} (hg : A.IsAtlasLocalPotential θ U g) (i : A.Index) :
    PlurisubharmonicOn (A.coordinate (fun x ↦ analyticExtension Z u x + (g x : EReal)) i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
  intro z hz
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
  let S := (A.chart i).symm ⁻¹' Z
  let σ := g ∘ (A.chart i).symm
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hg.1
  obtain ⟨W, hW, hzW, hWt, N, f, hf, hfZ⟩ := hEq i z hz.1
  let R := W ∩ D
  have hR : IsOpen R := hW.inter hD
  have hp : PlurisubharmonicOn
      (A.coordinate (fun x ↦ u x + (g x : EReal)) i) (R \ S) := by
    intro y hy
    exact (hu.corrected_off hZ hg).chartPlurisubharmonic i y ⟨hy.1.2.1, hy.1.2.2, hy.2⟩
  have hbound : Pending.PshHypersurfaceRemovable.LocallyBoundedAboveOff S R
      (A.coordinate (fun x ↦ u x + (g x : EReal)) i) := by
    intro y hy
    obtain ⟨V, hV, C, hC⟩ := hb ((A.chart i).symm y)
    have hc : ContinuousAt σ y :=
      ((hg.2.1 i).continuousOn _ hy.2).continuousAt (hD.mem_nhds hy.2)
    have hgBound : {t | σ t < σ y + 1} ∈ 𝓝 y :=
      hc.eventually_lt_const (by linarith : σ y < σ y + 1)
    refine ⟨(A.chart i).symm ⁻¹' V ∩ {t | σ t < σ y + 1},
      inter_mem (((A.chart i).continuousAt_symm hy.2.1).preimage_mem_nhds hV) hgBound,
      C + (σ y + 1), ?_⟩
    intro t ht htS
    have hraw : u ((A.chart i).symm t) ≤ (C : EReal) :=
      hC ((A.chart i).symm t) ht.1 htS
    have hfinite : (σ t : EReal) ≤ ((σ y + 1 : ℝ) : EReal) := by exact_mod_cast ht.2.le
    simpa only [coordinate, Function.comp_apply, σ, ← EReal.coe_add] using
      add_le_add hraw hfinite
  have hext := Pending.PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus
    hR hp hbound (fun j ↦ (hf j).mono inter_subset_left)
    (fun y hy ↦ hfZ y hy.1)
  apply (hext z ⟨hzW, hz⟩).congr
  filter_upwards [hD.mem_nhds hz] with y hy
  have hc : ContinuousAt (g ∘ (A.chart i).symm) y :=
    ((hg.2.1 i).continuousOn _ hy).continuousAt (hD.mem_nhds hy)
  exact (coordinate_analyticExtension_add_coe Z u i hy.1 hc).symm


/-- Actual off-set source witnesses preserve nondegeneracy of each genuine
corrected fill on its original domain. -/
theorem IsThetaPSHOn.corrected_analyticExtension_nondegenerate
    {θ : AtlasClosedRealOneOneForm A} {Z : Set X} {u : X → EReal}
    (hu : A.IsThetaPSHOn θ u Zᶜ) (hZ : IsClosed Z) (hproper : interior Z = ∅)
    {U : Set X} {g : X → ℝ} (hg : A.IsAtlasLocalPotential θ U g) :
    LocallyNondegenerateOn (fun x ↦ analyticExtension Z u x + (g x : EReal)) U := by
  intro x hx O hO hxO
  obtain ⟨i, hi⟩ := A.cover x
  let W := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ O)
  have hW : IsOpen W := (A.chart i).isOpen_inter_preimage_symm (hg.1.inter hO)
  have hxW : A.chart i x ∈ W := ⟨(A.chart i).map_source hi,
    by simpa only [mem_preimage, (A.chart i).left_inv hi] using (show x ∈ U ∩ O from ⟨hx, hxO⟩)⟩
  obtain ⟨z, hzW, hzZ⟩ := A.exists_coordinate_off_of_empty_interior hproper i hW
    inter_subset_left hxW
  have hpsh := hu.corrected_off hZ hg
  obtain ⟨y, hy, hfin⟩ := (hpsh.locallyNondegenerate (hg.1.sdiff hZ))
    ((A.chart i).symm z) ⟨hzW.2.1, hzZ⟩ O hO hzW.2.2
  refine ⟨y, ⟨hy.1.1, hy.2⟩, ?_⟩
  change analyticExtension Z u y + (g y : EReal) ≠ ⊥
  rw [hu.analyticExtension_eq_off hZ hy.1.2]
  exact hfin

/-- The actual canonical extension passes every original local-potential
test, in arbitrary chart dimensions and without compactness. -/
theorem IsThetaPSHOn.analyticExtension_isThetaPSH
    {θ : AtlasClosedRealOneOneForm A} {Z : Set X} {u : X → EReal}
    (hu : A.IsThetaPSHOn θ u Zᶜ) (hEq : A.HasAnalyticChartEquations Z)
    (hproper : interior Z = ∅) (hb : LocallyBoundedAboveOff Z u) :
    A.IsThetaPSH θ (analyticExtension Z u) := by
  have hZ := hEq.isClosed A
  refine ⟨analyticExtension_ne_top_of_locallyBounded hb, ?_⟩
  intro U g hg
  apply (isPSHOn_iff_chart_and_nondegenerate hg.1).mpr
  exact ⟨hu.chart_corrected_analyticExtension hZ hEq hb hg,
    hu.corrected_analyticExtension_nondegenerate hZ hproper hg⟩

/-- Genuine source theta-PSH extensions are pointwise unique, by existing
original PSH chart-null rigidity and actual finite-correction cancellation. -/
theorem IsThetaPSHOn.analyticExtension_unique
    {θ : AtlasClosedRealOneOneForm A} {Z : Set X} {u v : X → EReal}
    (hu : A.IsThetaPSHOn θ u Zᶜ) (hEq : A.HasAnalyticChartEquations Z)
    (hproper : interior Z = ∅) (hb : LocallyBoundedAboveOff Z u)
    (hv : A.IsThetaPSH θ v) (heq : EqOn v u Zᶜ) : v = analyticExtension Z u := by
  have hZ := hEq.isClosed A
  have hpl := hEq.locallyPluripolar A hproper
  have hext := hu.analyticExtension_isThetaPSH hEq hproper hb
  funext x
  obtain ⟨U, g, hxU, hg⟩ := exists_atlas_local_potential θ x
  obtain ⟨i, hi⟩ := A.cover x
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hg.1
  have hvp := (hv.2 U g hg).chartPlurisubharmonic i
  have hep := (hext.2 U g hg).chartPlurisubharmonic i
  have hae : A.coordinate (fun y ↦ v y + (g y : EReal)) i =ᵐ[volume.restrict D]
      A.coordinate (fun y ↦ analyticExtension Z u y + (g y : EReal)) i := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
      (hpl.ae_notMem_in_chart i volume)] with z hzZ
    change v ((A.chart i).symm z) + (g ((A.chart i).symm z) : EReal) =
      analyticExtension Z u ((A.chart i).symm z) + (g ((A.chart i).symm z) : EReal)
    rw [hu.analyticExtension_eq_off hZ hzZ, heq hzZ]
  have hpoint := hvp.eqOn_of_ae_eq hep hD volume hae
    ⟨(A.chart i).map_source hi,
      by simpa only [mem_preimage, (A.chart i).left_inv hi] using hxU⟩
  change v ((A.chart i).symm (A.chart i x)) + (g ((A.chart i).symm (A.chart i x)) : EReal) =
    analyticExtension Z u ((A.chart i).symm (A.chart i x)) +
      (g ((A.chart i).symm (A.chart i x)) : EReal) at hpoint
  rw [(A.chart i).left_inv hi] at hpoint
  exact le_antisymm
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hpoint.le)
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hpoint.ge)


/-- Bounds are required only near the original exceptional points. Genuine
corrected PSH and smooth finite potentials produce bounds at all off-set points. -/
theorem IsThetaPSHOn.locallyBoundedAboveOff_of_near_exceptional
    {θ : AtlasClosedRealOneOneForm A} {Z : Set X} {u : X → EReal}
    (hu : A.IsThetaPSHOn θ u Zᶜ) (hZ : IsClosed Z)
    (hb : ∀ x ∈ Z, ∃ V : Set X, V ∈ 𝓝 x ∧ ∃ C : ℝ,
      ∀ y ∈ V, y ∉ Z → u y ≤ (C : EReal)) : LocallyBoundedAboveOff Z u := by
  intro x
  by_cases hxZ : x ∈ Z
  · exact hb x hxZ
  · obtain ⟨U, g, hxU, hg⟩ := exists_atlas_local_potential θ x
    obtain ⟨i, hi⟩ := A.cover x
    let σ := g ∘ (A.chart i).symm
    let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
    have hzD : A.chart i x ∈ D := ⟨(A.chart i).map_source hi,
      by simpa only [mem_preimage, (A.chart i).left_inv hi] using hxU⟩
    have hzOff : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U \ Z) :=
      ⟨hzD.1, hzD.2, by simpa only [mem_preimage, (A.chart i).left_inv hi] using hxZ⟩
    have hpsh := (hu.corrected_off hZ hg).chartPlurisubharmonic i (A.chart i x) hzOff
    obtain ⟨C, hC, _⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hpsh.ne_top)
    have hevP : ∀ᶠ z in 𝓝 (A.chart i x),
        A.coordinate (fun y ↦ u y + (g y : EReal)) i z < (C : EReal) :=
      hpsh.upperSemicontinuousAt C hC
    have hc : ContinuousAt σ (A.chart i x) :=
      ((hg.2.1 i).continuousOn _ hzD).continuousAt
        (((A.chart i).isOpen_inter_preimage_symm hg.1).mem_nhds hzD)
    let B : ℝ := -σ (A.chart i x) + 1
    have hevG : ∀ᶠ z in 𝓝 (A.chart i x), -σ z < B :=
      hc.neg.eventually_lt_const (by change -σ (A.chart i x) < -σ (A.chart i x) + 1; linarith)
    have hev : ∀ᶠ y in 𝓝 x, u y ≤ ((C + B : ℝ) : EReal) := by
      filter_upwards [((A.chart i).continuousAt hi).eventually (hevP.and hevG),
        (A.chart i).open_source.mem_nhds hi] with y hy hys
      have hraw : u y + (g y : EReal) ≤ (C : EReal) := by
        simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hys] using hy.1.le
      have hneg : ((-g y : ℝ) : EReal) ≤ (B : EReal) := by
        have hreal : -g y < B := by
          simpa only [σ, Function.comp_apply, (A.chart i).left_inv hys] using hy.2
        exact_mod_cast hreal.le
      calc
        u y = (u y + (g y : EReal)) + ((-g y : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
        _ ≤ (C : EReal) + (B : EReal) := add_le_add hraw hneg
        _ = _ := (EReal.coe_add C B).symm
    exact ⟨{y | u y ≤ ((C + B : ℝ) : EReal)}, hev, C + B, fun _ hy _ ↦ hy⟩

/-- Actual existence and pointwise uniqueness for the original near-boundary
bounded theta-PSH extension, with all witnesses produced internally. -/
theorem exists_unique_bounded_theta_analytic_extension
    {θ : AtlasClosedRealOneOneForm A} {Z : Set X} {u : X → EReal}
    (hu : A.IsThetaPSHOn θ u Zᶜ) (hEq : A.HasAnalyticChartEquations Z)
    (hproper : interior Z = ∅)
    (hb : ∀ x ∈ Z, ∃ V : Set X, V ∈ 𝓝 x ∧ ∃ C : ℝ,
      ∀ y ∈ V, y ∉ Z → u y ≤ (C : EReal)) :
    ∃! v : X → EReal, A.IsThetaPSH θ v ∧ EqOn v u Zᶜ := by
  have hZ := hEq.isClosed A
  have hbound := hu.locallyBoundedAboveOff_of_near_exceptional hZ hb
  refine ⟨analyticExtension Z u,
    ⟨hu.analyticExtension_isThetaPSH hEq hproper hbound,
      fun x hx ↦ hu.analyticExtension_eq_off hZ hx⟩, ?_⟩
  intro v hv
  exact hu.analyticExtension_unique hEq hproper hbound hv.1 hv.2

end SGPT.PSH.VariableComplexAtlas
