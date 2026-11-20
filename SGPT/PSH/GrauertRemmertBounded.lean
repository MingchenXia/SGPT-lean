import SGPT.PSH.Pluripolar
import SGPT.PSH.AtlasAE
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Classical

variable {X : Type*} [TopologicalSpace X]

/-- The actual original upper-regularized extension across the exceptional set. -/
def analyticExtension (Z : Set X) (u : X → EReal) : X → EReal :=
  uscRegularization (fun x => if x ∈ Z then ⊥ else u x)

/-- Literal finite holomorphic equations for the actual exceptional set in every chart. -/
def HasAnalyticChartEquations (A : VariableComplexAtlas X) (Z : Set X) : Prop :=
  ∀ (i : A.Index) (z : ComplexModel (A.dimension i)), z ∈ (A.chart i).target →
    ∃ (W : Set (ComplexModel (A.dimension i))), IsOpen W ∧ z ∈ W ∧
      W ⊆ (A.chart i).target ∧ ∃ (N : ℕ) (g : Fin N → ComplexModel (A.dimension i) → ℂ),
        (∀ j, DifferentiableOn ℂ (g j) W) ∧
          ∀ y ∈ W, (A.chart i).symm y ∈ Z ↔ ∀ j, g j y = 0

/-- The actual neighborhood bound on the original off-set values. -/
def LocallyBoundedAboveOff (Z : Set X) (u : X → EReal) : Prop :=
  ∀ x : X, ∃ U : Set X, U ∈ 𝓝 x ∧ ∃ C : ℝ, ∀ y ∈ U, y ∉ Z → u y ≤ (C : EReal)

variable (A : VariableComplexAtlas X)

/-- Upper regularization commutes with the actual chart inverse on its true target. -/
theorem coordinate_analyticExtension (Z : Set X) (u : X → EReal) (i : A.Index)
    {z : ComplexModel (A.dimension i)} (hz : z ∈ (A.chart i).target) :
    A.coordinate (analyticExtension Z u) i z =
      Pending.PshCodimTwoExtension.extension ((A.chart i).symm ⁻¹' Z) (A.coordinate u i) z := by
  simpa only [analyticExtension, coordinate, Pending.PshCodimTwoExtension.extension,
    Function.comp_def, mem_preimage] using
    (uscRegularization_comp_openPartialHomeomorph_apply
      (fun x => if x ∈ Z then (⊥ : EReal) else u x) (A.chart i).symm hz).symm

/-- The genuine original off-set values are retained, including poles. -/
theorem analyticExtension_eq_off {Z : Set X} (hZ : IsClosed Z) {u : X → EReal}
    (hu : A.IsPSHOn u Zᶜ) {x : X} (hx : x ∉ Z) : analyticExtension Z u x = u x := by
  obtain ⟨i, hi⟩ := A.cover x
  have htarget := (A.chart i).map_source hi
  have hp : PlurisubharmonicOn (A.coordinate u i)
      ((A.chart i).target \ (A.chart i).symm ⁻¹' Z) := by
    simpa only [sdiff_eq, preimage_compl] using hu.chartPlurisubharmonic i
  have hO : IsOpen ((A.chart i).target \ (A.chart i).symm ⁻¹' Z) := by
    simpa only [sdiff_eq, preimage_compl] using
      (A.chart i).isOpen_inter_preimage_symm hZ.isOpen_compl
  have hxO : A.chart i x ∈ (A.chart i).target \ (A.chart i).symm ⁻¹' Z :=
    ⟨htarget, by simpa only [mem_preimage, (A.chart i).left_inv hi] using hx⟩
  have h := Pending.PshCodimTwoExtension.extension_eq hp hO hxO
  rw [← A.coordinate_analyticExtension Z u i htarget] at h
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using h

/-- Reuse the actual analytic removable producer in independently varying chart dimensions. -/
theorem analyticExtension_isPSH {Z : Set X} (hZ : IsClosed Z)
    (hpl : A.LocallyPluripolar Z) (hEq : A.HasAnalyticChartEquations Z) {u : X → EReal}
    (hu : A.IsPSHOn u Zᶜ) (hb : LocallyBoundedAboveOff Z u) :
    A.IsPSH (analyticExtension Z u) := by
  apply A.psh_iff_chart_and_nondegenerate.mpr
  constructor
  · intro i z hz
    obtain ⟨W, hW, hzW, hWt, N, g, hg, hgZ⟩ := hEq i z hz
    let S : Set (ComplexModel (A.dimension i)) := (A.chart i).symm ⁻¹' Z
    have hp : PlurisubharmonicOn (A.coordinate u i) (W \ S) := by
      intro y hy
      exact hu.chartPlurisubharmonic i y ⟨hWt hy.1, hy.2⟩
    have hbound : Pending.PshHypersurfaceRemovable.LocallyBoundedAboveOff S W
        (A.coordinate u i) := by
      intro y hy
      obtain ⟨U, hU, C, hC⟩ := hb ((A.chart i).symm y)
      refine ⟨(A.chart i).symm ⁻¹' U,
        ((A.chart i).continuousAt_symm (hWt hy)).preimage_mem_nhds hU, C, ?_⟩
      intro t ht htS
      exact hC ((A.chart i).symm t) ht htS
    have hext := Pending.PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus
      hW hp hbound hg hgZ
    apply (hext z hzW).congr
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
    exact (A.coordinate_analyticExtension Z u i hy).symm
  · intro x O hO hxO
    obtain ⟨i, hi⟩ := A.cover x
    let W := (A.chart i).target ∩ (A.chart i).symm ⁻¹' O
    have hW : IsOpen W := (A.chart i).isOpen_inter_preimage_symm hO
    have hxW : A.chart i x ∈ W :=
      ⟨(A.chart i).map_source hi, by simpa only [mem_preimage, (A.chart i).left_inv hi] using hxO⟩
    obtain ⟨z, hzW, hzZ⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (hW.measure_pos volume ⟨_, hxW⟩).ne'
      (ae_restrict_of_ae_restrict_of_subset inter_subset_left (hpl.ae_notMem_in_chart i volume))
    obtain ⟨y, hy, hyfin⟩ := (hu.locallyNondegenerate hZ.isOpen_compl)
      ((A.chart i).symm z) hzZ O hO hzW.2
    refine ⟨y, hy.2, ?_⟩
    rw [A.analyticExtension_eq_off hZ hu hy.1]
    exact hyfin

/-- Source uniqueness uses actual chart outer nullity and genuine PSH rigidity. -/
theorem analyticExtension_unique {Z : Set X} (hZ : IsClosed Z)
    (hpl : A.LocallyPluripolar Z) (hEq : A.HasAnalyticChartEquations Z) {u v : X → EReal}
    (hu : A.IsPSHOn u Zᶜ) (hb : LocallyBoundedAboveOff Z u)
    (hv : A.IsPSH v) (he : EqOn v u Zᶜ) : v = analyticExtension Z u := by
  apply hv.eq_of_coordinateAEEq (A.analyticExtension_isPSH hZ hpl hEq hu hb)
  intro i
  filter_upwards [hpl.ae_notMem_in_chart i volume] with z hz
  change v ((A.chart i).symm z) = analyticExtension Z u ((A.chart i).symm z)
  rw [A.analyticExtension_eq_off hZ hu hz]
  exact he hz

/-- The exact original upper-limit formula is the infimum of actual neighborhood off-set suprema. -/
theorem analyticExtension_eq_neighborhood_sup (Z : Set X) (u : X → EReal) (x : X) :
    analyticExtension Z u x = ⨅ (V : Set X) (_ : V ∈ 𝓝 x), ⨆ y ∈ V \ Z, u y := by
  unfold analyticExtension uscRegularization
  apply iInf_congr
  intro V
  apply iInf_congr
  intro _hV
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    by_cases hyZ : y ∈ Z
    · simp [hyZ]
    · simp only [if_neg hyZ]
      exact le_iSup₂ (f := fun y (_ : y ∈ V \ Z) => u y) y ⟨hy, hyZ⟩
  · refine iSup₂_le fun y hy => ?_
    have h := le_iSup₂ (f := fun y (_ : y ∈ V) => if y ∈ Z then (⊥ : EReal) else u y) y hy.1
    simpa only [if_neg hy.2] using h

/-- The original upper limit is the actual complete-lattice filter limsup,
without a realification or a measurability premise. -/
theorem analyticExtension_eq_limsup (Z : Set X) (u : X → EReal) (x : X) :
    analyticExtension Z u x = limsup u (𝓝[Zᶜ] x) := by
  rw [analyticExtension_eq_neighborhood_sup]
  simpa only [nhdsWithin, sdiff_eq, id] using
    (((𝓝 x).basis_sets.inf_principal Zᶜ).limsup_eq_iInf_iSup (u := u)).symm

/-- Actual finite equations imply closedness on the original variable-dimensional manifold. -/
theorem HasAnalyticChartEquations.isClosed {Z : Set X}
    (hEq : A.HasAnalyticChartEquations Z) : IsClosed Z := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨i, hi⟩ := A.cover x
  obtain ⟨W, hW, hxW, hWt, N, g, hg, he⟩ := hEq i (A.chart i x) ((A.chart i).map_source hi)
  obtain ⟨j, hj⟩ : ∃ j, g j (A.chart i x) ≠ 0 := by
    by_contra! h
    exact hx (by simpa only [(A.chart i).left_inv hi] using (he _ hxW).mpr h)
  have hS : (A.chart i).source ∩ (A.chart i) ⁻¹' W ∈ 𝓝 x :=
    ((A.chart i).isOpen_inter_preimage hW).mem_nhds ⟨hi, hxW⟩
  have hcont : ContinuousAt (fun y => g j (A.chart i y)) x :=
    ((hg j).continuousOn.continuousAt (hW.mem_nhds hxW)).comp ((A.chart i).continuousAt hi)
  filter_upwards [hS, hcont.eventually_ne hj] with y hy hne
  intro hyZ
  exact hne ((he _ hy.2).mp (by simpa only [(A.chart i).left_inv hy.1] using hyZ) j)

/-- Positive codimension supplies actual off-set points in every genuine coordinate neighborhood. -/
theorem exists_coordinate_off_of_empty_interior {Z : Set X} (hZ : interior Z = ∅)
    (i : A.Index) {W : Set (ComplexModel (A.dimension i))} (hW : IsOpen W)
    (hWt : W ⊆ (A.chart i).target) {z : ComplexModel (A.dimension i)} (hz : z ∈ W) :
    ∃ y ∈ W, (A.chart i).symm y ∉ Z := by
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' W
  have hU : IsOpen U := (A.chart i).isOpen_inter_preimage hW
  have hxU : (A.chart i).symm z ∈ U :=
    ⟨(A.chart i).map_target (hWt hz), by
      change A.chart i ((A.chart i).symm z) ∈ W
      rwa [(A.chart i).right_inv (hWt hz)]⟩
  have hnot : ¬ U ⊆ Z := by
    intro hsub
    have hmem := mem_interior_iff_mem_nhds.mpr (mem_of_superset (hU.mem_nhds hxU) hsub)
    simp only [hZ, mem_empty_iff_false] at hmem
  obtain ⟨x, hx, hxZ⟩ := not_subset.mp hnot
  exact ⟨A.chart i x, hx.2, by simpa only [(A.chart i).left_inv hx.1] using hxZ⟩

/-- Analytic equations and positive codimension produce the genuine source pole witnesses internally. -/
theorem HasAnalyticChartEquations.locallyPluripolar {Z : Set X}
    (hEq : A.HasAnalyticChartEquations Z) (hproper : interior Z = ∅) : A.LocallyPluripolar Z := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  obtain ⟨W, hW, hxW, hWt, N, g, hg, he⟩ := hEq i (A.chart i x) ((A.chart i).map_source hi)
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp hW (A.chart i x) hxW
  let B := ball (A.chart i x) r
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' B
  let w : X → EReal := fun y => generatorLog g (A.chart i y)
  have hU : IsOpen U := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hxU : x ∈ U := ⟨hi, mem_ball_self hr⟩
  have hBt : B ⊆ (A.chart i).target := hB.trans hWt
  have hgP : PlurisubharmonicOn (generatorLog g) B := by
    intro z hz
    simpa only [EReal.coe_one, one_mul] using
      (Pending.plurisubharmonicAt_scaled_generatorLog
        ⟨B, isOpen_ball, hz, fun j => (hg j).mono hB⟩ (c := 1) one_pos)
  have hcP : PlurisubharmonicOn (A.coordinate w i) B := by
    intro z hz
    apply (hgP z hz).congr
    filter_upwards [(A.chart i).open_target.mem_nhds (hBt hz)] with y hy
    simp only [coordinate, w, Function.comp_apply, (A.chart i).right_inv hy]
  obtain ⟨z, hzB, hzZ⟩ := A.exists_coordinate_off_of_empty_interior hproper i isOpen_ball hBt
    (mem_ball_self hr)
  have hfin : A.coordinate w i z ≠ ⊥ := by
    simp only [coordinate, w, Function.comp_apply, (A.chart i).right_inv (hBt hzB)]
    intro hbot
    exact hzZ ((he z (hB hzB)).mpr ((generatorLog_eq_bot_iff g z).mp hbot))
  have hpsh : A.IsPSHOn w U := by
    intro y hy
    refine ⟨i, hy.1, B, isOpen_ball, isConnected_ball hr, ?_, hy.2,
      hcP.discPshOn, z, hzB, hfin⟩
    intro t ht
    exact ⟨hBt ht, (A.chart i).map_target (hBt ht),
      by
        change A.chart i ((A.chart i).symm t) ∈ B
        rwa [(A.chart i).right_inv (hBt ht)]⟩
  refine ⟨U, hU, hxU, w, hpsh, ?_⟩
  intro y hy
  apply (generatorLog_eq_bot_iff g (A.chart i y)).mpr
  exact (he _ (hB hy.2.2)).mp (by simpa only [(A.chart i).left_inv hy.2.1] using hy.1)

/-- The original near-exceptional-set bound extends to all points from actual off-set PSH. -/
theorem locallyBoundedAboveOff_of_bound_on_exceptional_set {Z : Set X} {u : X → EReal}
    (hu : A.IsPSHOn u Zᶜ)
    (hb : ∀ x ∈ Z, ∃ U : Set X, U ∈ 𝓝 x ∧ ∃ C : ℝ,
      ∀ y ∈ U, y ∉ Z → u y ≤ (C : EReal)) : LocallyBoundedAboveOff Z u := by
  intro x
  by_cases hxZ : x ∈ Z
  · exact hb x hxZ
  · obtain ⟨i, hi⟩ := A.cover x
    have hcoord := hu.chartPlurisubharmonic i (A.chart i x)
      ⟨(A.chart i).map_source hi, by
        simpa only [mem_preimage, mem_compl_iff, (A.chart i).left_inv hi] using hxZ⟩
    obtain ⟨C, hC, _⟩ := EReal.lt_iff_exists_real_btwn.mp
      (lt_top_iff_ne_top.mpr (hu.ne_top hxZ))
    have hCc : A.coordinate u i (A.chart i x) < (C : EReal) := by
      simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using hC
    have hev : ∀ᶠ y in 𝓝 x, u y < (C : EReal) := by
      filter_upwards [((A.chart i).continuousAt hi).eventually
        (hcoord.upperSemicontinuousAt C hCc), (A.chart i).open_source.mem_nhds hi] with y hy hs
      simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hs] using hy
    exact ⟨{y | u y < (C : EReal)}, hev, C, fun y hy _ => hy.le⟩

/-- The full original locally bounded case, with internally produced closedness,
pole witnesses, source nondegeneracy, and pointwise uniqueness. -/
theorem exists_unique_bounded_analytic_extension {Z : Set X}
    (hEq : A.HasAnalyticChartEquations Z) (hproper : interior Z = ∅) {u : X → EReal}
    (hu : A.IsPSHOn u Zᶜ)
    (hb : ∀ x ∈ Z, ∃ U : Set X, U ∈ 𝓝 x ∧ ∃ C : ℝ,
      ∀ y ∈ U, y ∉ Z → u y ≤ (C : EReal)) :
    ∃! v : X → EReal, A.IsPSH v ∧ EqOn v u Zᶜ := by
  have hZ := hEq.isClosed A
  have hpl := hEq.locallyPluripolar A hproper
  have hbound := A.locallyBoundedAboveOff_of_bound_on_exceptional_set hu hb
  refine ⟨analyticExtension Z u,
    ⟨A.analyticExtension_isPSH hZ hpl hEq hu hbound,
      fun x hx => A.analyticExtension_eq_off hZ hu hx⟩, ?_⟩
  intro v hv
  exact A.analyticExtension_unique hZ hpl hEq hu hbound hv.1 hv.2

end SGPT.PSH.VariableComplexAtlas
