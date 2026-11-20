import SGPT.Unibranch.LocalParamGerm
import SGPT.PSH.GrauertRemmertBounded
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
import SGPT.Foundations.Analysis.Pending.BlowupExistenceOriginIdeal

/-!
# The Grauert--Remmert extension theorem on complex manifolds

Source: SGPT `thm:GRexten` (Brelot, Grauert--Remmert), and the manifold case of
SGPT `thm:GRexten2`, item (1).

Let `X` be a complex manifold (an actual atlas whose charts may have different
dimensions, `VariableComplexAtlas`), `Z ⊆ X` an analytic subset
(`HasAnalyticChartEquations`: in every chart, near every point, the common zero set
of finitely many holomorphic functions) and `φ` plurisubharmonic on `X \ Z`.

* Item (2) (`Z` of codimension at least one, i.e. with empty interior, and `φ` locally
  bounded above near `Z`) is `exists_unique_bounded_analytic_extension`
  (`SGPT.PSH.GrauertRemmertBounded`).
* Item (1): `Z` has codimension at least two everywhere (`HasChartCodimAtLeastTwo`:
  every regular point of `Z` has dimension at most the local dimension of `X` minus
  two).  Then `φ` is automatically locally bounded above near `Z`
  (`locallyBounded_of_hasChartCodimAtLeastTwo`, by local parametrization and line
  slicing, `LocalParamGerm`, `LocalParamSlice`), so item (2) applies
  (`exists_unique_codimTwo_analytic_extension`).

In both cases the extension is unique and equals the upper limit
`φ(x) = limsup_{X \ Z ∋ y → x} φ(y)` (`grauertRemmert_extension`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {X : Type*} [TopologicalSpace X]

/-- **Codimension at least two everywhere** (SGPT `thm:GRexten`, item (1)): every regular
point of `Z`, read in any chart of `X`, has complex dimension at most the chart dimension
minus two.  Here a regular point of dimension `k` of the chart image
`e(Z) = e.target ∩ e⁻¹(Z)` is a point near which `e(Z)` is biholomorphic to an open piece
of `ℂᵏ × {0}` (`RegularAtDim`); the local dimension of an analytic set is the maximal
dimension of its nearby regular points, so this says `dim_x Z ≤ dim_x X - 2` for all
`x ∈ Z`. -/
def HasChartCodimAtLeastTwo (A : VariableComplexAtlas X) (Z : Set X) : Prop :=
  ∀ (i : A.Index) (y : ComplexModel (A.dimension i)) (k : ℕ),
    RegularAtDim (n := A.dimension i) (M := ComplexModel (A.dimension i))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' Z) y k → k + 2 ≤ A.dimension i

variable {A : VariableComplexAtlas X}

/-- Codimension at least two implies codimension at least one: an interior point of `Z`
would be a regular point of full dimension. -/
theorem HasChartCodimAtLeastTwo.interior_eq_empty {Z : Set X}
    (hcodim : A.HasChartCodimAtLeastTwo Z) : interior Z = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨i, hi⟩ := A.cover x
  set e := A.chart i
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' interior Z) :=
    e.isOpen_inter_preimage_symm isOpen_interior
  have hxW : e x ∈ e.target ∩ e.symm ⁻¹' interior Z :=
    ⟨e.map_source hi, by simpa only [mem_preimage, e.left_inv hi] using hx⟩
  have hset : (univ : Set (ComplexModel (A.dimension i))) ∩ (e.target ∩ e.symm ⁻¹' interior Z) =
      (e.target ∩ e.symm ⁻¹' Z) ∩ (e.target ∩ e.symm ⁻¹' interior Z) := by
    ext y
    simp only [mem_inter_iff, mem_univ, true_and, mem_preimage]
    constructor
    · rintro ⟨hy, hyZ⟩
      exact ⟨⟨hy, interior_subset hyZ⟩, hy, hyZ⟩
    · rintro ⟨-, hy⟩
      exact hy
  have hreg := RegularPointDimension.regularAtDim_of_inter_eq hW hxW hset
    (AnalyticIrreducibleComponents.regularAtDim_univ (n := A.dimension i)
      (M := ComplexModel (A.dimension i)) (e x))
  have := hcodim i (e x) (A.dimension i) hreg
  omega

/-- **Local boundedness across a set of codimension at least two** (the main step of SGPT
`thm:GRexten`, item (1)).  A function plurisubharmonic off an analytic set of codimension at
least two is bounded above near every point of the set.  In a chart this is
`SGPT.Unibranch.LocalParam.exists_bound_of_codimTwo`. -/
theorem locallyBounded_of_hasChartCodimAtLeastTwo {Z : Set X}
    (hEq : A.HasAnalyticChartEquations Z) (hcodim : A.HasChartCodimAtLeastTwo Z)
    {u : X → EReal} (hu : A.IsPSHOn u Zᶜ) :
    ∀ x ∈ Z, ∃ U : Set X, U ∈ 𝓝 x ∧ ∃ C : ℝ, ∀ y ∈ U, y ∉ Z → u y ≤ (C : EReal) := by
  intro x _
  obtain ⟨i, hi⟩ := A.cover x
  set e := A.chart i
  set S : Set (ComplexModel (A.dimension i)) := e.target ∩ e.symm ⁻¹' Z with hSdef
  have hS : ∀ z ∈ e.target, ∃ W : Set (ComplexModel (A.dimension i)), IsOpen W ∧ z ∈ W ∧
      ∃ (N : ℕ) (g : Fin N → ComplexModel (A.dimension i) → ℂ),
        (∀ j, DifferentiableOn ℂ (g j) W) ∧ ∀ y ∈ W, y ∈ S ↔ ∀ j, g j y = 0 := by
    intro z hz
    obtain ⟨W, hW, hzW, hWt, N, g, hg, he⟩ := hEq i z hz
    refine ⟨W, hW, hzW, N, g, hg, fun y hy => ?_⟩
    rw [← he y hy]
    exact ⟨fun h => h.2, fun h => ⟨hWt hy, h⟩⟩
  have hψ : PlurisubharmonicOn (A.coordinate u i) (e.target \ S) := by
    refine (hu.chartPlurisubharmonic i).mono fun y hy => ⟨hy.1, fun hyZ => hy.2 ⟨hy.1, hyZ⟩⟩
  obtain ⟨U', hU', C, hC⟩ := SGPT.Unibranch.LocalParam.exists_bound_of_codimTwo e.open_target hS
    (fun y _ k hk => hcodim i y k hk) hψ (e.map_source hi)
  refine ⟨e.source ∩ e ⁻¹' U', inter_mem (e.open_source.mem_nhds hi)
    ((e.continuousAt hi).preimage_mem_nhds hU'), C, fun y hy hyZ => ?_⟩
  have h := hC (e y) hy.2 fun hyS => hyZ (by simpa only [mem_preimage, e.left_inv hy.1] using
    hyS.2)
  have hyy : (A.chart i).symm (e y) = y := (A.chart i).left_inv hy.1
  simpa only [coordinate, Function.comp_apply, hyy] using h

/-- **SGPT `thm:GRexten`, item (1), and the manifold case of `thm:GRexten2`, item (1).**
A function plurisubharmonic off an analytic set of codimension at least two in a complex
manifold has one and only one plurisubharmonic extension. -/
theorem exists_unique_codimTwo_analytic_extension {Z : Set X}
    (hEq : A.HasAnalyticChartEquations Z) (hcodim : A.HasChartCodimAtLeastTwo Z)
    {u : X → EReal} (hu : A.IsPSHOn u Zᶜ) :
    ∃! v : X → EReal, A.IsPSH v ∧ EqOn v u Zᶜ :=
  A.exists_unique_bounded_analytic_extension hEq hcodim.interior_eq_empty hu
    (locallyBounded_of_hasChartCodimAtLeastTwo hEq hcodim hu)

/-- **SGPT `thm:GRexten`** (Brelot, Grauert--Remmert), both items, together with the
uniqueness and the formula `eq:GRextvarphiexp`.  Let `Z` be an analytic subset of the complex
manifold `X` and `u` plurisubharmonic on `X \ Z`.  Assume either (1) `Z` has codimension at
least two everywhere, or (2) `Z` has codimension at least one everywhere (empty interior)
and `u` is locally bounded above near each point of `Z`.  Then `u` has exactly one
plurisubharmonic extension to `X`; it is `analyticExtension Z u`, whose value at every point
`x` is `limsup_{X \ Z ∋ y → x} u(y)`. -/
theorem grauertRemmert_extension {Z : Set X} (hEq : A.HasAnalyticChartEquations Z)
    {u : X → EReal} (hu : A.IsPSHOn u Zᶜ)
    (hcase : A.HasChartCodimAtLeastTwo Z ∨
      (interior Z = ∅ ∧ ∀ x ∈ Z, ∃ U : Set X, U ∈ 𝓝 x ∧ ∃ C : ℝ,
        ∀ y ∈ U, y ∉ Z → u y ≤ (C : EReal))) :
    A.IsPSH (analyticExtension Z u) ∧ EqOn (analyticExtension Z u) u Zᶜ ∧
      (∀ v : X → EReal, A.IsPSH v → EqOn v u Zᶜ → v = analyticExtension Z u) ∧
      ∀ x, analyticExtension Z u x = limsup u (𝓝[Zᶜ] x) := by
  have hproper : interior Z = ∅ := hcase.elim (fun h => h.interior_eq_empty) (fun h => h.1)
  have hb : ∀ x ∈ Z, ∃ U : Set X, U ∈ 𝓝 x ∧ ∃ C : ℝ, ∀ y ∈ U, y ∉ Z → u y ≤ (C : EReal) :=
    hcase.elim (fun h => locallyBounded_of_hasChartCodimAtLeastTwo hEq h hu) (fun h => h.2)
  have hZ := hEq.isClosed A
  have hpl := hEq.locallyPluripolar A hproper
  have hbound := A.locallyBoundedAboveOff_of_bound_on_exceptional_set hu hb
  exact ⟨A.analyticExtension_isPSH hZ hpl hEq hu hbound,
    fun x hx => A.analyticExtension_eq_off hZ hu hx,
    fun v hv he => A.analyticExtension_unique hZ hpl hEq hu hbound hv he,
    fun x => analyticExtension_eq_limsup Z u x⟩

/-! ### Sanity checks of the codimension condition -/

/-- The chart image of a set under a chart of the model space itself is the set. -/
theorem modelSelfChart_target_inter_preimage {d : ℕ} (e : ComplexChart d (ComplexModel d))
    (Z : Set (ComplexModel d)) : e.val.target ∩ e.val.symm ⁻¹' Z = Z := by
  have he : e.val = OpenPartialHomeomorph.refl (ComplexModel d) :=
    chartedSpaceSelf_atlas.mp e.property
  rw [he]
  simp

/-- Non-vacuity: the origin of `ℂ²` has codimension at least two. -/
theorem hasChartCodimAtLeastTwo_origin_two :
    (ofFixedModel 2 (ComplexModel 2)).HasChartCodimAtLeastTwo ({0} : Set (ComplexModel 2)) := by
  have key : ∀ (e : ComplexChart 2 (ComplexModel 2)) (y : ComplexModel 2) (k : ℕ),
      RegularAtDim (n := 2) (M := ComplexModel 2)
        (e.val.target ∩ e.val.symm ⁻¹' ({0} : Set (ComplexModel 2))) y k → k + 2 ≤ 2 := by
    intro e y k hk
    rw [modelSelfChart_target_inter_preimage] at hk
    have hy : y = 0 := hk.2.1
    subst hy
    have := RegularPointDimension.eq_of_regularAtDim hk
      (BlowupExistenceOriginIdeal.regularAtDim_zero (d := 2))
    omega
  exact fun e y k hk => key e y k hk

/-- The condition is not automatic: the origin of `ℂ` (a hypersurface) does not have
codimension at least two. -/
theorem not_hasChartCodimAtLeastTwo_origin_one :
    ¬ (ofFixedModel 1 (ComplexModel 1)).HasChartCodimAtLeastTwo
      ({0} : Set (ComplexModel 1)) := by
  intro h
  have := h (complexChartAt (n := 1) (0 : ComplexModel 1)) 0 0 (by
    change RegularAtDim (n := 1) (M := ComplexModel 1)
      ((complexChartAt (n := 1) (0 : ComplexModel 1)).val.target ∩
        (complexChartAt (n := 1) (0 : ComplexModel 1)).val.symm ⁻¹' ({0} : Set (ComplexModel 1)))
      0 0
    rw [modelSelfChart_target_inter_preimage]
    exact BlowupExistenceOriginIdeal.regularAtDim_zero (d := 1))
  change 0 + 2 ≤ 1 at this
  omega

end SGPT.PSH.VariableComplexAtlas
