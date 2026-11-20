import SGPT.PSH.NadelCoherence
import SGPT.Foundations.Analysis.Pending.ChartWeightedL2Transfer
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# The multiplier ideal sheaf by its sections (`def:pshfunctions:L1122`)

Source: `def:pshfunctions:L1122` of the chapter *Plurisubharmonic functions*: for
`φ ∈ PSH(X)` the multiplier ideal sheaf `𝓘(φ)` is the ideal sheaf with

`Γ(U, 𝓘(φ)) = {f ∈ 𝒪_X(U) : |f|² exp(-φ) ∈ L¹_loc(U)}`

for every open `U ⊆ X`.

`multiplierSections φ U` is this set, literally: holomorphic functions on `U` such that, in
every holomorphic chart `e`, the coordinate expression of `|f|² e^{-φ}` (with `e^{-φ} = ∞` at the
poles of `φ` and `0 · ∞ = 0`) is measurable with finite Lebesgue integral on a neighbourhood
(inside `U`) of every point.

The existing multiplier ideal `SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.multiplierIdeal 1 φ`
is a germ ideal (stalks tested in the preferred chart at each point).
`mem_multiplierSections_iff` shows that, for psh `φ`, the sections of the book's sheaf over `U` are
exactly the functions whose germs at every point of `U` lie in the stalks of
`multiplierIdeal 1 φ`; thus the book's sheaf is the sheaf of sections of the existing germ ideal.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace SGPT.PSH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `|f|² exp(-φ) ∈ L¹_loc(U)`: in every holomorphic chart `e` of `M`, every point of the
coordinate domain of `U` has an open neighbourhood inside it on which the coordinate expression
of `|f|² e^{-φ}` is measurable with finite Lebesgue integral. -/
def WeightedL1LocOn (φ : M → EReal) (f : M → ℂ) (U : Set M) : Prop :=
  ∀ e : ComplexChart n M, ∀ z ∈ e.val.target ∩ e.val.symm ⁻¹' U,
    ∃ V : Set (ComplexModel n), IsOpen V ∧ z ∈ V ∧ V ⊆ e.val.target ∩ e.val.symm ⁻¹' U ∧
      WeightedL2On (chartFunction φ e) 1 (fun w => f (e.val.symm w)) V volume

/-- `def:pshfunctions:L1122`. The sections `Γ(U, 𝓘(φ)) = {f ∈ 𝒪_X(U) : |f|² e^{-φ} ∈ L¹_loc(U)}`
of the multiplier ideal sheaf over an open set `U`. -/
def multiplierSections (φ : M → EReal) (U : Set M) : Set (M → ℂ) :=
  {f | MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f U ∧ WeightedL1LocOn (n := n) φ f U}

/-- A holomorphic function is holomorphic in every atlas chart. -/
theorem differentiableAt_comp_chart_symm {f : M → ℂ} (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f (e.val.symm z)) :
    DifferentiableAt ℂ (fun w => f (e.val.symm w)) z := by
  have hs : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val.symm z :=
    mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hz
  have := hf.comp z hs
  exact mdifferentiableAt_iff_differentiableAt.mp this

/-- The sections of the book's multiplier ideal sheaf over an open set `U` are exactly the
functions whose germs at all points of `U` lie in the existing multiplier germ ideal
`multiplierIdeal 1 φ` (tested in the preferred charts). -/
theorem mem_multiplierSections_iff {φ : M → EReal} (hφ : ManifoldPSH (n := n) φ)
    {U : Set M} (hU : IsOpen U) (f : M → ℂ) :
    f ∈ multiplierSections (n := n) φ U ↔ ∀ x ∈ U, (multiplierIdeal (n := n) 1 φ).mem x f := by
  constructor
  · rintro ⟨hf, hL⟩ x hx
    have hfx : HolomorphicAt n f x := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hf y hy).mdifferentiableAt (hU.mem_nhds hy)
    refine ⟨hfx, one_pos, ?_⟩
    set e := complexChartAt (n := n) x
    have hz : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' U :=
      ⟨e.val.map_source (mem_complexChartAt_source x), by
        simpa only [mem_preimage, e.val.left_inv (mem_complexChartAt_source x)] using hx⟩
    obtain ⟨V, hV, hzV, hVsub, hW⟩ := hL e (e.val x) hz
    refine ⟨V, hV, hzV, ?_, hW⟩
    intro w hw
    have hw' := hVsub hw
    have hm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f (e.val.symm w) :=
      (hf _ hw'.2).mdifferentiableAt (hU.mem_nhds hw'.2)
    exact (differentiableAt_comp_chart_symm e hw'.1 hm).differentiableWithinAt
  · intro h
    refine ⟨fun y hy => ((h y hy).1.self_of_nhds).mdifferentiableWithinAt, ?_⟩
    intro e z hz
    set x := e.val.symm z
    have hxs : x ∈ e.val.source := e.val.map_target hz.1
    have hpref := (h x hz.2).2
    have husc : UpperSemicontinuousOn (chartFunction φ e)
        (Pending.ChartWeightedL2.overlapDomain e (complexChartAt (n := n) x)) :=
      (hφ.chartPlurisubharmonic e).upperSemicontinuousOn.mono fun w hw => hw.1
    have htr := Pending.ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      e (complexChartAt (n := n) x) hxs (mem_complexChartAt_source x) husc one_ne_zero hpref
    have hez : e.val x = z := e.val.right_inv hz.1
    rw [hez] at htr
    obtain ⟨_, V, hV, hzV, _, hW⟩ := htr
    have hT : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.isOpen_inter_preimage_symm hU
    exact ⟨V ∩ (e.val.target ∩ e.val.symm ⁻¹' U), hV.inter hT, ⟨hzV, hz⟩,
      inter_subset_right, hW.mono inter_subset_left⟩

/-- The book's sheaf is an ideal sheaf in the sense of germs: its stalk at `x` (germs of sections
over open neighbourhoods of `x`) is the stalk of the existing multiplier germ ideal. -/
theorem exists_mem_multiplierSections_iff {φ : M → EReal} (hφ : ManifoldPSH (n := n) φ)
    (x : M) (f : M → ℂ) :
    (∃ U : Set M, IsOpen U ∧ x ∈ U ∧ f ∈ multiplierSections (n := n) φ U) ↔
      (multiplierIdeal (n := n) 1 φ).mem x f := by
  constructor
  · rintro ⟨U, hU, hxU, hf⟩
    exact (mem_multiplierSections_iff hφ hU f).mp hf x hxU
  · intro hx
    -- the germ condition at `x` holds on a whole neighbourhood of `x`
    obtain ⟨hhol, -, V, hV, hzV, hdiff, hW⟩ := hx
    set e := complexChartAt (n := n) x
    have hhol' : ∀ᶠ y in 𝓝 x, HolomorphicAt n f y := hhol.eventually_nhds
    obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hhol'
    let U' : Set M := O ∩ (e.val.source ∩ e.val ⁻¹' V)
    have hU' : IsOpen U' := hO.inter (e.val.isOpen_inter_preimage hV)
    have hxU' : x ∈ U' := ⟨hxO, mem_complexChartAt_source x, hzV⟩
    refine ⟨U', hU', hxU', ?_⟩
    rw [mem_multiplierSections_iff hφ hU']
    intro y hy
    have hye : MultiplierIntegrableAt (chartFunction φ e) 1 (fun z => f (e.val.symm z))
        (e.val y) volume := ⟨one_pos, V, hV, hy.2.2, hdiff, hW⟩
    have husc : UpperSemicontinuousOn (chartFunction φ (complexChartAt (n := n) y))
        (Pending.ChartWeightedL2.overlapDomain (complexChartAt (n := n) y) e) :=
      (hφ.chartPlurisubharmonic _).upperSemicontinuousOn.mono fun w hw => hw.1
    exact ⟨hOsub hy.1, Pending.ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      (complexChartAt (n := n) y) e (mem_complexChartAt_source y) hy.2.1 husc one_ne_zero hye⟩
