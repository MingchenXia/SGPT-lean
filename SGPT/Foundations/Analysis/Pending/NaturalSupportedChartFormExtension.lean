module

public import SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback
public import Mathlib.Topology.Algebra.Support

/-!
# Genuine compact-support chart extension of original smooth forms

Full tensor pullback, actual compact support and original chart inverse equations
internally supply smoothness across the boundary and the complete overlap law.
No global smooth form or compatibility certificate is an input.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ContDiff Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension

open FirstPass HolomorphicMaps NaturalSmoothTensorPullback

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual full tensor transport, zero outside its genuine overlap. -/
def transportedCoeff (e f : ComplexChart n M)
    (A : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :
    ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ :=
  (chartTransition f e).source.indicator (fun z =>
    (A (chartTransition f e z)).compContinuousLinearMap (chartTransitionDerivative f e z))

/-- Compact support internally supplies smoothness across the original overlap boundary. -/
theorem contDiffOn_transportedCoeff (e f : ComplexChart n M)
    {A : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ}
    (hA : ContDiff ℝ ∞ A) (hc : IsCompact (tsupport A))
    (hs : tsupport A ⊆ e.val.target) :
    ContDiffOn ℝ ∞ (transportedCoeff e f A) f.val.target := by
  intro z hz
  by_cases ho : z ∈ (chartTransition f e).source
  · have ht := (contDiffOn_chart_pullback f e hA.contDiffOn) z ho
    have ht' := ht.contDiffAt ((chartTransition f e).open_source.mem_nhds ho)
    have heq : transportedCoeff e f A =ᶠ[𝓝 z] fun y =>
        (A (chartTransition f e y)).compContinuousLinearMap (chartTransitionDerivative f e y) := by
      filter_upwards [(chartTransition f e).open_source.mem_nhds ho] with y hy
      exact indicator_of_mem hy _
    exact (ht'.congr_of_eventuallyEq heq).contDiffWithinAt
  · let C : Set M := e.val.symm '' tsupport A
    have hC : IsCompact C := hc.image_of_continuousOn (e.val.symm.continuousOn.mono hs)
    have hx : f.val.symm z ∉ C := by
      rintro ⟨y, hy, hxy⟩
      apply ho
      refine ⟨hz, ?_⟩
      change f.val.symm z ∈ e.val.source
      rw [← hxy]
      exact e.val.map_target (hs hy)
    have hcont : ContinuousAt f.val.symm z :=
      f.val.symm.continuousOn.continuousAt (f.val.open_target.mem_nhds hz)
    have hn : ∀ᶠ y in 𝓝 z, f.val.symm y ∉ C :=
      hcont.eventually (hC.isClosed.isOpen_compl.mem_nhds hx)
    have heq : transportedCoeff e f A =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hn] with y hy
      by_cases ho' : y ∈ (chartTransition f e).source
      · have hzero : A (chartTransition f e y) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro ha
          apply hy
          refine ⟨chartTransition f e y, ha, ?_⟩
          exact e.val.left_inv ho'.2
        simp only [transportedCoeff, indicator_of_mem ho', hzero]
        ext v
        rfl
      · exact indicator_of_notMem ho' _
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The genuine zero-extended global form, with all chart compatibility proved internally. -/
def extend (e : ComplexChart n M)
    (A : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)
    (hA : ContDiff ℝ ∞ A) (hc : IsCompact (tsupport A))
    (hs : tsupport A ⊆ e.val.target) : SmoothRealForm n M q where
  coeff := fun f => transportedCoeff e f A
  smooth := fun f => contDiffOn_transportedCoeff e f hA hc hs
  compatible := by
    intro f g z hz v
    have hgt : chartTransition f g z ∈ g.val.target := g.val.map_source hz.2
    have hsame : g.val.symm (chartTransition f g z) = f.val.symm z :=
      g.val.left_inv hz.2
    by_cases he : f.val.symm z ∈ e.val.source
    · have hfe : z ∈ (chartTransition f e).source := ⟨hz.1, he⟩
      have hge : chartTransition f g z ∈ (chartTransition g e).source := by
        refine ⟨hgt, ?_⟩
        change g.val.symm (chartTransition f g z) ∈ e.val.source
        rwa [hsame]
      have hmap : chartTransition f e z = chartTransition g e (chartTransition f g z) :=
        coordinateMap_change_source (f := id) (d := e) hz
      have hder : chartTransitionDerivative f e z =
          (chartTransitionDerivative g e (chartTransition f g z)).comp
            (chartTransitionDerivative f g z) :=
        coordinateMap_fderiv_change_source contMDiff_id f g e hz hfe
      simp only [transportedCoeff, indicator_of_mem hfe, indicator_of_mem hge,
        ContinuousAlternatingMap.compContinuousLinearMap_apply, hmap, hder]
      rfl
    · have hfe : z ∉ (chartTransition f e).source := fun h => he h.2
      have hge : chartTransition f g z ∉ (chartTransition g e).source := by
        intro h
        apply he
        have hh : g.val.symm (chartTransition f g z) ∈ e.val.source := h.2
        rwa [hsame] at hh
      simp only [transportedCoeff, indicator_of_notMem hfe, indicator_of_notMem hge]
      rfl

/-- Exact original coefficient readback, not merely geometric equality of classes. -/
theorem extend_coeff_self (e : ComplexChart n M)
    (A : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)
    (hA : ContDiff ℝ ∞ A) (hc : IsCompact (tsupport A))
    (hs : tsupport A ⊆ e.val.target) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (extend e A hA hc hs).coeff e z = A z := by
  have ho : z ∈ (chartTransition e e).source := ⟨hz, e.val.map_target hz⟩
  have heq : (chartTransition e e) =ᶠ[𝓝 z] id := by
    filter_upwards [e.val.open_target.mem_nhds hz] with y hy
    exact e.val.right_inv hy
  have hder : chartTransitionDerivative e e z = ContinuousLinearMap.id ℝ (ComplexModel n) := by
    exact heq.fderiv_eq.trans fderiv_id
  have hmap : chartTransition e e z = z := e.val.right_inv hz
  simp only [extend, transportedCoeff, indicator_of_mem ho, hmap, hder]
  ext v
  rfl

/-- The reconstructed form really vanishes outside the chosen chart's source. -/
theorem extend_coeff_eq_zero (e f : ComplexChart n M)
    (A : ComplexModel n → (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)
    (hA : ContDiff ℝ ∞ A) (hc : IsCompact (tsupport A))
    (hs : tsupport A ⊆ e.val.target) {z : ComplexModel n}
    (hz : f.val.symm z ∉ e.val.source) : (extend e A hA hc hs).coeff f z = 0 := by
  have ho : z ∉ (chartTransition f e).source := fun h => hz h.2
  change transportedCoeff e f A z = 0
  exact indicator_of_notMem ho (fun y =>
    (A (chartTransition f e y)).compContinuousLinearMap (chartTransitionDerivative f e y))

end SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension
