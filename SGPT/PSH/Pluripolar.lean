import SGPT.PSH.LocalManifold
import SGPT.Foundations.Analysis.FirstPass.PluripolarSets

/-!
# Exact source local pluripolar witnesses and chart outer nullity

The definition uses source PSH on actual open manifold neighborhoods, at every
original point. Genuine chart transport and local finite points construct the
existing TN coordinate witnesses; their proved measure theorem is reused.
-/

namespace SGPT.PSH.VariableComplexAtlas

open Set Metric MeasureTheory
open SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- SGPT `def:pluripolarsets`: actual neighborhood source PSH pole witnesses.
Ambient representatives are tested only on the actual open neighborhood. -/
def LocallyPluripolar (S : Set X) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ w : X → EReal, A.IsPSHOn w U ∧ ∀ y ∈ S ∩ U, w y = ⊥

/-- The source non-pluripolar predicate is the exact negation. -/
def NonPluripolar (S : Set X) : Prop := ¬ A.LocallyPluripolar S

/-- The source co-pluripolar predicate tests the actual complement. -/
def CoPluripolar (S : Set X) : Prop := A.LocallyPluripolar Sᶜ

/-- The actual portion of a set visible in this chart. -/
def pluripolarChartSet (S : Set X) (i : A.Index) : Set (ComplexModel (A.dimension i)) :=
  (A.chart i).target ∩ (A.chart i).symm ⁻¹' S

variable {A}

/-- Subsets reuse the same actual nontrivial witnesses. -/
theorem LocallyPluripolar.mono {S T : Set X} (hS : A.LocallyPluripolar S) (hTS : T ⊆ S) :
    A.LocallyPluripolar T := by
  intro x
  obtain ⟨U, hU, hx, w, hw, hp⟩ := hS x
  exact ⟨U, hU, hx, w, hw, fun y hy ↦ hp y ⟨hTS hy.1, hy.2⟩⟩

/-- Actual source neighborhood witnesses produce genuine coordinate pole
witnesses in every chart, with independently specified concrete dimensions. -/
theorem LocallyPluripolar.in_chart {S : Set X} (hS : A.LocallyPluripolar S) (i : A.Index) :
    SGPT.Foundations.Analysis.LocallyPluripolarOn (A.pluripolarChartSet S i) (A.chart i).target := by
  intro z hz
  obtain ⟨U, hU, hzU, w, hw, hp⟩ := hS ((A.chart i).symm z)
  have hT := (A.chart i).isOpen_inter_preimage_symm hU
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hT z ⟨hz, hzU⟩
  have hwB := hw.coordinate_pshOn_of_connected hU i isOpen_ball (isConnected_ball hr) hb
  refine ⟨ball z r, A.coordinate w i, isOpen_ball, mem_ball_self hr,
    (isConnected_ball hr).isPreconnected, hwB.disc.plurisubharmonicOn isOpen_ball,
    hwB.nontrivial, ?_⟩
  intro y hy hyS
  exact hp ((A.chart i).symm y) ⟨hyS.2, (hb hy).2⟩

/-- SGPT `prop:ppsnull`: actual coordinate Haar outer measure zero.
No measurability of S or global second countability of X is assumed. -/
theorem LocallyPluripolar.chart_measure_eq_zero {S : Set X}
    (hS : A.LocallyPluripolar S) (i : A.Index)
    (μ : Measure (ComplexModel (A.dimension i))) [μ.IsAddHaarMeasure] :
    μ (A.pluripolarChartSet S i) = 0 := by
  have hsub : A.pluripolarChartSet S i ⊆ (A.chart i).target := fun _ hz ↦ hz.1
  simpa only [inter_eq_left.mpr hsub] using
    (hS.in_chart i).measure_inter_eq_zero (A.chart i).open_target μ

/-- The source's Lebesgue measure convention is the actual coordinate volume. -/
theorem LocallyPluripolar.chart_volume_eq_zero {S : Set X}
    (hS : A.LocallyPluripolar S) (i : A.Index) :
    volume (A.pluripolarChartSet S i) = 0 := hS.chart_measure_eq_zero i volume

/-- The actual exceptional set is negligible in every coordinate measure. -/
theorem LocallyPluripolar.ae_notMem_in_chart {S : Set X}
    (hS : A.LocallyPluripolar S) (i : A.Index)
    (μ : Measure (ComplexModel (A.dimension i))) [μ.IsAddHaarMeasure] :
    ∀ᵐ z ∂μ.restrict (A.chart i).target, (A.chart i).symm z ∉ S := by
  filter_upwards [(hS.in_chart i).ae_notMem μ,
    ae_restrict_mem (A.chart i).open_target.measurableSet] with z hz hzT
  exact fun hzS ↦ hz ⟨hzT, hzS⟩

end SGPT.PSH.VariableComplexAtlas
