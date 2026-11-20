import SGPT.PSH.AtlasQPSHScaling
import SGPT.Foundations.Analysis.PshRegularDistribution

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Add the entire original forms, including their genuine tensor overlap law. -/
def AtlasClosedRealOneOneForm.add (θ η : AtlasClosedRealOneOneForm A) :
    AtlasClosedRealOneOneForm A where
  coeff := fun i z => θ.coeff i z + η.coeff i z
  smooth := fun i => (θ.smooth i).add (η.smooth i)
  compatible := by
    intro i j z hz w
    exact congrArg₂ (· + ·) (θ.compatible i j z hz w) (η.compatible i j z hz w)
  closed := by
    intro i z hz
    change extDeriv (fun y => θ.coeff i y + η.coeff i y) z = 0
    rw [extDeriv_fun_add
      (((θ.smooth i) z hz).contDiffAt ((A.chart i).open_target.mem_nhds hz)
        |>.differentiableAt (by simp))
      (((η.smooth i) z hz).contDiffAt ((A.chart i).open_target.mem_nhds hz)
        |>.differentiableAt (by simp)), θ.closed i z hz, η.closed i z hz, add_zero]
  typeOneOne := by
    intro i z hz u w
    exact congrArg₂ (· + ·) (θ.typeOneOne i z hz u w) (η.typeOneOne i z hz u w)

/-- Restriction retains smoothness and full dd-c equality in every actual chart. -/
theorem IsAtlasLocalPotential.mono_open {θ : AtlasClosedRealOneOneForm A}
    {U W : Set X} {g : X → ℝ} (hg : A.IsAtlasLocalPotential θ U g)
    (hW : IsOpen W) (hWU : W ⊆ U) : A.IsAtlasLocalPotential θ W g := by
  refine ⟨hW, fun i => (hg.2.1 i).mono (fun _ hz => ⟨hz.1, hWU hz.2⟩), ?_⟩
  exact fun i _ hz => hg.2.2 i ⟨hz.1, hWU hz.2⟩

/-- An arbitrary sum potential minus an actual first potential represents the second. -/
theorem IsAtlasLocalPotential.sub_of_add {θ η : AtlasClosedRealOneOneForm A}
    {U : Set X} {g a : X → ℝ} (hg : A.IsAtlasLocalPotential (θ.add η) U g)
    (ha : A.IsAtlasLocalPotential θ U a) :
    A.IsAtlasLocalPotential η U (fun x => g x - a x) := by
  refine ⟨hg.1, fun i => (hg.2.1 i).sub (ha.2.1 i), ?_⟩
  intro i z hz
  have hD := (A.chart i).isOpen_inter_preimage_symm hg.1
  change smoothDDC (fun y => (g ∘ (A.chart i).symm) y -
    (a ∘ (A.chart i).symm) y) z = η.coeff i z
  simp only [sub_eq_add_neg]
  rw [smoothDDC_add hD (hg.2.1 i) (ha.2.1 i).neg hz,
    smoothDDC_neg hD (ha.2.1 i) hz, hg.2.2 i hz, ha.2.2 i hz]
  change (θ.coeff i z + η.coeff i z) + -θ.coeff i z = η.coeff i z
  abel

/-- The same connected source neighborhoods yield a produced common finite point. -/
theorem IsPSHOn.add {u w : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) (hw : A.IsPSHOn w U) (hU : IsOpen U) :
    A.IsPSHOn (fun x => u x + w x) U := by
  intro x hx
  obtain ⟨i, hi, V, hV, hc, hVe, hxV, hpu⟩ := hu x hx
  have hpw := hw.coordinate_pshOn_of_connected hU i hV hc hVe
  have huae := (hpu.disc.plurisubharmonicOn hV).ae_finite volume hc.isPreconnected hpu.nontrivial
  have hwae := (hpw.disc.plurisubharmonicOn hV).ae_finite volume hc.isPreconnected hpw.nontrivial
  obtain ⟨y, hy, huy, hwy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hV.measure_pos volume ⟨_, hxV⟩).ne' (huae.and hwae)
  refine ⟨i, hi, V, hV, hc, hVe, hxV, hpu.disc.add hpw.disc, y, hy, ?_⟩
  exact EReal.add_ne_bot_iff.mpr ⟨huy.2, hwy.2⟩

/-- Maximum retains the original finite points in every relative open neighborhood. -/
theorem IsPSHOn.max {u w : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) (hw : A.IsPSHOn w U) (hU : IsOpen U) :
    A.IsPSHOn (fun x => max (u x) (w x)) U := by
  apply (isPSHOn_iff_chart_and_nondegenerate hU).mpr
  refine ⟨fun i => (hu.chartPlurisubharmonic i).max (hw.chartPlurisubharmonic i), ?_⟩
  intro x hx O hO hxO
  obtain ⟨y, hy, hn⟩ := hu.locallyNondegenerate hU x hx O hO hxO
  refine ⟨y, hy, ?_⟩
  intro h
  exact hn (le_bot_iff.mp ((le_max_left (u y) (w y)).trans_eq h))

/-- Test every actual sum potential using a genuinely produced overlap potential. -/
theorem IsThetaPSH.add {θ η : AtlasClosedRealOneOneForm A} {u w : X → EReal}
    (hu : A.IsThetaPSH θ u) (hw : A.IsThetaPSH η w) :
    A.IsThetaPSH (θ.add η) (fun x => u x + w x) := by
  refine ⟨fun x => EReal.add_ne_top (hu.1 x) (hw.1 x), ?_⟩
  intro U g hg x hx
  obtain ⟨V, a, hxV, ha⟩ := exists_atlas_local_potential θ x
  let W := U ∩ V
  have hW : IsOpen W := hg.1.inter ha.1
  have hgW := hg.mono_open hW inter_subset_left
  have haW := ha.mono_open hW inter_subset_right
  have hp := (hu.2 W a haW).add (hw.2 W (fun y => g y - a y)
    (hgW.sub_of_add haW)) hW
  have heq : (fun y => (u y + (a y : EReal)) +
      (w y + ((g y - a y : ℝ) : EReal))) =
      (fun y => (u y + w y) + (g y : EReal)) := by
    funext y
    calc
      (u y + (a y : EReal)) + (w y + ((g y - a y : ℝ) : EReal)) =
          (u y + w y) + ((a y : EReal) + ((g y - a y : ℝ) : EReal)) := by ac_rfl
      _ = (u y + w y) + (g y : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        congr 1
        ring
  rw [heq] at hp
  obtain ⟨i, hi, D, hD, hc, hDe, hxD, hpsh⟩ := hp x ⟨hx, hxV⟩
  exact ⟨i, hi, D, hD, hc, fun _ hz => ⟨(hDe hz).1, (hDe hz).2.1⟩, hxD, hpsh⟩

/-- A common original background gives a maximum for every actual local potential. -/
theorem IsThetaPSH.max {θ : AtlasClosedRealOneOneForm A} {u w : X → EReal}
    (hu : A.IsThetaPSH θ u) (hw : A.IsThetaPSH θ w) :
    A.IsThetaPSH θ (fun x => max (u x) (w x)) := by
  refine ⟨fun x => ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hu.1 x))
    (lt_top_iff_ne_top.mpr (hw.1 x))), ?_⟩
  intro U g hg
  have hp := (hu.2 U g hg).max (hw.2 U g hg) hg.1
  apply hp.congr
  intro x _
  exact max_add_add_right (u x) (w x) (g x : EReal)

/-- Manufacture a genuine entire global background for two independent QPSH inputs. -/
theorem IsQPSH.add {u w : X → EReal} (hu : A.IsQPSH u) (hw : A.IsQPSH w) :
    A.IsQPSH (fun x => u x + w x) := by
  obtain ⟨θ, hθ⟩ := hu
  obtain ⟨η, hη⟩ := hw
  exact ⟨θ.add η, hθ.add hη⟩

/-- Pair actual global membership with the already accepted rational presentation producer. -/
theorem IsQPSH.add_analytic {u w : X → EReal} (hu : A.IsQPSH u) (hw : A.IsQPSH w)
    (hanU : A.HasRationalAnalyticChartType u) (hanW : A.HasRationalAnalyticChartType w) :
    A.IsQPSH (fun x => u x + w x) ∧
      A.HasRationalAnalyticChartType (fun x => u x + w x) := by
  exact ⟨hu.add hw, hanU.add hanW⟩

end SGPT.PSH.VariableComplexAtlas
