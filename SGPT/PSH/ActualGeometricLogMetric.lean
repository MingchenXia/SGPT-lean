import SGPT.PSH.GlobalCartierLogGerm
import SGPT.PSH.LocalDivisorLogType
import SGPT.PSH.LogResolution

/-! Actual original arbitrary compact geometric Q divisors and their logs
manufacture genuine divisor metrics and bounded residuals internally. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ResidualNefReduction
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u

private theorem boundedRealGermAt_of_chartSmoothOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {V : Set M} (hV : IsOpen V) {h : M → ℝ}
    (hh : ∀ e : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V))
    {x : M} (hx : x∈V) : BoundedRealGermAt h x := by
  let e := complexChartAt (n := n) x
  have hxs : x∈e.val.source := mem_complexChartAt_source x
  have hmem : e.val x∈e.val.target ∩ e.val.symm ⁻¹' V :=
    ⟨e.val.map_source hxs,by simpa only [mem_preimage,e.val.left_inv hxs] using hx⟩
  have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hV
  have hc : ContinuousAt (fun z => h (e.val.symm z)) (e.val x) :=
    ((hh e).continuousOn).continuousAt (hopen.mem_nhds hmem)
  obtain ⟨C,hC,hCb⟩ :=
    (boundedRealGermAt_of_continuousAt hc).comp_continuousAt (e.val.continuousAt hxs)
  refine ⟨C,hC,?_⟩
  filter_upwards [hCb,e.val.open_source.mem_nhds hxs] with y hy hys
  simpa only [e.val.left_inv hys] using hy

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

/-- Complete original native logs and a genuine global Cartier coefficient
identity produce the full metric local type for ANY actual metric on SAME F.
The bounded real remainder is manufactured by full ideal/unit/smooth-weight
arguments and includes the original poles on the entire chosen neighborhood. -/
theorem native_log_metric_local_type
    {D : EffectiveGeometricQDivisor (m+1) M} {u : M → EReal}
    (hu : NativeHasLogSingularitiesAlong D u)
    (F : EffectiveDivisor (m+1) M) (d : ℕ) (hd : 0<d)
    (hcoeff : ∀ Q,D.coefficient Q=(cartierGeometricPrimeCoefficient F Q : ℚ)/(d : ℚ))
    (EH : MeteredEffectiveQDivisor (m+1) M) (hEH : DivisorMetric.IsDivisorMetric F EH) :
    HasLocalDivisorLogType (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH) u := by
  intro x
  obtain ⟨V,hV,hxV,g,hg,hgen,h,hh,hw⟩ := hEH x
  have hghol : HolomorphicAt (m+1) g x :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hg hxV
  obtain ⟨b,hb,hlog⟩ := exists_log_germ_of_global_cartier_coefficients hu F d hd hcoeff x g hghol (hgen x hxV)
  let c : ℝ := ((1/(d : ℚ) : ℚ) : ℝ)
  have hc : (0 : ℝ)≤c := by dsimp [c];positivity
  have hhbound : BoundedRealGermAt (fun y => c*h y) x := by
    obtain ⟨C,hC,hbound⟩ := boundedRealGermAt_of_chartSmoothOn hV hh hxV
    refine ⟨|c| * C,mul_nonneg (abs_nonneg _) hC,?_⟩
    filter_upwards [hbound] with y hy
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  let R : M → ℝ := fun y => b y-c*h y
  have hR : BoundedRealGermAt R x := hb.sub hhbound
  obtain ⟨C,hC,hRC⟩ := hR
  have hlocal : ∀ᶠ y in 𝓝 x,|R y|≤C ∧
      u y=(MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH).weight y+(R y : EReal) := by
    filter_upwards [hRC,hlog,hV.mem_nhds hxV] with y hy hlogy hyV
    refine ⟨hy,?_⟩
    have hsingle : generatorLog (fun _ : Fin 1 => g) y=logNormSq (g y) := by
      rw [generatorLog_eq_log_sum]
      simp [logNormSq]
    have hreal : ((c*h y : ℝ) : EReal)+(R y : EReal)=(b y : EReal) := by
      rw [←EReal.coe_add]
      congr 1
      dsimp [R]
      ring
    calc
      u y=(c : EReal)*logNormSq (g y)+(b y : EReal) := hlogy
      _ = (c : EReal)*logNormSq (g y)+(((c*h y : ℝ) : EReal)+(R y : EReal)) := by rw [hreal]
      _ = (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH).weight y+(R y : EReal) := by
        rw [MeteredDivisorScaling.weight_smul,hw y hyV,hsingle,
          EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c),
          ←EReal.coe_mul,add_assoc]
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel (m+1)) M
  obtain ⟨U,⟨hU,hxU,hconn⟩,hUlocal⟩ := (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp hlocal
  exact ⟨U,R,C,hC,hU,hconn,hxU,(fun y hy => (hUlocal hy).1),(fun y hy => (hUlocal hy).2)⟩

private theorem qdiv_ext {D E : EffectiveGeometricQDivisor (m+1) M}
    (h : ∀ Q,D.coefficient Q=E.coefficient Q) : D=E := by
  cases D
  cases E
  have hc := funext h
  cases hc
  rfl

/-- ORIGINAL arbitrary compact geometric Q divisor ALONE produces its
ACTUAL global integral Cartier representation and genuine smooth metric,
with ENTIRE geometric divisor identity and exact scaled original support. -/
theorem compact_exists_actual_metered_representation [CompactSpace M]
    (D : EffectiveGeometricQDivisor (m+1) M) :
    ∃ (d : ℕ) (F : EffectiveDivisor (m+1) M) (EH : MeteredEffectiveQDivisor (m+1) M),
      0<d ∧ D=cartierGeometricQDivisor F (1/(d : ℚ)) (by positivity) ∧
      EH.support=F.support ∧ DivisorMetric.IsDivisorMetric F EH ∧
      (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH).support=D.support ∧
      ∀ Q,D.coefficient Q=(cartierGeometricPrimeCoefficient F Q : ℚ)/(d : ℚ) := by
  obtain ⟨d,F,hd,hcoeff⟩ := compact_exists_global_integral_cartier D
  have hglobal (Q : GeometricPrimeCarrier (m+1) M) :
      D.coefficient Q=(cartierGeometricPrimeCoefficient F Q : ℚ)/(d : ℚ) := by
    have h := hcoeff Q
    change D.coefficient Q=(cartierGeometricPrimeCoefficient F Q : ℚ)/(d : ℚ) at h
    exact h
  have hc : (0 : ℚ)<1/(d : ℚ) := by positivity
  have hD : D=cartierGeometricQDivisor F (1/(d : ℚ)) (by positivity) := by
    apply qdiv_ext
    intro Q
    rw [hglobal Q,cartierGeometricQDivisor_coefficient]
    ring
  obtain ⟨EH,hEHsupport,hEH⟩ := DivisorMetric.exists_divisorMetric F
  refine ⟨d,F,EH,hd,hD,hEHsupport,hEH,?_,hglobal⟩
  rw [MeteredDivisorScaling.smul_support _ hc.ne',hEHsupport,hD,cartierGeometricQDivisor_support F hc]

/-- ORIGINAL compact D,u and their genuine complete native logarithms ALONE
manufacture the actual geometric Cartier representation, genuine metric,
exact original support, full local type and an actual globally bounded REAL
residual. No metered divisor or bounded residual certificate is a premise. -/
theorem compact_exists_actual_metered_log_dictionary [CompactSpace M]
    (D : EffectiveGeometricQDivisor (m+1) M) (u : M → EReal)
    (hu : NativeHasLogSingularitiesAlong D u) :
    ∃ (d : ℕ) (F : EffectiveDivisor (m+1) M) (EH : MeteredEffectiveQDivisor (m+1) M),
      0<d ∧ D=cartierGeometricQDivisor F (1/(d : ℚ)) (by positivity) ∧
      DivisorMetric.IsDivisorMetric F EH ∧
      (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH).support=D.support ∧
      HasLocalDivisorLogType (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH) u ∧
      Nonempty (HasLogSingularitiesAlong
        (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH) u) := by
  obtain ⟨d,F,EH,hd,hD,_hEHsupport,hEH,hsupport,hcoeff⟩ := compact_exists_actual_metered_representation D
  have hlocal := native_log_metric_local_type hu F d hd hcoeff EH hEH
  exact ⟨d,F,EH,hd,hD,hEH,hsupport,hlocal,hlocal.exists_bounded_divisorResidual⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
