import SGPT.NAPotential.DivDict2Blowup
import SGPT.Foundations.Analysis.Pending.OverBaseJacobianOrder
import SGPT.Foundations.Analysis.Pending.MultiplierPullbackNonzero
import SGPT.Foundations.Analysis.Pending.CoherentIdealCommonModelOrder

/-!
# The analytic order along a prime divisor of algebraic functions


`X` is a smooth projective integral complex scheme of dimension `m + 1`, `X(ℂ)` its complex
manifold, and `p` an analytic presentation of a prime divisor over `X(ℂ)`
(`SGPT.PSH.CompactPrimeOver.PrimePresentation`: a modification `π : Y → X(ℂ)` and a smooth
connected hypersurface `D ⊆ Y`).  Fix a point `y₀ ∈ D`, a flattening `Φ₀` of `D` at `y₀`, and
let `P₀ ∈ X` be the scheme point of `π(y₀)`.

For a germ `g ∈ 𝒪_{X,P₀}` of a regular function, `stalkOrd p y₀ Φ₀ g ∈ ℕ ∪ {∞}` is the order of
vanishing along `D` at `y₀` of the pull-back `g^an ∘ π` of its analytic germ
(`SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder.pullbackNormalOrder`).  It is

* multiplicative (`stalkOrd_mul`), ultrametric (`min_le_stalkOrd_add`), `0` on units
  (`stalkOrd_one`), `∞` exactly on `0` (`stalkOrd_zero`, `stalkOrd_ne_top`; the analytic germ map
  of an integral scheme is injective and a modification does not collapse nonzero germs).

For a regular function `r` on an open `U ∋ P₀` it is the order of `r^an ∘ π`
(`stalkOrd_germ`).  These are the axioms of a discrete valuation of `𝒪_{X,P₀}` with values in
`ℕ`; the valuation of the function field `ℂ(X)` it defines is built in `TowerAlgValuation`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.TowerAlg

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder HironakaHolomorphicJetRankLoci
open SGPT.PSH.CompactPrimeOver

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance towerAlgOrderPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance towerAlgOrderPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance towerAlgOrderPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-! ### Holomorphic representatives of algebraic germs -/

section Rep

variable (m) in
/-- A holomorphic representative near `x` of the analytic germ of `g ∈ 𝒪_{X,x}`. -/
def stalkRep (x : SchemeComplexPoint f) (g : X.presheaf.stalk (schemeComplexPointImage f x)) :
    SchemeComplexPoint f → ℂ :=
  (NativeHolGerm.exists_eq_mk (schemeNativeStalkGerm f (m + 1) x g)).choose

theorem stalkRep_holomorphicAt (x : SchemeComplexPoint f)
    (g : X.presheaf.stalk (schemeComplexPointImage f x)) :
    HolomorphicAt (m + 1) (stalkRep m x g) x :=
  (NativeHolGerm.exists_eq_mk (schemeNativeStalkGerm f (m + 1) x g)).choose_spec.choose

theorem schemeNativeStalkGerm_eq_mk_stalkRep (x : SchemeComplexPoint f)
    (g : X.presheaf.stalk (schemeComplexPointImage f x)) :
    schemeNativeStalkGerm f (m + 1) x g =
      NativeHolGerm.mk (stalkRep m x g) (stalkRep_holomorphicAt x g) :=
  (NativeHolGerm.exists_eq_mk (schemeNativeStalkGerm f (m + 1) x g)).choose_spec.choose_spec

/-- Any holomorphic function with the same analytic germ agrees with the representative near
`x`. -/
theorem stalkRep_eventuallyEq (x : SchemeComplexPoint f)
    (g : X.presheaf.stalk (schemeComplexPointImage f x)) {F : SchemeComplexPoint f → ℂ}
    (hF : HolomorphicAt (m + 1) F x)
    (hgF : schemeNativeStalkGerm f (m + 1) x g = NativeHolGerm.mk F hF) :
    stalkRep m x g =ᶠ[𝓝 x] F :=
  NativeHolGerm.mk_eq_mk_iff.mp ((schemeNativeStalkGerm_eq_mk_stalkRep x g).symm.trans hgF)

end Rep

/-! ### Germs in charts -/

section Chart

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- A function that does not vanish identically near `y` has a nonzero chart germ. -/
theorem chartTranslatedGerm_ne_zero {y : Y} {F : Y → ℂ} (hF : HolomorphicAt (m + 1) F y)
    (hne : ∃ᶠ z in 𝓝 y, F z ≠ 0) :
    chartTranslatedGerm y y (mem_chart_source _ y) F hF ≠ 0 := by
  intro h0
  let e := chartAt (ComplexModel (m + 1)) y
  have h1 : (fun z => F (e.symm (z + e y))) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      (0 : ComplexModel (m + 1) → ℂ) := by
    have h0' : chartTranslatedGerm y y (mem_chart_source _ y) F hF =
        HolGerm.mk (0 : ComplexModel (m + 1) → ℂ) eventually_differentiableAt_zero := by
      rw [h0, HolGerm.mk_zero]
    unfold chartTranslatedGerm translatedGerm at h0'
    exact HolGerm.mk_eq_mk_iff.mp h0'
  have ht : Tendsto (fun w : Y => e w - e y) (𝓝 y) (𝓝 0) := by
    have hc : ContinuousAt (fun w : Y => e w - e y) y :=
      (e.continuousAt (mem_chart_source _ y)).sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  have h2 : ∀ᶠ w in 𝓝 y, F w = 0 := by
    filter_upwards [ht.eventually h1, e.open_source.mem_nhds (mem_chart_source _ y)] with w hw hws
    simpa only [sub_add_cancel, e.left_inv hws, Pi.zero_apply] using hw
  exact (hne.and_eventually h2).exists.elim fun _ h => h.1 h.2

theorem chartTranslatedGerm_add {y : Y} {F G : Y → ℂ} (hF : HolomorphicAt (m + 1) F y)
    (hG : HolomorphicAt (m + 1) G y) :
    chartTranslatedGerm y y (mem_chart_source _ y) (fun w => F w + G w) (hF.add hG) =
      chartTranslatedGerm y y (mem_chart_source _ y) F hF +
        chartTranslatedGerm y y (mem_chart_source _ y) G hG := by
  unfold chartTranslatedGerm translatedGerm
  rw [← HolGerm.mk_add]

theorem functionNormalOrder_add {E : Set Y} {y : Y} (Φ : DivisorFlattening (m := m) E y)
    {F G : Y → ℂ} (hF : HolomorphicAt (m + 1) F y) (hG : HolomorphicAt (m + 1) G y) :
    min (functionNormalOrder Φ F hF) (functionNormalOrder Φ G hG) ≤
      functionNormalOrder Φ (fun w => F w + G w) (hF.add hG) := by
  unfold functionNormalOrder normalOrder
  rw [chartTranslatedGerm_add hF hG]
  exact min_le_emultiplicity_add

end Chart

/-! ### The order along `D` of algebraic germs -/

variable (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
  {y₀ : p.model} (Φ₀ : DivisorFlattening (m := m) p.divisor y₀)

/-- **The analytic order along `D` at `y₀`** of a germ `g ∈ 𝒪_{X,P₀}` (`P₀` the scheme point of
`π(y₀)`): the order of vanishing along `D` of `g^an ∘ π`. -/
def stalkOrd (g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) : ℕ∞ :=
  pullbackNormalOrder p.modification Φ₀ (stalkRep m (p.projection y₀) g)
    (stalkRep_holomorphicAt (p.projection y₀) g)

/-- The order can be computed on any holomorphic function with the analytic germ of `g`. -/
theorem stalkOrd_eq (g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀)))
    {F : SchemeComplexPoint f → ℂ} (hF : HolomorphicAt (m + 1) F (p.projection y₀))
    (hgF : schemeNativeStalkGerm f (m + 1) (p.projection y₀) g = NativeHolGerm.mk F hF) :
    stalkOrd p Φ₀ g = pullbackNormalOrder p.modification Φ₀ F hF :=
  pullbackNormalOrder_congr p.modification Φ₀ _ hF (stalkRep_eventuallyEq _ g hF hgF)

theorem stalkOrd_mul (g h : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) :
    stalkOrd p Φ₀ (g * h) = stalkOrd p Φ₀ g + stalkOrd p Φ₀ h := by
  have hg := stalkRep_holomorphicAt (m := m) (p.projection y₀) g
  have hh := stalkRep_holomorphicAt (m := m) (p.projection y₀) h
  have hgh : schemeNativeStalkGerm f (m + 1) (p.projection y₀) (g * h) =
      NativeHolGerm.mk (fun x => stalkRep m (p.projection y₀) g x * stalkRep m (p.projection y₀) h x)
        (hg.mul hh) := by
    rw [map_mul, schemeNativeStalkGerm_eq_mk_stalkRep, schemeNativeStalkGerm_eq_mk_stalkRep]
    rfl
  rw [stalkOrd_eq p Φ₀ _ _ hgh]
  exact OverBaseJacobianOrder.functionNormalOrder_mul Φ₀ _ _ _ _

theorem min_le_stalkOrd_add (g h : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))) :
    min (stalkOrd p Φ₀ g) (stalkOrd p Φ₀ h) ≤ stalkOrd p Φ₀ (g + h) := by
  have hg := stalkRep_holomorphicAt (m := m) (p.projection y₀) g
  have hh := stalkRep_holomorphicAt (m := m) (p.projection y₀) h
  have hgh : schemeNativeStalkGerm f (m + 1) (p.projection y₀) (g + h) =
      NativeHolGerm.mk (fun x => stalkRep m (p.projection y₀) g x + stalkRep m (p.projection y₀) h x)
        (hg.add hh) := by
    rw [map_add, schemeNativeStalkGerm_eq_mk_stalkRep, schemeNativeStalkGerm_eq_mk_stalkRep]
    rfl
  rw [stalkOrd_eq p Φ₀ _ _ hgh]
  exact functionNormalOrder_add Φ₀ _ _

theorem stalkOrd_zero : stalkOrd p Φ₀ 0 = ⊤ := by
  have h0 : schemeNativeStalkGerm f (m + 1) (p.projection y₀) 0 =
      NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0) := by
    rw [map_zero]
    rfl
  rw [stalkOrd_eq p Φ₀ _ _ h0]
  unfold pullbackNormalOrder functionNormalOrder
  have : chartTranslatedGerm y₀ y₀ (mem_chart_source _ y₀) ((fun _ => (0 : ℂ)) ∘ p.projection)
      ((holomorphicAt_const 0).comp_contMDiff
        (Eventually.of_forall fun _ => p.modification.1.contMDiffAt)) = 0 := by
    unfold chartTranslatedGerm translatedGerm
    rw [← HolGerm.mk_zero]
    rfl
  rw [this, normalOrder_zero]

theorem stalkOrd_one : stalkOrd p Φ₀ 1 = 0 := by
  have h1 : schemeNativeStalkGerm f (m + 1) (p.projection y₀) 1 =
      NativeHolGerm.mk (fun _ => (1 : ℂ)) (holomorphicAt_const 1) := by
    rw [map_one]
    rfl
  rw [stalkOrd_eq p Φ₀ _ _ h1]
  exact OverBaseJacobianOrder.functionNormalOrder_eq_zero_of_ne_zero Φ₀ _ _ one_ne_zero

/-- **The order of a nonzero germ is finite**: the analytic germ map of the integral scheme `X`
is injective, and the modification `π` does not collapse nonzero germs. -/
theorem stalkOrd_ne_top [IsIntegral X] {g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀))}
    (hg : g ≠ 0) : stalkOrd p Φ₀ g ≠ ⊤ := by
  have hhol := stalkRep_holomorphicAt (m := m) (p.projection y₀) g
  have hne : ∃ᶠ x in 𝓝 (p.projection y₀), stalkRep m (p.projection y₀) g x ≠ 0 := by
    intro hev
    apply hg
    apply schemeNativeStalkGerm_injective f (m + 1) (p.projection y₀)
    rw [map_zero, schemeNativeStalkGerm_eq_mk_stalkRep]
    have h0 : (0 : NativeHolGerm (m + 1) (SchemeComplexPoint f) (p.projection y₀)) =
        NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0) := rfl
    rw [h0]
    apply NativeHolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hev] with x hx
    exact not_ne_iff.mp hx
  have hcomp := MultiplierPullbackNonzero.frequently_comp_ne_zero p.modification y₀ hhol hne
  unfold stalkOrd pullbackNormalOrder functionNormalOrder
  exact normalOrder_ne_top Φ₀ (chartTranslatedGerm_ne_zero _ hcomp)

/-- The order of the germ of a regular function `r` on an open `U ∋ P₀` is the order along `D`
of `r^an ∘ π`. -/
theorem stalkOrd_germ (E : ClosedProjectiveEmbedding f) (U : X.Opens)
    (hU : schemeComplexPointImage f (p.projection y₀) ∈ U) (r : Γ(X, U)) :
    stalkOrd p Φ₀ ((X.presheaf.germ U _ hU).hom r) =
      pullbackNormalOrder p.modification Φ₀ (schemeOpenRegularFunction f (m + 1) E U r)
        (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U r _ hU) :=
  stalkOrd_eq p Φ₀ _ _ (schemeOpenRegularFunction_germ f (m + 1) E U r _ hU).symm

end SGPT.NAPotential.TowerAlg

end
