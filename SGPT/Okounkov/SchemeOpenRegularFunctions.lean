import SGPT.Okounkov.SchemeAffineStalkGerm
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient

/-!
# Original regular sections as actual analytic functions

The canonical function is evaluated from the original scheme stalk, through
the already constructed native stalk map.  Existing arbitrary-open local
representatives prove its holomorphy and full germ readback.  Original ring
operations and restrictions survive, and actual units are nowhere zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance openRegularPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance openRegularPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- Canonical values of the original regular section on its actual analytic
open, totalized by zero outside that open. -/
def schemeOpenRegularFunction (U : X.Opens) (r : Γ(X, U)) : SchemeComplexPoint f → ℂ := by
  classical
  letI := E.isSeparated
  letI := E.quasiCompact
  exact fun p => if hp : schemeComplexPointImage f p ∈ U then
    NativeHolGerm.eval (schemeNativeStalkGerm f n p
      (X.presheaf.germ U (schemeComplexPointImage f p) hp r)) else 0

/-- Every value uses exactly the original germ and the original native stalk
map, without choosing a local representative. -/
theorem schemeOpenRegularFunction_apply (U : X.Opens) (r : Γ(X, U))
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    letI := E.isSeparated
    letI := E.quasiCompact
    schemeOpenRegularFunction f n E U r p =
      NativeHolGerm.eval (schemeNativeStalkGerm f n p
        (X.presheaf.germ U (schemeComplexPointImage f p) hp r)) := by
  let := E.isSeparated
  let := E.quasiCompact
  simp only [schemeOpenRegularFunction, dif_pos hp]

private theorem exists_openRegularFunction_representative
    (U : X.Opens) (r : Γ(X, U)) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (H : SchemeComplexPoint f → ℂ) (hH : HolomorphicAt n H p),
      schemeOpenRegularFunction f n E U r =ᶠ[𝓝 p] H ∧
      schemeNativeStalkGerm f n p (X.presheaf.germ U (schemeComplexPointImage f p) hp r) =
        NativeHolGerm.mk H hH := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  obtain ⟨V, hV, hpV, hVU, H, hH, hread⟩ :=
    schemeRegularSection_locally_holomorphic f n E U r p hp
  have hHp : HolomorphicAt n H p :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hH hpV
  refine ⟨H, hHp, ?_, ?_⟩
  · filter_upwards [hV.mem_nhds hpV] with q hq
    have hqU : schemeComplexPointImage f q ∈ U := hVU hq
    have hHq : HolomorphicAt n H q :=
      InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hH hq
    have heq : schemeNativeStalkGerm f n q
        (X.presheaf.germ U (schemeComplexPointImage f q) hqU r) =
          NativeHolGerm.mk H hHq := by
      apply Subtype.ext
      exact hread q hq hqU
    rw [schemeOpenRegularFunction_apply f n E U r q hqU, heq, NativeHolGerm.eval_mk]
  · apply Subtype.ext
    exact hread p hpV hp

/-- The canonical realization is genuinely holomorphic at every point of the
actual original analytic open. -/
theorem schemeOpenRegularFunction_holomorphicAt (U : X.Opens) (r : Γ(X, U))
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    HolomorphicAt n (schemeOpenRegularFunction f n E U r) p := by
  obtain ⟨H, hH, hEq, _⟩ := exists_openRegularFunction_representative f n E U r p hp
  exact hH.congr hEq.symm

/-- The whole native germ of the canonical function is exactly the image of
the original section germ, rather than merely its point value. -/
theorem schemeOpenRegularFunction_germ (U : X.Opens) (r : Γ(X, U))
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    letI := E.isSeparated
    letI := E.quasiCompact
    NativeHolGerm.mk (schemeOpenRegularFunction f n E U r)
        (schemeOpenRegularFunction_holomorphicAt f n E U r p hp) =
      schemeNativeStalkGerm f n p
        (X.presheaf.germ U (schemeComplexPointImage f p) hp r) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨H, hH, hEq, hgerm⟩ := exists_openRegularFunction_representative f n E U r p hp
  exact (NativeHolGerm.mk_eq_mk_iff.mpr hEq).trans hgerm.symm

/-- Genuine manifold holomorphy holds on the entire original analytic open. -/
theorem schemeOpenRegularFunction_mdifferentiableOn (U : X.Opens) (r : Γ(X, U)) :
    MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (schemeOpenRegularFunction f n E U r) (schemeComplexPointImage f ⁻¹' U) := by
  intro p hp
  exact (schemeOpenRegularFunction_holomorphicAt f n E U r p hp).mdifferentiableAt.mdifferentiableWithinAt

theorem schemeOpenRegularFunction_add (U : X.Opens) (r s : Γ(X, U)) :
    EqOn (schemeOpenRegularFunction f n E U (r + s))
      (fun p => schemeOpenRegularFunction f n E U r p + schemeOpenRegularFunction f n E U s p)
      (schemeComplexPointImage f ⁻¹' U) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro p hp
  have hpU : schemeComplexPointImage f p ∈ U := hp
  simp only [schemeOpenRegularFunction, dif_pos hpU, map_add]

theorem schemeOpenRegularFunction_mul (U : X.Opens) (r s : Γ(X, U)) :
    EqOn (schemeOpenRegularFunction f n E U (r * s))
      (fun p => schemeOpenRegularFunction f n E U r p * schemeOpenRegularFunction f n E U s p)
      (schemeComplexPointImage f ⁻¹' U) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro p hp
  have hpU : schemeComplexPointImage f p ∈ U := hp
  simp only [schemeOpenRegularFunction, dif_pos hpU, map_mul]

theorem schemeOpenRegularFunction_one (U : X.Opens) :
    EqOn (schemeOpenRegularFunction f n E U 1) (fun _ => 1)
      (schemeComplexPointImage f ⁻¹' U) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro p hp
  have hpU : schemeComplexPointImage f p ∈ U := hp
  simp only [schemeOpenRegularFunction, dif_pos hpU, map_one]

/-- The genuine presheaf restriction identity survives on every point of the
smaller analytic open. -/
theorem schemeOpenRegularFunction_restrict (U V : X.Opens) (hUV : U ≤ V) (r : Γ(X, V)) :
    EqOn (schemeOpenRegularFunction f n E U (X.presheaf.map (homOfLE hUV).op r))
      (schemeOpenRegularFunction f n E V r) (schemeComplexPointImage f ⁻¹' U) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro p hp
  have hres : X.presheaf.germ U (schemeComplexPointImage f p) hp
      (X.presheaf.map (homOfLE hUV).op r) =
        X.presheaf.germ V (schemeComplexPointImage f p) (hUV hp) r :=
    congrArg (fun h : Γ(X, V) ⟶ X.presheaf.stalk (schemeComplexPointImage f p) => h r)
      (X.presheaf.germ_res (homOfLE hUV) (schemeComplexPointImage f p) hp)
  rw [schemeOpenRegularFunction_apply f n E U _ p hp,
    schemeOpenRegularFunction_apply f n E V r p (hUV hp), hres]

/-- Actual regular units, including genuine original frame transitions, give
nowhere-zero analytic functions on their entire original overlap. -/
theorem schemeOpenRegularFunction_unit_ne_zero (U : X.Opens) (r : Γ(X, U)ˣ)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    schemeOpenRegularFunction f n E U r p ≠ 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  rw [schemeOpenRegularFunction_apply f n E U r p hp]
  exact (((r.isUnit.map (X.presheaf.germ U (schemeComplexPointImage f p) hp).hom).map
    (schemeNativeStalkGerm f n p)).map NativeHolGerm.eval).ne_zero

end SGPT.Okounkov
