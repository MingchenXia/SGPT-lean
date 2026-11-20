import SGPT.Okounkov.SchemeOpenRegularFunctions
import SGPT.Foundations.Schemes.LineBundleSectionRing
import Mathlib.Topology.VectorBundle.Basic

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

local instance lineAtlasPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance lineAtlasPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- The actual original frame transition on its entire actual analytic overlap. -/
def schemeFrameTransition {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) : SchemeComplexPoint f → ℂ :=
  schemeOpenRegularFunction f n E (U ⊓ V)
    (localBundleFrameTransition α β (homOfLE inf_le_left) (homOfLE inf_le_right)).val

theorem schemeFrameTransition_holomorphicAt {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (p : SchemeComplexPoint f)
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    HolomorphicAt n (schemeFrameTransition f n E α β) p :=
  schemeOpenRegularFunction_holomorphicAt f n E (U ⊓ V) _ p ⟨hpU, hpV⟩

theorem schemeFrameTransition_ne_zero {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (p : SchemeComplexPoint f)
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    schemeFrameTransition f n E α β p ≠ 0 :=
  schemeOpenRegularFunction_unit_ne_zero f n E (U ⊓ V) _ p ⟨hpU, hpV⟩

/-- The same original transition, on any smaller common scheme open, has
the identical entire analytic function there. -/
theorem schemeFrameTransition_on_subopen {L : X.Modules} {U V W : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (hWU : W ≤ U) (hWV : W ≤ V) :
    EqOn (schemeOpenRegularFunction f n E W
      (localBundleFrameTransition α β (homOfLE hWU) (homOfLE hWV)).val)
      (schemeFrameTransition f n E α β) (schemeComplexPointImage f ⁻¹' W) := by
  have hW : W ≤ U ⊓ V := le_inf hWU hWV
  have hreg : (localBundleFrameTransition α β (homOfLE hWU) (homOfLE hWV)).val =
      X.presheaf.map (homOfLE hW).op
        (localBundleFrameTransition α β (homOfLE inf_le_left) (homOfLE inf_le_right)).val := by
    exact localBundleFrameTransition_restrict α β
      (homOfLE inf_le_left) (homOfLE inf_le_right) (homOfLE hW)
  rw [hreg]
  exact schemeOpenRegularFunction_restrict f n E W (U ⊓ V) hW _

theorem schemeFrameTransition_self {L : X.Modules} {U : X.Opens}
    (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) : schemeFrameTransition f n E α α p = 1 := by
  have hunit : localBundleFrameTransition α α
      (homOfLE inf_le_left : U ⊓ U ⟶ U) (homOfLE inf_le_right) = 1 := by
    have hi : (homOfLE inf_le_left : U ⊓ U ⟶ U) = homOfLE inf_le_right := Subsingleton.elim _ _
    rw [hi]
    simp only [localBundleFrameTransition, sectionFrameTransition_self]
  change schemeOpenRegularFunction f n E (U ⊓ U) _ p = 1
  rw [hunit]
  exact schemeOpenRegularFunction_one f n E (U ⊓ U) ⟨hp, hp⟩

theorem schemeFrameTransition_cocycle {L : X.Modules} {U V Z : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (γ : LocalBundleFrame L Z)
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) (hpZ : schemeComplexPointImage f p ∈ Z) :
    schemeFrameTransition f n E α γ p =
      schemeFrameTransition f n E β γ p * schemeFrameTransition f n E α β p := by
  let W : X.Opens := (U ⊓ V) ⊓ Z
  have hWU : W ≤ U := inf_le_left.trans inf_le_left
  have hWV : W ≤ V := inf_le_left.trans inf_le_right
  have hWZ : W ≤ Z := inf_le_right
  have hpW : schemeComplexPointImage f p ∈ W := ⟨⟨hpU, hpV⟩, hpZ⟩
  let r13 : Γ(X, W) := (localBundleFrameTransition α γ (homOfLE hWU) (homOfLE hWZ)).val
  let r23 : Γ(X, W) := (localBundleFrameTransition β γ (homOfLE hWV) (homOfLE hWZ)).val
  let r12 : Γ(X, W) := (localBundleFrameTransition α β (homOfLE hWU) (homOfLE hWV)).val
  have hunit : r13 = r23 * r12 := congrArg (fun q : Γ(X, W)ˣ => (q : Γ(X, W)))
    (localBundleFrameTransition_cocycle α β γ (homOfLE hWU) (homOfLE hWV) (homOfLE hWZ))
  calc
    _ = schemeOpenRegularFunction f n E W r13 p :=
      (schemeFrameTransition_on_subopen f n E α γ hWU hWZ hpW).symm
    _ = schemeOpenRegularFunction f n E W (r23 * r12) p :=
      congrArg (fun r : Γ(X, W) => schemeOpenRegularFunction f n E W r p) hunit
    _ = schemeOpenRegularFunction f n E W r23 p * schemeOpenRegularFunction f n E W r12 p :=
      schemeOpenRegularFunction_mul f n E W r23 r12 hpW
    _ = _ := congrArg₂ (· * ·)
      (schemeFrameTransition_on_subopen f n E β γ hWV hWZ hpW)
      (schemeFrameTransition_on_subopen f n E α β hWU hWV hpW)

/-- Every tensor power uses the power of ONE original analytic transition. -/
theorem schemeFrameTransition_tensorPower {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (k : ℕ)
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    schemeFrameTransition f n E (α.tensorPower k) (β.tensorPower k) p =
      schemeFrameTransition f n E α β p ^ k := by
  let := E.isSeparated
  let := E.quasiCompact
  have hp : schemeComplexPointImage f p ∈ U ⊓ V := ⟨hpU, hpV⟩
  simp only [schemeFrameTransition, localBundleFrameTransition_tensorPower,
    schemeOpenRegularFunction, dif_pos hp, Units.val_pow_eq_pow_val, map_pow]

/-- The original sheaf atlas manufactures the actual native complex line
bundle core, with no analytic atlas or gluing law supplied by the caller. -/
def schemeLineBundleCore {L : X.Modules} (a : LineBundleAtlas L) :
    VectorBundleCore ℂ (SchemeComplexPoint f) ℂ a.I where
  baseSet i := schemeComplexPointImage f ⁻¹' a.opens i
  isOpen_baseSet i := (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
  indexAt p := Classical.choose (a.covers (schemeComplexPointImage f p))
  mem_baseSet_at p := Classical.choose_spec (a.covers (schemeComplexPointImage f p))
  coordChange i j p := schemeFrameTransition f n E (a.frame i) (a.frame j) p •
    ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p hp v := by
    change schemeFrameTransition f n E (a.frame i) (a.frame i) p * v = v
    rw [schemeFrameTransition_self f n E (a.frame i) p hp, one_mul]
  continuousOn_coordChange i j := by
    have hg : ContinuousOn (schemeFrameTransition f n E (a.frame i) (a.frame j))
        ((schemeComplexPointImage f ⁻¹' a.opens i) ∩ (schemeComplexPointImage f ⁻¹' a.opens j)) :=
      fun p hp => (schemeFrameTransition_holomorphicAt f n E (a.frame i) (a.frame j)
        p hp.1 hp.2).mdifferentiableAt.continuousAt.continuousWithinAt
    exact hg.smul continuousOn_const
  coordChange_comp i j k p hp v := by
    change schemeFrameTransition f n E (a.frame j) (a.frame k) p *
      (schemeFrameTransition f n E (a.frame i) (a.frame j) p * v) =
        schemeFrameTransition f n E (a.frame i) (a.frame k) p * v
    rw [← mul_assoc, ← schemeFrameTransition_cocycle f n E (a.frame i) (a.frame j)
      (a.frame k) p hp.1.1 hp.1.2 hp.2]

end SGPT.Okounkov
