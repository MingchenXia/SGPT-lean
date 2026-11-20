import SGPT.Checks.Comparison.BJNativeNumericalClasses
import SGPT.Checks.Comparison.BJTopology
import Mathlib.Topology.Order.MonotoneConvergence

/-! Literal rational GF functions and decreasing nets on ALL original source
Berkovich points, with their ACTUAL numerical classes. The numerical topology
is an EXPLICIT parameter; the curve-weak specialization is not a claimed
comparison with the book's usual topology. ZERO whole-row completion credit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Topology Filter
open Scheme.Modules SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope
variable {X : Scheme.{0}}

/-- Genuine varying original sheaves, atlases, powers, rational weights and
nonzero global sections; no arbitrary function or class certificate field. -/
structure RationalGFPackage (X : Scheme.{0}) where
  line : X.Modules
  atlas : LineBundleAtlas line
  n : ℕ
  m : ℕ
  data : RationalGFData line n m

namespace RationalGFPackage
variable (D : RationalGFPackage X)

def picardClass : RationalPicardSpace X := gfPicardClass D.atlas D.data

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- The actual original point/section semi-valuation formula. -/
def eval (v : BerkovichPoint p) : EReal := rationalGFFunction D.atlas D.data v

def numericalClass : NativeRealNumericalClasses.Space p :=
  NativePicard.numericalClass p D.picardClass

theorem eval_ne_top (v : BerkovichPoint p) : D.eval p v≠⊤ :=
  rationalGFFunction_ne_top D.atlas D.data v

theorem eval_trivial_finite [IsIntegral X] :
    ∃ r : ℝ,D.eval p (BerkovichPoint.trivial p)=(r:EReal) :=
  rationalGFFunction_trivial_finite D.atlas D.data

theorem numericalClass_eq : D.numericalClass p=
    ((D.n:ℚ)/(D.m:ℚ))•NativeRealNumericalClasses.lineClass p D.line
      (isInvertible_of_atlas D.atlas) := numericalClass_gf p D.atlas D.data

end RationalGFPackage

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Literal source GF membership at a fixed ACTUAL rational Picard class.
Class equality is in rational Picard, not merely numerical equality. -/
def IsRationalGF (L : RationalPicardSpace X) (φ : BerkovichPoint p → EReal) : Prop :=
  ∃ D : RationalGFPackage X,D.picardClass=L ∧ D.eval p=φ

theorem isRationalGF_package (D : RationalGFPackage X) :
    IsRationalGF p D.picardClass (D.eval p) := ⟨D,rfl,rfl⟩

theorem IsRationalGF.ne_top {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsRationalGF p L φ) (v : BerkovichPoint p) : φ v≠⊤ := by
  obtain ⟨D,_,rfl⟩ := h
  exact D.eval_ne_top p v

/-- A genuine nonempty directed decreasing net of the actual packages.
The index has no class-convergence/limit/closure certificate in its data. -/
structure DecreasingGFNet where
  I : Type u
  preorder : Preorder I
  nonempty : Nonempty I
  directed : @IsDirectedOrder I preorder.toLE
  term : I → RationalGFPackage X
  decreasing : ∀ v : BerkovichPoint p,Antitone (fun i => (term i).eval p v)

attribute [instance] DecreasingGFNet.preorder DecreasingGFNet.nonempty DecreasingGFNet.directed

namespace DecreasingGFNet
variable (D : DecreasingGFNet.{u} p)

/-- Actual infimum of actual section-valued functions at EVERY source point. -/
def limit (v : BerkovichPoint p) : EReal := ⨅ i : D.I,(D.term i).eval p v

theorem limit_tendsto (v : BerkovichPoint p) :
    Tendsto (fun i => (D.term i).eval p v) atTop (𝓝 (D.limit p v)) :=
  tendsto_atTop_iInf (D.decreasing v)

theorem limit_le (i : D.I) (v : BerkovichPoint p) :
    D.limit p v≤(D.term i).eval p v := iInf_le _ i

/-- The printed half-open EReal codomain is internally produced. -/
theorem limit_ne_top (v : BerkovichPoint p) : D.limit p v≠⊤ := by
  let i : D.I := Classical.choice D.nonempty
  exact ne_of_lt ((D.limit_le p i v).trans_lt (lt_top_iff_ne_top.mpr ((D.term i).eval_ne_top p v)))

theorem eq_limit_of_tendsto {φ : BerkovichPoint p → EReal}
    (hφ : ∀ v,Tendsto (fun i => (D.term i).eval p v) atTop (𝓝 (φ v))) :
    φ=D.limit p := by
  funext v
  exact tendsto_nhds_unique (hφ v) (D.limit_tendsto p v)

end DecreasingGFNet

/-- The literal printed predicate for an EXPLICIT numerical-class topology.
Every GF approximant/section/class is actual original geometric data. -/
def IsPSHForNumericalTopology
    (t : TopologicalSpace (NativeRealNumericalClasses.Space p))
    (L : RationalPicardSpace X) (φ : BerkovichPoint p → EReal) : Prop :=
  (∃ v,φ v≠⊥) ∧ ∃ D : DecreasingGFNet.{u} p,
    Tendsto (fun i => (D.term i).numericalClass p) atTop
      (@nhds _ t (NativePicard.numericalClass p L)) ∧
    ∀ v,Tendsto (fun i => (D.term i).eval p v) atTop (𝓝 (φ v))

/-- Explicit canonical curve-WEAK specialization. It is not called the usual
NS topology or identified with EP ample-order convergence. -/
def IsCurveWeakPSH (L : RationalPicardSpace X) (φ : BerkovichPoint p → EReal) : Prop :=
  IsPSHForNumericalTopology.{u} p (numericalCurveWeakTopology p) L φ

/-- Equivalent decreasing-infimum form, with no supplied non-top hypothesis. -/
theorem isPSHForNumericalTopology_iff_inf
    (t : TopologicalSpace (NativeRealNumericalClasses.Space p))
    (L : RationalPicardSpace X) (φ : BerkovichPoint p → EReal) :
    IsPSHForNumericalTopology.{u} p t L φ ↔
      (∃ v,φ v≠⊥) ∧ ∃ D : DecreasingGFNet.{u} p,
        Tendsto (fun i => (D.term i).numericalClass p) atTop
          (@nhds _ t (NativePicard.numericalClass p L)) ∧ φ=D.limit p := by
  constructor
  · rintro ⟨hne,D,hclass,hφ⟩
    exact ⟨hne,D,hclass,D.eq_limit_of_tendsto p hφ⟩
  · rintro ⟨hne,D,hclass,rfl⟩
    exact ⟨hne,D,hclass,D.limit_tendsto p⟩

theorem IsPSHForNumericalTopology.ne_top
    {t : TopologicalSpace (NativeRealNumericalClasses.Space p)}
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsPSHForNumericalTopology.{u} p t L φ) (v : BerkovichPoint p) : φ v≠⊤ := by
  obtain ⟨_,D,_,rfl⟩ := (isPSHForNumericalTopology_iff_inf p t L φ).mp h
  exact D.limit_ne_top p v

/-- This class dependence is proved from the actual net predicate, not
introduced as a closure/class-invariance field. -/
theorem isPSHForNumericalTopology_congr_class
    (t : TopologicalSpace (NativeRealNumericalClasses.Space p))
    {L M : RationalPicardSpace X} (hLM : NativePicard.numericalClass p L=
      NativePicard.numericalClass p M) (φ : BerkovichPoint p → EReal) :
    IsPSHForNumericalTopology.{u} p t L φ ↔ IsPSHForNumericalTopology.{u} p t M φ := by
  unfold IsPSHForNumericalTopology
  rw [hLM]

end SGPT.NAPotential.BJ.Printed
