import SGPT.Projective.AlgebraicCurveClosedPoint
import SGPT.NAPotential.SmoothDivisorNormalOrder
import SGPT.Foundations.Schemes.LineSectionZeroSubscheme

/-! The SAME original algebraic section's true local principal quotient
length equals its actual native analytic normal order, with no order/length
comparison premise. Blueprint: algebraic-curve-native-degree.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.FSPos
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder
open scoped nonZeroDivisors

/-- Literal original frame coefficient in the SAME original scheme stalk. -/
def sectionStalkCoefficient {X : Scheme.{0}} {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (i : a.I)
    (x : X) (hx : x ∈ a.opens i) : X.presheaf.stalk x :=
  X.presheaf.germ (a.opens i) x hx
    ((a.frame i).coefficients (𝟙 (a.opens i)) (L.presheaf.map (a.opens i).leTop.op s))

/-- Actual integral restriction and the actual original germ map produce
nonzero local coefficients of the SAME nonzero original global section. -/
theorem sectionStalkCoefficient_ne_zero {X : Scheme.{0}} [IsIntegral X] {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0) (i : a.I)
    (x : X) (hx : x ∈ a.opens i) : sectionStalkCoefficient a s i x hx ≠ 0 := by
  let : Nonempty (a.opens i) := ⟨⟨x, hx⟩⟩
  have hr := sectionCoefficient_ne_zero a s hs (a.frame i) (𝟙 (a.opens i))
  intro hg
  apply hr
  apply germ_injective_of_isIntegral X x hx
  simpa only [sectionStalkCoefficient, map_zero] using hg

/-- The full actual principal quotient length is the genuine normalized
scheme order in its SAME original fraction field, without infinity loss. -/
theorem principalLength_eq_schemeOrder_toNat {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] (x : X) (hx : Order.coheight x = 1)
    (g : X.presheaf.stalk x) (hg : g ≠ 0) :
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸ Ideal.span {g}) =
      ((Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x).toNat : ℕ∞) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  let k := (Ring.ord (X.presheaf.stalk x) g).toNat
  have hfinite : Ring.ord (X.presheaf.stalk x) g ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  have hk : Ring.ord (X.presheaf.stalk x) g = (k : ℕ∞) :=
    (ENat.natCast_toNat hfinite).symm
  have hgF : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg
  have hord : Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x = (k : ℤ) := by
    apply (Scheme.ord_eq_iff hx hgF).mpr
    change Ring.ordFrac (X.presheaf.stalk x) (algebraMap (X.presheaf.stalk x) X.functionField g) = _
    rw [Ring.ordFrac_eq_ord _ hg,
      Ring.ordMonoidWithZeroHom_eq_coe (X.presheaf.stalk x)
        (mem_nonZeroDivisors_iff_ne_zero.mpr hg) hk]
  change Ring.ord (X.presheaf.stalk x) g = _
  rw [hord, Int.toNat_natCast]
  exact hk

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 1 f]

local instance curveLengthTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance curveLengthCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 1
local instance curveLengthManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold 1 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 1

/-- At EVERY original closed curve point, actual native coordinates are
produced and identify the full literal original section coefficient's
principal quotient length with its SAME genuine analytic zero order.
All original frames are retained; no length/order/centre output is input. -/
theorem exists_section_length_eq_normalOrder (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    let := E.isSeparated
    let := E.quasiCompact
    let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (0 + 1)
    let : IsComplexManifold (0 + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (0 + 1)
    ∃ (y : SchemeComplexPoint f), schemeComplexPointImage f y = x ∧
      ∃ Ψ : DivisorFlattening (m := 0) (schemeNativeAlgebraicTrace f (closure {x})) y,
        ∀ (i : a.I) (hy : schemeComplexPointImage f y ∈ a.opens i),
        Module.length (X.presheaf.stalk (schemeComplexPointImage f y))
          ((X.presheaf.stalk (schemeComplexPointImage f y)) ⧸
            Ideal.span {sectionStalkCoefficient a s i (schemeComplexPointImage f y) hy}) =
          normalOrder Ψ (stalkToModel f 1 y
            (sectionStalkCoefficient a s i (schemeComplexPointImage f y) hy)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (0 + 1)
  let : IsComplexManifold (0 + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (0 + 1)
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  dsimp only
  have hx1 := closedPoint_coheight_eq_one f x hx
  obtain ⟨y, hxy, Ψ, hord⟩ := SGPT.NAPotential.SmoothDivisorNormalOrder.exists_nativeNormalOrder f 0 hx1
  have himage : schemeComplexPointImage f y = x := by
    have hmem := specializes_iff_mem_closure.mp hxy
    rw [hx.closure_eq] at hmem
    exact hmem
  refine ⟨y, himage, Ψ, fun i hy => ?_⟩
  let g := sectionStalkCoefficient a s i (schemeComplexPointImage f y) hy
  have hg : g ≠ 0 := sectionStalkCoefficient_ne_zero a s hs i _ hy
  have hy1 : Order.coheight (schemeComplexPointImage f y) = 1 := himage.symm ▸ hx1
  have hmodel : stalkToModel f 1 y g ≠ 0 :=
    (map_ne_zero_iff _ (SGPT.NAPotential.AffineDivisorFlattening.stalkToModel_faithfullyFlat f 0 y).injective).mpr hg
  have hnormal := normalOrder_ne_top Ψ hmodel
  have horder := (congrArg
    (fun z : X => Scheme.ord (algebraMap (X.presheaf.stalk (schemeComplexPointImage f y))
      X.functionField g) z) himage).trans (hord g hg)
  have hlength := principalLength_eq_schemeOrder_toNat _ hy1 g hg
  rw [horder, Int.toNat_natCast] at hlength
  exact hlength.trans (ENat.natCast_toNat hnormal)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
