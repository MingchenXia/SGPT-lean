import SGPT.Okounkov.TranscendentalOkounkovBody
import SGPT.Okounkov.FlagCorrectionMatrix
import SGPT.Envelopes.SourceClassVolume
import SGPT.PSH.BookCurrentSpace
import SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The statement of the main theorem on transcendental Okounkov bodies

Source `thm:Okounkovtranmain` (chapter *The theory of Okounkov bodies*, Section
*Transcendental partial Okounkov bodies*, lines 1380--1400), the summary of
Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ).
Let `X` be a connected compact Kähler manifold of dimension `n > 0` with a smooth flag
`Y•`, and `α` a big class. Then `Δ_{Y•}(α)` (source `def:tradOk`, `tradOkounkovBody`) is a
convex body and

1. `vol Δ_{Y•}(α) = vol α / n!`;
2. `Δ_{Y•}(α) + Δ_{Y•}(α') ⊆ Δ_{Y•}(α + α')` for big `α'`;
3. `Δ_{W•}(π^*α) = Δ_{Y•}(α) g` for a proper bimeromorphic `π : Y → X` from a Kähler manifold
   and the lifting `(W•, g)` of `Y•` (source `def:lifting`);
4. `α ↦ Δ_{Y•}(α)` is continuous on the big cone for the Hausdorff metric;
5. for small `t > 0`, `{y : (t, y) ∈ Δ_{Y•}(α)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}((α - t{Y₁})|_{Y₁})`.

This file contains **statements only** (`def … : Prop`); nothing is proved here. It fixes the
target of the execution lanes of the formalization plan (blueprint
`claude-okounkov-transcendental.tex`).

## Formal conventions

* `X` and `Y•` are an `OriginalFlagGeometry (m + 1)` (`n = m + 1 > 0`); a class is an element
  of `RealBottChern (m + 1) X` (closed real smooth `(1,1)`-forms modulo `dd^c C^∞`, the
  project's `H^{1,1}(X, ℝ)`), bigness is `SGPT.PSH.BookCurrent.IsBig` (`def:psefclass`), the
  volume of a class is `SGPT.PSH.VariableComplexAtlas.sourceClassVolume` (`def:volcohclass`),
  the volume of a body is Lebesgue measure on `Fin n → ℝ`.
* `tradOkounkovBody F θ` depends a priori on the representative `θ`; `classOkounkovBody`
  evaluates it at a chosen representative, and `RepresentativeIndependence` (the open part of
  `def:tradOk`) states that every representative gives the same body.
* A convex body is a nonempty compact convex set (`appendix_almostsg`, empty interior allowed).
* Liftings are `IsFlagLifting` with correction matrix `flagLiftingCorrectionMatrix`
  (`def:lifting`, `prop:cormatrix`: `ν_W(π^*T) = ν_Y(T) ᵥ* cor`); the pullback class is the
  class of the pulled back representative.
* The Hausdorff metric is the Euclidean one (`EuclideanSpace.equiv`), as in
  `SGPT.AlmostSemigroup.BodyGeometry`; the topology of `H^{1,1}(X, ℝ)` is TN's quotient
  `C⁰` topology `classC0Topology` (independent of the Kähler background; on a compact Kähler
  manifold `H^{1,1}(X, ℝ)` is finite dimensional and this is its vector-space topology).
* `{Y₁}` is represented by the curvature form `E.curvature` of any unit metric `E` of the
  smooth divisor `Y₁` (Lelong--Poincaré), and `(·)|_{Y₁}` is the pullback of forms along the
  holomorphic inclusion of `Y₁` (the tail flag `F.tail`).

## Erratum (item 5)

Item 5 is false for general big classes (see `SliceFormulaBookStatement`): on the blow-up `X` of
`ℙ²` at a point and then at a point of the exceptional curve, with `E₁'` the strict transform
of the first exceptional curve (`E₁'² = -2`), `E₂` the second one (`E₂² = -1`, `E₁'·E₂ = 1`)
and `α = π^*H + E₁' + 3E₂`, every closed positive current in `α` has Lelong number `≥ 1` along
`E₁'` (Zariski/Siu decomposition), so the slices of `Δ(α)` with `Y₁ = E₁'` are empty for
`t ∈ (0, 1)`, while `(α - tE₁')|_{E₁'}` has degree `1 + 2t > 0` on `E₁' ≅ ℙ¹`, so the right-hand
side contains `0`. The book applies item 5 only to Kähler classes (`lma:Kahlerclassokounrest`),
where it holds; `KahlerSliceFormulaStatement` is the corrected item, and
`OkounkovTranMainStatement` the corrected theorem.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalMain

open Set Filter MeasureTheory
open scoped Pointwise Topology ENNReal Nat Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

variable {m : ℕ}

/-- The Euclidean copy of a subset of `ℝⁿ = Fin n → ℝ`, on which the Hausdorff metric of the
book (`appendix_almostsg`, Euclidean norm) is `Metric.hausdorffDist`. -/
def euclideanImage {k : ℕ} (S : Set (Fin k → ℝ)) : Set (EuclideanSpace ℝ (Fin k)) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm '' S

/-- The slice `{y ∈ ℝ^{n-1} : (t, y) ∈ Δ}` of a subset `Δ ⊆ ℝⁿ` at first coordinate `t`. -/
def firstCoordinateSlice (Δ : Set (Fin (m + 1) → ℝ)) (t : ℝ) : Set (Fin m → ℝ) :=
  {y | Fin.cons t y ∈ Δ}

variable (F : OriginalFlagGeometry.{u} (m + 1))

/-- `Δ_{Y•}(α)` for a class `α`, computed with a chosen representative of `α` (source
`def:tradOk`; `RepresentativeIndependence` states that the choice does not matter). -/
def classOkounkovBody (α : RealBottChern (m + 1) F.carrier) : Set (Fin (m + 1) → ℝ) :=
  tradOkounkovBody F (Quotient.out α)

/-- Restriction of a closed real `(1,1)`-form to the first flag member `Y₁`, i.e. its pullback
along the holomorphic inclusion `Y₁ ↪ X`, as a form on the tail flag geometry `F.tail`. -/
def firstFlagRestriction (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    ClosedRealOneOneForm m F.tail.carrier :=
  ClosedRealOneOneForm.pullback
    (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2) θ

/-- `E` is a unit metric of the smooth divisor `Y₁`: its weight is `log |s_{Y₁}|²` plus a
smooth function for a local defining equation `s_{Y₁}` of `Y₁`. Its curvature form
`E.curvature` represents the class `{Y₁}` of the current of integration `[Y₁]`. -/
def IsFirstDivisorUnitMetric (E : MeteredEffectiveQDivisor (m + 1) F.carrier) : Prop :=
  ∃ D : EffectiveDivisor (m + 1) F.carrier,
    D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))) ∧
      E.support = F.flag (1 : Fin (m + 2)) ∧ DivisorMetric.IsDivisorMetric D E

/-- The class `{θ}` is Kähler: it contains a Kähler form. -/
def IsKahlerClass (α : RealBottChern (m + 1) F.carrier) : Prop :=
  ∃ κ : ClosedRealOneOneForm (m + 1) F.carrier,
    κ.val.IsKahler ∧ RealBottChern.ofRepresentative κ = α

/-- Source `def:tradOk`, well-definedness: the body does not depend on the representative of
the class. -/
def RepresentativeIndependence : Prop :=
  ∀ θ : ClosedRealOneOneForm (m + 1) F.carrier,
    tradOkounkovBody F θ = classOkounkovBody F (RealBottChern.ofRepresentative θ)

/-- Source `thm:Okounkovtranmain`, first sentence: `Δ_{Y•}(α)` is a convex body (nonempty,
compact, convex) for every big class `α`. -/
def IsConvexBodyStatement : Prop :=
  ∀ α : RealBottChern (m + 1) F.carrier, SGPT.PSH.BookCurrent.IsBig α →
    Convex ℝ (classOkounkovBody F α) ∧ IsCompact (classOkounkovBody F α) ∧
      (classOkounkovBody F α).Nonempty

/-- Source `thm:Okounkovtranmain` (1): `vol Δ_{Y•}(α) = vol α / n!` for every big class `α`. -/
def VolumeIdentityStatement : Prop :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  ∀ α : RealBottChern (m + 1) F.carrier, SGPT.PSH.BookCurrent.IsBig α →
    volume (classOkounkovBody F α) =
      SGPT.PSH.VariableComplexAtlas.sourceClassVolume α / ((m + 1)! : ℝ≥0∞)

/-- Source `thm:Okounkovtranmain` (2): `Δ_{Y•}(α) + Δ_{Y•}(α') ⊆ Δ_{Y•}(α + α')` for big
classes `α`, `α'` (Minkowski sum). -/
def SuperadditivityStatement : Prop :=
  ∀ α α' : RealBottChern (m + 1) F.carrier, SGPT.PSH.BookCurrent.IsBig α →
    SGPT.PSH.BookCurrent.IsBig α' →
      classOkounkovBody F α + classOkounkovBody F α' ⊆ classOkounkovBody F (α + α')

/-- Source `thm:Okounkovtranmain` (3): for a proper bimeromorphic holomorphic map
`π : W → X` from a compact Kähler manifold carrying the lifting `W•` of `Y•`, and a
representative `θ` of a big class `α`, `Δ_{W•}(π^*α) = Δ_{Y•}(α) g` with
`g = cor(Y•, π)` acting on row vectors. -/
def LiftingInvarianceStatement : Prop :=
  ∀ (W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → F.carrier)
    (hπ : IsFlagLifting F W π) (θ : ClosedRealOneOneForm (m + 1) F.carrier),
    SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) →
      tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) =
        (fun x => Matrix.vecMul x
          (fun i j => (flagLiftingCorrectionMatrix (m + 1) F W π hπ i j : ℝ))) ''
          tradOkounkovBody F θ

/-- Source `thm:Okounkovtranmain` (4): `α ↦ Δ_{Y•}(α)` is continuous on the big cone for the
(Euclidean) Hausdorff metric. -/
def HausdorffContinuityStatement : Prop :=
  letI : TopologicalSpace (RealBottChern (m + 1) F.carrier) :=
    XiaoBottChernC0Closure.classC0Topology F.omega
  ∀ α : RealBottChern (m + 1) F.carrier, SGPT.PSH.BookCurrent.IsBig α →
    Tendsto (fun β => Metric.hausdorffDist (euclideanImage (classOkounkovBody F β))
        (euclideanImage (classOkounkovBody F α)))
      (𝓝[{β | SGPT.PSH.BookCurrent.IsBig β}] α) (𝓝 0)

/-- Source `thm:Okounkovtranmain` (5), **as stated in the book** (false in general, see the
module docstring): for every big class `α = {θ}` there is `t₀ > 0` such that for
`t ∈ (0, t₀)`, `{y : (t, y) ∈ Δ_{Y•}(α)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}((α - t{Y₁})|_{Y₁})`. -/
def SliceFormulaBookStatement : Prop :=
  ∀ θ : ClosedRealOneOneForm (m + 1) F.carrier,
    SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) →
      ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t ∈ Ioo 0 t₀, ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier,
        IsFirstDivisorUnitMetric F E →
          firstCoordinateSlice (tradOkounkovBody F θ) t =
            tradOkounkovBody F.tail (firstFlagRestriction F (θ - t • E.curvature))

/-- Source `thm:Okounkovtranmain` (5), **corrected**: the slice formula for a Kähler class
`α = {θ}` (the case used in `lma:Kahlerclassokounrest`). -/
def KahlerSliceFormulaStatement : Prop :=
  ∀ θ : ClosedRealOneOneForm (m + 1) F.carrier,
    IsKahlerClass F (RealBottChern.ofRepresentative θ) →
      ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t ∈ Ioo 0 t₀, ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier,
        IsFirstDivisorUnitMetric F E →
          firstCoordinateSlice (tradOkounkovBody F θ) t =
            tradOkounkovBody F.tail (firstFlagRestriction F (θ - t • E.curvature))

/-- Source `thm:Okounkovtranmain`, **literally as stated in the book** (together with the
well-definedness of `def:tradOk`). Its item 5 is false (erratum); do not target it. -/
def OkounkovTranMainBookStatement : Prop :=
  RepresentativeIndependence F ∧ IsConvexBodyStatement F ∧ VolumeIdentityStatement F ∧
    SuperadditivityStatement F ∧ LiftingInvarianceStatement F ∧
      HausdorffContinuityStatement F ∧ SliceFormulaBookStatement F

/-- Source `thm:Okounkovtranmain`, **corrected** (item 5 for Kähler classes), together with the
well-definedness of `def:tradOk`: the fixed target of the formalization. -/
def OkounkovTranMainStatement : Prop :=
  RepresentativeIndependence F ∧ IsConvexBodyStatement F ∧ VolumeIdentityStatement F ∧
    SuperadditivityStatement F ∧ LiftingInvarianceStatement F ∧
      HausdorffContinuityStatement F ∧ KahlerSliceFormulaStatement F

end SGPT.Okounkov.TranscendentalMain
