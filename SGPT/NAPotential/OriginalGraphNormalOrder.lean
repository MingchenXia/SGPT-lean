import SGPT.NAPotential.SmoothDivisorNormalOrder
import SGPT.NAPotential.NativeGraphDivisorOrder

/-!
# Original divisor normal order under the actual native graph maps

Complete blueprint: `original-graph-normal-order.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.OriginalGraphNormalOrder

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich
open SGPT.NAPotential.OpenDivisorOrderTransport SGPT.NAPotential.SmoothDivisorNormalOrder
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open SGPT.Foundations.Schemes SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending DemaillyApproximantDivisorialLelong FixedGermNormalOrder

/-- The target assertion records actual PRODUCED coordinates and all native germ/fraction
orders. It is only an output of the original graph producer, never an assumed certificate. -/
def OriginalNormalOrder {X T : Scheme.{0}} [IsIntegral T] (D : PrimeDivisorOver X)
    (f : T ⟶ Spec (.of ℂ)) (m : ℕ)
    [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f] (z : T)
    (φ : X.residueField (D.π (genericPoint D.Y)) ≃+* T.functionField) : Prop :=
  letI : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
  letI : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
    schemeAnalyticTNChartedSpace f (m + 1)
  letI : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
    schemeAnalyticTN_isComplexManifold f (m + 1)
  ∃ y : SchemeComplexPoint f, z ⤳ schemeComplexPointImage f y ∧
    ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
      (∀ g : T.presheaf.stalk (schemeComplexPointImage f y), g ≠ 0 →
        D.ord (φ.symm (algebraMap _ T.functionField g)) =
          ((normalOrder Ψ (stalkToModel f (m + 1) y g)).toNat : ℤ)) ∧
      ∀ r : X.residueField (D.π (genericPoint D.Y)), r ≠ 0 →
        ∃ a b : T.presheaf.stalk (schemeComplexPointImage f y), a ≠ 0 ∧ b ≠ 0 ∧
          φ r = algebraMap _ T.functionField a / algebraMap _ T.functionField b ∧
          D.ord r = ((normalOrder Ψ (stalkToModel f (m + 1) y a)).toNat : ℤ) -
            ((normalOrder Ψ (stalkToModel f (m + 1) y b)).toNat : ℤ)

set_option maxHeartbeats 1000000 in
/-- The original divisor produces its ACTUAL native graph maps and actual normal-order
coordinates on every genuine smooth centre neighbourhood. All centre, field-order,
flattening and germ/fraction comparisons are constructed internally. -/
theorem exists_originalGraphNormalOrder {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (D : PrimeDivisorOver X) (m : ℕ) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hV : D.π (genericPoint D.Y) ∈ V)
      (_ : D.π D.point ∈ V) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
      let bX := fun k => originalFunctionFieldEquiv D (b k)
      let B := Algebra.adjoin Γ(X, V) (Set.range bX)
      ∃ (i : B →+* D.Y.presheaf.stalk D.point) (z : Spec (.of B))
        (ψ : X.functionField ≃+* (Spec (.of B)).functionField),
        z.asIdeal = (maximalIdeal _).comap i ∧
        (∀ v : B, ψ v = StructureSheaf.toStalk B (genericPoint (Spec (.of B))) v) ∧
        IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
        Order.coheight z = 1 ∧
        ∀ (W : (Spec (.of B)).Opens) (hzW : z ∈ W),
          letI : Nonempty W := ⟨⟨z, hzW⟩⟩
          ∀ (fW : W.toScheme ⟶ Spec (.of ℂ))
            (hsm : SmoothOfRelativeDimension (m + 1) fW) (hsep : IsSeparated fW)
            (hqc : QuasiCompact fW),
            letI := hsm
            letI := hsep
            letI := hqc
            OriginalNormalOrder D fW m (⟨z, hzW⟩ : W.toScheme)
              (((originalFunctionFieldEquiv D).trans ψ).trans (openFunctionFieldEquiv W.ι)) := by
  obtain ⟨V, hVa, hV, hpV, s, b, i, z, ψ, hzi, hψ, hDVR, hz, -, hopen⟩ :=
    NativeGraphDivisorOrder.exists_nativeGraphOrder_on_open D
  refine ⟨V, hVa, hV, hpV, s, b, i, z, ψ, hzi, hψ, hDVR, hz, fun W hzW => ?_⟩
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  intro fW hsm hsep hqc
  let := hsm
  let := hsep
  let := hqc
  let : Smooth fW := SmoothOfRelativeDimension.smooth (m + 1) fW
  let : IsLocallyNoetherian W.toScheme := LocallyOfFiniteType.isLocallyNoetherian fW
  let : TopologicalSpace (SchemeComplexPoint fW) := schemeAnalyticPointTopology fW
  let : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint fW) :=
    schemeAnalyticTNChartedSpace fW (m + 1)
  let : IsComplexManifold (m + 1) (SchemeComplexPoint fW) :=
    schemeAnalyticTN_isComplexManifold fW (m + 1)
  obtain ⟨-, hzWco, hordW⟩ := hopen W hzW
  obtain ⟨y, hzy, Ψ, hreg, hrat⟩ := exists_nativeNormalOrder_withFractions
    (X := W.toScheme) fW m (z := ⟨z, hzW⟩) hzWco
  let φ := ((originalFunctionFieldEquiv D).trans ψ).trans (openFunctionFieldEquiv W.ι)
  refine ⟨y, hzy, Ψ, ?_, ?_⟩
  · intro g hg
    have h := hordW (φ.symm (algebraMap _ W.toScheme.functionField g))
    change D.ord (φ.symm (algebraMap _ W.toScheme.functionField g)) =
      Scheme.ord (φ (φ.symm (algebraMap _ W.toScheme.functionField g)))
        (⟨z, hzW⟩ : W.toScheme) at h
    rw [φ.apply_symm_apply] at h
    exact h.trans (hreg g hg)
  · intro r hr
    obtain ⟨a, b, ha, hb, hfrac, hnorm⟩ := hrat (φ r)
      ((map_ne_zero_iff _ φ.injective).mpr hr)
    exact ⟨a, b, ha, hb, hfrac, (hordW r).trans hnorm⟩

end SGPT.NAPotential.OriginalGraphNormalOrder
