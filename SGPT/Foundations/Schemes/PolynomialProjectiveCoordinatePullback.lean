import SGPT.Foundations.Schemes.PolynomialProjectiveAnticanonical
import SGPT.Foundations.Schemes.SchemeOpenFrameTransport
import SGPT.Foundations.Schemes.ProjectiveChartOverlap

/-! Genuine polynomial projective chart maps on actual regular sections. -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PrimeSpectrum
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine coordinate-open scheme isomorphism to its literal homogeneous ring spectrum. -/
def polynomialProjCoordinateSchemeIso (i : Fin (n + 1)) :
    (polynomialProjCoordinateOpen K n i).toScheme ≅
      Spec (.of (polynomialProjCoordinateRing K n i)) :=
  Proj.basicOpenIsoSpec _ (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) (by decide)

/-- Its actual global regular-function map is the native homogeneous section map. -/
theorem polynomialProjCoordinateSchemeIso_appTop (i : Fin (n + 1)) :
    (polynomialProjCoordinateSchemeIso K n i).hom.appTop =
      (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n i))).hom ≫
        CommRingCat.ofHom (polynomialProjCoordinateSectionMap K n i) ≫
          (polynomialProjCoordinateOpen K n i).topIso.inv :=
  Proj.basicOpenToSpec_app_top _ _

/-- The actual chart pullback of genuine regular sections to the affine spectrum. -/
def polynomialProjCoordinateRegularPullback (i : Fin (n + 1)) :
    Γ(polynomialProj K n, polynomialProjCoordinateOpen K n i) ⟶
      Γ(Spec (.of (polynomialProjCoordinateRing K n i)), ⊤) :=
  (polynomialProjCoordinateOpen K n i).topIso.inv ≫
    (polynomialProjCoordinateSchemeIso K n i).inv.appTop

/-- Actual homogeneous fractions pull back to the literal affine coordinate section map. -/
theorem polynomialProjCoordinateRegularPullback_fac (i : Fin (n + 1)) :
    CommRingCat.ofHom (polynomialProjCoordinateSectionMap K n i) ≫
      polynomialProjCoordinateRegularPullback K n i =
        (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n i))).inv := by
  let e := polynomialProjCoordinateSchemeIso K n i
  have hInv : e.inv.appTop = inv e.hom.appTop := by
    simpa using Scheme.Hom.inv_appTop e.hom
  apply (cancel_epi (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n i))).hom).mp
  change (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n i))).hom ≫
      (CommRingCat.ofHom (polynomialProjCoordinateSectionMap K n i) ≫
        (polynomialProjCoordinateOpen K n i).topIso.inv ≫ e.inv.appTop) = _
  have hApp := congrArg (fun t ↦ t ≫ e.inv.appTop) (polynomialProjCoordinateSchemeIso_appTop K n i)
  calc
    _ = e.hom.appTop ≫ e.inv.appTop := by simpa only [Category.assoc] using hApp.symm
    _ = _ := by rw [hInv]; simp

/-- Literal projective ratio functions pull back to literal affine ratio coordinates. -/
theorem polynomialProjCoordinateRegularPullback_ratio (i k : Fin (n + 1)) :
    polynomialProjCoordinateRegularPullback K n i
        (polynomialProjCoordinateRegularRatio K n i k) =
      affineCoordinateMap (.of (polynomialProjCoordinateRing K n i)) (.op ⊤)
        (polynomialProjCoordinateRatio K n i k) :=
  congr($(polynomialProjCoordinateRegularPullback_fac K n i).hom
    (polynomialProjCoordinateRatio K n i k))

/-- Actual ratio sections pull back along the true affine scheme isomorphism. -/
theorem polynomialProjCoordinateSchemeIso_top_ratio (i k : Fin (n + 1)) :
    (polynomialProjCoordinateSchemeIso K n i).hom.appTop
      ((Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n i))).inv
        (polynomialProjCoordinateRatio K n i k)) =
      (polynomialProjCoordinateOpen K n i).topIso.inv
        (polynomialProjCoordinateRegularRatio K n i k) := by
  have hFac : (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n i))).inv ≫
      (polynomialProjCoordinateSchemeIso K n i).hom.appTop =
        CommRingCat.ofHom (polynomialProjCoordinateSectionMap K n i) ≫
          (polynomialProjCoordinateOpen K n i).topIso.inv := by
    rw [polynomialProjCoordinateSchemeIso_appTop, Iso.inv_hom_id_assoc]
  exact congr($(hFac).hom (polynomialProjCoordinateRatio K n i k))

/-- Every actual open has the literal ratio-coordinate pullback formula. -/
theorem polynomialProjCoordinateSchemeIso_local_ratio (i k : Fin (n + 1))
    (V : (polynomialProjCoordinateOpen K n i).toScheme.Opens) :
    ((polynomialProjCoordinateSchemeIso K n i).hom.appIso V).hom
      (affineCoordinateMap (.of (polynomialProjCoordinateRing K n i))
        (.op ((polynomialProjCoordinateSchemeIso K n i).hom.opensFunctor.obj V))
          (polynomialProjCoordinateRatio K n i k)) =
      (polynomialProjCoordinateOpen K n i).toScheme.presheaf.map V.leTop.op
        ((polynomialProjCoordinateOpen K n i).topIso.inv
          (polynomialProjCoordinateRegularRatio K n i k)) := by
  have h := congr($(affineCoordinateMap_openImmersion_hom
    (polynomialProjCoordinateSchemeIso K n i).hom V).hom
      (polynomialProjCoordinateRatio K n i k))
  exact h.trans (congrArg ((polynomialProjCoordinateOpen K n i).toScheme.presheaf.map V.leTop.op)
    (polynomialProjCoordinateSchemeIso_top_ratio K n i k))
end
end SGPT.Foundations.Schemes
