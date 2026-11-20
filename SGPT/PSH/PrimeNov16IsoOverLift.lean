import SGPT.Unibranch.OriginalNativeModification
import SGPT.Unibranch.HironakaG11ModificationCalculus

/-! Full native good-locus lifting through the actual isomorphism-over witness.
This is local inverse geometry, with no global smooth-functor hypothesis.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16IsoOverLift
open Set CategoryTheory AlgebraicGeometry
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

/-- The actual isomorphism-over dictionary is injective on its actual good inverse image. -/
theorem injOn_preimage {A R : SourceReducedComplexSpace} {ρ : R ⟶ A}
    {T : Set A.obj.left} (hiso : IsIsoOver ρ T) :
    InjOn ρ.hom.left.base (ρ.hom.left.base ⁻¹' T) := by
  obtain ⟨V, j, hj, hjr, hjρ, _⟩ := hiso
  intro z hz w hw hzw
  obtain ⟨v, hv⟩ := hjr.symm ▸ hz
  obtain ⟨u, hu⟩ := hjr.symm ▸ hw
  have hvu : v = u := hjρ.base_open.injective (by
    change ρ.hom.left.base (j.base v) = ρ.hom.left.base (j.base u)
    rw [hv, hu]
    exact hzw)
  exact hv.symm.trans ((congrArg j.base hvu).trans hu)

/-- A genuine native incoming morphism whose image is in the actual good set
has a FULL scalar-compatible lift to the native manifold model of the SAME source. -/
theorem exists_native_lift {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {A R : SourceReducedComplexSpace} (ρ : R ⟶ A) {T : Set A.obj.left}
    (hiso : IsIsoOver ρ T) (E : wholeModel (n := n) M ≅ R)
    (F : wholeModel (n := m) N ⟶ A) (hF : range F.hom.left.base ⊆ T) :
    ∃ G : wholeModel (n := m) N ⟶ wholeModel (n := n) M,
      G ≫ (E.hom ≫ ρ) = F := by
  obtain ⟨V, j, _hj, _hjr, hjρ, hkr⟩ := hiso
  let k := j ≫ ρ.hom.left
  let : LocallyRingedSpace.IsOpenImmersion k := hjρ
  have hr : range F.hom.left.base ⊆ range k.base := hkr.symm ▸ hF
  let l := LocallyRingedSpace.IsOpenImmersion.lift k F.hom.left hr
  have hfac : l ≫ k = F.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac k F.hom.left hr
  let K := l ≫ j ≫ E.inv.hom.left
  have hpoint : K ≫ (wholeModel (n := n) M).obj.hom = (wholeModel (n := m) N).obj.hom := by
    have h := congrArg (fun H => H ≫ A.obj.hom) hfac
    simpa only [K, k, Category.assoc, Over.w E.inv.hom, Over.w ρ.hom, Over.w F.hom] using h
  let G : wholeModel (n := m) N ⟶ wholeModel (n := n) M :=
    ObjectProperty.homMk (Over.homMk K hpoint)
  refine ⟨G, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (l ≫ j ≫ (isoLeft E).inv) ≫ ((isoLeft E).hom ≫ ρ.hom.left) = F.hom.left
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hfac

end SGPT.PSH.PrimeNov16IsoOverLift
