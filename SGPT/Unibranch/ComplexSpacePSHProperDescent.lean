import SGPT.Unibranch.ComplexSpaceAnalyticFiber

/-! Actual ordinary PSH proper-connected-fiber descent of the unchanged
function to the unchanged original target. No descended PSH certificate.
Blueprint: complex-space-psh-proper-descent.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Genuine singular compact-fiber constancy internally manufactures the
unique actual USC descent; no constancy or output regularity is assumed. -/
theorem exists_unique_usc_descent_of_connected_proper_fibers
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (hp : IsProperMap f.hom.left.base)
    (hconn : ∀ x : X.obj.left,IsConnected (f.hom.left.base ⁻¹' {x}))
    {φ : Y.obj.left → EReal} (hφ : ∀ y,Y.IsLocallyAmbientPSHAt φ y) :
    ∃! ψ : X.obj.left → EReal, UpperSemicontinuous ψ ∧
      ∀ y : Y.obj.left,ψ (f.hom.left.base y) = φ y := by
  have hf : ∀ x : X.obj.left,∃ y : Y.obj.left,f.hom.left.base y = x := by
    intro x
    obtain ⟨y,hy⟩ := (hconn x).nonempty
    exact ⟨y,hy⟩
  choose s hs using hf
  let ψ : X.obj.left → EReal := fun x => φ (s x)
  have hread (y : Y.obj.left) : ψ (f.hom.left.base y) = φ y :=
    eq_on_connected_proper_fiber f hp (f.hom.left.base y) (hconn _) hφ (hs _) rfl
  have husc : UpperSemicontinuous φ := fun y => (hφ y).upperSemicontinuousAt
  have huscψ : UpperSemicontinuous ψ := by
    apply upperSemicontinuous_iff_isClosed_preimage.mpr
    intro a
    have hlevel : ψ ⁻¹' Ici a = f.hom.left.base '' (φ ⁻¹' Ici a) := by
      ext x
      constructor
      · intro hx
        refine ⟨s x,hx,hs x⟩
      · rintro ⟨y,hy,rfl⟩
        rwa [mem_preimage,hread]
    rw [hlevel]
    exact hp.isClosedMap _ (husc.isClosed_preimage a)
  refine ⟨ψ,⟨huscψ,hread⟩,?_⟩
  intro ψ' hψ'
  funext x
  rw [← hs x,hψ'.2,hread]

end SGPT.Unibranch.SourceReducedComplexSpace
