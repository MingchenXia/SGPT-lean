import SGPT.Unibranch.ComplexSpaceSmoothPSHMaximum
import SGPT.Unibranch.ResolutionLocal
import SGPT.Unibranch.HironakaG11ModificationCalculus

/-! Genuine finite maximum principle on original arbitrary singular spaces.
The accepted local resolution theorem is used read-only; no Hironaka
geometry is developed. Blueprint: complex-space-maximum-principle.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- The finite maximum locus is open on the ACTUAL singular complex space.
The smooth source and proper/surjective map are internally produced by the
accepted local resolution theorem. -/
theorem isOpen_maximumLocus_of_morphism {X S : SourceReducedComplexSpace}
    (f : S ⟶ X) {φ : X.obj.left → EReal} (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x)
    (C : ℝ) (hbound : ∀ s,φ (f.hom.left.base s) ≤ (C : EReal)) :
    IsOpen {s : S.obj.left | φ (f.hom.left.base s) = (C : EReal)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨V,j,hj,hxj,Y,π,hπ⟩ := SGPT.Unibranch.exists_local_resolution S x
  obtain ⟨v,hv⟩ := hxj
  have hmaxopen := hπ.1.isOpen_maximumLocus (π ≫ j ≫ f) hφ C (fun y => hbound _)
  let B : Set Y.obj.left := {y | φ (f.hom.left.base (j.hom.left.base (π.hom.left.base y))) ≠ (C : EReal)}
  have hBc : IsClosed B := hmaxopen.isClosed_compl
  have hBim : IsClosed (π.hom.left.base '' B) := hπ.2.1.isClosedMap B hBc
  have hvB : v ∉ π.hom.left.base '' B := by
    rintro ⟨q,hq,hqv⟩
    apply hq
    rw [hqv,hv]
    exact hx
  have hU : IsOpen ((π.hom.left.base '' B)ᶜ) := hBim.isOpen_compl
  have hjU : IsOpen (j.hom.left.base '' (π.hom.left.base '' B)ᶜ) :=
    hj.base_open.isOpenMap _ hU
  refine Filter.mem_of_superset (hjU.mem_nhds ⟨v,hvB,hv⟩) ?_
  rintro z ⟨w,hw,rfl⟩
  obtain ⟨q,hqw⟩ := hπ.2.surjective w
  by_contra hne
  apply hw
  refine ⟨q,?_,hqw⟩
  change φ (f.hom.left.base (j.hom.left.base (π.hom.left.base q))) ≠ _
  rwa [hqw]

/-- The original local-PSH finite maximum locus, as the identity-map case. -/
theorem isOpen_maximumLocus {X : SourceReducedComplexSpace}
    {φ : X.obj.left → EReal} (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x)
    (C : ℝ) (hbound : ∀ x,φ x ≤ (C : EReal)) :
    IsOpen {x : X.obj.left | φ x = (C : EReal)} :=
  isOpen_maximumLocus_of_morphism (𝟙 X) hφ C hbound

/-- An original locally ambient PSH function is constant along ANY actual
morphism from a compact connected possibly singular complex space. No
nondegeneracy or PSH certificate on the pulled-back function is assumed. -/
theorem eq_const_of_compact_connected_pullback {X S : SourceReducedComplexSpace}
    [CompactSpace S.obj.left] [ConnectedSpace S.obj.left] (f : S ⟶ X)
    {φ : X.obj.left → EReal} (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x) :
    ∃ a : EReal,a ≠ ⊤ ∧ (fun s => φ (f.hom.left.base s)) = fun _ => a := by
  let ψ : S.obj.left → EReal := fun s => φ (f.hom.left.base s)
  have huscφ : UpperSemicontinuous φ := fun x => (hφ x).upperSemicontinuousAt
  have husc : UpperSemicontinuous ψ := by
    intro s a ha
    exact f.hom.left.base.hom.continuous.continuousAt.tendsto.eventually (huscφ _ a ha)
  obtain ⟨x,-,hmax⟩ := (husc.upperSemicontinuousOn univ).exists_isMaxOn univ_nonempty isCompact_univ
  by_cases hxbot : ψ x = ⊥
  · refine ⟨⊥,bot_ne_top,funext fun y => le_antisymm ?_ bot_le⟩
    exact (hmax (mem_univ y)).trans_eq hxbot
  let C := (ψ x).toReal
  have hx : ψ x = (C : EReal) := (EReal.coe_toReal (hφ _).ne_top hxbot).symm
  have hb : ∀ y,ψ y ≤ (C : EReal) := fun y => (hmax (mem_univ y)).trans_eq hx
  have hopen := isOpen_maximumLocus_of_morphism f hφ C hb
  have hclosed : IsClosed {y : S.obj.left | ψ y = (C : EReal)} := by
    have heq : {y : S.obj.left | ψ y = (C : EReal)} = {y | (C : EReal) ≤ ψ y} := by
      ext y
      exact ⟨fun h => h.ge,fun h => le_antisymm (hb y) h⟩
    rw [heq]
    exact husc.isClosed_preimage (C : EReal)
  have hall := (show IsClopen {y : S.obj.left | ψ y = (C : EReal)} from
    ⟨hclosed,hopen⟩).eq_univ ⟨x,hx⟩
  refine ⟨(C : EReal),EReal.coe_ne_top _,funext fun y => ?_⟩
  have hy : y ∈ {y : S.obj.left | ψ y = (C : EReal)} := by rw [hall];trivial
  exact hy

/-- On a compact connected ACTUAL singular space, a locally ambient PSH
function is constant. The identically-bottom alternative is retained. -/
theorem eq_const_of_compact_connected {X : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] [ConnectedSpace X.obj.left]
    {φ : X.obj.left → EReal} (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x) :
    ∃ a : EReal,a ≠ ⊤ ∧ φ = fun _ => a :=
  eq_const_of_compact_connected_pullback (𝟙 X) hφ

end SGPT.Unibranch.SourceReducedComplexSpace
