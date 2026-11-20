import SGPT.PSH.OriginalThetaModificationDescent

/-! The whole original proper-bimeromorphic pullback is a literal order
isomorphism of original theta-PSH function spaces, not a quotient map. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Source prop:PSHpullbij on the actual original independently-dimensional
atlases, retaining empty/disconnected manifolds and every exceptional fibre. -/
def originalThetaPSHPullbackOrderIso [CompactSpace X]
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f)
    (θ : AtlasClosedRealOneOneForm B) :
    {z : Y → EReal // B.IsThetaPSH θ z} ≃o
      {w : X → EReal // A.IsThetaPSH (θ.holomorphicPullback hf.1) w} := by
  let F : {z : Y → EReal // B.IsThetaPSH θ z} →
      {w : X → EReal // A.IsThetaPSH (θ.holomorphicPullback hf.1) w} :=
    fun z => ⟨z.val ∘ f,z.property.comp_atlasAnalyticModification hf⟩
  have hi : Function.Injective F := by
    intro z w he
    apply Subtype.ext
    funext y
    obtain ⟨x,rfl⟩ := hf.surjective y
    exact congrFun (congrArg Subtype.val he) x
  have hs : Function.Surjective F := by
    intro w
    obtain ⟨z,hz,_⟩ := existsUnique_originalThetaPSH_descent hf θ w.property
    exact ⟨⟨z,hz.1⟩,Subtype.ext hz.2⟩
  refine { Equiv.ofBijective F ⟨hi,hs⟩ with map_rel_iff' := ?_ }
  intro z w
  change (∀ x,z.val (f x)≤w.val (f x)) ↔ ∀ y,z.val y≤w.val y
  constructor
  · intro h y
    obtain ⟨x,rfl⟩ := hf.surjective y
    exact h x
  · intro h x
    exact h (f x)

/-- Literal all-point readback of the source's pullback map, including poles. -/
theorem originalThetaPSHPullbackOrderIso_apply [CompactSpace X]
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f)
    (θ : AtlasClosedRealOneOneForm B) (z : {z : Y → EReal // B.IsThetaPSH θ z}) :
    (originalThetaPSHPullbackOrderIso hf θ z).val=z.val ∘ f := rfl

/-- The genuine inverse is an actual original theta-PSH function and has
exact equality on EVERY original source point, including exceptional fibres. -/
theorem originalThetaPSHPullbackOrderIso_symm_readback [CompactSpace X]
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f)
    (θ : AtlasClosedRealOneOneForm B)
    (w : {w : X → EReal // A.IsThetaPSH (θ.holomorphicPullback hf.1) w}) :
    ((originalThetaPSHPullbackOrderIso hf θ).symm w).val ∘ f=w.val := by
  have h := congrArg Subtype.val ((originalThetaPSHPullbackOrderIso hf θ).apply_symm_apply w)
  exact h

end SGPT.PSH.VariableComplexAtlas
