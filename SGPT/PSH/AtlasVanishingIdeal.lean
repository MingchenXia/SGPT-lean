import SGPT.PSH.AtlasOpenScalarGerms

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The literal ORIGINAL reduced ideal: actual every-chart holomorphic germs
which actually vanish near the point on the SAME original set. -/
def atlasVanishingIdeal (A : VariableComplexAtlas X) (S : Set X) : AtlasGermIdeal A where
  mem x g := A.AtlasHolomorphicAt g x ∧ ∀ᶠ y in 𝓝 x, y ∈ S → g y = 0

/-- BOTH full original-open reduced-ideal membership directions, for EVERY
actual scalar function on the SAME open, including every singular stalk. -/
theorem atlasVanishingIdeal_openRestriction_mem_iff (A : VariableComplexAtlas X)
    (U : Opens X) (S : Set X) (p : U) (g : U → ℂ) :
    (atlasVanishingIdeal (A.openRestriction U) ((Subtype.val : U → X) ⁻¹' S)).mem p g ↔
      (atlasVanishingIdeal A S).mem p.val (extendOpens U g) := by
  change ((A.openRestriction U).AtlasHolomorphicAt g p ∧
    ∀ᶠ q in 𝓝 p, q.val ∈ S → g q = 0) ↔
      (A.AtlasHolomorphicAt (extendOpens U g) p.val ∧
        ∀ᶠ y in 𝓝 p.val, y ∈ S → extendOpens U g y = 0)
  have hv : (∀ᶠ q in 𝓝 p, q.val ∈ S → g q = 0) ↔
      ∀ᶠ y in 𝓝 p.val, y ∈ S → extendOpens U g y = 0 := by
    rw [eventually_nhds_val_iff U]
    simp only [extendOpens_val]
  exact and_congr (atlasHolomorphicAt_openRestriction_iff_extend A U) hv

/-- ANY original scalar retains its ENTIRE reduced-ideal membership under
literal restriction; no regular point or support proxy replaces the stalk. -/
theorem atlasVanishingIdeal_comp_open_val_mem_iff (A : VariableComplexAtlas X)
    (U : Opens X) (S : Set X) (p : U) (f : X → ℂ) :
    (atlasVanishingIdeal (A.openRestriction U) ((Subtype.val : U → X) ⁻¹' S)).mem p
      (f ∘ Subtype.val) ↔ (atlasVanishingIdeal A S).mem p.val f := by
  change ((A.openRestriction U).AtlasHolomorphicAt (f ∘ Subtype.val) p ∧
    ∀ᶠ q in 𝓝 p, q.val ∈ S → f q.val = 0) ↔
      (A.AtlasHolomorphicAt f p.val ∧ ∀ᶠ y in 𝓝 p.val, y ∈ S → f y = 0)
  exact and_congr (atlasHolomorphicAt_comp_open_val_iff A U) (eventually_nhds_val_iff U (x := p) (P := fun y => y ∈ S → f y = 0)).symm

/-- The EXISTING whole native conversion gives EXACTLY the actual native
reduced ideal, at EVERY scalar stalk, for ANY set and ANY dimension. -/
theorem atlasVanishingIdeal_toNative {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (S : Set M) :
    (atlasVanishingIdeal (ofFixedModel n M) S).toNative = vanishingIdeal (n := n) S := by
  apply GermIdeal.ext
  funext x g
  exact propext (and_congr atlasHolomorphicAt_iff_native Iff.rfl)

end SGPT.PSH.VariableComplexAtlas
