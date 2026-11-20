import SGPT.BDivisor.CofinalLinearFamilies
import SGPT.BDivisor.BD2DangFavreNef

set_option autoImplicit false

open Filter

namespace SGPT.BDivisor

variable {I J A : Type*} [Preorder I]
variable {E : I → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
variable {B : J → Type*} [∀ j, AddCommGroup (B j)] [∀ j, Module ℝ (B j)]

/-- On a compatible family, convergence in every model is equivalent to
convergence on a cofinal set of models, with their intrinsic Euclidean topologies. -/
theorem compatibleLinearFamilies_tendsto_iff_cofinal
    (push : ∀ ⦃i j : I⦄, i ≤ j → E j →ₗ[ℝ] E i)
    (F : J → I) (cofinal : ∀ i : I, ∃ j : J, i ≤ F j)
    (u : A → compatibleLinearFamilies push) (v : compatibleLinearFamilies push)
    (l : Filter A) :
    (∀ i, Tendsto (fun a => (u a).val i) l
      (@nhds _ (euclideanTopology (E i)) (v.val i))) ↔
    (∀ j, Tendsto (fun a => (u a).val (F j)) l
      (@nhds _ (euclideanTopology (E (F j))) (v.val (F j)))) := by
  constructor
  · exact fun h j => h (F j)
  · intro h i
    obtain ⟨j, hij⟩ := cofinal i
    have hu : (fun a => push hij ((u a).val (F j))) = (fun a => (u a).val i) := by
      funext a
      exact (u a).property i (F j) hij
    have hv := v.property i (F j) hij
    simpa only [hu, hv] using tendsto_euclideanTopology_map (push hij) (h j)

/-- The cofinal numerical traces detect exactly convergence of their incarnation-wise
Chern classes. The Chern map can land in an ambient Bott--Chern module. -/
theorem compatibleLinearFamilies_tendsto_iff_cofinal_chern
    (push : ∀ ⦃i j : I⦄, i ≤ j → E j →ₗ[ℝ] E i)
    (F : J → I) (cofinal : ∀ i : I, ∃ j : J, i ≤ F j)
    (chern : ∀ j, E (F j) →ₗ[ℝ] B j) (hchern : ∀ j, Function.Injective (chern j))
    (u : A → compatibleLinearFamilies push) (v : compatibleLinearFamilies push)
    (l : Filter A) :
    (∀ i, Tendsto (fun a => (u a).val i) l
      (@nhds _ (euclideanTopology (E i)) (v.val i))) ↔
    (∀ j, Tendsto (fun a => chern j ((u a).val (F j))) l
      (@nhds _ (euclideanTopology (B j)) (chern j (v.val (F j))))) := by
  rw [compatibleLinearFamilies_tendsto_iff_cofinal push F cofinal u v l]
  exact forall_congr' fun j => DFAlg.tendsto_euclideanTopology_iff_of_injective _ (hchern j)

end SGPT.BDivisor
