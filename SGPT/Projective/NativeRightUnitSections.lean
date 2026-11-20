import SGPT.Bergman.SourceTensorDictionary

/-! Literal actual native RIGHT tensor unit on all holomorphic sections.
Blueprint: `algebraic-native-ci-cuts.tex`, algebraic-native-ci:right-unit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Bundle Set Filter
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original fiber right unitor, without changing the bundle metric. -/
def rightUnitFiberIsometry (B : HermitianHolomorphicLineBundle.{0,0} n M) (x : M) :
    (tensor B unit).Fiber x ≃ₗᵢ[ℂ] B.Fiber x :=
  TensorProduct.ridIsometry ℂ (B.Fiber x)

/-- In the SAME actual tensor frame, the fiber right unitor preserves the
original frame coefficient on EVERY genuine frame point. -/
theorem rightUnit_coordinate {B : HermitianHolomorphicLineBundle.{0,0} n M}
    (e : AtlasFrame B) {x : M} (hx : x ∈ e.val.baseSet)
    (t : (tensor B unit).Fiber x) :
    ((tensorAtlasFrame e unitAtlasFrame).val ⟨x, t⟩).2 =
      (e.val ⟨x, rightUnitFiberIsometry B x t⟩).2 := by
  let := e.property
  let : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℂ) := ⟨by rfl⟩
  have h : tensorCoordinate B.Fiber (Bundle.Trivial M ℂ)
      e.val (Bundle.Trivial.trivialization M ℂ) x =
      (e.val.linearMapAt ℂ x).comp (TensorProduct.rid ℂ (B.Fiber x)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    change tensorCoordinate B.Fiber (Bundle.Trivial M ℂ)
      e.val (Bundle.Trivial.trivialization M ℂ) x (a ⊗ₜ[ℂ] b) =
      e.val.linearMapAt ℂ x (TensorProduct.rid ℂ (B.Fiber x) (a ⊗ₜ[ℂ] b))
    simp [tensorCoordinate_tmul, TensorProduct.rid_tmul, map_smul, smul_eq_mul, mul_comm]
  change tensorCoordinate B.Fiber (Bundle.Trivial M ℂ)
    e.val (Bundle.Trivial.trivialization M ℂ) x t = _
  rw [h]
  exact congrFun (Trivialization.coe_linearMapAt_of_mem e.val hx) (rightUnitFiberIsometry B x t)

/-- The original actual fiber right unitor sends ALL holomorphic sections to ALL sections. -/
def rightUnitSection (B : HermitianHolomorphicLineBundle.{0,0} n M)
    (s : HolomorphicSections (n := n) (tensor B unit).Fiber) :
    HolomorphicSections (n := n) B.Fiber where
  toFun := fun x => rightUnitFiberIsometry B x (s x)
  contMDiff_toFun := by
    intro x
    let e : AtlasFrame B := ⟨trivializationAt ℂ B.Fiber x, inferInstance⟩
    let := e.property
    let q := tensorAtlasFrame e unitAtlasFrame
    let := q.property
    have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ B.Fiber x
    apply (e.val.contMDiffAt_section_iff hx).mpr
    have hs := (q.val.contMDiffAt_section_iff (show x ∈ q.val.baseSet from ⟨hx, Set.mem_univ x⟩)).mp
      (s.contMDiff x)
    apply hs.congr_of_eventuallyEq
    filter_upwards [e.val.open_baseSet.mem_nhds hx] with y hy
    exact (rightUnit_coordinate e hy (s y)).symm

/-- The inverse is the SAME original section tensor the actual scalar one. -/
def rightUnitSectionInv (B : HermitianHolomorphicLineBundle.{0,0} n M)
    (s : HolomorphicSections (n := n) B.Fiber) :
    HolomorphicSections (n := n) (tensor B unit).Fiber where
  toFun := fun x => (rightUnitFiberIsometry B x).symm (s x)
  contMDiff_toFun := by
    intro x
    let e : AtlasFrame B := ⟨trivializationAt ℂ B.Fiber x, inferInstance⟩
    let := e.property
    let q := tensorAtlasFrame e unitAtlasFrame
    let := q.property
    have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ B.Fiber x
    apply (q.val.contMDiffAt_section_iff (show x ∈ q.val.baseSet from ⟨hx, Set.mem_univ x⟩)).mpr
    have hs := (e.val.contMDiffAt_section_iff hx).mp (s.contMDiff x)
    apply hs.congr_of_eventuallyEq
    filter_upwards [e.val.open_baseSet.mem_nhds hx] with y hy
    rw [rightUnit_coordinate e hy, LinearIsometryEquiv.apply_symm_apply]

/-- The literal right-unit isomorphism on the ENTIRE native H0 space. -/
def rightUnitSectionsEquiv (B : HermitianHolomorphicLineBundle.{0,0} n M) :
    HolomorphicSections (n := n) (tensor B unit).Fiber ≃ₗ[ℂ]
      HolomorphicSections (n := n) B.Fiber where
  toFun := rightUnitSection B
  invFun := rightUnitSectionInv B
  left_inv s := by ext x; exact (rightUnitFiberIsometry B x).symm_apply_apply (s x)
  right_inv s := by ext x; exact (rightUnitFiberIsometry B x).apply_symm_apply (s x)
  map_add' s t := by ext x; exact map_add (rightUnitFiberIsometry B x) (s x) (t x)
  map_smul' a s := by ext x; exact map_smul (rightUnitFiberIsometry B x) a (s x)

/-- Exact unchanged physical coefficient of the SAME inverse right-unit section. -/
theorem rightUnitSectionInv_coordinate (B : HermitianHolomorphicLineBundle.{0,0} n M)
    (s : HolomorphicSections (n := n) B.Fiber) (e : AtlasFrame B)
    {x : M} (hx : x ∈ e.val.baseSet) :
    ((tensorAtlasFrame e unitAtlasFrame).val ⟨x, rightUnitSectionInv B s x⟩).2 =
      (e.val ⟨x, s x⟩).2 := by
  rw [rightUnit_coordinate e hx]
  exact congrArg (fun v => (e.val ⟨x, v⟩).2)
    ((rightUnitFiberIsometry B x).apply_symm_apply (s x))

/-- Pointwise zero is preserved by the ACTUAL same fiber right unitor inverse. -/
theorem rightUnitSectionInv_eq_zero_iff (B : HermitianHolomorphicLineBundle.{0,0} n M)
    (s : HolomorphicSections (n := n) B.Fiber) (x : M) :
    rightUnitSectionInv B s x = 0 ↔ s x = 0 :=
  (rightUnitFiberIsometry B x).symm.map_eq_zero_iff

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
