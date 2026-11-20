import SGPT.Foundations.Schemes.BundleMorphismGluing
import SGPT.Foundations.Schemes.LineBundleSectionRing

/-! # Actual tensor-power regrouping in one genuine line atlas

Every comparison is obtained by descent of literal actual frame maps on
the same original cover. Native transition laws prove compatibility;
the readbacks retain actual regular coefficients on all subordinate opens.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.obj)

/-- The actual sheafified tensor isomorphism preserves literal pure tensors. -/
theorem nativeBundleTensorIso_tensorSection {P P' Q Q' : X.Modules}
    (e : P ≅ P') (f : Q ≅ Q') (U : X.Opens)
    (s : bundleSections P U) (t : bundleSections Q U) :
    (bundleTensorIso e f).hom.val.app (op U) (tensorSection P Q U s t) =
      tensorSection P' Q' U (e.hom.val.app (op U) s) (f.hom.val.app (op U) t) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he := adj.unit.naturality
    (MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
      ((SheafOfModules.forget _).mapIso f)).hom
  have hs := congrArg (fun α ↦ (α.app (op U)).hom (s ⊗ₜ[Γ(X, U)] t)) he
  exact hs.symm

/-- The actual tensor-left-unit morphism evaluates the literal pure tensor
using the actual regular-function scalar action. -/
theorem nativeBundleTensorLeftUnitIso_tensorSection (P : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (s : bundleSections P U) :
    (bundleTensorLeftUnitIso P).hom.val.app (op U)
      (tensorSection (SheafOfModules.unit X.ringCatSheaf) P U r s) = r • s := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he := (adj.homEquiv (bundleTensorPresheaf (SheafOfModules.unit X.ringCatSheaf) P)
    P).apply_symm_apply (MonoidalCategory.leftUnitor P.val).hom
  have hs := congrArg (fun α ↦ (α.app (op U)).hom (r ⊗ₜ[Γ(X, U)] s)) he
  change (bundleTensorLeftUnitIso P).hom.val.app (op U)
    (tensorSection (SheafOfModules.unit X.ringCatSheaf) P U r s) =
    (MonoidalCategory.leftUnitor (ModuleCat.of Γ(X, U) (bundleSections P U))).hom
      (r ⊗ₜ[Γ(X, U)] s) at hs
  exact hs.trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r s)

/-- Its actual inverse is the actual unit-frame tensor section. -/
theorem nativeBundleTensorLeftUnitIso_inv_apply (P : X.Modules) (U : X.Opens)
    (s : bundleSections P U) :
    (bundleTensorLeftUnitIso P).inv.val.app (op U) s =
      tensorSection (SheafOfModules.unit X.ringCatSheaf) P U (1 : Γ(X, U)) s := by
  have hh := congrArg (fun α ↦ α.val.app (op U)
    (tensorSection (SheafOfModules.unit X.ringCatSheaf) P U (1 : Γ(X, U)) s))
      (bundleTensorLeftUnitIso P).hom_inv_id
  change (bundleTensorLeftUnitIso P).inv.val.app (op U)
    ((bundleTensorLeftUnitIso P).hom.val.app (op U)
      (tensorSection (SheafOfModules.unit X.ringCatSheaf) P U (1 : Γ(X, U)) s)) =
    tensorSection (SheafOfModules.unit X.ringCatSheaf) P U (1 : Γ(X, U)) s at hh
  rw [nativeBundleTensorLeftUnitIso_tensorSection, one_smul] at hh
  exact hh

private theorem nativeMatchingFrame_compatible {ι : Type u} (P Q : X.Modules)
    (U : ι → X.Opens) (p : ∀ i, LocalBundleFrame P (U i)) (q : ∀ i, LocalBundleFrame Q (U i))
    (hu : ∀ i j (W : X.Opens) (h : W ⟶ U i) (k : W ⟶ U j),
      localBundleFrameTransition (p i) (p j) h k = localBundleFrameTransition (q i) (q j) h k) :
    ∀ i j, bundleHomRestriction P Q (Opens.infLELeft (U i) (U j)) ((p i ≪≫ (q i).symm).hom) =
      bundleHomRestriction P Q (Opens.infLERight (U i) (U j)) ((p j ≪≫ (q j).symm).hom) := by
  intro i j
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s
  let h : W.unop.left ⟶ U i := W.unop.hom ≫ Opens.infLELeft (U i) (U j)
  let k : W.unop.left ⟶ U j := W.unop.hom ≫ Opens.infLERight (U i) (U j)
  apply ((q j).coefficients k).injective
  change (q j).coefficients k (((q i).coefficients h).symm ((p i).coefficients h s)) =
    (q j).coefficients k (((q j).coefficients k).symm ((p j).coefficients k s))
  rw [localBundleFrameTransition_coefficients (q i) (q j) h k,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← hu]
  exact (localBundleFrameTransition_coefficients (p i) (p j) h k s).symm

/-- Matching literal transitions on one genuine cover descend an actual
isomorphism of the original module sheaves. -/
def nativeMatchingBundleFrameIso {ι : Type u} (P Q : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (p : ∀ i, LocalBundleFrame P (U i)) (q : ∀ i, LocalBundleFrame Q (U i))
    (hu : ∀ i j (W : X.Opens) (h : W ⟶ U i) (k : W ⟶ U j),
      localBundleFrameTransition (p i) (p j) h k = localBundleFrameTransition (q i) (q j) h k) : P ≅ Q :=
  bundleGlueIso P Q U hc (fun i ↦ p i ≪≫ (q i).symm) (nativeMatchingFrame_compatible P Q U p q hu)

/-- The genuine descended matching-frame map preserves its actual coefficients
on every subordinate cover open. -/
theorem nativeMatchingBundleFrameIso_coefficients {ι : Type u} (P Q : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (p : ∀ i, LocalBundleFrame P (U i)) (q : ∀ i, LocalBundleFrame Q (U i))
    (hu : ∀ i j (W : X.Opens) (h : W ⟶ U i) (k : W ⟶ U j),
      localBundleFrameTransition (p i) (p j) h k = localBundleFrameTransition (q i) (q j) h k)
    (i : ι) {W : X.Opens} (h : W ⟶ U i) (s : bundleSections P W) :
    (q i).coefficients h ((nativeMatchingBundleFrameIso P Q U hc p q hu).hom.val.app (op W) s) =
      (p i).coefficients h s := by
  have he := bundleGlueIso_restrict P Q U hc (fun i ↦ p i ≪≫ (q i).symm)
    (nativeMatchingFrame_compatible P Q U p q hu) i
  have hs := congrArg (fun e ↦ e.hom.val.app (op (Over.mk h)) s) he
  change (nativeMatchingBundleFrameIso P Q U hc p q hu).hom.val.app (op W) s =
    ((q i).coefficients h).symm ((p i).coefficients h s) at hs
  exact (congrArg ((q i).coefficients h) hs).trans (((q i).coefficients h).apply_symm_apply _)

private theorem nativeMatchingBundleFrameIso_eq {ι : Type u} (P Q : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (p : ∀ i, LocalBundleFrame P (U i)) (q : ∀ i, LocalBundleFrame Q (U i))
    (hu : ∀ i j (W : X.Opens) (h : W ⟶ U i) (k : W ⟶ U j),
      localBundleFrameTransition (p i) (p j) h k = localBundleFrameTransition (q i) (q j) h k)
    (E : P ≅ Q) (hE : ∀ i (W : X.Opens) (h : W ⟶ U i) (s : bundleSections P W),
      (q i).coefficients h (E.hom.val.app (op W) s) = (p i).coefficients h s) :
    nativeMatchingBundleFrameIso P Q U hc p q hu = E := by
  apply Iso.ext
  apply bundleHom_ext P Q U hc
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext s
  apply ((q i).coefficients W.unop.hom).injective
  exact (nativeMatchingBundleFrameIso_coefficients P Q U hc p q hu i W.unop.hom s).trans
    (hE i W.unop.left W.unop.hom s).symm

/-- Genuine actual sheaf isomorphisms transport through recursively formed
native tensor powers using actual unit and tensor maps. -/
def nativeLineTensorPowerIso {P Q : X.Modules} (e : P ≅ Q) :
    ∀ m : ℕ, bundleTensorPower P m ≅ bundleTensorPower Q m
  | 0 => Iso.refl _
  | m + 1 => bundleTensorIso (nativeLineTensorPowerIso e m) e

/-- The actual additive tensor-power comparison in the original native atlas. -/
def nativeLineTensorPowerAddIso {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ) :
    bundleTensorPower L (m + n) ≅ bundleTensor (bundleTensorPower L m) (bundleTensorPower L n) :=
  nativeMatchingBundleFrameIso _ _ a.opens a.covers
    (fun i ↦ (a.frame i).tensorPower (m + n))
    (fun i ↦ ((a.frame i).tensorPower m).tensor ((a.frame i).tensorPower n))
    (by
      intro i j W h k
      rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower, pow_add])

/-- Its literal actual coefficients on every subordinate atlas open. -/
theorem nativeLineTensorPowerAddIso_coefficients {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i) (s : bundleSections (bundleTensorPower L (m + n)) W) :
    (((a.frame i).tensorPower m).tensor ((a.frame i).tensorPower n)).coefficients h
        ((nativeLineTensorPowerAddIso a m n).hom.val.app (op W) s) =
      ((a.frame i).tensorPower (m + n)).coefficients h s :=
  nativeMatchingBundleFrameIso_coefficients (bundleTensorPower L (m + n))
    (bundleTensor (bundleTensorPower L m) (bundleTensorPower L n)) a.opens a.covers
    (fun k ↦ (a.frame k).tensorPower (m + n))
    (fun k ↦ ((a.frame k).tensorPower m).tensor ((a.frame k).tensorPower n))
    (by
      intro k l V p q
      rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower, pow_add]) i h s

/-- The inverse regrouping has the true product coefficient on actual pure tensors. -/
theorem nativeLineTensorPowerAddIso_inv_tensorSection {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i)
    (s : bundleSections (bundleTensorPower L m) W) (t : bundleSections (bundleTensorPower L n) W) :
    ((a.frame i).tensorPower (m + n)).coefficients h
        ((nativeLineTensorPowerAddIso a m n).inv.val.app (op W)
          (tensorSection (bundleTensorPower L m) (bundleTensorPower L n) W s t)) =
      ((a.frame i).tensorPower m).coefficients h s * ((a.frame i).tensorPower n).coefficients h t := by
  have he := nativeLineTensorPowerAddIso_coefficients a m n i h
    ((nativeLineTensorPowerAddIso a m n).inv.val.app (op W)
      (tensorSection (bundleTensorPower L m) (bundleTensorPower L n) W s t))
  have hh := congrArg (fun α ↦ α.val.app (op W)
    (tensorSection (bundleTensorPower L m) (bundleTensorPower L n) W s t))
      (nativeLineTensorPowerAddIso a m n).inv_hom_id
  change (nativeLineTensorPowerAddIso a m n).hom.val.app (op W)
    ((nativeLineTensorPowerAddIso a m n).inv.val.app (op W)
      (tensorSection (bundleTensorPower L m) (bundleTensorPower L n) W s t)) =
    tensorSection (bundleTensorPower L m) (bundleTensorPower L n) W s t at hh
  exact he.symm.trans ((congrArg
    ((((a.frame i).tensorPower m).tensor ((a.frame i).tensorPower n)).coefficients h) hh).trans
      (LocalBundleFrame.tensor_coefficients _ _ h s t))

private theorem nativeLineTensorPowerUnitMatching_eq {L : X.Modules}
    (a : LineBundleAtlas L) (n k : ℕ) (hk : k = n)
    (hu : ∀ i j (W : X.Opens) (h : W ⟶ a.opens i) (q : W ⟶ a.opens j),
      localBundleFrameTransition ((a.frame i).tensorPower k) ((a.frame j).tensorPower k) h q =
      localBundleFrameTransition (((a.frame i).tensorPower 0).tensor ((a.frame i).tensorPower n))
        (((a.frame j).tensorPower 0).tensor ((a.frame j).tensorPower n)) h q) :
    HEq (nativeMatchingBundleFrameIso (bundleTensorPower L k)
      (bundleTensor (bundleTensorPower L 0) (bundleTensorPower L n)) a.opens a.covers
      (fun i ↦ (a.frame i).tensorPower k)
      (fun i ↦ ((a.frame i).tensorPower 0).tensor ((a.frame i).tensorPower n)) hu)
      (bundleTensorLeftUnitIso (bundleTensorPower L n)).symm := by
  cases hk
  apply heq_of_eq
  apply nativeMatchingBundleFrameIso_eq
  intro i W h s
  exact (congrArg
    ((((a.frame i).tensorPower 0).tensor ((a.frame i).tensorPower n)).coefficients h)
      (nativeBundleTensorLeftUnitIso_inv_apply (bundleTensorPower L n) W s)).trans
    ((LocalBundleFrame.tensor_coefficients ((a.frame i).tensorPower 0)
      ((a.frame i).tensorPower n) h (1 : Γ(X, W)) s).trans (one_mul _))

/-- The zero-left comparison is precisely the actual unit inverse,
including the genuine equality of the tensor-power exponents. -/
theorem nativeLineTensorPowerAddIso_zero_left {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ) :
    HEq (nativeLineTensorPowerAddIso a 0 n)
      (bundleTensorLeftUnitIso (bundleTensorPower L n)).symm :=
  nativeLineTensorPowerUnitMatching_eq a n (0 + n) (Nat.zero_add n)
    (by
      intro i j W h k
      rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower, pow_add])

/-- Iterated actual power sheaves compare using the same actual atlas. -/
def nativeLineTensorPowerMulIso {L : X.Modules} (a : LineBundleAtlas L) (r m : ℕ) :
    bundleTensorPower L (r * m) ≅ bundleTensorPower (bundleTensorPower L r) m :=
  nativeMatchingBundleFrameIso _ _ a.opens a.covers
    (fun i ↦ (a.frame i).tensorPower (r * m))
    (fun i ↦ ((a.frame i).tensorPower r).tensorPower m)
    (by
      intro i j W h k
      rw [localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, pow_mul])

/-- The iterated power comparison has its actual original-atlas coefficient readback. -/
theorem nativeLineTensorPowerMulIso_coefficients {L : X.Modules} (a : LineBundleAtlas L) (r m : ℕ)
    (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i) (s : bundleSections (bundleTensorPower L (r * m)) W) :
    (((a.frame i).tensorPower r).tensorPower m).coefficients h
        ((nativeLineTensorPowerMulIso a r m).hom.val.app (op W) s) =
      ((a.frame i).tensorPower (r * m)).coefficients h s :=
  nativeMatchingBundleFrameIso_coefficients (bundleTensorPower L (r * m))
    (bundleTensorPower (bundleTensorPower L r) m) a.opens a.covers
    (fun k ↦ (a.frame k).tensorPower (r * m))
    (fun k ↦ ((a.frame k).tensorPower r).tensorPower m)
    (by
      intro k l V p q
      rw [localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, pow_mul]) i h s

/-- The actual associativity comparison for line powers, descended from
their genuine nested tensor frames on the same atlas. -/
def nativeLineTensorPowerAssociatorIso {L : X.Modules} (a : LineBundleAtlas L) (m n p : ℕ) :
    bundleTensor (bundleTensor (bundleTensorPower L m) (bundleTensorPower L n)) (bundleTensorPower L p) ≅
      bundleTensor (bundleTensorPower L m) (bundleTensor (bundleTensorPower L n) (bundleTensorPower L p)) :=
  nativeMatchingBundleFrameIso _ _ a.opens a.covers
    (fun i ↦ (((a.frame i).tensorPower m).tensor ((a.frame i).tensorPower n)).tensor
      ((a.frame i).tensorPower p))
    (fun i ↦ ((a.frame i).tensorPower m).tensor
      (((a.frame i).tensorPower n).tensor ((a.frame i).tensorPower p)))
    (by
      intro i j W h k
      rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensor,
        localBundleFrameTransition_tensor, localBundleFrameTransition_tensor, mul_assoc])

/-- The true associativity comparison keeps the actual nested-frame coefficients. -/
theorem nativeLineTensorPowerAssociatorIso_coefficients {L : X.Modules} (a : LineBundleAtlas L)
    (m n p : ℕ) (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i)
    (s : bundleSections
      (bundleTensor (bundleTensor (bundleTensorPower L m) (bundleTensorPower L n)) (bundleTensorPower L p)) W) :
    (((a.frame i).tensorPower m).tensor
        (((a.frame i).tensorPower n).tensor ((a.frame i).tensorPower p))).coefficients h
      ((nativeLineTensorPowerAssociatorIso a m n p).hom.val.app (op W) s) =
    ((((a.frame i).tensorPower m).tensor ((a.frame i).tensorPower n)).tensor
      ((a.frame i).tensorPower p)).coefficients h s :=
  nativeMatchingBundleFrameIso_coefficients
    (bundleTensor (bundleTensor (bundleTensorPower L m) (bundleTensorPower L n)) (bundleTensorPower L p))
    (bundleTensor (bundleTensorPower L m) (bundleTensor (bundleTensorPower L n) (bundleTensorPower L p)))
    a.opens a.covers
    (fun k ↦ (((a.frame k).tensorPower m).tensor ((a.frame k).tensorPower n)).tensor
      ((a.frame k).tensorPower p))
    (fun k ↦ ((a.frame k).tensorPower m).tensor
      (((a.frame k).tensorPower n).tensor ((a.frame k).tensorPower p)))
    (by
      intro k l V h q
      rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensor,
        localBundleFrameTransition_tensor, localBundleFrameTransition_tensor, mul_assoc]) i h s

/-- Literal actual triple tensors have the genuine associativity image. -/
theorem nativeLineTensorPowerAssociatorIso_tensorSection {L : X.Modules} (a : LineBundleAtlas L)
    (m n p : ℕ) (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i)
    (s : bundleSections (bundleTensorPower L m) W)
    (t : bundleSections (bundleTensorPower L n) W)
    (v : bundleSections (bundleTensorPower L p) W) :
    (nativeLineTensorPowerAssociatorIso a m n p).hom.val.app (op W)
      (tensorSection (bundleTensor (bundleTensorPower L m) (bundleTensorPower L n))
        (bundleTensorPower L p) W (tensorSection (bundleTensorPower L m) (bundleTensorPower L n) W s t) v) =
      tensorSection (bundleTensorPower L m) (bundleTensor (bundleTensorPower L n) (bundleTensorPower L p)) W s
        (tensorSection (bundleTensorPower L n) (bundleTensorPower L p) W t v) := by
  apply ((((a.frame i).tensorPower m).tensor
    (((a.frame i).tensorPower n).tensor ((a.frame i).tensorPower p))).coefficients h).injective
  rw [nativeLineTensorPowerAssociatorIso_coefficients,
    LocalBundleFrame.tensor_coefficients, LocalBundleFrame.tensor_coefficients,
    LocalBundleFrame.tensor_coefficients, LocalBundleFrame.tensor_coefficients, mul_assoc]

/-- The genuine actual polarization-residue power comparison, derived from
literal matching native frame transitions on the original cover. -/
def nativeLineTensorPowerResidueIso {L : X.Modules} (a : LineBundleAtlas L) (r m j : ℕ) :
    bundleTensorPower L (r * m + j) ≅
      bundleTensor (bundleTensorPower (bundleTensorPower L r) m) (bundleTensorPower L j) :=
  nativeMatchingBundleFrameIso _ _ a.opens a.covers
    (fun i ↦ (a.frame i).tensorPower (r * m + j))
    (fun i ↦ (((a.frame i).tensorPower r).tensorPower m).tensor ((a.frame i).tensorPower j))
    (by
      intro i k W h q
      rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, pow_add, pow_mul])

/-- Every actual residue regrouping keeps its precise native frame coefficient. -/
theorem nativeLineTensorPowerResidueIso_coefficients {L : X.Modules} (a : LineBundleAtlas L) (r m j : ℕ)
    (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i) (s : bundleSections (bundleTensorPower L (r * m + j)) W) :
    ((((a.frame i).tensorPower r).tensorPower m).tensor ((a.frame i).tensorPower j)).coefficients h
        ((nativeLineTensorPowerResidueIso a r m j).hom.val.app (op W) s) =
      ((a.frame i).tensorPower (r * m + j)).coefficients h s :=
  nativeMatchingBundleFrameIso_coefficients (bundleTensorPower L (r * m + j))
    (bundleTensor (bundleTensorPower (bundleTensorPower L r) m) (bundleTensorPower L j))
    a.opens a.covers
    (fun k ↦ (a.frame k).tensorPower (r * m + j))
    (fun k ↦ (((a.frame k).tensorPower r).tensorPower m).tensor ((a.frame k).tensorPower j))
    (by
      intro k l V p q
      rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, localBundleFrameTransition_tensorPower,
        localBundleFrameTransition_tensorPower, pow_add, pow_mul]) i h s

/-- The inverse true residue comparison reads back the actual product
of the iterated-power coefficient and the residue coefficient. -/
theorem nativeLineTensorPowerResidueIso_inv_tensorSection {L : X.Modules} (a : LineBundleAtlas L)
    (r m j : ℕ) (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i)
    (s : bundleSections (bundleTensorPower (bundleTensorPower L r) m) W)
    (t : bundleSections (bundleTensorPower L j) W) :
    ((a.frame i).tensorPower (r * m + j)).coefficients h
      ((nativeLineTensorPowerResidueIso a r m j).inv.val.app (op W)
        (tensorSection (bundleTensorPower (bundleTensorPower L r) m) (bundleTensorPower L j) W s t)) =
      (((a.frame i).tensorPower r).tensorPower m).coefficients h s *
        ((a.frame i).tensorPower j).coefficients h t := by
  have he := nativeLineTensorPowerResidueIso_coefficients a r m j i h
    ((nativeLineTensorPowerResidueIso a r m j).inv.val.app (op W)
      (tensorSection (bundleTensorPower (bundleTensorPower L r) m) (bundleTensorPower L j) W s t))
  have hh := congrArg (fun α ↦ α.val.app (op W)
    (tensorSection (bundleTensorPower (bundleTensorPower L r) m) (bundleTensorPower L j) W s t))
      (nativeLineTensorPowerResidueIso a r m j).inv_hom_id
  change (nativeLineTensorPowerResidueIso a r m j).hom.val.app (op W)
    ((nativeLineTensorPowerResidueIso a r m j).inv.val.app (op W)
      (tensorSection (bundleTensorPower (bundleTensorPower L r) m) (bundleTensorPower L j) W s t)) =
    tensorSection (bundleTensorPower (bundleTensorPower L r) m) (bundleTensorPower L j) W s t at hh
  exact he.symm.trans ((congrArg
    (((((a.frame i).tensorPower r).tensorPower m).tensor ((a.frame i).tensorPower j)).coefficients h) hh).trans
      (LocalBundleFrame.tensor_coefficients _ _ h s t))

end

end SGPT.Foundations.Schemes
