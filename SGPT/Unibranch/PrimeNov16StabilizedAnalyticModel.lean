import SGPT.Unibranch.SourceMorphismExt
import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound

/-! One genuine zero coordinate stabilizes the SAME original reduced analytic model.
Blueprint: prime-nov16-stabilized-analytic-model.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps
namespace SGPT.Unibranch.PrimeNov16StabilizedAnalyticModel
open SourceReducedComplexSpace RegularLocusDense

def head (n : ℕ) : ComplexModel (n+1) →L[ℂ] ComplexModel n := coordinateProjection (n+1) n

def zeroInclusion (n : ℕ) : ComplexModel n →L[ℂ] ComplexModel (n+1) := coordinateInclusion (n+1) n

def last (n : ℕ) : ComplexModel (n+1) →L[ℂ] ℂ := EuclideanSpace.proj (Fin.last n)

def join (n : ℕ) : (ComplexModel n × ℂ) →L[ℂ] ComplexModel (n+1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i : Fin (n+1) => if h : i.val < n then w.1 ⟨i.val,h⟩ else w.2)
      map_add' := by intro w w';ext i;by_cases h : i.val < n <;> simp [h]
      map_smul' := by intro c w;ext i;by_cases h : i.val < n <;> simp [h] }

theorem head_zeroInclusion (n : ℕ) (w : ComplexModel n) : head n (zeroInclusion n w)=w :=
  coordinateProjection_coordinateInclusion (Nat.le_succ n) w

theorem last_zeroInclusion (n : ℕ) (w : ComplexModel n) : last n (zeroInclusion n w)=0 := by
  simp [last,zeroInclusion,coordinateInclusion_apply]

theorem head_join (n : ℕ) (w : ComplexModel n × ℂ) : head n (join n w)=w.1 := by
  ext i
  have hi : i.val < n+1 := Nat.lt_trans i.isLt (Nat.lt_succ_self n)
  simp [head,coordinateProjection_apply,join,hi,i.isLt]

theorem last_join (n : ℕ) (w : ComplexModel n × ℂ) : last n (join n w)=w.2 := by
  simp [last,join]

theorem join_head_last (n : ℕ) (z : ComplexModel (n+1)) : join n (head n z,last n z)=z := by
  ext i
  by_cases hi : i.val < n
  · change (if h : i.val < n then head n z ⟨i.val,h⟩ else last n z)=z i
    rw [dif_pos hi]
    change coordinateProjection (n+1) n z ⟨i.val,hi⟩=z i
    rw [coordinateProjection_apply,dif_pos i.isLt]
  · have hie : i=Fin.last n := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hi)
    subst i
    simp [join,last]

theorem join_zero (n : ℕ) (w : ComplexModel n) : join n (w,0)=zeroInclusion n w := by
  ext i
  simp [join,zeroInclusion,coordinateInclusion_apply]

def split (n : ℕ) : ComplexModel (n+1) ≃L[ℂ] (ComplexModel n × ℂ) :=
  ContinuousLinearEquiv.equivOfInverse ((head n).prod (last n)) (join n)
    (join_head_last n) (fun w => Prod.ext (head_join n w) (last_join n w))

theorem split_fst (n : ℕ) (z : ComplexModel (n+1)) : (split n z).1=head n z := rfl

theorem split_snd (n : ℕ) (z : ComplexModel (n+1)) : (split n z).2=last n z := rfl

theorem split_zeroInclusion (n : ℕ) (w : ComplexModel n) :
    split n (zeroInclusion n w)=(w,0) :=
  Prod.ext (head_zeroInclusion n w) (last_zeroInclusion n w)

def lastVector (n : ℕ) : ComplexModel (n+1) →L[ℂ] ComplexModel 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun _ : Fin 1 => last n z)
      map_add' := by intro z z';ext i;simp
      map_smul' := by intro c z;ext i;simp }

theorem lastVector_zero_iff (n : ℕ) (z : ComplexModel (n+1)) : lastVector n z=0 ↔ last n z=0 := by
  constructor
  · intro h
    exact congrArg (fun w : ComplexModel 1 => w 0) h
  · intro h
    ext i
    exact h

def domain {n : ℕ} (U : Opens (ComplexModel n)) : Opens (ComplexModel (n+1)) :=
  ⟨(head n) ⁻¹' (U : Set (ComplexModel n)),U.isOpen.preimage (head n).continuous⟩

theorem domain_eq_split_preimage {n : ℕ} (U : Opens (ComplexModel n)) :
    (domain U : Set (ComplexModel (n+1)))=
      (split n) ⁻¹' ((U : Set (ComplexModel n)) ×ˢ (Set.univ : Set ℂ)) := by
  ext z
  exact ⟨fun hz => ⟨hz,Set.mem_univ _⟩,fun hz => hz.1⟩

theorem domain_connected {n : ℕ} (U : Opens (ComplexModel n))
    (hU : IsConnected (U : Set (ComplexModel n))) :
    IsConnected (domain U : Set (ComplexModel (n+1))) := by
  rw [domain_eq_split_preimage]
  exact (split n).toHomeomorph.isConnected_preimage.mpr
    (hU.prod (isConnected_univ : IsConnected (Set.univ : Set ℂ)))

def baseProjection {n : ℕ} (U : Opens (ComplexModel n)) : domain U → U :=
  fun z => ⟨head n z.val,z.property⟩

def baseInclusion {n : ℕ} (U : Opens (ComplexModel n)) : U → domain U :=
  fun w => ⟨zeroInclusion n w.val,by
    change head n (zeroInclusion n w.val) ∈ U
    rw [head_zeroInclusion]
    exact w.property⟩

def carrier {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U) : Set (domain U) :=
  {z | baseProjection U z ∈ C ∧ last n z.val=0}

theorem baseProjection_holomorphic {n : ℕ} (U : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ (baseProjection U) :=
  BlowupRestrictOpen.contMDiff_opens_mk ((head n).contMDiff.comp contMDiff_subtype_val) (fun z => z.property)

theorem baseInclusion_holomorphic {n : ℕ} (U : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (baseInclusion U) :=
  BlowupRestrictOpen.contMDiff_opens_mk ((zeroInclusion n).contMDiff.comp contMDiff_subtype_val)
    (fun w => by change head n (zeroInclusion n w.val) ∈ U;rw [head_zeroInclusion];exact w.property)

theorem carrier_analytic {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) : IsComplexAnalyticSubset (n := n+1) (carrier U C) := by
  have ha := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (baseProjection_holomorphic U) hC
  have hb : IsComplexAnalyticSubset (n := n+1)
      ((fun z : domain U => lastVector n z.val) ⁻¹' ({0} : Set (ComplexModel 1))) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      ((lastVector n).contMDiff.comp contMDiff_subtype_val)
      (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))
  have he : carrier U C = (baseProjection U) ⁻¹' C ∩
      (fun z : domain U => lastVector n z.val) ⁻¹' ({0} : Set (ComplexModel 1)) := by
    ext z
    exact and_congr_right (fun _ => (lastVector_zero_iff n z.val).symm)
  rw [he]
  exact ha.inter hb

def projection {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC) ⟶
      sourceReducedComplexSpaceModel U C hC :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (baseProjection_holomorphic U) (fun _ hz => hz.1))
    (actualSubspaceMap_point (baseProjection_holomorphic U) (fun _ hz => hz.1)))

def inclusion {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    sourceReducedComplexSpaceModel U C hC ⟶
      sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC) :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (baseInclusion_holomorphic U) (fun w hw => by
      refine ⟨?_,last_zeroInclusion n w.val⟩
      have he : baseProjection U (baseInclusion U w)=w := Subtype.ext (head_zeroInclusion n w.val)
      exact he.symm ▸ hw))
    (actualSubspaceMap_point (baseInclusion_holomorphic U) _))

def modelIso {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC) ≅
      sourceReducedComplexSpaceModel U C hC where
  hom := projection U C hC
  inv := inclusion U C hC
  hom_inv_id := by
    apply morphism_eq_of_base_eq
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change zeroInclusion n (head n z.val.val)=z.val.val
    have h := join_head_last n z.val.val
    rw [z.property.2,join_zero] at h
    exact h
  inv_hom_id := by
    apply morphism_eq_of_base_eq
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    exact head_zeroInclusion n w.val.val

def rawModelIso {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    (sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC)).obj.left ≅
      (sourceReducedComplexSpaceModel U C hC).obj.left where
  hom := (projection U C hC).hom.left
  inv := (inclusion U C hC).hom.left
  hom_inv_id := congrArg (fun f :
    sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC) ⟶
      sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC) => f.hom.left)
    (modelIso U C hC).hom_inv_id
  inv_hom_id := congrArg (fun f : sourceReducedComplexSpaceModel U C hC ⟶
    sourceReducedComplexSpaceModel U C hC => f.hom.left) (modelIso U C hC).inv_hom_id

instance projection_open {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    LocallyRingedSpace.IsOpenImmersion (projection U C hC).hom.left := by
  let E := rawModelIso U C hC
  let : IsIso (projection U C hC).hom.left := E.isIso_hom
  infer_instance

instance inclusion_open {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    LocallyRingedSpace.IsOpenImmersion (inclusion U C hC).hom.left := by
  let E := rawModelIso U C hC
  let : IsIso (inclusion U C hC).hom.left := E.isIso_inv
  infer_instance

theorem projection_coordinates {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) (z : carrier U C) :
    ((projection U C hC).hom.left.base z).val.val=head n z.val.val := rfl

theorem inclusion_coordinates {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) (w : C) :
    ((inclusion U C hC).hom.left.base w).val.val=zeroInclusion n w.val.val := rfl

theorem split_inclusion_coordinates {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) (w : C) :
    split n ((inclusion U C hC).hom.left.base w).val.val=(w.val.val,0) :=
  split_zeroInclusion n w.val.val

theorem split_carrier_coordinates {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) (z : carrier U C) :
    split n z.val.val=(((projection U C hC).hom.left.base z).val.val,0) :=
  Prod.ext rfl z.property.2

theorem projection_scalar {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    (projection U C hC).hom.left ≫ (sourceReducedComplexSpaceModel U C hC).obj.hom =
      (sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC)).obj.hom :=
  Over.w (projection U C hC).hom

theorem inclusion_scalar {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    (inclusion U C hC).hom.left ≫
      (sourceReducedComplexSpaceModel (domain U) (carrier U C) (carrier_analytic U C hC)).obj.hom =
      (sourceReducedComplexSpaceModel U C hC).obj.hom := Over.w (inclusion U C hC).hom
end SGPT.Unibranch.PrimeNov16StabilizedAnalyticModel
