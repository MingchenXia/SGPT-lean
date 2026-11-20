import SGPT.Trace.BertiniUniversalSubmersion

/-! Genuine actual universal q products: SAME original X point, original
parameter deletion/reconstruction, native holomorphic diffeomorphism. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily
open scoped ProductComplexManifold

variable {k : ℕ}
def parameterZeroInsert (m : Fin (k + 1)) : ComplexModel k →L[ℂ] ComplexModel (k + 1) :=
  LinearMap.toContinuousLinearMap {
    toFun b := WithLp.toLp 2 (Fin.insertNth m 0 fun j => b j)
    map_add' a b := by
      ext j
      rcases Fin.eq_self_or_eq_succAbove m j with rfl | ⟨l,rfl⟩ <;> simp
    map_smul' a b := by
      ext j
      rcases Fin.eq_self_or_eq_succAbove m j with rfl | ⟨l,rfl⟩ <;> simp }

def parameterDelete (m : Fin (k + 1)) : ComplexModel (k + 1) →L[ℂ] ComplexModel k :=
  LinearMap.toContinuousLinearMap {
    toFun ζ := WithLp.toLp 2 (fun j => ζ (m.succAbove j))
    map_add' _ _ := by ext j; rfl
    map_smul' _ _ := by ext j; rfl }

theorem parameterDelete_zeroInsert (m : Fin (k + 1)) (b : ComplexModel k) :
    parameterDelete m (parameterZeroInsert m b) = b := by
  ext j
  simp [parameterDelete,parameterZeroInsert]

theorem parameterZeroInsert_delete (m : Fin (k + 1)) (ζ : ComplexModel (k + 1)) :
    parameterZeroInsert m (parameterDelete m ζ) = ζ - ζ m • EuclideanSpace.single m 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove m j with rfl | ⟨l,rfl⟩ <;>
    simp [parameterDelete,parameterZeroInsert,Fin.succAbove_ne]

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  (i j : Fin (k + 1 + 1)) (m : Fin (k + 1))

omit [IsComplexManifold n X] in
theorem parameterDelete_corrected (ζ : ComplexModel (k + 1)) (x : X) :
    parameterDelete m (correctedParameter p i j m ζ x) = parameterDelete m ζ := by
  ext l
  simp [parameterDelete,correctedParameter,Fin.succAbove_ne]

omit [IsComplexManifold n X] in
theorem correctedParameter_from_delete (ζ : ComplexModel (k + 1)) (x : X)
    (hm : parameterCoefficient p i j m x ≠ 0) (hzero : localEquation p i j (ζ,x) = 0) :
    correctedParameter p i j m (parameterZeroInsert m (parameterDelete m ζ)) x = ζ := by
  have hG : localEquation p i j (parameterZeroInsert m (parameterDelete m ζ),x) =
      -(parameterCoefficient p i j m x * ζ m) := by
    rw [parameterZeroInsert_delete]
    unfold localEquation
    rw [pairing_affineLift_sub_smul_single]
    change localEquation p i j (ζ,x) - parameterCoefficient p i j m x * ζ m = _
    rw [hzero,zero_sub]
  have hdiv : -(parameterCoefficient p i j m x * ζ m) / parameterCoefficient p i j m x = -ζ m := by
    field_simp
  rw [correctedParameter,hG,hdiv,neg_smul,sub_neg_eq_add,parameterZeroInsert_delete]
  abel

theorem contMDiffAt_parameterCoefficient {x : X} (hx : p x ∈ (affineChart j).source) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (parameterCoefficient p i j m) x :=
  contMDiffAt_of_eventually_mdifferentiableAt
    (holomorphicAt_affineLift_affineChart_comp p p.contMDiff j (i.succAbove m) hx)

def localXOpen : TopologicalSpace.Opens X :=
  ⟨{x | p x ∈ (affineChart j).source ∧ parameterCoefficient p i j m x ≠ 0},by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact (p.contMDiff.continuous.continuousAt.eventually
      ((affineChart j).open_source.mem_nhds hx.1)).and
      ((contMDiffAt_parameterCoefficient p i j m hx.1).continuousAt.eventually_ne hx.2)⟩

def localIncidenceOpen :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    TopologicalSpace.Opens (affineIncidence p i) := by
  let := affineChartedSpace p i
  let := affineComplex p i
  exact ⟨{q | q.val.2 ∈ localXOpen p i j m},
    (localXOpen p i j m).isOpen.preimage (nativeXMap p i).contMDiff.continuous⟩

def localProductForward :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    ContMDiffMap 𝓘(ℂ, ComplexModel (k + 1 + n - 1)) 𝓘(ℂ, ComplexModel (k + n))
      (localIncidenceOpen p i j m) (ComplexModel k × localXOpen p i j m) ∞ := by
  let := affineChartedSpace p i
  let := affineComplex p i
  let f : localIncidenceOpen p i j m → ComplexModel k × localXOpen p i j m :=
    fun q => (parameterDelete m q.val.val.1,⟨q.val.val.2,q.property⟩)
  have ht := (parameterDelete m).contMDiff.comp ((nativeParameterMap p i).contMDiff.comp
    (contMDiff_subtype_val (U := localIncidenceOpen p i j m)))
  have hx0 := (nativeXMap p i).contMDiff.comp (contMDiff_subtype_val (U := localIncidenceOpen p i j m))
  have hx : ContMDiff 𝓘(ℂ, ComplexModel (k + 1 + n - 1)) 𝓘(ℂ, ComplexModel n) ∞
      (fun q : localIncidenceOpen p i j m => (f q).2) :=
    (ContMDiff.subtypeVal_comp_iff (localXOpen p i j m) _).mp hx0
  exact ⟨f,contMDiff_prodMk ht hx⟩

def localProductInverse :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    ContMDiffMap 𝓘(ℂ, ComplexModel (k + n)) 𝓘(ℂ, ComplexModel (k + 1 + n - 1))
      (ComplexModel k × localXOpen p i j m) (localIncidenceOpen p i j m) ∞ := by
  let := affineChartedSpace p i
  let := affineComplex p i
  let f : ComplexModel k × localXOpen p i j m → localIncidenceOpen p i j m := fun q =>
    ⟨⟨(correctedParameter p i j m (parameterZeroInsert m q.1) q.2.val,q.2.val),
      (mem_affineIncidence_iff_localEquation p i j q.2.property.1).mpr
        (correctedParameter_equation_zero p i j m (parameterZeroInsert m q.1) q.2.val q.2.property.2)⟩,q.2.property⟩
  refine ⟨f,?_⟩
  apply (ContMDiff.subtypeVal_comp_iff (localIncidenceOpen p i j m) f).mp
  intro q
  apply contMDiffAt_affineIncidence_of_val p i
  have hx : ContMDiff 𝓘(ℂ, ComplexModel (k + n)) 𝓘(ℂ, ComplexModel n) ∞
      (fun q : ComplexModel k × localXOpen p i j m => q.2.val) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hz : ContMDiff 𝓘(ℂ, ComplexModel (k + n)) 𝓘(ℂ, ComplexModel (k + 1)) ∞
      (fun q : ComplexModel k × localXOpen p i j m => parameterZeroInsert m q.1) :=
    (parameterZeroInsert m).contMDiff.comp contMDiff_fst
  have hpair := contMDiffAt_nativePair (X := X) (z := q) hz.contMDiffAt hx.contMDiffAt
  have hG0 : ContMDiffAt 𝓘(ℂ, ComplexModel (k + 1 + n)) 𝓘(ℂ, ℂ) ∞
      (localEquation p i j) (parameterZeroInsert m q.1,q.2.val) :=
    contMDiffAt_of_eventually_mdifferentiableAt (holomorphicAt_localEquation p i j q.2.property.1)
  have hG := ContMDiffAt.comp (f := fun q : ComplexModel k × localXOpen p i j m =>
    (parameterZeroInsert m q.1,q.2.val)) (g := localEquation p i j) q hG0 hpair
  have hc := ContMDiffAt.comp (f := fun q : ComplexModel k × localXOpen p i j m => q.2.val)
    (g := parameterCoefficient p i j m) q (contMDiffAt_parameterCoefficient p i j m q.2.property.1) hx.contMDiffAt
  have hparam : ContMDiffAt 𝓘(ℂ, ComplexModel (k + n)) 𝓘(ℂ, ComplexModel (k + 1)) ∞
      (fun u : ComplexModel k × localXOpen p i j m =>
        correctedParameter p i j m (parameterZeroInsert m u.1) u.2.val) q :=
    hz.contMDiffAt.sub ((hG.mul (hc.inv₀ q.2.property.2)).smul contMDiffAt_const)
  exact contMDiffAt_nativePair (X := X) hparam hx.contMDiffAt

def localProductDiffeomorph :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    Diffeomorph 𝓘(ℂ, ComplexModel (k + 1 + n - 1)) 𝓘(ℂ, ComplexModel (k + n))
      (localIncidenceOpen p i j m) (ComplexModel k × localXOpen p i j m) ∞ := by
  let := affineChartedSpace p i
  let := affineComplex p i
  exact {
    toEquiv := {
      toFun := localProductForward p i j m
      invFun := localProductInverse p i j m
      left_inv := by
        intro q
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · exact correctedParameter_from_delete p i j m q.val.val.1 q.val.val.2 q.property.2
            ((mem_affineIncidence_iff_localEquation p i j q.property.1).mp q.val.property)
        · rfl
      right_inv := by
        intro q
        apply Prod.ext
        · change parameterDelete m (correctedParameter p i j m (parameterZeroInsert m q.1) q.2.val) = q.1
          rw [parameterDelete_corrected,parameterDelete_zeroInsert]
        · rfl }
    contMDiff_toFun := (localProductForward p i j m).contMDiff
    contMDiff_invFun := (localProductInverse p i j m).contMDiff }

theorem exists_localProduct_at (q : affineIncidence p i) :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    ∃ (j : Fin (k + 1 + 1)) (m : Fin (k + 1)), q.val.2 ∈ localXOpen p i j m ∧
      ∀ u : ComplexModel k × localXOpen p i j m,
        nativeXMap p i ((localProductDiffeomorph p i j m).symm u).val = u.2.val := by
  let := affineChartedSpace p i
  let := affineComplex p i
  let j := chartIndex (p q.val.2)
  have hj : p q.val.2 ∈ (affineChart j).source := mem_affineChart_chartIndex (p q.val.2)
  have hzero := (mem_affineIncidence_iff_localEquation p i j hj).mp q.property
  obtain ⟨m,hm⟩ := exists_succAbove_ne_zero_of_pairing_eq_zero (affineLift_ne_zero j _) hzero
  exact ⟨j,m,⟨hj,hm⟩,fun _ => rfl⟩

end SGPT.Trace.BertiniUniversal
