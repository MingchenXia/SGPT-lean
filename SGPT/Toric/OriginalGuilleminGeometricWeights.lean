import SGPT.Toric.OriginalGuilleminCornerCharts
import SGPT.Toric.OriginalGuilleminStrictLevi
import SGPT.Toric.NativeOriginalEdgeManifold
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import Mathlib.Topology.Continuous

/-!
# The literal Guillemin weights in the actual original native atlas

The fixed corner basis is connected to the existing original vertex charts by
its genuine holomorphic inverse pair. All source assertions refer to the actual
original homogeneous-coordinate nonvanishing opens.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.Convex SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Topology ContDiff Classical
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

private theorem geometricCornerModel_source (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalGuilleminCornerModelChart γ hs v).source =
      (originalPolytopeNativeModelChart γ hs v).source := by
  rw [originalPolytopeNativeModelChart_source]
  simpa only [originalGuilleminCornerModelChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ] using
      (originalGuilleminCornerPiChart_spec γ hs v).2.2.1

private theorem geometricTransition_contDiffOn (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (w v : latticePolytopeVertices γ) :
    ContDiffOn ℂ ∞ (originalGuilleminCornerNativeTransition γ hs w v)
      (originalGuilleminCornerNativeTransition γ hs w v).source :=
  contDiffOn_of_differentiableOn_complex
    (fun z hz => ((analyticOnNhd_originalGuilleminCornerNativeTransition γ hs w v) z hz).differentiableAt.differentiableWithinAt)
    (originalGuilleminCornerNativeTransition γ hs w v).open_source

private theorem geometricTransition_contDiff (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiff ℂ ∞ (originalGuilleminCornerNativeTransition γ hs v v) := by
  have h := geometricTransition_contDiffOn γ hs v v
  rw [(originalGuilleminCornerNativeTransition_sameVertex_source_target γ hs v).1] at h
  exact contDiffOn_univ.mp h

/-- The literal corner weight expressed in the EXISTING original native chart. -/
def originalGuilleminGeometricNativeWeight (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) : ℝ :=
  originalGuilleminNativeCornerWeight γ hs v
    (originalGuilleminCornerNativeTransition γ hs v v z)

/-- Genuine global smoothness follows from the actual same-vertex chart link. -/
theorem contDiff_originalGuilleminGeometricNativeWeight (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiff ℝ ∞ (originalGuilleminGeometricNativeWeight γ hs v) :=
  (contDiff_originalGuilleminNativeCornerWeight γ hs v).comp
    ((geometricTransition_contDiff γ hs v).restrict_scalars ℝ)

/-- The actual inverse derivative and full normalized pullback preserve strict
positivity, including every coordinate-zero stratum and dimension zero. -/
theorem isStrictlyPositive_smoothDDC_originalGuilleminGeometricNativeWeight
    (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)
    (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    IsStrictlyPositive (smoothDDC (originalGuilleminGeometricNativeWeight γ hs v) z) := by
  let T := originalGuilleminCornerNativeTransition γ hs v v
  have hS : T.source = univ :=
    (originalGuilleminCornerNativeTransition_sameVertex_source_target γ hs v).1
  have hV : T.target = univ :=
    (originalGuilleminCornerNativeTransition_sameVertex_source_target γ hs v).2
  have hF : ContDiff ℂ ∞ T := geometricTransition_contDiff γ hs v
  have hG : ContDiff ℂ ∞ T.symm := by
    have h := contDiffOn_of_differentiableOn_complex
      (fun u hu => ((analyticOnNhd_originalGuilleminCornerNativeTransition_symm γ hs v v)
        u hu).differentiableAt.differentiableWithinAt) T.symm.open_source
    change ContDiffOn ℂ ∞ T.symm T.target at h
    rw [hV] at h
    exact contDiffOn_univ.mp h
  have hFd := hF.differentiable (by simp)
  have hGd := hG.differentiable (by simp)
  have hinj : Function.Injective (fderiv ℝ T z) := by
    have heq : T.symm ∘ T = id := funext fun u => T.left_inv (by rw [hS]; exact mem_univ u)
    have hc := fderiv_comp z ((hGd (T z)).restrictScalars ℝ) ((hFd z).restrictScalars ℝ)
    rw [heq, fderiv_id] at hc
    intro u u' huu'
    have hu := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L u) hc
    have hu' := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L u') hc
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at hu hu'
    rw [huu'] at hu
    exact hu.trans hu'.symm
  have hpull := HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ hF.contDiffOn
    (contDiff_originalGuilleminNativeCornerWeight γ hs v).contDiffOn (mapsTo_univ _ _)
    (mem_univ z)
  change IsStrictlyPositive (smoothDDC (fun u =>
    originalGuilleminNativeCornerWeight γ hs v (T u)) z)
  rw [hpull]
  intro η hη
  have hη' : fderiv ℝ T z η ≠ 0 := by
    intro h0
    apply hη
    exact hinj (by simpa using h0)
  have hI : fderiv ℝ T z (Complex.I • η) = Complex.I • fderiv ℝ T z η := by
    rw [(hFd z).fderiv_restrictScalars ℝ]
    exact (fderiv ℂ T z).map_smul Complex.I η
  have hvec : (fun i => fderiv ℝ T z (![η, Complex.I • η] i)) =
      ![fderiv ℝ T z η, Complex.I • fderiv ℝ T z η] := by
    funext i
    fin_cases i <;> simp [hI]
  change 0 < (smoothDDC (originalGuilleminNativeCornerWeight γ hs v) (T z))
    (fun i => fderiv ℝ T z (![η, Complex.I • η] i))
  rw [hvec]
  exact isStrictlyPositive_smoothDDC_originalGuilleminNativeCornerWeight γ hs v (T z) _ hη'

/-- The literal original point potential on its actual vertex open. -/
def originalGuilleminVertexPotential (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (p : originalPolytopeNativeSpace γ) : ℝ :=
  originalGuilleminNativeCornerWeight γ hs v (originalGuilleminCornerModelChart γ hs v p)

/-- Smoothness in EVERY chart of the existing native atlas on the true domain. -/
theorem originalGuilleminVertexPotential_chart_smooth (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    ∀ e : ComplexChart n (originalPolytopeNativeSpace γ),
      ContDiffOn ℝ ∞ (fun z => originalGuilleminVertexPotential γ hs v (e.val.symm z))
        (e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs v).source) := by
  let := originalPolytopeNativeChartedSpace γ hs
  intro e
  obtain ⟨w, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
  have h := (contDiff_originalGuilleminNativeCornerWeight γ hs v).contDiffOn.comp
    ((geometricTransition_contDiffOn γ hs w v).restrict_scalars ℝ)
    (mapsTo_univ _ _)
  simpa only [originalGuilleminVertexPotential, originalGuilleminCornerNativeTransition,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_apply,
    Function.comp_def, OpenPartialHomeomorph.symm_source,
    geometricCornerModel_source, originalPolytopeNativeComplexChart] using h

/-- The literal finite original Legendre reference is read at the literal orbit. -/
theorem originalGuilleminVertexPotential_orbit_eq_reference (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    originalGuilleminVertexPotential γ hs v (originalPolytopeNativeOrbitMap γ a) =
      (originalCanonicalReference γ hs (torusLogCoordinates (latticeTorusPoint a))).toReal -
        originalCoordinatePairing n (integerCast v.val)
          (torusLogCoordinates (latticeTorusPoint a)) := by
  change originalGuilleminComplexCornerWeight γ hs v
    (originalPolytopeNativeModelEquiv n ((originalPolytopeNativeModelEquiv n).symm
      (originalGuilleminCornerPiChart γ hs v (originalPolytopeNativeOrbitMap γ a)))) = _
  rw [(originalPolytopeNativeModelEquiv n).apply_symm_apply]
  have heq : (fun j => Complex.normSq
      (originalGuilleminCornerPiChart γ hs v (originalPolytopeNativeOrbitMap γ a) j)) =
      (fun j => Real.exp (originalCoordinatePairing n
        (integerCast (originalVertexHalfspaceBasis γ hs v j))
          (torusLogCoordinates (latticeTorusPoint a)))) := by
    funext j
    rw [originalGuilleminCornerPiChart_orbit]
    have hlog := latticeCharacter_log_norm_sq (originalVertexHalfspaceBasis γ hs v j) a
    rw [Complex.sq_norm] at hlog
    change Real.log (Complex.normSq (latticeCharacter
      (originalVertexHalfspaceBasis γ hs v j) a : ℂ)) =
        originalCoordinatePairing n (integerCast (originalVertexHalfspaceBasis γ hs v j))
          (torusLogCoordinates (latticeTorusPoint a)) at hlog
    rw [← hlog, Real.exp_log (Complex.normSq_pos.mpr (Units.ne_zero _))]
  change originalGuilleminCornerWeight γ hs v _ = _
  exact (congrArg (originalGuilleminCornerWeight γ hs v) (Subtype.ext heq)).trans
    (originalGuilleminCornerWeight_exp_eq_reference γ hs v _)

/-- The actual normalized original homogeneous coordinate at the other vertex. -/
def originalGuilleminOverlapUnit (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (p : originalPolytopeNativeSpace γ) : ℂ :=
  monomialVertexVector (originalVertexHalfspaceBasis γ hs v) (originalPolytopeFullExponents γ)
    (originalPolytopeNativeVertexIndex γ v) (originalGuilleminCornerPiChart γ hs v p)
      (originalPolytopeNativeVertexIndex γ w)

private theorem geometricCorner_representative (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (p : originalPolytopeNativeSpace γ)
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    p.val = monomialVertexPoint (originalVertexHalfspaceBasis γ hs v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
        (originalGuilleminCornerPiChart γ hs v p) := by
  have hp' : p ∈ (originalGuilleminCornerPiChart γ hs v).source := by
    rw [(originalGuilleminCornerPiChart_spec γ hs v).2.2.1]
    simpa only [originalPolytopeNativeModelChart_source] using hp
  calc
    p.val = ((originalGuilleminCornerPiChart γ hs v).symm
        (originalGuilleminCornerPiChart γ hs v p)).val :=
      (congrArg Subtype.val ((originalGuilleminCornerPiChart γ hs v).left_inv hp')).symm
    _ = _ := (originalGuilleminCornerPiChart_spec γ hs v).2.2.2.1 _

/-- Nonvanishing follows from actual membership in both original vertex opens. -/
theorem originalGuilleminOverlapUnit_ne_zero (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (p : originalPolytopeNativeSpace γ)
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    originalGuilleminOverlapUnit γ hs v w p ≠ 0 := by
  apply (originalPolytopeNativePiChart_mem_source_iff γ hs w p
    _ (monomialVertexVector_ne_zero _ _ _ _) (geometricCorner_representative γ hs v p hv)).mp
  simpa only [originalPolytopeNativeModelChart_source] using hw

private theorem geometricOverlapUnit_ratio (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (p : originalPolytopeNativeSpace γ)
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (Z : Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) (hZ : Z ≠ 0)
    (hpZ : p.val = Projectivization.mk ℂ Z hZ) :
    originalGuilleminOverlapUnit γ hs v w p =
      Z (originalPolytopeNativeVertexIndex γ w) / Z (originalPolytopeNativeVertexIndex γ v) := by
  let V := monomialVertexVector (originalVertexHalfspaceBasis γ hs v)
    (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
      (originalGuilleminCornerPiChart γ hs v p)
  have hV : V ≠ 0 := monomialVertexVector_ne_zero _ _ _ _
  have hpV : p.val = Projectivization.mk ℂ V hV := geometricCorner_representative γ hs v p hv
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ V Z hV hZ).mp (hpV.symm.trans hpZ)
  have hvi : (a : ℂ) * Z (originalPolytopeNativeVertexIndex γ v) = 1 := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, V,
      monomialVertexVector_vertex] using congrFun ha (originalPolytopeNativeVertexIndex γ v)
  have hwi : (a : ℂ) * Z (originalPolytopeNativeVertexIndex γ w) =
      V (originalPolytopeNativeVertexIndex γ w) := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using
      congrFun ha (originalPolytopeNativeVertexIndex γ w)
  have hden : Z (originalPolytopeNativeVertexIndex γ v) ≠ 0 :=
    (originalPolytopeNativePiChart_mem_source_iff γ hs v p Z hZ hpZ).mp
      (by simpa only [originalPolytopeNativeModelChart_source] using hv)
  change V (originalPolytopeNativeVertexIndex γ w) = _
  apply (eq_div_iff hden).mpr
  rw [← hwi]
  calc
    (a : ℂ) * Z (originalPolytopeNativeVertexIndex γ w) *
        Z (originalPolytopeNativeVertexIndex γ v) =
      Z (originalPolytopeNativeVertexIndex γ w) *
        ((a : ℂ) * Z (originalPolytopeNativeVertexIndex γ v)) := by ring
    _ = _ := by rw [hvi, mul_one]

private theorem geometricPotential_continuousOn (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContinuousOn (originalGuilleminVertexPotential γ hs v)
      (originalPolytopeNativeModelChart γ hs v).source := by
  have h := (contDiff_originalGuilleminNativeCornerWeight γ hs v).continuous.comp_continuousOn (originalGuilleminCornerModelChart γ hs v).continuousOn
  rw [geometricCornerModel_source] at h
  exact h

private theorem geometricOverlapUnit_continuousOn (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) :
    ContinuousOn (originalGuilleminOverlapUnit γ hs v w)
      (originalPolytopeNativeModelChart γ hs v).source := by
  have hP : ContinuousOn (originalGuilleminCornerPiChart γ hs v)
      (originalPolytopeNativeModelChart γ hs v).source := by
    have h := (originalGuilleminCornerPiChart γ hs v).continuousOn
    rw [(originalGuilleminCornerPiChart_spec γ hs v).2.2.1] at h
    simpa only [originalPolytopeNativeModelChart_source] using h
  have hV := (continuous_apply (originalPolytopeNativeVertexIndex γ w)).comp
    (continuous_monomialVertexVector (originalVertexHalfspaceBasis γ hs v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v))
  exact hV.comp_continuousOn hP

private theorem geometricOverlapUnit_orbit (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    originalGuilleminOverlapUnit γ hs v w (originalPolytopeNativeOrbitMap γ a) =
      (latticeCharacter (w.val - v.val) a : ℂ) := by
  have hv : originalPolytopeNativeOrbitMap γ a ∈
      (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs v a
  rw [geometricOverlapUnit_ratio γ hs v w _ hv
    (monomialOrbitVector (originalPolytopeFullExponents γ) a)
    (monomialOrbitVector_ne_zero _ _) rfl]
  change (latticeCharacter (originalPolytopeFullExponents γ
    (originalPolytopeNativeVertexIndex γ w)) a : ℂ) /
      (latticeCharacter (originalPolytopeFullExponents γ
        (originalPolytopeNativeVertexIndex γ v)) a : ℂ) = _
  rw [← Units.val_div_eq_div_val, ← originalLatticeCharacter_sub]
  have hw' : originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ w) = w.val :=
    latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) w
  have hv' : originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) = v.val :=
    latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) v
  rw [hw', hv']

/-- Equality of finite continuous values extends from the DENSE ORIGINAL orbit
onto the entire TRUE overlap, retaining all permitted coordinate divisors. -/
theorem originalGuilleminVertexPotential_transition (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (p : originalPolytopeNativeSpace γ)
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    originalGuilleminVertexPotential γ hs v p - originalGuilleminVertexPotential γ hs w p =
      Real.log (Complex.normSq (originalGuilleminOverlapUnit γ hs v w p)) := by
  let D := (originalPolytopeNativeModelChart γ hs v).source ∩
    (originalPolytopeNativeModelChart γ hs w).source
  have hD : IsOpen D := (originalPolytopeNativeModelChart γ hs v).open_source.inter
    (originalPolytopeNativeModelChart γ hs w).open_source
  have hf : ContinuousOn (fun q => originalGuilleminVertexPotential γ hs v q -
      originalGuilleminVertexPotential γ hs w q) D :=
    ((geometricPotential_continuousOn γ hs v).mono inter_subset_left).sub
      ((geometricPotential_continuousOn γ hs w).mono inter_subset_right)
  have hg : ContinuousOn (fun q => Real.log (Complex.normSq
      (originalGuilleminOverlapUnit γ hs v w q))) D := by
    apply (Complex.continuous_normSq.comp_continuousOn
      ((geometricOverlapUnit_continuousOn γ hs v w).mono inter_subset_left)).log
    intro q hq
    exact (Complex.normSq_pos.mpr (originalGuilleminOverlapUnit_ne_zero γ hs v w q
      hq.1 hq.2)).ne'
  have horbit : ∀ a : Fin n → ℂˣ,
      originalGuilleminVertexPotential γ hs v (originalPolytopeNativeOrbitMap γ a) -
        originalGuilleminVertexPotential γ hs w (originalPolytopeNativeOrbitMap γ a) =
          Real.log (Complex.normSq (originalGuilleminOverlapUnit γ hs v w
            (originalPolytopeNativeOrbitMap γ a))) := by
    intro a
    rw [originalGuilleminVertexPotential_orbit_eq_reference,
      originalGuilleminVertexPotential_orbit_eq_reference, geometricOverlapUnit_orbit,
      ← Complex.sq_norm, latticeCharacter_log_norm_sq]
    simp only [originalCanonicalPairing_apply, integerCast, Pi.sub_apply,
      Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hEq : EqOn (fun q => originalGuilleminVertexPotential γ hs v q -
      originalGuilleminVertexPotential γ hs w q)
      (fun q => Real.log (Complex.normSq (originalGuilleminOverlapUnit γ hs v w q)))
      (originalPolytopeNativeOrbitMap γ '' (originalPolytopeNativeOrbitMap γ ⁻¹' D)) := by
    rintro q ⟨a, _, rfl⟩
    exact horbit a
  have hall := hEq.of_subset_closure hf hg (image_preimage_subset _ _)
    ((denseRange_originalPolytopeNativeOrbitMap γ).subset_closure_image_preimage_of_isOpen hD)
  exact hall ⟨hv, hw⟩

private theorem geometricCornerVector_analyticAt (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (i : Fin (originalPolytopeFullIndexSize γ + 1)) (z : Fin n → ℂ) :
    AnalyticAt ℂ (fun u => monomialVertexVector (originalVertexHalfspaceBasis γ hs v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) u i) z := by
  change AnalyticAt ℂ (fun u : Fin n → ℂ => ∏ j : Fin n,
    u j ^ monomialVertexExponent (originalVertexHalfspaceBasis γ hs v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) i j) z
  exact Finset.analyticAt_fun_prod Finset.univ (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z).pow _)

private theorem geometricOverlapUnit_chart_analyticAt (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w t : latticePolytopeVertices γ)
    (u : ComplexModel n)
    (hu : u ∈ (originalGuilleminCornerNativeTransition γ hs t v).source) :
    AnalyticAt ℂ (fun z => originalGuilleminOverlapUnit γ hs v w
      ((originalPolytopeNativeModelChart γ hs t).symm z)) u := by
  let T := originalGuilleminCornerNativeTransition γ hs t v
  have hT : AnalyticAt ℂ T u :=
    analyticOnNhd_originalGuilleminCornerNativeTransition γ hs t v u hu
  have hinner : AnalyticAt ℂ (fun z => originalPolytopeNativeModelEquiv n (T z)) u :=
    ((originalPolytopeNativeModelEquiv n).toContinuousLinearMap.analyticAt (T u)).comp hT
  have hA := AnalyticAt.comp
    (f := fun z => originalPolytopeNativeModelEquiv n (T z))
    (g := fun x => monomialVertexVector (originalVertexHalfspaceBasis γ hs v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) x
        (originalPolytopeNativeVertexIndex γ w))
    (geometricCornerVector_analyticAt γ hs v (originalPolytopeNativeVertexIndex γ w)
      (originalPolytopeNativeModelEquiv n (T u))) hinner
  change AnalyticAt ℂ (fun z => monomialVertexVector (originalVertexHalfspaceBasis γ hs v)
    (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
      (originalPolytopeNativeModelEquiv n ((originalPolytopeNativeModelEquiv n).symm
        (originalGuilleminCornerPiChart γ hs v
          ((originalPolytopeNativeModelChart γ hs t).symm z))))
      (originalPolytopeNativeVertexIndex γ w)) u at hA
  simpa only [(originalPolytopeNativeModelEquiv n).apply_symm_apply,
    originalGuilleminOverlapUnit] using hA

/-- The actual whole-overlap value cocycle is pluriharmonic in EVERY original
native chart. Only the true original vertex denominators must be nonzero. -/
theorem smoothDDC_originalGuilleminVertexPotential_sub (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    ∀ (e : ComplexChart n (originalPolytopeNativeSpace γ)) (u : ComplexModel n),
      u ∈ e.val.target →
      e.val.symm u ∈ (originalPolytopeNativeModelChart γ hs v).source →
      e.val.symm u ∈ (originalPolytopeNativeModelChart γ hs w).source →
      smoothDDC (fun z => originalGuilleminVertexPotential γ hs v (e.val.symm z) -
        originalGuilleminVertexPotential γ hs w (e.val.symm z)) u = 0 := by
  let := originalPolytopeNativeChartedSpace γ hs
  intro e u hu hv hw
  obtain ⟨t, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
  have huV : u ∈ (originalGuilleminCornerNativeTransition γ hs t v).source := by
    refine ⟨hu, ?_⟩
    rwa [geometricCornerModel_source]
  have huW : u ∈ (originalGuilleminCornerNativeTransition γ hs t w).source := by
    refine ⟨hu, ?_⟩
    rwa [geometricCornerModel_source]
  have hzero := Pending.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
    (f := fun z => originalGuilleminOverlapUnit γ hs v w
      ((originalPolytopeNativeModelChart γ hs t).symm z))
    (by
      filter_upwards [(originalGuilleminCornerNativeTransition γ hs t v).open_source.mem_nhds huV]
        with z hz
      exact (geometricOverlapUnit_chart_analyticAt γ hs v w t z hz).differentiableAt)
    (originalGuilleminOverlapUnit_ne_zero γ hs v w _ hv hw)
  have heq : (fun z => originalGuilleminVertexPotential γ hs v
        ((originalPolytopeNativeModelChart γ hs t).symm z) -
      originalGuilleminVertexPotential γ hs w ((originalPolytopeNativeModelChart γ hs t).symm z))
      =ᶠ[𝓝 u] (fun z => Real.log (Complex.normSq (originalGuilleminOverlapUnit γ hs v w
        ((originalPolytopeNativeModelChart γ hs t).symm z)))) := by
    filter_upwards [(originalGuilleminCornerNativeTransition γ hs t v).open_source.mem_nhds huV,
      (originalGuilleminCornerNativeTransition γ hs t w).open_source.mem_nhds huW] with z hzv hzw
    exact originalGuilleminVertexPotential_transition γ hs v w _
      (by
        have hq := hzv.2
        change (originalPolytopeNativeModelChart γ hs t).symm z ∈
          (originalGuilleminCornerModelChart γ hs v).source at hq
        rwa [geometricCornerModel_source] at hq)
      (by
        have hq := hzw.2
        change (originalPolytopeNativeModelChart γ hs t).symm z ∈
          (originalGuilleminCornerModelChart γ hs w).source at hq
        rwa [geometricCornerModel_source] at hq)
  change smoothDDC (fun z => originalGuilleminVertexPotential γ hs v
      ((originalPolytopeNativeModelChart γ hs t).symm z) -
    originalGuilleminVertexPotential γ hs w ((originalPolytopeNativeModelChart γ hs t).symm z)) u = 0
  rw [smoothDDC_congr heq]
  exact hzero

end SGPT.Toric
