import SGPT.Unibranch.UnibAnSpace
import SGPT.Okounkov.SchemeNativeAnalyticSubset
import SGPT.Unibranch.HironakaG10GenGluing
import SGPT.Unibranch.OriginalNativeModification

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Schemes SGPT.Unibranch SGPT.Okounkov
open scoped Manifold ContDiff

namespace SGPT.Unibranch.UnibAn

noncomputable section

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance preferredPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance preferredAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

variable {N : ℕ}
variable (φ : MvPolynomial (Fin N) ℂ →ₐ[ℂ] SchemeCoordinateAffineRing f n p)
variable (hφ : Function.Surjective φ)

private abbrev presentationEquiv :=
  Ideal.quotientKerAlgEquivOfSurjective hφ

/-- An embedded chart with exactly the affine open used by the native
analytic manifold chart. -/
abbrev preferredEmbeddedChart : EmbeddedChart f := by
  let c := (standardSmoothComplexAffineChart f n p).val
  let E := presentationEquiv f n p φ hφ
  let a : c.ring ≅ coordRing (RingHom.ker φ) := E.symm.toRingEquiv.toCommRingCatIso
  refine ⟨N, RingHom.ker φ, Spec.map a.hom ≫ c.map, inferInstance, ?_⟩
  rw [Category.assoc, ← affinePointFieldAlgebra_structure (c.map ≫ f), complexAffineStructureMap,
    ← Spec.map_comp]
  congr 1
  ext b
  exact E.symm.commutes b

private theorem presentationEquiv_mk (P : MvPolynomial (Fin N) ℂ) :
    presentationEquiv f n p φ hφ (Ideal.Quotient.mk (RingHom.ker φ) P) = φ P := by
  apply (presentationEquiv f n p φ hφ).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact (Ideal.quotientKerAlgEquivOfSurjective_symm_apply hφ P).symm

/-- On the native chart source the two realizations give the very same scheme
point and the very same evaluations of all original polynomial coordinates. -/
theorem exists_preferredEmbeddedChart_point (y : SchemeComplexPoint f)
    (hy : y ∈ (schemeAnalyticTNChart f n p).source) :
    ∃ z : polynomialZeroSet (preferredEmbeddedChart f n p φ hφ).ideal,
      chartPoint (preferredEmbeddedChart f n p φ hφ) z = y ∧
      ∀ P : MvPolynomial (Fin N) ℂ,
        polyEval P (z.val.val : ComplexModel N) =
          schemeNativeAffineCoordinateFunction f n p (φ P) (schemeAnalyticTNChart f n p y) := by
  let α := standardSmoothComplexPointOpenChart f n p y
  let E := presentationEquiv f n p φ hφ
  let κ : MvPolynomial (Fin N) ℂ ⧸ RingHom.ker φ →+* ℂ :=
    α.toRingHom.comp E.toRingHom
  have hκ : κ.comp (algebraMap ℂ _) = RingHom.id ℂ := by
    ext b
    change α (E (algebraMap ℂ _ b)) = b
    rw [E.commutes, α.commutes] <;> rfl
  let z := ofEval κ hκ
  have hys : y ∈ (standardSmoothComplexPointOpenChart f n p).source := by
    rw [schemeAnalyticTNChart_source, schemeAnalyticCoordinateChart_source] at hy
    exact hy.1
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    have hyrev : (standardSmoothComplexPointOpenChart f n p).symm α = y :=
      (standardSmoothComplexPointOpenChart f n p).left_inv hys
    have hval := (standardSmoothComplexPointOpenChart_symm_val f n p α).symm.trans
      (congrArg Subtype.val hyrev)
    change (chartPoint (preferredEmbeddedChart f n p φ hφ) z).val = y.val
    rw [chartPoint_val, pointEval_ofEval]
    change Spec.map (CommRingCat.ofHom κ) ≫
        (Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
          (standardSmoothComplexAffineChart f n p).val.map) = y.val
    rw [← Category.assoc, ← Spec.map_comp]
    have hcomp : CommRingCat.ofHom E.symm.toRingHom ≫ CommRingCat.ofHom κ =
        CommRingCat.ofHom α.toRingHom := by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun a => ?_
      change α (E (E.symm a)) = α a
      rw [AlgEquiv.apply_symm_apply]
    rw [hcomp]
    exact hval
  · intro P
    calc
      _ = pointEval z (Ideal.Quotient.mk (RingHom.ker φ) P) := (pointEval_mk z P).symm
      _ = κ (Ideal.Quotient.mk (RingHom.ker φ) P) :=
        congrArg (fun v : MvPolynomial (Fin N) ℂ ⧸ RingHom.ker φ →+* ℂ =>
          v (Ideal.Quotient.mk (RingHom.ker φ) P)) (pointEval_ofEval κ hκ)
      _ = _ := by
        change α (E (Ideal.Quotient.mk (RingHom.ker φ) P)) = _
        rw [show E (Ideal.Quotient.mk (RingHom.ker φ) P) = φ P from
          presentationEquiv_mk f n p φ hφ P]
        exact (schemeNativeAffineCoordinateFunction_source f n p (φ P) y hy).symm

/-- Polynomial lifts of the native free generators recover the exact native
chart coordinates on the native chart source. -/
theorem exists_preferredEmbeddedChart_inverse_polynomials :
    ∃ P : Fin n → MvPolynomial (Fin N) ℂ,
      ∀ (z : polynomialZeroSet (preferredEmbeddedChart f n p φ hφ).ideal),
        chartPoint (preferredEmbeddedChart f n p φ hφ) z ∈
            (schemeAnalyticTNChart f n p).source →
        (schemeCoordinateModelEquiv n).symm
            (fun i => polyEval (P i) (z.val.val : ComplexModel N)) =
          schemeAnalyticTNChart f n p (chartPoint (preferredEmbeddedChart f n p φ hφ) z) := by
  classical
  have hsurj : ∀ i : Fin n, ∃ P, φ P = standardSmoothComplexChartFreeGenerator f n p i :=
    fun i => hφ _
  choose P hP using hsurj
  refine ⟨P, ?_⟩
  intro z hy
  let e := preferredEmbeddedChart f n p φ hφ
  let y := chartPoint e z
  obtain ⟨z', hz', hEval⟩ := exists_preferredEmbeddedChart_point f n p φ hφ y hy
  have hz : z' = z := chartPoint_injective e hz'
  subst z'
  apply (schemeCoordinateModelEquiv n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext i
  have hy' : y ∈ (schemeAnalyticCoordinateChart f n p).source := by
    simpa only [schemeAnalyticTNChart_source] using hy
  have htarget : schemeCoordinateModelEquiv n (schemeAnalyticTNChart f n p y) =
      schemeAnalyticCoordinateChart f n p y :=
    (schemeCoordinateModelEquiv n).apply_symm_apply _
  rw [htarget, schemeAnalyticCoordinateChart_apply f n p y hy']
  exact (hEval (P i)).trans (by
    rw [schemeNativeAffineCoordinateFunction_source f n p _ y hy, hP])

end

open SGPT.Foundations.Analysis.Pending HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces
open SGPT.Unibranch.OriginalNativeModification

noncomputable section

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]

local instance nativeTopo : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nativeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance nativeManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The original smooth whole model maps to the glued analytic scheme using
the same complex points and the actual local holomorphic pullback. -/
theorem exists_smoothModel_to_analytification :
    ∃ F : wholeModel (n := n) (SchemeComplexPoint f) ⟶ analytification f,
      ∀ y : SchemeComplexPoint f,
        pointMap f (F.hom.left.base ⟨y, Set.mem_univ y⟩) = y := by
  classical
  let pointEquiv := Equiv.ofBijective (pointMap f) ⟨pointMap_injective, pointMap_surjective⟩
  let A := wholeModel (n := n) (SchemeComplexPoint f)
  let φ : A.obj.left → (analytification f).obj.left := fun y =>
    pointEquiv.symm (show (Set.univ : Set (SchemeComplexPoint f)) from y).val
  suffices h : ∃ F : A ⟶ analytification f, ∀ y : A.obj.left, F.hom.left.base y = φ y by
    obtain ⟨F, hF⟩ := h
    refine ⟨F, fun y => ?_⟩
    exact (congrArg (pointMap f) (hF ⟨y, Set.mem_univ y⟩)).trans (pointEquiv.apply_symm_apply y)
  refine HironakaG10GenGluing.exists_hom_of_local (A := A) (B := analytification f) φ ?_
  intro x
  let p : SchemeComplexPoint f := x.val
  let c := (standardSmoothComplexAffineChart f n p).val
  let := affinePointFieldAlgebra (c.map ≫ f)
  have hc : Algebra.FiniteType ℂ c.ring := complexAffineChart_finiteType f c
  obtain ⟨N, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hc
  let e := preferredEmbeddedChart f n p q hq
  let U : Opens (SchemeComplexPoint f) :=
    ⟨(schemeAnalyticTNChart f n p).source, (schemeAnalyticTNChart f n p).open_source⟩
  let S : Set U := (Subtype.val : U → SchemeComplexPoint f) ⁻¹'
    (Set.univ : Set (SchemeComplexPoint f))
  let j : actualSubspaceLocallyRingedSpace (n := n) S ⟶ A.obj.left :=
    actualOpenSubspaceMap (n := n) (Set.univ : Set (SchemeComplexPoint f)) U
  let coords (u : U) : Fin N → ℂ := fun a =>
    schemeNativeAffineCoordinateFunction f n p (q (MvPolynomial.X a)) (schemeAnalyticTNChart f n p u)
  let g : U → Amb e := fun u => ofCoords (coords u)
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel e.dim) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff (⊤ : Opens (ComplexModel e.dim)) _).mp
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
      (fun u => (schemeCoordinateModelEquiv N).symm (coords u))
    apply (schemeCoordinateModelEquiv N).symm.contDiff.contMDiff.comp
    apply contMDiff_pi_space.mpr
    intro a u
    have hchart : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (schemeAnalyticTNChart f n p) u.val :=
      (contMDiffOn_chart (x := p) (n := ∞)).contMDiffAt (U.isOpen.mem_nhds u.property)
    have hcoeff := schemeNativeAffineCoordinateFunction_analytic f n p (q (MvPolynomial.X a))
      ((schemeAnalyticTNChart f n p) u) ((schemeAnalyticTNChart f n p).map_source u.property)
    have hval : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (Subtype.val : U → SchemeComplexPoint f) u := contMDiff_subtype_val.contMDiffAt
    exact (hcoeff.contDiffAt.contMDiffAt.comp _ hchart).comp u hval
  have hpt (u : U) : ∃ z : polynomialZeroSet e.ideal, chartPoint e z = u.val ∧ g u = z.val := by
    obtain ⟨z, hz, hEval⟩ := exists_preferredEmbeddedChart_point f n p q hq u.val u.property
    refine ⟨z, hz, eq_of_complexCoordinates_eq ?_⟩
    funext a
    have ha := hEval (MvPolynomial.X a)
    rw [show polyEval (MvPolynomial.X a) (z.val.val : ComplexModel N) =
      complexCoordinates (z.val.val : ComplexModel N) a from MvPolynomial.eval_X a] at ha
    exact (congrFun (complexCoordinates_ofCoords (coords u)) a).trans ha.symm
  have hgS : Set.MapsTo g S (polynomialZeroSet e.ideal) := by
    intro u _
    obtain ⟨z, _, hz⟩ := hpt u
    rw [hz]
    exact z.property
  let G : actualSubspaceLocallyRingedSpace (n := n) S ⟶ chartModel e := actualSubspaceMap (n := n) (m := N) hg hgS
  have hj : LocallyRingedSpace.IsOpenImmersion j :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (Set.univ : Set (SchemeComplexPoint f)) U
  have hpU : p ∈ U := by
    change p ∈ (schemeAnalyticTNChart f n p).source
    rw [schemeAnalyticTNChart_source]
    exact schemeAnalyticCoordinateChart_point_mem_source f n p
  refine ⟨_, j, G ≫ chartEmbedding e, hj, ⟨⟨⟨p, hpU⟩, Set.mem_univ p⟩, rfl⟩, ?_, ?_⟩
  · change (G ≫ chartEmbedding e) ≫ structureMap f =
      j ≫ subspacePointMap (n := n) (Set.univ : Set (SchemeComplexPoint f))
    simp only [Category.assoc, chartEmbedding_structureMap]
    exact (actualSubspaceMap_point (n := n) (m := N) hg hgS).trans
      (actualSubspaceMap_point (n := n) (m := n) (f := (Subtype.val : U → SchemeComplexPoint f))
        contMDiff_subtype_val (fun _ hy => hy)).symm
  · intro u
    apply pointMap_injective
    change pointMap f ((G ≫ chartEmbedding e).base u) = pointMap f (pointEquiv.symm u.val.val)
    obtain ⟨z, hz, hgz⟩ := hpt u.val
    have he : G.base u = z := Subtype.ext hgz
    rw [comp_base_apply, he, pointMap_chartEmbedding]
    exact hz.trans (pointEquiv.apply_symm_apply _).symm

/-- The polynomial free-generator coordinates give the inverse morphism on the
same actual complex points. -/
theorem exists_analytification_to_smoothModel :
    ∃ G : analytification f ⟶ wholeModel (n := n) (SchemeComplexPoint f),
      ∀ x : analytificationLRS f, (G.hom.left.base x).val = pointMap f x := by
  classical
  let A := wholeModel (n := n) (SchemeComplexPoint f)
  let ψ : analytificationLRS f → A.obj.left := fun x => ⟨pointMap f x, Set.mem_univ _⟩
  suffices h : ∃ G : analytification f ⟶ A,
      ∀ x : analytificationLRS f, G.hom.left.base x = ψ x by
    obtain ⟨G, hG⟩ := h
    exact ⟨G, fun x => congrArg Subtype.val (hG x)⟩
  refine HironakaG10GenGluing.exists_hom_of_local (A := analytification f) (B := A) ψ ?_
  intro x
  let p := pointMap f x
  let c := (standardSmoothComplexAffineChart f n p).val
  let := affinePointFieldAlgebra (c.map ≫ f)
  have hc : Algebra.FiniteType ℂ c.ring := complexAffineChart_finiteType f c
  obtain ⟨N, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hc
  let e := preferredEmbeddedChart f n p q hq
  let b := schemeAnalyticTNChart f n p
  have hp : p ∈ b.source := by
    change p ∈ (schemeAnalyticTNChart f n p).source
    rw [schemeAnalyticTNChart_source]
    exact schemeAnalyticCoordinateChart_point_mem_source f n p
  obtain ⟨z, hz, _⟩ := exists_preferredEmbeddedChart_point f n p q hq p hp
  have hzx : (chartEmbedding e).base z = x := by
    apply pointMap_injective
    exact (pointMap_chartEmbedding e z).trans hz
  obtain ⟨P, hP⟩ := exists_preferredEmbeddedChart_inverse_polynomials f n p q hq
  let t : ComplexModel N → ComplexModel n := fun w =>
    (schemeCoordinateModelEquiv n).symm (fun i => polyEval (P i) w)
  have ht : ContDiff ℂ ∞ t :=
    (schemeCoordinateModelEquiv n).symm.contDiff.comp
      (contDiff_pi.mpr fun i => contDiff_polyEval (P i))
  have hSubsetOpen : IsOpen (chartPoint e ⁻¹' b.source) :=
    b.open_source.preimage (chartPoint_isOpenEmbedding e).continuous
  obtain ⟨O, hO, hOpre⟩ := isOpen_induced_iff.mp hSubsetOpen
  let U : Opens (Amb e) :=
    ⟨O ∩ (fun w : Amb e => t (w : ComplexModel N)) ⁻¹' b.target,
      hO.inter (b.open_target.preimage (ht.continuous.comp continuous_subtype_val))⟩
  let S : Set U := (Subtype.val : U → Amb e) ⁻¹' polynomialZeroSet e.ideal
  let j₀ : actualSubspaceLocallyRingedSpace (n := N) S ⟶ chartModel e :=
    actualOpenSubspaceMap (n := N) (polynomialZeroSet e.ideal) U
  let j := j₀ ≫ chartEmbedding e
  have hj : LocallyRingedSpace.IsOpenImmersion j := by unfold j j₀; infer_instance
  have hU (s : S) : chartPoint e (j₀.base s) ∈ b.source := by
    change j₀.base s ∈ chartPoint e ⁻¹' b.source
    rw [← hOpre]
    exact s.val.property.1
  have hzpoint : chartPoint e z = p := hz
  have hzs : chartPoint e z ∈ b.source :=
    Eq.mpr (congrArg (fun y : SchemeComplexPoint f => y ∈ b.source) hzpoint) hp
  have hzU : z.val ∈ U := by
    refine ⟨?_, ?_⟩
    · change z ∈ (Subtype.val : polynomialZeroSet e.ideal → Amb e) ⁻¹' O
      rw [hOpre]
      exact hzs
    · change t (z.val.val : ComplexModel N) ∈ b.target
      rw [show t (z.val.val : ComplexModel N) = b (chartPoint e z) from hP z hzs]
      exact b.map_source hzs
  let g : U → SchemeComplexPoint f := fun u => b.symm (t (u.val : ComplexModel N))
  have hg : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel n) ∞ g := by
    intro u
    have htarget : t (u.val : ComplexModel N) ∈ b.target := u.property.2
    have hb : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b.symm
        (t (u.val : ComplexModel N)) :=
      (contMDiffOn_chart_symm (x := p) (n := ∞)).contMDiffAt (b.open_target.mem_nhds htarget)
    exact hb.comp u (ht.contMDiff.contMDiffAt.comp u
      (contMDiff_subtype_val.comp contMDiff_subtype_val).contMDiffAt)
  let G : actualSubspaceLocallyRingedSpace (n := N) S ⟶ A.obj.left :=
    actualSubspaceMap (n := N) (m := n) hg (fun y _ => Set.mem_univ (g y))
  refine ⟨_, j, G, hj, ⟨⟨⟨z.val, hzU⟩, z.property⟩, hzx⟩, ?_, ?_⟩
  · change G ≫ subspacePointMap (n := n) (Set.univ : Set (SchemeComplexPoint f)) = j ≫ structureMap f
    simp only [j, Category.assoc, chartEmbedding_structureMap]
    exact (actualSubspaceMap_point (n := N) (m := n) hg (fun y _ => Set.mem_univ (g y))).trans
      (actualSubspaceMap_point (n := N) (m := N) (f := (Subtype.val : U → Amb e))
        contMDiff_subtype_val (fun _ hy => hy)).symm
  · intro s
    apply Subtype.ext
    change b.symm (t (s.val.val : ComplexModel N)) =
      pointMap f ((j₀ ≫ chartEmbedding e).base s)
    rw [comp_base_apply, pointMap_chartEmbedding]
    change b.symm (t ((j₀.base s).val : ComplexModel N)) = chartPoint e (j₀.base s)
    rw [show t ((j₀.base s).val : ComplexModel N) = b (chartPoint e (j₀.base s)) from
      hP (j₀.base s) (hU s)]
    exact b.left_inv (hU s)

theorem exists_smoothModel_analytification_iso :
    ∃ E : wholeModel (n := n) (SchemeComplexPoint f) ≅ analytification f,
      ∀ y : SchemeComplexPoint f,
        pointMap f (E.hom.hom.left.base ⟨y, Set.mem_univ y⟩) = y := by
  obtain ⟨F, hF⟩ := exists_smoothModel_to_analytification f n
  obtain ⟨G, hG⟩ := exists_analytification_to_smoothModel f n
  refine ⟨⟨F, G, ?_, ?_⟩, hF⟩
  · apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro y
    apply Subtype.ext
    exact (hG _).trans (hF y.val)
  · apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro x
    apply pointMap_injective
    exact (hF _).trans (hG x)

end

end SGPT.Unibranch.UnibAn
