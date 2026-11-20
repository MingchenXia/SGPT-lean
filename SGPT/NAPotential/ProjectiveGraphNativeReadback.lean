import SGPT.NAPotential.ProjectiveGraphPointEvaluation
import SGPT.NAPotential.ProjectiveGraphLiteralImmersion

/-!
# The actual original graph coefficients read the same native complex point

Blueprint: `projective-graph-native-readback.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphNativeReadback

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Okounkov
open ProjectiveGraphRegularEvaluation ProjectiveGraphPointEvaluation

/-- Canonical original global-section evaluation on an actual affine point is literal Spec preimage. -/
theorem sectionEvaluationHom_affine (B : CommRingCat) (g : Spec B ⟶ Spec (.of ℂ))
    (q : SchemeComplexPoint g) (a : B) :
    sectionEvaluationHom g q ((Scheme.ΓSpecIso B).inv a) = (Spec.preimage q.val).hom a := by
  let c : ComplexAffineChart (Spec B) := ⟨B, 𝟙 _, inferInstance⟩
  let z : ComplexAffineChartPoint g c := ⟨q.val, by simpa only [c, Category.id_comp] using q.property⟩
  have hz : complexAffineChartPointMap g c z = q := by
    apply Subtype.ext
    exact Category.comp_id q.val
  have hc : Set.range c.map ⊆ (⊤ : (Spec B).Opens) := by intro _ _; trivial
  have ha : schemeAffineSectionCoefficient c ⊤ hc ((Scheme.ΓSpecIso B).inv a) = a := by
    simp [schemeAffineSectionCoefficient, Scheme.Hom.appLE, c]
  have hs := schemeAffineOriginalRegularStalk_section g c z ⊤ hc ((Scheme.ΓSpecIso B).inv a)
  rw [ha] at hs
  have he := schemeComplexPointStalkEval_affine g c z a
  rw [hs] at he
  change sectionEvaluationHom g (complexAffineChartPointMap g c z) ((Scheme.ΓSpecIso B).inv a) = _ at he
  rw [hz] at he
  exact he.trans (affineSchemePointEquivOfStructure_apply _ z a)


/-- Original section evaluation after actual pullback is the SAME actual native affine point map. -/
theorem sectionEvaluationHom_affine_pullback {M : Scheme.{0}} (f : M ⟶ Spec (.of ℂ))
    (B : CommRingCat) (g : Spec B ⟶ Spec (.of ℂ)) (h : M ⟶ Spec B) (hh : h ≫ g = f)
    (p : SchemeComplexPoint f) (a : B) :
    sectionEvaluationHom f p (h.appTop ((Scheme.ΓSpecIso B).inv a)) =
      (Spec.preimage (p.val ≫ h)).hom a := by
  rw [sectionEvaluationHom_appTop]
  have he := schemeComplexPointStalkEval_comp f g h hh p
  have ht := DFunLike.congr_fun he
    ((Spec B).presheaf.germ ⊤ (h (schemeComplexPointImage f p)) trivial ((Scheme.ΓSpecIso B).inv a))
  exact ht.symm.trans (sectionEvaluationHom_affine B g (schemeComplexPointMap f g h hh p) a)

open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphProjection ProjectiveGraphAnalyticMap ProjectiveGraphLiteralImmersion
open ProjectiveGraphCentredChart ProjectiveGraphCoordinateCharts ProjectiveGraphSegreEquations
open ProjectiveGraphSegre
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis.FirstPass

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  [hU : Nonempty (coordOpen E j)] {s : ℕ} (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens)

/-- The actual original graph algebra evaluator is exactly the original native Spec point ring map. -/
theorem graphPointEval_eq_native
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    graphPointEval (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p =
      (Spec.preimage (p.val ≫ W.ι)).hom := by
  ext a
  exact sectionEvaluationHom_affine_pullback _ _ (projection (coordOpen E j)
    (isAffineOpen_coordOpen E j) b ≫ f) W.ι (Category.assoc _ _ _).symm p a

/-- Every literal original Segre coordinate is its actual original coefficient times its normalized generator. -/
theorem literalCoordinates_eq (k : Fin (segreDim E.ambientDimension s + 1)) :
    literalCoordinates E j hU b k =
      algebraMap Γ(X, coordOpen E j) (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))
        (ratio E j (segreIdx E.ambientDimension s k).1) *
          (Fin.cons (1 : Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)) (fun (i : Fin s) => (⟨b i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ :
            Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))) : Fin (s + 1) →
            Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)) (segreIdx E.ambientDimension s k).2 := by
  apply Subtype.ext
  change chartGenericCoordinates E j hU (segreIdx E.ambientDimension s k).1 *
    (Fin.cons (1 : X.functionField) b : Fin (s + 1) → X.functionField) (segreIdx E.ambientDimension s k).2 = _
  refine Fin.cases ?_ (fun i => ?_) (segreIdx E.ambientDimension s k).2
  · simp only [Fin.cons_zero]
    rfl
  · simp only [Fin.cons_succ]
    rfl

/-- Actual normalized native point coordinates cannot vanish, because their actual pivot value is one. -/
theorem evaluatedCoordinates_ne_zero
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    (fun k => graphPointEval (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p
      (literalCoordinates E j hU b k)) ≠ 0 := by
  intro h
  have hp := congrFun h (coordSegrePivot E j s)
  rw [literalCoordinates_pivot, map_one, Pi.zero_apply] at hp
  exact one_ne_zero hp

variable {m : ℕ} [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

omit [IsProper f] in
/-- Literal original graph coordinates have exactly the actual normalized original product-graph Segre lift. -/
theorem graphPointEval_literalCoordinates
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    (fun k => graphPointEval (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p
      (literalCoordinates E j hU b k)) =
      segreVec (homCoords f E (m + 1) j
        (schemeComplexPointMap _ f (openProjection (coordOpen E j) (isAffineOpen_coordOpen E j) b W) rfl p))
          (openGraphLift (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p) := by
  funext k
  rw [literalCoordinates_eq, map_mul, graphPointEval_coefficient (coordOpen E j) (isAffineOpen_coordOpen E j) b W (m + 1) E]
  change _ * _ = _ * _
  congr 1
  refine Fin.cases ?_ (fun i => ?_) (segreIdx E.ambientDimension s k).2
  · simp only [Fin.cons_zero, map_one, openGraphLift]
  · simp only [Fin.cons_succ, openGraphLift]
    rfl

/-- **The same original product graph map has exactly the native normalized coordinate projective class**. -/
theorem segreAmbientMap_openGraphMap_eq
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    segreAmbientMap (m := m) E
      (openGraphMap (f := f) (m := m) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p) =
      mk (fun k => graphPointEval (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p
        (literalCoordinates E j hU b k)) (evaluatedCoordinates_ne_zero E j b W p) := by
  let q := schemeComplexPointMap _ f
    (openProjection (coordOpen E j) (isAffineOpen_coordOpen E j) b W) rfl p
  have hq : schemeComplexPointImage f q ∈ coordOpen E j := projection_mem _ _ b _
  change segreMap (projectivePoint f E (m + 1) q)
    (mk (openGraphLift (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p) _) = _
  rw [projectivePoint_eq f E (m + 1) j hq]
  simpa only [graphPointEval_literalCoordinates (m := m) E j b W p] using
    (segreMap_mk (homCoords_ne_zero f E (m + 1) j hq)
      (openGraphLift_ne_zero (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W p))

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphNativeReadback
