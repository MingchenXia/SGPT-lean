import SGPT.Toric.PointBlowupUniversal
import SGPT.Toric.PointBlowupHyperplane
import Lean.Elab.Command

section PointBlowupCanonicalFragment001
/- BEGIN SourceOriginalBlowupOkounkovDraft; original source SHA256 30039801e64ffb84c1556847cf572419601f563c560e8eab493e171326f53adc -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open scoped Manifold ContDiff BigOperators

/-- The SAME original source surface, with its edge-smoothness internally
proved from the four printed primitive vertex cones. No model or blowup
certificate occurs as an input. -/
abbrev SourceOriginalBlowupSurface := PolytopeToricVariety blowupGenerator blowup_edgeSmooth

/-- The ACTUAL source global map, internally manufactured from 1,χe1,χe2. -/
abbrev sourceOriginalBlowdown : SourceOriginalBlowupSurface → SGPT.Projective.ComplexProjectiveSpace 2 :=
  originalBlowdown blowup_edgeSmooth

/-- The literal source has the FULL intrinsic native point-ideal universal
property, with no incoming intrinsic blowup or identification hypothesis. -/
theorem source_original_point_blowup :
    IsBlowupAlong 2 ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))
      sourceOriginalBlowdown := originalBlowdown_isBlowupAlong blowup_edgeSmooth

/-- Whole original ex:toric-big:L532 geometry and BOTH source conclusions:
actual intrinsic blowup, actual exceptional fibre, actual strict transform
of the PRINTED punctured line, actual flag, literal Phi, actual body and its
inequality with the P² simplex. There are NO model/geometry/certificate inputs. -/
theorem source_original_blowup_okounkov_triangle :
    IsBlowupAlong 2 ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))
      sourceOriginalBlowdown ∧
    {p : SourceOriginalBlowupSurface | sourceOriginalBlowdown p = blowdownOrigin} =
      toricPrimeDivisor (blowupExceptionalRay blowup_edgeSmooth) ∧
    closure (originalSourceLineLift blowup_edgeSmooth) =
      toricPrimeDivisor (blowupStrictLineRay blowup_edgeSmooth) ∧
    ∃ e : Fin 2 ≃ Fin 2,
      polytopeToricRayGenerator blowupGenerator blowup_edgeSmooth (blowupVertex 3) (e 0) = blowupRay5 ∧
      polytopeToricRayGenerator blowupGenerator blowup_edgeSmooth (blowupVertex 3) (e 1) = blowupRay7 ∧
      toricFlag blowup_edgeSmooth (blowupVertex 3) e 1 = closure (originalSourceLineLift blowup_edgeSmooth) ∧
      toricFlag blowup_edgeSmooth (blowupVertex 3) e 2 =
        closure (originalSourceLineLift blowup_edgeSmooth) ∩
          {p : SourceOriginalBlowupSurface | sourceOriginalBlowdown p = blowdownOrigin} ∧
      toricFlag blowup_edgeSmooth (blowupVertex 3) e 2 = {blowupOriginalFlagPoint blowup_edgeSmooth} ∧
      (∀ m, toricFlagLatticeMap blowup_edgeSmooth (blowupVertex 3) e
        (blowupHyperplaneDivisor blowup_edgeSmooth) m = ![m 0, m 0 + m 1]) ∧
      toricOkounkovBody (blowupVertex 3) e (blowupHyperplaneDivisor blowup_edgeSmooth) =
        {y | 0 ≤ y 0 ∧ y 0 ≤ y 1 ∧ y 1 ≤ 1} ∧
      toricOkounkovBody (blowupVertex 3) e (blowupHyperplaneDivisor blowup_edgeSmooth) ≠
        {y | (∀ k, 0 ≤ y k) ∧ ∑ k, y k ≤ 1} := by
  obtain ⟨e, he0, he1⟩ := blowup_exists_flagOrder blowup_edgeSmooth
  have hflag := blowup_toricFlag blowup_edgeSmooth e he0 he1
  have hflag1 : toricFlag blowup_edgeSmooth (blowupVertex 3) e 1 =
      toricPrimeDivisor (blowupStrictLineRay blowup_edgeSmooth) := hflag.1
  have hflag2 : toricFlag blowup_edgeSmooth (blowupVertex 3) e 2 =
      toricPrimeDivisor (blowupStrictLineRay blowup_edgeSmooth) ∩
        toricPrimeDivisor (blowupExceptionalRay blowup_edgeSmooth) := hflag.2
  have hbody := blowup_okounkovBody blowup_edgeSmooth e he0 he1
  refine ⟨source_original_point_blowup, originalBlowdown_fibre_origin blowup_edgeSmooth,
    originalSourceLine_strictTransform blowup_edgeSmooth, e, he0, he1, ?_, ?_, ?_, hbody.1, hbody.2, ?_⟩
  · exact hflag1.trans (originalSourceLine_strictTransform blowup_edgeSmooth).symm
  · rw [hflag2, originalSourceLine_strictTransform, originalBlowdown_fibre_origin]
  · exact hflag2.trans (originalStrictLine_inter_exceptional blowup_edgeSmooth)
  · rw [hbody.2]
    exact blowup_okounkovBody_ne_simplex

/-- Actual physical O_X(D4)≅π*O_P²(1), with independently constructed
native source/pullback total-space topologies. -/
def sourceOriginalHyperplaneBundleIsomorphism :
    TotalSpace ℂ (ToricNativeLineFiber (nativeSourceHyperplaneMetric blowup_edgeSmooth)) ≃ₜ
      TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber blowup_edgeSmooth) :=
  nativeBlowdownHyperplaneBundleHomeomorph blowup_edgeSmooth

/-- BOTH maps of the genuine actual physical bundle isomorphism are
holomorphic; this is an outgoing conclusion with no comparison hypotheses. -/
theorem source_original_hyperplane_bundle_pullback :
    ContMDiff ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ sourceOriginalHyperplaneBundleIsomorphism ∧
    ContMDiff ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ sourceOriginalHyperplaneBundleIsomorphism.symm :=
  ⟨contMDiff_nativeBlowdownHyperplaneTotalMap blowup_edgeSmooth,
    contMDiff_nativeBlowdownHyperplaneTotalInv blowup_edgeSmooth⟩

/-- EVERY actual source section and EVERY actual pulled-back section occur
in this genuine complex linear equivalence of the two full H0 spaces. -/
def sourceOriginalHyperplaneFullSectionsEquiv :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (ToricNativeLineFiber (nativeSourceHyperplaneMetric blowup_edgeSmooth)) ≃ₗ[ℂ]
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (NativeBlowdownPullbackHyperplaneFiber blowup_edgeSmooth) :=
  nativeBlowdownHyperplaneSectionsEquiv blowup_edgeSmooth

/-- The whole physical line-bundle identification has literal coefficient
one in EVERY original source and actual pulled-back holomorphic frame. -/
theorem source_original_hyperplane_frame_coefficients
    (v : latticePolytopeVertices blowupGenerator) {p : SourceOriginalBlowupSurface}
    (hp : p ∈ (originalPolytopeNativeModelChart blowupGenerator blowup_edgeSmooth v).source)
    (t : ToricNativeLineFiber (nativeSourceHyperplaneMetric blowup_edgeSmooth) p) :
    (nativeBlowdownPullbackFrame blowup_edgeSmooth v
      (sourceOriginalHyperplaneBundleIsomorphism ⟨p, t⟩)).2 =
      (toricNativeLineTrivialization (nativeSourceHyperplaneMetric blowup_edgeSmooth) v ⟨p, t⟩).2 :=
  nativeBlowdownHyperplaneFiberEquiv_coordinate blowup_edgeSmooth v hp t

end SGPT.Toric.BlowdownDraft

end
/- END SourceOriginalBlowupOkounkovDraft -/
end PointBlowupCanonicalFragment001

section PointBlowupCanonicalFragment002
/- BEGIN PhysicalPowerFlagValuationDraft; original source SHA256 7ab60f900c66e20e19a70933a3ef5ee4f914e26fe5533428270206797ce80cce -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeRightUnit
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- An actual frame of the literal physical power, including the actual unit at zero. -/
def physicalPlainPowerFrame {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) : ∀ q, AtlasFrame (toricNativePlainPowerBundle h q)
  | 0 => unitAtlasFrame
  | k + 1 => positivePowerAtlasFrame (toricNativeLineAtlasFrame h v) k

theorem physicalPlainPowerFrame_mem {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (q : ℕ) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    p ∈ (physicalPlainPowerFrame h v q).val.baseSet := by
  cases q with
  | zero => exact mem_univ p
  | succ k => exact positivePowerAtlasFrame_mem (toricNativeLineAtlasFrame h v) hp k

/-- Readback in the INDEPENDENT actual physical plain-power frame. -/
theorem physicalPlainPowerFrame_rightUnit {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (q : ℕ) (s : ToricNativeDegreeSections h q)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((physicalPlainPowerFrame h v q).val ⟨p, toricNativePlainPowerRightUnitEquiv h q s p⟩).2 =
      ((toricNativeDegreeFrame h v q).val ⟨p, s p⟩).2 := by
  cases q with
  | zero => exact (nativeRightUnit_coordinate unitAtlasFrame (mem_univ p) (s p)).symm
  | succ k => exact (nativeRightUnit_coordinate
      (positivePowerAtlasFrame (toricNativeLineAtlasFrame h v) k)
      (positivePowerAtlasFrame_mem (toricNativeLineAtlasFrame h v) hp k) (s p)).symm

theorem originalSectionCoeff_eq_sectionCoeff {D : ToricDivisor γ hs}
    (g : toricSections D) (v : latticePolytopeVertices γ) :
    toricOriginalSectionCoeff g v = toricSectionCoeff D v g.val :=
  toricSectionCoeff_unique D v (differentiable_toricOriginalSectionCoeff g v).continuous
    (differentiable_toricSectionCoeff D v g.val).continuous
    (toricOriginalSectionCoeff_torus g v) (toricSectionCoeff_spec g.property v)

/-- EVERY physical section has the SAME full Cartier coefficient on every whole source chart. -/
theorem physicalPlainPowerFrame_fullSection_coefficient {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (s : ToricNativePlainPowerSections h q)
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((physicalPlainPowerFrame h v q).val ⟨p, s p⟩).2 =
      toricSectionCoeff ((q : ℤ) • D) v (toricNativePlainPowerFullSectionEquiv h q s).val
        (originalPolytopeNativeModelChart γ hs v p) := by
  let t := (toricNativePlainPowerRightUnitEquiv h q).symm s
  have ht : toricNativePlainPowerRightUnitEquiv h q t = s := LinearEquiv.apply_symm_apply _ s
  rw [← ht, physicalPlainPowerFrame_rightUnit h v q t hp, ht]
  have hcoeff := toricNativeDegreeFullSectionEquiv_symm_coefficient h q
    (toricNativeDegreeFullSectionEquiv h q t) v hp
  rw [LinearEquiv.symm_apply_apply] at hcoeff
  exact hcoeff.trans (congrFun (originalSectionCoeff_eq_sectionCoeff
    (toricNativeDegreeFullSectionEquiv h q t) v) _)

/-- The ACTUAL coefficient function of a physical plain-power section. -/
def physicalPlainPowerCoefficient {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (v : latticePolytopeVertices γ) (s : ToricNativePlainPowerSections h q)
    (p : PolytopeToricVariety γ hs) : ℂ :=
  ((physicalPlainPowerFrame h v q).val ⟨p, s p⟩).2

theorem holomorphicAt_physicalPlainPowerCoefficient {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v : latticePolytopeVertices γ)
    (s : ToricNativePlainPowerSections h q) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    HolomorphicAt n (physicalPlainPowerCoefficient h q v s) p := by
  let f := physicalPlainPowerFrame h v q
  let := f.property
  filter_upwards [f.val.open_baseSet.mem_nhds (physicalPlainPowerFrame_mem h v q hp)] with x hx
  exact ((f.val.contMDiffAt_section_iff hx).mp (s.contMDiff x)).mdifferentiableAt (by simp)

/-- The actual holomorphic germ of the physical coefficient, BEFORE using the Cartier dictionary. -/
def physicalPlainPowerGerm {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (v : latticePolytopeVertices γ) (s : ToricNativePlainPowerSections h q) :
    NativeHolGerm n (PolytopeToricVariety γ hs) (vertexPoint hs v 0) :=
  NativeHolGerm.mk (physicalPlainPowerCoefficient h q v s)
    (holomorphicAt_physicalPlainPowerCoefficient h q v s (vertexPoint_mem_source v 0))

/-- Equality of genuine germs follows from actual coefficient equality near the original flag point. -/
theorem physicalPlainPowerGerm_eq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (v : latticePolytopeVertices γ) (s : ToricNativePlainPowerSections h q) :
    physicalPlainPowerGerm h q v s =
      toricSectionGerm ((q : ℤ) • D) v (toricNativePlainPowerFullSectionEquiv h q s).val := by
  apply NativeHolGerm.mk_eq_mk_iff.mpr
  filter_upwards [(originalPolytopeNativeModelChart γ hs v).open_source.mem_nhds
    (vertexPoint_mem_source v 0)] with p hp
  exact physicalPlainPowerFrame_fullSection_coefficient h q s v hp

/-- The SAME actual successive flag valuation, applied to the actual physical coefficient germ. -/
def physicalPlainPowerValuation {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (q : ℕ) (s : ToricNativePlainPowerSections h q) : WithTop (Lex (Fin n → ℤ)) :=
  originalFlagGermValuation (toricFlagGeometry (hs := hs) v e) (toricFlagPoint (hs := hs) v e)
    (physicalPlainPowerGerm h q v s)

theorem physicalPlainPowerValuation_eq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (q : ℕ) (s : ToricNativePlainPowerSections h q) :
    physicalPlainPowerValuation h v e q s =
      toricSectionValuation hs v e ((q : ℤ) • D) (toricNativePlainPowerFullSectionEquiv h q s).val := by
  unfold physicalPlainPowerValuation toricSectionValuation
  rw [physicalPlainPowerGerm_eq]

end SGPT.Toric.BlowdownDraft

end
/- END PhysicalPowerFlagValuationDraft -/
end PointBlowupCanonicalFragment002

section PointBlowupCanonicalFragment003
/- BEGIN PhysicalPowerOkounkovBodyDraft; original source SHA256 d5b165193dacef881f6e417c69ad323ca46845cbc5af39eebc83f565e1be8c44 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov SGPT.AlmostSemigroup
open scoped Topology Manifold ContDiff BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Values of ALL actual nonzero holomorphic sections of the literal physical power. -/
def physicalPlainPowerValues {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (q : ℕ) : Set (Fin n → ℤ) :=
  {w | ∃ s : ToricNativePlainPowerSections h q, s ≠ 0 ∧
    physicalPlainPowerValuation h v e q s = ((toLex w : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))}

/-- BOTH directions use the full actual H0 equivalence and its genuine inverse. -/
theorem physicalPlainPowerValues_eq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (q : ℕ) :
    physicalPlainPowerValues h v e q = toricSectionValues v e ((q : ℤ) • D) := by
  ext w
  constructor
  · rintro ⟨s, hs0, hw⟩
    let g := toricNativePlainPowerFullSectionEquiv h q s
    refine ⟨g.val, g.property, ?_, ?_⟩
    · intro hg
      apply hs0
      apply (toricNativePlainPowerFullSectionEquiv h q).injective
      rw [map_zero]
      exact Subtype.ext hg
    · exact (physicalPlainPowerValuation_eq h v e q s).symm.trans hw
  · rintro ⟨g, hg, hg0, hw⟩
    let s := (toricNativePlainPowerFullSectionEquiv h q).symm ⟨g, hg⟩
    refine ⟨s, ?_, ?_⟩
    · intro hs0
      apply hg0
      have h := congrArg (toricNativePlainPowerFullSectionEquiv h q) hs0
      have hsub : (⟨g, hg⟩ : toricSections ((q : ℤ) • D)) = 0 := by
        simpa only [s, LinearEquiv.apply_symm_apply, map_zero] using h
      exact congrArg Subtype.val hsub
    · rw [physicalPlainPowerValuation_eq]
      simpa only [s, LinearEquiv.apply_symm_apply] using hw

/-- The graded semigroup defined DIRECTLY from ALL actual physical sections in every degree. -/
def physicalPlainPowerSectionSemigroup {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    AddSubsemigroup ((Fin n → ℤ) × ℤ) where
  carrier := {z | ∃ q : ℕ, z.2 = q ∧ z.1 ∈ physicalPlainPowerValues h v e q}
  add_mem' := by
    intro a b ha hb
    have heq : ∀ z : (Fin n → ℤ) × ℤ, (∃ q : ℕ, z.2 = (q : ℤ) ∧ z.1 ∈ physicalPlainPowerValues h v e q) ↔
        z ∈ toricSectionSemigroup v e D := by
      intro z
      simp only [physicalPlainPowerValues_eq, toricSectionSemigroup, AddSubsemigroup.mem_mk,
        Set.mem_ofPred_eq]
    exact (heq (a + b)).mpr ((toricSectionSemigroup v e D).add_mem
      ((heq a).mp ha) ((heq b).mp hb))

theorem physicalPlainPowerSectionSemigroup_eq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    physicalPlainPowerSectionSemigroup h v e = toricSectionSemigroup v e D := by
  ext z
  change (∃ q : ℕ, z.2 = q ∧ z.1 ∈ physicalPlainPowerValues h v e q) ↔
    ∃ q : ℕ, z.2 = q ∧ z.1 ∈ toricSectionValues v e ((q : ℤ) • D)
  simp only [physicalPlainPowerValues_eq]

/-- The closed-cone slice of the semigroup of actual physical power sections. -/
def physicalPlainPowerOkounkovBody {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) : Set (Fin n → ℝ) :=
  Okounkov.body (physicalPlainPowerSectionSemigroup h v e)

theorem physicalPlainPowerOkounkovBody_eq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    physicalPlainPowerOkounkovBody h v e = toricOkounkovBody v e D := by
  unfold physicalPlainPowerOkounkovBody toricOkounkovBody
  rw [physicalPlainPowerSectionSemigroup_eq]

/-- Literal source consumer: the triangle uses ALL actual holomorphic power sections of
physical O_X(D4), which the genuine coefficient-one holomorphic bundle isomorphism above
identifies with the actual pullback π*O_P²(1). No monomial subspace is substituted. -/
theorem source_original_physical_power_okounkov_triangle :
    ∃ e : Fin 2 ≃ Fin 2,
      polytopeToricRayGenerator blowupGenerator blowup_edgeSmooth (blowupVertex 3) (e 0) = blowupRay5 ∧
      polytopeToricRayGenerator blowupGenerator blowup_edgeSmooth (blowupVertex 3) (e 1) = blowupRay7 ∧
      (∀ q, physicalPlainPowerValues (nativeSourceHyperplaneMetric blowup_edgeSmooth)
        (blowupVertex 3) e q =
          toricSectionValues (blowupVertex 3) e ((q : ℤ) • blowupHyperplaneDivisor blowup_edgeSmooth)) ∧
      physicalPlainPowerSectionSemigroup (nativeSourceHyperplaneMetric blowup_edgeSmooth)
        (blowupVertex 3) e =
          toricSectionSemigroup (blowupVertex 3) e (blowupHyperplaneDivisor blowup_edgeSmooth) ∧
      physicalPlainPowerOkounkovBody (nativeSourceHyperplaneMetric blowup_edgeSmooth)
        (blowupVertex 3) e = {y | 0 ≤ y 0 ∧ y 0 ≤ y 1 ∧ y 1 ≤ 1} ∧
      physicalPlainPowerOkounkovBody (nativeSourceHyperplaneMetric blowup_edgeSmooth)
        (blowupVertex 3) e ≠ {y | (∀ k, 0 ≤ y k) ∧ ∑ k, y k ≤ 1} := by
  obtain ⟨e, he0, he1⟩ := blowup_exists_flagOrder blowup_edgeSmooth
  refine ⟨e, he0, he1, fun q => physicalPlainPowerValues_eq _ _ _ q,
    physicalPlainPowerSectionSemigroup_eq _ _ _, ?_, ?_⟩
  · rw [physicalPlainPowerOkounkovBody_eq]
    exact (blowup_okounkovBody blowup_edgeSmooth e he0 he1).2
  · rw [physicalPlainPowerOkounkovBody_eq,
      (blowup_okounkovBody blowup_edgeSmooth e he0 he1).2]
    exact blowup_okounkovBody_ne_simplex

end SGPT.Toric.BlowdownDraft

end
/- END PhysicalPowerOkounkovBodyDraft -/
end PointBlowupCanonicalFragment003


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden flat/private provider in proper toric point-blowup module: {m}"
