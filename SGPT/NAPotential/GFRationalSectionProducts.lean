import SGPT.Okounkov.SchemeSectionWeight
import SGPT.NAPotential.BJSectionLogNorm

/-! # Actual products of the ORIGINAL sections and their whole metric logarithms
Blueprint: `gf-rational-hull.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis.FirstPass

variable {X : Scheme.{0}} {L : X.Modules}

/-- Literal transport in the actual original tensor degree. -/
def castDegreeSection {r s : ℕ} (h : r = s) (t : bundlePowerGlobalSections L r) :
    bundlePowerGlobalSections L s := h ▸ t

/-- The genuine glued product of the actual original section word, in its actual common tensor degree. -/
def sectionWordProduct (a : LineBundleAtlas L) (N : ℕ) :
    (l : List (bundlePowerGlobalSections L N)) → bundlePowerGlobalSections L (N * l.length)
  | [] => castDegreeSection (Nat.mul_zero N).symm (bundlePowerGlobalOne L)
  | t :: l => castDegreeSection
      ((Nat.add_comm N (N * l.length)).trans (Nat.mul_succ N l.length).symm)
        (atlasPowerGlobalMul a N (N * l.length) t (sectionWordProduct a N l))

variable {f : X ⟶ Spec (.of ℂ)} [IsProper f]

/-- Actual original valuations respect the literal tensor-degree transport. -/
theorem castDegreeSection_value (a : LineBundleAtlas L) {r s : ℕ} (h : r = s)
    (t : bundlePowerGlobalSections L r) (v : BerkovichPoint f) :
    powerSectionValue a s (castDegreeSection h t) v = powerSectionValue a r t v := by
  cases h
  rfl

/-- The genuine degree-zero section unit has value zero at EVERY original Berkovich point. -/
theorem sectionUnit_value (a : LineBundleAtlas L) (v : BerkovichPoint f) :
    powerSectionValue a 0 (bundlePowerGlobalOne L) v = 0 := by
  change v.sectionVal _ _ (atlasPowerGlobalCoefficients a 0 (centerIndex a v) (bundlePowerGlobalOne L)) = 0
  rw [atlasPowerGlobalCoefficients_one]
  simp only [BerkovichPoint.sectionVal, map_one, BerkovichPoint.valAt_one]

/-- **Actual section-word products add the original values at ALL original Berkovich points**, including poles. -/
theorem sectionWordProduct_value (a : LineBundleAtlas L) (N : ℕ)
    (l : List (bundlePowerGlobalSections L N)) (v : BerkovichPoint f) :
    powerSectionValue a (N * l.length) (sectionWordProduct a N l) v =
      (l.map (fun t => powerSectionValue a N t v)).sum := by
  induction l with
  | nil => rw [sectionWordProduct, castDegreeSection_value, sectionUnit_value]; rfl
  | cons t l ih =>
    rw [sectionWordProduct, castDegreeSection_value, powerSectionValue_mul, ih]
    rfl

include f in
/-- The ORIGINAL nonzero sections manufacture nonvanishing of their ACTUAL product, rather than assume it. -/
theorem sectionWordProduct_ne_zero [IsIntegral X] (a : LineBundleAtlas L) (N : ℕ)
    (l : List (bundlePowerGlobalSections L N)) (hl : ∀ t ∈ l, t ≠ 0) :
    sectionWordProduct a N l ≠ 0 := by
  intro hz
  have hv := sectionWordProduct_value a N l (BerkovichPoint.trivial f)
  rw [hz, powerSectionValue_zero] at hv
  have hsum : (l.map (fun t => powerSectionValue a N t (BerkovichPoint.trivial f))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact powerSectionValue_trivial a N t (hl t ht)
  rw [hsum] at hv
  exact WithTop.top_ne_zero hv

variable (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  (H : SchemeLineBundleMetric f n E L)

omit [IsProper f] in
/-- The SAME original metric respects literal transport in the original tensor degree. -/
theorem castDegreeSection_logNormSq (a : LineBundleAtlas L) {r s : ℕ} (h : r = s)
    (t : bundlePowerGlobalSections L r) :
    H.sectionLogNormSq a s (castDegreeSection h t) = H.sectionLogNormSq a r t := by
  cases h
  rfl

omit [IsProper f] in
/-- **The ACTUAL common-degree original section product has the sum of its ORIGINAL whole logarithmic norms**, including zero loci. -/
theorem sectionWordProduct_logNormSq (a : LineBundleAtlas L) (N : ℕ)
    (l : List (bundlePowerGlobalSections L N)) :
    H.sectionLogNormSq a (N * l.length) (sectionWordProduct a N l) =
      fun p => (l.map (fun t => H.sectionLogNormSq a N t p)).sum := by
  induction l with
  | nil => rw [sectionWordProduct, castDegreeSection_logNormSq, H.sectionLogNormSq_one]; rfl
  | cons t l ih =>
    rw [sectionWordProduct, castDegreeSection_logNormSq, H.sectionLogNormSq_mul, ih]
    rfl

end SGPT.NAPotential.BJ.GfIm.RationalHull
