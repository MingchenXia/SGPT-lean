import SGPT.Toric.SourceGeodGEndpoints
import SGPT.Convex.ClosedStripConjugation

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))
local notation "X" => PolytopeToricVariety γ hs
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem realProfile_mono {u v : X → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) (hle : u ≤ v) :
    h.realProfile u ≤ h.realProfile v := by
  intro x
  have hh := (h.le_iff hu hv).mp hle x
  rw [(h.realProfile_mem hu).2, (h.realProfile_mem hv).2, EReal.coe_le_coe_iff] at hh
  exact hh

private theorem slice_mem_of_isToricSubgeodesic
    {u₀ u₁ : X → EReal} {c : Ioo (0 : ℝ) 1 → X → EReal}
    (hc : h.IsToricSubgeodesic omega u₀ u₁ c) (t : Ioo (0 : ℝ) 1) : c t ∈ h.PSHTor := by
  refine ⟨?_, hc.2 t⟩
  have hh := hc.1.2.2.1.1 t.val t.property
  simpa only [ioo01Curve_of_mem c u₀ t.property] using hh

def sourceGeodGOpenProfile {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal} (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    E × Ioo (0 : ℝ) 1 → ℝ := fun p => h.realProfile (a.2.2.val p.2) p.1

theorem sourceGeodGOpenProfile_spec {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    h.IsToricSubgeodesicProfile a.1.val a.2.1.val (h.sourceGeodGOpenProfile omega a) :=
  h.isToricSubgeodesicProfile_of_isToricSubgeodesic omega
    a.1.property.1 a.2.1.property.1 a.2.2.property

/-- The source curve itself manufactures its literal proper closed-strip
extension. The first endpoint is part of the original source object. -/
def sourceGeodGClosedProfile {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) : E × ℝ → EReal :=
  closedStripExtension (stripFunction (h.sourceGeodGOpenProfile omega a))
    (h.realProfile a.1.val) (h.realProfile_mem a.1.property.1).1.1
    (h.sourceGeodGOpenProfile_spec omega a).1

def sourceGeodGDual {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal} (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    E × ℝ → EReal :=
  conjugate (timeProductPairing (innerₗ E)) (h.sourceGeodGClosedProfile omega a)

theorem sourceGeodGClosedProfile_proper_closed {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    IsProper (h.sourceGeodGClosedProfile omega a) ∧
      LowerSemicontinuous (h.sourceGeodGClosedProfile omega a) :=
  closedStripExtension_isProper_lowerSemicontinuous
    (stripFunction (h.sourceGeodGOpenProfile omega a))
    (h.realProfile a.1.val) (h.realProfile a.2.1.val)
    (h.realProfile_mem a.1.property.1).1.1 (h.realProfile_mem a.2.1.property.1).1.1
    (h.sourceGeodGOpenProfile_spec omega a).1
    (h.sourceGeodGOpenProfile_spec omega a).2.2
    (h.sourceGeodGOpenProfile_spec omega a).2.1

theorem sourceGeodGClosedProfile_left {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) (x : E) :
    h.sourceGeodGClosedProfile omega a (x, 0) = (h.realProfile a.1.val x : EReal) :=
  closedStripExtension_left _ _ _ _ (h.sourceGeodGOpenProfile_spec omega a).2.2 x

theorem sourceGeodGClosedProfile_right {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) (x : E) :
    h.sourceGeodGClosedProfile omega a (x, 1) = (h.realProfile a.2.1.val x : EReal) :=
  closedStripExtension_right _ _ _ _ (h.realProfile_mem a.2.1.property.1).1.1 _
    (h.sourceGeodGOpenProfile_spec omega a).2.1 x

theorem sourceGeodGClosedProfile_interior {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁)
    (x : E) (t : Ioo (0 : ℝ) 1) :
    h.sourceGeodGClosedProfile omega a (x, t.val) =
      (h.realProfile (a.2.2.val t) x : EReal) := by
  unfold sourceGeodGClosedProfile
  rw [closedStripExtension_interior _ _ _ _ t.property,
    stripFunction_of_mem _ x t.property]
  rfl

/-- Both original endpoint lower bounds are obtained from the actual endpoint
hyperplanes of the manufactured extension and the original inequalities ψ≤φ. -/
theorem sourceGeodGDual_lower {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) (m : E) (s : ℝ) :
    max (h.legendre φ₀ m) (h.legendre φ₁ m + (s : EReal)) ≤
      h.sourceGeodGDual omega a (m, s) := by
  have hp₀ : h.profile a.1.val ≤ h.profile φ₀ := by
    intro x
    exact add_le_add (a.1.property.2 _) le_rfl
  have hp₁ : h.profile a.2.1.val ≤ h.profile φ₁ := by
    intro x
    exact add_le_add (a.2.1.property.2 _) le_rfl
  have hh := closedStripConjugate_lower_bounds (innerₗ E)
    (stripFunction (h.sourceGeodGOpenProfile omega a))
    (h.realProfile a.1.val) (h.realProfile a.2.1.val)
    (h.realProfile_mem a.1.property.1).1.1 (h.realProfile_mem a.2.1.property.1).1.1
    (h.sourceGeodGOpenProfile_spec omega a).1
    (h.sourceGeodGOpenProfile_spec omega a).2.2
    (h.sourceGeodGOpenProfile_spec omega a).2.1 m s
  have h₀ := conjugate_antitone (innerₗ E) hp₀ m
  have h₁ := conjugate_antitone (innerₗ E) hp₁ m
  rw [(h.realProfile_mem a.1.property.1).2] at h₀
  rw [(h.realProfile_mem a.2.1.property.1).2] at h₁
  exact (max_le_max h₀ (add_le_add h₁ le_rfl)).trans hh

/-- The actual source slice infimum, not a supplied common profile, produces
the existential closed proper G in the printed upper bound. -/
theorem sourceGeodGDual_mem {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    IsProper (h.sourceGeodGDual omega a) ∧ LowerSemicontinuous (h.sourceGeodGDual omega a) ∧
      ∃ G : E → EReal, IsProper G ∧ LowerSemicontinuous G ∧
        ∀ (m : E) (s : ℝ),
          max (h.legendre φ₀ m) (h.legendre φ₁ m + (s : EReal)) ≤ h.sourceGeodGDual omega a (m, s) ∧
          h.sourceGeodGDual omega a (m, s) ≤ G m + ((max s 0 : ℝ) : EReal) := by
  let c := a.2.2.val
  let curve := ioo01Curve c a.1.val
  let η := sourceSliceInfimum curve
  have hinv : ∀ t ∈ Ioo (0 : ℝ) 1, PolytopeToricInvariant γ hs (curve t) := by
    intro t ht
    rw [show curve t = c ⟨t, ht⟩ from ioo01Curve_of_mem c a.1.val ht]
    exact a.2.2.property.2 _
  have hη : η ∈ h.PSHTor :=
    ⟨a.2.2.property.1.isThetaPSH_sliceInfimum, polytopeToricInvariant_sliceInfimum hinv⟩
  have hη₀ : η ≤ a.1.val := a.2.2.property.1.sliceInfimum_le_thetaRooftop.trans
    (thetaRooftop_le_left h.atlasForm a.1.val a.2.1.val)
  have hη₁ : η ≤ a.2.1.val := a.2.2.property.1.sliceInfimum_le_thetaRooftop.trans
    (thetaRooftop_le_right h.atlasForm a.1.val a.2.1.val)
  have hηt (t : Ioo (0 : ℝ) 1) : η ≤ c t := by
    intro p
    have hh := iInf_le (fun r : Ioo (0 : ℝ) 1 => curve r.val p) t
    simpa only [η, sourceSliceInfimum, curve, ioo01Curve_of_mem c a.1.val t.property] using hh
  have hlower (x : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      h.realProfile η x ≤ closedConvexStripProfile
        (stripFunction (h.sourceGeodGOpenProfile omega a))
        (h.realProfile a.1.val) (h.realProfile_mem a.1.property.1).1.1
        (h.sourceGeodGOpenProfile_spec omega a).1 (x, t) := by
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | hti)
    · rw [closedConvexStripProfile_left _ _ _ _ (h.sourceGeodGOpenProfile_spec omega a).2.2]
      exact h.realProfile_mono hη a.1.property.1 hη₀ x
    · rw [closedConvexStripProfile_right _ _ _ _
        (h.realProfile_mem a.2.1.property.1).1.1 _ (h.sourceGeodGOpenProfile_spec omega a).2.1]
      exact h.realProfile_mono hη a.2.1.property.1 hη₁ x
    · rw [closedConvexStripProfile_interior _ _ _ _ hti, stripFunction_of_mem _ x hti]
      exact h.realProfile_mono hη
        (h.slice_mem_of_isToricSubgeodesic omega a.2.2.property ⟨t, hti⟩) (hηt ⟨t, hti⟩) x
  refine ⟨isProper_conjugate_of_isContPerfPair _
    (h.sourceGeodGClosedProfile_proper_closed omega a).1, lowerSemicontinuous_conjugate _ _,
    conjugate (innerₗ E) (fun x => (h.realProfile η x : EReal)), ?_,
    lowerSemicontinuous_conjugate _ _, ?_⟩
  · exact isProper_conjugate_of_isContPerfPair _
      (isProper_coe_of_convexOn (h.realProfile_mem hη).1.1)
  · intro m s
    exact ⟨h.sourceGeodGDual_lower omega a m s,
      closedStripConjugate_upper_bound (innerₗ E)
        (stripFunction (h.sourceGeodGOpenProfile omega a)) (h.realProfile a.1.val)
        (h.realProfile η) (h.realProfile_mem a.1.property.1).1.1
        (h.sourceGeodGOpenProfile_spec omega a).1 hlower m s⟩

def sourceGeodGForward {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal} (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    h.sourceGeodGDuals φ₀ φ₁ :=
  ⟨h.sourceGeodGDual omega a, h.sourceGeodGDual_mem omega a⟩

end BigToricMetric
end SGPT.Toric
