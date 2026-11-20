import SGPT.Toric.SourceGeodGRecovery

/-! Whole original cor:geodG: arbitrary original toric endpoints, actual source
subgeodesics with endpoints below them, and the exact proper closed dual bounds.
The bijection is actual closed-strip conjugation in every natural dimension. -/

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

private theorem eq_of_realProfile_eq {u v : X → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor)
    (hh : h.realProfile u = h.realProfile v) : u = v := by
  have he : h.equivRealGrowth ⟨u, hu⟩ = h.equivRealGrowth ⟨v, hv⟩ := Subtype.ext hh
  exact congrArg Subtype.val (h.equivRealGrowth.injective he)

theorem sourceGeodGClosedProfile_biconjugate {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    conjugate (timeProductPairing (innerₗ E)).flip (h.sourceGeodGDual omega a) =
      h.sourceGeodGClosedProfile omega a := by
  have hp := h.sourceGeodGClosedProfile_proper_closed omega a
  change conjugate (timeProductPairing (innerₗ E)).flip
    (conjugate (timeProductPairing (innerₗ E)) (h.sourceGeodGClosedProfile omega a)) = _
  rw [biconjugate_eq_convexClosure_of_isContPerfPair _ hp.1.1]
  exact convexClosure_eq_self_of_isClosedConvex (Or.inr (Or.inr hp))

/-- Endpoint profiles and all interior profiles read back from the same literal
closed extension, so both original endpoints and the whole source curve agree. -/
theorem sourceGeodGClosedProfile_injective {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal} :
    Function.Injective (h.sourceGeodGClosedProfile omega (φ₀ := φ₀) (φ₁ := φ₁)) := by
  intro a b hab
  have he₀ : a.1.val = b.1.val := by
    apply h.eq_of_realProfile_eq a.1.property.1 b.1.property.1
    funext x
    have hh := congrFun hab (x, 0)
    rw [h.sourceGeodGClosedProfile_left omega a x,
      h.sourceGeodGClosedProfile_left omega b x] at hh
    exact EReal.coe_injective hh
  have he₁ : a.2.1.val = b.2.1.val := by
    apply h.eq_of_realProfile_eq a.2.1.property.1 b.2.1.property.1
    funext x
    have hh := congrFun hab (x, 1)
    rw [h.sourceGeodGClosedProfile_right omega a x,
      h.sourceGeodGClosedProfile_right omega b x] at hh
    exact EReal.coe_injective hh
  have hprofiles (t : Ioo (0 : ℝ) 1) (x : E) :
      h.realProfile (a.2.2.val t) x = h.realProfile (b.2.2.val t) x := by
    have hh := congrFun hab (x, t.val)
    rw [h.sourceGeodGClosedProfile_interior omega a x t,
      h.sourceGeodGClosedProfile_interior omega b x t] at hh
    exact EReal.coe_injective hh
  rcases a with ⟨⟨u₀, hu₀, hu₀le⟩, ⟨u₁, hu₁, hu₁le⟩, ⟨ca, hca⟩⟩
  rcases b with ⟨⟨v₀, hv₀, hv₀le⟩, ⟨v₁, hv₁, hv₁le⟩, ⟨cb, hcb⟩⟩
  dsimp at he₀ he₁
  subst v₀ v₁
  have hp : (fun p : E × Ioo (0 : ℝ) 1 => h.realProfile (ca p.2) p.1) =
      (fun p : E × Ioo (0 : ℝ) 1 => h.realProfile (cb p.2) p.1) :=
    funext fun p => hprofiles p.2 p.1
  have he : h.toricSubgeodesicEquiv omega hu₀ hu₁ ⟨ca, hca⟩ =
      h.toricSubgeodesicEquiv omega hu₀ hu₁ ⟨cb, hcb⟩ := Subtype.ext hp
  have hc : ca = cb := congrArg Subtype.val
    ((h.toricSubgeodesicEquiv omega hu₀ hu₁).injective he)
  subst cb
  rfl

theorem sourceGeodGForward_bijective {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (hφ₀ : φ₀ ∈ h.PSHTor) (hφ₁ : φ₁ ∈ h.PSHTor) :
    Function.Bijective (h.sourceGeodGForward omega (φ₀ := φ₀) (φ₁ := φ₁)) := by
  constructor
  · intro a b hab
    apply h.sourceGeodGClosedProfile_injective omega
    have hh := congrArg Subtype.val hab
    have hc := congrArg (conjugate (timeProductPairing (innerₗ E)).flip) hh
    exact (h.sourceGeodGClosedProfile_biconjugate omega a).symm.trans
      (hc.trans (h.sourceGeodGClosedProfile_biconjugate omega b))
  · intro Ψ
    obtain ⟨a, ha⟩ := h.exists_sourceGeodGClosedProfile_eq_conjugate omega hφ₀ hφ₁ Ψ
    refine ⟨a, Subtype.ext ?_⟩
    change conjugate (timeProductPairing (innerₗ E)) (h.sourceGeodGClosedProfile omega a) = Ψ.val
    rw [ha]
    have hb := biconjugate_eq_convexClosure_of_isContPerfPair
      (timeProductPairing (innerₗ E)).flip Ψ.property.1.1
    have hb' : conjugate (timeProductPairing (innerₗ E))
        (conjugate (timeProductPairing (innerₗ E)).flip Ψ.val) = convexClosure Ψ.val := by
      simpa only [LinearMap.flip_flip] using hb
    exact hb'.trans (convexClosure_eq_self_of_isClosedConvex
      (Or.inr (Or.inr ⟨Ψ.property.1, Ψ.property.2.1⟩)))

/-- WHOLE original cor:geodG, with arbitrary original toric endpoints, their
literal source lower-endpoint subgeodesics, and the printed closed proper dual
bounds. No positive-mass, P-equivalence or nonempty-common-domain premise. -/
def sourceToricGeodGEquiv {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (hφ₀ : φ₀ ∈ h.PSHTor) (hφ₁ : φ₁ ∈ h.PSHTor) :
    h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁ ≃ h.sourceGeodGDuals φ₀ φ₁ :=
  Equiv.ofBijective (h.sourceGeodGForward omega) (h.sourceGeodGForward_bijective omega hφ₀ hφ₁)

theorem sourceToricGeodGEquiv_apply {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (hφ₀ : φ₀ ∈ h.PSHTor) (hφ₁ : φ₁ ∈ h.PSHTor)
    (a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁) :
    (h.sourceToricGeodGEquiv omega hφ₀ hφ₁ a).val = h.sourceGeodGDual omega a := rfl

/-- The inverse reads the actual full product conjugate of Ψ, including both
true boundary hyperplanes and +∞ off the strip. -/
theorem sourceToricGeodGEquiv_symm_closedProfile {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (hφ₀ : φ₀ ∈ h.PSHTor) (hφ₁ : φ₁ ∈ h.PSHTor) (Ψ : h.sourceGeodGDuals φ₀ φ₁) :
    h.sourceGeodGClosedProfile omega ((h.sourceToricGeodGEquiv omega hφ₀ hφ₁).symm Ψ) =
      conjugate (timeProductPairing (innerₗ E)).flip Ψ.val := by
  let a := (h.sourceToricGeodGEquiv omega hφ₀ hφ₁).symm Ψ
  have hh := congrArg Subtype.val ((h.sourceToricGeodGEquiv omega hφ₀ hφ₁).apply_symm_apply Ψ)
  change h.sourceGeodGDual omega a = Ψ.val at hh
  exact (h.sourceGeodGClosedProfile_biconjugate omega a).symm.trans
    (congrArg (conjugate (timeProductPairing (innerₗ E)).flip) hh)

end BigToricMetric
end SGPT.Toric
