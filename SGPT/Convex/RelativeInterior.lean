import SGPT.Convex.AffineMinorant
import SGPT.Convex.IntrinsicSegment
import Mathlib.Analysis.Convex.Continuous

/-!
# Relative interiors of effective domains

The source closure agreement in Appendix A uses the actual affine span of the
effective domain. Finite-dimensional continuity is applied only after transport
to its direction space, so lower-dimensional domains are included.
-/

namespace SGPT.Convex

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Properness makes the real restriction to the actual effective domain convex. -/
theorem convexOn_toReal_effectiveDomain {f : E → EReal} (hf : IsProper f) :
    ConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x).toReal) := by
  have hfinite {x : E} (hx : x ∈ effectiveDomain f) : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 x)).symm
  refine ⟨convex_effectiveDomain hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ effectiveDomain f :=
    convex_effectiveDomain hf.1 hx hy ha hb hab
  have hp : (x, (f x).toReal) ∈ epigraph f := (hfinite hx).le
  have hq : (y, (f y).toReal) ∈ epigraph f := (hfinite hy).le
  have h := hf.1 hp hq ha hb hab
  change f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) at h
  rw [hfinite hxy, EReal.coe_le_coe_iff] at h
  exact h

omit [NormedSpace ℝ E] in
/-- Outside the actual closed effective domain, no real height occurs in the
closed epigraph, so regularization is positive infinity. -/
theorem regularization_eq_top_of_not_mem_closure_effectiveDomain {f : E → EReal}
    {x : E} (hx : x ∉ _root_.closure (effectiveDomain f)) : regularization f x = ⊤ := by
  have hsub : _root_.closure (epigraph f) ⊆
      Prod.fst ⁻¹' _root_.closure (effectiveDomain f) := by
    apply closure_minimal
    · intro p hp
      exact subset_closure (hp.trans_lt (EReal.coe_lt_top p.2))
    · exact isClosed_closure.preimage continuous_fst
  apply top_le_iff.mp
  unfold regularization
  apply le_iInf
  intro r
  apply le_iInf
  intro h
  exact False.elim (hx (hsub h))

variable [FiniteDimensional ℝ E]

/-- The real restriction to the actual domain affine span is continuous at each
relative-interior point, by transport to the direction subspace. -/
theorem continuousAt_toReal_affineSpan_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsProper f) (x : affineSpan ℝ (effectiveDomain f))
    (hx : (x : E) ∈ intrinsicInterior ℝ (effectiveDomain f)) :
    ContinuousAt (fun z : affineSpan ℝ (effectiveDomain f) ↦ (f z).toReal) x := by
  let A := affineSpan ℝ (effectiveDomain f)
  let : Nonempty A := ⟨x⟩
  let e := AffineIsometryEquiv.vaddConst ℝ x
  let F := A.subtype.comp e.toAffineEquiv.toAffineMap
  let D : Set A.direction := F ⁻¹' effectiveDomain f
  have hxA : x ∈ interior ((↑) ⁻¹' effectiveDomain f : Set A) := by
    obtain ⟨y, hy, heq⟩ := mem_intrinsicInterior.mp hx
    have hyx : y = x := Subtype.ext heq
    simpa only [hyx] using hy
  have hzero : (0 : A.direction) ∈ interior D := by
    change (0 : A.direction) ∈ interior
      (e.toHomeomorph ⁻¹' ((↑) ⁻¹' effectiveDomain f : Set A))
    rw [← e.toHomeomorph.preimage_interior]
    change e 0 ∈ interior ((↑) ⁻¹' effectiveDomain f : Set A)
    simpa [e] using hxA
  have hconv : ConvexOn ℝ D (fun v ↦ (f (F v)).toReal) :=
    (convexOn_toReal_effectiveDomain hf).comp_affineMap F
  have hc : ContinuousAt (fun v : A.direction ↦ (f (F v)).toReal) 0 :=
    (hconv.continuousOn_interior 0 hzero).continuousAt (isOpen_interior.mem_nhds hzero)
  have hc' : ContinuousAt (fun v : A.direction ↦ (f (F v)).toReal) (e.symm x) := by
    simpa [e] using hc
  have h := hc'.comp e.symm.continuous.continuousAt
  change ContinuousAt (fun z : A ↦ (f (e (e.symm z))).toReal) x at h
  simpa only [e.apply_symm_apply] using h

/-- Relative-interior continuity forbids the actual epigraph closure from
containing a height smaller than the obstacle value. -/
theorem le_height_of_mem_closure_epigraph_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsProper f) {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    {r : ℝ} (hr : (x, r) ∈ _root_.closure (epigraph f)) : f x ≤ (r : EReal) := by
  let A := affineSpan ℝ (effectiveDomain f)
  let xA : A := ⟨x, subset_affineSpan ℝ _ (intrinsicInterior_subset hx)⟩
  let J : A × ℝ → E × ℝ := Prod.map Subtype.val id
  let C : Set (A × ℝ) := J ⁻¹' epigraph f
  have hJ : Topology.IsEmbedding J := Topology.IsEmbedding.subtypeVal.prodMap .id
  have himage : J '' C = epigraph f := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      have hpD : p.1 ∈ effectiveDomain f := hp.trans_lt (EReal.coe_lt_top p.2)
      exact ⟨(⟨p.1, subset_affineSpan ℝ _ hpD⟩, p.2), hp, rfl⟩
  have hcl : (xA, r) ∈ _root_.closure C := by
    rw [hJ.closure_eq_preimage_closure_image, himage]
    exact hr
  let H : A × ℝ → ℝ := fun p ↦ (f p.1).toReal - p.2
  have hc : ContinuousAt (fun z : A ↦ (f z).toReal) xA :=
    continuousAt_toReal_affineSpan_of_mem_intrinsicInterior hf xA hx
  have hH : ContinuousAt H (xA, r) := by
    have hc' : ContinuousAt (fun p : A × ℝ ↦ (f p.1).toReal) (xA, r) :=
      ContinuousAt.comp' (f := fun p : A × ℝ ↦ p.1)
        (g := fun z : A ↦ (f z).toReal) hc
        (show ContinuousAt (fun p : A × ℝ ↦ p.1) (xA, r) from continuous_fst.continuousAt)
    exact hc'.sub (show ContinuousAt (fun p : A × ℝ ↦ p.2) (xA, r) from
      continuous_snd.continuousAt)
  have hm : Set.MapsTo H C (Set.Iic 0) := by
    intro p hp
    have hp' : f p.1 ≤ (p.2 : EReal) := hp
    have hfinite : f p.1 = ((f p.1).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt (hp'.trans_lt (EReal.coe_lt_top p.2))) (hf.2.2 p.1)).symm
    rw [hfinite, EReal.coe_le_coe_iff] at hp'
    change (f p.1).toReal - p.2 ≤ 0
    linarith
  have hbound := hH.continuousWithinAt.mem_closure hcl hm
  have hh : H (xA, r) ≤ 0 := by simpa only [isClosed_Iic.closure_eq, mem_Iic] using hbound
  have hxD : x ∈ effectiveDomain f := intrinsicInterior_subset hx
  have hfinite : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hxD) (hf.2.2 x)).symm
  rw [hfinite, EReal.coe_le_coe_iff]
  dsimp [H, xA] at hh
  linarith

/-- At an actual relative-interior domain point, regularization equals the
original proper convex function. -/
theorem regularization_eq_of_mem_intrinsicInterior {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) :
    regularization f x = f x := by
  apply le_antisymm (regularization_le f x)
  by_contra h
  obtain ⟨r, hr₁, hr₂⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hr : (x, r) ∈ _root_.closure (epigraph f) := by
    rw [← epigraph_regularization]
    exact hr₁.le
  exact not_le_of_gt hr₂ (le_height_of_mem_closure_epigraph_of_mem_intrinsicInterior hf hx hr)

/-- Full source relative-boundary agreement: a proper convex function and its
actual source closure agree away from the intrinsic frontier of the domain. -/
theorem convexClosure_eq_of_not_mem_intrinsicFrontier {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∉ intrinsicFrontier ℝ (effectiveDomain f)) :
    convexClosure f x = f x := by
  rw [convexClosure_of_forall_ne_bot hf.2.2]
  by_cases hcl : x ∈ _root_.closure (effectiveDomain f)
  · have hri : x ∈ intrinsicInterior ℝ (effectiveDomain f) := by
      simpa only [closure_sdiff_intrinsicFrontier] using
        (show x ∈ _root_.closure (effectiveDomain f) \ intrinsicFrontier ℝ (effectiveDomain f)
          from ⟨hcl, hx⟩)
    exact regularization_eq_of_mem_intrinsicInterior hf hri
  · rw [regularization_eq_top_of_not_mem_closure_effectiveDomain hcl]
    have hnot : x ∉ effectiveDomain f := fun h ↦ hcl (subset_closure h)
    have ht : f x = ⊤ := by
      by_contra h
      exact hnot (lt_top_iff_ne_top.mpr h)
    exact ht.symm

/-- A source-closed convex function has exactly the closed epigraph determined
by its actual relative-interior restriction, including infinite constants. -/
theorem epigraph_eq_closure_restrictedEpigraph_of_isClosedConvex {f : E → EReal}
    (hf : IsClosedConvex f) :
    epigraph f = _root_.closure (restrictedEpigraph f) := by
  have hlsc : LowerSemicontinuous f := by
    rw [← convexClosure_eq_self_of_isClosedConvex hf]
    exact lowerSemicontinuous_convexClosure f
  exact subset_antisymm
    (epigraph_subset_closure_restrictedEpigraph (isConvex_of_isClosedConvex hf))
    (closure_minimal (fun _ h ↦ h.1) (isClosed_epigraph_iff_lowerSemicontinuous.mpr hlsc))

/-- Full source `prop:closedcvx_domain`: source-closed convex functions are
uniquely determined by their common relative-interior domain and values there. -/
theorem eq_of_isClosedConvex_of_eqOn_intrinsicInterior {f g : E → EReal}
    (hf : IsClosedConvex f) (hg : IsClosedConvex g)
    (hD : intrinsicInterior ℝ (effectiveDomain f) = intrinsicInterior ℝ (effectiveDomain g))
    (hfg : Set.EqOn f g (intrinsicInterior ℝ (effectiveDomain f))) : f = g := by
  have hrestricted : restrictedEpigraph f = restrictedEpigraph g := by
    ext p
    constructor
    · intro hp
      refine ⟨?_, hD ▸ hp.2⟩
      change g p.1 ≤ (p.2 : EReal)
      rw [← hfg hp.2]
      exact hp.1
    · intro hp
      have hpD : p.1 ∈ intrinsicInterior ℝ (effectiveDomain f) := hD.symm ▸ hp.2
      refine ⟨?_, hpD⟩
      change f p.1 ≤ (p.2 : EReal)
      rw [hfg hpD]
      exact hp.1
  have hepi : epigraph f = epigraph g := by
    rw [epigraph_eq_closure_restrictedEpigraph_of_isClosedConvex hf,
      epigraph_eq_closure_restrictedEpigraph_of_isClosedConvex hg, hrestricted]
  apply le_antisymm
  · apply le_iff_epigraph_subset.mpr
    rw [hepi]
  · apply le_iff_epigraph_subset.mpr
    rw [hepi]

end SGPT.Convex
