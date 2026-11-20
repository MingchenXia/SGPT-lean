import SGPT.Convex.Epigraph
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Intrinsic-interior segments and actual epigraph density

Shared geometric producers for Appendix A's relative-interior Legendre
formula and uniqueness of closed convex functions. Intrinsic interior always
uses the actual affine span; no full-dimensional-domain assumption is made.
-/

namespace SGPT.Convex

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive coefficient at an actual intrinsic-interior point keeps a
convex combination in the intrinsic interior. -/
theorem combo_mem_intrinsicInterior {C : Set E} (hC : Convex ℝ C)
    {x y : E} (hx : x ∈ intrinsicInterior ℝ C) (hy : y ∈ C)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ intrinsicInterior ℝ C := by
  rcases mem_intrinsicInterior.mp hx with ⟨xA, hxA, rfl⟩
  let A := affineSpan ℝ C
  let : Nonempty A := ⟨xA⟩
  let e := AffineIsometryEquiv.vaddConst ℝ xA
  let F := A.subtype.comp e.toAffineEquiv.toAffineMap
  let C' : Set A.direction := F ⁻¹' C
  let yA : A := ⟨y, subset_affineSpan ℝ C hy⟩
  let yD : A.direction := e.symm yA
  have hC' : Convex ℝ C' := hC.affine_preimage F
  have hzero : (0 : A.direction) ∈ interior C' := by
    change (0 : A.direction) ∈ interior (e.toHomeomorph ⁻¹' ((↑) ⁻¹' C : Set A))
    rw [← e.toHomeomorph.preimage_interior]
    change e 0 ∈ interior ((↑) ⁻¹' C : Set A)
    simpa [e] using hxA
  have hFy : F yD = y := by simp [F, yD, yA]
  have hyD : yD ∈ C' := by change F yD ∈ C; rw [hFy]; exact hy
  have hi := hC'.combo_interior_self_mem_interior hzero hyD ha hb hab
  have hmem : F (a • 0 + b • yD) ∈ intrinsicInterior ℝ C := by
    apply mem_intrinsicInterior.mpr
    refine ⟨e (a • 0 + b • yD), ?_, rfl⟩
    change e (a • 0 + b • yD) ∈ interior ((↑) ⁻¹' C : Set A)
    change a • 0 + b • yD ∈ e.toHomeomorph ⁻¹' interior ((↑) ⁻¹' C : Set A)
    rw [e.toHomeomorph.preimage_interior]
    exact hi
  have hyvalue : (yD : E) + (xA : E) = y := by
    simpa [F, e, AffineSubspace.coe_vadd, vadd_eq_add] using hFy
  have hvalue : F (a • 0 + b • yD) = a • (xA : E) + b • y := by
    change a • (0 : E) + b • (yD : E) + (xA : E) = _
    rw [smul_zero, zero_add, (eq_sub_iff_add_eq).mpr hyvalue, smul_sub]
    calc
      _ = (b • y - b • (xA : E)) + (a + b) • (xA : E) := by rw [hab, one_smul]
      _ = _ := by rw [add_smul]; abel
  simpa only [hvalue] using hmem

/-- The actual epigraph restricted to the intrinsic interior of the actual
effective domain. Both infinite-value conventions remain in the obstacle. -/
def restrictedEpigraph (f : E → EReal) : Set (E × ℝ) :=
  {p | p ∈ epigraph f ∧ p.1 ∈ intrinsicInterior ℝ (effectiveDomain f)}

/-- Actual open epigraph segments show relative-interior restriction is dense
in the full epigraph; no continuity or properness certificate is assumed. -/
theorem epigraph_subset_closure_restrictedEpigraph [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : IsConvex f) :
    epigraph f ⊆ _root_.closure (restrictedEpigraph f) := by
  intro p hp
  have hpD : p.1 ∈ effectiveDomain f := hp.trans_lt (EReal.coe_lt_top p.2)
  obtain ⟨w, hw⟩ := (show (effectiveDomain f).Nonempty from ⟨p.1, hpD⟩).intrinsicInterior
    (convex_effectiveDomain hf)
  have hwmem : w ∈ effectiveDomain f := intrinsicInterior_subset hw
  have hwD : f w < ⊤ := hwmem
  obtain ⟨u, hu, _⟩ := EReal.exists_between_coe_real hwD
  let q : E × ℝ := (w, u)
  have hq : q ∈ epigraph f := hu.le
  have hsegment : openSegment ℝ p q ⊆ restrictedEpigraph f := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hf hp hq ha.le hb.le hab, ?_⟩
    change a • p.1 + b • w ∈ intrinsicInterior ℝ (effectiveDomain f)
    simpa only [add_comm] using combo_mem_intrinsicInterior (convex_effectiveDomain hf)
      hw hpD hb ha.le (by linarith : b + a = 1)
  apply _root_.closure_mono hsegment
  exact segment_subset_closure_openSegment (left_mem_segment ℝ p q)

end SGPT.Convex
