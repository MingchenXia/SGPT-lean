import SGPT.Toric.Toric3OkounkovBody
import SGPT.Toric.PolytopeToricMongeAmpere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual inverse edge-basis transpose has exactly the original ray
pairings as its coordinates. Unimodularity was proved independently. -/
theorem latticeBasisLogInverseTranspose_vertex (v : latticePolytopeVertices γ)
    (x : E) (j : Fin n) :
    latticeBasisLogInverseTranspose (originalPolytopeNativeBasis γ hs v) x j =
      latticeFunctional (polytopeToricRayGenerator γ hs v j) x := by
  change latticeFunctional
    (fun k => (originalPolytopeNativeBasis γ hs v).repr (Pi.single k 1) j) x = _
  congr 1

/-- Literal affine lattice coordinates of the original toric flag, as an
actual homeomorphism into the source's real tuple space. -/
def toricFlagRealHomeomorph (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) : E ≃ₜ (Fin n → ℝ) :=
  (((latticeBasisUnimodularChange (originalPolytopeNativeBasis γ hs v)).affine
      (latticeVector (toricCartierDatum D v))).trans
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph).trans
      (Homeomorph.piCongrLeft (Y := fun _ : Fin n => ℝ) e.symm)

theorem toricFlagRealHomeomorph_apply (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) (x : E) :
    toricFlagRealHomeomorph v e D x = toricFlagRealMap hs v e D x := by
  funext j
  have hperm (w : Fin n → ℝ) :
      (Homeomorph.piCongrLeft (Y := fun _ : Fin n => ℝ) e.symm) w j = w (e j) := by
    have hh := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) e.symm w (e j)
    change (Equiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm) w j = w (e j)
    simpa only [Equiv.symm_apply_apply] using hh
  change (Homeomorph.piCongrLeft (Y := fun _ : Fin n => ℝ) e.symm)
    ((EuclideanSpace.equiv (Fin n) ℝ)
      ((latticeBasisUnimodularChange (originalPolytopeNativeBasis γ hs v)).affine
        (latticeVector (toricCartierDatum D v)) x)) j = _
  rw [hperm]
  change latticeBasisLogInverseTranspose (originalPolytopeNativeBasis γ hs v)
    (x - latticeVector (toricCartierDatum D v)) (e j) = _
  rw [latticeBasisLogInverseTranspose_vertex, map_sub, latticeFunctional_latticeVector, intPairing_comm]
  rfl

/-- Normalized lattice volume is genuinely preserved by the original
unimodular flag coordinate map, including n=0. -/
theorem measurePreserving_toricFlagRealHomeomorph (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (D : ToricDivisor γ hs) :
    MeasurePreserving (toricFlagRealHomeomorph v e D) volume volume := by
  have hA : MeasurePreserving
      ((latticeBasisUnimodularChange (originalPolytopeNativeBasis γ hs v)).affine
        (latticeVector (toricCartierDatum D v))) volume volume :=
    ⟨(Homeomorph.continuous _).measurable,
      (latticeBasisUnimodularChange _).measurePreserving_affine _⟩
  have hP := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm
  exact hP.comp ((PiLp.volume_preserving_ofLp (Fin n)).comp hA)

/-- Ordinary volume of the literal original image, with no determinant or
normalization supplied as a premise. -/
theorem volume_image_toricFlagRealMap (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) (C : Set E) :
    volume (toricFlagRealMap hs v e D '' C) = volume C := by
  let f := toricFlagRealHomeomorph v e D
  have hf : MeasurePreserving f.toMeasurableEquiv volume volume :=
    measurePreserving_toricFlagRealHomeomorph v e D
  have heq : (toricFlagRealMap hs v e D '' C) = f.symm ⁻¹' C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change f.symm (toricFlagRealMap hs v e D x) ∈ C
      rw [← toricFlagRealHomeomorph_apply, f.symm_apply_apply]
      exact hx
    · intro hy
      exact ⟨f.symm y, hy, (toricFlagRealHomeomorph_apply v e D (f.symm y)).symm.trans
        (f.apply_symm_apply y)⟩
  rw [heq]
  exact hf.symm.measure_preimage_equiv C

end SGPT.Toric
