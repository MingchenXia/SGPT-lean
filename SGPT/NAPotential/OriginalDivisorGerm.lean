import SGPT.NAPotential.OpenDivisorOrderTransport

/-!
# Every original divisor residue germ is the same actual native rational germ

Complete blueprint: `original-divisor-germ.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.OriginalDivisorGerm

open AlgebraicGeometry CategoryTheory
open SGPT.NAPotential.Berkovich OpenDivisorOrderTransport
open SGPT.NAPotential.AlgPrimes3.PrimeDivisorOver'

/-- The canonical ORIGINAL residue-field dictionary preserves every actual original
stalk germ, through its actual original specialization map. -/
theorem originalFunctionFieldEquiv_specialization {X : Scheme.{0}} [IsIntegral X]
    (D : PrimeDivisorOver X) (x : X) (h : D.π (genericPoint D.Y) ⤳ x)
    (g : X.presheaf.stalk x) :
    originalFunctionFieldEquiv D ((BerkovichPoint.specializationMap h).hom g) =
      algebraMap (X.presheaf.stalk x) X.functionField g := by
  obtain ⟨V, hx, a, rfl⟩ := X.presheaf.exists_germ_eq g
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  have hη : D.π (genericPoint D.Y) ∈ V := h.mem_open V.isOpen hx
  have hm : X.presheaf.germ V x hx ≫ BerkovichPoint.specializationMap h =
      CommRingCat.ofHom (sectionToField D V hη) := by
    change X.presheaf.germ V x hx ≫
        (X.presheaf.stalkSpecializes h ≫ X.residue (D.π (genericPoint D.Y))) =
      X.presheaf.germ V (D.π (genericPoint D.Y)) hη ≫ X.residue (D.π (genericPoint D.Y))
    rw [← Category.assoc, X.presheaf.germ_stalkSpecializes]
  have harg := congrArg
    (fun k : Γ(X, V) ⟶ X.residueField (D.π (genericPoint D.Y)) => k a) hm
  rw [X.algebraMap_germ_eq_germToFunctionField hx a]
  rw [show (BerkovichPoint.specializationMap h).hom (X.presheaf.germ V x hx a) =
      sectionToField D V hη a from harg]
  exact originalFunctionFieldEquiv_sectionToField D V hη a

end SGPT.NAPotential.OriginalDivisorGerm
