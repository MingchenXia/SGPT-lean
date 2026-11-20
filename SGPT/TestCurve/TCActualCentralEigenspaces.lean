import SGPT.TestCurve.TCActualCentralLinear
import SGPT.TestCurve.TCActualCentralSurjectivity
import SGPT.TestCurve.TCActualTotalEigen
import SGPT.TestCurve.GeometricCharacterSpaces

/-! Actual geometric central eigenspaces with the genuine covariant sign. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.GeomLin

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a) (Λ : GeomLinearization T)

/-- The actual covariant operator uses the inverse of the raw geometric pullback parameter. -/
def covariantCentralAction (c : ℂˣ) (m : ℕ) :
    Module.End ℂ (centralFiberSectionSpace T m) :=
  centralActSectionLinearMap T Λ c⁻¹ m

/-- Genuine geometric character vectors on the ENTIRE actual central fibre. -/
def geometricCentralWeight (m : ℕ) (lam : ℤ) :
    Submodule ℂ (centralFiberSectionSpace T m) where
  carrier := {u | ∀ c : ℂˣ, covariantCentralAction T Λ c m u = ((c ^ lam : ℂˣ) : ℂ) • u}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv c
    rw [map_add, hu c, hv c, smul_add]
  smul_mem' := by
    intro b u hu c
    rw [map_smul, hu c, smul_smul, smul_smul, mul_comm]

/-- Literal restriction intertwines the actual covariant character with the original weight. -/
theorem restriction_covariant_character [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) {m : ℕ} {lam : ℤ}
    {s : SectionSpace T.structureMap T.line m} (hs : s ∈ weightSpace T m lam) (c : ℂˣ) :
    covariantCentralAction T Λ c m (centralFiberRestriction T m s) =
      ((c ^ lam : ℂˣ) : ℂ) • centralFiberRestriction T m s := by
  change centralActSection T Λ c⁻¹ m (centralFiberRestriction T m s) = _
  rw [centralFiberRestriction_actSection,
    Λ.actSection_eq_negative_character_of_mem_weightSpace E hs, map_smul]
  simp only [inv_zpow, zpow_neg, inv_inv]

include Λ in
/-- Genuine spanning in actual central H0 follows from the actual surjectivity and total weights. -/
theorem restriction_weight_iSup_eq_top [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (m : ℕ)
    (hsurj : Function.Surjective (centralFiberRestriction T m)) :
    (⨆ lam : ℤ, (weightSpace T m lam).map (centralFiberRestriction T m)) = ⊤ := by
  have hspan : (⨆ lam : ℤ, weightSpace T m lam) = ⊤ :=
    ((GeomLinearization.toSectionLinearization E Λ).isInternal m).submodule_iSup_eq_top
  rw [← Submodule.map_iSup, hspan]
  simpa using (LinearMap.range_eq_top.mpr hsurj)

/-- Actual geometric central eigenspaces equal the literal restricted original weight spaces. -/
theorem geometricCentralWeight_eq_restriction_weight [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (m : ℕ)
    (hsurj : Function.Surjective (centralFiberRestriction T m)) (lam : ℤ) :
    geometricCentralWeight T Λ m lam =
      (weightSpace T m lam).map (centralFiberRestriction T m) := by
  ext u
  exact (SGPT.TestCurve.GeometricCharacterSpaces.mem_iff_character
    (fun c => covariantCentralAction T Λ c m)
    (fun mu => (weightSpace T m mu).map (centralFiberRestriction T m))
    (restriction_weight_iSup_eq_top T Λ E m hsurj)
    (by
      intro mu v hv c
      obtain ⟨s, hs, rfl⟩ := hv
      exact restriction_covariant_character T Λ E hs c) lam u).symm

end SGPT.TestCurve.CentralFiber
