import SGPT.Foundations.Schemes.NativePowerSectionRing
import SGPT.Foundations.Schemes.TwistedModuleSectionAction

/-!
# Multiplication on actual tensor-power residue sections

The original-atlas residue regrouping intertwines the actual twisted section
action with multiplication in the original line-bundle section ring.
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace SGPT.Foundations.Schemes

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}}

/-- Scalar tensor-frame coefficients are the scalar coefficients of the
actual module-valued tensor coefficients. -/
theorem nativeTensorFrame_coefficients_eq_moduleCoefficients
    {P Q : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame P U) (f : LocalBundleFrame Q U) (h : W ⟶ U)
    (t : bundleSections (bundleTensor P Q) W) :
    (e.tensor f).coefficients h t =
      f.coefficients h (e.tensorModuleCoefficients Q h t) := by
  conv_lhs => rw [← e.tensorModuleCoefficients_reconstruct Q h t]
  rw [LocalBundleFrame.tensor_coefficients, LinearEquiv.apply_symm_apply, one_mul]

private theorem inverse_global_coefficients {P Q : X.Modules}
    (E : P ≅ Q) (U V : X.Opens) (h : U ⟶ V) {R : Type u}
    (α : bundleSections P U → R) (β : bundleSections Q U → R)
    (hc : ∀ s, β (E.hom.val.app (.op U) s) = α s) (t : bundleSections Q V) :
    α (P.val.map h.op (E.inv.val.app (.op V) t)) = β (Q.val.map h.op t) := by
  rw [← hc, PresheafOfModules.naturality_apply]
  have hi : E.hom.val.app (.op V) (E.inv.val.app (.op V) t) = t :=
    congr($(E.inv_hom_id).val.app (.op V) |>.hom t)
  rw [hi]

variable (L : IntrinsicLineBundle X) (q : ℕ)

/-- The inverse original-atlas residue regrouping on actual global sections. -/
def IntrinsicLineBundle.nativeResidueSection (m r : ℕ) :
    bundleTwistedGlobalSections (L.tensorPower q).sheaf (bundleTensorPower L.sheaf r) m →+
      bundlePowerGlobalSections L.sheaf (q * m + r) :=
  ((nativeLineTensorPowerResidueIso L.atlas q m r).inv.val.app (.op ⊤)).hom.toAddMonoidHom

/-- Residue regrouping retains the original tensor-frame coefficient on every
subordinate open of the original atlas. -/
theorem IntrinsicLineBundle.nativeResidueSection_coefficients (m r : ℕ) (i : L.atlas.I)
    (W : X.Opens) (h : W ⟶ L.atlas.opens i)
    (t : bundleTwistedGlobalSections (L.tensorPower q).sheaf (bundleTensorPower L.sheaf r) m) :
    ((L.atlas.frame i).tensorPower (q * m + r)).coefficients h
      ((bundleTensorPower L.sheaf (q * m + r)).val.map W.leTop.op
        (L.nativeResidueSection q m r t)) =
    ((((L.atlas.frame i).tensorPower q).tensorPower m).tensor
        ((L.atlas.frame i).tensorPower r)).coefficients h
      ((bundleTensor (bundleTensorPower (bundleTensorPower L.sheaf q) m)
        (bundleTensorPower L.sheaf r)).val.map W.leTop.op t) := by
  exact inverse_global_coefficients (nativeLineTensorPowerResidueIso L.atlas q m r)
    W ⊤ W.leTop (((L.atlas.frame i).tensorPower (q * m + r)).coefficients h)
    (((((L.atlas.frame i).tensorPower q).tensorPower m).tensor
      ((L.atlas.frame i).tensorPower r)).coefficients h)
    (fun s ↦ nativeLineTensorPowerResidueIso_coefficients L.atlas q m r i h s) t

/-- Actual power regrouping preserves section multiplication on any scheme,
including the genuine arithmetic identification of its degrees. -/
theorem IntrinsicLineBundle.nativePowerSection_mul (d m : ℕ)
    (s : bundlePowerGlobalSections (L.tensorPower q).sheaf d)
    (t : bundlePowerGlobalSections (L.tensorPower q).sheaf m) :
    HEq (L.nativePowerSection q (d + m)
      (atlasPowerGlobalMul (L.tensorPower q).atlas d m s t))
      (atlasPowerGlobalMul L.atlas (q * d) (q * m)
        (L.nativePowerSection q d s) (L.nativePowerSection q m t)) := by
  apply atlasPowerGlobalCoefficients_heq L.atlas (Nat.mul_add q d m)
  intro i
  have hc (k : ℕ) (v : bundlePowerGlobalSections (L.tensorPower q).sheaf k) :
      atlasPowerGlobalCoefficients L.atlas (q * k) i (L.nativePowerSection q k v) =
        atlasPowerGlobalCoefficients (L.tensorPower q).atlas k i v :=
    L.nativePowerSection_coefficients q k i (L.atlas.opens i) (𝟙 _) v
  rw [atlasPowerGlobalMul_coefficients]
  rw [hc, hc, hc, atlasPowerGlobalMul_coefficients]

/-- The inverse genuine residue regrouping intertwines the actual twisted
section action with the original line-bundle section product. -/
theorem IntrinsicLineBundle.nativeResidueSection_action (d m r : ℕ)
    (s : bundlePowerGlobalSections (L.tensorPower q).sheaf d)
    (t : bundleTwistedGlobalSections (L.tensorPower q).sheaf (bundleTensorPower L.sheaf r) m) :
    HEq (L.nativeResidueSection q (d + m) r
      (atlasTwistedGlobalAction (L.tensorPower q).atlas (bundleTensorPower L.sheaf r) d m s t))
      (atlasPowerGlobalMul L.atlas (q * d) (q * m + r)
        (L.nativePowerSection q d s) (L.nativeResidueSection q m r t)) := by
  apply atlasPowerGlobalCoefficients_heq L.atlas (by simp [Nat.mul_add, Nat.add_assoc])
  intro i
  have hp (k : ℕ) (v : bundlePowerGlobalSections (L.tensorPower q).sheaf k) :
      atlasPowerGlobalCoefficients L.atlas (q * k) i (L.nativePowerSection q k v) =
        atlasPowerGlobalCoefficients (L.tensorPower q).atlas k i v :=
    L.nativePowerSection_coefficients q k i (L.atlas.opens i) (𝟙 _) v
  have hr (k : ℕ)
      (v : bundleTwistedGlobalSections (L.tensorPower q).sheaf (bundleTensorPower L.sheaf r) k) :
      atlasPowerGlobalCoefficients L.atlas (q * k + r) i (L.nativeResidueSection q k r v) =
      ((L.atlas.frame i).tensorPower r).coefficients (𝟙 _)
        (atlasTwistedGlobalCoefficients (L.tensorPower q).atlas
          (bundleTensorPower L.sheaf r) k i v) := by
    exact (L.nativeResidueSection_coefficients q k r i (L.atlas.opens i) (𝟙 _) v).trans
      (nativeTensorFrame_coefficients_eq_moduleCoefficients _ _ (𝟙 _) _)
  rw [atlasPowerGlobalMul_coefficients, hr, hp, hr, atlasTwistedGlobalAction_coefficients]
  exact LinearEquiv.map_smul _ _ _

/-- In the original section ring, a genuine twisted residue action is
multiplication by the actual power-section-ring image. -/
theorem IntrinsicLineBundle.nativeResidueSection_action_ofSection [IsIntegral X]
    (d m r : ℕ) (s : bundlePowerGlobalSections (L.tensorPower q).sheaf d)
    (t : bundleTwistedGlobalSections (L.tensorPower q).sheaf (bundleTensorPower L.sheaf r) m) :
    L.ofSection (q * (d + m) + r) (L.nativeResidueSection q (d + m) r
      (atlasTwistedGlobalAction (L.tensorPower q).atlas (bundleTensorPower L.sheaf r) d m s t)) =
    L.nativePowerSectionRingHom q ((L.tensorPower q).ofSection d s) *
      L.ofSection (q * m + r) (L.nativeResidueSection q m r t) := by
  rw [L.nativePowerSectionRingHom_ofSection, L.ofSection_mul]
  have hdeg : q * (d + m) + r = q * d + (q * m + r) := by
    rw [Nat.mul_add, Nat.add_assoc]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (Sigma.ext hdeg (L.nativeResidueSection_action q d m r s t))

end
end SGPT.Foundations.Schemes
