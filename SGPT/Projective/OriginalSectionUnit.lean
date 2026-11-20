import SGPT.Foundations.Schemes.NativeTensorPowerIsoFrames
import SGPT.Foundations.Schemes.LineSectionZeroSubscheme

/-! Literal original Γ(L) to Γ(L^1) through the ACTUAL tensor left unit,
including every frame coefficient and ENTIRE original zero ideal/scheme.
Blueprint: original-section-unit.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite
variable {X : Scheme.{0}} {L : X.Modules}

/-- Actual original inverse tensor left-unit map on the original section. -/
def originalSectionUnit (s : Γ(L, ⊤)) : bundlePowerGlobalSections L 1 :=
  (bundleTensorLeftUnitIso L).inv.val.app (.op ⊤) s

/-- Literal original cancellation, not an identification of degree-one sheaves. -/
theorem originalSectionUnit_hom (s : Γ(L, ⊤)) :
    (bundleTensorLeftUnitIso L).hom.val.app (.op ⊤) (originalSectionUnit s) = s := by
  exact congr($( (bundleTensorLeftUnitIso L).inv_hom_id).val.app (.op ⊤) |>.hom s)

/-- True inverse left-unit transport preserves nonzero original sections. -/
theorem originalSectionUnit_ne_zero_iff (s : Γ(L, ⊤)) : originalSectionUnit s ≠ 0 ↔ s ≠ 0 := by
  constructor
  · intro hs hzero
    apply hs
    simp only [originalSectionUnit, hzero, map_zero]
  · intro hs hz
    apply hs
    have h := originalSectionUnit_hom s
    simpa only [hz, map_zero] using h.symm

private theorem originalLeftUnit_coefficients {U V : X.Opens}
    (b : LocalBundleFrame L U) (h : V ⟶ U) (t : bundleSections (bundleTensorPower L 1) V) :
    b.coefficients h ((bundleTensorLeftUnitIso L).hom.val.app (.op V) t) =
      (b.tensorPower 1).coefficients h t := by
  have ht := nativeTensorFrame_reconstruct (b.tensorPower 0) b h t
  conv_lhs => rw [← ht]
  change b.coefficients h ((bundleTensorLeftUnitIso L).hom.val.app (.op V)
    (tensorSection (SheafOfModules.unit X.ringCatSheaf) L V (1 : Γ(X, V))
      ((b.coefficients h).symm ((b.tensorPower 1).coefficients h t)))) = _
  rw [nativeBundleTensorLeftUnitIso_tensorSection, one_smul, LinearEquiv.apply_symm_apply]

/-- Every original actual subordinate frame coefficient is preserved. -/
theorem originalSectionUnit_coefficients (s : Γ(L, ⊤)) {U V : X.Opens}
    (b : LocalBundleFrame L U) (h : V ⟶ U) :
    (b.tensorPower 1).coefficients h
      ((bundleTensorPower L 1).val.map V.leTop.op (originalSectionUnit s)) =
      b.coefficients h (L.val.map V.leTop.op s) := by
  rw [← originalLeftUnit_coefficients b h]
  have hn := PresheafOfModules.naturality_apply (bundleTensorLeftUnitIso L).hom.val
    V.leTop.op (originalSectionUnit s)
  have hh : (bundleTensorLeftUnitIso L).hom.val.app (.op V)
      ((bundleTensorPower L 1).val.map V.leTop.op (originalSectionUnit s)) =
      L.val.map V.leTop.op s := hn.trans (congrArg (fun t => L.val.map V.leTop.op t)
        (originalSectionUnit_hom s))
  exact congrArg (b.coefficients h) hh

/-- Actual entire original ideal sheaf equality, proved on a genuine affine frame cover. -/
theorem originalSectionUnit_zeroIdeal (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    sectionZeroIdealSheaf (a.tensorPower 1) (originalSectionUnit s) = sectionZeroIdealSheaf a s := by
  classical
  let I := Σ i : a.I, {V : X.Opens // IsAffineOpen V ∧ V ≤ a.opens i}
  let U (i : I) : X.affineOpens := ⟨i.2.val, i.2.property.1⟩
  have hcover : ⨆ i, (U i).1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨V, hV, hxV, hVi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV, hVi⟩⟩, hxV⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro i
  change sectionZeroIdeal (bundleTensorPower L 1) (originalSectionUnit s) i.2.val =
    sectionZeroIdeal L s i.2.val
  rw [sectionZeroIdeal_eq_span_frame (L := bundleTensorPower L 1) (originalSectionUnit s) ((a.frame i.1).tensorPower 1)
      (homOfLE i.2.property.2),
    sectionZeroIdeal_eq_span_frame s (a.frame i.1) (homOfLE i.2.property.2)]
  exact congrArg (fun r : Γ(X, i.2.val) => Ideal.span {r})
    (originalSectionUnit_coefficients s (a.frame i.1) (homOfLE i.2.property.2))

/-- Actual entire zero schemes are isomorphic, retaining all original nilpotent structure. -/
def originalSectionUnit_zeroSchemeIso (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    sectionZeroSubscheme (a.tensorPower 1) (originalSectionUnit s) ≅ sectionZeroSubscheme a s :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (originalSectionUnit_zeroIdeal a s))

private theorem subscheme_eqToIso_ι {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
  cases h
  simp

/-- Literal original inclusion square for the actual entire scheme isomorphism. -/
theorem originalSectionUnit_zeroSchemeIso_ι (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    (originalSectionUnit_zeroSchemeIso a s).hom ≫ sectionZeroι a s =
      sectionZeroι (a.tensorPower 1) (originalSectionUnit s) :=
  subscheme_eqToIso_ι (originalSectionUnit_zeroIdeal a s)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
