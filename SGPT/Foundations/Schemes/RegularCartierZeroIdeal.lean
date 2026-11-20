import SGPT.Foundations.Schemes.NativeRegularProjectiveFlag

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The standard geometric local condition on the ACTUAL quasicoherent
ideal: actual affine neighborhoods with actual regular principal equations. -/
def IsEffectiveCartierIdeal {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
    ∃ t : Γ(X, U), t ∈ nonZeroDivisors Γ(X, U) ∧ I.ideal U = Ideal.span {t}

/-- Literal actual dual evaluation identifies the true zero ideal module
with the actual dual line on every genuinely regular framed affine open. -/
def sectionZeroIdealDualEquiv {X : Scheme.{u}} {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (U : X.affineOpens)
    {W : X.Opens} (e : LocalBundleFrame L W) (i : U.val ⟶ W)
    (hr : e.coefficients i (L.presheaf.map U.val.leTop.op s) ∈ nonZeroDivisors Γ(X, U)) :
    Γ(bundleDual L, U) ≃ₗ[Γ(X, U)] (sectionZeroIdealSheaf a s).ideal U := by
  let E := (sectionZeroEvaluation L s U).rangeRestrict
  apply LinearEquiv.ofBijective E
  constructor
  · intro α β h
    apply (e.dual.coefficients i).injective
    have he := congrArg Subtype.val h
    change sectionZeroEvaluation L s U α = sectionZeroEvaluation L s U β at he
    rw [sectionZeroEvaluation_frame s e i, sectionZeroEvaluation_frame s e i] at he
    exact (mul_cancel_left_mem_nonZeroDivisors hr).mp he
  · intro r
    obtain ⟨α, hα⟩ := r.property
    exact ⟨α, Subtype.ext hα⟩

/-- The equivalence's forward map is LITERALLY the original evaluation. -/
theorem sectionZeroIdealDualEquiv_apply {X : Scheme.{u}} {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (U : X.affineOpens)
    {W : X.Opens} (e : LocalBundleFrame L W) (i : U.val ⟶ W)
    (hr : e.coefficients i (L.presheaf.map U.val.leTop.op s) ∈ nonZeroDivisors Γ(X, U))
    (α : Γ(bundleDual L, U)) :
    (sectionZeroIdealDualEquiv a s U e i hr α : Γ(X, U)) = sectionZeroEvaluation L s U α := rfl

/-- Actual ideal/dual-line equivalences commute with the ORIGINAL actual
restriction maps on genuinely regular framed affine opens. -/
theorem sectionZeroIdealDualEquiv_restrict {X : Scheme.{u}} {L : X.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (U V : X.affineOpens) (h : V.val ≤ U.val)
    {WU WV : X.Opens} (eU : LocalBundleFrame L WU) (eV : LocalBundleFrame L WV)
    (iU : U.val ⟶ WU) (iV : V.val ⟶ WV)
    (hrU : eU.coefficients iU (L.presheaf.map U.val.leTop.op s) ∈ nonZeroDivisors Γ(X, U))
    (hrV : eV.coefficients iV (L.presheaf.map V.val.leTop.op s) ∈ nonZeroDivisors Γ(X, V))
    (α : Γ(bundleDual L, U)) :
    (sectionZeroIdealDualEquiv a s V eV iV hrV
      ((bundleDual L).presheaf.map (homOfLE h).op α) : Γ(X, V)) =
      X.presheaf.map (homOfLE h).op
        (sectionZeroIdealDualEquiv a s U eU iU hrU α : Γ(X, U)) :=
  sectionZeroEvaluation_restrict L s h α

/-- Genuine original coordinates and produced nonzerodivisors give ACTUAL
regular principal affine equations for the SAME original zero ideal sheaf. -/
theorem nativePositiveProjectiveSectionZero_isEffectiveCartierIdeal
    (K : Type) [Field K] (N : ℕ) {X : Scheme} (f : X ⟶ polynomialProj K N)
    [IsAffineHom f] (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)
    (s : bundlePowerGlobalSections L.sheaf q)
    (hr : nativePositiveProjectiveSectionRegular K N f L q e s) :
    IsEffectiveCartierIdeal (sectionZeroIdealSheaf (L.atlas.tensorPower q) s) := by
  classical
  intro x
  have hx : x ∈ iSup (actualPolynomialProjectivePullbackCoordinateOpens f) := by
    rw [actualPolynomialProjectivePullbackCoordinateOpens_covers]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  let S : Finset (Fin (N + 1)) := {j}
  have hS : S.Nonempty := Finset.singleton_nonempty j
  let W := actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) S
  let U : X.affineOpens :=
    ⟨W, actualPolynomialProjectivePullbackSubsetOpen_isAffine K N f S hS⟩
  let E := nativePositiveProjectiveCoordinateFrame K N f L q e hS.choose
  let i : U.val ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K N hS.choose :=
    homOfLE (Finset.inf_le hS.choose_spec)
  refine ⟨U, ?_, E.coefficients i ((bundleTensorPower L.sheaf q).presheaf.map W.leTop.op s),
    hr S hS, ?_⟩
  · simpa only [U, W, S, actualSchemeSubsetOpen, Finset.inf_singleton] using hj
  · exact sectionZeroIdeal_eq_span_frame s E i

/-- EVERY actual chosen native cut has its SAME actual effective Cartier
ideal, including empty and nonreduced later strata, with no value certificate. -/
theorem NativeClosedProjectiveStratum.cut_isEffectiveCartierIdeal {N : ℕ}
    (T : NativeClosedProjectiveStratum N) :
    IsEffectiveCartierIdeal (sectionZeroIdealSheaf
      ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1) T.cutSection) := by
  let : IsClosedImmersion T.val.hom := T.property
  exact nativePositiveProjectiveSectionZero_isEffectiveCartierIdeal ℂ N T.val.hom
    (nativeProjectivePositiveLine ℂ N T.val.hom) 1
    (nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom) T.cutSection T.cutSection_regular

end
end SGPT.Foundations.Schemes
