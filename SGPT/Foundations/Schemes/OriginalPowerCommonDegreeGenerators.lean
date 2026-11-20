import SGPT.Foundations.Schemes.NativePositiveResidueCoefficients
import SGPT.Foundations.Schemes.PolynomialCommonDegreeGenerators

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Surjective additive semilinear maps send spanning families to spanning
families over the ACTUAL target ring. The scalar hom need not be surjective. -/
theorem span_range_eq_top_of_semilinear_surjective
    {R S : Type*} [Semiring R] [Semiring S]
    {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
    (φ : R →+* S) (F : M →+ N) (hF : Function.Surjective F)
    (hsmul : ∀ (r : R) (m : M), F (r • m) = φ r • F m)
    {I : Type*} (v : I → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span S (Set.range (fun i ↦ F (v i))) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨y, rfl⟩ := hF z
  have hy : y ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
  refine Submodule.span_induction (p := fun x _ ↦
    F x ∈ Submodule.span S (Set.range (fun i ↦ F (v i)))) ?_ ?_ ?_ ?_ hy
  · rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · simpa only [map_zero] using (Submodule.span S (Set.range (fun i ↦ F (v i)))).zero_mem
  · intro x y hx hy ihx ihy
    simpa only [map_add] using (Submodule.span S (Set.range (fun i ↦ F (v i)))).add_mem ihx ihy
  · intro a x hx ih
    rw [hsmul]
    exact (Submodule.span S (Set.range (fun i ↦ F (v i)))).smul_mem (φ a) ih

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (f : X ⟶ polynomialProj K n)

/-- The ACTUAL chart isomorphism and original structural scalar map take
native chart spans to full residual-section spans over the ORIGINAL chart
ring. No scalar surjectivity or replacement of the ring action is needed. -/
theorem polynomialProjTwistedCoefficient_span_originalRing (M : X.Modules) (d : ℕ)
    {I : Type} (t : I → bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj M) d) (i : Fin (n + 1))
    (ht : Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun b ↦ (polynomialProjChartTopSectionsIso ((Scheme.Modules.pushforward f).obj M) i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
          ((Scheme.Modules.pushforward f).obj M) d i (t b)))) = ⊤) :
    Submodule.span Γ(X, f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)
      (Set.range (fun b ↦ (show bundleSections M (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) from
        atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
          ((Scheme.Modules.pushforward f).obj M) d i (t b)))) = ⊤ := by
  let U := polynomialProjCoordinateOpen K n i
  let V := f ⁻¹ᵁ U
  let E := polynomialProjChartTopSectionsIso ((Scheme.Modules.pushforward f).obj M) i
  let φ : polynomialProjCoordinateRing K n i →+* Γ(X, V) :=
    (f.app U).hom.comp (homogeneousPolynomialBasicOpenAwayEquiv i).toRingHom
  let F : Γ(polynomialProjModuleChart ((Scheme.Modules.pushforward f).obj M) i, ⊤) →+
      bundleSections M V := E.hom.hom
  have hf : Function.Surjective F := (ConcreteCategory.bijective_of_isIso E.hom).surjective
  have hs (a : polynomialProjCoordinateRing K n i)
      (s : Γ(polynomialProjModuleChart ((Scheme.Modules.pushforward f).obj M) i, ⊤)) :
      F (a • s) = φ a • F s := by
    exact polynomialProjChartTopSectionsIso_smul K n ((Scheme.Modules.pushforward f).obj M) i a s
  have hsp := span_range_eq_top_of_semilinear_surjective φ F hf hs
    (fun b ↦ E.inv (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
      ((Scheme.Modules.pushforward f).obj M) d i (t b))) ht
  have hfun : (fun b ↦ F (E.inv (atlasTwistedGlobalCoefficients
      (polynomialProjTwistingLine K n).atlas ((Scheme.Modules.pushforward f).obj M) d i (t b)))) =
      (fun b ↦ (show bundleSections M V from atlasTwistedGlobalCoefficients
        (polynomialProjTwistingLine K n).atlas ((Scheme.Modules.pushforward f).obj M) d i (t b))) := by
    funext b
    exact Iso.inv_hom_id_apply E _
  rw [hfun] at hsp
  exact hsp

variable (L : IntrinsicLineBundle X) (q : ℕ)
  (e : bundleTensorPower L.sheaf q ≅
    (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The SAME existing residue inverse takes genuine common-degree twisted
chart spans to full spans of ORIGINAL L^(q*m+r) sections on the SAME chart,
over the ACTUAL original chart ring and with its original module action. -/
theorem nativePolarizedInverse_originalPower_chart_span (m r : ℕ)
    {I : Type} (t : I → bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m)
    (i : Fin (n + 1))
    (ht : Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun b ↦ (polynomialProjChartTopSectionsIso
        ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) i).inv
          (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
            ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m i (t b)))) = ⊤) :
    Submodule.span Γ(X, f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)
      (Set.range (fun b ↦ (bundleTensorPower L.sheaf (q * m + r)).val.map
        (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i).leTop.op
        ((nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r).inv.val.app (.op ⊤) (t b)))) = ⊤ := by
  let V := f ⁻¹ᵁ polynomialProjCoordinateOpen K n i
  let M := bundleTensorPower L.sheaf r
  let Q := bundleTensorPower L.sheaf (q * m + r)
  let A := nativeLineTensorPowerAddIso L.atlas (q * m) r
  let E0 := (SheafOfModules.evaluation (R := X.ringCatSheaf) (.op V)).mapIso A
  let E1 : bundleSections Q V ≃ₗ[Γ(X, V)]
      bundleSections (bundleTensor (bundleTensorPower L.sheaf (q * m)) M) V := E0.toLinearEquiv
  let E2 : bundleSections (bundleTensor (bundleTensorPower L.sheaf (q * m)) M) V ≃ₗ[Γ(X, V)]
      bundleSections M V :=
    (nativePositiveProjectivePowerFrame K n f L q e m i).tensorModuleCoefficients M (𝟙 V)
  let J : bundleSections Q V ≃ₗ[Γ(X, V)] bundleSections M V := E1.trans E2
  let c (b : I) : bundleSections M V :=
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
      ((Scheme.Modules.pushforward f).obj M) m i (t b)
  let v (b : I) : bundleSections Q V := Q.val.map V.leTop.op
    ((nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r).inv.val.app (.op ⊤) (t b))
  have hres : Submodule.span Γ(X, V) (Set.range c) = ⊤ :=
    polynomialProjTwistedCoefficient_span_originalRing K n f M m t i ht
  have hsp := span_range_eq_top_of_semilinear_surjective (RingHom.id Γ(X, V))
    J.symm.toLinearMap.toAddMonoidHom J.symm.surjective (fun a x ↦ J.symm.map_smul a x) c hres
  have hc (b : I) : J (v b) = c b :=
    nativePolarizedResidueTensorTwist_inv_globalCoefficients K n f L q e m r i (t b)
  have hfun : (fun b ↦ J.symm (c b)) = v := by
    funext b
    apply J.injective
    rw [J.apply_symm_apply]
    exact (hc b).symm
  change Submodule.span Γ(X, V) (Set.range (fun b ↦ J.symm (c b))) = ⊤ at hsp
  rw [hfun] at hsp
  exact hsp

/-- Actual closed-projective line geometry PRODUCES a finite index and one
bound for ORIGINAL full-ring sections in every degree q*D+r above that bound.
Their restrictions span every original chart over its ACTUAL original ring. -/
theorem nativePositiveProjective_exists_commonDegree_originalPower_chart_generators
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)
    [IsClosedImmersion f] (r : ℕ) :
    ∃ (m : Fin (n + 1) → ℕ) (B : ℕ), ∀ D : ℕ, B ≤ D →
      ∃ s : (Σ j : Fin (n + 1), Fin (m j)) → bundlePowerGlobalSections L.sheaf (q * D + r),
        ∀ i, Submodule.span Γ(X, f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)
          (Set.range (fun b ↦ (bundleTensorPower L.sheaf (q * D + r)).val.map
            (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i).leTop.op (s b))) = ⊤ := by
  obtain ⟨m, B, h⟩ := closedPolynomialProjPushforward_exists_commonDegree_chart_generators
    K n f (L.atlas.tensorPower r)
  refine ⟨m, B, fun D hD ↦ ?_⟩
  obtain ⟨t, ht⟩ := h D hD
  refine ⟨fun b ↦ (nativePolarizedResiduePushforwardTensorTwistIso L n f q e D r).inv.val.app
    (.op ⊤) (t b), fun i ↦ ?_⟩
  exact nativePolarizedInverse_originalPower_chart_span K n f L q e D r t i (ht i)

/-- Actual Fano geometry produces SAME-bound common-degree chart-generating
families in the ORIGINAL anticanonical powers, for every residual r. -/
theorem SmoothProjectiveFano.nativeAnticanonical_commonDegree_chart_generators {a : ℕ}
    (F : SmoothProjectiveFano a) (r : ℕ) :
    ∃ (m : Fin (F.projective.ambientDimension + 1) → ℕ) (B : ℕ), ∀ D : ℕ, B ≤ D →
      ∃ s : (Σ j : Fin (F.projective.ambientDimension + 1), Fin (m j)) →
        bundlePowerGlobalSections (anticanonicalLineSheaf F.structureMap a) (F.anticanonicalPower * D + r),
        ∀ i, Submodule.span Γ(F.scheme,
          F.projective.map ⁻¹ᵁ polynomialProjCoordinateOpen ℂ F.projective.ambientDimension i)
          (Set.range (fun b ↦ (bundleTensorPower (anticanonicalLineSheaf F.structureMap a)
            (F.anticanonicalPower * D + r)).val.map
              (F.projective.map ⁻¹ᵁ polynomialProjCoordinateOpen ℂ F.projective.ambientDimension i).leTop.op
                (s b))) = ⊤ :=
  nativePositiveProjective_exists_commonDegree_originalPower_chart_generators ℂ
    F.projective.ambientDimension F.projective.map (smoothAnticanonicalLineBundle F.structureMap a)
    F.anticanonicalPower F.positivityIso r

end
end SGPT.Foundations.Schemes
