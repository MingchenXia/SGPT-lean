import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateAction
import SGPT.Foundations.Schemes.NativeProjectivePushforward

/-! # Genuine coordinate-power uniqueness of actual twisted sections

Actual frame transitions propagate restriction-zero to coordinate overlaps.
Native affine quasicoherent localization supplies actual ratio-power
annihilators; the finite coordinate cover supplies one common exponent.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual chart pullback of regular sections is the inverse native coordinate scheme map. -/
theorem polynomialProjChartTopRegular_pullback (j : Fin (n + 1)) :
    (polynomialProj K n).presheaf.map
      (eqToHom (polynomialProjCoordinateImmersion_image_top K n j)).op ≫
      ((polynomialProjCoordinateImmersion K n j).appIso ⊤).hom =
    (polynomialProjCoordinateOpen K n j).topIso.inv ≫
      (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide)).inv.appTop := by
  let U := polynomialProjCoordinateOpen K n j
  let e := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide)
  have htop : e.inv ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have heApp : U.toScheme.presheaf.map (eqToHom htop).op ≫
      (e.inv.appIso ⊤).hom = e.inv.appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    simp [Scheme.Hom.appLE]
  change _ ≫ ((e.inv ≫ U.ι).appIso ⊤).hom = U.topIso.inv ≫ e.inv.appTop
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_hom, Scheme.Opens.ι_appIso, Iso.refl_hom, Category.id_comp]
  rw [← heApp]
  change ((polynomialProj K n).presheaf.map _ ≫ (polynomialProj K n).presheaf.map _) ≫
      (e.inv.appIso ⊤).hom =
    ((polynomialProj K n).presheaf.map _ ≫ (polynomialProj K n).presheaf.map _) ≫
      (e.inv.appIso ⊤).hom
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 2

/-- The true affine-coordinate scalar map is the actual projective regular-section map. -/
theorem polynomialProjChartTopScalar_transport (j : Fin (n + 1)) :
    (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n j))).inv ≫
      ((polynomialProjCoordinateImmersion K n j).appIso ⊤).inv ≫
      (polynomialProj K n).presheaf.map
        (eqToHom (polynomialProjCoordinateImmersion_image_top K n j).symm).op =
    (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide)).hom := by
  let e := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide)
  let a := Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide)
  have hInv : e.inv.appTop = inv e.hom.appTop := by
    simpa using Scheme.Hom.inv_appTop e.hom
  have hfac : a.hom ≫ (polynomialProjCoordinateOpen K n j).topIso.inv ≫ e.inv.appTop =
      (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n j))).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n j))).hom).mp
    have hApp : e.hom.appTop =
        (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n j))).hom ≫
          a.hom ≫ (polynomialProjCoordinateOpen K n j).topIso.inv := by
      change (Proj.basicOpenToSpec _ _).app ⊤ = _ ≫ Proj.awayToSection _ _ ≫ _
      exact Proj.basicOpenToSpec_app_top _ _
    have hApp' := congrArg (fun q => q ≫ e.inv.appTop) hApp
    calc
      _ = e.hom.appTop ≫ e.inv.appTop := by simpa only [Category.assoc] using hApp'.symm
      _ = _ := by rw [hInv]; simp
  rw [← polynomialProjChartTopRegular_pullback K n j] at hfac
  rw [← hfac]
  simp [a]

/-- Actual overlap scalars are restrictions of the actual projective whole-chart fraction scalars. -/
theorem polynomialProjChartOverlapScalar_transport (j k : Fin (n + 1)) :
    affineCoordinateMap (.of (polynomialProjCoordinateRing K n j))
        (.op (PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j k))) ≫
      ((polynomialProjCoordinateImmersion K n j).appIso _).inv ≫
      (polynomialProj K n).presheaf.map
        (eqToHom (polynomialProjCoordinateImmersion_image_ratioOpen K n j k).symm).op =
    (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide)).hom ≫
      (polynomialProj K n).presheaf.map (homOfLE inf_le_left).op := by
  unfold affineCoordinateMap
  rw [Category.assoc, Scheme.Hom.appIso_inv_naturality_assoc]
  rw [← polynomialProjChartTopScalar_transport K n j]
  simp only [Category.assoc]
  congr 2

variable (M : (polynomialProj K n).Modules) (i : Fin (n + 1)) (d : ℕ)
  (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d)

/-- The true whole-chart section equivalence preserves actual coordinate scalar multiplication. -/
theorem polynomialProjChartTopSectionsIso_smul (j : Fin (n + 1))
    (r : polynomialProjCoordinateRing K n j) (s : Γ(polynomialProjModuleChart M j, ⊤)) :
    (polynomialProjChartTopSectionsIso M j).hom (r • s) =
      homogeneousPolynomialBasicOpenAwayEquiv j r •
        (polynomialProjChartTopSectionsIso M j).hom s := by
  have hs : r • s =
      (Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n j))).inv r • s := by
    change ((Spec (.of (polynomialProjCoordinateRing K n j))).presheaf.map (𝟙 (.op ⊤)))
      ((Scheme.ΓSpecIso (.of (polynomialProjCoordinateRing K n j))).inv r) • s = _
    rw [(Spec (.of (polynomialProjCoordinateRing K n j))).presheaf.map_id]
    rfl
  change M.presheaf.map (eqToHom (polynomialProjCoordinateImmersion_image_top K n j).symm).op
      ((M.restrictAppIso (polynomialProjCoordinateImmersion K n j) ⊤).hom (r • s)) = _
  rw [hs, Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.map_smul]
  congr 1
  exact congr($(polynomialProjChartTopScalar_transport K n j).hom r)

/-- The true chart equivalence sends every native scalar power to its actual regular-section power. -/
theorem polynomialProjChartTopSectionsIso_pow_smul (j : Fin (n + 1))
    (r : polynomialProjCoordinateRing K n j) (N : ℕ)
    (s : Γ(polynomialProjModuleChart M j, ⊤)) :
    (polynomialProjChartTopSectionsIso M j).hom (r ^ N • s) =
      (homogeneousPolynomialBasicOpenAwayEquiv j r) ^ N •
        (polynomialProjChartTopSectionsIso M j).hom s := by
  rw [polynomialProjChartTopSectionsIso_smul, map_pow]

/-- The actual overlap section identification preserves scalar multiplication by true restricted fractions. -/
theorem polynomialProjChartOverlapSectionsIso_smul (j k : Fin (n + 1))
    (r : polynomialProjCoordinateRing K n j)
    (s : Γ(polynomialProjModuleChart M j,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j k))) :
    (polynomialProjChartOverlapSectionsIso M j k).hom (r • s) =
      (polynomialProj K n).presheaf.map (homOfLE
        (show polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n k ≤
          polynomialProjCoordinateOpen K n j from inf_le_left)).op
        (homogeneousPolynomialBasicOpenAwayEquiv j r) •
        (polynomialProjChartOverlapSectionsIso M j k).hom s := by
  have hs : r • s = affineCoordinateMap (.of (polynomialProjCoordinateRing K n j))
      (.op (PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j k))) r • s := rfl
  change M.presheaf.map
      (eqToHom (polynomialProjCoordinateImmersion_image_ratioOpen K n j k).symm).op
      ((M.restrictAppIso (polynomialProjCoordinateImmersion K n j) _).hom (r • s)) = _
  rw [hs, Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.map_smul]
  congr 1
  exact congr($(polynomialProjChartOverlapScalar_transport K n j k).hom r)

/-- Native overlap power actions are powers of the true restricted homogeneous regular fractions. -/
theorem polynomialProjChartOverlapSectionsIso_pow_smul (j k : Fin (n + 1))
    (r : polynomialProjCoordinateRing K n j) (N : ℕ)
    (s : Γ(polynomialProjModuleChart M j,
      PrimeSpectrum.basicOpen (polynomialProjCoordinateRatio K n j k))) :
    (polynomialProjChartOverlapSectionsIso M j k).hom (r ^ N • s) =
      ((polynomialProj K n).presheaf.map (homOfLE
        (show polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n k ≤
          polynomialProjCoordinateOpen K n j from inf_le_left)).op
        (homogeneousPolynomialBasicOpenAwayEquiv j r)) ^ N •
        (polynomialProjChartOverlapSectionsIso M j k).hom s := by
  rw [polynomialProjChartOverlapSectionsIso_smul, map_pow, map_pow]

/-- True frame transitions propagate actual zero coefficients to every genuine coordinate overlap. -/
theorem polynomialTwistedGlobalCoefficients_overlap_zero
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0)
    (j : Fin (n + 1)) :
    M.val.map (homOfLE (show polynomialProjCoordinateOpen K n j ⊓
        polynomialProjCoordinateOpen K n i ≤ polynomialProjCoordinateOpen K n j from inf_le_left)).op
      (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t) = 0 := by
  have hh := LocalBundleFrame.twisted_global_coefficients_transition
    ((polynomialProjTwistingLine K n).atlas.frame i)
    ((polynomialProjTwistingLine K n).atlas.frame j) M
    (homOfLE (show polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n i ≤
      polynomialProjCoordinateOpen K n i from inf_le_right))
    (homOfLE (show polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n i ≤
      polynomialProjCoordinateOpen K n j from inf_le_left)) d t
  change M.val.map _ (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t) =
    _ • M.val.map _ (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t) at hh
  rw [h, map_zero, smul_zero] at hh
  exact hh

/-- The literal affine chart coefficient vanishes under the true principal-ratio overlap restriction. -/
theorem polynomialTwistedGlobalChartCoefficients_overlap_zero
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0)
    (j : Fin (n + 1)) :
    polynomialProjChartOverlapRestriction M j i
      ((polynomialProjChartTopSectionsIso M j).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t)) = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (polynomialProjChartOverlapSectionsIso M j i).hom).injective
  rw [map_zero, polynomialProjChartOverlapRestriction_actual]
  rw [Iso.inv_hom_id_apply]
  have hh := polynomialTwistedGlobalCoefficients_overlap_zero K n M i d t h j
  exact hh

/-- True affine quasicoherent localization gives an actual chart ratio-power annihilator. -/
theorem polynomialTwistedGlobalChartCoefficients_annihilator
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0)
    (j : Fin (n + 1)) [(polynomialProjModuleChart M j).IsQuasicoherent] :
    ∃ N : ℕ, polynomialProjCoordinateRatio K n j i ^ N •
      ((polynomialProjChartTopSectionsIso M j).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t)) = 0 :=
  affineSection_zero_after_power (polynomialProjModuleChart M j)
    (polynomialProjCoordinateRatio K n j i)
    (polynomialTwistedGlobalChartCoefficients_overlap_zero K n M i d t h j)

/-- The actual finite coordinate cover yields one common ratio-power chart annihilator. -/
theorem polynomialTwistedGlobalChartCoefficients_uniformAnnihilator
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent]
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0) :
    ∃ N : ℕ, ∀ j : Fin (n + 1), polynomialProjCoordinateRatio K n j i ^ N •
      ((polynomialProjChartTopSectionsIso M j).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t)) = 0 := by
  classical
  choose N hN using fun j => polynomialTwistedGlobalChartCoefficients_annihilator K n M i d t h j
  let B := Finset.univ.sup N
  refine ⟨B, fun j => ?_⟩
  have hj : N j ≤ B := Finset.le_sup (Finset.mem_univ j)
  rw [show B = (B - N j) + N j by omega, pow_add, mul_smul, hN j, smul_zero]

/-- A common native chart annihilator is a common actual projective ratio annihilator. -/
theorem polynomialTwistedGlobalCoefficients_uniformAnnihilator
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent]
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0) :
    ∃ N : ℕ, ∀ j : Fin (n + 1),
      (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i)) ^ N •
        atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d j t = 0 := by
  obtain ⟨N, hN⟩ := polynomialTwistedGlobalChartCoefficients_uniformAnnihilator K n M i d t h
  refine ⟨N, fun j => ?_⟩
  have hj := congrArg (polynomialProjChartTopSectionsIso M j).hom (hN j)
  rw [polynomialProjChartTopSectionsIso_pow_smul, map_zero, Iso.inv_hom_id_apply] at hj
  exact hj

/-- Genuine sheaf separation turns local ratio annihilation into actual global coordinate-power zero. -/
theorem polynomialTwistedGlobalCoordinatePowerAction_zero
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent]
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0) :
    ∃ N : ℕ, atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas M N d
      (polynomialProjTwistedGlobalCoordinatePower K n i N) t = 0 := by
  obtain ⟨N, hN⟩ := polynomialTwistedGlobalCoefficients_uniformAnnihilator K n M i d t h
  refine ⟨N, atlasTwistedGlobalCoefficients_ext (polynomialProjTwistingLine K n).atlas M
    (N + d) _ 0 (fun j => ?_)⟩
  rw [polynomialProjTwistedCoordinatePowerAction_coefficients, atlasTwistedGlobalCoefficients_zero]
  exact hN j

/-- Actual vanishing on one coordinate chart makes a coordinate power kill the literal Γ-star element. -/
theorem polynomialTwistedSection_X_pow_zero
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent]
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = 0) :
    ∃ N : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ N •
      (polynomialProjTwistingLine K n).ofTwistedSection M d t = 0 := by
  obtain ⟨N, hN⟩ := polynomialTwistedGlobalCoordinatePowerAction_zero K n M i d t h
  refine ⟨N, ?_⟩
  rw [polynomialProjTwistedSectionModule_X_pow_smul, hN, map_zero]

/-- True equal chart coefficients become equal after an actual coordinate power in the native Γ-star module. -/
theorem polynomialTwistedSection_eq_after_X_pow
    [∀ j : Fin (n + 1), (polynomialProjModuleChart M j).IsQuasicoherent]
    (s : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d)
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i s =
      atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t) :
    ∃ N : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ N •
        (polynomialProjTwistingLine K n).ofTwistedSection M d s =
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ N •
        (polynomialProjTwistingLine K n).ofTwistedSection M d t := by
  have hz : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i (s - t) = 0 := by
    unfold atlasTwistedGlobalCoefficients
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨N, hN⟩ := polynomialTwistedSection_X_pow_zero K n M i d (s - t) hz
  refine ⟨N, sub_eq_zero.mp ?_⟩
  simpa only [map_sub, smul_sub] using hN

variable {K n}

/-- True closed-projective line geometry supplies every localization input to actual coordinate-power uniqueness. -/
theorem closedPolynomialProjPushforwardTwistedSection_X_pow_zero
    {X : Scheme} (f : X ⟶ polynomialProj K n) [IsClosedImmersion f]
    {L : X.Modules} (a : LineBundleAtlas L) (i : Fin (n + 1)) (d : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj L) d)
    (h : atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
      ((Scheme.Modules.pushforward f).obj L) d i t = 0) :
    ∃ N : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ N •
      (polynomialProjTwistingLine K n).ofTwistedSection ((Scheme.Modules.pushforward f).obj L) d t = 0 := by
  let : ∀ j : Fin (n + 1),
      (polynomialProjModuleChart ((Scheme.Modules.pushforward f).obj L) j).IsQuasicoherent :=
    fun j => polynomialProjPushforwardChart_isQuasicoherent f a j
  exact polynomialTwistedSection_X_pow_zero K n ((Scheme.Modules.pushforward f).obj L) i d t h

end

end SGPT.Foundations.Schemes
