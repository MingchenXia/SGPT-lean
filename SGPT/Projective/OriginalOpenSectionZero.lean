import SGPT.Projective.OriginalPullbackFrameTransition
import SGPT.Foundations.Schemes.LineSectionZeroSubscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! SAME actual original ordinary pulled section and ENTIRE open zero-scheme
base change. Blueprint: original-open-section-zero.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory Limits AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
variable {X Y : Scheme.{0}} {L : Y.Modules}

/-- Actual original global section pullback, through the original adjunction unit. -/
def originalPulledSection (f : X ⟶ Y) (s : Γ(L, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj L, ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op ⊤)) s

/-- EVERY original inverse-open physical regular coefficient, without readback input. -/
theorem originalPulledSection_coefficients (f : X ⟶ Y) (s : Γ(L, ⊤))
    {U V : Y.Opens} (b : LocalBundleFrame L U) (j : V ⟶ U) :
    (matePullbackFrame f b).coefficients ((Opens.map f.base).map j)
      (((Scheme.Modules.pullback f).obj L).val.map (f ⁻¹ᵁ V).leTop.op (originalPulledSection f s)) =
      f.app V (b.coefficients j (L.val.map V.leTop.op s)) := by
  have hn := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val V.leTop.op s
  have he : (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op V))
      (L.val.map V.leTop.op s) =
      ((Scheme.Modules.pullback f).obj L).val.map (f ⁻¹ᵁ V).leTop.op (originalPulledSection f s) := hn
  rw [← he]
  exact matePullbackFrame_coefficient_simple f b j _

/-- The actual coefficient reader on ANY actual source-open subordinate open. -/
theorem originalOpenPulledSection_coefficients {U : Y.Opens} (s : Γ(L, ⊤))
    {V : Y.Opens} (b : LocalBundleFrame L V) (W : U.toScheme.Opens) (j : W ⟶ U.ι ⁻¹ᵁ V) :
    (matePullbackFrame U.ι b).coefficients j
      (((Scheme.Modules.pullback U.ι).obj L).val.map W.leTop.op (originalPulledSection U.ι s)) =
      b.coefficients (homOfLE (show U.ι ''ᵁ W ≤ V from by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact (leOfHom j) hy))
        (L.val.map (U.ι ''ᵁ W).leTop.op s) := by
  have h := originalPulledSection_coefficients U.ι s b
    (homOfLE (show U.ι ''ᵁ W ≤ V from by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (leOfHom j) hy))
  have hW : U.ι ⁻¹ᵁ (U.ι ''ᵁ W) = W := U.ι.preimage_image_eq W
  let k : W ⟶ U.ι ⁻¹ᵁ (U.ι ''ᵁ W) := eqToHom hW.symm
  let P := (Scheme.Modules.pullback U.ι).obj L
  have hr := (matePullbackFrame U.ι b).coefficients_restrict
    ((Opens.map U.ι.base).map (homOfLE (show U.ι ''ᵁ W ≤ V from by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (leOfHom j) hy))) k
    (P.val.map (U.ι ⁻¹ᵁ (U.ι ''ᵁ W)).leTop.op (originalPulledSection U.ι s))
  have hres : P.val.map k.op
      (P.val.map (U.ι ⁻¹ᵁ (U.ι ''ᵁ W)).leTop.op (originalPulledSection U.ι s)) =
      P.val.map W.leTop.op (originalPulledSection U.ι s) := by
    rw [← P.val.map_comp_apply]
    rfl
  rw [hres] at hr
  change (matePullbackFrame U.ι b).coefficients j _ =
    U.toScheme.presheaf.map k.op _ at hr
  refine hr.trans ((congrArg (U.toScheme.presheaf.map k.op) h).trans ?_)
  have he := congrArg (fun q => q
    (b.coefficients (homOfLE (show U.ι ''ᵁ W ≤ V from by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (leOfHom j) hy)) (L.val.map (U.ι ''ᵁ W).leTop.op s)))
    (U.ι.appIso_hom' W)
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom] at he
  exact he.symm

/-- ACTUAL entire original pulled zero ideal equals genuine original ideal-sheaf base change. -/
theorem originalOpenSection_zeroIdeal (U : Y.Opens) (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    sectionZeroIdealSheaf (matePullbackAtlas U.ι a) (originalPulledSection U.ι s) =
      (sectionZeroIdealSheaf a s).comap U.ι := by
  classical
  let I := Σ i : a.I, {W : U.toScheme.Opens // IsAffineOpen W ∧ W ≤ U.ι ⁻¹ᵁ a.opens i}
  let W (i : I) : U.toScheme.affineOpens := ⟨i.2.val, i.2.property.1⟩
  have hcover : ⨆ i, (W i).1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := a.covers (U.ι x)
    obtain ⟨V, hV, hxV, hVi⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ U.ι ⁻¹ᵁ a.opens i from hi)
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV, hVi⟩⟩, hxV⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top W hcover
  intro i
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
  change sectionZeroIdeal ((Scheme.Modules.pullback U.ι).obj L)
      (originalPulledSection U.ι s) i.2.val =
    (sectionZeroIdeal L s (U.ι ''ᵁ i.2.val)).comap (RingHom.id _)
  rw [Ideal.comap_id]
  rw [sectionZeroIdeal_eq_span_frame (L := (Scheme.Modules.pullback U.ι).obj L)
      (originalPulledSection U.ι s) (matePullbackFrame U.ι (a.frame i.1))
      (homOfLE i.2.property.2),
    sectionZeroIdeal_eq_span_frame s (a.frame i.1) (homOfLE (show U.ι ''ᵁ i.2.val ≤ a.opens i.1 from by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact i.2.property.2 hy))]
  exact congrArg (fun r : Γ(U.toScheme, i.2.val) => Ideal.span {r})
    (originalOpenPulledSection_coefficients s (a.frame i.1) i.2.val (homOfLE i.2.property.2))

/-- ENTIRE original pulled-section zero scheme is the ACTUAL original inverse-image open zero scheme. -/
def originalOpenSection_zeroSchemeIso (U : Y.Opens) (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    sectionZeroSubscheme (matePullbackAtlas U.ι a) (originalPulledSection U.ι s) ≅
      sectionZeroι a s ⁻¹ᵁ U :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (originalOpenSection_zeroIdeal U a s)) ≪≫
    (sectionZeroIdealSheaf a s).comapIso U.ι ≪≫
      pullbackSymmetry U.ι (sectionZeroι a s) ≪≫ pullbackRestrictIsoRestrict (sectionZeroι a s) U

/-- Actual original zero-scheme isomorphism retains its literal original immersion square. -/
theorem originalOpenSection_zeroSchemeIso_ι (U : Y.Opens) (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    (originalOpenSection_zeroSchemeIso U a s).hom ≫ (sectionZeroι a s ⁻¹ᵁ U).ι ≫ sectionZeroι a s =
      sectionZeroι (matePullbackAtlas U.ι a) (originalPulledSection U.ι s) ≫ U.ι := by
  have he {I J : U.toScheme.IdealSheafData} (h : I = J) :
      (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
    cases h
    simp
  simp only [originalOpenSection_zeroSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullbackSymmetry_hom_comp_fst_assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    ← Category.assoc, he]
  exact originalOpenSection_zeroIdeal U a s

end SGPT.Projective.NumEq.AlgebraicCurveDegree
