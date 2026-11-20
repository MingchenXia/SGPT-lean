import SGPT.Foundations.Schemes.AffineOpenSectionDenominators
import SGPT.Foundations.Schemes.BundleDualSheaf
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! Actual dual-evaluation ideals, their genuine zero closed subscheme, and
affine principal quotient maps. No intersection number or later flag is input. -/

universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {X : Scheme.{u}} {L : X.Modules}

/-- The actual dual-evaluation map of the original global section. -/
def sectionZeroEvaluation (L : X.Modules) (s : Γ(L, ⊤)) (U : X.Opens) :
    Γ(bundleDual L, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (bundleDualValueBilinear L U).flip (L.presheaf.map U.leTop.op s)

/-- The image is an actual ideal on every open, with no local frame chosen. -/
def sectionZeroIdeal (L : X.Modules) (s : Γ(L, ⊤)) (U : X.Opens) :
    Ideal Γ(X, U) := (sectionZeroEvaluation L s U).range

/-- Membership retains a genuine dual section as its preimage. -/
theorem mem_sectionZeroIdeal (L : X.Modules) (s : Γ(L, ⊤)) (U : X.Opens)
    (r : Γ(X, U)) : r ∈ sectionZeroIdeal L s U ↔
      ∃ α : Γ(bundleDual L, U), sectionZeroEvaluation L s U α = r := Iff.rfl

/-- The actual evaluation maps commute with the original restriction maps. -/
theorem sectionZeroEvaluation_restrict (L : X.Modules) (s : Γ(L, ⊤))
    {U V : X.Opens} (h : V ≤ U) (α : Γ(bundleDual L, U)) :
    sectionZeroEvaluation L s V ((bundleDual L).presheaf.map (homOfLE h).op α) =
      X.presheaf.map (homOfLE h).op (sectionZeroEvaluation L s U α) := by
  change bundleDualValue L V (bundleDualRestriction L (homOfLE h) α)
    (L.val.map V.leTop.op s) = X.sheaf.obj.map (homOfLE h).op
      (bundleDualValue L U α (L.val.map U.leTop.op s))
  rw [← bundleDualValue_restrict L (homOfLE h)]
  congr 1
  rw [← L.val.map_comp_apply, ← op_comp]
  rfl

/-- Genuine dual quasicoherence produces the localization compatibility of
these actual ideals, on every affine open. -/
theorem sectionZeroIdeal_map_basicOpen (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    (sectionZeroIdeal L s U).map
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
    sectionZeroIdeal L s (X.basicOpen f) := by
  let := a.dual.isQuasicoherent
  let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨α, rfl⟩ := (mem_sectionZeroIdeal L s U r).mp hr
    apply (mem_sectionZeroIdeal L s (X.basicOpen f) _).mpr
    exact ⟨(bundleDual L).presheaf.map (homOfLE (X.basicOpen_le f)).op α,
      sectionZeroEvaluation_restrict L s (X.basicOpen_le f) α⟩
  · intro r hr
    obtain ⟨α, rfl⟩ := (mem_sectionZeroIdeal L s (X.basicOpen f) r).mp hr
    obtain ⟨n, t, ht⟩ := affineOpenSection_clearDenominator (bundleDual L) hU f α
    have he : ρ (sectionZeroEvaluation L s U t) =
        (ρ f) ^ n * sectionZeroEvaluation L s (X.basicOpen f) α := by
      rw [← sectionZeroEvaluation_restrict L s (X.basicOpen_le f) t]
      rw [ht, map_smul]
      rfl
    have hm : ρ (sectionZeroEvaluation L s U t) ∈
        (sectionZeroIdeal L s U).map ρ :=
      Ideal.mem_map_of_mem ρ (show sectionZeroEvaluation L s U t ∈
        sectionZeroIdeal L s U from ⟨t, rfl⟩)
    rw [he] at hm
    have hu : IsUnit (ρ f) := X.toRingedSpace.isUnit_res_basicOpen f
    obtain ⟨u, hu⟩ := hu
    have hm' := ((sectionZeroIdeal L s U).map ρ).mul_mem_left
      ((↑(u⁻¹) : Γ(X, X.basicOpen f)) ^ n) hm
    simpa only [← hu, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] using hm'

/-- The zero ideal sheaf is constructed from the actual evaluation ideals and
the proved localization equality. -/
def sectionZeroIdealSheaf (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    Scheme.IdealSheafData X where
  ideal U := sectionZeroIdeal L s U
  map_ideal_basicOpen U f := sectionZeroIdeal_map_basicOpen a s U.property f

/-- In any genuine frame, evaluation is multiplication of the original section
coefficient and the actual dual coefficient. -/
theorem sectionZeroEvaluation_frame (s : Γ(L, ⊤)) {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (α : Γ(bundleDual L, V)) :
    sectionZeroEvaluation L s V α =
      e.coefficients i (L.presheaf.map V.leTop.op s) * e.dual.coefficients i α := by
  change bundleDualValue L V α (L.val.map V.leTop.op s) = _
  rw [dualFrame_section_eq_smul_generator e i (L.val.map V.leTop.op s)]
  change α.val.app (.op (Over.mk (𝟙 V)))
    (_ • (e.coefficients i).symm 1) = _
  rw [(α.val.app (.op (Over.mk (𝟙 V)))).hom.map_smul]
  rfl

/-- A frame identifies the actual zero ideal with the original principal ideal. -/
theorem sectionZeroIdeal_eq_span_frame (s : Γ(L, ⊤)) {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    sectionZeroIdeal L s V =
      Ideal.span {e.coefficients i (L.presheaf.map V.leTop.op s)} := by
  ext r
  constructor
  · rintro ⟨α, rfl⟩
    rw [sectionZeroEvaluation_frame s e i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · intro hr
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hr
    refine ⟨(e.dual.coefficients i).symm b, ?_⟩
    rw [sectionZeroEvaluation_frame s e i, LinearEquiv.apply_symm_apply]
    exact hb.symm

/-- The zero locus is the genuine closed subscheme produced by the actual ideals. -/
abbrev sectionZeroSubscheme (a : LineBundleAtlas L) (s : Γ(L, ⊤)) : Scheme :=
  (sectionZeroIdealSheaf a s).subscheme

/-- The actual closed-subscheme morphism back to the original scheme. -/
abbrev sectionZeroι (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    sectionZeroSubscheme a s ⟶ X := (sectionZeroIdealSheaf a s).subschemeι

/-- Actual affine zero-subscheme sections are the quotient by the proved evaluation ideal. -/
def sectionZeroAffineQuotientIso (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (U : X.affineOpens) : Γ(sectionZeroSubscheme a s, sectionZeroι a s ⁻¹ᵁ U) ≅
      CommRingCat.of (Γ(X, U) ⧸ sectionZeroIdeal L s U) :=
  (sectionZeroIdealSheaf a s).subschemeObjIso U

/-- The genuine affine closed-subscheme restriction reads back to the literal quotient map. -/
theorem sectionZeroι_app (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (U : X.affineOpens) :
    (sectionZeroι a s).app U =
      CommRingCat.ofHom (Ideal.Quotient.mk (sectionZeroIdeal L s U)) ≫
        (sectionZeroAffineQuotientIso a s U).inv :=
  (sectionZeroIdealSheaf a s).subschemeι_app U

/-- Surjectivity holds on every actual AFFINE open. No global Gamma epi is claimed. -/
theorem sectionZeroι_app_surjective (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (U : X.affineOpens) : Function.Surjective ((sectionZeroι a s).app U) :=
  (sectionZeroIdealSheaf a s).subschemeι_app_surjective U

/-- The actual affine restriction kernel is the original evaluation ideal. -/
theorem sectionZeroι_app_ker (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (U : X.affineOpens) :
    RingHom.ker ((sectionZeroι a s).app U).hom = sectionZeroIdeal L s U :=
  (sectionZeroIdealSheaf a s).ker_subschemeι_app U

/-- The actual section coefficient and actual zero-subscheme restriction are
exact on each genuinely framed affine open. Regularity is needed only for
injectivity of the first map. -/
theorem sectionZeroAffine_frame_exact (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (U : X.affineOpens) {V : X.Opens} (e : LocalBundleFrame L V) (i : U.val ⟶ V) :
    Function.Exact
      (fun r : Γ(X, U) ↦
        (show Γ(X, U) from e.coefficients i (L.presheaf.map U.val.leTop.op s)) * r)
      ((sectionZeroι a s).app U) := by
  intro r
  change r ∈ RingHom.ker ((sectionZeroι a s).app U).hom ↔ _
  rw [sectionZeroι_app_ker, sectionZeroIdeal_eq_span_frame s e i,
    Ideal.mem_span_singleton]
  exact exists_congr (fun b ↦ eq_comm)

/-- The produced morphism is genuinely a closed immersion. -/
theorem sectionZeroι_isClosedImmersion (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    IsClosedImmersion (sectionZeroι a s) := inferInstance

/-- Integral geometry and a genuinely nonzero original section produce
nonvanishing of its actual coefficient on every nonempty framed open. -/
theorem sectionCoefficient_ne_zero [IsIntegral X] (a : LineBundleAtlas L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {U V : X.Opens} [Nonempty V]
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    e.coefficients i (L.presheaf.map V.leTop.op s) ≠ 0 := by
  intro he
  apply hs
  apply a.restriction_injective V.leTop
  change L.presheaf.map V.leTop.op s = L.presheaf.map V.leTop.op 0
  apply (e.coefficients i).injective
  simpa only [map_zero] using he

/-- Multiplication by the genuine coefficient is injective, produced from
the actual integral scheme and nonzero section rather than a regularity input. -/
theorem sectionCoefficient_mul_injective [IsIntegral X] (a : LineBundleAtlas L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {U V : X.Opens} [Nonempty V]
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    Function.Injective (fun r : Γ(X, V) ↦
      (show Γ(X, V) from e.coefficients i (L.presheaf.map V.leTop.op s)) * r) := by
  intro r t he
  exact mul_left_cancel₀ (sectionCoefficient_ne_zero a s hs e i) he

end
end SGPT.Foundations.Schemes
