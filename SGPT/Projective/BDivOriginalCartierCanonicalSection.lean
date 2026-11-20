import SGPT.Foundations.Schemes.LineSectionZeroSubscheme
import SGPT.Projective.BDivCartierIdealModulePrereqs

/-! An effective algebraic Cartier ideal determines its actual inverse
line and canonical section. No comparison-module import is required. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open SGPT.Foundations.Schemes

namespace SGPT.Projective.BDivNov16

noncomputable section

private def regularIdealGeneratorEquiv {R : Type*} [CommRing R]
    (I : Ideal R) (g : R) (hg : g ∈ nonZeroDivisors R) (hI : I = Ideal.span {g}) :
    R ≃ₗ[R] I := by
  have hmem : g ∈ I := hI.symm ▸ Ideal.mem_span_singleton_self g
  refine LinearEquiv.ofBijective
    { toFun := fun r => ⟨r * g, I.mul_mem_left r hmem⟩
      map_add' := fun r s => Subtype.ext (add_mul r s g)
      map_smul' := fun r s => Subtype.ext (mul_assoc r s g) } ⟨?_, ?_⟩
  · intro r s hrs
    apply sub_eq_zero.mp
    apply (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp
    rw [sub_mul, show r * g = s * g from congrArg Subtype.val hrs, sub_self]
  · intro a
    have ha : (a : R) ∈ Ideal.span {g} := by rw [← hI]; exact a.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ha
    exact ⟨r, Subtype.ext hr⟩

variable {X : Scheme.{0}} (I : X.IdealSheafData)

/-- The regular-generator trivialization is a frame of the genuine ideal
module over the actual affine open, retaining the whole sheaf. -/
def originalCartierIdealFrame (U : X.affineOpens) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) (hI : I.ideal U = Ideal.span {g}) :
    LocalBundleFrame I.toModules (U : X.Opens) := by
  let e : Γ(X, U) ≃ₗ[Γ(X, U)]
      moduleSpecΓFunctor.obj (I.toModules.restrict U.2.fromSpec) :=
    ((regularIdealGeneratorEquiv (I.ideal U) g hg hI).trans
      (I.toModulesSectionsEquiv U).symm).trans (I.toModules.topSectionsEquiv U.2)
  let := I.isIso_fromTildeΓ_toModules U.2
  let affineIso : SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf ≅
      I.toModules.restrict U.2.fromSpec :=
    (tildeSelf (R := Γ(X, U))).symm ≪≫
      (tilde.functor Γ(X, U)).mapIso e.toModuleIso ≪≫
        asIso (I.toModules.restrict U.2.fromSpec).fromTildeΓ
  exact ((Opens.sheafOfModulesEquivOverInverseUnit (U : X.Opens) X.ringCatSheaf).symm ≪≫
    (Scheme.Modules.overEquiv (U : X.Opens)).inverse.mapIso
      ((Scheme.Modules.restrictUnitIso U.2.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso affineIso ≪≫
          I.toModules.restrictιIso U.2) ≪≫ I.toModules.overIso U).symm

/-- The actual locally principal ideal is a line bundle. -/
def originalCartierIdealAtlas (hI : I.IsInvertible) : LineBundleAtlas I.toModules := by
  classical
  choose U hx g hg hgen using hI
  exact ⟨X, fun x => (U x : X.Opens), fun x => ⟨x, hx x⟩,
    fun x => originalCartierIdealFrame I (U x) (g x) (hg x) (hgen x)⟩

/-- The canonical section of the genuine inverse Cartier line is the actual
inclusion of the original ideal sheaf, viewed as a dual section on top. -/
def originalCartierCanonicalSection : Γ(bundleDual I.toModules, ⊤) :=
  (SheafOfModules.overFunctor X.ringCatSheaf ⊤).map I.toModulesInclusion

/-- The coefficient of the canonical section is the original local ideal
generator read from the dual frame. -/
theorem originalCartierCanonicalSection_coefficients {U V : X.Opens}
    (e : LocalBundleFrame I.toModules U) (j : V ⟶ U) :
    e.dual.coefficients j ((bundleDual I.toModules).val.map V.leTop.op
      (originalCartierCanonicalSection I)) = (((e.coefficients j).symm 1).val : Γ(X, V)) := by
  rw [LocalBundleFrame.dual_coefficients]
  rfl

private def idealModuleSectionValue (V : X.Opens) (s : Γ(I.toModules, V)) : Γ(X, V) :=
  s.val

private theorem ideal_eq_span_of_frame (V : X.affineOpens) {U : X.Opens}
    (e : LocalBundleFrame I.toModules U) (j : (V : X.Opens) ⟶ U) :
    I.ideal V =
      @Ideal.span Γ(X, V) inferInstance {idealModuleSectionValue I V ((e.coefficients j).symm 1)} := by
  let t := (e.coefficients j).symm 1
  let b : Γ(X, V) := idealModuleSectionValue I V t
  have ht : b ∈ I.ideal V := (I.isLocallyMem_iff V t.val).mp t.property
  change I.ideal V = @Ideal.span Γ(X, V) inferInstance {b}
  apply le_antisymm
  · intro r hr
    let s : Γ(I.toModules, V) := ⟨r, (I.isLocallyMem_iff V r).mpr hr⟩
    let c : Γ(X, V) := e.coefficients j s
    have hs := dualFrame_section_eq_smul_generator e j s
    have he : r = c * b := congrArg (idealModuleSectionValue I V) hs
    exact Ideal.mem_span_singleton'.mpr ⟨c, he.symm⟩
  · apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact ht

/-- The actual canonical section cuts out the same entire original ideal
sheaf, including its scheme structure. -/
theorem originalCartierCanonicalSection_zeroIdeal (hI : I.IsInvertible) :
    sectionZeroIdealSheaf (originalCartierIdealAtlas I hI).dual
      (originalCartierCanonicalSection I) = I := by
  classical
  let a := originalCartierIdealAtlas I hI
  let K := Σ i : a.I, {V : X.Opens // IsAffineOpen V ∧ V ≤ a.opens i}
  let V (i : K) : X.affineOpens := ⟨i.2.val, i.2.property.1⟩
  have hcover : ⨆ i, (V i).1 = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨W, hW, hxW, hWi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨W, hW, hWi⟩⟩, hxW⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V hcover
  intro i
  let e := a.frame i.1
  let j : (V i : X.Opens) ⟶ a.opens i.1 := homOfLE i.2.property.2
  change sectionZeroIdeal _ (originalCartierCanonicalSection I) (V i : X.Opens) = I.ideal (V i)
  refine (sectionZeroIdeal_eq_span_frame (originalCartierCanonicalSection I) e.dual j).trans ?_
  have hcoeff := originalCartierCanonicalSection_coefficients I e j
  exact (congrArg (fun r : Γ(X, V i) => Ideal.span {r}) hcoeff).trans
    (ideal_eq_span_of_frame I (V i) e j).symm


/-- Zero as a section gives the zero ideal sheaf on every actual affine open. -/
theorem originalSectionZeroIdeal_zero {L : X.Modules} (a : LineBundleAtlas L) :
    sectionZeroIdealSheaf a (0 : Γ(L, ⊤)) = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  change sectionZeroIdeal L (0 : Γ(L, ⊤)) U.1 = ⊥
  apply le_antisymm _ bot_le
  intro r hr
  obtain ⟨α, rfl⟩ := (mem_sectionZeroIdeal L (0 : Γ(L, ⊤)) U.1 r).mp hr
  have h := show sectionZeroEvaluation L (0 : Γ(L, ⊤)) U.1 α = 0 from by
    change ((bundleDualValueBilinear L (U : X.Opens)).flip
      ((L.val.map U.1.leTop.op) (0 : Γ(L, ⊤)))) α = 0
    simp only [map_zero, LinearMap.zero_apply]
  exact Ideal.mem_bot.mpr h

theorem originalCartierCanonicalSection_ne_zero (hI : I.IsInvertible) (hne : I ≠ ⊥) :
    originalCartierCanonicalSection I ≠ 0 := by
  intro hz
  apply hne
  calc
    I = sectionZeroIdealSheaf (originalCartierIdealAtlas I hI).dual
        (originalCartierCanonicalSection I) := (originalCartierCanonicalSection_zeroIdeal I hI).symm
    _ = ⊥ := by rw [hz, originalSectionZeroIdeal_zero]

end

end SGPT.Projective.BDivNov16
