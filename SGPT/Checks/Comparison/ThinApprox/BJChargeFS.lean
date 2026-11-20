import SGPT.Checks.Comparison.BJModel3Chart
import SGPT.Checks.Comparison.ThinApprox.BJModelAmplePairing
import SGPT.Foundations.Envelope.AlgGeom.BaseIdealPullbackGeneratingSections
import SGPT.Foundations.Envelope.AlgGeom.InvertibleSectionFamilyImage
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveBaseIdealEpimorphism
import SGPT.Foundations.Envelope.AlgGeom.IdealModuleOpenRestriction
import SGPT.Foundations.Envelope.AlgGeom.CurveLineSectionPositivity
import SGPT.Foundations.Envelope.AlgGeom.InvertibleBaseIdealPullback
import SGPT.Foundations.Envelope.AlgGeom.SchemeTensorUnitSections

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# Fubini–Study functions are `ω`-psh (lane BJ-CHARGE, step R4b of `claude-bj-model3:plan`)

Source: Boucksom–Jonsson ([BJ22], `references/bj22-trivval`), Example `exam:FSpsh`
(`𝓗(L) ⊆ PL ∩ PSH(L)`: a globally generated test configuration is relatively nef) and
Proposition `prop:FSideal` (Fubini–Study functions are `m⁻¹ φ_𝔞` with `M ⊗ 𝔞_λ` globally
generated). Towards `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint:
`claude-bj-charge.tex`.

Let `φ = k⁻¹ φ_𝔞` be a Fubini–Study function of `ω` in the flag form `IsFlagFS`:
`M` invertible with `[M] = k ω`, `M ⊗ 𝔞_λ` globally generated for all `λ`. On the chart
`X × 𝔸¹ = pr₂⁻¹(D₊(x₀))` of `X × ℙ¹` the ideal `t^b 𝔞 = ∑_j pr₁^{-1}(𝔞_{b-j}) 𝓘^j` is the sum of
the section ideals of the sections `t^j · pr₁^* s` of `pr₁^* M`, `s` running through generators of
`M ⊗ 𝔞_{b-j}`. The evaluation of this family is an epimorphism onto `t^b 𝔞`
(SGPT.Foundations.Envelope's `familyEvaluation_imageIdeal`), and SGPT.Foundations.Envelope's divided epimorphism
transports it along the blow-down: `(t^b 𝔞) · 𝒪 ⊗ π^* M` is globally generated over
`π⁻¹(X × 𝔸¹)`, which contains the central fibre. Hence it has nonnegative degree on every curve
of the central fibre, and `φ` is an `ω`-psh PL function (`IsOmegaPshPL`, lane BJ-MODEL3).

## Main results

* `sectionIdeal_smul_ideal`: the section ideal of `f • s` is `(f) · 𝔟_s` on affine opens;
* `centralIdeal_comap_ideal`: on the chart, the ideal of the central fibre is `(t)`;
* `flagSheaf_comap_eq_iSup_sectionIdeal`: on the chart, `t^b 𝔞 = ∑ 𝔟_{t^j pr₁^* s}`;
* `nonempty_generatingSections_flagLine`: `(t^b 𝔞) · 𝒪 ⊗ π^* M` is globally generated over
  `π⁻¹(X × 𝔸¹)`;
* `isNefOn_flagLine`: it is nef on the central fibre;
* `isOmegaPshPL_of_isFlagFS`: **Fubini–Study functions are `ω`-psh** ([BJ22, `exam:FSpsh`]);
* `flagFS_mem_psh`, `bjAppSeq_of_omegaPsh_pairings`: the Fubini–Study hypothesis of
  `ampleEnergyPairingOfFlagFS` / `bjAppSeq_of_flagFS_pairings` is discharged by any energy pairing
  whose `ω`-psh functions contain the `IsOmegaPshPL` functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.InvertibleSheafBaseIdeal
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJIntersect
open FlagIdealBound SGPT.Support.Alterations SGPT.Support.Alterations.Geometry

section smul

universe u

variable {Y : Scheme.{u}} {L : Y.Modules}

/-- Membership in the ideal of a section on an affine open: the values of the evaluation of the
section against local dual sections. -/
theorem mem_sectionIdeal_ideal (hL : Scheme.Modules.IsInvertible L) (s : Γ(L, ⊤))
    (W : Y.affineOpens) (a : Γ(Y, W.1)) :
    a ∈ (sectionIdeal hL s).ideal W ↔ ∃ d, (sectionEvaluation L s).val.app (.op W.1) d = a :=
  Iff.rfl

/-- The ideal of the section `f • s` on an affine open `W` is `(f|_W) · 𝔟_s(W)`. -/
theorem sectionIdeal_smul_ideal (hL : Scheme.Modules.IsInvertible L) (f : Γ(Y, ⊤))
    (s : Γ(L, ⊤)) (W : Y.affineOpens) :
    (sectionIdeal hL (f • s)).ideal W =
      Ideal.span {Y.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op f} *
        (sectionIdeal hL s).ideal W := by
  ext a
  rw [Ideal.mem_span_singleton_mul, mem_sectionIdeal_ideal]
  simp only [mem_sectionIdeal_ideal, SchemeTensorUnitSections.sectionEvaluation_apply,
    Scheme.Modules.map_smul]
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨_, ⟨d, rfl⟩, ?_⟩
    rw [SGPT.Support.ModularCurves.SheafOfModules.evalSection_smul_right]
    rfl
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    refine ⟨d, ?_⟩
    rw [SGPT.Support.ModularCurves.SheafOfModules.evalSection_smul_right]
    rfl

end smul

section chart

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))

/-- The chart `X × 𝔸¹ = pr₂⁻¹(D₊(x₀))` of `X × ℙ¹`. -/
abbrev lineChartOpen : (productLine p).Opens := productSnd p ⁻¹ᵁ (chartOpen ℂ).1

theorem le_preimage_chartOpen (W : (lineChartOpen p).toScheme.Opens) :
    W ≤ ((lineChartOpen p).ι ≫ productSnd p) ⁻¹ᵁ (chartOpen ℂ).1 := by
  intro x _
  change productSnd p ((lineChartOpen p).ι x) ∈ (chartOpen ℂ).1
  exact x.2

/-- The coordinate `t` on the chart `X × 𝔸¹`, pulled back from a section `g` of `ℙ¹` over the
chart `D₊(x₀)`. -/
def chartCoord (g : Γ(projectiveSpace ℂ 1, (chartOpen ℂ).1)) :
    Γ((lineChartOpen p).toScheme, ⊤) :=
  ((lineChartOpen p).ι ≫ productSnd p).appLE (chartOpen ℂ).1 ⊤ (le_preimage_chartOpen p ⊤) g

/-- **On the chart `X × 𝔸¹`, the ideal of the central fibre is `(t)`.** -/
theorem centralIdeal_comap_ideal {g : Γ(projectiveSpace ℂ 1, (chartOpen ℂ).1)}
    (hg : (zeroIdeal ℂ).ideal (chartOpen ℂ) = Ideal.span {g})
    (W : (lineChartOpen p).toScheme.affineOpens) :
    ((centralIdeal p).comap (lineChartOpen p).ι).ideal W =
      Ideal.span {(lineChartOpen p).toScheme.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
        (chartCoord p g)} := by
  rw [centralIdeal, ← Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_ideal_of_affine_opens _ _ W (chartOpen ℂ)
      (le_preimage_chartOpen p W.1), hg, Ideal.map_span, Set.image_singleton]
  congr 2
  rw [chartCoord, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- The section ideals on the chart: `𝔟_{t^j · pr₁^* s} = (t^j) · pr₁^{-1} 𝔟_s` on affine opens. -/
theorem sectionIdeal_chart_ideal {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (g : Γ(projectiveSpace ℂ 1, (chartOpen ℂ).1)) (j : ℕ) (s : Γ(M, ⊤))
    (W : (lineChartOpen p).toScheme.affineOpens) :
    (sectionIdeal (hM.pullback ((lineChartOpen p).ι ≫ productFst p))
        (chartCoord p g ^ j •
          Scheme.Modules.affinePullbackUnitTop ((lineChartOpen p).ι ≫ productFst p) M s)).ideal W =
      Ideal.span {(lineChartOpen p).toScheme.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
        (chartCoord p g)} ^ j *
        ((sectionIdeal hM s).comap ((lineChartOpen p).ι ≫ productFst p)).ideal W := by
  rw [sectionIdeal_smul_ideal, map_pow, Ideal.span_singleton_pow,
    InvertibleBaseIdealPullback.sectionIdeal_comap]

/-- **On the chart `X × 𝔸¹`, `t^b 𝔞` is generated by the sections `t^j · pr₁^* s`**, `s` running
through generators of `M ⊗ 𝔞_{b-j}` ([BJ22, proof of `prop:FSideal`]). -/
theorem flagSheaf_comap_eq_iSup_sectionIdeal {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (𝔞 : FlagIdeal X) (b : ℤ) (S : ℤ → Set Γ(M, ⊤))
    (hS : ∀ l, 𝔞.ideal l = ⨆ s ∈ S l, sectionIdeal hM s)
    {g : Γ(projectiveSpace ℂ 1, (chartOpen ℂ).1)}
    (hg : (zeroIdeal ℂ).ideal (chartOpen ℂ) = Ideal.span {g}) :
    (flagSheaf p 𝔞 b).comap (lineChartOpen p).ι =
      ⨆ x : Σ j : ℕ, S (b - j), sectionIdeal (hM.pullback ((lineChartOpen p).ι ≫ productFst p))
        (chartCoord p g ^ x.1 •
          Scheme.Modules.affinePullbackUnitTop ((lineChartOpen p).ι ≫ productFst p) M x.2.1) := by
  refine Scheme.IdealSheafData.ext (funext fun W => ?_)
  rw [flagSheaf, Scheme.IdealSheafData.comap_iSup, Scheme.IdealSheafData.ideal_iSup,
    Scheme.IdealSheafData.ideal_iSup, iSup_apply, iSup_apply, iSup_sigma]
  refine iSup_congr fun j => ?_
  rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    centralIdeal_comap_ideal p hg W, ← Scheme.IdealSheafData.comap_comp, hS, iSup_subtype',
    Scheme.IdealSheafData.comap_iSup, Scheme.IdealSheafData.ideal_iSup, iSup_apply,
    mul_comm, Submodule.mul_iSup]
  refine iSup_congr fun s => ?_
  rw [sectionIdeal_chart_ideal]

end chart

/-! ### Global generation of `π^*M ⊗ (t^b 𝔞) · 𝒪` over `π⁻¹(X × 𝔸¹)` -/

section generation

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))

open Scheme.Modules InvertibleSectionFamilyImage ProjectiveBaseIdealEpimorphism
  BaseIdealPullbackGeneratingSections

attribute [local instance] Scheme.Modules.monoidalCategory

/-- **The line bundle `(t^b 𝔞) · 𝒪 ⊗ π^* pr₁^* M`** on the model `𝒳_{𝔠, c}` (an invertible sheaf when
the model dominates the model of `(𝔞, b)`). -/
def flagLine (M : X.Modules) (𝔞 : FlagIdeal X) (b : ℤ) (𝔠 : FlagIdeal X) (c : ℤ) :
    (flagModel p 𝔠 c).Modules :=
  ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔠 c)).toModules ⊗
    (Scheme.Modules.pullback (flagModelπ p 𝔠 c ≫ productFst p)).obj M

/-- The open `π⁻¹(X × 𝔸¹)` of the model, a neighbourhood of the central fibre. -/
abbrev modelChart (𝔠 : FlagIdeal X) (c : ℤ) : (flagModel p 𝔠 c).Opens :=
  flagModelπ p 𝔠 c ⁻¹ᵁ lineChartOpen p

/-- **Global generation over `π⁻¹(X × 𝔸¹)`** ([BJ22, `exam:FSpsh`]): if `M ⊗ 𝔞_λ` is globally
generated for every `λ`, then `(t^b 𝔞) · 𝒪 ⊗ π^* M` is generated by global sections over
`π⁻¹(X × 𝔸¹)`. On the chart, `t^b 𝔞` is the sum of the section ideals of the sections
`t^j · pr₁^* s` of `pr₁^* M` (`flagSheaf_comap_eq_iSup_sectionIdeal`); the evaluation of this family
is an epimorphism onto `t^b 𝔞`, and SGPT.Foundations.Envelope's divided epimorphism transports it to the
model. -/
theorem nonempty_generatingSections_flagLine {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) {𝔞 : FlagIdeal X} (h𝔞 : 𝔞.IsGeneratedBy hM) (b : ℤ)
    (𝔠 : FlagIdeal X) (c : ℤ) :
    Nonempty ((Scheme.Modules.pullback (modelChart p 𝔠 c).ι).obj
      (flagLine p M 𝔞 b 𝔠 c)).GeneratingSections := by
  choose S hS using h𝔞
  obtain ⟨g, -, hg⟩ := exists_zeroIdeal_ideal_chartOpen ℂ
  let U := lineChartOpen p
  let f₁ : U.toScheme ⟶ X := U.ι ≫ productFst p
  let LU := (Scheme.Modules.pullback f₁).obj M
  have hLU : Scheme.Modules.IsInvertible LU := hM.pullback f₁
  let ι := Σ j : ℕ, S (b - j)
  let σ : ι → Γ(LU, ⊤) := fun x =>
    chartCoord p g ^ x.1 • Scheme.Modules.affinePullbackUnitTop f₁ M x.2.1
  let I := (flagSheaf p 𝔞 b).comap U.ι
  have hI : I = ⨆ x, sectionIdeal hLU (σ x) :=
    flagSheaf_comap_eq_iSup_sectionIdeal p hM 𝔞 b S hS hg
  let : ((tensorRight (C := U.toScheme.Modules) (dualObj LU)).obj
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) ι)).IsQuasicoherent :=
    freeTensorDual_isQuasicoherent hLU ι
  have himg : QuasicoherentImageIdeal.imageIdeal _ (familyEvaluation hLU σ) = I :=
    (familyEvaluation_imageIdeal hLU σ).trans hI.symm
  let P := imageFactorOfEq (familyEvaluation hLU σ) I himg
  let : Epi P := imageFactorOfEq_epi _ _ himg
  let π := flagModelπ p 𝔠 c
  let V := modelChart p 𝔠 c
  let μ : V.toScheme ⟶ U.toScheme := π ∣_ U
  have hμ : μ ≫ U.ι = V.ι ≫ π := morphismRestrict_ι π U
  let q := dividedEpimorphism μ (SheafOfModules.free (R := U.toScheme.ringCatSheaf) ι) LU hLU I P
  have hq : Epi q := dividedEpimorphism_epi μ _ LU hLU I P
  -- identify the target with the restriction of `flagLine`
  let J := (flagSheaf p 𝔞 b).comap π
  have hJ : J.comap V.ι = I.comap μ := by
    simp only [J, I, ← Scheme.IdealSheafData.comap_comp, hμ]
  let : IsIso (J.toModulesComapPullbackMap V.ι) :=
    J.toModulesComapPullbackMap_isIso_of_isOpenImmersion V.ι
  let e₂ : (Scheme.Modules.pullback V.ι).obj J.toModules ≅ (I.comap μ).toModules :=
    asIso (J.toModulesComapPullbackMap V.ι) ≪≫ eqToIso (by rw [hJ])
  have hf : V.ι ≫ π ≫ productFst p = μ ≫ f₁ := by
    simp only [f₁, ← Category.assoc, hμ]
  let e₃ : (Scheme.Modules.pullback V.ι).obj
      ((Scheme.Modules.pullback (π ≫ productFst p)).obj M) ≅ (Scheme.Modules.pullback μ).obj LU :=
    (Scheme.Modules.pullbackComp V.ι (π ≫ productFst p)).app M ≪≫
      (Scheme.Modules.pullbackCongr hf).app M ≪≫ ((Scheme.Modules.pullbackComp μ f₁).app M).symm
  let : (Scheme.Modules.pullback V.ι).Monoidal := pullbackMonoidal V.ι
  let e : (Scheme.Modules.pullback V.ι).obj (flagLine p M 𝔞 b 𝔠 c) ≅
      (tensorRight (C := V.toScheme.Modules) ((Scheme.Modules.pullback μ).obj LU)).obj
        (I.comap μ).toModules :=
    (Functor.Monoidal.μIso (Scheme.Modules.pullback V.ι) _ _).symm ≪≫ (e₂ ⊗ᵢ e₃)
  let : Epi (q ≫ e.inv) := epi_comp q e.inv
  exact ⟨(ClosedProjectiveGlobalGeneration.pullback_generatingSections μ
    (SheafOfModules.free.generatingSections (R := U.toScheme.ringCatSheaf) ι)).ofEpi (q ≫ e.inv)⟩

/-- **The central fibre lies in the chart `π⁻¹(X × 𝔸¹)`.** -/
theorem centralFibre_subset_modelChart (𝔠 : FlagIdeal X) (c : ℤ) :
    centralFibre p 𝔠 c ⊆ (modelChart p 𝔠 c : Set (flagModel p 𝔠 c)) := by
  intro x hx
  have hx' : flagModelπ p 𝔠 c x ∈ ((centralIdeal p).support : Set (productLine p)) := hx
  rw [support_centralIdeal] at hx'
  obtain ⟨z, hz⟩ := hx'
  show productSnd p (flagModelπ p 𝔠 c x) ∈ (chartOpen ℂ).1
  refine ⟨Spec.map (CommRingCat.ofHom (evalZero ℂ)) z, trivial, ?_⟩
  rw [← hz, zeroPoint, Scheme.Hom.comp_apply]
  rfl

variable [IsProjective p]

/-- **`(t^b 𝔞) · 𝒪 ⊗ π^* M` is nef on the central fibre** when `M ⊗ 𝔞_λ` is globally generated for
all `λ` ([BJ22, `exam:FSpsh`]): every closed integral curve `C` of the central fibre lies in the
chart `π⁻¹(X × 𝔸¹)`, over which the sheaf is globally generated, so its degree on `C` is
nonnegative (SGPT.Foundations.Envelope's `degree_pullback_nonneg_of_generatingSections`). -/
theorem isNefOn_flagLine {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    {𝔞 : FlagIdeal X} (h𝔞 : 𝔞.IsGeneratedBy hM)
    (b : ℤ) {𝔠 : FlagIdeal X} {c : ℤ} (hdom : Dominates p 𝔠 c 𝔞 b) :
    IsNefOn (flagModelStructure p 𝔠 c) (flagLine p M 𝔞 b 𝔠 c) (centralFibre p 𝔠 c) := by
  intro C hC
  let : IsClosedImmersion C.inclusion := C.closed
  let : IsIntegral C.carrier := C.integral
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
  let V := modelChart p 𝔠 c
  obtain ⟨G⟩ := nonempty_generatingSections_flagLine p hM h𝔞 b 𝔠 c
  have hinv : Scheme.Modules.IsInvertible (flagLine p M 𝔞 b 𝔠 c) :=
    (hdom.1.isInvertibleModule_toModules.tensorObj
      (hM.pullback (flagModelπ p 𝔠 c ≫ productFst p))).of_iso
        (SGPT.Support.ModularCurves.monoidalTensorObjIso _ _)
  have hrange : Set.range C.inclusion ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact hC.trans (centralFibre_subset_modelChart p 𝔠 c)
  let i := IsOpenImmersion.lift V.ι C.inclusion hrange
  have hi : i ≫ V.ι = C.inclusion := IsOpenImmersion.lift_fac _ _ _
  have hq : IsProjectiveFactorization (C.inclusion ≫ flagModelStructure p 𝔠 c) :=
    (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective
      (flagModelStructure p 𝔠 c)).comp_isClosedImmersion C.inclusion C.closed
  have h := CurveLineSectionPositivity.degree_pullback_nonneg_of_generatingSections
    (C.inclusion ≫ flagModelStructure p 𝔠 c) hq C.dimension.le i
    ((Scheme.Modules.pullback V.ι).obj (flagLine p M 𝔞 b 𝔠 c)) (hinv.pullback V.ι) G
  let E : (Scheme.Modules.pullback C.inclusion).obj (flagLine p M 𝔞 b 𝔠 c) ≅
      (Scheme.Modules.pullback i).obj
        ((Scheme.Modules.pullback V.ι).obj (flagLine p M 𝔞 b 𝔠 c)) :=
    (Scheme.Modules.pullbackCongr hi.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp i V.ι).app _).symm
  rw [CurveLineDegrees.degree_eq_of_iso _ E]
  exact h

end generation

/-! ### Fubini–Study functions are `ω`-psh -/

section psh

universe u

open SGPT.NAPotential.BJ.NativePicard

attribute [local instance] Scheme.Modules.monoidalCategory

variable {X : Scheme.{0}}

/-- The rational Picard class of an atlas is the `ℚ`-class of the invertible sheaf
(`RationalPicardSpace X` and `PicQ X` are the same space). -/
theorem rationalPicardClass_eq_picQ {M : X.Modules} (a : SGPT.Foundations.Schemes.LineBundleAtlas M) :
    rationalPicardClass a = picQ ⟨M, isInvertible_of_atlas a⟩ := by
  simp only [rationalPicardClass, rationalizePicard, AddMonoidHom.coe_mk, ZeroHom.coe_mk, picQ,
    lineCls]
  congr 2

/-- The `ℚ`-class of a tensor product of invertible sheaves is the sum of the classes. -/
theorem picQ_tensor {Y : Scheme.{0}} {L N : Y.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hN : Scheme.Modules.IsInvertible N) (hLN : Scheme.Modules.IsInvertible (L ⊗ N)) :
    picQ ⟨L ⊗ N, hLN⟩ = picQ ⟨L, hL⟩ + picQ ⟨N, hN⟩ := by
  simp only [picQ]
  rw [lineCls_tensor hL hN hLN, TensorProduct.tmul_add]

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- **Fubini–Study functions are `ω`-psh** ([BJ22, Example `exam:FSpsh`], step R4b of
`claude-bj-model3:plan`): every Fubini–Study function `φ = k⁻¹ φ_𝔞` of `ω` in the flag form of
[BJ22, `prop:FSideal`] (`IsFlagFS`) is an `ω`-psh PL function (`IsOmegaPshPL`). On the good model
of `(𝔞 · (t^0), b + 1)`, `φ = φ_D` for `D = k⁻¹ (b 𝒳₀ - E_{t^b 𝔞})`, and
`k (π^*ω + [𝒪(D)]) = [(t^b 𝔞) · 𝒪 ⊗ π^* M] - b [𝓘 · 𝒪]` is relatively nef: the first class by
global generation over `π⁻¹(X × 𝔸¹)` (`isNefOn_flagLine`), the second because `±[𝒪(𝒳₀)]` are
relatively nef. -/
theorem isOmegaPshPL_of_isFlagFS {ω : RationalPicardSpace X} {φ : BerkovichPoint p → ℝ}
    (h : IsFlagFS p ω φ) : IsOmegaPshPL ω φ := by
  obtain ⟨M, a, k, hk, 𝔞, hgen, hcls, hφ⟩ := h
  have hM : Scheme.Modules.IsInvertible M := isInvertible_of_atlas a
  obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound 𝔞
  obtain ⟨hgood, hdom⟩ := isGoodModel_mul_monomial p hb
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨_, _, hgood, ((k : ℚ)⁻¹) • flagDiv hgood.2 hdom, ?_, ?_⟩
  · funext v
    rw [map_smul, fn_flagDiv hgood.2 hdom hb, hφ v, Pi.smul_apply, Rat.smul_def]
    push_cast
    rfl
  · set 𝔠 := 𝔞 * FlagIdeal.monomial X 0
    set c := b + 1
    let π := flagModelπ p 𝔠 c
    have hinv : Scheme.Modules.IsInvertible (flagLine p M 𝔞 b 𝔠 c) :=
      (hdom.1.isInvertibleModule_toModules.tensorObj (hM.pullback (π ≫ productFst p))).of_iso
        (SGPT.Support.ModularCurves.monoidalTensorObjIso _ _)
    have hN : picQ ⟨flagLine p M 𝔞 b 𝔠 c, hinv⟩ ∈
        relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c) :=
      picQ_mem_relNefCone _ _ (isNefOn_flagLine p hM hgen b hdom)
    have hω : ω = ((k : ℚ)⁻¹) • picQ ⟨M, hM⟩ := by
      rw [← rationalPicardClass_eq_picQ a, hcls, smul_smul, inv_mul_cancel₀ hk', one_smul]
    have hline : picQ ⟨flagLine p M 𝔞 b 𝔠 c, hinv⟩ =
        picQ (flagVert hdom).line + omegaPullback 𝔠 c (picQ ⟨M, hM⟩) := by
      rw [omegaPullback, picPullbackQ_picQ]
      exact picQ_tensor hdom.1.isInvertibleModule_toModules (hM.pullback (π ≫ productFst p)) hinv
    have key : omegaPullback 𝔠 c ω + VDiv.cls (((k : ℚ)⁻¹) • flagDiv hgood.2 hdom) =
        ((k : ℚ)⁻¹) • (picQ ⟨flagLine p M 𝔞 b 𝔠 c, hinv⟩ +
          (b : ℚ) • -picQ (centralLine p 𝔠 c)) := by
      rw [hline, hω, map_smul, map_smul, flagDiv, map_sub, VDiv.cls_single, VDiv.cls_single,
        picQ_centralVert_line]
      module
    rw [key]
    refine Submodule.smul_mem _ (⟨(k : ℚ)⁻¹, by positivity⟩ : {r : ℚ // 0 ≤ r}) (add_mem hN ?_)
    rcases le_or_gt 0 b with hb0 | hb0
    · exact Submodule.smul_mem _ (⟨(b : ℚ), by exact_mod_cast hb0⟩ : {r : ℚ // 0 ≤ r})
        (neg_picQ_centralLine_mem_relNefCone p 𝔠 c)
    · rw [show (b : ℚ) • -picQ (centralLine p 𝔠 c) = (-(b : ℚ)) • picQ (centralLine p 𝔠 c) by
        rw [smul_neg, neg_smul]]
      exact Submodule.smul_mem _ (⟨-(b : ℚ), by
        have : (b : ℚ) < 0 := by exact_mod_cast hb0
        linarith⟩ : {r : ℚ // 0 ≤ r}) (picQ_centralLine_mem_relNefCone p 𝔠 c)

/-- **R4b discharges the Fubini–Study hypothesis of `ampleEnergyPairingOfFlagFS`**: if the
`ω`-psh functions of an energy pairing contain the `ω`-psh PL functions of the models
(`IsOmegaPshPL`), they contain the Fubini–Study functions of `ω`. -/
theorem flagFS_mem_psh {ω : RationalPicardSpace X} {n : ℕ}
    (B : SGPT.NAPotential.BJEnergy.EnergyPairing (BerkovichPoint p) n)
    (hpsh : ∀ φ : BerkovichPoint p → ℝ, IsOmegaPshPL ω φ → ∃ f ∈ B.psh, (f : BerkovichPoint p → ℝ) = φ)
    (φ : BerkovichPoint p → ℝ) (hφ : IsFlagFS p ω φ) :
    ∃ f ∈ B.psh, (f : BerkovichPoint p → ℝ) = φ :=
  hpsh φ (isOmegaPshPL_of_isFlagFS p hφ)

/-- **`thm:BJappseq` from energy pairings containing the `ω`-psh PL functions** (R4b applied to
`bjAppSeq_of_flagFS_pairings`): `thm:pshdetbydiv` (`DivisorialComparison`) and, in every rational
class `ω` with ample numerical class, an energy pairing on `X^An` with trivial point `v_triv`,
whose `ω`-psh functions contain the `IsOmegaPshPL` functions and which charges every divisorial
point, imply `thm:BJappseq`. -/
theorem bjAppSeq_of_omegaPsh_pairings (hcomp : SGPT.NAPotential.ThinApprox.BJ.AppSeq.DivisorialComparison p)
    (hE : ∀ ω : RationalPicardSpace X,
      SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p →
        ∃ (n : ℕ) (B : SGPT.NAPotential.BJEnergy.EnergyPairing (BerkovichPoint p) n),
          B.triv = BerkovichPoint.trivial p ∧
          (∀ φ : BerkovichPoint p → ℝ, IsOmegaPshPL ω φ →
            ∃ f ∈ B.psh, (f : BerkovichPoint p → ℝ) = φ) ∧
          ∀ v ∈ divisorialSet p, B.IsCharged v) :
    SGPT.NAPotential.ThinApprox.BJ.AppSeq.BJAppSeqStatement.{u} p := by
  refine bjAppSeq_of_flagFS_pairings p hcomp fun ω hω => ?_
  obtain ⟨n, B, htriv, hpsh, hcharged⟩ := hE ω hω
  exact ⟨n, B, htriv, flagFS_mem_psh p B hpsh, hcharged⟩

end psh

end SGPT.NAPotential.ThinApprox.BJ
