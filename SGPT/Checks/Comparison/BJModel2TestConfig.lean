import SGPT.Checks.Comparison.BJModel2FlagSheaf
import SGPT.Support.Principalization.Scheme.BlowUp.Glue.Global
import SGPT.Support.Principalization.Scheme.BlowUp.Glue.Trivial
import SGPT.Support.Principalization.Scheme.BlowUp.BlowUpMap
import SGPT.Support.Principalization.Scheme.BlowUp.ProductCenter
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveBlowupSequence
import SGPT.Foundations.Envelope.AlgGeom.HironakaDeJongBlowupComparison
import SGPT.Support.Alterations.Geometry.BlowupIntegral

/-!
# Blow-up models of flag ideals (lane BJ-MODEL2, steps R1(c), R1(d))

Source: [BJ22] (`references/bj22-trivval`), §1.2 and §2.1 (proof of `thm:VCarPL`: "the
normalized blow-up `𝒳` of `X × 𝔸¹` along `𝔞` is a test configuration, `𝔞·𝒪_𝒳 = 𝒪_𝒳(D)` with
`D` a vertical Cartier divisor"; any finitely many flag ideals are invertible on a common such
model). Used for `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-model2.tex`.

For a flag ideal `𝔞` on `X` with weight bound `b` let

  `flagModel p 𝔞 b = Bl_{t^b 𝔞}(X × ℙ¹)`,   `flagModelπ : flagModel p 𝔞 b ⟶ X × ℙ¹`

(Hironaka's blow-up `Scheme.IdealSheafData.blowUp` of the ideal sheaf `flagSheaf p 𝔞 b`).

## Main results

* `flagModel_isBlowUp`: the universal property ([Sta, Tag 0806]);
* `flagModel_isIntegral`: the model is integral (de Jong: blow-ups of integral schemes along
  nonzero ideal sheaves are integral);
* `flagModelStructure_isProjective`: the model is projective over `k`, hence proper;
* `isInvertible_comap_flagSheaf`: `(t^b 𝔞)·𝒪_𝒳` is invertible — on the model `𝔞` becomes a
  vertical Cartier divisor;
* `flagModelπ_isIso_restrict`: `flagModelπ` is an isomorphism off the cosupport of `t^b 𝔞`, which
  is contained in the central fibre (`support_flagSheaf_le`);
* `flagModelMap`: the model of `𝔞 𝔟` dominates the model of `𝔞` over `X × ℙ¹`, and
  `exists_common_flagModel`: finitely many flag ideals become invertible on one common model,
  which dominates the model of each of them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.NAPotential.BJModel FlagIdealBound

/-- Blow-ups of integral schemes along ideal sheaves with proper support are integral (de Jong's
`isIntegral_blowup` transported along SGPT.Foundations.Envelope's comparison of the two blow-up
constructions; this is SGPT.Foundations.Envelope's `Scheme.IdealSheafData.isIntegral_blowUp_of_support_ne_top`,
restated here because that module has no compiled object file in the shared build). -/
theorem blowUp_isIntegral {Y : Scheme.{0}} [IsIntegral Y] (D : Y.IdealSheafData)
    (hD : D.support ≠ ⊤) : IsIntegral D.blowUp := by
  let : IsIntegral (SGPT.Support.Alterations.Geometry.BlowupGluing.blowup D) :=
    SGPT.Support.Alterations.Geometry.BlowupIntegral.isIntegral_blowup D hD
  exact IsIntegral.of_isIso (SGPT.Foundations.Envelope.HironakaDeJongBlowupComparison.globalIso D).hom

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (.of k))

/-- **The blow-up model of a flag ideal** ([BJ22, §2.1]): the blow-up of `X × ℙ¹` along
`t^b 𝔞`. Its normalization is the test configuration of `𝔞`. -/
abbrev flagModel (𝔞 : FlagIdeal X) (b : ℤ) : Scheme.{0} := (flagSheaf p 𝔞 b).blowUp

/-- The blow-down morphism `flagModel p 𝔞 b ⟶ X × ℙ¹`. -/
abbrev flagModelπ (𝔞 : FlagIdeal X) (b : ℤ) : flagModel p 𝔞 b ⟶ productLine p :=
  (flagSheaf p 𝔞 b).blowUpπ

/-- The structure morphism of the model over `k`. -/
abbrev flagModelStructure (𝔞 : FlagIdeal X) (b : ℤ) : flagModel p 𝔞 b ⟶ Spec (.of k) :=
  flagModelπ p 𝔞 b ≫ productStructure p

variable (𝔞 : FlagIdeal X) (b : ℤ)

/-- The universal property of the blow-up model. -/
theorem flagModel_isBlowUp : IsBlowUp (flagSheaf p 𝔞 b) (flagModelπ p 𝔞 b) :=
  Scheme.IdealSheafData.blowUp.isBlowUp _

/-- **`(t^b 𝔞)·𝒪` is invertible on the model**: `𝔞` becomes a vertical Cartier divisor. -/
theorem isInvertible_comap_flagSheaf :
    ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔞 b)).IsInvertible :=
  Scheme.IdealSheafData.blowUp.isInvertible_comap_π _

/-- **The model is integral** when `X` is integral and projective over `k`. -/
instance flagModel_isIntegral [IsIntegral X] [IsProjective p] : IsIntegral (flagModel p 𝔞 b) :=
  let := productLine_isIntegral_of_isProjective p
  blowUp_isIntegral _ (support_flagSheaf_ne_top p 𝔞 b)

/-- **The model is projective over `k`** (polynomial projective factorization) when `X` is. -/
theorem flagModelStructure_isProjectiveFactorization [IsProjective p] :
    IsProjectiveFactorization (flagModelStructure p 𝔞 b) :=
  SGPT.Foundations.Envelope.ProjectiveBlowupSequence.blowup_isProjectiveFactorization _ _
    (productStructure_isProjectiveFactorization p
      (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p))

/-- **The model is projective over `k`** (Hironaka's projectivity predicate). -/
instance flagModelStructure_isProjective [IsProjective p] :
    IsProjective (flagModelStructure p 𝔞 b) :=
  SGPT.Foundations.Envelope.NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization _
    (flagModelStructure_isProjectiveFactorization p 𝔞 b)

instance flagModelStructure_isProper [IsProjective p] : IsProper (flagModelStructure p 𝔞 b) :=
  (flagModelStructure_isProjectiveFactorization p 𝔞 b).isProper

instance flagModelπ_isProper [IsProjective p] : IsProper (flagModelπ p 𝔞 b) :=
  Scheme.IdealSheafData.blowUp.isProper_π _

instance flagModel_compactSpace [IsProjective p] : CompactSpace (flagModel p 𝔞 b) :=
  QuasiCompact.compactSpace_of_compactSpace (flagModelStructure p 𝔞 b)

instance flagModel_isSeparated [IsProjective p] : (flagModel p 𝔞 b).IsSeparated :=
  ⟨by
    have h : IsSeparated (flagModelStructure p 𝔞 b ≫ terminal.from (Spec (.of k))) :=
      inferInstance
    simpa only [terminal.comp_from] using h⟩

/-- **The blow-down is an isomorphism off the cosupport of `t^b 𝔞`**, in particular over the
complement of the central fibre (`support_flagSheaf_le`). -/
theorem flagModelπ_isIso_restrict :
    IsIso (flagModelπ p 𝔞 b ∣_ (flagSheaf p 𝔞 b).support.compl) :=
  Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support _

/-- The open set over which the blow-down is an isomorphism contains `X × (ℙ¹ ∖ {0})`. -/
theorem compl_central_le_compl_support :
    (centralIdeal p).support.compl ≤ (flagSheaf p 𝔞 b).support.compl := fun _ hx hx' =>
  hx (support_flagSheaf_le p 𝔞 b hx')

/-! ### Common models -/

section common

variable {𝔞} {𝔟 : FlagIdeal X} {b} {b' : ℤ}

/-- If `t^c 𝔠 = t^b 𝔞 · J` for an ideal sheaf `J`, then `t^b 𝔞` is invertible on the model of
`𝔠` (factors of invertible ideal sheaves are invertible). -/
theorem isInvertible_comap_of_flagSheaf_eq_mul {𝔠 : FlagIdeal X} {c : ℤ}
    {J : (productLine p).IdealSheafData} (h : flagSheaf p 𝔠 c = flagSheaf p 𝔞 b * J) :
    ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔠 c)).IsInvertible := by
  have h' := isInvertible_comap_flagSheaf p 𝔠 c
  rw [h, Scheme.IdealSheafData.comap_mul] at h'
  exact (Scheme.IdealSheafData.IsInvertible.of_mul h').1

/-- **Domination of models**: if `t^c 𝔠 = t^b 𝔞 · J`, the model of `𝔠` maps to the model of
`𝔞` over `X × ℙ¹` (universal property of the blow-up). -/
def flagModelMap {𝔠 : FlagIdeal X} {c : ℤ} {J : (productLine p).IdealSheafData}
    (h : flagSheaf p 𝔠 c = flagSheaf p 𝔞 b * J) : flagModel p 𝔠 c ⟶ flagModel p 𝔞 b :=
  Scheme.IdealSheafData.blowUp.lift _ _ (isInvertible_comap_of_flagSheaf_eq_mul p h)

@[reassoc (attr := simp)]
theorem flagModelMap_π {𝔠 : FlagIdeal X} {c : ℤ} {J : (productLine p).IdealSheafData}
    (h : flagSheaf p 𝔠 c = flagSheaf p 𝔞 b * J) :
    flagModelMap p h ≫ flagModelπ p 𝔞 b = flagModelπ p 𝔠 c :=
  Scheme.IdealSheafData.blowUp.lift_π _ _ _

/-- The model of `𝔞 𝔟` dominates the model of `𝔞`. -/
abbrev flagModelMulLeft (h𝔞 : IsWeightBound 𝔞 b) (h𝔟 : IsWeightBound 𝔟 b') :
    flagModel p (𝔞 * 𝔟) (b + b') ⟶ flagModel p 𝔞 b :=
  flagModelMap p (flagSheaf_mul p h𝔞 h𝔟)

/-- The model of `𝔞 𝔟` dominates the model of `𝔟`. -/
abbrev flagModelMulRight (h𝔞 : IsWeightBound 𝔞 b) (h𝔟 : IsWeightBound 𝔟 b') :
    flagModel p (𝔞 * 𝔟) (b + b') ⟶ flagModel p 𝔟 b' :=
  flagModelMap p ((flagSheaf_mul p h𝔞 h𝔟).trans (mul_comm _ _))

/-- The relation "the model of `(𝔠, c)` dominates the model of `(𝔞, b)` over `X × ℙ¹`, and
`t^b 𝔞` is invertible on it". -/
def Dominates (𝔠 : FlagIdeal X) (c : ℤ) (𝔞 : FlagIdeal X) (b : ℤ) : Prop :=
  ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔠 c)).IsInvertible ∧
    ∃ g : flagModel p 𝔠 c ⟶ flagModel p 𝔞 b, g ≫ flagModelπ p 𝔞 b = flagModelπ p 𝔠 c

theorem dominates_of_flagSheaf_eq_mul {𝔠 : FlagIdeal X} {c : ℤ}
    {J : (productLine p).IdealSheafData} (h : flagSheaf p 𝔠 c = flagSheaf p 𝔞 b * J) :
    Dominates p 𝔠 c 𝔞 b :=
  ⟨isInvertible_comap_of_flagSheaf_eq_mul p h, flagModelMap p h, flagModelMap_π p h⟩

/-- Finitely many flag ideals divide a common one: for flag ideals `𝔞 i` with weight bounds
`b i`, `i < n`, their product `𝔠` (with weight bound `c = ∑ b i`) satisfies
`t^c 𝔠 = t^{b i} 𝔞 i · Jᵢ` for every `i`. -/
theorem exists_common_flagSheaf_factor : ∀ (n : ℕ) (𝔞 : Fin n → FlagIdeal X) (b : Fin n → ℤ),
    (∀ i, IsWeightBound (𝔞 i) (b i)) →
      ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsWeightBound 𝔠 c ∧
        ∀ i, ∃ J : (productLine p).IdealSheafData, flagSheaf p 𝔠 c = flagSheaf p (𝔞 i) (b i) * J
  | 0, _, _, _ => ⟨1, 0, fun l hl => by
      rw [FlagIdeal.one_def]; exact isWeightBound_monomial 0 l hl, fun i => i.elim0⟩
  | n + 1, 𝔞, b, h => by
    obtain ⟨𝔠, c, hc, hfac⟩ := exists_common_flagSheaf_factor n (fun i => 𝔞 i.succ)
      (fun i => b i.succ) (fun i => h i.succ)
    refine ⟨𝔞 0 * 𝔠, b 0 + c, (h 0).mul hc, fun i => ?_⟩
    rw [flagSheaf_mul p (h 0) hc]
    refine Fin.cases ⟨flagSheaf p 𝔠 c, rfl⟩ (fun j => ?_) i
    obtain ⟨J, hJ⟩ := hfac j
    refine ⟨flagSheaf p (𝔞 0) (b 0) * J, ?_⟩
    rw [hJ]
    ring

/-- **Common models of finitely many flag ideals** ([BJ22, §2.1]): for flag ideals `𝔞 i` with
weight bounds `b i`, `i < n`, there is a flag ideal `𝔠` (their product) with weight bound `c` whose
model dominates the model of every `𝔞 i` over `X × ℙ¹`, every `t^{b i} 𝔞 i` being invertible on
it. -/
theorem exists_common_flagModel (n : ℕ) (𝔞 : Fin n → FlagIdeal X) (b : Fin n → ℤ)
    (h : ∀ i, IsWeightBound (𝔞 i) (b i)) :
    ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsWeightBound 𝔠 c ∧ ∀ i, Dominates p 𝔠 c (𝔞 i) (b i) := by
  obtain ⟨𝔠, c, hc, hfac⟩ := exists_common_flagSheaf_factor p n 𝔞 b h
  exact ⟨𝔠, c, hc, fun i => (hfac i).elim fun _ hJ => dominates_of_flagSheaf_eq_mul p hJ⟩

end common

end SGPT.NAPotential.BJ
