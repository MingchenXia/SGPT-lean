import SGPT.Projective.OkounkovOriginalPerturbAbsorptionUnits
import SGPT.Projective.OkounkovOriginalMultiplierExponentOrder
import SGPT.Projective.OkounkovOriginalLeftUnitMultiplier
import SGPT.Okounkov.OkoNSAlgebraic

/-! SAME original entire raw multiplier values under actual uniform residue/twist absorption, no source-weight normalization.
Blueprint: okounkov-original-perturb-value-inclusion.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalPerturbValueInclusion
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation SGPT.Projective.NumEq.AlgebraicCurveDegree
variable {X : Scheme.{0}} [IsIntegral X]

private theorem unitSection_value {n : ℕ} {M : X.Modules} (b : LineBundleAtlas M) (g : ℕ)
    (σ : bundlePowerGlobalSections M g)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c) :
    plainSectionValue v c ((b.tensorPower g).tensorPower 1) (originalSectionUnit σ)=sectionValue v c b g σ := by
  rw [ValGen2.sectionValue_eq_plainSectionValue (a:=b) (v:=v) hc g σ]
  let a := b.tensorPower g
  let U := a.opens (a.centerIndex c)
  let : Nonempty U := ⟨⟨c,a.centerIndex_mem c⟩⟩
  change v (globalSectionToFunctionField ((a.frame (a.centerIndex c)).tensorPower 1) (originalSectionUnit σ))=
    v (globalSectionToFunctionField (a.frame (a.centerIndex c)) σ)
  exact congrArg v (congrArg (X.germToFunctionField U) (originalSectionUnit_coefficients σ (a.frame (a.centerIndex c)) (𝟙 U)))

variable (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (E : ClosedProjectiveEmbedding f) [IsSeparated f] [QuasiCompact f]
local instance perturbValueInclusionTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbValueInclusionCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance perturbValueInclusionManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

private theorem unitSection_multiplier {M : X.Modules} (b : LineBundleAtlas M) (g : ℕ) (hg : 0<g)
    (ψ : SchemeComplexPoint f → EReal) (σ : bundlePowerGlobalSections M g)
    (hσ : IsPlainIdealSection f n E (multiplierIdeal (n:=n) (g:ℝ) ψ) σ) :
    IsPlainIdealSection f n E (multiplierIdeal (n:=n) (g:ℝ) ψ) (originalSectionUnit σ) := by
  let η := fun x => (g:EReal)*ψ x
  have heq : multiplierIdeal (n:=n) (1:ℝ) η=multiplierIdeal (n:=n) (g:ℝ) ψ := by
    simpa only [Nat.mul_one,Nat.cast_one] using ValGen2.multiplierIdeal_natCast_mul f n ψ hg zero_lt_one
  have hσ₁ : IsPlainIdealSection f n E (multiplierIdeal (n:=n) (1:ℝ) η) σ := by rw [heq];exact hσ
  have hunit : IsIdealSection f n E (multiplierIdeal (n:=n) (1:ℝ) η) 1 (originalSectionUnit σ) :=
    (OriginalLeftUnitMultiplier.originalLeftUnitHom_multiplier_iff f n E (originalSectionUnit σ) η 1).mp
      (by rw [originalSectionUnit_hom];exact hσ₁)
  have hplain := OriginalIdealProducts.isPlainMultiplierIdealSection_of_isIdealSection f n E
    (b.tensorPower g) η 1 (originalSectionUnit σ) (by simpa only [Nat.cast_one] using hunit)
  simp only [Nat.cast_one] at hplain
  rw [heq] at hplain
  exact hplain

variable [Nonempty (SchemeComplexPoint f)] {L T A : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (aA : LineBundleAtlas A)

include aT in
/-- Actual ordinary source sections land in the LITERAL target unit-twisted H0 with SAME value and correct multiplier. -/
theorem exists_absorbed_unitTwistedSection (H : SchemeLineBundleMetric f n E L)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (q p g r : ℕ) (hq : 0<q) (hg : 0<g)
    (bS : LineBundleAtlas (bundleTensor T (bundleTensorPower L (q*g+r))))
    (bF : LineBundleAtlas (bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g))))
    (s : Γ(bundleTensor T (bundleTensorPower L (q*g+r)),⊤)) (hs : s≠0)
    (hI : IsPlainIdealSection f n E (multiplierIdeal (n:=n) ((q*g+r:ℕ):ℝ) φ) s)
    (t : Γ(bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g)),⊤))
    (ht : c∉(sectionZeroIdealSheaf bF t).support) :
    ∃ σ : Γ(bundleTensor (SheafOfModules.unit X.ringCatSheaf)
        (bundleTensorPower (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) g),⊤),
      σ≠0 ∧ IsPlainIdealSection f n E (multiplierIdeal (n:=n) (g:ℝ) (fun x => (q:EReal)*φ x)) σ ∧
      plainSectionValue v c (((OkoNS.perturbAtlas a aA q p).tensorPower g).tensorPower 1) σ=plainSectionValue v c bS s := by
  let bM := OkoNS.perturbAtlas a aA q p
  have hle := OriginalMultiplierExponentOrder.multiplierIdeal_le_of_nat_le f n E a H hφ (q*g+r) (q*g)
    (Nat.mul_pos hq hg) (by omega)
  have hI' : IsPlainIdealSection f n E (multiplierIdeal (n:=n) ((q*g:ℕ):ℝ) φ) s :=
    fun U e x hx => hle x _ (hI U e x hx)
  obtain ⟨τ,hτ,hvalue,hτI⟩ := OriginalPerturbAbsorption.exists_unit_absorptionSection a aT aA f n E v hc
    q p g r bS bF bM φ ((q*g:ℕ):ℝ) s hs hI' t ht
  have heq := ValGen2.multiplierIdeal_natCast_mul f n φ hq hg
  have hτI' : IsPlainIdealSection f n E (multiplierIdeal (n:=n) (g:ℝ) (fun x => (q:EReal)*φ x)) τ := by
    rw [heq]
    simpa only [Nat.cast_mul] using hτI
  exact ⟨originalSectionUnit τ,(originalSectionUnit_ne_zero_iff τ).mpr hτ,
    unitSection_multiplier f n E bM g hg (fun x => (q:EReal)*φ x) τ hτI',
    (unitSection_value bM g τ v hc).trans hvalue⟩

include aT in
/-- ENTIRE literal original raw value inclusion, manufactured from a genuine ordinary unit factor. -/
theorem twistedMultiplierValues_subset_unitPerturb_of_factor (H : SchemeLineBundleMetric f n E L)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (q p g r : ℕ) (hq : 0<q) (hg : 0<g)
    (bS : LineBundleAtlas (bundleTensor T (bundleTensorPower L (q*g+r))))
    (bF : LineBundleAtlas (bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g))))
    (t : Γ(bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g)),⊤))
    (ht : c∉(sectionZeroIdealSheaf bF t).support) :
    AlgebraicValuation.twistedMultiplierValues f n E v c (q*g+r) bS φ ⊆
    AlgebraicValuation.twistedMultiplierValues (T:=SheafOfModules.unit X.ringCatSheaf)
      (L:=bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) f n E v c g
      (((OkoNS.perturbAtlas a aA q p).tensorPower g).tensorPower 1) (fun x => (q:EReal)*φ x) := by
  rintro x ⟨s,hs,hI,hx⟩
  have hk : 0<q*g+r := (Nat.mul_pos hq hg).trans_le (by omega)
  have hI' := hI.resolve_left hk.ne'
  obtain ⟨σ,hσ,hσI,hvalue⟩ := exists_absorbed_unitTwistedSection f n E a aT aA H hφ v hc q p g r hq hg bS bF s hs hI' t ht
  have hvec := plainSectionVector_eq_of_value_eq (v:=v) c c
    (((OkoNS.perturbAtlas a aA q p).tensorPower g).tensorPower 1) bS σ s hσ hs hvalue
  exact ⟨σ,hσ,Or.inr hσI,hx.trans hvec.symm⟩

include a aT in
/-- ONE actual threshold BEFORE ALL metrics/weights/positive numerator multiples/high degrees/residues/atlases/centres, full raw values. -/
theorem exists_uniform_perturb_multiplier_value_inclusions (P : SGPT.LineBundle.AmplePolarization f A)
    (q : ℕ) (hq : 0<q) :
    ∃ B : ℕ, 0<B ∧ ∀ p₀ : ℕ, 0<p₀ → ∀ g : ℕ, B≤g → ∀ r : Fin q,
      ∀ (H : SchemeLineBundleMetric f n E L) (φ : SchemeComplexPoint f → EReal)
        (_hφ : IsThetaPshPotential (H.curvature a).val φ)
        (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X) (_hc : IsNonnegAt v c)
        (bS : LineBundleAtlas (bundleTensor T (bundleTensorPower L (q*g+r.val)))),
      AlgebraicValuation.twistedMultiplierValues f n E v c (q*g+r.val) bS φ ⊆
      AlgebraicValuation.twistedMultiplierValues (T:=SheafOfModules.unit X.ringCatSheaf)
        (L:=bundleTensor (bundleTensorPower L q) (bundleTensorPower A (P.power*p₀))) f n E v c g
        (((OkoNS.perturbAtlas a aA q (P.power*p₀)).tensorPower g).tensorPower 1) (fun x => (q:EReal)*φ x) := by
  obtain ⟨B,hB,hunit⟩ := OriginalPerturbAbsorptionUnits.exists_perturb_absorption_unit_factors f a aT aA P q
  refine ⟨B,hB,?_⟩
  intro p₀ hp₀ g hg r H φ hφ v c hc bS
  let bF := pairwiseTensorAtlas (ValGen2.dualAtlas (pairwiseTensorAtlas aT (a.tensorPower r.val)))
    (aA.tensorPower ((P.power*p₀)*g))
  obtain ⟨t,ht⟩ := hunit p₀ hp₀ g hg r c
  exact twistedMultiplierValues_subset_unitPerturb_of_factor f n E a aT aA H hφ v hc q (P.power*p₀) g r.val hq
    (hB.trans_le hg) bS bF t (ht bF)
end SGPT.Okounkov.OriginalPerturbValueInclusion
