import SGPT.Unibranch.HironakaG10GnHGF
import SGPT.Unibranch.HironakaG10FrHF1

/-!
# `hF1` without named input: the Frisch route closed (lane G10GN, run 0081)

`HironakaG10GnHGF.hGF_holds` discharges the generic-flatness hypothesis `hGF` of lane G10FR/G10R3's splice
`HironakaG10FrHF1.hF1_of_hGF` and `HironakaG10FrHF1.hironakaFlattening_of_hGF`:

* **`hGF_all`**: `hGF` in exactly the binder of `hF1_of_hGF` (all dimensions, fibre point `0`);
* **`hF1`**: the hypothesis `hF1` of `HironakaG10RdFinal.hironakaFlattening_of_frisch` (the relative non-flat locus
  of an analytic subset is analytic, for proper stages with compact source);
* **`hironakaFlattening_of_hT`**: Hironaka's flattening theorem from `hT` alone.

No named input. BP: hironaka-g10gn-hgf.tex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.HironakaG10GnHF1

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending OkaRelationSheaf
  HironakaG10LocFibreOpen HironakaG10LocRelative HironakaSingularModuleSheafStalk
open SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.HironakaG10HirGermFlattener
  SGPT.Unibranch.HironakaG10HirLocalFlattener
  SGPT.Unibranch.HironakaG10RelativeNonflatStrata
  SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10ChowFlatteningDriver
  SGPT.Unibranch.HironakaG10ChowCentreMachine
  SGPT.Unibranch.HironakaG10ChowLeavingRounds
  SGPT.Unibranch.HironakaG10SourceCSet
  SGPT.Unibranch.HironakaG10RdLemma455
  SGPT.Unibranch.HironakaG10RdTheoremI
  SGPT.Unibranch.HironakaG10RdPermRun
  SGPT.Unibranch.HironakaG10RdEndToEnd
  SGPT.Unibranch.HironakaG10EpS3
  SGPT.Unibranch.HironakaG10ChowFlatteningReduction
  SGPT.Unibranch.HironakaG10TmFlattenerCover
  SGPT.Unibranch.HironakaG10RdMacroStep
  SGPT.Unibranch.HironakaG10SbFlattenerSupportGerm
  SGPT.Unibranch.EmbeddedIdealBlowupNonunitLocus
  SGPT.Unibranch.HironakaG10MwWindowFamily SGPT.Unibranch.HironakaG10FrRouteG
  SGPT.Unibranch.HironakaG10GfModStart SGPT.Unibranch.HironakaG10FrNativeIV9

/-- `hGF` in the binder of `HironakaG10FrHF1.hF1_of_hGF`. -/
theorem hGF_all : ∀ (m t : ℕ) (p₀ : ComplexModel m) (P : Set (ComplexModel m)), IsAnalyticNear P p₀ → p₀ ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, (0 : ComplexModel t)) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p 0 :=
  fun _ _ p₀ => SGPT.Unibranch.HironakaG10GnHGF.hGF_holds 0 p₀

/-- **`hF1` of `HironakaG10RdFinal.hironakaFlattening_of_frisch`, with no named input**: for a proper stage with
compact source, the relative non-flat locus of an analytic subset is analytic. -/
theorem hF1 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
    ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A) :=
  SGPT.Unibranch.HironakaG10FrHF1.hF1_of_hGF hGF_all

/-- **Hironaka's flattening theorem from `hT` alone** (the Frisch route `hF1` closed by `hGF_all`). -/
theorem hironakaFlattening_of_hT
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z) :
    HironakaFlattening :=
  SGPT.Unibranch.HironakaG10FrHF1.hironakaFlattening_of_hGF hGF_all hT

end SGPT.Unibranch.HironakaG10GnHF1
