import SGPT.Checks.Comparison.TraceGFSectionPullback
import SGPT.Foundations.Envelope.AlgGeom.InvertibleBaseIdealTransport

/-! Actual restricted raw sections and canonical first-power transport, with whole ideal identities.
Source `thm:comp_traceop`; blueprint `trace-raw-section-transport.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open AlgebraicGeometry CategoryTheory Opposite SGPT.Foundations.Schemes
open Scheme.Modules SGPT.Support.ModularCurves
open SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.InvertibleSheafBaseIdeal

local instance (X : Scheme.{0}) : ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

variable {X : Scheme.{0}}

/-- An actual original sheaf iso preserves the ENTIRE same original section ideal. -/
theorem sectionZeroIdealSheaf_map_iso {M P : X.Modules} (a : LineBundleAtlas M)
    (b : LineBundleAtlas P) (e : M ≅ P) (s : Γ(M, ⊤)) :
    sectionZeroIdealSheaf b (e.hom.val.app (op ⊤) s) = sectionZeroIdealSheaf a s := by
  rw [sectionZeroIdealSheaf_eq_sectionIdeal, sectionZeroIdealSheaf_eq_sectionIdeal]
  ext U r
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨(dualMapObj e.hom).val.app (op U.1) d,
      (InvertibleBaseIdealTransport.sectionEvaluation_map e.hom s U.1 d).symm⟩
  · rintro ⟨d, rfl⟩
    let t : Γ(P, ⊤) := e.hom.val.app (op ⊤) s
    have ht : e.inv.val.app (op ⊤) t = s := by
      have h := congrArg (fun q : M ⟶ M => q.val.app (op ⊤) s) e.hom_inv_id
      exact h
    refine ⟨(dualMapObj e.inv).val.app (op U.1) d, ?_⟩
    have h := InvertibleBaseIdealTransport.sectionEvaluation_map e.inv t U.1 d
    rw [ht] at h
    exact h.symm

/-- The canonical ACTUAL first-power section, using the actual tensor-unit inverse. -/
def rawPowerOneLift (P : X.Modules) (s : Γ(P, ⊤)) : bundlePowerGlobalSections P 1 :=
  (bundleTensorLeftUnitIso P).inv.val.app (op ⊤) s

/-- The actual original tensor-unit map reads back the literal SAME original section. -/
theorem rawPowerOneLift_readback (P : X.Modules) (s : Γ(P, ⊤)) :
    (bundleTensorLeftUnitIso P).hom.val.app (op ⊤) (rawPowerOneLift P s) = s := by
  exact congrArg (fun q : P ⟶ P => q.val.app (op ⊤) s) (bundleTensorLeftUnitIso P).inv_hom_id

/-- Genuine actual nonzero raw sections stay nonzero under the actual canonical lift. -/
theorem rawPowerOneLift_ne_zero (P : X.Modules) {s : Γ(P, ⊤)} (hs : s ≠ 0) :
    rawPowerOneLift P s ≠ 0 := by
  intro hzero
  have h := rawPowerOneLift_readback P s
  rw [hzero, map_zero] at h
  exact hs h.symm

/-- The entire original zero ideal remains unchanged by the actual first-power lift. -/
theorem sectionZeroIdealSheaf_rawPowerOneLift {P : X.Modules} (b : LineBundleAtlas P)
    (s : Γ(P, ⊤)) :
    sectionZeroIdealSheaf (b.tensorPower 1) (rawPowerOneLift P s) = sectionZeroIdealSheaf b s := by
  have h := sectionZeroIdealSheaf_map_iso (b.tensorPower 1) b (bundleTensorLeftUnitIso P)
    (rawPowerOneLift P s)
  exact h.symm.trans (congrArg (sectionZeroIdealSheaf b) (rawPowerOneLift_readback P s))

/-- The WHOLE actual pulled family, canonically expressed in first degree,
has exactly the actual original inverse-image ideal. Zero terms are retained. -/
theorem actual_restricted_firstPower_family_ideal {Y : Scheme.{0}} (i : Y ⟶ X)
    {M : X.Modules} (a : LineBundleAtlas M) {J : Type} (s : J → Γ(M, ⊤)) :
    (⨆ j, sectionZeroIdealSheaf ((a.nativePullback i).tensorPower 1)
      (rawPowerOneLift ((Scheme.Modules.pullback i).obj M) (affinePullbackUnitTop i M (s j)))) =
        (⨆ j, sectionZeroIdealSheaf a (s j)).comap i := by
  simp_rw [sectionZeroIdealSheaf_rawPowerOneLift]
  exact (sectionFamilyIdeal_comap i a s).symm

end SGPT.NAPotential.TraceComparison
