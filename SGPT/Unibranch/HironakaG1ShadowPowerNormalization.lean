import SGPT.Unibranch.OriginalNativeShadowInvariantCentre
import SGPT.Foundations.Analysis.Pending.HironakaG1UniformFamilyPowerCuts

/-! Actual compact-shadow normalization using the SAME attained anchor.
Blueprint FIRST: hironaka-g1-shadow-power-normalization.tex.
The new level is a TRUE powered value; no unequal-mark level equality.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.HironakaG1ShadowPowerNormalization
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  OriginalNativeHSCompactShadowWindows OriginalNativeShadowInvariantCentre
  HironakaG11VanishingWindows HironakaG11VanishingPrincipalization HironakaG11CompatibleAnalyticCover
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres
  HironakaActualPowerBoundaryExponents HironakaG1UniformFamilyPowerCuts
open ResolutionInvariantSpec (IsInvDomain)

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left} (M : Maximum X K) (hK : IsCompact K)
local notation "H" => originalStalkHS X M.point
local notation "n" => H 1-1
local notation "F" => OriginalNativeShadowInvariantCentre.centres M hK

def anchorIndex : (M.windows hK).ι := (level_attained M hK).choose

def anchorPoint : ((M.windows hK).window (anchorIndex M hK)).carrier :=
  (level_attained M hK).choose_spec.choose

theorem anchor_spec : anchorPoint M hK∈piece M hK (anchorIndex M hK) ∧
    value M hK (anchorIndex M hK) (anchorPoint M hK).val=level M hK :=
  (level_attained M hK).choose_spec.choose_spec

def powerRecord (e : ℕ) (i : (M.windows hK).ι) : MarkedIdeal n (Amb (M.windows hK).window i) :=
  powerMarked (record M hK i) e

def powerValue (e : ℕ) (i : (M.windows hK).ι) (y : ((M.windows hK).window i).ambient) : ValTy n :=
  (invariant M).toResolutionInvariant.inv (powerRecord M hK e i) BlowupTower.refl y

def powerLevel (e : ℕ) : ValTy n := powerValue M hK e (anchorIndex M hK) (anchorPoint M hK).val

private theorem power_cosupp_eq (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι) :
    (powerRecord M hK e i).cosupp=(record M hK i).cosupp :=
  powerMarked_cosupp (record M hK i) (domain M hK i) he


/-- Entire further power is a genuine power of the ORIGINAL raw native
record, for the real common-mark comparison consumer. -/
theorem power_record_eq_raw_power (e : ℕ) (i : (M.windows hK).ι) :
    powerRecord M hK e i=powerMarked ((M.windows hK).record i)
      (OriginalNativeShadowInvariantCentre.exponent M hK i*e) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · rfl
  · exact MarkedIdealOperationsTransform.idealPow_idealPow
      ((M.windows hK).native i).1.isWellFormed.isCoherent
      (OriginalNativeShadowInvariantCentre.exponent M hK i) e
  · exact Nat.mul_assoc _ _ _

theorem power_raw_exponent_pos (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι) :
    1≤OriginalNativeShadowInvariantCentre.exponent M hK i*e :=
  Nat.mul_pos (exponent_pos M hK i) he

/-- The actual candidate pieces keep the SAME footprints/native K maps. -/
def powerPiece (e : ℕ) (i : (M.windows hK).ι) : Set ((M.windows hK).window i).carrier :=
  (Subtype.val : ((M.windows hK).window i).carrier → ((M.windows hK).window i).ambient) ⁻¹'
    ((powerRecord M hK e i).cosupp ∩ (M.windows hK).footprint i) ∩
      ((M.windows hK).window i).toLocalEmbedding.toPoint ⁻¹' K

theorem power_piece_eq (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι) :
    powerPiece M hK e i=piece M hK i := by
  unfold powerPiece piece
  rw [power_cosupp_eq M hK e he i]

/-- ALL actual cosupport points/windows, including outside K. -/
theorem power_level_comparisons (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι)
    (y : ((M.windows hK).window i).ambient) (hy : y∈(record M hK i).cosupp) :
    (value M hK i y<level M hK ↔ powerValue M hK e i y<powerLevel M hK e) ∧
    (value M hK i y≤level M hK ↔ powerValue M hK e i y≤powerLevel M hK e) ∧
    (value M hK i y=level M hK ↔ powerValue M hK e i y=powerLevel M hK e) := by
  have hA : (anchorPoint M hK).val∈(record M hK (anchorIndex M hK)).cosupp:=
    (anchor_spec M hK).1.1.1
  have h:=uniform_power_comparisons
    (X := fun j=>Amb (M.windows hK).window j) (record M hK) (domain M hK)
    (fun j=>(record_hs M hK j).2.2.1)
    (fun a b=>(record_mark M hK a).trans (record_mark M hK b).symm)
    e he i (anchorIndex M hK) BlowupTower.refl BlowupTower.refl trivial trivial y hy
    (anchorPoint M hK).val hA
  change (value M hK i y<value M hK (anchorIndex M hK) (anchorPoint M hK).val ↔
      powerValue M hK e i y<powerLevel M hK e) ∧
    (value M hK i y≤value M hK (anchorIndex M hK) (anchorPoint M hK).val ↔
      powerValue M hK e i y≤powerLevel M hK e) ∧
    (value M hK i y=value M hK (anchorIndex M hK) (anchorPoint M hK).val ↔
      powerValue M hK e i y=powerLevel M hK e) at h
  rw [(anchor_spec M hK).2] at h
  exact h

theorem power_level_bound_piece (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι)
    (c : ((M.windows hK).window i).carrier) (hc : c∈powerPiece M hK e i) :
    powerValue M hK e i c.val≤powerLevel M hK e := by
  rw [power_piece_eq M hK e he i] at hc
  exact ((power_level_comparisons M hK e he i c.val hc.1.1).2.1).mp
    (level_bound_piece M hK i c hc)

theorem power_level_attained (e : ℕ) (he : 1≤e) :
    ∃i,∃c : ((M.windows hK).window i).carrier,
      c∈powerPiece M hK e i ∧ powerValue M hK e i c.val=powerLevel M hK e := by
  refine ⟨anchorIndex M hK,anchorPoint M hK,?_,rfl⟩
  rw [power_piece_eq M hK e he]
  exact (anchor_spec M hK).1

def powerGoodOpen (e : ℕ) (i : (M.windows hK).ι) : Opens ((M.windows hK).window i).ambient :=
  ⟨interior {y | y∉(powerRecord M hK e i).cosupp ∨ powerValue M hK e i y≤powerLevel M hK e},
    isOpen_interior⟩

theorem powerGoodOpen_eq (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι) :
    powerGoodOpen M hK e i=goodOpen M hK i := by
  apply Opens.ext
  change interior {y | y∉(powerRecord M hK e i).cosupp ∨ powerValue M hK e i y≤powerLevel M hK e}=
    interior {y | y∉(record M hK i).cosupp ∨ value M hK i y≤level M hK}
  congr 1
  ext y
  rw [power_cosupp_eq M hK e he i]
  by_cases hy : y∈(record M hK i).cosupp
  · simpa only [mem_ofPred_eq,hy,not_true_eq_false,false_or] using
      (power_level_comparisons M hK e he i y hy).2.1.symm
  · simp only [mem_ofPred_eq,hy,not_false_eq_true,true_or]

def powerAmbientCentre (e : ℕ) (i : (M.windows hK).ι) : Set ((M.windows hK).window i).ambient :=
  {y | y∈(powerRecord M hK e i).cosupp ∧ powerValue M hK e i y=powerLevel M hK e}

theorem power_ambient_centre_eq (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι) :
    powerAmbientCentre M hK e i={y | y∈(record M hK i).cosupp ∧ value M hK i y=level M hK} := by
  unfold powerAmbientCentre
  rw [power_cosupp_eq M hK e he i]
  ext y
  constructor
  · rintro ⟨hy,hv⟩
    exact ⟨hy,((power_level_comparisons M hK e he i y hy).2.2).mpr hv⟩
  · rintro ⟨hy,hv⟩
    exact ⟨hy,((power_level_comparisons M hK e he i y hy).2.2).mp hv⟩

/-- The SAME existing good-open window and physical centre point type. -/
def powerCentre (e : ℕ) (i : (M.windows hK).ι) : Set ((F).window i) :=
  (Subtype.val : (F).window i → ((M.windows hK).window i).ambient) ⁻¹' powerAmbientCentre M hK e i

theorem power_centre_eq (e : ℕ) (he : 1≤e) (i : (M.windows hK).ι) :
    powerCentre M hK e i=(F).centre i := by
  change (Subtype.val : (F).window i → ((M.windows hK).window i).ambient) ⁻¹' powerAmbientCentre M hK e i=
    (Subtype.val : (F).window i → ((M.windows hK).window i).ambient) ⁻¹'
      {y | y∈(record M hK i).cosupp ∧ value M hK i y=level M hK}
  rw [power_ambient_centre_eq M hK e he i]
  rfl

def powerSupport (e : ℕ) : Set X.obj.left :=
  ⋃i,((F).windowMap i).hom.left.base ''
    ((Subtype.val : (F).windowCarrier i → (F).window i) ⁻¹' powerCentre M hK e i)

theorem power_support_eq (e : ℕ) (he : 1≤e) : powerSupport M hK e=(F).support := by
  unfold powerSupport
  simp_rw [power_centre_eq M hK e he]
  rfl

private theorem common_mark_pos : 0<commonMark M hK := by
  let : Fintype (M.windows hK).ι:=Fintype.ofFinite (M.windows hK).ι
  exact HironakaG11InvCommonMark.prodMark_pos (fun j=>((M.windows hK).record j).d)
    (fun j=>((M.windows hK).native j).1.one_le_d)

/-- Numerical product marks + ACTUAL own support/opens preserved on both
sides; no equality of two independent levels/supports inferred. -/
theorem common_product_mark {L : Set X.obj.left} (N : Maximum X L) (hL : IsCompact L) :
    0<commonMark M hK ∧ 0<commonMark N hL ∧
    (∀i,(powerRecord M hK (commonMark N hL) i).d=commonMark M hK*commonMark N hL) ∧
    (∀j,(powerRecord N hL (commonMark M hK) j).d=commonMark M hK*commonMark N hL) ∧
    powerSupport M hK (commonMark N hL)=(F).support ∧
    powerSupport N hL (commonMark M hK)=(centres N hL).support ∧
    (∀i,powerGoodOpen M hK (commonMark N hL) i=goodOpen M hK i) ∧
    (∀j,powerGoodOpen N hL (commonMark M hK) j=goodOpen N hL j) := by
  have hp:=common_mark_pos M hK
  have hq:=common_mark_pos N hL
  refine ⟨hp,hq,?_,?_,power_support_eq M hK _ hq,power_support_eq N hL _ hp,
    (fun i=>powerGoodOpen_eq M hK _ hq i),(fun j=>powerGoodOpen_eq N hL _ hp j)⟩
  · intro i
    change (record M hK i).d*commonMark N hL=_
    rw [record_mark]
  · intro j
    change (record N hL j).d*commonMark M hK=_
    rw [record_mark,Nat.mul_comm]

end
end SGPT.Unibranch.HironakaG1ShadowPowerNormalization
