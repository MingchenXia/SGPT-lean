import SGPT.Okounkov.SchemeProjectiveOriginalFlag
import SGPT.Okounkov.SchemeOriginalSectionFrameIndependence
import SGPT.AlmostSemigroup.Basic

/-!
# The actual original graded section semigroup

Literal nonzero section witnesses, genuine SAME-frame products and actual full
natural vectors manufacture additive closure. Existing source stalk-unit frame
independence and the original graded slice API retain the exact original data.
No full lattice generation, cone bound, rank or twisted Gamma is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionSemigroupTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionSemigroupCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Literal actual original section witnesses, with internally proved additive closure. -/
def schemeProjectiveSectionSemigroup {L : X.Modules} (a : LineBundleAtlas L) :
    AddSubsemigroup ((Fin n → ℤ) × ℤ) := by
  letI := E.isSeparated
  letI := E.quasiCompact
  let ω := schemeProjectiveTNKahlerBackground f n E
  let p := (schemeProjectiveOriginalFlagPoint f n E ω Y hY).val
  refine
    { carrier := {z | ∃ (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0),
        z = ((fun i => (schemeFubiniStudySectionVector f n E Y hY a m s hs i : ℤ)), (m : ℤ))}
      add_mem' := ?_ }
  rintro z w ⟨m, s, hs, rfl⟩ ⟨k, t, ht, rfl⟩
  let u := atlasPowerGlobalMul a m k s t
  have hu : u ≠ 0 := schemePointPowerGlobalMul_ne_zero f n p a m k s t hs ht
  have hv := schemeOriginalFlagSectionVector_mul f n E ω Y hY a m k s t hs ht
  change schemeFubiniStudySectionVector f n E Y hY a (m + k) u hu =
    schemeFubiniStudySectionVector f n E Y hY a m s hs +
      schemeFubiniStudySectionVector f n E Y hY a k t ht at hv
  refine ⟨m + k, u, hu, ?_⟩
  rw [hv]
  ext i <;> simp

/-- The actual nonzero degree-zero unit has precisely the whole zero vector. -/
theorem schemeProjectiveSectionSemigroup_zero_mem {L : X.Modules} (a : LineBundleAtlas L) :
    (0 : (Fin n → ℤ) × ℤ) ∈ schemeProjectiveSectionSemigroup f n E Y hY a := by
  let := E.isSeparated
  let := E.quasiCompact
  let ω := schemeProjectiveTNKahlerBackground f n E
  have hs := schemeOriginalFlagSectionOne_ne_zero f n E ω Y hY a
  have hv : schemeFubiniStudySectionVector f n E Y hY a 0 (bundlePowerGlobalOne L) hs = 0 :=
    schemeOriginalFlagSectionVector_one f n E ω Y hY a
  refine ⟨0, bundlePowerGlobalOne L, hs, ?_⟩
  rw [hv]
  rfl

/-- Every actual semigroup coordinate and degree is genuinely nonnegative. -/
theorem schemeProjectiveSectionSemigroup_nonneg {L : X.Modules} (a : LineBundleAtlas L)
    (z : (Fin n → ℤ) × ℤ) (hz : z ∈ schemeProjectiveSectionSemigroup f n E Y hY a) :
    (∀ i, 0 ≤ z.1 i) ∧ 0 ≤ z.2 := by
  obtain ⟨m, s, hs, rfl⟩ := hz
  exact ⟨fun _ => Int.natCast_nonneg _, Int.natCast_nonneg _⟩

/-- The EXISTING graded slice has precisely the actual same-degree section witnesses. -/
theorem schemeProjectiveSectionSemigroup_mem_slice {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (u : Fin n → ℤ) :
    u ∈ SGPT.AlmostSemigroup.slice
        (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) (m : ℤ) ↔
      ∃ (s : bundlePowerGlobalSections L m) (hs : s ≠ 0),
        u = fun i => (schemeFubiniStudySectionVector f n E Y hY a m s hs i : ℤ) := by
  change (∃ (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
      (u, (m : ℤ)) = ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ))) ↔ _
  constructor
  · rintro ⟨k, s, hs, h⟩
    have hd : (m : ℤ) = (k : ℤ) := congrArg Prod.snd h
    have hk : m = k := by exact_mod_cast hd
    subst k
    exact ⟨s, hs, congrArg Prod.fst h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨m, s, hs, Prod.ext h rfl⟩

/-- Actual original stalk-unit frame independence gives equality of the WHOLE graded semigroup. -/
theorem schemeProjectiveSectionSemigroup_atlas_independent {L : X.Modules}
    (a b : LineBundleAtlas L) :
    schemeProjectiveSectionSemigroup f n E Y hY a =
      schemeProjectiveSectionSemigroup f n E Y hY b := by
  let := E.isSeparated
  let := E.quasiCompact
  have hv (c d : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) :
      schemeFubiniStudySectionVector f n E Y hY c m s hs =
        schemeFubiniStudySectionVector f n E Y hY d m s hs :=
    schemeOriginalFlagSectionVector_atlas_independent f n E
      (schemeProjectiveTNKahlerBackground f n E) Y hY c d m s hs
  ext z
  constructor
  · rintro ⟨m, s, hs, hz⟩
    refine ⟨m, s, hs, ?_⟩
    rw [← hv a b m s hs]
    exact hz
  · rintro ⟨m, s, hs, hz⟩
    refine ⟨m, s, hs, ?_⟩
    rw [← hv b a m s hs]
    exact hz

/-- The ACTUAL degree slice is in genuine bijection with the whole original finite-value set. -/
def schemeProjectiveSectionSliceEquivValues {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.AlmostSemigroup.slice
        (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) (m : ℤ) ≃
      schemeOriginalFlagSectionValues f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a m := by
  letI := E.isSeparated
  letI := E.quasiCompact
  refine Equiv.ofBijective (fun u => ⟨((toLex u.val : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))), ?_⟩)
    ⟨?_, ?_⟩
  · obtain ⟨s, hs, hu⟩ := (schemeProjectiveSectionSemigroup_mem_slice f n E Y hY a m u.val).mp u.property
    refine ⟨s, hs, ?_⟩
    rw [schemeFubiniStudySectionValue_vector f n E Y hY a m s hs, hu]
  · intro u v h
    apply Subtype.ext
    have hlex : toLex u.val = toLex v.val := WithTop.coe_injective (congrArg Subtype.val h)
    exact congrArg (ofLex : Lex (Fin n → ℤ) → Fin n → ℤ) hlex
  · rintro ⟨v, hv⟩
    obtain ⟨s, hs, hvalue⟩ := hv
    refine ⟨⟨(fun i => (schemeFubiniStudySectionVector f n E Y hY a m s hs i : ℤ)),
      (schemeProjectiveSectionSemigroup_mem_slice f n E Y hY a m _).mpr ⟨s, hs, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (schemeFubiniStudySectionValue_vector f n E Y hY a m s hs).symm.trans hvalue

/-- Genuine projective H0 and the actual finite-leaf producer make EVERY degree slice finite. -/
theorem schemeProjectiveSectionSemigroup_slice_finite {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    (SGPT.AlmostSemigroup.slice
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) (m : ℤ)).Finite := by
  let := E.isSeparated
  let := E.quasiCompact
  let := (schemeFubiniStudySectionValues_finite f n E Y hY a m).to_subtype
  let : Finite (SGPT.AlmostSemigroup.slice
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) (m : ℤ)) :=
    Finite.of_equiv _ (schemeProjectiveSectionSliceEquivValues f n E Y hY a m).symm
  exact Set.toFinite _

/-- The literal source semigroup slice counts the EXACT original structural section dimension. -/
theorem schemeProjectiveSectionSemigroup_slice_card_eq_finrank {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L m)
    Nat.card (SGPT.AlmostSemigroup.slice
        (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) (m : ℤ)) =
      Module.finrank ℂ (bundlePowerGlobalSections L m) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  exact (Nat.card_congr (schemeProjectiveSectionSliceEquivValues f n E Y hY a m)).trans
    (schemeFubiniStudySectionValues_card_eq_finrank f n E Y hY a m)

end SGPT.Okounkov
