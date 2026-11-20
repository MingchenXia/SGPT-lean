import SGPT.PSH.SourcePlurifineNonBorelPoles
import SGPT.PSH.SourcePlurifineNonBorelCardinality

/-! Whole original chapter_pshfunctions remark42: an actual fine-open set
need not be Borel or a countable union of the exact original basic sets. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceNonBorelDraft
open Set Filter MeasureTheory Metric TopologicalSpace SGPT.BBJ SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
local notation "Bits" => ℕ → Bool

def fineCode (b : Bits) : domain := ⟨code b, code_mem b⟩

lemma continuous_fineCode : Continuous fineCode := by
  exact (projectiveModelEquiv.continuous.comp
    (Complex.continuous_ofReal.comp continuous_cantorCode)).subtype_mk _

lemma exists_separator_level (a : Bits) :
    ∃ c : ℝ, (c : EReal) < separator a (code a) := by
  obtain ⟨c, -, hc⟩ := EReal.lt_iff_exists_real_btwn.mp
    (bot_lt_iff_ne_bot.mpr (separator_ne_bot_at_code a))
  exact ⟨c, hc⟩

def separatingLevel (a : Bits) : ℝ := Classical.choose (exists_separator_level a)

def neighborhood (a : Bits) : Set domain :=
  {z | (separatingLevel a : EReal) < separator a z.val}

lemma neighborhood_open (a : Bits) : IsOpen[domainPlurifineTopology domain] (neighborhood a) :=
  SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.isOpen_psh_superlevel
    (separator_psh a) (separatingLevel a)

lemma fineCode_mem_neighborhood (a b : Bits) : fineCode b ∈ neighborhood a ↔ b = a := by
  constructor
  · intro h
    by_contra hne
    have hp := separator_eq_bot_at_other_code (Ne.symm hne)
    change (separatingLevel a : EReal) < separator a (code b) at h
    rw [hp] at h
    exact not_lt_bot h
  · intro h
    change (separatingLevel a : EReal) < separator a (code b)
    rw [h]
    exact Classical.choose_spec (exists_separator_level a)

def codedOpen (A : Set Bits) : Set domain := ⋃ a ∈ A, neighborhood a

lemma codedOpen_open (A : Set Bits) : IsOpen[domainPlurifineTopology domain] (codedOpen A) := by
  let : TopologicalSpace domain := domainPlurifineTopology domain
  exact isOpen_iUnion (fun a => isOpen_iUnion (fun _ => neighborhood_open a))

lemma preimage_codedOpen (A : Set Bits) : fineCode ⁻¹' codedOpen A = A := by
  ext b
  simp only [mem_preimage, codedOpen, mem_iUnion, fineCode_mem_neighborhood]
  constructor
  · rintro ⟨a, ha, h⟩
    exact h.symm ▸ ha
  · intro hb
    exact ⟨b, hb, rfl⟩

lemma sourcePlurifineBasis_borel {n : ℕ} (Ω : Opens (ComplexModel n))
    {S : Set Ω} (hS : S ∈ sourcePlurifineBasis Ω) : MeasurableSet S := by
  obtain ⟨U, u, hU, hUΩ, hu, rfl⟩ := hS
  have hm : Measurable (U.domRestrict u) :=
    (upperSemicontinuousOn_iff_restrict.mpr
      (raw_pshOn_of_identityAtlas hu).upperSemicontinuousOn).measurable
  have hT : MeasurableSet {z : U | (0 : EReal) < u z.val} :=
    measurableSet_lt measurable_const hm
  have hI := (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hT
  have hA : MeasurableSet {z : ComplexModel n | z ∈ U ∧ (0 : EReal) < u z} := by
    convert hI using 1
    ext z
    constructor
    · rintro ⟨hz, hp⟩
      exact ⟨⟨z, hz⟩, hp, rfl⟩
    · rintro ⟨⟨y, hyU⟩, hp, rfl⟩
      exact ⟨hyU, hp⟩
  exact hA.preimage measurable_subtype_coe

/-- The positive companion: EVERY countable subfamily of the exact source
basis has a Borel union in the original Euclidean domain. -/
lemma sourcePlurifineBasis_countable_union_borel {n : ℕ} (Ω : Opens (ComplexModel n))
    {C : Set (Set Ω)} (hC : C.Countable) (hCB : C ⊆ sourcePlurifineBasis Ω) :
    MeasurableSet (⋃₀ C) :=
  MeasurableSet.sUnion hC (fun _T hT => sourcePlurifineBasis_borel Ω (hCB hT))

lemma exists_nonBorel_fineOpen :
    ∃ S : Set domain, IsOpen[domainPlurifineTopology domain] S ∧ ¬ MeasurableSet S := by
  obtain ⟨A, hA⟩ := exists_nonmeasurable_bits
  refine ⟨codedOpen A, codedOpen_open A, ?_⟩
  intro hm
  have hp := hm.preimage continuous_fineCode.measurable
  rw [preimage_codedOpen] at hp
  exact hA hp

/-- Original existential ``in general'' assertion, in actual complex dimension
one, with both the original Borel and exact countable-basic-union conclusions. -/
theorem source_nonBorel_plurifine_open :
    (domain : Set (ComplexModel 1)).Nonempty ∧
    ∃ S : Set domain,
      IsOpen[domainPlurifineTopology domain] S ∧ ¬ MeasurableSet S ∧
      ¬ ∃ C : Set (Set domain), C.Countable ∧ C ⊆ sourcePlurifineBasis domain ∧ S = ⋃₀ C := by
  obtain ⟨S, hS, hn⟩ := exists_nonBorel_fineOpen
  refine ⟨⟨code (fun _ => false), code_mem _⟩, S, hS, hn, ?_⟩
  rintro ⟨C, hC, hCB, rfl⟩
  exact hn (sourcePlurifineBasis_countable_union_borel domain hC hCB)

end SGPT.PSH.SourceNonBorelDraft
