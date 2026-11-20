import SGPT.PSH.PlurifineBasis
import Mathlib.Order.LiminfLimsup

/-! Source thinness uses ordinary closure and the actual punctured filter.
The fine topology is the independently constructed genuine PSH topology. -/
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology
variable {n : ℕ}

/-- The literal source pointwise thinness predicate, including its closure alternative. -/
def sourceThinAt (Ω : Opens (ComplexModel n)) (E : Set Ω) (x : Ω) : Prop :=
  x ∉ closure E ∨ (x ∈ closure E ∧
    ∃ (U : Set (ComplexModel n)) (u : ComplexModel n → EReal),
      IsOpen U ∧ U ⊆ Ω ∧ x.val ∈ U ∧
      (VariableComplexAtlas.identityAtlas n).IsPSHOn u U ∧
      limsup (fun y : Ω ↦ u y.val) (𝓝[((Subtype.val ⁻¹' U ∩ E) \ {x})] x) < u x.val)

/-- The source global thinness predicate quantifies over every original point. -/
def sourceThinSet (Ω : Opens (ComplexModel n)) (E : Set Ω) : Prop :=
  ∀ x : Ω, sourceThinAt Ω E x

private theorem local_superlevel (Ω : Opens (ComplexModel n))
    {U : Set (ComplexModel n)} (hU : IsOpen U) {u : ComplexModel n → EReal}
    (hu : (VariableComplexAtlas.identityAtlas n).IsPSHOn u U) (c : ℝ) :
    IsOpen[domainPlurifineTopology Ω] {z : Ω | z.val ∈ U ∧ (c : EReal) < u z.val} := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-c)
  have hkc : -(k : ℝ) < c := by linarith
  have hraw := raw_pshOn_of_identityAtlas hu
  convert isOpen_domainPlurifine_local_real_superlevel Ω hU
    (SGPT.Foundations.Analysis.FirstPass.MongeAmpere.truncationReal_plurisubharmonicOn
      (Ω := ⟨U, hU⟩) hraw k) c using 1
  ext z
  by_cases hz : z.val ∈ U
  · simp only [mem_ofPred_eq, hz, true_and]
    rw [← EReal.coe_lt_coe_iff,
      SGPT.Foundations.Analysis.FirstPass.MongeAmpere.coe_truncationReal
        (Ω := ⟨U, hU⟩) hraw k hz]
    simp only [SGPT.Foundations.Analysis.FirstPass.MongeAmpere.truncation, lt_max_iff]
    have hnot : ¬ (c : EReal) < (((-(k : ℝ)) : ℝ) : EReal) :=
      not_lt_of_ge (EReal.coe_le_coe_iff.mpr hkc.le)
    simp only [hnot, or_false]
  · simp only [mem_ofPred_eq, hz, false_and]

/-- Exact source thinness, with no basis or requested equivalence premise. -/
theorem sourceThinAt_iff_punctured_complement_fine_nhds
    (Ω : Opens (ComplexModel n)) (E : Set Ω) (x : Ω) :
    sourceThinAt Ω E x ↔ (E \ {x})ᶜ ∈ @nhds Ω (domainPlurifineTopology Ω) x := by
  classical
  constructor
  · rintro (hx | ⟨_, U, u, hU, hUΩ, hxU, hu, hgap⟩)
    · have hordinary : (closure E)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
      have hfine := (nhds_mono (domainPlurifine_le_euclidean Ω)) hordinary
      exact mem_of_superset hfine (by intro y hy h; exact hy (subset_closure h.1))
    · obtain ⟨c, hlc, hcu⟩ := EReal.exists_between_coe_real hgap
      have hevent := eventually_lt_of_limsup_lt hlc
      have hevent' : ∀ᶠ y in 𝓝 x,
          y ∈ (Subtype.val ⁻¹' U ∩ E) \ {x} → u y.val < (c : EReal) :=
        eventually_nhdsWithin_iff.mp hevent
      obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hevent'
      have hWfine : IsOpen[domainPlurifineTopology Ω] W :=
        (domainPlurifine_le_euclidean Ω) W hW
      have hSf := local_superlevel Ω hU hu c
      have hnb : W ∩ {z : Ω | z.val ∈ U ∧ (c : EReal) < u z.val} ∈
          @nhds Ω (domainPlurifineTopology Ω) x :=
        by
          let : TopologicalSpace Ω := domainPlurifineTopology Ω
          exact (hWfine.inter hSf).mem_nhds ⟨hxW, hxU, hcu⟩
      apply mem_of_superset hnb
      intro y hy hE
      have hsmall := hWsub hy.1 ⟨⟨hy.2.1, hE.1⟩, hE.2⟩
      exact (not_lt_of_ge hsmall.le) hy.2.2
  · intro hnb
    by_cases hx : x ∈ closure E
    · right
      refine ⟨hx, ?_⟩
      obtain ⟨S, hSsub, hS, hxS⟩ :=
        (@mem_nhds_iff Ω (domainPlurifineTopology Ω) x ((E \ {x})ᶜ)).mp hnb
      obtain ⟨O, g, hO, hxO, hg, hgx, _, _, _, hTsub⟩ :=
        SGPT.Foundations.Analysis.Pending.PlurifineSingleSuperlevelNeighborhoods.exists_bounded_single_superlevel
          hS hxS
      obtain ⟨U, hU, hUΩ, hUO⟩ := exists_ambient_open_of_subtype_open Ω O hO
      have hmem (z : Ω) : z.val ∈ U ↔ z ∈ O := by
        change z ∈ Subtype.val ⁻¹' U ↔ z ∈ O
        rw [hUO]
      refine ⟨U, fun z ↦ (g z : EReal), hU, hUΩ, (hmem x).mpr hxO,
        real_isPSHOn_identityAtlas hU (hg.mono hUΩ), ?_⟩
      have hle : ∀ᶠ y in 𝓝[((Subtype.val ⁻¹' U ∩ E) \ {x})] x,
          (g y.val : EReal) ≤ 0 := by
        apply eventually_nhdsWithin_iff.mpr
        exact Eventually.of_forall (fun y hy ↦ by
          have hn : ¬ 0 < g y.val := by
            intro hp
            exact hSsub (hTsub ⟨(hmem y).mp hy.1.1, hp⟩) ⟨hy.1.2, hy.2⟩
          exact_mod_cast le_of_not_gt hn)
      have hlim : limsup (fun y : Ω ↦ (g y.val : EReal))
          (𝓝[((Subtype.val ⁻¹' U ∩ E) \ {x})] x) ≤ 0 := limsup_le_of_le (h := hle)
      apply lt_of_le_of_lt hlim
      change (0 : EReal) < (g x.val : EReal)
      rw [hgx]
      norm_num
    · exact Or.inl hx

/-- Source finite unions, including all closure alternatives and empty filters. -/
theorem sourceThinAt_union (Ω : Opens (ComplexModel n)) (E F : Set Ω) (x : Ω)
    (hE : sourceThinAt Ω E x) (hF : sourceThinAt Ω F x) :
    sourceThinAt Ω (E ∪ F) x := by
  rw [sourceThinAt_iff_punctured_complement_fine_nhds] at hE hF ⊢
  simpa only [union_sdiff_distrib, compl_union] using inter_mem hE hF

/-- The original Cartan criterion at an original member of E. -/
theorem fine_nhds_iff_complement_sourceThinAt (Ω : Opens (ComplexModel n))
    (E : Set Ω) (x : Ω) (hx : x ∈ E) :
    E ∈ @nhds Ω (domainPlurifineTopology Ω) x ↔ sourceThinAt Ω Eᶜ x := by
  rw [sourceThinAt_iff_punctured_complement_fine_nhds]
  have heq : Eᶜ \ {x} = Eᶜ := by
    ext y
    simp only [Set.mem_sdiff, mem_compl_iff, mem_singleton_iff]
    constructor
    · exact And.left
    · intro hy
      exact ⟨hy, fun h ↦ hy (h ▸ hx)⟩
  rw [heq, compl_compl]

end SGPT.PSH
