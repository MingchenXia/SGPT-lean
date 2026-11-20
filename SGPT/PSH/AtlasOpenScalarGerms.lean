import SGPT.PSH.AtlasOpenRestriction
import SGPT.PSH.AtlasInfinityIdeal

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology

universe u
variable {X : Type u} [TopologicalSpace X]

private theorem restricted_scalar_coordinates {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n)) (U : Opens X) (hU : Nonempty U)
    (g : U → ℂ) (V : Set U) :
    ((e.subtypeRestr hU).target ∩ (e.subtypeRestr hU).symm ⁻¹' V =
      e.target ∩ e.symm ⁻¹' ((Subtype.val : U → X) '' V)) ∧
    EqOn (g ∘ (e.subtypeRestr hU).symm) (extendOpens U g ∘ e.symm)
      ((e.subtypeRestr hU).target ∩ (e.subtypeRestr hU).symm ⁻¹' V) := by
  constructor
  · ext z
    constructor
    · rintro ⟨hz, hzV⟩
      exact ⟨e.subtypeRestr_target_subset hU hz,
        (e.subtypeRestr hU).symm z, hzV, e.subtypeRestr_symm_apply hU hz⟩
    · rintro ⟨hz, p, hp, he⟩
      have hpS : p.val ∈ e.source := by rw [he]; exact e.map_target hz
      have hz' : z ∈ (e.subtypeRestr hU).target := by
        have h := e.map_subtype_source hU hpS
        have hep : e p.val = z := by rw [he]; exact e.right_inv hz
        rwa [hep] at h
      have hinv : (e.subtypeRestr hU).symm z = p :=
        Subtype.ext ((e.subtypeRestr_symm_apply hU hz').trans he.symm)
      refine ⟨hz', ?_⟩
      change (e.subtypeRestr hU).symm z ∈ V
      rw [hinv]
      exact hp
  · intro z hz
    change g ((e.subtypeRestr hU).symm z) = extendOpens U g (e.symm z)
    rw [← e.subtypeRestr_symm_apply hU hz.1]
    exact (extendOpens_val U g ((e.subtypeRestr hU).symm z)).symm

/-- EVERY actual inherited chart gives exactly the SAME original scalar
holomorphy on the literal image, including ANY subset and the empty open. -/
theorem chartHolomorphicOn_openRestriction_iff (A : VariableComplexAtlas X) (U : Opens X)
    (g : U → ℂ) (V : Set U) :
    (A.openRestriction U).ChartHolomorphicOn g V ↔
      A.ChartHolomorphicOn (extendOpens U g) ((Subtype.val : U → X) '' V) := by
  classical
  by_cases hU : Nonempty U
  · unfold openRestriction
    rw [dif_pos hU]
    change (∀ i, DifferentiableOn ℂ (g ∘ ((A.chart i).subtypeRestr hU).symm)
      (((A.chart i).subtypeRestr hU).target ∩ ((A.chart i).subtypeRestr hU).symm ⁻¹' V)) ↔ _
    constructor
    · intro h i
      obtain ⟨hd, he⟩ := restricted_scalar_coordinates (A.chart i) U hU g V
      rw [← hd]
      exact (h i).congr fun z hz => (he hz).symm
    · intro h i
      obtain ⟨hd, he⟩ := restricted_scalar_coordinates (A.chart i) U hU g V
      apply (h i).congr_mono he
      exact hd.subset
  · have himage : (Subtype.val : U → X) '' V = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨p, _, _⟩
      exact hU ⟨p⟩
    unfold openRestriction
    rw [dif_neg hU]
    constructor
    · intro _ i
      simp only [himage, preimage_empty, inter_empty]
      exact differentiableOn_empty
    · intro _ i
      exact Fin.elim0 i.down

/-- Both actual open-neighborhood directions retain the SAME scalar germ. -/
theorem atlasHolomorphicAt_openRestriction_iff_extend (A : VariableComplexAtlas X)
    (U : Opens X) {g : U → ℂ} {p : U} :
    (A.openRestriction U).AtlasHolomorphicAt g p ↔
      A.AtlasHolomorphicAt (extendOpens U g) p.val := by
  constructor
  · rintro ⟨V, hV, hpV, hg⟩
    exact ⟨Subtype.val '' V, U.isOpen.isOpenMap_subtype_val V hV,
      ⟨p, hpV, rfl⟩, (chartHolomorphicOn_openRestriction_iff A U g V).mp hg⟩
  · rintro ⟨W, hW, hpW, hg⟩
    let V : Set U := Subtype.val ⁻¹' W
    refine ⟨V, hW.preimage continuous_subtype_val, hpW,
      (chartHolomorphicOn_openRestriction_iff A U g V).mpr ?_⟩
    intro i
    apply (hg i).mono
    rintro z ⟨hz, p, hp, he⟩
    refine ⟨hz, ?_⟩
    change (A.chart i).symm z ∈ W
    rw [← he]
    exact hp

/-- Literal restriction of ANY original scalar has exactly its original
holomorphic germ; extension differs only away from the actual open. -/
theorem atlasHolomorphicAt_comp_open_val_iff (A : VariableComplexAtlas X) (U : Opens X)
    {f : X → ℂ} {p : U} :
    (A.openRestriction U).AtlasHolomorphicAt (f ∘ Subtype.val) p ↔
      A.AtlasHolomorphicAt f p.val := by
  have heq : extendOpens U (f ∘ Subtype.val) =ᶠ[𝓝 p.val] f := by
    filter_upwards [eventually_mem_opens U p] with y hy
    exact extendOpens_val U (f ∘ Subtype.val) ⟨y, hy⟩
  constructor
  · intro h
    exact ((atlasHolomorphicAt_openRestriction_iff_extend A U).mp h).congr heq
  · intro h
    exact (atlasHolomorphicAt_openRestriction_iff_extend A U).mpr (h.congr heq.symm)

/-- BOTH full finite-span inclusions use the ACTUAL original family and all
its actual holomorphic coefficients, never a support or equation certificate. -/
theorem atlasIsInSpanAt_comp_open_val_iff (A : VariableComplexAtlas X) (U : Opens X)
    {S : (X → ℂ) → Prop} {p : U} {g : U → ℂ} :
    (A.openRestriction U).AtlasIsInSpanAt
      (fun s' => ∃ s, S s ∧ s' = s ∘ Subtype.val) p g ↔
      A.AtlasIsInSpanAt S p.val (extendOpens U g) := by
  classical
  constructor
  · rintro ⟨hg, N, s', a, hs', ha, hsum⟩
    choose s hs hss using hs'
    refine ⟨(atlasHolomorphicAt_openRestriction_iff_extend A U).mp hg, N, s,
      fun i => extendOpens U (a i), hs,
      fun i => (atlasHolomorphicAt_openRestriction_iff_extend A U).mp (ha i), ?_⟩
    have hsum' := (eventually_nhds_val_iff U (x := p) (P := fun y => ∀ hy : y ∈ U,
      g ⟨y, hy⟩ = ∑ i, a i ⟨y, hy⟩ * s' i ⟨y, hy⟩)).mpr
        (hsum.mono fun p' hp' _ => hp')
    filter_upwards [hsum', eventually_mem_opens U p] with y hy hyU
    have e1 : extendOpens U g y = g ⟨y, hyU⟩ := extendOpens_val U g ⟨y, hyU⟩
    have e2 : ∀ i, extendOpens U (a i) y = a i ⟨y, hyU⟩ :=
      fun i => extendOpens_val U _ ⟨y, hyU⟩
    simp only [e1, e2, hy hyU, hss]
    rfl
  · rintro ⟨hg, N, s, a, hs, ha, hsum⟩
    refine ⟨(atlasHolomorphicAt_openRestriction_iff_extend A U).mpr hg, N,
      fun i => s i ∘ Subtype.val, fun i => a i ∘ Subtype.val,
      fun i => ⟨s i, hs i, rfl⟩,
      fun i => (atlasHolomorphicAt_comp_open_val_iff A U).mpr (ha i), ?_⟩
    have h := (eventually_nhds_val_iff U).mp hsum
    filter_upwards [h] with y hy
    simpa only [extendOpens_val, Function.comp_apply] using hy

end SGPT.PSH.VariableComplexAtlas
