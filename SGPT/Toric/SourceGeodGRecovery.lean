import SGPT.Toric.SourceGeodGForward
import SGPT.Convex.ClosedStripConjugateRecovery

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))
local notation "X" => PolytopeToricVariety γ hs
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The original dual inequalities manufacture an actual original toric
subgeodesic, with original endpoint inequalities at every pole, whose literal
closed-strip extension is the actual full product conjugate of Ψ. -/
theorem exists_sourceGeodGClosedProfile_eq_conjugate {φ₀ φ₁ : PolytopeToricVariety γ hs → EReal}
    (hφ₀ : φ₀ ∈ h.PSHTor) (hφ₁ : φ₁ ∈ h.PSHTor)
    (Ψ : h.sourceGeodGDuals φ₀ φ₁) :
    ∃ a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁,
      h.sourceGeodGClosedProfile omega a =
        conjugate (timeProductPairing (innerₗ E)).flip Ψ.val := by
  obtain ⟨G, hG, hGL, hbounds⟩ := Ψ.property.2.2
  have hlower (m : E) (s : ℝ) :
      max (conjugate (innerₗ E) (fun x => (h.realProfile φ₀ x : EReal)) m)
        (conjugate (innerₗ E) (fun x => (h.realProfile φ₁ x : EReal)) m + (s : EReal)) ≤
          Ψ.val (m, s) := by
    simpa only [legendre, (h.realProfile_mem hφ₀).2, (h.realProfile_mem hφ₁).2] using
      (hbounds m s).1
  have hupper (m : E) (s : ℝ) : Ψ.val (m, s) ≤ G m + ((max s 0 : ℝ) : EReal) :=
    (hbounds m s).2
  let g := timeConjugateRealProfile (innerₗ E) Ψ.val
  let H := conjugate (timeProductPairing (innerₗ E)).flip Ψ.val
  obtain ⟨hc, hslice, h₀, h₁, hlim₀, hlim₁, hfinite⟩ :=
    timeConjugateRealProfile_spec (innerₗ E) (h.realProfile φ₀) (h.realProfile φ₁)
      Ψ.val G Ψ.property.1 hG hlower hupper
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hf₀ : (fun x => g (x, 0)) ∈ RealGrowthClass (innerₗ E) (toricDivisorPolytope D) := by
    refine ⟨hslice 0 hzero, ?_⟩
    obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp
      (h.realProfile_mem hφ₀).1.2
    apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    exact ⟨C, fun x => (EReal.coe_le_coe_iff.mpr (h₀ x)).trans (hC x)⟩
  have hf₁ : (fun x => g (x, 1)) ∈ RealGrowthClass (innerₗ E) (toricDivisorPolytope D) := by
    refine ⟨hslice 1 hone, ?_⟩
    obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp
      (h.realProfile_mem hφ₁).1.2
    apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    exact ⟨C, fun x => (EReal.coe_le_coe_iff.mpr (h₁ x)).trans (hC x)⟩
  let ψ₀ := h.extension (fun x => g (x, 0)) hf₀
  let ψ₁ := h.extension (fun x => g (x, 1)) hf₁
  have hψ₀ : ψ₀ ∈ h.PSHTor := h.extension_mem _ hf₀
  have hψ₁ : ψ₁ ∈ h.PSHTor := h.extension_mem _ hf₁
  have hr₀ : h.realProfile ψ₀ = fun x => g (x, 0) := by
    funext x
    change (h.profile (h.extension _ hf₀) x).toReal = _
    rw [h.profile_extension]
    exact EReal.toReal_coe _
  have hr₁ : h.realProfile ψ₁ = fun x => g (x, 1) := by
    funext x
    change (h.profile (h.extension _ hf₁) x).toReal = _
    rw [h.profile_extension]
    exact EReal.toReal_coe _
  have hψ₀le : ψ₀ ≤ φ₀ := by
    apply (h.le_iff hψ₀ hφ₀).mpr
    intro x
    rw [(h.realProfile_mem hψ₀).2, (h.realProfile_mem hφ₀).2, hr₀]
    exact EReal.coe_le_coe_iff.mpr (h₀ x)
  have hψ₁le : ψ₁ ≤ φ₁ := by
    apply (h.le_iff hψ₁ hφ₁).mpr
    intro x
    rw [(h.realProfile_mem hψ₁).2, (h.realProfile_mem hφ₁).2, hr₁]
    exact EReal.coe_le_coe_iff.mpr (h₁ x)
  let F : E × Ioo (0 : ℝ) 1 → ℝ := fun p => g (p.1, p.2.val)
  have hstrip : EqOn (stripFunction F) g (univ ×ˢ Ioo (0 : ℝ) 1) :=
    fun p hp => stripFunction_of_mem F p.1 hp.2
  have hF : h.IsToricSubgeodesicProfile ψ₀ ψ₁ F := by
    refine ⟨((hc.subset (prod_mono subset_rfl Ioo_subset_Icc_self)
      (convex_univ.prod (convex_Ioo 0 1))).congr hstrip.symm), ?_, ?_⟩
    · intro x
      rw [hr₁]
      apply (hlim₁ x).congr'
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact (stripFunction_of_mem F x ht).symm
    · intro x
      rw [hr₀]
      apply (hlim₀ x).congr'
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact (stripFunction_of_mem F x ht).symm
  let c := (h.toricSubgeodesicEquiv omega hψ₀ hψ₁).symm ⟨F, hF⟩
  let a : h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁ :=
    ⟨⟨ψ₀, hψ₀, hψ₀le⟩, ⟨ψ₁, hψ₁, hψ₁le⟩, c⟩
  have hopen : h.sourceGeodGOpenProfile omega a = F :=
    congrArg Subtype.val ((h.toricSubgeodesicEquiv omega hψ₀ hψ₁).apply_symm_apply ⟨F, hF⟩)
  refine ⟨a, ?_⟩
  funext p
  rcases p with ⟨x, t⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | hti)
    · have hh := h.sourceGeodGClosedProfile_left omega a x
      change h.sourceGeodGClosedProfile omega a (x, 0) = (h.realProfile ψ₀ x : EReal) at hh
      rw [hr₀] at hh
      exact hh.trans (hfinite (x, 0) ⟨mem_univ _, hzero⟩)
    · have hh := h.sourceGeodGClosedProfile_right omega a x
      change h.sourceGeodGClosedProfile omega a (x, 1) = (h.realProfile ψ₁ x : EReal) at hh
      rw [hr₁] at hh
      exact hh.trans (hfinite (x, 1) ⟨mem_univ _, hone⟩)
    · have hh := h.sourceGeodGClosedProfile_interior omega a x ⟨t, hti⟩
      have hv := congrFun hopen (x, ⟨t, hti⟩)
      change h.realProfile (a.2.2.val ⟨t, hti⟩) x = g (x, t) at hv
      rw [hv] at hh
      exact hh.trans (hfinite (x, t) ⟨mem_univ _, Ioo_subset_Icc_self hti⟩)
  · have hh := timeConjugate_eq_top_of_not_mem_Icc (innerₗ E) Ψ.val G hG hupper x ht
    simpa only [sourceGeodGClosedProfile, closedStripExtension, if_neg ht] using hh.symm

end BigToricMetric
end SGPT.Toric
