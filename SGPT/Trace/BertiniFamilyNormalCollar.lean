import SGPT.Trace.BertiniFamilyNormalIntegral

/-! Actual proper projection produces compact collars covered by true original normal charts. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))

omit [IsComplexManifold (d + 1) X] [CompactSpace X] in
def familyClosedParameterCollar (r : ℝ) : Set (familyIncidence p i a v U) :=
  {q | q.val.1.val ∈ Metric.closedBall (0 : ComplexModel 1) r}

theorem isCompact_familyClosedParameterCollar (r : ℝ)
    (hU : Metric.closedBall (0 : ComplexModel 1) r ⊆ U) :
    IsCompact (familyClosedParameterCollar p i a v U r) := by
  let K := Metric.closedBall (0 : ComplexModel 1) r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ComplexModel 1) r)
  let f : K → U := fun z => ⟨z.val,hU z.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hK : IsCompact (Set.range f) := isCompact_range hf
  have hset : (familyProjection p i a v U) ⁻¹' Set.range f = familyClosedParameterCollar p i a v U r := by
    ext q
    constructor
    · rintro ⟨z,hz⟩
      have heq : z.val = q.val.1.val := congrArg Subtype.val hz
      change q.val.1.val ∈ K
      exact heq ▸ z.property
    · intro hq
      exact ⟨⟨q.val.1.val,hq⟩,rfl⟩
  rw [← hset]
  exact (isProperMap_familyProjection p i a v U p.contMDiff).isCompact_preimage hK

theorem isCompact_familyCentralFibre (h0 : (0 : ComplexModel 1) ∈ U) :
    IsCompact {q : familyIncidence p i a v U | scalarParameter p i a v U q = 0} := by
  have hset : {q : familyIncidence p i a v U | scalarParameter p i a v U q = 0} =
      (familyProjection p i a v U) ⁻¹' {⟨0,h0⟩} :=
    Set.ext fun q => scalarParameter_zero_iff_projection p i a v U h0 q
  rw [hset]
  exact (isProperMap_familyProjection p i a v U p.contMDiff).isCompact_preimage isCompact_singleton

theorem exists_familyClosedParameterCollar_in_open (h0 : (0 : ComplexModel 1) ∈ U)
    (O : Set (familyIncidence p i a v U)) (hO : IsOpen O)
    (hcentral : {q | scalarParameter p i a v U q = 0} ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      IsCompact (familyClosedParameterCollar p i a v U r) ∧ familyClosedParameterCollar p i a v U r ⊆ O := by
  let f := familyProjection p i a v U
  let t0 : U := ⟨0,h0⟩
  have hC : IsClosed (f '' Oᶜ) := (isProperMap_familyProjection p i a v U p.contMDiff).isClosedMap _ hO.isClosed_compl
  have ht0 : t0 ∉ f '' Oᶜ := by
    rintro ⟨q,hq,hft⟩
    exact hq (hcentral ((scalarParameter_zero_iff_projection p i a v U h0 q).mpr hft))
  let V : Set U := (f '' Oᶜ)ᶜ
  let G : Set (ComplexModel 1) := (Subtype.val : U → ComplexModel 1) '' V
  have hG : IsOpen G := U.isOpen.isOpenMap_subtype_val V hC.isOpen_compl
  have h0G : (0 : ComplexModel 1) ∈ G := ⟨t0,ht0,rfl⟩
  obtain ⟨s,hs,hball⟩ := Metric.isOpen_iff.mp hG 0 h0G
  have hclosed : Metric.closedBall (0 : ComplexModel 1) (s / 2) ⊆ G :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hU : Metric.closedBall (0 : ComplexModel 1) (s / 2) ⊆ U := by
    intro z hz
    obtain ⟨t,_,rfl⟩ := hclosed hz
    exact t.property
  refine ⟨s / 2,by positivity,hU,isCompact_familyClosedParameterCollar p i a v U (s / 2) hU,?_⟩
  intro q hq
  obtain ⟨t,ht,heq⟩ := hclosed hq
  have htq : t = f q := Subtype.ext heq
  have hqV : f q ∈ V := htq ▸ ht
  by_contra hqO
  exact hqV ⟨q,hqO,rfl⟩

variable (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

theorem exists_family_finite_normal_collar (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ (k : ℕ) (F : Fin k → FlatData (d + 1) d (familyIncidence p i a v U)
        {y | scalarParameter p i a v U y = 0}) (r : ℝ),
      0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      IsCompact (familyClosedParameterCollar p i a v U r) ∧
      (∀ j, ∀ y ∈ (F j).ambSource, fcoord (F j) y (Fin.last d) = scalarParameter p i a v U y) ∧
      (∀ j, ∃ q : familyIncidence p i a v U, scalarParameter p i a v U q = 0 ∧
        q ∈ (F j).ambSource ∧ fcoord (F j) q = 0) ∧
      familyClosedParameterCollar p i a v U r ⊆ ⋃ j, (F j).ambSource := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let K : Set (familyIncidence p i a v U) := {q | scalarParameter p i a v U q = 0}
  have hE (q : K) := exists_actual_parameter_normal_flatData p i a v U hsm q.val q.property
  let F (q : K) := (hE q).choose
  have hF (q : K) := (hE q).choose_spec
  let V : K → Set (familyIncidence p i a v U) := fun q => (F q).ambSource
  have hV (q : K) : IsOpen (V q) := (F q).isOpen_ambSource
  have hc : K ⊆ ⋃ q, V q := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨q,hq⟩,(hF ⟨q,hq⟩).1⟩
  obtain ⟨A,hA⟩ := (isCompact_familyCentralFibre p i a v U h0).elim_finite_subcover V hV hc
  let a0 : Fin A.card → K := fun j => (A.equivFin.symm j).val
  let Fs : Fin A.card → FlatData (d + 1) d (familyIncidence p i a v U) K := fun j => F (a0 j)
  let O := ⋃ j, (Fs j).ambSource
  have hO : IsOpen O := isOpen_iUnion fun j => (Fs j).isOpen_ambSource
  have hKO : K ⊆ O := by
    intro q hq
    obtain ⟨x,hx,hqx⟩ := mem_iUnion₂.mp (hA hq)
    exact mem_iUnion.mpr ⟨A.equivFin ⟨x,hx⟩,by simpa only [Fs,a0,Equiv.symm_apply_apply] using hqx⟩
  obtain ⟨r,hr,hrU,hrK,hrO⟩ := exists_familyClosedParameterCollar_in_open p i a v U h0 O hO hKO
  refine ⟨A.card,Fs,r,hr,hrU,hrK,?_,?_,hrO⟩
  · intro j
    exact (hF (a0 j)).2.2.1
  · intro j
    exact ⟨(a0 j).val,(a0 j).property,(hF (a0 j)).1,(hF (a0 j)).2.1⟩

end SGPT.Trace.BertiniFamilyCanonical
