import SGPT.PSH.PlurifineDensity
import SGPT.Foundations.Analysis.FirstPass.QuasiPshSingularities

namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

/-- A genuine smooth perturbation of a raw PSH function is fine-continuous,
including actual poles. -/
theorem continuous_domainPlurifine_psh_add_continuous {n : ℕ}
    (Ω : Opens (ComplexModel n)) {p : ComplexModel n → EReal}
    (hp : PlurisubharmonicOn p Ω) {h : ComplexModel n → ℝ}
    (hh : ContinuousOn h Ω) :
    @Continuous Ω EReal (domainPlurifineTopology Ω) inferInstance
      (fun z ↦ p z.val + (h z.val : EReal)) := by
  let : TopologicalSpace Ω := domainPlurifineTopology Ω
  have hc : Continuous (fun z : Ω ↦ p z.val) :=
    SGPT.Foundations.Analysis.Pending.PlurifinePshTopology.continuous_psh hp
  have hg : Continuous (fun z : Ω ↦ (h z.val : EReal)) :=
    continuous_coe_real_ereal.comp (continuous_le_dom
      (domainPlurifine_le_euclidean Ω)
      (continuousOn_iff_continuous_domRestrict.mp hh))
  rw [continuous_iff_continuousAt]
  intro z
  exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))).comp (hc.continuousAt.prodMk hg.continuousAt)

/-- True raw quasi-PSH germs yield actual fine-continuous functions on the
original domain; this is a local analytic consumer, not the source global-form definition. -/
theorem continuous_domainPlurifine_quasiPSH {n : ℕ}
    (Ω : Opens (ComplexModel n)) {u : ComplexModel n → EReal}
    (hu : QuasiPlurisubharmonicOn u Ω) :
    @Continuous Ω EReal (domainPlurifineTopology Ω) inferInstance
      (fun z ↦ u z.val) := by
  let : TopologicalSpace Ω := domainPlurifineTopology Ω
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨p, h, ⟨U, hU, hzU, hp⟩, hh, heq⟩ := hu z.val z.property
  obtain ⟨V, hVV, hV, hxV⟩ := mem_nhds_iff.mp (hh.and heq)
  let W : Opens (ComplexModel n) := ⟨U ∩ V ∩ (Ω : Set (ComplexModel n)),
    (hU.inter hV).inter Ω.isOpen⟩
  have hzW : z.val ∈ (W : Set (ComplexModel n)) := ⟨⟨hzU, hxV⟩, z.property⟩
  have hWΩ : (W : Set (ComplexModel n)) ⊆ Ω := fun _ hx ↦ hx.2
  have hpW : PlurisubharmonicOn p W :=
    (hp.plurisubharmonicOn hU).mono (fun _ hx ↦ hx.1.1)
  have hhW : ContinuousOn h W := fun y hy ↦ (hVV hy.1.2).1.continuousAt.continuousWithinAt
  have hc := continuous_domainPlurifine_psh_add_continuous W hpW hhW
  have heqW : (fun w : W ↦ u w.val) = (fun w : W ↦ p w.val + (h w.val : EReal)) := by
    funext w
    exact (hVV w.property.1.2).2
  have huc : @Continuous W EReal (domainPlurifineTopology W) inferInstance
      (fun w ↦ u w.val) := heqW ▸ hc
  let : TopologicalSpace W := domainPlurifineTopology W
  have hi : @IsOpenMap W Ω (domainPlurifineTopology W) (domainPlurifineTopology Ω)
      (holomorphicDomainMap (F := id) hWΩ) := fun S hS ↦
    isOpen_domainPlurifine_image_inclusion hWΩ hS
  let w : W := ⟨z.val, hzW⟩
  have ht : Tendsto (fun z : Ω ↦ u z.val)
      (Filter.map (holomorphicDomainMap (F := id) hWΩ) (𝓝 w))
      (𝓝 (u w.val)) := tendsto_map'_iff.mpr huc.continuousAt
  have hw : holomorphicDomainMap (F := id) hWΩ w = z := Subtype.ext rfl
  have hn := hi.nhds_le w
  rw [hw] at hn
  exact ht.mono_left hn

end SGPT.PSH

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology
universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual chart quasi-PSH germs produce global continuity for the independently
constructed manifold fine topology. -/
theorem continuous_plurifine_of_chart_quasiPSH {u : X → EReal}
    (hu : ∀ i, QuasiPlurisubharmonicOn (A.coordinate u i) (A.chart i).target) :
    @Continuous X EReal A.plurifineTopology inferInstance u := by
  change @Continuous X EReal
    (⨆ i, coinduced (A.chartInverse i) (domainPlurifineTopology (A.chartDomain i)))
    inferInstance u
  apply continuous_iSup_dom.mpr
  intro i
  apply continuous_coinduced_dom.mpr
  exact continuous_domainPlurifine_quasiPSH (A.chartDomain i) (hu i)

/-- Source PSH functions in actual varying-dimension charts are fine-continuous. -/
theorem IsPSH.continuous_plurifine {u : X → EReal} (hu : A.IsPSH u) :
    @Continuous X EReal A.plurifineTopology inferInstance u :=
  continuous_plurifine_of_chart_quasiPSH
    (fun i z hz ↦ (hu.chartPlurisubharmonic i z hz).quasiPlurisubharmonicAt)

/-- Genuine EReal order continuity, including poles, gives fine-open strict
comparison for actual local quasi-PSH coordinate germs. -/
theorem isOpen_plurifine_lt_of_chart_quasiPSH {u w : X → EReal}
    (hu : ∀ i, QuasiPlurisubharmonicOn (A.coordinate u i) (A.chart i).target)
    (hw : ∀ i, QuasiPlurisubharmonicOn (A.coordinate w i) (A.chart i).target) :
    IsOpen[A.plurifineTopology] {x | u x < w x} := by
  apply (A.isOpen_plurifine_iff _).mpr
  intro i
  let : TopologicalSpace (A.chartDomain i) := domainPlurifineTopology (A.chartDomain i)
  exact isOpen_lt (continuous_domainPlurifine_quasiPSH (A.chartDomain i) (hu i))
    (continuous_domainPlurifine_quasiPSH (A.chartDomain i) (hw i))

/-- Genuine source PSH strict comparisons are fine-open on the original manifold. -/
theorem IsPSH.isOpen_plurifine_lt {u w : X → EReal}
    (hu : A.IsPSH u) (hw : A.IsPSH w) :
    IsOpen[A.plurifineTopology] {x | u x < w x} :=
  isOpen_plurifine_lt_of_chart_quasiPSH
    (fun i z hz ↦ (hu.chartPlurisubharmonic i z hz).quasiPlurisubharmonicAt)
    (fun i z hz ↦ (hw.chartPlurisubharmonic i z hz).quasiPlurisubharmonicAt)

end SGPT.PSH.VariableComplexAtlas
