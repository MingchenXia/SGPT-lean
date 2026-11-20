import SGPT.Trace.BertiniOriginalMemberHodgeIntegral

/-! Original slice producer retaining ACTUAL preferred chart and affine frame data. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProductComplexManifold
open scoped ProductComplexManifold

section General
variable {n N : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {p : X → ComplexProjectiveSpace N} {φ : X → EReal}
theorem exists_preferred_sliceChart (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {q₀ : HyperplaneSpace N × X}
    (hmem : q₀.2 ∈ member p q₀.1) (hsm : ¬ IsSingularPointOfMember n p q₀.1 q₀.2) :
    ∃ c : SliceChart n p φ,
      c.i = chartIndex q₀.1 ∧ c.e = complexChartAt (n := n) q₀.2 ∧
      c.ζ₀ = affineChart (chartIndex q₀.1) q₀.1 ∧
      c.z₀ = (complexChartAt (n := n) q₀.2).val q₀.2 ∧ q₀ ∈ c.domain := by
  set i := chartIndex q₀.1 with hi
  set e := complexChartAt (n := n) q₀.2 with he
  set j := chartIndex (p q₀.2) with hj
  have hq1 : q₀.1 ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hq2 : q₀.2 ∈ e.val.source := mem_complexChartAt_source _
  have hqj : p q₀.2 ∈ (affineChart j).source := mem_affineChart_chartIndex _
  set L := prodModelEquiv N n with hL
  set w₀ := prodChart (affineChart i) e.val q₀ with hw₀
  have hw₀V : w₀ ∈ conormalDomain p e j := (prodChart_mem_conormalDomain_iff p hq2).mpr hqj
  have hgen0 : conormalGenerator p i e j 0 w₀ = 0 :=
    (conormalGenerator_zero_prodChart_eq_zero_iff p hq1 hq2 hqj).mpr hmem
  obtain ⟨m, hm⟩ : ∃ m : Fin n, conormalGenerator p i e j m.succ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hsm ((conormalGenerator_prodChart_iff p hp hq1 hq2 hqj).mp fun k => ?_)
    refine Fin.cases ?_ (fun m => ?_) k
    · exact hgen0
    · exact hcon m
  have hGd : DifferentiableAt ℂ (conormalGenerator p i e j 0) w₀ :=
    (differentiableOn_conormalGenerator p hp i e j 0 w₀ hw₀V).differentiableAt
      ((isOpen_conormalDomain p hp e j).mem_nhds hw₀V)
  have hderiv : fderiv ℂ (conormalGenerator p i e j 0) w₀ (slDir (N := N) m) ≠ 0 := by
    rw [fderiv_conormalGenerator_zero_slDir p hp hw₀V m]
    exact hm
  have hΨ := hasFDerivAt_flatMap p m hGd.hasFDerivAt
  have hinj : Function.Injective (fderiv ℂ (flatMap p i e j m) w₀) := by
    rw [hΨ.fderiv]
    exact injective_flatMap_deriv hderiv
  obtain ⟨Φ, hΦs, hΦf, -⟩ := exists_localHolomorphicEquivAt (isOpen_conormalDomain p hp e j)
    hw₀V (differentiableOn_flatMap p hp i e j m) hinj
  set ζ₀ := affineChart i q₀.1 with hζ₀
  set z₀ := e.val q₀.2 with hz₀
  have hw₀eq : w₀ = L (ζ₀, z₀) := rfl
  -- the local decomposition of `φ` at `x₀`
  obtain ⟨ψ, h, ⟨U, hUo, hzU, hUpsh⟩, -, heq⟩ := hφ e z₀ (e.val.map_source hq2)
  obtain ⟨V₁, hV₁, hV₁o, hzV₁⟩ := _root_.eventually_nhds_iff.mp heq
  set V := U ∩ V₁ ∩ e.val.target with hVdef
  have hVo : IsOpen V := (hUo.inter hV₁o).inter e.val.open_target
  have hzV : z₀ ∈ V := ⟨⟨hzU, hzV₁⟩, e.val.map_source hq2⟩
  have hpsh : PlurisubharmonicOn ψ V := fun y hy => (hUpsh.plurisubharmonicOn hUo) y hy.1.1
  have heqV : ∀ y ∈ V, φ (e.val.symm y) = ψ y + (h y : EReal) := fun y hy => hV₁ y hy.1.2
  -- the target region
  set R := Φ.target ∩ Φ.invFun ⁻¹' (L.symm ⁻¹' (univ ×ˢ V)) with hR
  have hRo : IsOpen R := Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target
    ((isOpen_univ.prod hVo).preimage L.symm.continuous)
  have ht₀ : flatProj m w₀ = Φ.toFun w₀ := by rw [hΦf, flatMap_eq_flatProj p hgen0]
  have ht₀R : flatProj m (L (ζ₀, z₀)) ∈ R := by
    rw [← hw₀eq, ht₀]
    refine ⟨Φ.mapsTo_toFun Φ.center_mem_source, ?_⟩
    simp only [mem_preimage, Φ.left_inv w₀ Φ.center_mem_source, mem_prod, mem_univ, true_and]
    rw [hw₀eq, ContinuousLinearEquiv.symm_apply_apply]
    exact hzV
  set κ : ComplexModel N × ComplexModel n → ComplexModel (N + n) :=
    fun q => flatProj m (L q) with hκ
  have hκc : Continuous κ := (flatProj m).continuous.comp L.continuous
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hRo.preimage hκc) (ζ₀, z₀) ht₀R
  have hmaps : ∀ ζ ∈ ball ζ₀ r, ∀ b ∈ ball z₀ r, flatProj m (L (ζ, b)) ∈ R := by
    intro ζ hζ b hb
    have : (ζ, b) ∈ ball (ζ₀, z₀) r := by
      rw [← ball_prod_same]
      exact ⟨hζ, hb⟩
    exact hball this
  refine ⟨⟨i, e, j, m, w₀, Φ, hΦs, hΦf, ζ₀, z₀, hw₀eq, r, hr, V, hVo, fun y hy => hy.2, ψ, h,
    hpsh, heqV, fun ζ hζ b hb => (hmaps ζ hζ b hb).1,
    fun ζ hζ b hb => ((hmaps ζ hζ b hb).2).2⟩, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨hq1, hq2, Φ.center_mem_source, mem_ball_self (half_pos hr), mem_ball_self hr⟩

end General

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal}

theorem exists_preferred_sliceChart_originalSource
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) {q₀ : HyperplaneSpace N × X}
    (hmem : q₀.2 ∈ member p q₀.1) (hsm : ¬ IsSingularPointOfMember (d + 1) p q₀.1 q₀.2) :
    ∃ c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ,
      c.i = chartIndex q₀.1 ∧ c.e = complexChartAt (n := d + 1) q₀.2 ∧
      c.ζ₀ = affineChart (chartIndex q₀.1) q₀.1 ∧ q₀.2 ∈ c.originalSliceAmbientSource c.ζ₀ := by
  obtain ⟨c,hi,he,hζ,hz,hq⟩ := exists_preferred_sliceChart p.contMDiff hφ hmem hsm
  refine ⟨c,hi,he,hζ,?_⟩
  have hx : q₀.2 ∈ c.e.val.source := hq.2.1
  have hzc : c.e.val q₀.2 = c.z₀ := by rw [he,hz]
  have hw : prodModelEquiv N (d + 1) (c.ζ₀,c.e.val q₀.2) ∈ c.Φ.source := by
    rw [hzc,← c.w₀_eq]
    exact c.Φ.center_mem_source
  have hlift : c.tangentLift (originalMemberCoordinateDelete c.m c.z₀) = c.z₀ := by
    ext k
    rcases Fin.eq_self_or_eq_succAbove c.m k with rfl | ⟨j,rfl⟩ <;>
      simp [SliceChart.tangentLift,tangentCoordinateInsert,originalMemberCoordinateDelete,Fin.succAbove_ne]
  change q₀.2 ∈ c.e.val.source ∩ c.e.val ⁻¹'
    ((fun z => prodModelEquiv N (d + 1) (c.ζ₀,z)) ⁻¹' c.Φ.source ∩
      (originalMemberCoordinateDelete c.m) ⁻¹' c.tangentPatch)
  refine ⟨hx,hw,?_⟩
  change c.tangentLift (originalMemberCoordinateDelete c.m (c.e.val q₀.2)) ∈ ball c.z₀ c.r
  rw [hzc,hlift]
  exact mem_ball_self c.r_pos

end SGPT.Trace.Bertini
