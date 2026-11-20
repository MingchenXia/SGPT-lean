import SGPT.Foundations.Analysis.Pending.SNCPrincipalFiniteGeneratorNormalForm

set_option autoImplicit false

/-! # Actual support containment supplies monomials and whole-family weights in a fixed adapted chart -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.SNCSupportedDivisorFixedChartNormalForm

open FirstPass FirstPass.HolomorphicIdealSheaves NormalCrossings InvertibleIdealQuotient

noncomputable section

private theorem frequently_ne_zero_of_coordinate_zero_locus {n : ℕ}
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hzero : ∀ᶠ z in 𝓝 0, H z = 0 → ∃ j : Fin n, z j = 0) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0 := by
  classical
  obtain ⟨N, hdiv⟩ :=
    HolomorphicCoordinateFactorization.exists_coordinate_product_power_dvd_of_zero_locus hH hzero
  have hprod : (∏ j : Fin n, HolGerm.mk (fun z : ComplexModel n => z j)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ =>
      (HolomorphicCoordinatePrime.prime_coordinate_germ j).ne_zero
  have hnon : HolGerm.mk H hH ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdiv
    exact (pow_ne_zero N hprod) hdiv
  change ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n), ¬ H z ≠ 0
  intro h
  apply hnon
  have heq : H =ᶠ[𝓝 (0 : ComplexModel n)] (0 : ComplexModel n → ℂ) :=
    h.mono fun _ hz => not_ne_iff.mp hz
  exact (HolGerm.mk_eq_mk_iff.mpr heq).trans HolGerm.mk_zero

/-- Actual support containment suffices in the same given adapted chart. -/
theorem exists_unit_monomial_generator_in_adapted_coordinates
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support ⊆ ⋃ H ∈ E, H) (x : M)
    (S : Fin E.length → Finset (Fin n))
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hcard : ∀ i, x ∈ E.get i → (S i).card = 1)
    (hflat : ∀ i, x ∈ E.get i → ∀ {y : M},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i))) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U ∧
      (∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ U, ∀ f : M → ℂ, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ
        (fun w => g ((complexChartAt (n := n) x).val.symm (Φ.invFun w))) z) ∧
      (∀ᶠ z in 𝓝 0, g ((complexChartAt (n := n) x).val.symm (Φ.invFun z)) = 0 →
        ∃ j : Fin n, z j = 0) ∧
      (∃ᶠ z in 𝓝 0, g ((complexChartAt (n := n) x).val.symm (Φ.invFun z)) ≠ 0) ∧
      ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
        (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
        (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
          fun z => H z * ∏ j : Fin n, z j ^ a j := by
  classical
  obtain ⟨U, hU, hxU, g, hg, hnon, hgen⟩ := D.isInvertible x
  let e := complexChartAt (n := n) x
  have h0t : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val x := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  let T : ComplexModel n → M := fun z => e.val.symm (Φ.invFun z)
  have hT0 : T 0 = x := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_chart_source (ComplexModel n) x)]
  have hTc : ContinuousAt T 0 :=
    (e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))).comp
      ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)).continuousAt)
  have hT : Tendsto T (𝓝 0) (𝓝 x) := by
    simpa only [hT0] using hTc.tendsto
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hxi).elim
    · have hi : ∀ᶠ y in 𝓝 x, y ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hxi
      exact hi.mono fun _ hy _ => hy
  let G : ComplexModel n → ℂ := fun z => g (T z)
  have hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z := by
    have hchart := differentiableOn_comp_chartSymm x hg
    have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.isOpen_inter_preimage_symm hU
    filter_upwards [Φ.isOpen_target.mem_nhds h0t, hT.eventually (hU.mem_nhds hxU)] with z hz hzU
    have hcoord : DifferentiableAt ℂ (fun w => g (e.val.symm w)) (Φ.invFun z) :=
      hchart.differentiableAt (hopen.mem_nhds ⟨hsrc (Φ.mapsTo_invFun hz), hzU⟩)
    exact hcoord.comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))
  have hzero : ∀ᶠ z in 𝓝 0, G z = 0 → ∃ j : Fin n, z j = 0 := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0t,
      hT.eventually (hU.mem_nhds hxU), hT.eventually havoid] with z hz hzU hzavoid hGz
    have hsup : T z ∈ D.support :=
      (SNCDivisorLocalGenerator.mem_support_iff_generator_eq_zero D
        (holomorphicAt_of_mdifferentiableOn hU hg hzU) (hgen (T z) hzU)).mpr hGz
    have hmem : ∃ H ∈ E, T z ∈ H := by
      have hsup' := hsupport hsup
      obtain ⟨F, hF⟩ := mem_iUnion.mp hsup'
      obtain ⟨hFE, hzF⟩ := mem_iUnion.mp hF
      exact ⟨F, hFE, hzF⟩
    obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp hmem
    have hxi : x ∈ E.get i := by
      by_contra h
      exact hzavoid i h hi
    have htarget : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hz)
    have hy : T z ∈ e.val.source := e.val.map_target htarget
    have hphi : e.val (T z) ∈ Φ.source := by
      dsimp only [T]
      rw [e.val.right_inv htarget]
      exact Φ.mapsTo_invFun hz
    have heq : Φ.toFun (e.val (T z)) = z := by
      dsimp only [T]
      rw [e.val.right_inv htarget, Φ.right_inv z hz]
    have hsub : z ∈ coordSubspace (S i) := by
      rw [← heq]
      exact (hflat i hxi hy hphi).mp hi
    have hpos : 0 < (S i).card := by rw [hcard i hxi]; norm_num
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact ⟨j, hsub j hj⟩
  obtain ⟨a, H, hH, hH0, hfactor⟩ :=
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus hG hzero
  exact ⟨U, hU, hxU, g, hg, hnon, hgen, hG, hzero,
    frequently_ne_zero_of_coordinate_zero_locus hG hzero, a, H, hH, hH0, hfactor⟩


/-- The literal complete original finite family is retained in the same chart. -/
theorem exists_generatorLog_ae_normal_form_in_adapted_coordinates
    {n s : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support ⊆ ⋃ H ∈ E, H) (x : M)
    (S : Fin E.length → Finset (Fin n))
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hcard : ∀ i, x ∈ E.get i → (S i).card = 1)
    (hflat : ∀ i, x ∈ E.get i → ∀ {y : M},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i)))
    (G : Fin s → M → ℂ) (hG : ∀ i, HolomorphicAt n (G i) x)
    (hgen : ∀ F : M → ℂ, D.ideal.mem x F ↔
      IsInSpanAt (n := n) (· ∈ Set.range G) x F) :
    ∃ (a : Fin n → ℕ) (η : ComplexModel n → ℝ) (R : ℝ), 0 < R ∧
      (∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt η z) ∧
      generatorLog (fun i z => G i ((complexChartAt (n := n) x).val.symm (Φ.invFun z)))
        =ᵐ[volume.restrict (ball 0 R)]
        (fun z => (∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) := by
  classical
  obtain ⟨U, hU, hxU, g, hg, _, hprincipal, hgT, hzero, hnon, _⟩ :=
    exists_unit_monomial_generator_in_adapted_coordinates
      D E hE hsupport x S Φ hsrc h0 hcard hflat
  let T : ComplexModel n → M := fun z =>
    (complexChartAt (n := n) x).val.symm (Φ.invFun z)
  have hfull : ∀ F : M → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range G) x F ↔ IsInSpanAt (n := n) (· = g) x F :=
    fun F => (hgen F).symm.trans (hprincipal x hxU F)
  have hfullT := ManifoldPrincipalSpanAdaptedTransport.full_principal_generation_comp_adapted
    x Φ hsrc h0 G g hfull
  have hGT (i : Fin s) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun w => G i (T w)) z := by
    have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
      x Φ h0 G (G i)).mp (isInSpanAt_self ⟨i, rfl⟩ (hG i))
    exact h.1.mono fun _ hz => hz.differentiableAt
  exact PrincipalFiniteSpanLogNorm.exists_generatorLog_normal_form_of_full_principal_generation
    (fun i z => G i (T z)) hGT hgT hfullT hnon hzero

end
end SGPT.Foundations.Analysis.Pending.SNCSupportedDivisorFixedChartNormalForm
