import SGPT.Foundations.Analysis.Pending.SNCSupportedDivisorFixedChartNormalForm
import SGPT.Foundations.Analysis.Pending.PrincipalGeneratorLogPointwiseNormalForm

set_option autoImplicit false

/-! # Every positive full-family principal order belongs to an actual SNC component

Full original stalk generation supplies an all-point coordinate normal form;
its positive orders internally locate genuine active divisor components.
Reference: Demailly, CADG and Analytic Methods, local principal SNC ideals.
-/

open Set Filter Metric
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.SNCPrincipalPositiveCoordinateComponents

open FirstPass FirstPass.HolomorphicIdealSheaves NormalCrossings InvertibleIdealQuotient

noncomputable section


private theorem exists_coordinate_unit_point {n : ℕ} (j : Fin n) {r : ℝ}
    (hr : 0 < r) :
    ∃ z : ComplexModel n, z ∈ ball 0 r ∧ z j = 0 ∧ ∀ i : Fin n, i ≠ j → z i ≠ 0 := by
  classical
  let v : ComplexModel n := WithLp.toLp 2 (fun i => if i = j then 0 else (1 : ℂ))
  let δ : ℝ := r / (‖v‖ + 1)
  let z : ComplexModel n := δ • v
  have hd : 0 < δ := div_pos hr (by positivity)
  have hdR : δ * (‖v‖ + 1) = r := by
    dsimp only [δ]
    exact div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < ‖v‖ + 1))
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    dsimp only [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    nlinarith
  · simp [z, v]
  · intro i hi
    change δ • (if i = j then (0 : ℂ) else 1) ≠ 0
    rw [if_neg hi]
    exact smul_ne_zero hd.ne' one_ne_zero

private theorem coordinate_sum_eq_bot {n : ℕ} (a : Fin n → ℕ)
    (j : Fin n) (hj : 0 < a j) {z : ComplexModel n} (hz : z j = 0) :
    (∑ i : Fin n, ((2 * (a i : ℝ) : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖z i‖)) = ⊥ := by
  classical
  rw [← Finset.add_sum_erase Finset.univ
    (fun i : Fin n => ((2 * (a i : ℝ) : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖z i‖)) (Finset.mem_univ j),
    hz, norm_zero, ENNReal.ofReal_zero, ENNReal.log_zero,
    EReal.coe_mul_bot_of_pos (by positivity : 0 < 2 * (a j : ℝ)), EReal.bot_add]

/-- The actual complete principal presentation produces one all-point normal
form whose every positive order corresponds to a genuine active SNC component. -/
theorem exists_normal_form_with_active_components {n s : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support = ⋃ H ∈ E, H) (x : M)
    (G : Fin s → M → ℂ) (hG : ∀ i, HolomorphicAt n (G i) x)
    (hgen : ∀ F : M → ℂ, D.ideal.mem x F ↔
      IsInSpanAt (n := n) (· ∈ Set.range G) x F) :
    ∃ (S : Fin E.length → Finset (Fin n))
      (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
      Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
      (∀ i, x ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | x ∈ E.get i} ∧
      (∀ i, x ∈ E.get i → ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i))) ∧
      ∃ (a : Fin n → ℕ) (η : ComplexModel n → ℝ) (R : ℝ), 0 < R ∧
        (∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt η z) ∧
        (∀ z ∈ ball (0 : ComplexModel n) R,
          generatorLog (fun i w => G i ((complexChartAt (n := n) x).val.symm (Φ.invFun w))) z =
            (∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) *
              ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) ∧
        ∀ j : Fin n, 0 < a j → ∃ i : Fin E.length, x ∈ E.get i ∧ S i = {j} := by
  classical
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, hinj⟩ := hE.2 x
  obtain ⟨U, hU, hxU, g, hg, _hnon, hprincipal, hgT, hzero, hnon, _⟩ :=
    SNCSupportedDivisorFixedChartNormalForm.exists_unit_monomial_generator_in_adapted_coordinates
      D E hE hsupport.le x S Φ hsrc h0 hcard hflat
  let e := complexChartAt (n := n) x
  let T : ComplexModel n → M := fun z => e.val.symm (Φ.invFun z)
  let GT : Fin s → ComplexModel n → ℂ := fun i z => G i (T z)
  let gT : ComplexModel n → ℂ := fun z => g (T z)
  have hGT (i : Fin s) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (GT i) z := by
    have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
      x Φ h0 G (G i)).mp (isInSpanAt_self ⟨i, rfl⟩ (hG i))
    exact h.1.mono fun _ hz => hz.differentiableAt
  have hfull : ∀ F : M → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range G) x F ↔ IsInSpanAt (n := n) (· = g) x F :=
    fun F => (hgen F).symm.trans (hprincipal x hxU F)
  have hfullT := ManifoldPrincipalSpanAdaptedTransport.full_principal_generation_comp_adapted
    x Φ hsrc h0 G g hfull
  have hspan := PrincipalFiniteSpanLogNorm.ideal_span_eq_of_full_principal_generation
    GT hGT hgT hfullT
  obtain ⟨a, η, R₀, hR₀, hη, hweight⟩ :=
    PrincipalGeneratorLogPointwiseNormalForm.exists_generatorLog_coordinate_normal_form
      GT hGT hgT hnon hspan hzero
  obtain ⟨Q, hQ, hGQ, k, hk⟩ :=
    PrincipalHolomorphicGeneratorQuotients.exists_holomorphic_quotients_of_principal_span
      GT hGT hgT hnon hspan
  have hQk : ∀ᶠ z in 𝓝 (0 : ComplexModel n), Q k z ≠ 0 :=
    (hQ k).self_of_nhds.continuousAt.eventually_ne hk
  have h0t : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val x := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have hT0 : T 0 = x := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_complexChartAt_source x)]
  have hTc : ContinuousAt T 0 :=
    (e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))).comp
      ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)).continuousAt)
  have ht : Tendsto T (𝓝 0) (𝓝 x) := by simpa only [hT0] using hTc.tendsto
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hxi).elim
    · have hi : ∀ᶠ y in 𝓝 x, y ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hxi
      exact hi.mono fun _ hz _ => hz
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      z ∈ ball 0 R₀ ∧ z ∈ Φ.target ∧ T z ∈ U ∧
      (∀ i : Fin E.length, x ∉ E.get i → T z ∉ E.get i) ∧
      Q k z ≠ 0 ∧ GT k z = gT z * Q k z := by
    filter_upwards [ball_mem_nhds _ hR₀, Φ.isOpen_target.mem_nhds h0t,
      ht.eventually (hU.mem_nhds hxU), ht.eventually havoid, hQk, hGQ k]
      with z hz hzΦ hzU hzavoid hzQ hzGQ
    exact ⟨hz, hzΦ, hzU, hzavoid, hzQ, hzGQ⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨S, Φ, hsrc, h0, hcard, hinj, hflat, a, η, R, hR,
    (fun z hz => hη z (hball hz).1), (fun z hz => hweight z (hball hz).1), ?_⟩
  intro j hj
  obtain ⟨z, hz, hzj, hzother⟩ := exists_coordinate_unit_point j hR
  obtain ⟨hzR₀, hzΦ, hzU, hzavoid, hzQ, hzGQ⟩ := hball hz
  have hbot : generatorLog GT z = ⊥ := by
    rw [hweight z hzR₀, coordinate_sum_eq_bot a j hj hzj, EReal.bot_add]
  have hGk : GT k z = 0 := (generatorLog_eq_bot_iff GT z).mp hbot k
  have hgz : gT z = 0 := (mul_eq_zero.mp (hzGQ.symm.trans hGk)).resolve_right hzQ
  have hsupportz : T z ∈ D.support :=
    (SNCDivisorLocalGenerator.mem_support_iff_generator_eq_zero D
      (holomorphicAt_of_mdifferentiableOn hU hg hzU) (hprincipal (T z) hzU)).mpr hgz
  have hmem : ∃ H ∈ E, T z ∈ H := by
    rw [hsupport] at hsupportz
    obtain ⟨H, hH⟩ := mem_iUnion.mp hsupportz
    obtain ⟨hHE, hzH⟩ := mem_iUnion.mp hH
    exact ⟨H, hHE, hzH⟩
  obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp hmem
  have hxi : x ∈ E.get i := by
    by_contra h
    exact hzavoid i h hi
  have htarget : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hzΦ)
  have hzsource : T z ∈ e.val.source := e.val.map_target htarget
  have hchart : e.val (T z) = Φ.invFun z := e.val.right_inv htarget
  have hφ : e.val (T z) ∈ Φ.source := by rw [hchart]; exact Φ.mapsTo_invFun hzΦ
  have heq : Φ.toFun (e.val (T z)) = z := by rw [hchart, Φ.right_inv z hzΦ]
  have hsub : z ∈ coordSubspace (S i) := by
    rw [← heq]
    exact (hflat i hxi hzsource hφ).mp hi
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp (hcard i hxi)
  have hlj : l = j := by
    by_contra hn
    exact hzother l hn (hsub l (by rw [hl]; exact Finset.mem_singleton_self l))
  exact ⟨i, hxi, by simpa only [hlj] using hl⟩

end
end SGPT.Foundations.Analysis.Pending.SNCPrincipalPositiveCoordinateComponents
