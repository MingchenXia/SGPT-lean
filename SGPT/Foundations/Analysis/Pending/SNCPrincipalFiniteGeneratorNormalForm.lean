import SGPT.Foundations.Analysis.Pending.ManifoldPrincipalSpanAdaptedTransport
import SGPT.Foundations.Analysis.Pending.PrincipalFiniteSpanLogNorm
import SGPT.Foundations.Analysis.Pending.SNCDivisorLocalGenerator

set_option autoImplicit false

/-! # Genuine SNC principalization supplies the literal complete finite generator-log weight -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.SNCPrincipalFiniteGeneratorNormalForm

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

/-- Natural full finite generation of a genuine SNC divisor supplies the literal entire AE weight. -/
theorem exists_adapted_generatorLog_ae_normal_form {n s : ℕ} {M : Type*}
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
        generatorLog (fun i z => G i ((complexChartAt (n := n) x).val.symm (Φ.invFun z)))
          =ᵐ[volume.restrict (ball 0 R)]
          (fun z => (∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) *
            ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) := by
  classical
  obtain ⟨U, hU, hxU, g, hg, _, hprincipal, S, Φ, hsrc, h0, hcard, hinj, hflat,
      b, K, hK, hK0, hfactor⟩ :=
    SNCDivisorLocalGenerator.exists_adapted_unit_monomial_generator D E hE hsupport x
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
  have hgm : HolomorphicAt n g x := holomorphicAt_of_mdifferentiableOn hU hg hxU
  have hgT : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun w => g (T w)) z := by
    have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
      x Φ h0 (fun _ : Fin 1 => g) g).mp (isInSpanAt_self ⟨0, rfl⟩ hgm)
    exact h.1.mono fun _ hz => hz.differentiableAt
  have hKn : ∀ᶠ z in 𝓝 (0 : ComplexModel n), K z ≠ 0 :=
    hK.self_of_nhds.continuousAt.eventually_ne hK0
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      g (T z) = 0 → ∃ j : Fin n, z j = 0 := by
    filter_upwards [hfactor, hKn] with z hfac hkn hz
    have hp : (∏ j : Fin n, z j ^ b j) = 0 :=
      (mul_eq_zero.mp (hfac.symm.trans hz)).resolve_left hkn
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
    refine ⟨j, ?_⟩
    by_contra hne
    exact (pow_ne_zero (b j) hne) hj
  obtain ⟨a, η, R, hR, hη, heq⟩ :=
    PrincipalFiniteSpanLogNorm.exists_generatorLog_normal_form_of_full_principal_generation
      (fun i z => G i (T z)) hGT hgT hfullT
      (frequently_ne_zero_of_coordinate_zero_locus hgT hzero) hzero
  exact ⟨S, Φ, hsrc, h0, hcard, hinj, hflat, a, η, R, hR, hη, heq⟩

end
end SGPT.Foundations.Analysis.Pending.SNCPrincipalFiniteGeneratorNormalForm
