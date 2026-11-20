import SGPT.Foundations.Analysis.Pending.PrincipalAnalyticTruncationStability
import SGPT.Foundations.Analysis.Pending.SNCPrincipalFiniteGeneratorNormalForm

set_option autoImplicit false

/-! # Actual SNC geometry supplies strict weighted stability for the complete family -/

open Set Filter
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.SNCFiniteFamilyTruncationStability

open FirstPass FirstPass.HolomorphicIdealSheaves NormalCrossings InvertibleIdealQuotient

noncomputable section

private theorem holomorphic_adapted {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {F : M → ℂ} (hF : HolomorphicAt n F x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z := by
  have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 (fun _ : Fin 1 => F) F).mp (isInSpanAt_self ⟨0, rfl⟩ hF)
  exact h.1.mono fun _ hz => hz.differentiableAt

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

/-- One genuine adapted coordinate choice supplies the full original-family
strict integral consumer before all later levels, truncations and tests. -/
theorem exists_adapted_strict_truncation_stability {n s : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support = ⋃ H ∈ E, H) (x : M)
    (G : Fin s → M → ℂ) (hG : ∀ i, HolomorphicAt n (G i) x)
    (hgen : ∀ F : M → ℂ, D.ideal.mem x F ↔
      IsInSpanAt (n := n) (· ∈ Set.range G) x F) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
      (hGT : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
        (fun w => G i ((complexChartAt (n := n) x).val.symm (Φ.invFun w))) z),
      Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
      ∀ (q q' : ℝ), 0 < q' → q' < q → ∀ F : ComplexModel n → ℂ,
        (∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel n → ℂ)
          (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z),
          (∀ i, HolGerm.mk (Q i) (hQ i) ∈
            Ideal.span (Set.range fun j => HolGerm.mk
              (fun w => G j ((complexChartAt (n := n) x).val.symm (Φ.invFun w))) (hGT j)) ⊔
            (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
              (fun z : ComplexModel n => z j)
              (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j))) ^ N) ∧
          MultiplierIntegrableAt (generatorLog Q) q F 0 MeasureTheory.volume) →
        MultiplierIntegrableAt
          (generatorLog (fun i w => G i
            ((complexChartAt (n := n) x).val.symm (Φ.invFun w))))
          q' F 0 MeasureTheory.volume := by
  classical
  obtain ⟨U, hU, hxU, g, hg, _hnon, hprincipal, S, Φ, hsrc, h0, _hcard, _hinj,
      _hflat, a, K, hK, hK0, hfactor⟩ :=
    SNCDivisorLocalGenerator.exists_adapted_unit_monomial_generator D E hE hsupport x
  let T : ComplexModel n → M := fun z =>
    (complexChartAt (n := n) x).val.symm (Φ.invFun z)
  let hGT := fun i => holomorphic_adapted x Φ h0 (hG i)
  have hgm : HolomorphicAt n g x := holomorphicAt_of_mdifferentiableOn hU hg hxU
  have hgT := holomorphic_adapted x Φ h0 hgm
  have hfull : ∀ F : M → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range G) x F ↔ IsInSpanAt (n := n) (· = g) x F :=
    fun F => (hgen F).symm.trans (hprincipal x hxU F)
  have hfullT := ManifoldPrincipalSpanAdaptedTransport.full_principal_generation_comp_adapted
    x Φ hsrc h0 G g hfull
  have hspan := PrincipalFiniteSpanLogNorm.ideal_span_eq_of_full_principal_generation
    (fun i z => G i (T z)) hGT hgT hfullT
  have hKn : ∀ᶠ z in 𝓝 (0 : ComplexModel n), K z ≠ 0 :=
    hK.self_of_nhds.continuousAt.eventually_ne hK0
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      g (T z) = 0 → ∃ j : Fin n, z j = 0 := by
    filter_upwards [hfactor, hKn] with z hfac hkn hz
    have hp : (∏ j : Fin n, z j ^ a j) = 0 :=
      (mul_eq_zero.mp (hfac.symm.trans hz)).resolve_left hkn
    obtain ⟨j, _hj, hzero⟩ := Finset.prod_eq_zero_iff.mp hp
    refine ⟨j, ?_⟩
    by_contra hn
    exact (pow_ne_zero (a j) hn) hzero
  refine ⟨Φ, hGT, hsrc, h0, ?_⟩
  intro q q' hq' hqq' F htrunc
  exact PrincipalAnalyticTruncationStability.multiplierIntegrableAt_of_all_principal_truncations
    (fun i z => G i (T z)) hGT hgT
    (frequently_ne_zero_of_coordinate_zero_locus hgT hzero) hspan hzero hq' hqq' htrunc

end
end SGPT.Foundations.Analysis.Pending.SNCFiniteFamilyTruncationStability
