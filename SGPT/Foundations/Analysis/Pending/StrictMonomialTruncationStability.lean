import SGPT.Foundations.Analysis.Pending.TruncatedIntegrabilityFullCoordinateOrders
import SGPT.Foundations.Analysis.Pending.MultiplierHaarLinearTransport

set_option autoImplicit false

/-! # Strict monomial truncation stability with actual coordinate transport -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.StrictMonomialTruncationStability

open FirstPass HolomorphicGermReducednessBridge

noncomputable section

/-- The actual coordinate isometry transports all original truncation families
and integrals; the original test supplies its order before the level decrease. -/
theorem exists_coordinate_factor_with_strict_threshold {m : ℕ}
    (j : Fin (m + 2)) (A : ℕ) {q : ℝ} {F : ComplexModel (m + 2) → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), F z ≠ 0)
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 2) → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {HolGerm.mk (fun z : ComplexModel (m + 2) => z j)
          (eventually_differentiableAt_coordinate j) ^ A} ⊔
        (Ideal.span (Set.range fun i : Fin (m + 2) => HolGerm.mk
          (fun z : ComplexModel (m + 2) => z i) (eventually_differentiableAt_coordinate i))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    ∃ (b : ℕ) (H : ComplexModel (m + 2) → ℂ),
      (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ H z) ∧
      F =ᶠ[𝓝 0] (fun z => z j ^ b * H z) ∧
      ∀ q' : ℝ, q' < q → q' * (A : ℝ) < (b : ℝ) + 1 := by
  classical
  let e : Equiv.Perm (Fin (m + 2)) := Equiv.swap j (Fin.last (m + 1))
  let L : ComplexModel (m + 2) ≃L[ℂ] ComplexModel (m + 2) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toContinuousLinearEquiv
  have hL (z : ComplexModel (m + 2)) (i : Fin (m + 2)) : (L z) i = z (e.symm i) := rfl
  have hLinv (z : ComplexModel (m + 2)) (i : Fin (m + 2)) : (L.symm z) i = z (e i) := by
    have hh := congrArg (fun w : ComplexModel (m + 2) => w (e i)) (L.apply_symm_apply z)
    rw [hL, e.symm_apply_apply] at hh
    exact hh
  have hLj (z : ComplexModel (m + 2)) : (L z) j = z (Fin.last (m + 1)) := by
    rw [hL]
    simp [e]
  have hLinvlast (z : ComplexModel (m + 2)) :
      (L.symm z) (Fin.last (m + 1)) = z j := by rw [hLinv]; simp [e]
  have hTinv : Tendsto L.symm (𝓝 (0 : ComplexModel (m + 2))) (𝓝 0) :=
    HolGerm.tendsto_clm_nhds_zero (L.symm : ComplexModel (m + 2) →L[ℂ] ComplexModel (m + 2))
  have hF' : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (F ∘ L) z :=
    eventually_differentiableAt_comp_clm
      (L : ComplexModel (m + 2) →L[ℂ] ComplexModel (m + 2)) hF
  have hne' : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), (F ∘ L) z ≠ 0 := by
    by_contra hn
    have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), F (L z) = 0 := by
      filter_upwards [Filter.not_frequently.mp hn] with z hz
      exact not_ne_iff.mp hz
    have hback : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), F z = 0 := by
      filter_upwards [hTinv.eventually hzero] with z hz
      simpa only [L.apply_symm_apply] using hz
    obtain ⟨z, hz, hz0⟩ := (hne.and_eventually hback).exists
    exact hz hz0
  let t : Fin (m + 2) → HolGerm (ComplexModel (m + 2)) := fun i =>
    HolGerm.mk (fun z : ComplexModel (m + 2) => z i) (eventually_differentiableAt_coordinate i)
  let φ : HolGerm (ComplexModel (m + 2)) ≃+* HolGerm (ComplexModel (m + 2)) :=
    HolGerm.comapEquiv L
  have hcoord (i : Fin (m + 2)) : φ (t i) = t (e.symm i) := by
    dsimp only [φ, t]
    rw [HolGerm.comapEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => hL z i
  have hcoordj : φ (t j) = t (Fin.last (m + 1)) := by
    rw [hcoord]
    simp [e]
  have hmapnormal : Ideal.map φ.toRingHom (Ideal.span {t j ^ A}) =
      Ideal.span {t (Fin.last (m + 1)) ^ A} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    change Ideal.span {φ (t j) ^ A} = _
    rw [hcoordj]
  have hmapcoords : Ideal.map φ.toRingHom (Ideal.span (Set.range t)) =
      Ideal.span (Set.range t) := by
    rw [Ideal.map_span]
    congr 1
    ext g
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.symm i, (hcoord i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨t (e i), ⟨e i, rfl⟩, ?_⟩
      change φ (t (e i)) = t i
      simpa only [e.symm_apply_apply] using hcoord (e i)
  have htrunc' : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 2) → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {t (Fin.last (m + 1)) ^ A} ⊔ (Ideal.span (Set.range t)) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q (F ∘ L) 0 volume := by
    intro N
    obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc N
    let Q' : Fin r → ComplexModel (m + 2) → ℂ := fun i => (Q i) ∘ L
    have hQ' (i : Fin r) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (Q' i) z :=
      eventually_differentiableAt_comp_clm
        (L : ComplexModel (m + 2) →L[ℂ] ComplexModel (m + 2)) (hQ i)
    refine ⟨r, Q', hQ', ?_, ?_⟩
    · intro i
      have hmapped := Ideal.mem_map_of_mem φ.toRingHom (hmem i)
      change φ (HolGerm.mk (Q i) (hQ i)) ∈
        Ideal.map φ.toRingHom (Ideal.span {t j ^ A} ⊔ (Ideal.span (Set.range t)) ^ N) at hmapped
      rw [Ideal.map_sup, Ideal.map_pow, hmapnormal, hmapcoords] at hmapped
      simpa only [φ, HolGerm.comapEquiv_mk, Q'] using hmapped
    · have hint' := (MultiplierHaarLinearTransport.multiplierIntegrableAt_continuousLinearEquiv_iff
        volume volume L (x := (0 : ComplexModel (m + 2)))).mpr
          (by simpa only [L.map_zero] using hint)
      have hlog : generatorLog Q' = generatorLog Q ∘ L := by
        funext z
        rfl
      rw [hlog]
      exact hint'
  obtain ⟨b, G, hG, hfactor, _hfreq, hthreshold⟩ :=
    WeightedTruncationNormalThreshold.exists_normal_factor_with_strict_threshold A hF' hne' htrunc'
  have hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (G ∘ L.symm) z :=
    eventually_differentiableAt_comp_clm
      (L.symm : ComplexModel (m + 2) →L[ℂ] ComplexModel (m + 2)) hG
  refine ⟨b, G ∘ L.symm, hH, ?_, hthreshold⟩
  filter_upwards [hTinv.eventually hfactor] with z hz
  simpa only [Function.comp_apply, L.apply_symm_apply, hLinvlast] using hz

/-- Actual source integrals for every monomial truncation return genuine
lower-level SNC multiplier membership of the same original arbitrary test. -/
theorem multiplierIntegrableAt_of_all_monomial_truncations {m : ℕ}
    (a : Fin (m + 2) → ℕ) {q q' : ℝ} (hq' : 0 < q') (hqq' : q' < q)
    {F : ComplexModel (m + 2) → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), F z ≠ 0)
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 2) → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {∏ j : Fin (m + 2), HolGerm.mk (fun z : ComplexModel (m + 2) => z j)
          (eventually_differentiableAt_coordinate j) ^ a j} ⊔
        (Ideal.span (Set.range fun j : Fin (m + 2) => HolGerm.mk
          (fun z : ComplexModel (m + 2) => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    MultiplierIntegrableAt (fun z : ComplexModel (m + 2) =>
      ∑ j, (((2 * (a j : ℝ)) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖))
      q' F 0 volume := by
  classical
  obtain ⟨d, H, hH, _hHne, heq, hnot⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hF hne
  let t : Fin (m + 2) → HolGerm (ComplexModel (m + 2)) := fun i =>
    HolGerm.mk (fun z : ComplexModel (m + 2) => z i) (eventually_differentiableAt_coordinate i)
  have hthreshold (j : Fin (m + 2)) : q' * (a j : ℝ) < (d j : ℝ) + 1 := by
    have hI : Ideal.span {∏ i : Fin (m + 2), t i ^ a i} ≤ Ideal.span {t j ^ a j} := by
      apply Ideal.span_le.mpr
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    have htruncj : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 2) → ℂ)
        (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ (Q i) z),
        (∀ i, HolGerm.mk (Q i) (hQ i) ∈
          Ideal.span {t j ^ a j} ⊔ (Ideal.span (Set.range t)) ^ N) ∧
        MultiplierIntegrableAt (generatorLog Q) q F 0 volume := by
      intro N
      obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc N
      exact ⟨r, Q, hQ, fun i => (sup_le_sup hI le_rfl) (hmem i), hint⟩
    obtain ⟨b, G, hG, hfactor, hbound⟩ :=
      exists_coordinate_factor_with_strict_threshold j (a j) hF hne htruncj
    have hbd := TruncatedIntegrabilityFullCoordinateOrders.normal_exponent_le_full_coordinate_order
      j d hF hH hG heq hfactor (hnot j)
    have hbdR : (b : ℝ) ≤ (d j : ℝ) := by exact_mod_cast hbd
    exact (hbound q' hqq').trans_le (add_le_add hbdR le_rfl)
  have hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)),
      ContinuousAt (fun _ : ComplexModel (m + 2) => (0 : ℝ)) z :=
    Eventually.of_forall fun _ => continuousAt_const
  simpa only [EReal.coe_zero, add_zero] using
    HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
      d (fun j => (a j : ℝ)) hq' hH heq hρ hthreshold

end
end SGPT.Foundations.Analysis.Pending.StrictMonomialTruncationStability
