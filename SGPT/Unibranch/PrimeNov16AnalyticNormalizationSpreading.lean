import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGenerators
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! ORIGINAL canonical normal generators, same denominator and monic equations
spread to ONE actual neighbourhood. No spreading/graph certificate is input.
Blueprint: prime-nov16-analytic-normalization-spreading.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric Polynomial
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolGerm
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationSpreading

private theorem cleared_monic_relation {A : Type*} [CommRing A] [IsDomain A]
    {p : A[X]} (hp : p.Monic) {x : FractionRing A} (hx : aeval x p = 0)
    {h g : A} (hg : algebraMap A (FractionRing A) g = algebraMap A (FractionRing A) h * x) :
    g ^ p.natDegree + ∑ j ∈ Finset.range p.natDegree,
      p.coeff j * h ^ (p.natDegree-j) * g ^ j = 0 := by
  have hs := Polynomial.scaleRoots_aeval_eq_zero (r := h) hx
  rw [← hg,aeval_algebraMap_apply,map_eq_zero_iff _ (IsFractionRing.injective A _)] at hs
  rw [aeval_eq_sum_range' (n := p.natDegree+1) (by rw [natDegree_scaleRoots]; omega),
    Finset.sum_range_succ] at hs
  simp only [coeff_scaleRoots,smul_eq_mul] at hs
  rw [Nat.sub_self,pow_zero,mul_one,hp.coeff_natDegree,one_mul] at hs
  exact (add_comm _ _).trans hs

private theorem representative_cleared_relation {n : ℕ} (Z : Set (ComplexModel n))
    (H G : ComplexModel n → ℂ) (C : ℕ → ComplexModel n → ℂ)
    (hH : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ H z)
    (hG : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ G z)
    (hC : ∀ j,∀ᶠ z in 𝓝 0,DifferentiableAt ℂ (C j) z) (d : ℕ)
    (heq : (Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk G hG)) ^ d +
      ∑ j ∈ Finset.range d,
        Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk (C j) (hC j)) *
          Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk H hH) ^ (d-j) *
          Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk G hG) ^ j = 0) :
    ∀ᶠ z in 𝓝 0,z ∈ Z →
      G z ^ d + ∑ j ∈ Finset.range d,C j z * H z ^ (d-j) * G z ^ j = 0 := by
  have hd : ∀ j,∀ᶠ z in 𝓝 0,
      DifferentiableAt ℂ (fun z => C j z * H z ^ (d-j) * G z ^ j) z := fun j =>
    eventually_differentiableAt_mul
      (eventually_differentiableAt_mul (hC j) (eventually_differentiableAt_pow hH _))
      (eventually_differentiableAt_pow hG _)
  let hf := eventually_differentiableAt_add (eventually_differentiableAt_pow hG d)
    (eventually_differentiableAt_sum (Finset.range d) hd)
  have key : HolGerm.mk (fun z => G z ^ d + ∑ j ∈ Finset.range d,
      C j z * H z ^ (d-j) * G z ^ j) hf =
      (HolGerm.mk G hG)^d + ∑ j ∈ Finset.range d,
        HolGerm.mk (C j) (hC j) * (HolGerm.mk H hH)^(d-j) * (HolGerm.mk G hG)^j := by
    rw [HolGerm.mk_add _ _ (eventually_differentiableAt_pow hG d)
      (eventually_differentiableAt_sum (Finset.range d) hd),
      HolGerm.mk_sum _ _ hd,HolGerm.mk_pow G hG d]
    congr 1
  apply mem_vanishingIdeal_mk.mp
  rw [key]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_add,map_sum,map_mul,map_pow] using heq

private theorem rational_monic_relation {d : ℕ} {c : ℕ → ℂ} {H G : ℂ}
    (hH : H ≠ 0) (hrel : G^d + ∑ j ∈ Finset.range d,c j * H^(d-j) * G^j = 0) :
    (G/H)^d + ∑ j ∈ Finset.range d,c j * (G/H)^j = 0 := by
  have hd : H^d ≠ 0 := pow_ne_zero _ hH
  have he : H^d * ((G/H)^d + ∑ j ∈ Finset.range d,c j * (G/H)^j) =
      G^d + ∑ j ∈ Finset.range d,c j * H^(d-j) * G^j := by
    rw [mul_add,Finset.mul_sum,div_pow,mul_div_cancel₀ _ hd]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjd : j ≤ d := (Finset.mem_range.mp hj).le
    rw [div_pow,← Nat.sub_add_cancel hjd,pow_add,Nat.add_sub_cancel]
    field_simp
  exact (mul_eq_zero.mp (he.trans hrel)).resolve_left hd

/-- ORIGINAL irreducible germ and neighbourhood ONLY. Canonical algebra data,
actual representatives, uniform holomorphicity and all carrier equations are
manufactured together; desired spreading/normalization is not an input. -/
theorem exists_original_normal_generators_spread {n : ℕ} {Z N : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    let A := HolGerm (ComplexModel n) ⧸ vanishingIdeal Z
    let B := integralClosure A (FractionRing A)
    ∃ (k : ℕ) (s : Fin k → B) (h : A) (g : Fin k → A) (p : Fin k → A[X]),
      h ≠ 0 ∧ Submodule.span A (range s) = ⊤ ∧
      (∀ i,algebraMap A (FractionRing A) (g i) = algebraMap A (FractionRing A) h *
          (s i : FractionRing A) ∧ (p i).Monic ∧ aeval (s i : FractionRing A) (p i) = 0) ∧
      ∃ (H : ComplexModel n → ℂ) (hH : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ H z)
        (G : Fin k → ComplexModel n → ℂ)
        (hG : ∀ i,∀ᶠ z in 𝓝 0,DifferentiableAt ℂ (G i) z)
        (C : Fin k → ℕ → ComplexModel n → ℂ)
        (hC : ∀ i j,∀ᶠ z in 𝓝 0,DifferentiableAt ℂ (C i j) z) (r : ℝ),
        0 < r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
        Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk H hH) = h ∧
        (∀ i,Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk (G i) (hG i)) = g i) ∧
        (∀ i j,Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk (C i j) (hC i j)) = (p i).coeff j) ∧
        DifferentiableOn ℂ H (ball 0 r) ∧
        (∀ i,DifferentiableOn ℂ (G i) (ball 0 r)) ∧
        (∀ i j,j < (p i).natDegree → DifferentiableOn ℂ (C i j) (ball 0 r)) ∧
        (¬ ∀ᶠ z in 𝓝 0,z ∈ Z → H z = 0) ∧
        ∀ z ∈ Z,z ∈ ball 0 r → H z ≠ 0 → ∀ i,
          (G i z/H z)^(p i).natDegree + ∑ j ∈ Finset.range (p i).natDegree,
            C i j z * (G i z/H z)^j = 0 := by
  let : (vanishingIdeal Z).IsPrime := (isIrreducibleGerm_iff_isPrime hZ.1).mp hZ
  let A := HolGerm (ComplexModel n) ⧸ vanishingIdeal Z
  obtain ⟨k,s,h,g,p,hh,hs,hp⟩ :=
    PrimeNov16AnalyticNormalizationGenerators.exists_original_germ_normal_generators hZ
  obtain ⟨H0,hH0⟩ := Ideal.Quotient.mk_surjective h
  choose G0 hG0 using fun i => Ideal.Quotient.mk_surjective (g i)
  choose C0 hC0 using fun i j => Ideal.Quotient.mk_surjective ((p i).coeff j)
  obtain ⟨H,hH,hHrep⟩ := HolGerm.exists_eq_mk H0
  choose G hG hGrep using fun i => HolGerm.exists_eq_mk (G0 i)
  choose C hC hCrep using fun i j => HolGerm.exists_eq_mk (C0 i j)
  have hHclass : Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk H hH) = h := by
    rw [← hHrep]
    exact hH0
  have hGclass : ∀ i,Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk (G i) (hG i)) = g i := by
    intro i
    rw [← hGrep i]
    exact hG0 i
  have hCclass : ∀ i j,Ideal.Quotient.mk (vanishingIdeal Z) (HolGerm.mk (C i j) (hC i j)) =
      (p i).coeff j := by
    intro i j
    rw [← hCrep i j]
    exact hC0 i j
  have hrel : ∀ i,∀ᶠ z in 𝓝 0,z ∈ Z → (G i z)^(p i).natDegree +
      ∑ j ∈ Finset.range (p i).natDegree,C i j z * H z^((p i).natDegree-j) * G i z^j = 0 := by
    intro i
    apply representative_cleared_relation Z H (G i) (C i) hH (hG i) (hC i) (p i).natDegree
    simpa only [hHclass,hGclass,hCclass] using
      cleared_monic_relation (hp i).2.1 (hp i).2.2 (hp i).1
  have hnonzero : ¬ ∀ᶠ z in 𝓝 0,z ∈ Z → H z = 0 := by
    intro hzero
    apply hh
    rw [← hHclass]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_vanishingIdeal_mk.mpr hzero)
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ H z ∧ (∀ i,DifferentiableAt ℂ (G i) z) ∧
      (∀ i (j : Fin (p i).natDegree),DifferentiableAt ℂ (C i j) z) ∧
      (∀ i,z ∈ Z → (G i z)^(p i).natDegree +
        ∑ j ∈ Finset.range (p i).natDegree,C i j z * H z^((p i).natDegree-j) * G i z^j = 0) ∧ z ∈ N := by
    filter_upwards [hH,eventually_all.mpr hG,
      eventually_all.mpr (fun i => eventually_all.mpr (fun j : Fin (p i).natDegree => hC i j)),
      eventually_all.mpr hrel,hN] with z hzH hzG hzC hzrel hzN
    exact ⟨hzH,hzG,hzC,hzrel,hzN⟩
  obtain ⟨r,hrpos,hr⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨k,s,h,g,p,hh,hs,hp,H,hH,G,hG,C,hC,r,hrpos,?_,hHclass,hGclass,hCclass,
    ?_,?_,?_,hnonzero,?_⟩
  · intro z hz
    exact (hr z hz).2.2.2.2
  · intro z hz
    exact (hr z hz).1.differentiableWithinAt
  · intro i z hz
    exact ((hr z hz).2.1 i).differentiableWithinAt
  · intro i j hj z hz
    exact ((hr z hz).2.2.1 i ⟨j,hj⟩).differentiableWithinAt
  · intro z hzZ hz hHz i
    exact rational_monic_relation hHz ((hr z hz).2.2.2.1 i hzZ)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationSpreading
