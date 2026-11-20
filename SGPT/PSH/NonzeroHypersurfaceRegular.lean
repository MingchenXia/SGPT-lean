import SGPT.PSH.CartierComponentOrders
import SGPT.Foundations.Analysis.Pending.ActualHolomorphicGermFactoriality
import SGPT.Foundations.Analysis.Pending.ActualPrimeRegularFiniteAvoidance
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- An original nonzero holomorphic germ vanishing at the center internally
produces a prime power and the same actual nondivisible holomorphic cofactor. -/
theorem exists_holomorphic_prime_power_cofactor {m : ℕ}
    (f : ComplexModel (m + 1) → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hF : HolGerm.mk f hf ≠ 0) (hzero : f 0 = 0) :
    ∃ (q g : ComplexModel (m + 1) → ℂ) (a : ℕ)
      (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
      (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z),
      Prime (HolGerm.mk q hq) ∧ 0 < a ∧
        ¬HolGerm.mk q hq ∣ HolGerm.mk g hg ∧
        f =ᶠ[𝓝 0] fun z => q z ^ a * g z := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  have hnu : ¬IsUnit (HolGerm.mk f hf) := by
    rw [HolGerm.isUnit_iff_eval_ne_zero, HolGerm.eval_mk, hzero]
    simp
  obtain ⟨Q, hQi, hQdiv⟩ := WfDvdMonoid.exists_irreducible_factor hnu hF
  have hQ : Prime Q := irreducible_iff_prime.mp hQi
  obtain ⟨G, hfactor, hnot⟩ :=
    (FiniteMultiplicity.of_prime_left hQ hF).exists_eq_pow_mul_and_not_dvd
  obtain ⟨q, hq, hQrep⟩ := HolGerm.exists_eq_mk Q
  obtain ⟨g, hg, hGrep⟩ := HolGerm.exists_eq_mk G
  let a := multiplicity Q (HolGerm.mk f hf)
  have heq : HolGerm.mk f hf = HolGerm.mk (fun z => q z ^ a * g z)
      (eventually_differentiableAt_mul (eventually_differentiableAt_pow hq a) hg) := by
    rw [HolGerm.mk_mul (fun z => q z ^ a) g (eventually_differentiableAt_pow hq a) hg,
      HolGerm.mk_pow q hq a, ← hQrep, ← hGrep]
    exact hfactor
  exact ⟨q, g, a, hq, hg, by simpa only [hQrep] using hQ,
    multiplicity_pos_of_dvd hQdiv, by simpa only [hQrep, hGrep] using hnot,
    HolGerm.mk_eq_mk_iff.mp heq⟩

/-- The ORIGINAL possibly reducible/nonreduced nonzero equation supplies
actual codimension-one regular zeros in every origin neighborhood. -/
theorem frequently_regular_zero_of_nonzero_holomorphic_germ {m : ℕ}
    (f : ComplexModel (m + 1) → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hF : HolGerm.mk f hf ≠ 0) (hzero : f 0 = 0) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      f z = 0 ∧ RegularAtDim (n := m + 1) {w | f w = 0} z m := by
  obtain ⟨q, g, a, hq, hg, hQ, ha, hnot, heq⟩ :=
    exists_holomorphic_prime_power_cofactor f hf hF hzero
  have hfreq := ActualPrimeRegularFiniteAvoidance.frequently_regular_zero_avoiding_finite_family
    q hq hQ (fun _ : Fin 1 => g) (fun _ => hg) (fun _ => hnot)
  obtain ⟨N, hNsub, hN, h0N⟩ := _root_.mem_nhds_iff.mp (hg.and heq)
  rw [Filter.frequently_iff]
  intro S hS
  obtain ⟨z, hzS, ⟨⟨hqzero, hqreg, hgtest⟩, hzN⟩⟩ :=
    Filter.frequently_iff.mp (hfreq.and_eventually (hN.mem_nhds h0N)) hS
  have hgne : g z ≠ 0 := hgtest 0
  have hznear : ∀ᶠ w in 𝓝 z, w ∈ N := hN.mem_nhds hzN
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ N ∧ g w ≠ 0 :=
    hznear.and ((hNsub hzN).1.continuousAt.eventually_ne hgne)
  obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp hnear
  have hzeros : {w | q w = 0} ∩ O = {w | f w = 0} ∩ O := by
    ext w
    constructor
    · rintro ⟨hqw, hwO⟩
      refine ⟨?_, hwO⟩
      change q w = 0 at hqw
      change f w = 0
      have hfw : f w = q w ^ a * g w := (hNsub (hOsub hwO).1).2
      rw [hfw, hqw, zero_pow ha.ne', zero_mul]
    · rintro ⟨hfw, hwO⟩
      refine ⟨?_, hwO⟩
      have hmul : q w ^ a * g w = 0 := (hNsub (hOsub hwO).1).2.symm.trans hfw
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hmul).resolve_right (hOsub hwO).2)
  have hfzero : f z = 0 := by
    have hfz : f z = q z ^ a * g z := (hNsub hzN).2
    rw [hfz, hqzero, zero_pow ha.ne', zero_mul]
  exact ⟨z, hzS, hfzero, RegularPointDimension.regularAtDim_of_inter_eq hO hzO hzeros hqreg⟩

end SGPT.PSH
