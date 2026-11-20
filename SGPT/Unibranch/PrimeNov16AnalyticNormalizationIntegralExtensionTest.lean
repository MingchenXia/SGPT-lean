import SGPT.Unibranch.PrimeNov16AnalyticNormalizationFaithfulIntegralRadical
import Mathlib.RingTheory.Finiteness.Ideal

/-! Complete faithful integral test criterion WITHOUT a domain/unibranch assumption.
Blueprint: prime-nov16-analytic-normalization-integral-extension-test.tex.
Its power-denominator premise must be geometrically manufactured by an analytic caller. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralExtensionTest

def extensionConductor {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : Ideal A where
  carrier := {a | ∀ b : B,∃ r : A,f a*b=f r}
  zero_mem' := fun b => ⟨0,by simp⟩
  add_mem' := by
    intro a b ha hb z
    obtain ⟨r,hr⟩ := ha z
    obtain ⟨s,hs⟩ := hb z
    exact ⟨r+s,by rw [map_add,add_mul,hr,hs,map_add]⟩
  smul_mem' := by
    intro r a ha z
    obtain ⟨s,hs⟩ := ha z
    exact ⟨r*s,by rw [smul_eq_mul,map_mul,mul_assoc,hs,map_mul]⟩

theorem conductor_eq_top_iff_surjective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    extensionConductor f = ⊤ ↔ Function.Surjective f := by
  constructor
  · intro htop b
    have h1 : (1 : A) ∈ extensionConductor f := by rw [htop]; trivial
    obtain ⟨a,ha⟩ := h1 b
    exact ⟨a,by simpa only [map_one,one_mul] using ha.symm⟩
  · intro hs
    apply top_unique
    intro a _ha b
    obtain ⟨c,rfl⟩ := hs b
    exact ⟨a*c,map_mul f a c |>.symm⟩

theorem radical_multiplier_preserves {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B]
    (hf : Function.Injective (algebraMap A B)) (h : A) (w : B)
    (hw : ∀ u ∈ (Ideal.span {h}).radical,∃ v : A,w*algebraMap A B u=algebraMap A B v) :
    ∀ u ∈ (Ideal.span {h}).radical,∃ v ∈ (Ideal.span {h}).radical,w*algebraMap A B u=algebraMap A B v := by
  intro u hu
  obtain ⟨v,hv⟩ := hw u hu
  let f : A →+* B := algebraMap A B
  have huB : f u ∈ ((Ideal.span {h}).map f).radical := by
    obtain ⟨m,hm⟩ := hu
    refine ⟨m,?_⟩
    rw [← map_pow]
    exact Ideal.mem_map_of_mem f hm
  have hvI : v ∈ (Ideal.span {h}).radical := by
    rw [← PrimeNov16AnalyticNormalizationFaithfulIntegralRadical.radical_contraction hf (Ideal.span {h})]
    change f v ∈ ((Ideal.span {h}).map f).radical
    rw [← hv]
    exact Ideal.mul_mem_left _ w huB
  exact ⟨v,hvI,hv⟩

theorem surjective_of_radical_test_and_power_denominator {A B : Type*}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B] [Algebra.IsIntegral A B]
    (hf : Function.Injective (algebraMap A B)) (h : A)
    (hreg : algebraMap A B h ∈ nonZeroDivisors B)
    (hpower : ∃ N : ℕ,∀ b : B,∃ a : A,algebraMap A B (h^N)*b=algebraMap A B a)
    (htest : (((Ideal.span {h}).radical)*Ideal.span {h}).colon
      ((Ideal.span {h}).radical : Set A) = Ideal.span {h}) :
    Function.Surjective (algebraMap A B) := by
  classical
  by_contra hsurj
  let f : A →+* B := algebraMap A B
  let C := extensionConductor f
  let I := (Ideal.span {h}).radical
  have hCne : C ≠ ⊤ := fun he => hsurj ((conductor_eq_top_iff_surjective f).mp he)
  obtain ⟨N,hN⟩ := hpower
  have hhC : h ∈ C.radical := ⟨N,hN⟩
  have hIC : I ≤ C.radical := by
    have hs : Ideal.span {h} ≤ C.radical := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hhC)
    simpa only [Ideal.radical_idem] using Ideal.radical_mono hs
  have hex : ∃ k : ℕ,I^k ≤ C := Ideal.exists_pow_le_of_le_radical_of_fg hIC I.fg_of_isNoetherianRing
  let k := Nat.find hex
  have hk : I^k ≤ C := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hz
    apply hCne
    apply top_unique
    simpa only [hz,pow_zero,Ideal.one_eq_top] using hk
  have hprev : ¬ I^(k-1) ≤ C := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hk0) (by decide))
  change ¬ ∀ a : A,a ∈ I^(k-1) → a ∈ C at hprev
  push Not at hprev
  obtain ⟨a,ha,haC⟩ := hprev
  change ¬ ∀ b : B,∃ r : A,f a*b=f r at haC
  push Not at haC
  obtain ⟨b,hb⟩ := haC
  let w : B := f a*b
  have hclear : ∀ u ∈ I,∃ v : A,w*f u=f v := by
    intro u hu
    have hau : a*u ∈ I^k := by
      have hm : a*u ∈ I^(k-1)*I := Ideal.mul_mem_mul ha hu
      rwa [← pow_succ,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] at hm
    obtain ⟨v,hv⟩ := (hk hau) b
    refine ⟨v,?_⟩
    change (f a*b)*f u = _
    rw [map_mul] at hv
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hv
  have hstable := radical_multiplier_preserves hf h w hclear
  have hhI : h ∈ I := Ideal.le_radical (Ideal.subset_span (Set.mem_singleton h))
  obtain ⟨c,_hcI,hwc⟩ := hstable h hhI
  have hc : c ∈ (I*Ideal.span {h}).colon (I : Set A) := by
    apply Submodule.mem_colon.mpr
    intro u hu
    obtain ⟨v,hvI,hwv⟩ := hstable u hu
    apply Ideal.mem_mul_span_singleton.mpr
    refine ⟨v,hvI,?_⟩
    change v*h=c*u
    apply hf
    rw [map_mul,map_mul,← hwv,← hwc]
    ring
  rw [htest] at hc
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hc
  have he : w*f h=f r*f h := by rw [hwc,hr,map_mul,mul_comm]
  have hw : w=f r := (isRegular_iff_mem_nonZeroDivisors.mpr hreg).right he
  exact hb r hw

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralExtensionTest
