import SGPT.Okounkov.NativeHolomorphicGermRing
import SGPT.Okounkov.EffectiveDivisorLocalSections
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Multiplicity

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient

/-- The literal actual inherited-atlas restriction of original holomorphic
germs to the original first flag member. -/
def originalFirstFlagGermRestriction {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : F.tail.carrier) :
    NativeHolGerm (m + 1) F.carrier x.1 →+* NativeHolGerm m F.tail.carrier x :=
  @NativeHolGerm.comap (m + 1) F.carrier F.topology F.charts m F.tail.carrier
    F.tail.topology F.tail.charts F.complex F.tail.complex
    (Subtype.val : F.tail.carrier → F.carrier)
    (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2) x

theorem originalFirstFlagGermRestriction_mk {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : F.carrier → ℂ) (hf : HolomorphicAt (m + 1) f x.1) :
    ((originalFirstFlagGermRestriction F x (NativeHolGerm.mk f hf) :
      NativeHolGerm m F.tail.carrier x) : Germ (𝓝 x) ℂ) =
      (fun y : F.tail.carrier => f y.1) :=
  rfl

/-- Actual original first-divisor regularity produces a nonzero parameter
with zero value and the whole exact kernel of the literal tail restriction.
No parameter, principal-kernel record or residual certificate is supplied. -/
theorem exists_originalFirstFlagGermParameter {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) :
    ∃ t : NativeHolGerm (m + 1) F.carrier x.1, t ≠ 0 ∧ NativeHolGerm.eval t = 0 ∧
      RingHom.ker (originalFirstFlagGermRestriction F x) = Ideal.span {t} := by
  have hInv := BlowupExistenceCodimOne.isInvertible_vanishingIdeal_of_codimOne F.firstDivisor.1
    (smooth_divisor_interior_eq_empty F.firstDivisor)
    (fun y hy => ⟨m, F.firstDivisor.2.2 y hy, rfl⟩)
  obtain ⟨U, hU, hxU, t, htU, htnon, hgen⟩ := hInv x.1
  have ht : HolomorphicAt (m + 1) t x.1 :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU htU hxU
  have htmem := (hgen x.1 hxU t).mpr (isInSpanAt_self rfl ht)
  have htvan : ∀ᶠ y in 𝓝 x.1, y ∈ F.flag (1 : Fin (m + 2)) → t y = 0 := htmem.2
  have htne : NativeHolGerm.mk t ht ≠ 0 := by
    intro hz
    have heq : t =ᶠ[𝓝 x.1] (0 : F.carrier → ℂ) :=
      NativeHolGerm.mk_eq_mk_iff (hg := holomorphicAt_const 0) |>.mp hz
    have hmem : {y | y ∈ U ∧ t y = 0} ∈ 𝓝 x.1 := by
      filter_upwards [hU.mem_nhds hxU, heq] with y hy hzero
      exact ⟨hy, hzero⟩
    obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hmem
    obtain ⟨y, hy, hyne⟩ := htnon V hVopen (fun y hy => (hVsub hy).1) ⟨x.1, hxV⟩
    exact hyne (hVsub hy).2
  refine ⟨NativeHolGerm.mk t ht, htne, ?_, ?_⟩
  · exact htvan.self_of_nhds x.property
  · ext g
    obtain ⟨f, hf, rfl⟩ := NativeHolGerm.exists_eq_mk g
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    have hres : originalFirstFlagGermRestriction F x (NativeHolGerm.mk f hf) = 0 ↔
        (f ∘ (Subtype.val : F.tail.carrier → F.carrier)) =ᶠ[𝓝 x] 0 := by
      rw [Subtype.ext_iff]
      change ((fun y : F.tail.carrier => f y.1) : Germ (𝓝 x) ℂ) =
        ((0 : F.tail.carrier → ℂ) : Germ (𝓝 x) ℂ) ↔ _
      exact Germ.coe_eq
    have hvan : (f ∘ (Subtype.val : F.tail.carrier → F.carrier)) =ᶠ[𝓝 x] 0 ↔
        (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem x.1 f := by
      constructor
      · intro hzero
        obtain ⟨V, hV, hsub⟩ := (mem_nhds_subtype (F.flag (1 : Fin (m + 2))) x _).mp hzero
        refine ⟨hf, ?_⟩
        filter_upwards [hV] with y hy
        intro hyF
        exact hsub (show (⟨y, hyF⟩ : F.tail.carrier) ∈ Subtype.val ⁻¹' V from hy)
      · intro hmem
        filter_upwards [continuous_subtype_val.continuousAt.eventually hmem.2] with y hy
        exact hy y.property
    rw [hres, hvan]
    constructor
    · intro hmem
      obtain ⟨_, q, hq, hfac⟩ := isInSpanAt_eq_iff.mp ((hgen x.1 hxU f).mp hmem)
      refine ⟨NativeHolGerm.mk q hq, ?_⟩
      change NativeHolGerm.mk f hf = NativeHolGerm.mk (fun y => t y * q y) (ht.mul hq)
      apply NativeHolGerm.mk_eq_mk_iff.mpr
      exact hfac.mono fun y hy => hy.trans (mul_comm _ _)
    · rintro ⟨q, heq⟩
      obtain ⟨r, hr, rfl⟩ := NativeHolGerm.exists_eq_mk q
      have hfac : f =ᶠ[𝓝 x.1] fun y => t y * r y :=
        NativeHolGerm.mk_eq_mk_iff (hg := ht.mul hr) |>.mp heq
      refine ⟨hf, ?_⟩
      filter_upwards [hfac, htvan] with y hy htzero
      intro hyF
      rw [hy, htzero hyF, zero_mul]

/-- Genuine original local-ring separation and the internally produced exact
kernel give a finite maximal first order and an actual NONZERO literal tail
quotient for every nonzero original germ. No rank/value certificate is input. -/
theorem exists_originalFirstFlagGermDivision {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    ∃ (t : NativeHolGerm (m + 1) F.carrier x.1) (a : ℕ)
      (q : NativeHolGerm (m + 1) F.carrier x.1),
      t ≠ 0 ∧ NativeHolGerm.eval t = 0 ∧
      RingHom.ker (originalFirstFlagGermRestriction F x) = Ideal.span {t} ∧
      f = t ^ a * q ∧ originalFirstFlagGermRestriction F x q ≠ 0 ∧
      ∀ b : ℕ, t ^ b ∣ f ↔ b ≤ a := by
  obtain ⟨t, htne, hteval, hker⟩ := exists_originalFirstFlagGermParameter F x
  let R := NativeHolGerm (m + 1) F.carrier x.1
  let M : Ideal R := IsLocalRing.maximalIdeal R
  have htM : t ∈ M := by
    change ¬IsUnit t
    rw [NativeHolGerm.isUnit_iff_eval_ne_zero]
    exact fun h => h hteval
  have hfinite : FiniteMultiplicity t f := by
    by_contra hnot
    have hall := FiniteMultiplicity.not_iff_forall.mp hnot
    have hmem : f ∈ ⨅ N : ℕ, M ^ N := by
      refine (Submodule.mem_iInf _).mpr fun N => ?_
      obtain ⟨q, hq⟩ := hall N
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htM N)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing M (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
      at hmem
    exact hf hmem
  obtain ⟨q, hfac, hnot⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  have hres : originalFirstFlagGermRestriction F x q ≠ 0 := by
    intro hzero
    have hmem : q ∈ RingHom.ker (originalFirstFlagGermRestriction F x) := hzero
    rw [hker] at hmem
    exact hnot (Ideal.mem_span_singleton.mp hmem)
  exact ⟨t, multiplicity t f, q, htne, hteval, hker, hfac, hres,
    fun _ => hfinite.pow_dvd_iff_le_multiplicity⟩

end SGPT.Okounkov
