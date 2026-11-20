import SGPT.PSH.FiniteCartierGeneratorProduct
import SGPT.PSH.LocalRationalDivisorGrouping

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending HironakaEffectiveDivisorSum InvertibleIdealQuotient
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual reduced invertible ideal of the ORIGINAL canonical prime;
existing codimension-one geometry internally supplies invertibility. -/
def geometricPrimeCarrierEffectiveDivisor (P : GeometricPrimeCarrier (m + 1) M) :
    EffectiveDivisor (m + 1) M :=
  ActualCodimensionOneDivisorCurrent.effectiveDivisor P.subvariety
    (by have h := P.subvariety_codimension; omega)

theorem geometricPrimeCarrierEffectiveDivisor_ideal (P : GeometricPrimeCarrier (m + 1) M) :
    (geometricPrimeCarrierEffectiveDivisor P).ideal = vanishingIdeal (n := m + 1) P.val := by
  change vanishingIdeal (n := m + 1) P.subvariety.carrier = _
  rw [P.subvariety_carrier]

theorem geometricPrimeCarrierEffectiveDivisor_support (P : GeometricPrimeCarrier (m + 1) M) :
    (geometricPrimeCarrierEffectiveDivisor P).support = P.val := by
  rw [geometricPrimeCarrierEffectiveDivisor, ActualCodimensionOneDivisorCurrent.support_effectiveDivisor,
    P.subvariety_carrier]

/-- ORIGINAL D,x alone manufacture the exact finite nearby original family,
a LOCAL denominator, actual reduced generators and a genuine integral Cartier
sum whose WHOLE stalks on ONE original U have the literal product generator. -/
theorem exists_geometric_q_local_integral_cartier_presentation
    (D : EffectiveGeometricQDivisor (m + 1) M) (x : M) :
    ∃ U : Opens M, x ∈ U ∧
      ∃ (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
        (a : {P // 0 < D.coefficient P} → ℕ)
        (g : {P // 0 < D.coefficient P} → M → ℂ),
        (∀ P, P ∈ s ↔ (P.val.val ∩ (U : Set M)).Nonempty) ∧ 0 < d ∧
        (∀ P ∈ s, 0 < a P ∧ D.coefficient P.val = (a P : ℚ) / (d : ℚ)) ∧
        (∀ P ∈ s, MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (g P) U ∧
          ∀ y ∈ U, ∀ h, (vanishingIdeal (n := m + 1) P.val.val).mem y h ↔
            IsInSpanAt (n := m + 1) (· = g P) y h) ∧
        let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
        let G := fun y => ∏ P ∈ s, g P y ^ a P
        MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) G U ∧
        (∀ y ∈ U, ∀ h, F.ideal.mem y h ↔ IsInSpanAt (n := m + 1) (· = G) y h) ∧
        F.support ∩ (U : Set M) = D.support ∩ (U : Set M) ∧
        ∀ y, (∑ P : {P // P ∈ s}, ((D.coefficient P.val.val : ℝ) : EReal) *
          logNormSq (g P.val y)) = (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (G y) := by
  classical
  let I := {P // 0 < D.coefficient P}
  let E : I → EffectiveDivisor (m + 1) M := fun P => geometricPrimeCarrierEffectiveDivisor P.val
  obtain ⟨N, hN, hT⟩ := D.locallyFinite_positive x
  obtain ⟨V, hVN, hV, hxV⟩ := _root_.mem_nhds_iff.mp hN
  choose W hW hxW g hg _hnon hgen using fun P : I => (E P).isInvertible x
  let T := hT.toFinset
  let U : Opens M := ⟨V ∩ ⋂ P ∈ T, W P,
    hV.inter (isOpen_biInter_finset (fun P _ => hW P))⟩
  have hxU : x ∈ U := ⟨hxV, mem_iInter₂.mpr (fun P _ => hxW P)⟩
  have hUN : (U : Set M) ⊆ N := fun _ hy => hVN hy.1
  have hfinite : {P : I | (P.val.val ∩ (U : Set M)).Nonempty}.Finite :=
    hT.subset (fun P hP => hP.mono (inter_subset_inter_right _ hUN))
  let s := hfinite.toFinset
  have hs (P : I) : P ∈ s ↔ (P.val.val ∩ (U : Set M)).Nonempty := hfinite.mem_toFinset
  have hsT : ∀ P ∈ s, P ∈ T := by
    intro P hP
    exact hT.mem_toFinset.mpr (((hs P).mp hP).mono (inter_subset_inter_right _ hUN))
  have hUW : ∀ P ∈ s, (U : Set M) ⊆ W P := by
    intro P hP y hy
    exact mem_iInter₂.mp hy.2 P (hsT P hP)
  obtain ⟨d, a, hd, ha, hlog⟩ := exists_finite_rational_logarithmic_product_grouping s
    (fun P : I => D.coefficient P.val) (fun P _ => P.property)
  have hhol : ∀ P ∈ s, ∀ y ∈ U, HolomorphicAt (m + 1) (g P) y :=
    fun P hP y hy => holomorphicAt_of_mdifferentiableOn (hW P) (hg P) (hUW P hP hy)
  have hgenU : ∀ P ∈ s, ∀ y ∈ U, ∀ h, (E P).ideal.mem y h ↔
      IsInSpanAt (n := m + 1) (· = g P) y h :=
    fun P hP y hy => hgen P y (hUW P hP hy)
  have hsup : ∀ (t : Finset I), (∀ P ∈ t, 0 < a P) →
      (∑ P ∈ t, a P • E P).support = ⋃ P ∈ t, P.val.val := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | @insert P t hPt ih =>
      intro hpos
      rw [Finset.sum_insert hPt, support_add, support_nsmul (E P) (hpos P (by simp)),
        ih (fun Q hQ => hpos Q (Finset.mem_insert_of_mem hQ)),
        geometricPrimeCarrierEffectiveDivisor_support]
      ext y
      simp only [Finset.mem_insert, mem_union, mem_iUnion, exists_prop]
      aesop
  refine ⟨U, hxU, s, d, a, g, hs, hd, ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    refine ⟨(hg P).mono (hUW P hP), ?_⟩
    intro y hy h
    rw [← geometricPrimeCarrierEffectiveDivisor_ideal]
    exact hgenU P hP y hy h
  · intro y hy
    exact (MonomialPart.holomorphicAt_finset_prod s
      (fun P hP => CompanionReduction.holomorphicAt_pow_of (hhol P hP y hy) (a P))).mdifferentiableAt.mdifferentiableWithinAt
  · intro y hy h
    exact finite_cartier_sum_generator_product s E a g y
      (fun P hP => hhol P hP y hy) (fun P hP => hgenU P hP y hy) h
  · rw [hsup s (fun P hP => (ha P hP).1)]
    ext y
    constructor
    · rintro ⟨hy, hyU⟩
      obtain ⟨P, _hP, hyP⟩ := mem_iUnion₂.mp hy
      exact ⟨(D.mem_support y).mpr ⟨P.val, P.property, hyP⟩, hyU⟩
    · rintro ⟨hy, hyU⟩
      obtain ⟨P, hP, hyP⟩ := (D.mem_support y).mp hy
      let PP : I := ⟨P, hP⟩
      exact ⟨mem_iUnion₂.mpr ⟨PP, (hs PP).mpr ⟨y, hyP, hyU⟩, hyP⟩, hyU⟩
  · intro y
    have hprod : (∏ P : {P // P ∈ s}, g P.val y ^ a P.val) =
        ∏ P ∈ s, g P y ^ a P := Finset.prod_coe_sort s (fun P => g P y ^ a P)
    exact (hlog (fun P => g P y)).trans (congrArg
      (fun z => (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq z) hprod)

end SGPT.PSH
