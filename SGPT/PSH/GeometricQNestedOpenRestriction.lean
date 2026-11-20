import SGPT.PSH.GeometricQOpenBiholomorphicNaturality
import SGPT.PSH.GeometricQOpenCartierCompatibility

/-! Full genuine nested-open Cartier ideals and rational coefficients. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff Classical
universe u

variable {M : Type u} [TopologicalSpace M]

/-- The actual image of the composite of two original open inclusions. -/
def flattenOpen (V : Opens M) (W : Opens V) : Opens M :=
  ⟨Set.range (fun q : W => q.val.val),
    (V.isOpen.isOpenEmbedding_subtypeVal.comp W.isOpen.isOpenEmbedding_subtypeVal).isOpen_range⟩

/-- The genuine range homeomorphism, with the SAME underlying original point. -/
def flattenHomeomorph (V : Opens M) (W : Opens V) : W ≃ₜ flattenOpen V W :=
  (V.isOpen.isOpenEmbedding_subtypeVal.comp W.isOpen.isOpenEmbedding_subtypeVal).isEmbedding.toHomeomorph

@[simp] theorem flattenHomeomorph_val (V : Opens M) (W : Opens V) (q : W) :
    (flattenHomeomorph V W q).val=q.val.val := rfl

@[simp] theorem flattenHomeomorph_symm_val (V : Opens M) (W : Opens V)
    (q : flattenOpen V W) : ((flattenHomeomorph V W).symm q).val.val=q.val :=
  congrArg Subtype.val ((flattenHomeomorph V W).apply_symm_apply q)

variable {n : ℕ} [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual nested inclusions give holomorphy of their range identification. -/
theorem flattenHomeomorph_contMDiff (V : Opens M) (W : Opens V) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (flattenHomeomorph V W) := by
  apply (ContMDiff.iff_comp_isImmersionOfComplement
    (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} (flattenOpen V W))).mpr
  refine ⟨(flattenHomeomorph V W).continuous,?_⟩
  change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (fun q : W => q.val.val)
  exact (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
    (Subtype.val : V → M)).comp
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : W → V))

/-- The actual range inverse is holomorphic through BOTH genuine open subtypes. -/
theorem flattenHomeomorph_symm_contMDiff (V : Opens M) (W : Opens V) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (flattenHomeomorph V W).symm := by
  have hV : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun q : flattenOpen V W => ((flattenHomeomorph V W).symm q).val) := by
    apply (ContMDiff.iff_comp_isImmersionOfComplement
      (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} V)).mpr
    refine ⟨continuous_subtype_val.comp (flattenHomeomorph V W).symm.continuous,?_⟩
    have h : (fun q : flattenOpen V W => ((flattenHomeomorph V W).symm q).val.val)=
        (Subtype.val : flattenOpen V W → M) := funext (flattenHomeomorph_symm_val V W)
    simpa only [Function.comp_def,h] using
      (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (Subtype.val : flattenOpen V W → M))
  apply (ContMDiff.iff_comp_isImmersionOfComplement
    (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} W)).mpr
  exact ⟨(flattenHomeomorph V W).symm.continuous,hV⟩

/-- The ENTIRE Cartier ideal commutes with the genuine nested-open square,
by coherent ideal composition along the literal same point map. -/
theorem nestedOpen_cartier_ideal_square
    (F : EffectiveDivisor n M) (V : Opens M) (W : Opens V) :
    (cartierOpenRestriction (cartierOpenRestriction F V) W).ideal=
      GermIdeal.pullback (m := n) (flattenHomeomorph V W)
        (cartierOpenRestriction F (flattenOpen V W)).ideal := by
  have hF := DivisorMetric.isCoherent_of_isInvertible F.isInvertible
  rw [cartierOpenRestriction_ideal,cartierOpenRestriction_ideal,cartierOpenRestriction_ideal]
  calc
    _ = GermIdeal.pullback (m := n) (fun q : W => q.val.val) F.ideal :=
      (GermIdealTotalTransform.pullback_comp
        (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
          (Subtype.val : V → M))
        (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
          (Subtype.val : W → V)) hF).symm
    _ = _ := GermIdealTotalTransform.pullback_comp
      (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (Subtype.val : flattenOpen V W → M))
      (flattenHomeomorph_contMDiff V W) hF

private theorem qdiv_ext {D E : EffectiveGeometricQDivisor n M}
    (h : ∀ Q,D.coefficient Q=E.coefficient Q) : D=E := by
  cases D
  cases E
  have hc := funext h
  cases hc
  rfl

/-- The ENTIRE genuine rational divisor restriction composes on actual opens.
All coefficients are proved from an internally produced local integral Cartier
representative and full-ideal functoriality; zero-dimensional primes are empty. -/
theorem geometricQOpen_nested (D : EffectiveGeometricQDivisor n M)
    (V : Opens M) (W : Opens V) :
    geometricQDivisorOpenRestrictionAnyDimension
      (geometricQDivisorOpenRestrictionAnyDimension D V) W=
    geometricQDivisorBiholomorphicPreimage
      (geometricQDivisorOpenRestrictionAnyDimension D (flattenOpen V W))
      (flattenHomeomorph V W) (flattenHomeomorph_contMDiff V W)
      (flattenHomeomorph_symm_contMDiff V W) := by
  apply qdiv_ext
  intro Q
  cases n with
  | zero => exact isEmptyElim Q
  | succ m =>
    let e := flattenHomeomorph V W
    let he := flattenHomeomorph_contMDiff (n := m+1) V W
    let hei := flattenHomeomorph_symm_contMDiff (n := m+1) V W
    let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
    let P := K.symm Q
    obtain ⟨q,hq⟩ := Q.nonempty
    have hqP : e q∈P.val := by
      have hc : e ⁻¹' P.val=Q.val :=
        congrArg (fun A : GeometricPrimeCarrier (m+1) W => A.val) (K.apply_symm_apply Q)
      rwa [←hc] at hq
    obtain ⟨N,hqN,s,d,a,_hs,hd,_ha,_hglobal,hopen⟩ :=
      exists_geometric_q_local_integral_global_open_coefficients D q.val.val
    let F := ∑ A ∈ s,a A • geometricPrimeCarrierEffectiveDivisor A.val
    have hdQ : (0 : ℚ)<d := by exact_mod_cast hd
    have hV (A : GeometricPrimeCarrier (m+1) V)
        (hA : (A.val ∩ (Subtype.val : V → M) ⁻¹' (N : Set M)).Nonempty) :
        (geometricQDivisorOpenRestriction D V).coefficient A=
          (1/(d : ℚ))*(cartierGeometricPrimeCoefficient (cartierOpenRestriction F V) A : ℚ) := by
      rw [hopen V A hA]
      ring
    have hleft := geometricQDivisorOpenRestriction_coefficient_of_local_cartier_coefficients
      (geometricQDivisorOpenRestriction D V) (cartierOpenRestriction F V)
      (1/(d : ℚ)) (by positivity) ((Subtype.val : V → M) ⁻¹' (N : Set M))
      hV W Q ⟨q,hq,hqN⟩
    have hright := hopen (flattenOpen V W) P ⟨e q,hqP,by exact hqN⟩
    have horder := cartierGeometricPrimeCoefficient_biholomorphic_of_ideal_eq e he hei
      (cartierOpenRestriction F (flattenOpen V W))
      (cartierOpenRestriction (cartierOpenRestriction F V) W)
      (nestedOpen_cartier_ideal_square F V W) P
    change cartierGeometricPrimeCoefficient
      (cartierOpenRestriction (cartierOpenRestriction F V) W) (K P)=_ at horder
    rw [show K P=Q from K.apply_symm_apply Q] at horder
    change (geometricQDivisorOpenRestriction (geometricQDivisorOpenRestriction D V) W).coefficient Q=
      (geometricQDivisorOpenRestriction D (flattenOpen V W)).coefficient P
    rw [hleft,hright,horder]
    ring

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
