import SGPT.PSH.AtlasLogLocalIntegral
import SGPT.PSH.NativeCommonCartierWithin
import SGPT.PSH.GeometricQOpenCartierCompatibility
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

/-! Genuine native logarithmic reconstruction from the actual Cartier/product
and coefficient fields manufactured by the ORIGINAL source input. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff Classical
universe u

/-- In actual native dimension0 every genuine QPSH function has local real
bounded singleton presentations and an actual EMPTY logarithmic prime family. -/
theorem native_log_of_qpsh_dim_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    (D : EffectiveGeometricQDivisor 0 M) {u : M → EReal}
    (hu : (ofFixedModel 0 M).IsQPSH u) : NativeHasLogSingularitiesAlongAnyDimension D u := by
  refine ⟨hu,?_⟩
  intro x
  let U : Opens M := ⟨{x},RooftopDimZero.isOpen_singleton_of_dim_zero rfl x⟩
  have hb : u x≠⊥ := RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl
    hu.locallyNondegenerate x
  have hxfinite : u x=(u x).toReal := (EReal.coe_toReal (hu.ne_top x) hb).symm
  refine ⟨U,Set.mem_singleton x,0,(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),
    (fun i => Fin.elim0 i),(fun _ => (u x).toReal),|(u x).toReal|,
    (fun i => Fin.elim0 i),(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),
    (fun i => Fin.elim0 i),(fun P => isEmptyElim P),abs_nonneg _,(fun _ => le_refl _),?_⟩
  intro q
  have hqx : q.val=x := q.property
  simp only [Finset.univ_eq_empty,Finset.sum_empty,zero_add,hqx]
  exact hxfinite

/-- The independently defined genuine Cartier divisor/product, complete
coefficient dictionary and bounded real equation reconstruct every actual
native local prime/equation/remainder field by existing actual factorization. -/
theorem native_log_of_cartier_equation {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveGeometricQDivisor n M) (u : M → EReal)
    (hu : (ofFixedModel n M).IsQPSH u)
    (d : ℕ) (hd : 0<d) (H : EffectiveDivisor n M) (G : M → ℂ)
    (hcoeff : ∀ Q : GeometricPrimeCarrier n M,
      D.coefficient Q=(nativeCartierCoefficientAny H Q : ℚ)/(d : ℚ))
    (hgen : ∀ q,HolomorphicAt n G q ∧ ∀ g,H.ideal.mem q g ↔ IsInSpanAt (n := n) (· = G) q g)
    (R : M → ℝ) (C : ℝ) (hC : 0≤C) (hR : ∀ q,|R q|≤C)
    (hlog : ∀ q,u q=(((1/(d : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (G q)+(R q : EReal)) :
    NativeHasLogSingularitiesAlongAnyDimension D u := by
  cases n with
  | zero => exact native_log_of_qpsh_dim_zero D hu
  | succ m =>
    refine ⟨hu,?_⟩
    intro x
    have hdQ : (0 : ℚ)<d := by exact_mod_cast hd
    obtain ⟨U,hx,_hUN,_hgenU,r,W,a,p,_v,RU,CU,hW,ha,hp,hideal,_hv,_hfactor,hCartier,hCU,hRU,hlogU⟩ :=
      exists_native_common_open_cartier_prime_logarithms_within H x G
        (Eventually.of_forall hgen) (1/(d : ℚ)) (by positivity) u R
        ⟨C,hC,Eventually.of_forall hR⟩ (Eventually.of_forall hlog) univ Filter.univ_mem
    refine ⟨U,hx,r,W,(fun i => (1/(d : ℚ))*(a i : ℚ)),p,RU,CU,hW,
      (fun i => mul_pos (by positivity) (by exact_mod_cast ha i)),hp,hideal,?_,hCU,hRU,hlogU⟩
    intro Q
    have hQ : (Q.val ∩ (Subtype.val : U → M) ⁻¹' (univ : Set M)).Nonempty := by
      obtain ⟨q,hq⟩ := Q.nonempty
      exact ⟨q,hq,mem_univ _⟩
    have hreader := geometricQDivisorOpenRestriction_coefficient_of_local_cartier_coefficients
      D H (1/(d : ℚ)) (by positivity) univ
      (fun P _ => by
        have h := hcoeff P
        change D.coefficient P=(cartierGeometricPrimeCoefficient H P : ℚ)/(d : ℚ) at h
        rw [h]
        ring)
      U Q hQ
    change (geometricQDivisorOpenRestriction D U).coefficient Q = _
    rw [hreader,hCartier,cartierGeometricPrimeCoefficient_finset_sum,Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : W i=Q
    · simp [cartierGeometricPrimeCoefficient_reduced,hi,div_eq_mul_inv,mul_comm]
    · simp [cartierGeometricPrimeCoefficient_reduced,hi,Ne.symm hi]

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL source logs alone produce a complete genuine native logarithmic
predicate on an actual original-open component. Every model/divisor/equation
and native regularity field is manufactured; none is a source premise. -/
theorem original_log_exists_local_native
    {D : AtlasEffectiveGeometricQDivisor A} {u : X → EReal}
    (hu : SourceHasLogSingularitiesAlong D u) (x : X) :
    ∃ (U : Opens X) (hx : x∈U),
      letI := A.openRestriction_paracompactSpace U
      let p : U := ⟨x,hx⟩
      letI := (A.openRestriction U).componentChartedSpace p
      letI := (A.openRestriction U).componentComplexManifold_of_paracompact p
      NativeHasLogSingularitiesAlongAnyDimension (D.nativeOpenRestrictionComponent U p)
        (fun q : (A.openRestriction U).componentOpen p => u q.val.val) := by
  obtain ⟨U,hx,d,H,G,R,C,hd,hqpsh,hC,hR,hcoef,hgen,hlog⟩ := original_log_local_component_integral hu x
  let := A.openRestriction_paracompactSpace U
  let p : U := ⟨x,hx⟩
  let := (A.openRestriction U).componentChartedSpace p
  let := (A.openRestriction U).componentComplexManifold_of_paracompact p
  exact ⟨U,hx,native_log_of_cartier_equation _ _ hqpsh d hd H G hcoef hgen R C hC hR hlog⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
