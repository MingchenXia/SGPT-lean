import SGPT.PSH.HermitianProductsLocality
import SGPT.PSH.HermitianFrozenCoefficients
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasing

/-!
# Increasing continuity of the actual nonclosed-background product

The base current is the genuine constant current `1`. Ordinary increasing
mixed Bedford--Taylor measure convergence supplies top degree. Constant
semipositive test forms have actual smooth PSH potentials, so adding fixed
smooth slots recovers every lower-degree current coefficient. Finally the
literal finite residual expansion is weakly continuous term by term.

No increasing-continuity claim against an arbitrary singular base current
is made: Lebesgue almost-everywhere limits do not suffice for such bases.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere FirstPass.MixedMongeAmpere StronglyPositiveForms
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorForms LocalBedfordTaylorCollar LocalBedfordTaylorContinuity
  LocalBedfordTaylorDecreasing LocalBedfordTaylorLocality ConstantFormProducts
  LocalBedfordTaylorCanonicalTraceMeasure LocalBedfordTaylorSmoothTraceMeasure
  BedfordTaylor
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The actual test forms on which a current sequence converges form a
real linear subspace. Projection is used only to state the subspace on
the ambient alternating forms; it is the identity on `formSpan`. -/
def weakConvergenceForms {r : ℕ} (T : ℕ → LocalProductCurrent n U r)
    (T₀ : LocalProductCurrent n U r) : Submodule ℝ (RealForm n (2 * r)) where
  carrier := {γ | ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => T j (formProj n r γ) φ) atTop
    (𝓝 (T₀ (formProj n r γ) φ))}
  zero_mem' := by
    intro φ
    simpa only [map_zero, LinearMap.zero_apply, _root_.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  add_mem' := by
    intro γ δ hγ hδ φ
    simpa only [map_add, LinearMap.add_apply, _root_.add_apply] using (hγ φ).add (hδ φ)
  smul_mem' := by
    intro c γ hγ φ
    simpa only [map_smul, LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul] using
      (hγ φ).const_mul c

/-- A smooth wedge by an actual constant form is evaluation on its
literal prescribed-degree exterior product. -/
theorem wedgeForm_constant_apply {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m) (β : formSpan n k) (γ : formSpan n r)
    (φ : 𝓓(U, ℝ)) :
    wedgeForm h T (contDiffOn_const (c := (β : RealForm n (2 * k)))) γ φ =
      T (wedgeSpan n h γ β) φ := by
  rw [wedgeForm_apply_eq h T contDiffOn_const (fun _ _ => β.property)
    (fun _ : Unit => fun _ : ComplexModel n => (1 : ℝ)) (fun _ => contDiffOn_const)
    (fun _ => β) (fun _ _ => by simp only [Finset.univ_unique, Finset.sum_singleton, one_smul])]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  congr 1
  ext x
  simp only [mulSmoothOnCLM_apply, mul_one]

/-- Degree transport of the genuine constant current does not choose a
new current. -/
theorem castLPC_oneCurrentOf {a b : ℕ} (ha : a = n) (hb : b = n) (hab : a = b) :
    castLPC hab (oneCurrentOf (U := U) ha) = oneCurrentOf hb := by
  subst hab
  rfl

/-- Top-degree coefficient convergence follows from the proved actual
mixed-measure increasing theorem and its canonical recursive trace identity. -/
theorem tendsto_btProduct_top_of_monotone_ae
    (v : ℕ → Fin n → ComplexModel n → ℝ) (v₀ : Fin n → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (hmono : ∀ i z, z ∈ U → Monotone fun j => v j i z)
    (hae : ∀ i, ∀ᵐ z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    (φ : 𝓓(U, ℝ)) :
    Tendsto (fun j => btProduct n 0 (v j) (oneCurrentOf (Nat.zero_add n))
      (kahlerPower n 0) φ) atTop
      (𝓝 (btProduct n 0 v₀ (oneCurrentOf (Nat.zero_add n)) (kahlerPower n 0) φ)) := by
  let μs : ℕ → Measure (ComplexModel n) := fun j => recursiveMixedTraceMeasure U (v j) (hv j)
  let μ : Measure (ComplexModel n) := recursiveMixedTraceMeasure U v₀ hv₀
  have hadm : IsIncAdmissible n U v₀ (fun i j => v j i) :=
    ⟨hv₀, fun i => isIncApprox_of_monotone_ae (hv₀ i) (fun j => hv j i) (hmono i) (hae i),
      fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  have hlim := incPClaim_all U v₀ (fun i j => v j i) μs μ hadm
    (fun j => BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure (hv j)))
    (BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure hv₀))
    φ φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset
  have hj (j : ℕ) : (∫ z, φ z ∂μs j) =
      btProduct n 0 (v j) (oneCurrentOf (Nat.zero_add n)) (kahlerPower n 0) φ :=
    IsPositive.integral_traceMeasure _ φ
  have h₀ : (∫ z, φ z ∂μ) =
      btProduct n 0 v₀ (oneCurrentOf (Nat.zero_add n)) (kahlerPower n 0) φ :=
    IsPositive.integral_traceMeasure _ φ
  simpa only [hj, h₀] using hlim

/-- Prescribed-degree transport commutes with a genuine smooth wedge. -/
theorem wedgeForm_castLPC_source {a b r k : ℕ} (hab : a = b) (h : r + k = a)
    (T : LocalProductCurrent n U a) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm (h.trans hab) (castLPC hab T) hα = wedgeForm h T hα := by
  subst hab
  rfl

/-- Appending an actual smooth PSH potential whose full Hessian is a
constant form transfers that factor to the literal current test form. -/
theorem btProduct_snoc_constant_hessian_apply (p r : ℕ)
    (T : LocalProductCurrent n U (r + 1 + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + 1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {β : RealForm n 2} (hβ : IsSemipositiveOneOne β)
    {q : ComplexModel n → ℝ} (hq : ContDiff ℝ ∞ q) (hddc : ∀ z, smoothDDC q z = β)
    (γ : formSpan n r) (φ : 𝓓(U, ℝ)) :
    btProduct (p + 1) r (Fin.snoc v q)
      (castLPC (by omega : r + 1 + p = r + (p + 1)) T) γ φ =
      btProduct p (r + 1) v T (wedgeLM r hβ.1 γ) φ := by
  have hdeg : r + 1 + p = r + (p + 1) := by omega
  let C := castLPC hdeg T
  have hC : IsPositive C := isPositive_castLPC hdeg hT
  have hCc : IsClosedAny (r + (p + 1)) C := isClosedAny_castLPC hdeg hTc
  have hlevi : ∀ z ∈ U, ∀ w : ComplexModel n, 0 ≤ leviForm q z w := by
    intro z _ w
    have heq := smoothDDC_complexDiagonal_eq_leviForm (z := z)
      (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) w
    rw [hddc z] at heq
    have hnonneg := (le_div_iff₀ Real.pi_pos).mp (heq ▸ hβ.2 w)
    linarith
  have hbase : ddcMul C q = wedgeForm
      (by omega : r + p + 1 = r + 1 + p) T (contDiffOn_ddcForm hq.contDiffOn) := by
    rw [ddcMul_eq_ddcWedge hC hCc hq.contDiffOn, ddcWedge_eq_wedgeForm]
    exact wedgeForm_castLPC_source (r := r + p) (k := 1) hdeg
      (by omega) T (contDiffOn_ddcForm hq.contDiffOn)
  change btProduct (p + 1) r (Fin.snoc v q) C γ φ = _
  rw [btProduct_succ, Fin.init_snoc, Fin.snoc_last, hbase,
    btProduct_wedgeForm_ddcForm hq.contDiffOn hlevi p r v T (by omega) hT hTc hv,
    ddcWedge_eq_wedgeForm]
  rw [wedgeForm_congr rfl (btProduct p (r + 1) v T)
    (contDiffOn_ddcForm hq.contDiffOn) (contDiffOn_const (c := β))
    (fun z _ => hddc z)]
  have he := wedgeForm_constant_apply rfl (btProduct p (r + 1) v T)
    (⟨β, oneOne_mem_formSpan hβ.1⟩ : formSpan n 1) γ φ
  exact he

/-- Increasing ordinary products against the genuine current `1` converge
in every coefficient. Additional constant semipositive test factors are
realized as fixed smooth PSH slots, reducing recursively to the proved
top-degree mixed-measure increasing theorem. -/
theorem weakTendsto_btProduct_oneCurrent_of_monotone_ae : ∀ (r p : ℕ)
    (hdegree : r + p = n)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ),
    (∀ j i, IsLocallyBoundedPshOn U (v j i)) →
    (∀ i, IsLocallyBoundedPshOn U (v₀ i)) →
    (∀ i z, z ∈ U → Monotone fun j => v j i z) →
    (∀ i, ∀ᵐ z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z))) →
    WeakTendsto (fun j => btProduct p r (v j) (oneCurrentOf (U := U) hdegree))
      (btProduct p r v₀ (oneCurrentOf (U := U) hdegree))
  | 0, p, hdegree, v, v₀, hv, hv₀, hmono, hae => by
    have hp : p = n := by simpa only [Nat.zero_add] using hdegree
    subst p
    let L := weakConvergenceForms
      (fun j => btProduct n 0 (v j) (oneCurrentOf (U := U) hdegree))
      (btProduct n 0 v₀ (oneCurrentOf (U := U) hdegree))
    have hcone : spCone (n := n) 0 ≤ (L : PointedCone ℝ (RealForm n 0)) := by
      apply Submodule.span_le.mpr
      intro β hβ
      rw [mem_singleton_iff] at hβ
      subst β
      change ∀ φ : 𝓓(U, ℝ), Tendsto
        (fun j => btProduct n 0 (v j) (oneCurrentOf (U := U) hdegree)
          (formProj n 0 coordinateWedgeUnit) φ) atTop
        (𝓝 (btProduct n 0 v₀ (oneCurrentOf (U := U) hdegree) (formProj n 0 coordinateWedgeUnit) φ))
      have hproj : formProj n 0 coordinateWedgeUnit = kahlerPower n 0 :=
        formProj_coe (kahlerPower n 0)
      intro φ
      simpa only [hproj] using tendsto_btProduct_top_of_monotone_ae v v₀ hv hv₀ hmono hae φ
    have hspan : formSpan n 0 ≤ L := Submodule.span_le.mpr fun β hβ => hcone hβ
    intro γ φ
    have hγ := hspan γ.property φ
    simpa only [formProj_coe] using hγ
  | r + 1, p, hdegree, v, v₀, hv, hv₀, hmono, hae => by
    let L := weakConvergenceForms
      (fun j => btProduct p (r + 1) (v j) (oneCurrentOf (U := U) hdegree))
      (btProduct p (r + 1) v₀ (oneCurrentOf (U := U) hdegree))
    have hgen : ∀ P ∈ spCone (n := n) r, ∀ β : RealForm n 2,
        IsSemipositiveOneOne β → coordinateWedge P β ∈ L := by
      intro P hP β hβ
      obtain ⟨q, hq, hddc⟩ := HermitianFrozenCoefficients.exists_global_constant_potential β hβ.1
      have hlevi : ∀ z ∈ U, ∀ w : ComplexModel n, 0 ≤ leviForm q z w := by
        intro z _ w
        have heq := smoothDDC_complexDiagonal_eq_leviForm (z := z)
          (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) w
        rw [hddc z] at heq
        have hnonneg := (le_div_iff₀ Real.pi_pos).mp (heq ▸ hβ.2 w)
        linarith
      have hqpsh : PlurisubharmonicOn (fun z => (q z : EReal)) U :=
        plurisubharmonicOn_of_levi_nonneg
          (hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) U.isOpen hlevi
      have hqloc : IsLocallyBoundedPshOn U q :=
        isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_of_psh hq.contDiffOn hqpsh)
      let w : ℕ → Fin (p + 1) → ComplexModel n → ℝ := fun j => Fin.snoc (v j) q
      let w₀ : Fin (p + 1) → ComplexModel n → ℝ := Fin.snoc v₀ q
      have hw (j : ℕ) (i : Fin (p + 1)) : IsLocallyBoundedPshOn U (w j i) := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [w, Fin.snoc_last] using hqloc
        · simpa only [w, Fin.snoc_castSucc] using hv j i
      have hw₀ (i : Fin (p + 1)) : IsLocallyBoundedPshOn U (w₀ i) := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa only [w₀, Fin.snoc_last] using hqloc
        · simpa only [w₀, Fin.snoc_castSucc] using hv₀ i
      have hwmono (i : Fin (p + 1)) : ∀ z, z ∈ U → Monotone fun j => w j i z := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · intro z _
          simpa only [w, Fin.snoc_last] using (monotone_const : Monotone fun _ : ℕ => q z)
        · simpa only [w, Fin.snoc_castSucc] using hmono i
      have hwae (i : Fin (p + 1)) :
          ∀ᵐ z, z ∈ U → Tendsto (fun j => w j i z) atTop (𝓝 (w₀ i z)) := by
        refine Fin.lastCases ?_ (fun i => ?_) i
        · exact Eventually.of_forall fun z _ => by
            simpa only [w, w₀, Fin.snoc_last] using
              (tendsto_const_nhds : Tendsto (fun _ : ℕ => q z) atTop (𝓝 (q z)))
        · simpa only [w, w₀, Fin.snoc_castSucc] using hae i
      have hdegree' : r + (p + 1) = n := by omega
      have hconv := weakTendsto_btProduct_oneCurrent_of_monotone_ae r (p + 1)
        hdegree' w w₀ hw hw₀ hwmono hwae
      let γ : formSpan n r := ⟨P, mem_formSpan_of_mem_spCone hP⟩
      have hproj : formProj n (r + 1) (coordinateWedge P β) = wedgeLM r hβ.1 γ :=
        formProj_coe (wedgeLM r hβ.1 γ)
      change ∀ φ : 𝓓(U, ℝ), Tendsto
        (fun j => btProduct p (r + 1) (v j) (oneCurrentOf (U := U) hdegree)
          (formProj n (r + 1) (coordinateWedge P β)) φ) atTop
        (𝓝 (btProduct p (r + 1) v₀ (oneCurrentOf (U := U) hdegree)
          (formProj n (r + 1) (coordinateWedge P β)) φ))
      rw [hproj]
      intro φ
      have hj (j : ℕ) : btProduct (p + 1) r (w j) (oneCurrentOf (U := U) hdegree') γ φ =
          btProduct p (r + 1) (v j) (oneCurrentOf (U := U) hdegree) (wedgeLM r hβ.1 γ) φ := by
        have h := btProduct_snoc_constant_hessian_apply p r (oneCurrentOf (U := U) hdegree)
          (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (v j) (hv j) hβ hq hddc γ φ
        rw [castLPC_oneCurrentOf (U := U) hdegree hdegree'] at h
        exact h
      have h₀ : btProduct (p + 1) r w₀ (oneCurrentOf (U := U) hdegree') γ φ =
          btProduct p (r + 1) v₀ (oneCurrentOf (U := U) hdegree) (wedgeLM r hβ.1 γ) φ := by
        have h := btProduct_snoc_constant_hessian_apply p r (oneCurrentOf (U := U) hdegree)
          (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) v₀ hv₀ hβ hq hddc γ φ
        rw [castLPC_oneCurrentOf (U := U) hdegree hdegree'] at h
        exact h
      simpa only [hj, h₀] using hconv γ φ
    have hcone : spCone (n := n) (r + 1) ≤ (L : PointedCone ℝ (RealForm n (2 * (r + 1)))) := by
      apply Submodule.span_le.mpr
      intro β hβ
      obtain ⟨P, hP, δ, hδ, rfl⟩ := hβ
      exact hgen P hP δ hδ
    have hspan : formSpan n (r + 1) ≤ L := Submodule.span_le.mpr fun β hβ => hcone hβ
    intro γ φ
    have hγ := hspan γ.property φ
    simpa only [formProj_coe] using hγ

/-- Each literal subset term of the nonclosed Hermitian expansion is
weakly continuous along actual increasing bounded PSH factors. -/
theorem backgroundExpansionTerm_increasing_oneCurrent (p r : ℕ) (hdegree : r + p = n)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (hmono : ∀ i z, z ∈ U → Monotone fun j => v j i z)
    (hae : ∀ i, ∀ᵐ z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    WeakTendsto (fun j => backgroundExpansionTerm p r (v j) hσ (oneCurrentOf (U := U) hdegree) s)
      (backgroundExpansionTerm p r v₀ hσ (oneCurrentOf (U := U) hdegree) s) := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  have hdegree' : r + (p - s.card) + s.card = n := by omega
  unfold backgroundExpansionTerm
  apply weakTendsto_wedgeForm
  rw [castLPC_oneCurrentOf (U := U) hdegree hdegree']
  exact weakTendsto_btProduct_oneCurrent_of_monotone_ae (r + (p - s.card)) s.card
    hdegree' (fun j i => v j (s.orderEmbOfFin rfl i)) (fun i => v₀ (s.orderEmbOfFin rfl i))
    (fun j i => hv j _) (fun i => hv₀ _) (fun i z hz => hmono _ z hz) (fun i => hae _)

/-- Actual nonclosed-background current convergence for the genuine
finite residual expansion, with all ordinary BT terms produced by the
increasing theorem above. The smooth residual need not be closed. -/
theorem backgroundExpansion_increasing_oneCurrent (p r : ℕ) (hdegree : r + p = n)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (hmono : ∀ i z, z ∈ U → Monotone fun j => v j i z)
    (hae : ∀ i, ∀ᵐ z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    WeakTendsto (fun j => backgroundExpansion p r (v j) hσ (oneCurrentOf (U := U) hdegree))
      (backgroundExpansion p r v₀ hσ (oneCurrentOf (U := U) hdegree)) := by
  classical
  intro γ φ
  simp only [backgroundExpansion, LinearMap.sum_apply, _root_.sum_apply]
  exact tendsto_finsetSum _ fun s _ =>
    backgroundExpansionTerm_increasing_oneCurrent p r hdegree v v₀ hv hv₀ hmono hae hσ s γ φ

end SGPT.PSH.HermitianProducts
