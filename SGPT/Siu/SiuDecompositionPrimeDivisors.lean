import SGPT.PSH.SharedPrimeGlobalEquality
import SGPT.Foundations.Analysis.Pending.ClosureDifferenceAnalytic
import SGPT.Foundations.Analysis.Pending.HironakaNormalCrossingsBranchOverlap
import SGPT.Foundations.Analysis.Pending.MemberPullback
import SGPT.Foundations.Analysis.Pending.ActualPrimeGermGenericAvoidance

/-!
# Distinct prime divisors meet in a nowhere dense subset

Source: the proof of Siu's decomposition `eq:Siudec`; Xia, *Foundations of pluripotential
theory*, `thm:siu-divisorial-decomposition`, Step 2 (`eq:prime-divisor-component`: "two distinct
prime divisors are not contained in one another") and Step 3 (`D ∩ D'` is a proper analytic subset
of `D` for `D ≠ D'`).

* `SGPT.Siu.eq_of_subset`: a prime divisor contained in another prime divisor is equal to it.  At a
  regular point `x` of `P` the germ of `P` is `{q = 0}` for a flat coordinate `q`, whose germ is
  prime; the vanishing ideal of the germ of `Q ⊇ P` at `x` lies in `(q)`, and two prime divisors
  whose vanishing ideals lie in a common principal prime ideal coincide
  (`SGPT.PSH.geometricPrimeCarrier_eq_of_common_chart_prime`).
* `SGPT.Siu.exists_mem_inter_notMem`: if `P ≠ Q`, every open set meeting `P` contains points of
  `P \ Q` (the identity principle for the irreducible set `P`:
  `ClosureDifferenceAnalytic.eq_of_subset_of_inter_open_subset`).
* `SGPT.Siu.exists_mem_inter_notMem_biUnion`: the same for finitely many prime divisors different
  from `P`, i.e. `P \ (Q₁ ∪ ⋯ ∪ Q_N)` is dense in `P`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending AnalyticGermDecomposition

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

theorem isComplexAnalyticSubset_primeCarrier (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    IsComplexAnalyticSubset (n := m + 1) P.val := by
  rw [← P.subvariety_carrier]
  exact P.subvariety.analytic

theorem isIrreducible_primeCarrier (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    IsComplexAnalyticallyIrreducible (n := m + 1) P.val := by
  rw [← P.subvariety_carrier]
  exact P.subvariety.irreducible_carrier

/-- A prime divisor has a regular point of dimension `m` (codimension one). -/
theorem exists_regularAtDim_primeCarrier (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    ∃ x, RegularAtDim (n := m + 1) P.val x m := by
  obtain ⟨x, -, hx⟩ := P.subvariety.exists_regular_point
  have hdim : P.subvariety.dim = m := by have h := P.subvariety_codimension; omega
  refine ⟨x, ?_⟩
  have h' := hx
  rw [hdim, P.subvariety_carrier] at h'
  exact h'

/-- The derivative of a local biholomorphism is injective at every point of its source. -/
theorem injective_fderiv_localHolomorphicEquivAt {p : ComplexModel (m + 1)}
    (Φ : LocalHolomorphicEquivAt (n := m + 1) p) {a : ComplexModel (m + 1)} (ha : a ∈ Φ.source) :
    Function.Injective (fderiv ℂ Φ.toFun a) := by
  have hb : Φ.toFun a ∈ Φ.target := Φ.mapsTo_toFun ha
  have hdf : DifferentiableAt ℂ Φ.toFun a :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds ha)
  have hdg : DifferentiableAt ℂ Φ.invFun (Φ.toFun a) :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hb)
  have hcomp : HasFDerivAt (Φ.invFun ∘ Φ.toFun)
      ((fderiv ℂ Φ.invFun (Φ.toFun a)).comp (fderiv ℂ Φ.toFun a)) a :=
    hdg.hasFDerivAt.comp a hdf.hasFDerivAt
  have hid : Φ.invFun ∘ Φ.toFun =ᶠ[𝓝 a] id := by
    filter_upwards [Φ.isOpen_source.mem_nhds ha] with z hz
    exact Φ.left_inv z hz
  have hid' : HasFDerivAt (Φ.invFun ∘ Φ.toFun)
      (ContinuousLinearMap.id ℂ (ComplexModel (m + 1))) a :=
    (hasFDerivAt_id a).congr_of_eventuallyEq hid
  have heq := hcomp.unique hid'
  intro v w hvw
  have := congrArg (fun L : ComplexModel (m + 1) →L[ℂ] ComplexModel (m + 1) => L v - L w) heq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hvw, sub_self,
    ContinuousLinearMap.id_apply] at this
  exact sub_eq_zero.mp this.symm

omit [IsComplexManifold (m + 1) M] in
/-- A flat chart of codimension one: the germ of `A` at the centre of `Φ` is the zero set of the
last flat coordinate, whose germ is prime. -/
theorem exists_flat_equation_aux {A : Set M} (e : ComplexChart (m + 1) M)
    {p : ComplexModel (m + 1)} (Φ : LocalHolomorphicEquivAt (n := m + 1) p)
    (hsrc : Φ.source ⊆ e.val.target) (hcenter : Φ.toFun p = 0)
    (hflat : ∀ {y : M}, y ∈ e.val.source → e.val y ∈ Φ.source →
      (y ∈ A ↔ Φ.toFun (e.val y) ∈ complexCoordinatePlane (m + 1) m)) :
    ∃ (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z),
      Prime (HolGerm.mk q hq) ∧
        {w : ComplexModel (m + 1) | w + p ∈ e.val.target ∩ e.val.symm ⁻¹' A} =ᶠ[𝓝 0]
          {z | q z = 0} := by
  let q : ComplexModel (m + 1) → ℂ := fun w => Φ.toFun (w + p) (Fin.last m)
  have htr : Tendsto (fun w : ComplexModel (m + 1) => w + p) (𝓝 0) (𝓝 p) := by
    simpa only [zero_add] using (continuous_add_const p).tendsto (0 : ComplexModel (m + 1))
  have hsrcN : ∀ᶠ w in 𝓝 (0 : ComplexModel (m + 1)), w + p ∈ Φ.source :=
    htr (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z := by
    filter_upwards [hsrcN] with w hw
    have hd : DifferentiableAt ℂ Φ.toFun (w + p) :=
      Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hw)
    exact ((EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ).differentiableAt.comp
      w (hd.comp w (differentiableAt_id.add_const p)))
  have hq0 : q 0 = 0 := by
    change Φ.toFun (0 + p) (Fin.last m) = 0
    rw [zero_add, hcenter]
    rfl
  have hdq : fderiv ℂ q 0 ≠ 0 := by
    have hp0 : p ∈ Φ.source := Φ.center_mem_source
    have hsurj : Function.Surjective (fderiv ℂ Φ.toFun p) :=
      LinearMap.injective_iff_surjective
        (f := ((fderiv ℂ Φ.toFun p : ComplexModel (m + 1) →L[ℂ] ComplexModel (m + 1)) :
          ComplexModel (m + 1) →ₗ[ℂ] ComplexModel (m + 1))) |>.mp
        (injective_fderiv_localHolomorphicEquivAt Φ hp0)
    obtain ⟨v, hv⟩ := hsurj (EuclideanSpace.single (Fin.last m) 1)
    have hd : DifferentiableAt ℂ Φ.toFun (0 + p) := by
      rw [zero_add]
      exact Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp0)
    have hinner : HasFDerivAt (fun w : ComplexModel (m + 1) => Φ.toFun (w + p))
        (fderiv ℂ Φ.toFun p) 0 := by
      rw [hasFDerivAt_comp_add_right p, zero_add]
      rw [zero_add] at hd
      exact hd.hasFDerivAt
    have hderiv : HasFDerivAt q
        ((EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ).comp
          (fderiv ℂ Φ.toFun p)) 0 :=
      (EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ).hasFDerivAt.comp _ hinner
    rw [hderiv.fderiv]
    intro h0
    have := congrArg (fun L : ComplexModel (m + 1) →L[ℂ] ℂ => L v) h0
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hv] at this
    simp at this
  refine ⟨q, hq, HironakaNormalCrossingsBranchOverlap.prime_germ_of_fderiv_ne_zero hq hq0 hdq, ?_⟩
  filter_upwards [hsrcN] with w hw
  have hwt : w + p ∈ e.val.target := hsrc hw
  have hys : e.val.symm (w + p) ∈ e.val.source := e.val.map_target hwt
  have hey : e.val (e.val.symm (w + p)) = w + p := e.val.right_inv hwt
  have hfl := hflat (y := e.val.symm (w + p)) hys (by rw [hey]; exact hw)
  rw [hey] at hfl
  apply propext
  change (w + p ∈ e.val.target ∩ e.val.symm ⁻¹' A) ↔ Φ.toFun (w + p) (Fin.last m) = 0
  constructor
  · intro hmem
    exact (hfl.mp hmem.2) (Fin.last m) (by simp)
  · intro hz
    refine ⟨hwt, hfl.mpr ?_⟩
    intro i hi
    have : i = Fin.last m := Fin.ext (by have := i.isLt; simp at hi ⊢; omega)
    rw [this]
    exact hz

omit [IsComplexManifold (m + 1) M] in
/-- At a regular point of codimension one, the germ of `A` is the zero set of a flat coordinate
`q` whose germ is prime. -/
theorem exists_flat_equation_of_regularAtDim {A : Set M} {x : M}
    (hx : RegularAtDim (n := m + 1) A x m) :
    ∃ (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z),
      Prime (HolGerm.mk q hq) ∧
        AnalyticDescendingChain.chartGerm (n := m + 1) A x =ᶠ[𝓝 0] {z | q z = 0} := by
  obtain ⟨-, -, Φ, hsrc, hcenter, hflat⟩ := hx
  exact exists_flat_equation_aux (complexChartAt (n := m + 1) x) Φ hsrc hcenter hflat

/-- **A prime divisor contained in another prime divisor is equal to it.** -/
theorem eq_of_subset {P Q : SGPT.PSH.GeometricPrimeCarrier (m + 1) M} (h : P.val ⊆ Q.val) :
    P = Q := by
  obtain ⟨x, hx⟩ := exists_regularAtDim_primeCarrier P
  obtain ⟨q, hq, hQ, hgerm⟩ := exists_flat_equation_of_regularAtDim hx
  have hPI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) =
      Ideal.span {HolGerm.mk q hq} := by
    rw [vanishingIdeal_congr hgerm]
    exact (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1
  have hQI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) Q.val x) ≤
      vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) :=
    vanishingIdeal_anti (Eventually.of_forall fun z hz =>
      AnalyticDescendingChain.chartGerm_mono h x hz)
  exact SGPT.PSH.geometricPrimeCarrier_eq_of_common_chart_prime P Q x q hq hQ hPI.le
    (hQI.trans hPI.le)

/-- **Distinct prime divisors meet in a nowhere dense subset**: if `P ≠ Q`, every open set meeting
`P` contains a point of `P` outside `Q`. -/
theorem exists_mem_inter_notMem {P Q : SGPT.PSH.GeometricPrimeCarrier (m + 1) M} (hPQ : P ≠ Q)
    {O : Set M} (hO : IsOpen O) (hne : (P.val ∩ O).Nonempty) :
    ∃ y ∈ P.val ∩ O, y ∉ Q.val := by
  by_contra hcon
  push Not at hcon
  have hV : IsComplexAnalyticSubset (n := m + 1) (P.val ∩ Q.val) :=
    (isComplexAnalyticSubset_primeCarrier P).inter (isComplexAnalyticSubset_primeCarrier Q)
  have heq := ClosureDifferenceAnalytic.eq_of_subset_of_inter_open_subset hV
    (isIrreducible_primeCarrier P)
    inter_subset_left hO hne (fun y hy => ⟨hy.1, hcon y hy⟩)
  exact hPQ (eq_of_subset (fun y hy => (heq.symm ▸ hy : y ∈ P.val ∩ Q.val).2))

/-- **`P \ (Q₁ ∪ ⋯ ∪ Q_N)` is dense in `P`** for prime divisors `Qᵢ ≠ P`. -/
theorem exists_mem_inter_notMem_biUnion {P : SGPT.PSH.GeometricPrimeCarrier (m + 1) M}
    (F : Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) M)) (hPF : P ∉ F)
    {O : Set M} (hO : IsOpen O) (hne : (P.val ∩ O).Nonempty) :
    ∃ y ∈ P.val ∩ O, ∀ Q ∈ F, y ∉ Q.val := by
  classical
  induction F using Finset.induction_on generalizing O with
  | empty => obtain ⟨y, hy⟩ := hne; exact ⟨y, hy, fun Q hQ => absurd hQ (Finset.notMem_empty Q)⟩
  | @insert Q F hQF ih =>
      have hPQ : P ≠ Q := fun h => hPF (h ▸ Finset.mem_insert_self P F)
      have hPF' : P ∉ F := fun h => hPF (Finset.mem_insert_of_mem h)
      obtain ⟨y, ⟨hyP, hyO⟩, hyQ⟩ := exists_mem_inter_notMem hPQ hO hne
      have hO' : IsOpen (O ∩ Q.valᶜ) := hO.inter Q.isClosed.isOpen_compl
      obtain ⟨z, ⟨hzP, hzO, hzQ⟩, hzF⟩ := ih hPF' hO' ⟨y, hyP, hyO, hyQ⟩
      refine ⟨z, ⟨hzP, hzO⟩, fun Q' hQ' => ?_⟩
      rcases Finset.mem_insert.mp hQ' with rfl | hQ'
      · exact hzQ
      · exact hzF Q' hQ'

/-- Closure form: every point of `P` is a limit of points of `P` outside finitely many prime
divisors different from `P`. -/
theorem subset_closure_diff_biUnion {P : SGPT.PSH.GeometricPrimeCarrier (m + 1) M}
    (F : Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) M)) (hPF : P ∉ F) :
    P.val ⊆ closure (P.val \ ⋃ Q ∈ F, Q.val) := by
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  obtain ⟨y, ⟨hyP, hyO⟩, hyF⟩ := exists_mem_inter_notMem_biUnion F hPF hO ⟨x, hx, hxO⟩
  refine ⟨y, hyO, hyP, ?_⟩
  simp only [mem_iUnion, not_exists]
  exact fun Q hQ => hyF Q hQ

end SGPT.Siu
