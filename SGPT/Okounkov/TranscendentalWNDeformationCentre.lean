import SGPT.Okounkov.TranscendentalWNDeformationStatement
import SGPT.Foundations.Analysis.Pending.RegularPointDimension
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

/-!
# The centre `Z × {0}` of the deformation to the normal cone

Blueprint `tok-wn:deformation` (chapter `claude-tok-wn`) and `tok-wn-def:centre`
(`claude-tok-wn-def`); WN21 §1.1.

For a subset `A` of a complex manifold `X` (dimension `n`) regular of dimension `k` at `x`, and a
point `y` of a complex manifold `Y` (dimension `n'`), the product `A × {y} ⊆ X × Y` is regular of
dimension `k` at `(x, y)`: in the product chart, `(Φ(a), b - e'(y))` flattens it onto
`ℂᵏ × 0`, the free coordinates being the first `k` coordinates of the `X`-block
(`regularAtDim_prod_singleton`).  Hence:

* `isClosedSubmanifold_deformationCentre`: `Z × {0}` is a closed submanifold of `X × ℙ¹`, of
  dimension `m` (codimension two), `regularAtDim_deformationCentre`;
* `interior_deformationCentre`: it has empty interior (a regular set of dimension `< n` has empty
  interior);
* `regularAtDim_centralBase`, `isClosed_centralBase`: `X × {0}` is a closed submanifold of
  dimension `m + 1`, containing the centre (`deformationCentre_subset_centralBase`).

These are the hypotheses of TN's blow-up existence theorem and of the strict-transform theorem.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

/-! ### Coordinate planes in product coordinates -/

/-- `L(a, b) ∈ ℂᵏ × 0 ⊆ ℂⁿ⁺ⁿ'` iff `a ∈ ℂᵏ × 0 ⊆ ℂⁿ` and `b = 0`, for `k ≤ n`. -/
theorem prodModelEquiv_mem_complexCoordinatePlane_iff_of_le {n n' k : ℕ} (hk : k ≤ n)
    (a : ComplexModel n) (b : ComplexModel n') :
    prodModelEquiv n n' (a, b) ∈ complexCoordinatePlane (n + n') k ↔
      a ∈ complexCoordinatePlane n k ∧ b = 0 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h (Fin.castAdd n' i) (by simpa using hi)
      simpa [prodModelEquiv] using this
    · ext j
      have := h (Fin.natAdd n j) (by simp; omega)
      simpa [prodModelEquiv] using this
  · rintro ⟨ha, rfl⟩ i hi
    refine Fin.addCases (fun i hi => ?_) (fun j _ => ?_) i hi
    · have := ha i (by simpa using hi)
      simpa [prodModelEquiv] using this
    · simp [prodModelEquiv]

/-! ### Products with a point -/

section Product

variable {n n' : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

omit [IsComplexManifold n X] [IsComplexManifold n' Y] in
/-- **The product flattening**: a flattening `Φ` of `A` at `x` gives the flattening
`L(a, b) ↦ L(Φ a, b - e'(y))` of `A × {y}` at `(x, y)` in the product chart. -/
theorem exists_prod_singleton_flattening {A : Set X} {x : X} {k : ℕ} (hkn : k ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hΦsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (hΦ0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n k))
    (y : Y) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n + n')
        ((complexChartAt (n := n + n') ((x, y) : X × Y)).val (x, y)),
      Ψ.source ⊆ (complexChartAt (n := n + n') ((x, y) : X × Y)).val.target ∧
      Ψ.toFun ((complexChartAt (n := n + n') ((x, y) : X × Y)).val (x, y)) = 0 ∧
      (∀ {q : X × Y}, q ∈ (complexChartAt (n := n + n') ((x, y) : X × Y)).val.source →
        (complexChartAt (n := n + n') ((x, y) : X × Y)).val q ∈ Ψ.source →
          (q ∈ A ×ˢ ({y} : Set Y) ↔
            Ψ.toFun ((complexChartAt (n := n + n') ((x, y) : X × Y)).val q) ∈
              complexCoordinatePlane (n + n') k)) ∧
      (∀ w, Ψ.toFun w = prodModelEquiv n n'
        (Φ.toFun ((prodModelEquiv n n').symm w).1,
          ((prodModelEquiv n n').symm w).2 - (complexChartAt (n := n') y).val y)) ∧
      (∀ w, w ∈ Ψ.source ↔ ((prodModelEquiv n n').symm w).1 ∈ Φ.source ∧
          ((prodModelEquiv n n').symm w).2 ∈ (complexChartAt (n := n') y).val.target) := by
  have hchart : (complexChartAt (n := n + n') ((x, y) : X × Y)).val =
      prodChart (complexChartAt (n := n) x).val (complexChartAt (n := n') y).val := rfl
  -- the flattening `L(a, b) ↦ L(Φ a, b - e'(y))`
  let c : ComplexModel n' := (complexChartAt (n := n') y).val y
  let src : Set (ComplexModel (n + n')) :=
    {w | ((prodModelEquiv n n').symm w).1 ∈ Φ.source ∧
      ((prodModelEquiv n n').symm w).2 ∈ (complexChartAt (n := n') y).val.target}
  let tgt : Set (ComplexModel (n + n')) :=
    {w | ((prodModelEquiv n n').symm w).1 ∈ Φ.target ∧
      ((prodModelEquiv n n').symm w).2 + c ∈ (complexChartAt (n := n') y).val.target}
  let f : ComplexModel (n + n') → ComplexModel (n + n') :=
    fun w => prodModelEquiv n n'
      (Φ.toFun ((prodModelEquiv n n').symm w).1, ((prodModelEquiv n n').symm w).2 - c)
  let g : ComplexModel (n + n') → ComplexModel (n + n') :=
    fun w => prodModelEquiv n n'
      (Φ.invFun ((prodModelEquiv n n').symm w).1, ((prodModelEquiv n n').symm w).2 + c)
  have hLs : Continuous (fun w : ComplexModel (n + n') => (prodModelEquiv n n').symm w) :=
    (prodModelEquiv n n').symm.continuous
  have hsrc : IsOpen src :=
    (Φ.isOpen_source.preimage (continuous_fst.comp hLs)).inter
      ((complexChartAt (n := n') y).val.open_target.preimage (continuous_snd.comp hLs))
  have htgt : IsOpen tgt :=
    (Φ.isOpen_target.preimage (continuous_fst.comp hLs)).inter
      ((complexChartAt (n := n') y).val.open_target.preimage
        ((continuous_snd.comp hLs).add continuous_const))
  have hLsd : Differentiable ℂ (fun w : ComplexModel (n + n') => (prodModelEquiv n n').symm w) :=
    (prodModelEquiv n n').symm.differentiable
  have hfd : DifferentiableOn ℂ f src := by
    have h1 : DifferentiableOn ℂ
        (fun w : ComplexModel (n + n') => Φ.toFun ((prodModelEquiv n n').symm w).1) src :=
      Φ.toFun_holomorphic.comp (differentiable_fst.comp hLsd).differentiableOn
        (fun w hw => hw.1)
    have h2 : DifferentiableOn ℂ
        (fun w : ComplexModel (n + n') => ((prodModelEquiv n n').symm w).2 - c) src :=
      ((differentiable_snd.comp hLsd).sub_const c).differentiableOn
    exact (prodModelEquiv n n').differentiable.comp_differentiableOn (h1.prodMk h2)
  have hgd : DifferentiableOn ℂ g tgt := by
    have h1 : DifferentiableOn ℂ
        (fun w : ComplexModel (n + n') => Φ.invFun ((prodModelEquiv n n').symm w).1) tgt :=
      Φ.invFun_holomorphic.comp (differentiable_fst.comp hLsd).differentiableOn
        (fun w hw => hw.1)
    have h2 : DifferentiableOn ℂ
        (fun w : ComplexModel (n + n') => ((prodModelEquiv n n').symm w).2 + c) tgt :=
      ((differentiable_snd.comp hLsd).add_const c).differentiableOn
    exact (prodModelEquiv n n').differentiable.comp_differentiableOn (h1.prodMk h2)
  have hcenter : (complexChartAt (n := n + n') ((x, y) : X × Y)).val (x, y) =
      prodModelEquiv n n' ((complexChartAt (n := n) x).val x, c) := rfl
  let Ψ : LocalHolomorphicEquivAt (n := n + n')
      ((complexChartAt (n := n + n') ((x, y) : X × Y)).val (x, y)) :=
    { source := src
      target := tgt
      isOpen_source := hsrc
      isOpen_target := htgt
      center_mem_source := by
        rw [hcenter]
        refine ⟨?_, ?_⟩
        · simpa using Φ.center_mem_source
        · simpa [c] using (complexChartAt (n := n') y).val.map_source
            (mem_complexChartAt_source (n := n') y)
      toFun := f
      invFun := g
      toFun_holomorphic := hfd
      invFun_holomorphic := hgd
      mapsTo_toFun := fun w hw => by
        refine ⟨?_, ?_⟩
        · simpa [f] using Φ.mapsTo_toFun hw.1
        · simpa [f] using hw.2
      mapsTo_invFun := fun w hw => by
        refine ⟨?_, ?_⟩
        · simpa [g] using Φ.mapsTo_invFun hw.1
        · simpa [g] using hw.2
      left_inv := fun w hw => by
        simp only [f, g, ContinuousLinearEquiv.symm_apply_apply, sub_add_cancel]
        rw [Φ.left_inv _ hw.1]
        simp
      right_inv := fun w hw => by
        simp only [f, g, ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel_right]
        rw [Φ.right_inv _ hw.1]
        simp }
  refine ⟨Ψ, ?_, ?_, ?_, fun w => rfl, fun w => Iff.rfl⟩
  · intro w hw
    rw [hchart, prodChart_target]
    exact ⟨hΦsrc hw.1, hw.2⟩
  · show f (prodModelEquiv n n' ((complexChartAt (n := n) x).val x, c)) = 0
    simp only [f, ContinuousLinearEquiv.symm_apply_apply, sub_self]
    rw [hΦ0]
    simp
  · intro q hq hqΨ
    rw [hchart, prodChart_source] at hq
    have hq1 : (complexChartAt (n := n) x).val q.1 ∈ Φ.source := by
      have h := hqΨ.1
      rw [hchart] at h
      simpa using h
    show q ∈ A ×ˢ ({y} : Set Y) ↔
      f (prodChart (complexChartAt (n := n) x).val (complexChartAt (n := n') y).val q) ∈
        complexCoordinatePlane (n + n') k
    simp only [f, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [prodModelEquiv_mem_complexCoordinatePlane_iff_of_le hkn, mem_prod, mem_singleton_iff,
      sub_eq_zero, hflat hq.1 hq1]
    refine and_congr Iff.rfl ⟨fun h => by rw [h], fun h => ?_⟩
    exact (complexChartAt (n := n') y).val.injOn hq.2 (mem_complexChartAt_source (n := n') y) h

omit [IsComplexManifold n X] [IsComplexManifold n' Y] in
/-- **A product with a point is regular**: if `A` is regular of dimension `k` at `x`, then
`A × {y}` is regular of dimension `k` at `(x, y)`, flattened in the product chart by
`L(a, b) ↦ L(Φ a, b - e'(y))`. -/
theorem regularAtDim_prod_singleton {A : Set X} {x : X} {k : ℕ}
    (hA : RegularAtDim (n := n) A x k) (y : Y) :
    RegularAtDim (n := n + n') (A ×ˢ ({y} : Set Y)) (x, y) k := by
  obtain ⟨hkn, hxA, Φ, hΦsrc, hΦ0, hflat⟩ := hA
  obtain ⟨Ψ, hΨsrc, hΨ0, hΨflat, -, -⟩ :=
    exists_prod_singleton_flattening (n' := n') (A := A) (y := y) hkn Φ hΦsrc hΦ0 hflat
  exact ⟨hkn.trans (Nat.le_add_right n n'), ⟨hxA, rfl⟩, Ψ, hΨsrc, hΨ0, hΨflat⟩

omit [IsComplexManifold n X] in
/-- A set that is regular of dimension `k < n` at each of its points has empty interior. -/
theorem interior_eq_empty_of_regularAtDim {N : Set X} {d : ℕ} (hd : d < n)
    (hS : ∀ x ∈ N, RegularAtDim (n := n) N x d) : interior N = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he : (univ : Set X) ∩ interior N = N ∩ interior N := by
    ext z
    simp only [mem_inter_iff, mem_univ, true_and]
    exact ⟨fun hz => ⟨interior_subset hz, hz⟩, fun hz => hz.2⟩
  have hNn : RegularAtDim (n := n) N x n :=
    RegularPointDimension.regularAtDim_of_inter_eq isOpen_interior hx he
      (AnalyticIrreducibleComponents.regularAtDim_univ (n := n) x)
  have hdim := RegularPointDimension.eq_of_regularAtDim hNn (hS x (interior_subset hx))
  omega

end Product

/-! ### The centre and the central base fibre -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

theorem mem_deformationCentre_iff {q : F.carrier × ProjectiveLine} :
    q ∈ deformationCentre F ↔ q.1 ∈ F.flag (1 : Fin (m + 2)) ∧ q.2 = projectiveZero := by
  simp [deformationCentre]

theorem mem_centralBase_iff {q : F.carrier × ProjectiveLine} :
    q ∈ centralBase F ↔ q.2 = projectiveZero := by
  simp [centralBase]

theorem deformationCentre_subset_centralBase : deformationCentre F ⊆ centralBase F :=
  fun _ hq => (mem_centralBase_iff F).mpr ((mem_deformationCentre_iff F).mp hq).2

theorem isClosed_deformationCentre : IsClosed (deformationCentre F) :=
  F.firstDivisor.1.prod isClosed_singleton

theorem isClosed_centralBase : IsClosed (centralBase F) :=
  isClosed_univ.prod isClosed_singleton

/-- `Z × {0}` is regular of dimension `m` at each of its points. -/
theorem regularAtDim_deformationCentre {q : F.carrier × ProjectiveLine}
    (hq : q ∈ deformationCentre F) :
    RegularAtDim (n := m + 1 + 1) (deformationCentre F) q m := by
  obtain ⟨x, p⟩ := q
  obtain ⟨hx, hp⟩ := (mem_deformationCentre_iff F).mp hq
  simp only at hx hp
  subst hp
  exact regularAtDim_prod_singleton (F.firstDivisor.2.2 x hx) projectiveZero

/-- `X × {0}` is regular of dimension `m + 1` at each of its points. -/
theorem regularAtDim_centralBase {q : F.carrier × ProjectiveLine} (hq : q ∈ centralBase F) :
    RegularAtDim (n := m + 1 + 1) (centralBase F) q (m + 1) := by
  obtain ⟨x, p⟩ := q
  have hp : p = projectiveZero := (mem_centralBase_iff F).mp hq
  subst hp
  exact regularAtDim_prod_singleton
    (AnalyticIrreducibleComponents.regularAtDim_univ (n := m + 1) x) projectiveZero

/-- **`Z × {0}` is a closed submanifold of `X × ℙ¹`** (of dimension `m`, codimension two). -/
theorem isClosedSubmanifold_deformationCentre :
    IsClosedSubmanifold (m + 1 + 1) (deformationCentre F) :=
  ⟨isClosed_deformationCentre F, fun _ hq => ⟨m, regularAtDim_deformationCentre F hq⟩⟩

/-- `X × {0}` is a closed submanifold of `X × ℙ¹` (of dimension `m + 1`). -/
theorem isClosedSubmanifold_centralBase : IsClosedSubmanifold (m + 1 + 1) (centralBase F) :=
  ⟨isClosed_centralBase F, fun _ hq => ⟨m + 1, regularAtDim_centralBase F hq⟩⟩

/-- **`Z × {0}` has empty interior** in `X × ℙ¹`. -/
theorem interior_deformationCentre : interior (deformationCentre F) = ∅ :=
  interior_eq_empty_of_regularAtDim (by omega) fun _ hq => regularAtDim_deformationCentre F hq

/-- `X × {0}` has empty interior in `X × ℙ¹`. -/
theorem interior_centralBase : interior (centralBase F) = ∅ :=
  interior_eq_empty_of_regularAtDim (by omega) fun _ hq => regularAtDim_centralBase F hq

/-- `Z` has empty interior in `X`. -/
theorem interior_firstFlag : interior (F.flag (1 : Fin (m + 2))) = ∅ :=
  interior_eq_empty_of_regularAtDim (by omega) fun x hx => F.firstDivisor.2.2 x hx

end SGPT.Okounkov.TranscendentalWN
