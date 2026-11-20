import SGPT.Foundations.Analysis.Pending.NormalDirectionVanishing
import SGPT.Foundations.Analysis.Pending.SkodaElMirSubmanifold
import SGPT.Foundations.Analysis.Pending.DiagonalFibreIntegration
import SGPT.Foundations.Analysis.Pending.SmoothCurrentClosedness

set_option autoImplicit false

/-!
# The tangential reduction on the diagonal

Let `X` be a compact complex manifold and `Θ` a closed positive current of bidimension `(n, n)` on
`X × X` carried by the diagonal `Δ`.  With `Φ = diag ∘ p₁ : (x, y) ↦ (x, x)`,

`Θ (Φ^* φ) = Θ (φ)` for every test form `φ` (`apply_pullback_diagProjMap_eq`),

i.e. `Θ = diag_* p₁_* Θ`: only the restriction of `φ` to the tangent spaces of `Δ` along `Δ` is
seen by `Θ` (step (S3) of the support theorem `bou:diagonal-support`, TN.4 step B4.4;
`demailly-cadg:III.2.10`).

*Proof.*  Test forms are spanned by the elementary forms `h b₁ ∧ ⋯ ∧ b_q`
(`testSpace_le_span_elemSet`), and `Φ^*(h b₁ ∧ ⋯) = (h ∘ Φ) Φ^*b₁ ∧ ⋯`.  Localise `h` by a partition
of unity subordinate to product charts at diagonal points and to `X × X \ Δ` (where `Θ` sees nothing,
`CarriedCurrentTests`).  In the product chart at `(x₀, x₀)` the map `Φ` is the linear projection
`π (u, u') = (u, u)`, and for a real two-form `A` and `ν = 1 - π`,

`A(ξ, η) - A(πξ, πη) = A(νξ, (π + ν/2)η) - A(νη, (π + ν/2)ξ)` (`twoForm_sub_comp`),

where `νξ = ∑ Re Lₐ(ξ) Nₐ` with `Lₐ` the `ℂ`-linear coordinates of `u' - u`.  Hence
`b - Φ^*b = ∑ γ Π₁₁ d(Re Lₐ ∧ ds_c) + ∑ η Π₁₁ (ds_c ∧ ds_d)` with coefficients `η` vanishing on `Δ`.
The first terms are killed for EVERY other factor by
`NormalDirectionVanishing.apply_wedge_normalPair_eq_zero` (`Re Lₐ + i Im Lₐ` is holomorphic), the
second by `CarriedCurrentTests.apply_smulTest_eq_zero`; replacing the factors `bᵢ` by `Φ^*bᵢ` one at a
time (two-forms commute) and `h` by `h ∘ Φ` (equal on `Δ`) proves the claim.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.DiagonalTangentialReduction

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents ClosedProductCurrents CurrentTraceMeasure
  CurrentRestriction SlotTestForms CarriedCurrentTests TopDegreeDensity NormalDirectionVanishing

/-! ### Elementary test forms -/

section Elem

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The elementary form `h · b₀ ∧ ⋯ ∧ b_{q-1}`. -/
def elemForm (h : M → ℝ) (hh : ChartSmooth (n := N) h) :
    (q : ℕ) → (Fin q → SmoothRealForm N M 2) → SmoothRealForm N M (2 * q)
  | 0, _ => smulFun h hh unitForm
  | q + 1, b => wedgeTwo (elemForm h hh q fun i => b i.castSucc) (b (Fin.last q))

theorem elemForm_succ (h : M → ℝ) (hh : ChartSmooth (n := N) h) (q : ℕ)
    (b : Fin (q + 1) → SmoothRealForm N M 2) :
    elemForm h hh (q + 1) b = wedgeTwo (elemForm h hh q fun i => b i.castSucc) (b (Fin.last q)) :=
  rfl

theorem elemForm_snoc (h : M → ℝ) (hh : ChartSmooth (n := N) h) (q : ℕ)
    (b : Fin q → SmoothRealForm N M 2) (β : SmoothRealForm N M 2) :
    elemForm h hh (q + 1) (Fin.snoc b β) = wedgeTwo (elemForm h hh q b) β := by
  rw [elemForm_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- **Coefficients of an elementary form**: `h · wedgeProd b`. -/
theorem elemForm_coeff (h : M → ℝ) (hh : ChartSmooth (n := N) h) :
    ∀ (q : ℕ) (b : Fin q → SmoothRealForm N M 2) (e : ComplexChart N M) (z : ComplexModel N),
      (elemForm h hh q b).coeff e z = h (e.val.symm z) • wedgeProd q fun i => (b i).coeff e z
  | 0, _, _, _ => rfl
  | q + 1, b, e, z => by
    change coordinateWedge ((elemForm h hh q fun i => b i.castSucc).coeff e z)
      ((b (Fin.last q)).coeff e z) = _
    rw [elemForm_coeff h hh q, coordinateWedge_smul_left, wedgeProd_succ]

theorem elemForm_mem (h : M → ℝ) (hh : ChartSmooth (n := N) h) :
    ∀ (q : ℕ) (b : Fin q → SmoothRealForm N M 2), (∀ i, (b i).IsTypeOneOne) →
      elemForm h hh q b ∈ testSpace N M q
  | 0, _, _ => smulFun_unitForm_mem_testSpace h hh
  | q + 1, _, hb => wedgeTwo_mem_testSpace (elemForm_mem h hh q _ fun _ => hb _) (hb _)

/-- An elementary form as a test form. -/
def elemTest (h : M → ℝ) (hh : ChartSmooth (n := N) h) (q : ℕ)
    (b : Fin q → SmoothRealForm N M 2) (hb : ∀ i, (b i).IsTypeOneOne) : testSpace N M q :=
  ⟨elemForm h hh q b, elemForm_mem h hh q b hb⟩

@[simp] theorem coe_elemTest (h : M → ℝ) (hh : ChartSmooth (n := N) h) (q : ℕ)
    (b : Fin q → SmoothRealForm N M 2) (hb : ∀ i, (b i).IsTypeOneOne) :
    ((elemTest h hh q b hb : testSpace N M q) : SmoothRealForm N M (2 * q)) = elemForm h hh q b :=
  rfl

theorem coe_wedgeTestLM {β : SmoothRealForm N M 2} (hβ : β.IsTypeOneOne) (q : ℕ)
    (φ : testSpace N M q) :
    ((wedgeTestLM hβ q φ : testSpace N M (q + 1)) : SmoothRealForm N M (2 * (q + 1))) =
      wedgeTwo (φ : SmoothRealForm N M (2 * q)) β :=
  rfl

variable (N M) in
/-- The elementary forms of degree `2q`. -/
def elemSet (q : ℕ) : Set (SmoothRealForm N M (2 * q)) :=
  {a | ∃ (h : M → ℝ) (hh : ChartSmooth (n := N) h) (b : Fin q → SmoothRealForm N M 2),
    (∀ i, (b i).IsTypeOneOne) ∧ a = elemForm h hh q b}

theorem wedgeTwo_zero_left {k : ℕ} (β : SmoothRealForm N M 2) :
    wedgeTwo (0 : SmoothRealForm N M k) β = 0 := by
  have h := wedgeTwo_smul_left (0 : ℝ) (0 : SmoothRealForm N M k) β
  rwa [zero_smul, zero_smul] at h

/-- **Test forms are spanned by elementary forms.** -/
theorem testSpace_le_span_elemSet :
    ∀ q : ℕ, testSpace N M q ≤ Submodule.span ℝ (elemSet N M q)
  | 0 => by
    refine Submodule.span_le.mpr ?_
    rintro a ⟨h, hh, rfl⟩
    exact Submodule.subset_span ⟨h, hh, Fin.elim0, fun i => i.elim0, rfl⟩
  | q + 1 => by
    refine Submodule.span_le.mpr ?_
    rintro a ⟨P, hP, β, hβ, rfl⟩
    have hspan := testSpace_le_span_elemSet q hP
    clear hP
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, b, hb, rfl⟩ := hx
      refine Submodule.subset_span ⟨h, hh, Fin.snoc b β, fun i => ?_, (elemForm_snoc h hh q b β).symm⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hβ
      · rw [Fin.snoc_castSucc]; exact hb j
    | zero => rw [wedgeTwo_zero_left]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [wedgeTwo_add_left]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [wedgeTwo_smul_left]; exact Submodule.smul_mem _ c hx

theorem span_elemSet_le_testSpace (q : ℕ) : Submodule.span ℝ (elemSet N M q) ≤ testSpace N M q :=
  Submodule.span_le.mpr fun _ ⟨h, hh, b, hb, ha⟩ => ha ▸ elemForm_mem h hh q b hb

/-- **Two functionals agreeing on elementary forms agree.** -/
theorem linearMap_ext_elem {q : ℕ} {L L' : testSpace N M q →ₗ[ℝ] ℝ}
    (h : ∀ (h : M → ℝ) (hh : ChartSmooth (n := N) h) (b : Fin q → SmoothRealForm N M 2)
      (hb : ∀ i, (b i).IsTypeOneOne), L (elemTest h hh q b hb) = L' (elemTest h hh q b hb)) :
    L = L' := by
  ext ⟨φ, hφ⟩
  refine Submodule.span_induction (p := fun x _ => ∀ hx : x ∈ testSpace N M q,
      L ⟨x, hx⟩ = L' ⟨x, hx⟩) ?_ ?_ ?_ ?_ (testSpace_le_span_elemSet q hφ) hφ
  · rintro x ⟨h', hh', b, hb, rfl⟩ _
    exact h h' hh' b hb
  · intro hx
    have : (⟨0, hx⟩ : testSpace N M q) = 0 := rfl
    rw [this, map_zero, map_zero]
  · intro x y hx hy ihx ihy hxy
    have hx' := span_elemSet_le_testSpace q hx
    have hy' := span_elemSet_le_testSpace q hy
    have : (⟨x + y, hxy⟩ : testSpace N M q) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [this, map_add, map_add, ihx hx', ihy hy']
  · intro c x hx ihx hcx
    have hx' := span_elemSet_le_testSpace q hx
    have : (⟨c • x, hcx⟩ : testSpace N M q) = c • ⟨x, hx'⟩ := rfl
    rw [this, map_smul, map_smul, ihx hx']

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] {f : V → M}

/-- **Pullback of an elementary form.** -/
theorem pullback_elemForm (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ f)
    (h : M → ℝ) (hh : ChartSmooth (n := N) h) :
    ∀ (q : ℕ) (b : Fin q → SmoothRealForm N M 2),
      SmoothRealForm.pullback hf (elemForm h hh q b) =
        elemForm (fun x => h (f x)) (chartSmooth_comp hf hh) q
          (fun i => SmoothRealForm.pullback hf (b i))
  | 0, _ => by
    change SmoothRealForm.pullback hf (smulFun h hh unitForm) = _
    rw [pullback_smulFun hf, pullback_unitForm hf]
    rfl
  | q + 1, b => by
    rw [elemForm_succ, pullback_wedgeTwo hf, pullback_elemForm hf h hh q]
    rfl

end Elem

/-! ### Linear algebra of two-forms -/

section Algebra

variable {N : ℕ}

/-- A real two-form as a bilinear map. -/
def twoFormBilin (A : RealForm N 2) : ComplexModel N →ₗ[ℝ] ComplexModel N →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => A ![u, v]) (coordinateFrame_twoForm_add_left A)
    (coordinateFrame_twoForm_smul_left A) (coordinateFrame_twoForm_add_right A)
    (coordinateFrame_twoForm_smul_right A)

@[simp] theorem twoFormBilin_apply (A : RealForm N 2) (u v : ComplexModel N) :
    twoFormBilin A u v = A ![u, v] := rfl

/-- **A two-form in the standard real coordinates**:
`A(ξ, η) = ∑_{c,d} (A(E_c, E_d)/2) (s_c(ξ) s_d(η) - s_c(η) s_d(ξ))`. -/
theorem twoForm_eq_sum (A : RealForm N 2) (ξ η : ComplexModel N) :
    A ![ξ, η] = ∑ c, ∑ d, A ![topBasis N c, topBasis N d] / 2 *
      (coordFun c ξ * coordFun d η - coordFun c η * coordFun d ξ) := by
  have hexp : ∀ u v : ComplexModel N, A ![u, v] =
      ∑ c, ∑ d, coordFun c u * coordFun d v * A ![topBasis N c, topBasis N d] := by
    intro u v
    have h0 : A ![u, v] = twoFormBilin A (∑ c, coordFun c u • topBasis N c)
        (∑ d, coordFun d v • topBasis N d) := by
      rw [sum_coordFun_smul, sum_coordFun_smul, twoFormBilin_apply]
    rw [h0]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      twoFormBilin_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hswap : ∑ c, ∑ d, A ![topBasis N c, topBasis N d] * (coordFun c η * coordFun d ξ) =
      -A ![ξ, η] := by
    rw [← coordinateFrame_twoForm_swap A ξ η, hexp η ξ]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have h1 : ∑ c, ∑ d, A ![topBasis N c, topBasis N d] * (coordFun c ξ * coordFun d η) =
      A ![ξ, η] := by
    rw [hexp ξ η]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hsplit : ∑ c, ∑ d, A ![topBasis N c, topBasis N d] / 2 *
      (coordFun c ξ * coordFun d η - coordFun c η * coordFun d ξ) =
      (∑ c, ∑ d, A ![topBasis N c, topBasis N d] * (coordFun c ξ * coordFun d η) -
        ∑ c, ∑ d, A ![topBasis N c, topBasis N d] * (coordFun c η * coordFun d ξ)) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hsplit, h1, hswap]
  ring

/-- **The normal decomposition**: for `ν = 1 - π` with `νξ = ∑ ℓₐ(ξ) Nₐ`,
`A(ξ, η) - A(πξ, πη) = ∑ₐ (ℓₐ(ξ) A(Nₐ, (π + ν/2)η) - ℓₐ(η) A(Nₐ, (π + ν/2)ξ))`. -/
theorem twoForm_sub_comp (A : RealForm N 2) (π : ComplexModel N →L[ℝ] ComplexModel N)
    {ι : Type*} [Fintype ι] (ℓ : ι → ComplexModel N →L[ℝ] ℝ) (Nv : ι → ComplexModel N)
    (hν : ∀ ξ, ξ - π ξ = ∑ a, ℓ a ξ • Nv a) (ξ η : ComplexModel N) :
    A ![ξ, η] - A ![π ξ, π η] =
      ∑ a, (ℓ a ξ * A ![Nv a, π η + (1 / 2 : ℝ) • (η - π η)] -
        ℓ a η * A ![Nv a, π ξ + (1 / 2 : ℝ) • (ξ - π ξ)]) := by
  set B := twoFormBilin A
  have hsum : ∀ ζ ζ' : ComplexModel N, ∑ a, ℓ a ζ * A ![Nv a, ζ'] = B (ζ - π ζ) ζ' := by
    intro ζ ζ'
    rw [hν ζ]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, B,
      twoFormBilin_apply]
  rw [Finset.sum_sub_distrib, hsum, hsum]
  have hanti : ∀ u v, B u v = -B v u := fun u v => by
    simp only [B, twoFormBilin_apply]
    exact coordinateFrame_twoForm_swap A v u
  have hξ : ξ = π ξ + (ξ - π ξ) := by abel
  have hη : η = π η + (η - π η) := by abel
  set p := π ξ
  set q := ξ - π ξ
  set P := π η
  set Q := η - π η
  change B ξ η - B p P = B q (P + (1 / 2 : ℝ) • Q) - B Q (p + (1 / 2 : ℝ) • q)
  rw [hξ, hη]
  simp only [map_add, LinearMap.add_apply, map_smul, smul_eq_mul]
  rw [hanti Q p, hanti Q q]
  ring

end Algebra

/-! ### The product chart at a diagonal point -/

section ProductModel

open ProductComplexManifold SkodaElMirSubmanifold

variable {n : ℕ}

/-- `π(u, u') = (u, u)` in the product model `ℂⁿ⁺ⁿ`. -/
def diagProj (n : ℕ) : ComplexModel (n + n) →L[ℂ] ComplexModel (n + n) :=
  (prodModelEquiv n n).toContinuousLinearMap.comp
    (((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n)).prod
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n))).comp
      (prodModelEquiv n n).symm.toContinuousLinearMap)

theorem diagProj_apply (u u' : ComplexModel n) :
    diagProj n (prodModelEquiv n n (u, u')) = prodModelEquiv n n (u, u) := by
  simp [diagProj]

theorem diagDifference_apply (u u' : ComplexModel n) :
    diagDifference n (prodModelEquiv n n (u, u')) = u' - u := by
  simp [diagDifference]

/-- The `ℂ`-linear normal coordinates `yⱼ`, `-i yⱼ` of the diagonal, `y = u' - u`. -/
def normalCoord (a : Fin 2 × Fin n) : ComplexModel (n + n) →L[ℂ] ℂ :=
  (![1, -Complex.I] a.1 : ℂ) •
    ((EuclideanSpace.proj a.2 : ComplexModel n →L[ℂ] ℂ).comp (diagDifference n))

/-- Their real parts. -/
def normalRe (a : Fin 2 × Fin n) : ComplexModel (n + n) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((normalCoord a).restrictScalars ℝ)

/-- The dual normal vectors. -/
def normalVec (a : Fin 2 × Fin n) : ComplexModel (n + n) :=
  prodModelEquiv n n (0, (![1, Complex.I] a.1 : ℂ) • EuclideanSpace.single a.2 (1 : ℂ))

theorem normalRe_apply (a : Fin 2 × Fin n) (ξ : ComplexModel (n + n)) :
    normalRe a ξ = (normalCoord a ξ).re := rfl

/-- **`ξ - πξ = ∑ₐ Re Lₐ(ξ) Nₐ`.** -/
theorem sub_diagProj_eq (ξ : ComplexModel (n + n)) :
    ξ - diagProj n ξ = ∑ a, normalRe a ξ • normalVec a := by
  obtain ⟨⟨u, u'⟩, rfl⟩ := (prodModelEquiv n n).surjective ξ
  rw [diagProj_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
  have hterm : ∀ a : Fin 2 × Fin n, normalRe a (prodModelEquiv n n (u, u')) • normalVec a =
      prodModelEquiv n n (0, (((![1, -Complex.I] a.1 * (u' - u) a.2).re : ℝ) : ℂ) •
        ((![1, Complex.I] a.1 : ℂ) • EuclideanSpace.single a.2 (1 : ℂ))) := by
    intro a
    rw [← Complex.coe_smul, normalVec, ← map_smul, Prod.smul_mk, smul_zero, normalRe_apply,
      normalCoord, smul_apply, ContinuousLinearMap.comp_apply,
      diagDifference_apply, smul_eq_mul]
    rfl
  simp_rw [hterm, ← map_sum]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    simp
  · rw [Prod.snd_sum, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
    dsimp only
    have hy : u' - u = ∑ j, ((u' - u) j • EuclideanSpace.single j (1 : ℂ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (u' - u)]
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    conv_lhs => rw [hy]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, one_smul]
    rw [smul_smul, ← add_smul]
    congr 1
    have hre : (-Complex.I * (u' - u) j).re = ((u' - u) j).im := by
      simp [Complex.mul_re]
    rw [hre, Complex.re_add_im]

/-- The constant two-form `ℓ ∧ m` of two real covectors. -/
def pairForm {N : ℕ} (ℓ m : ComplexModel N →L[ℝ] ℝ) : RealForm N 2 :=
  oneWedge ℓ (ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel N) ℝ (0 : Fin 1) m)

theorem pairForm_apply {N : ℕ} (ℓ m : ComplexModel N →L[ℝ] ℝ) (u v : ComplexModel N) :
    pairForm ℓ m ![u, v] = ℓ u * m v - ℓ v * m u :=
  oneWedge_apply_two ℓ m u v

/-- The vectors `πE_c + (E_c - πE_c)/2`. -/
def halfVec (c : Fin (2 * (n + n))) : ComplexModel (n + n) :=
  diagProj n (topBasis (n + n) c) +
    (1 / 2 : ℝ) • (topBasis (n + n) c - diagProj n (topBasis (n + n) c))

theorem halfVec_sum (ζ : ComplexModel (n + n)) :
    diagProj n ζ + (1 / 2 : ℝ) • (ζ - diagProj n ζ) =
      ∑ c, coordFun c ζ • halfVec c := by
  have hlin : ∀ v : ComplexModel (n + n), diagProj n v + (1 / 2 : ℝ) • (v - diagProj n v) =
      ((diagProj n).restrictScalars ℝ + (1 / 2 : ℝ) •
        (ContinuousLinearMap.id ℝ (ComplexModel (n + n)) - (diagProj n).restrictScalars ℝ)) v :=
    fun v => rfl
  rw [hlin]
  conv_lhs => rw [← sum_coordFun_smul ζ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ← hlin]
  rfl

/-- **The decomposition of `A - π^*B` at a point of the product chart**: a sum of `(1,1)`-parts of
`Re Lₐ ∧ s_c` (normal) and of `s_c ∧ s_d` with coefficients `(A - B)(πE_c, πE_d)/2` (which vanish
when `A = B`). -/
theorem sub_compDiagProj_eq (A B : RealForm (n + n) 2) (hA : IsOneOne A) (hB : IsOneOne B) :
    A - B.compContinuousLinearMap ((diagProj n).restrictScalars ℝ) =
      (∑ a, ∑ c, A ![normalVec a, halfVec c] • pi11 (pairForm (normalRe a) (coordFun c))) +
        ∑ c, ∑ d, ((A - B) ![diagProj n (topBasis (n + n) c), diagProj n (topBasis (n + n) d)] /
          2) • pi11 (pairForm (coordFun c) (coordFun d)) := by
  set π' : ComplexModel (n + n) →L[ℝ] ComplexModel (n + n) := (diagProj n).restrictScalars ℝ
    with hπ'
  have hπ : ∀ v, π' (Complex.I • v) = Complex.I • π' v := fun v => (diagProj n).map_smul _ v
  have hlhs : IsOneOne (A - B.compContinuousLinearMap π') := by
    have hBπ := isOneOne_compContinuousLinearMap hB π' hπ
    intro u v
    simp only [ContinuousAlternatingMap.sub_apply]
    rw [hA u v, hBπ u v]
  have key : A - B.compContinuousLinearMap π' =
      (∑ a, ∑ c, A ![normalVec a, halfVec c] • pairForm (normalRe a) (coordFun c)) +
        ∑ c, ∑ d, ((A - B) ![diagProj n (topBasis (n + n) c), diagProj n (topBasis (n + n) d)] /
          2) • pairForm (coordFun c) (coordFun d) := by
    ext v
    rw [eq_vec_two v]
    set ξ := v 0
    set η := v 1
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      pairForm_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two]
    have h1 := twoForm_sub_comp A π' normalRe normalVec sub_diagProj_eq ξ η
    have h2 := twoForm_eq_sum ((A - B).compContinuousLinearMap π') ξ η
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two,
      ContinuousAlternatingMap.sub_apply] at h2
    have hexp : ∀ (a : Fin 2 × Fin n) (ζ : ComplexModel (n + n)),
        A ![normalVec a, π' ζ + (1 / 2 : ℝ) • (ζ - π' ζ)] =
          ∑ c, coordFun c ζ * A ![normalVec a, halfVec c] := by
      intro a ζ
      rw [show π' ζ = diagProj n ζ from rfl, halfVec_sum, ← twoFormBilin_apply, map_sum]
      simp only [map_smul, smul_eq_mul, twoFormBilin_apply]
    simp only [hexp] at h1
    have hfirst : A ![ξ, η] - A ![π' ξ, π' η] =
        ∑ a, ∑ c, A ![normalVec a, halfVec c] *
          (normalRe a ξ * coordFun c η - normalRe a η * coordFun c ξ) := by
      rw [h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have hsecond : A ![π' ξ, π' η] - B ![π' ξ, π' η] =
        ∑ c, ∑ d, (A ![π' (topBasis (n + n) c), π' (topBasis (n + n) d)] -
          B ![π' (topBasis (n + n) c), π' (topBasis (n + n) d)]) / 2 *
            (coordFun c ξ * coordFun d η - coordFun c η * coordFun d ξ) := h2
    rw [show A ![ξ, η] - B ![π' ξ, π' η] =
      (A ![ξ, η] - A ![π' ξ, π' η]) + (A ![π' ξ, π' η] - B ![π' ξ, π' η]) by ring,
      hfirst, hsecond]
    rfl
  rw [← pi11_eq_self hlhs, key, pi11_add, pi11_sum, pi11_sum]
  simp only [pi11_sum, pi11_smul]

end ProductModel

/-! ### The product chart on `X × X` -/

section Chart

open ProductComplexManifold SkodaElMirSubmanifold HolomorphicMaps ChartPartition
open scoped ProductComplexManifold

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (X) in
/-- `Φ(x, y) = (x, x)`, i.e. `diag ∘ p₁`. -/
def diagProjMap : X × X → X × X := fun p => (p.1, p.1)

theorem contMDiff_diagProjMap :
    ContMDiff 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞ (diagProjMap X) :=
  contMDiff_prodMk contMDiff_fst contMDiff_fst

variable (n) in
/-- The product chart at `(x₀, x₀)`. -/
abbrev diagChart (x₀ : X) : ComplexChart (n + n) (X × X) := complexChartAt (n := n + n) (x₀, x₀)

omit [IsComplexManifold n X] in
theorem diagChart_val (x₀ : X) :
    (diagChart n x₀).val = prodChart (chartAt (ComplexModel n) x₀) (chartAt (ComplexModel n) x₀) :=
  rfl

omit [IsComplexManifold n X] in
theorem diagChart_mapsTo {x₀ : X} {p : X × X} (hp : p ∈ (diagChart n x₀).val.source) :
    diagProjMap X p ∈ (diagChart n x₀).val.source ∧
      (diagChart n x₀).val (diagProjMap X p) = diagProj n ((diagChart n x₀).val p) := by
  rw [diagChart_val, prodChart_source] at hp ⊢
  refine ⟨⟨hp.1, hp.1⟩, ?_⟩
  simp only [prodChart_apply, diagProjMap, diagProj_apply]

omit [IsComplexManifold n X] in
theorem diagProj_mem_target {x₀ : X} {w : ComplexModel (n + n)}
    (hw : w ∈ (diagChart n x₀).val.target) : diagProj n w ∈ (diagChart n x₀).val.target := by
  have hs := (diagChart n x₀).val.map_target hw
  rw [← (diagChart n x₀).val.right_inv hw, ← (diagChart_mapsTo hs).2]
  exact (diagChart n x₀).val.map_source (diagChart_mapsTo hs).1

omit [IsComplexManifold n X] in
theorem coordinateMap_diagProjMap {x₀ : X} {w : ComplexModel (n + n)}
    (hw : w ∈ (diagChart n x₀).val.target) :
    coordinateMap (diagProjMap X) (diagChart n x₀) (diagChart n x₀) w = diagProj n w := by
  have hs := (diagChart n x₀).val.map_target hw
  change (diagChart n x₀).val (diagProjMap X ((diagChart n x₀).val.symm w)) = _
  rw [(diagChart_mapsTo hs).2, (diagChart n x₀).val.right_inv hw]

/-- **`Φ^*b` in the product chart**: `(Φ^*b)(w) = π^*(b(πw))`. -/
theorem pullback_diagProjMap_coeff (b : SmoothRealForm (n + n) (X × X) 2) {x₀ : X}
    {w : ComplexModel (n + n)} (hw : w ∈ (diagChart n x₀).val.target) :
    (SmoothRealForm.pullback contMDiff_diagProjMap b).coeff (diagChart n x₀) w =
      (b.coeff (diagChart n x₀) (diagProj n w)).compContinuousLinearMap
        ((diagProj n).restrictScalars ℝ) := by
  have hdom : w ∈ coordinateDomain (diagProjMap X) (diagChart n x₀) (diagChart n x₀) :=
    ⟨hw, (diagChart_mapsTo ((diagChart n x₀).val.map_target hw)).1⟩
  rw [SmoothRealForm.pullback_coeff _ b _ _ hdom, coordinateMap_diagProjMap hw]
  have heq : coordinateMap (diagProjMap X) (diagChart n x₀) (diagChart n x₀) =ᶠ[𝓝 w]
      (diagProj n).restrictScalars ℝ := by
    filter_upwards [(diagChart n x₀).val.open_target.mem_nhds hw] with y hy
    exact coordinateMap_diagProjMap hy
  rw [heq.fderiv_eq, ContinuousLinearMap.fderiv]

omit [IsComplexManifold n X] in
/-- On the diagonal, `π` fixes the chart point and the normal coordinates vanish. -/
theorem diagonal_chart {x₀ : X} {p : X × X} (hΔ : p ∈ Set.diagonal X) :
    diagProj n ((diagChart n x₀).val p) = (diagChart n x₀).val p ∧
      ∀ a, normalCoord a ((diagChart n x₀).val p) = 0 := by
  obtain ⟨x, y⟩ := p
  obtain rfl : x = y := hΔ
  simp only [diagChart_val, prodChart_apply, diagProj_apply, true_and]
  intro a
  simp [normalCoord, diagDifference_apply]

/-- The imaginary parts of the normal coordinates. -/
def normalIm (a : Fin 2 × Fin n) : ComplexModel (n + n) →L[ℝ] ℝ :=
  Complex.imCLM.comp ((normalCoord a).restrictScalars ℝ)

/-- **`Re Lₐ + i Im Lₐ` is holomorphic**: if a cut-off `χ` equals `1` on an open set `O` and
`ρ = 0` off `O`, the chart extensions of `χ Re Lₐ`, `χ Im Lₐ` form a holomorphic pair where
`ρ ≠ 0`. -/
theorem isHoloPairOn_normal (x₀ : X) {χ ρ : ComplexModel (n + n) → ℝ} {O : Set (ComplexModel (n + n))}
    (hO : IsOpen O) (hχO : ∀ z ∈ O, χ z = 1) (hρO : Function.support ρ ⊆ O)
    (a : Fin 2 × Fin n) :
    IsHoloPairOn (N := n + n) (chartExtend (diagChart n x₀) fun z => χ z * normalRe a z)
      (chartExtend (diagChart n x₀) fun z => χ z * normalIm a z) (chartExtend (diagChart n x₀) ρ) := by
  intro f z hz hρz v
  set E := diagChart n x₀
  have hxs : f.val.symm z ∈ E.val.source := by
    by_contra h
    exact hρz (chartExtend_of_notMem h)
  have hEx : E.val (f.val.symm z) ∈ O := by
    rw [chartExtend_of_mem hxs] at hρz
    exact hρO hρz
  have hzd : z ∈ coordinateDomain id f E := ⟨hz, hxs⟩
  set Ψ := coordinateMap id f E with hΨ
  have hΨc : ContDiffAt ℝ ∞ Ψ z := coordinateMap_contDiffAt_real contMDiff_id f E hzd
  have hev : ∀ᶠ y in 𝓝 z, y ∈ coordinateDomain id f E ∧ Ψ y ∈ O := by
    have h1 : ∀ᶠ y in 𝓝 z, y ∈ coordinateDomain id f E :=
      (coordinateDomain_isOpen contMDiff_id f E).mem_nhds hzd
    exact h1.and (hΨc.continuousAt.preimage_mem_nhds (hO.mem_nhds hEx))
  have hg : (fun y => chartExtend E (fun z => χ z * normalRe a z) (f.val.symm y)) =ᶠ[𝓝 z]
      fun y => normalRe a (Ψ y) := by
    filter_upwards [hev] with y hy
    rw [chartExtend_of_mem hy.1.2]
    change χ (Ψ y) * normalRe a (Ψ y) = _
    rw [hχO _ hy.2, one_mul]
  have hF : (fun y => chartExtend E (fun z => χ z * normalIm a z) (f.val.symm y)) =ᶠ[𝓝 z]
      fun y => normalIm a (Ψ y) := by
    filter_upwards [hev] with y hy
    rw [chartExtend_of_mem hy.1.2]
    change χ (Ψ y) * normalIm a (Ψ y) = _
    rw [hχO _ hy.2, one_mul]
  have hΨd : DifferentiableAt ℝ Ψ z := hΨc.differentiableAt (by simp)
  have hRe : fderiv ℝ (fun y => normalRe a (Ψ y)) z = (normalRe a).comp (fderiv ℝ Ψ z) :=
    ((normalRe a).hasFDerivAt.comp z hΨd.hasFDerivAt).fderiv
  have hIm : fderiv ℝ (fun y => normalIm a (Ψ y)) z = (normalIm a).comp (fderiv ℝ Ψ z) :=
    ((normalIm a).hasFDerivAt.comp z hΨd.hasFDerivAt).fderiv
  rw [hg.fderiv_eq, hF.fderiv_eq, hRe, hIm]
  simp only [ContinuousLinearMap.comp_apply]
  rw [coordinateMap_fderiv_map_smul_complex contMDiff_id f E hzd Complex.I v]
  simp only [normalIm, normalRe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, Complex.imCLM_apply,
    Complex.reCLM_apply, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add]
  rfl

end Chart

/-! ### Cut-off linear functions in a chart -/

section CutOff

open ChartPartition

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- A smooth function on a chart target, cut off inside the target, extends to a chart-smooth
function. -/
theorem chartSmooth_chartExtend_mul (E : ComplexChart N M) {ψ : ComplexModel N → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψt : tsupport ψ ⊆ E.val.target)
    {f : ComplexModel N → ℝ} (hf : ContDiffOn ℝ ∞ f E.val.target) :
    ChartSmooth (n := N) (chartExtend E fun z => ψ z * f z) :=
  chartSmooth_chartExtend E
    (SmoothCurrentClosedness.contDiff_mul_of_tsupport_subset E.val.open_target hψ hψt hf)
    (hψc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)
    (tsupport_mul_subset_left.trans hψt)

/-- **`d(χℓ ∧ dχm) = ℓ ∧ m`** where the cut-off `χ` is `1` near the point. -/
theorem exactPair_cutoff_coeff (E : ComplexChart N M) {χ : ComplexModel N → ℝ}
    (ℓ m : ComplexModel N →L[ℝ] ℝ) (hℓ : ChartSmooth (n := N) (chartExtend E fun z => χ z * ℓ z))
    (hm : ChartSmooth (n := N) (chartExtend E fun z => χ z * m z)) {w : ComplexModel N}
    (hw : w ∈ E.val.target) (hχ : (fun z => χ z) =ᶠ[𝓝 w] fun _ => 1) :
    (exactPair _ _ hℓ hm).coeff E w = pairForm ℓ m := by
  have h1 : ∀ L : ComplexModel N →L[ℝ] ℝ,
      (fun y => chartExtend E (fun z => χ z * L z) (E.val.symm y)) =ᶠ[𝓝 w] fun y => L y := by
    intro L
    filter_upwards [SlotTestForms.chartExtend_eventuallyEq hw, hχ] with y hy1 hy2
    rw [hy1, hy2, one_mul]
  ext v
  rw [eq_vec_two v, exactPair_coeff_apply _ _ hℓ hm E hw, (h1 ℓ).fderiv_eq, (h1 m).fderiv_eq,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv, pairForm_apply]

end CutOff

/-! ### The chart-local vanishing -/

section Core

open ProductComplexManifold SkodaElMirSubmanifold HolomorphicMaps ChartPartition
open scoped ProductComplexManifold

theorem isTypeOneOne_sub {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] {a b : SmoothRealForm N M 2}
    (ha : a.IsTypeOneOne) (hb : b.IsTypeOneOne) : (a - b).IsTypeOneOne := fun e z hz u v => by
  simp only [coeff_sub, ContinuousAlternatingMap.sub_apply]
  rw [ha e z hz u v, hb e z hz u v]

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

theorem isTypeOneOne_sub_pullback {b : SmoothRealForm (n + n) (X × X) 2}
    (hb : b.IsTypeOneOne) :
    (b - SmoothRealForm.pullback contMDiff_diagProjMap b).IsTypeOneOne :=
  isTypeOneOne_sub hb (isTypeOneOne_pullback contMDiff_diagProjMap hb)

theorem coordinateWedge_smul_zero_left {N p : ℕ} (P : RealForm N p) (B : RealForm N 2) :
    coordinateWedge ((0 : ℝ) • P) B = 0 := by
  rw [coordinateWedge_smul_left, zero_smul]

variable [CompactSpace X] [MeasurableSpace (X × X)] [BorelSpace (X × X)]
  (w : KahlerBackground (n + n) (X × X)) {q : ℕ} {Θ : ProductCurrent (n + n) (X × X) (q + 1)}
  (hΘ : IsPositive Θ)

include hΘ in
/-- **The chart-local vanishing**: near every diagonal point, a closed positive current carried by
`Δ` does not see `R ∧ (b - Φ^*b)` for elementary `R` supported near the point. -/
theorem exists_nhds_apply_wedge_sub_pullback_eq_zero (hΘc : IsClosedCurrent Θ)
    (hcar : traceMeasure w Θ hΘ (Set.diagonal X)ᶜ = 0) (x₀ : X) :
    ∃ U : Set (X × X), IsOpen U ∧ (x₀, x₀) ∈ U ∧
      ∀ (h : X × X → ℝ) (hh : ChartSmooth (n := n + n) h), tsupport h ⊆ U →
      ∀ (c : Fin q → SmoothRealForm (n + n) (X × X) 2) (hc : ∀ i, (c i).IsTypeOneOne)
        (b : SmoothRealForm (n + n) (X × X) 2) (hb : b.IsTypeOneOne),
        Θ (wedgeTestLM (isTypeOneOne_sub_pullback hb) q (elemTest h hh q c hc)) = 0 := by
  set E := diagChart n x₀ with hE
  have hx₀ : (x₀, x₀) ∈ E.val.source := mem_complexChartAt_source _
  set z₀ := E.val (x₀, x₀) with hz₀
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.mp E.val.open_target z₀ (E.val.map_source hx₀)
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hball : ∀ s, s < ε → closedBall z₀ s ⊆ E.val.target := fun s hs =>
    (closedBall_subset_ball hs).trans hεt
  have hBt : ball z₀ r ⊆ E.val.target :=
    ball_subset_closedBall.trans (hball r (by rw [hr]; linarith))
  refine ⟨E.val.symm '' ball z₀ r, E.val.symm.isOpen_image_of_subset_source isOpen_ball
    (by simpa using hBt), ⟨z₀, mem_ball_self hr0, E.val.left_inv hx₀⟩, ?_⟩
  intro h hh hhU c hc b hb
  have hΔm : MeasurableSet (Set.diagonal X) := isClosed_diagonal.measurableSet
  -- cut-offs
  let χ : ContDiffBump z₀ := ⟨3 * r, 7 / 2 * r, by positivity, by linarith⟩
  let ρb : ContDiffBump z₀ := ⟨2 * r, 5 / 2 * r, by positivity, by linarith⟩
  let ρc : ContDiffBump z₀ := ⟨r, 3 / 2 * r, hr0, by linarith⟩
  have hχt : tsupport χ ⊆ E.val.target := by
    rw [χ.tsupport_eq]; exact hball (7 / 2 * r) (by rw [hr]; linarith)
  have hρt : tsupport ρb ⊆ E.val.target := by
    rw [ρb.tsupport_eq]; exact hball (5 / 2 * r) (by rw [hr]; linarith)
  have hρct : tsupport ρc ⊆ E.val.target := by
    rw [ρc.tsupport_eq]; exact hball (3 / 2 * r) (by rw [hr]; linarith)
  have hcl : ∀ L : ComplexModel (n + n) →L[ℝ] ℝ, ContDiffOn ℝ ∞ (fun z => L z) E.val.target :=
    fun L => L.contDiff.contDiffOn
  -- the global functions
  have hg : ∀ a, ChartSmooth (n := n + n) (chartExtend E fun z => χ z * normalRe a z) := fun a =>
    chartSmooth_chartExtend_mul E χ.contDiff χ.hasCompactSupport hχt (hcl _)
  have hF : ∀ a, ChartSmooth (n := n + n) (chartExtend E fun z => χ z * normalIm a z) := fun a =>
    chartSmooth_chartExtend_mul E χ.contDiff χ.hasCompactSupport hχt (hcl _)
  have hS : ∀ c', ChartSmooth (n := n + n) (chartExtend E fun z => χ z * coordFun c' z) :=
    fun c' => chartSmooth_chartExtend_mul E χ.contDiff χ.hasCompactSupport hχt (hcl _)
  have hρ : ChartSmooth (n := n + n) (chartExtend E fun z => ρb z) :=
    chartSmooth_chartExtend E ρb.contDiff ρb.hasCompactSupport hρt
  -- the coefficient functions
  set γ : Fin 2 × Fin n → Fin (2 * (n + n)) → ComplexModel (n + n) → ℝ :=
    fun a c' z => (b.coeff E z) ![normalVec a, halfVec c'] with hγdef
  set η : Fin (2 * (n + n)) → Fin (2 * (n + n)) → ComplexModel (n + n) → ℝ :=
    fun c' d z => (b.coeff E z - b.coeff E (diagProj n z))
      ![diagProj n (topBasis (n + n) c'), diagProj n (topBasis (n + n) d)] / 2 with hηdef
  have hbE : ContDiffOn ℝ ∞ (b.coeff E) E.val.target := b.smooth E
  have hbπ : ContDiffOn ℝ ∞ (fun z => b.coeff E (diagProj n z)) E.val.target :=
    hbE.comp ((diagProj n).restrictScalars ℝ).contDiff.contDiffOn
      (fun z hz => diagProj_mem_target hz)
  have hγ : ∀ a c', ContDiffOn ℝ ∞ (γ a c') E.val.target := fun a c' =>
    (ContinuousAlternatingMap.apply ℝ (ComplexModel (n + n)) ℝ ![normalVec a, halfVec c']).contDiff.comp_contDiffOn hbE
  have hη : ∀ c' d, ContDiffOn ℝ ∞ (η c' d) E.val.target := fun c' d =>
    (((ContinuousAlternatingMap.apply ℝ (ComplexModel (n + n)) ℝ
      ![diagProj n (topBasis (n + n) c'), diagProj n (topBasis (n + n) d)]).contDiff.comp_contDiffOn
        (hbE.sub hbπ)).div_const 2)
  have hΓ : ∀ a c', ChartSmooth (n := n + n) (chartExtend E fun z => ρc z * γ a c' z) :=
    fun a c' => chartSmooth_chartExtend_mul E ρc.contDiff ρc.hasCompactSupport hρct (hγ a c')
  have hΛ : ∀ c' d, ChartSmooth (n := n + n) (chartExtend E fun z => ρc z * η c' d z) :=
    fun c' d => chartSmooth_chartExtend_mul E ρc.contDiff ρc.hasCompactSupport hρct (hη c' d)
  set R := elemTest h hh q c hc with hRdef
  have hRcoeff : ∀ (f : ComplexChart (n + n) (X × X)) z,
      ((R : testSpace (n + n) (X × X) q) : SmoothRealForm (n + n) (X × X) (2 * q)).coeff f z =
        h (f.val.symm z) • wedgeProd q fun i => (c i).coeff f z :=
    fun f z => elemForm_coeff h hh q c f z
  have hW : ∀ {β : SmoothRealForm (n + n) (X × X) 2} (hβ : β.IsTypeOneOne)
      (f : ComplexChart (n + n) (X × X)) z,
      ((wedgeTestLM hβ q R : testSpace (n + n) (X × X) (q + 1)) :
        SmoothRealForm (n + n) (X × X) (2 * (q + 1))).coeff f z =
        coordinateWedge (((R : testSpace (n + n) (X × X) q) :
          SmoothRealForm (n + n) (X × X) (2 * q)).coeff f z) (β.coeff f z) :=
    fun _ _ _ => rfl
  have hsm : ∀ {H : X × X → ℝ} (hH : ChartSmooth (n := n + n) H)
      (φ : testSpace (n + n) (X × X) (q + 1)) (f : ComplexChart (n + n) (X × X)) z,
      ((smulTest H hH φ : testSpace (n + n) (X × X) (q + 1)) :
        SmoothRealForm (n + n) (X × X) (2 * (q + 1))).coeff f z =
        H (f.val.symm z) • (φ : SmoothRealForm (n + n) (X × X) (2 * (q + 1))).coeff f z :=
    fun _ _ _ _ => rfl
  have hsuppB : ∀ z ∈ E.val.target, h (E.val.symm z) ≠ 0 → z ∈ ball z₀ r := by
    intro z hz h0
    obtain ⟨z', hz', hzz'⟩ := hhU (subset_tsupport _ h0)
    have hzz : z' = z := by
      have h' := congrArg E.val hzz'
      rwa [E.val.right_inv (hBt hz'), E.val.right_inv hz] at h'
    rwa [← hzz]
  have hχ1 : ∀ z ∈ ball z₀ r, (fun y => χ y) =ᶠ[𝓝 z] fun _ => 1 := by
    intro z hz
    have hz3 : z ∈ ball z₀ (3 * r) := ball_subset_ball (by linarith) hz
    filter_upwards [isOpen_ball.mem_nhds hz3] with y hy
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hy)
  have hρc1 : ∀ z ∈ ball z₀ r, ρc z = 1 := fun z hz =>
    ρc.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hzero : ∀ (f : ComplexChart (n + n) (X × X)) z, h (f.val.symm z) = 0 →
      ∀ β : SmoothRealForm (n + n) (X × X) 2,
        coordinateWedge (((R : testSpace (n + n) (X × X) q) :
          SmoothRealForm (n + n) (X × X) (2 * q)).coeff f z) (β.coeff f z) = 0 := by
    intro f z h0 β
    rw [hRcoeff, h0, coordinateWedge_smul_zero_left]
  -- the decomposition
  have hsplit : Θ (wedgeTestLM (isTypeOneOne_sub_pullback hb) q R) =
      (∑ a, ∑ c', Θ (smulTest _ (hΓ a c')
        (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hg a) (hS c'))) q R))) +
      ∑ c', ∑ d, Θ (smulTest _ (hΛ c' d)
        (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hS c') (hS d))) q R)) := by
    simp only [← map_sum, ← map_add]
    refine hΘ.apply_eq_of_coeff_eqOn fun f z hz => ?_
    refine SlotTestForms.coeff_eq_of_chart E (K := tsupport h)
      (hhU.trans (image_symm_subset_source hBt)) ?_ ?_ ?_ f hz
    · intro z hz
      simp only [Submodule.coe_add, Submodule.coe_sum, coeff_add,
        ClosedCurrentLocalTests.coeff_sum, hsm, hW]
      by_cases h0 : h (E.val.symm z) = 0
      · simp only [hzero E z h0, smul_zero, Finset.sum_const_zero, add_zero]
      · have hzB := hsuppB z hz h0
        have hX : ∀ a c', (exactPair _ _ (hg a) (hS c')).coeff E z =
            pairForm (normalRe a) (coordFun c') := fun a c' =>
          exactPair_cutoff_coeff E _ _ (hg a) (hS c') hz (hχ1 z hzB)
        have hY : ∀ c' d, (exactPair _ _ (hS c') (hS d)).coeff E z =
            pairForm (coordFun c') (coordFun d) := fun c' d =>
          exactPair_cutoff_coeff E _ _ (hS c') (hS d) hz (hχ1 z hzB)
        have hΓz : ∀ a c', chartExtend E (fun z => ρc z * γ a c' z) (E.val.symm z) =
            γ a c' z := fun a c' => by
          rw [SlotTestForms.chartExtend_symm hz, hρc1 z hzB, one_mul]
        have hΛz : ∀ c' d, chartExtend E (fun z => ρc z * η c' d z) (E.val.symm z) =
            η c' d z := fun c' d => by
          rw [SlotTestForms.chartExtend_symm hz, hρc1 z hzB, one_mul]
        rw [coeff_sub, pullback_diagProjMap_coeff b hz,
          sub_compDiagProj_eq _ _ (hb E z hz) (hb E _ (diagProj_mem_target hz))]
        simp only [pi11Form_coeff, hX, hY, hΓz, hΛz]
        rw [← wedgeCLM_apply, map_add, map_sum, map_sum]
        simp only [map_sum, map_smul, wedgeCLM_apply, hγdef, hηdef]
    · intro f' z' _ hK
      rw [hW]
      exact hzero f' z' (image_eq_zero_of_notMem_tsupport hK) _
    · intro f' z' _ hK
      simp only [Submodule.coe_add, Submodule.coe_sum, coeff_add,
        ClosedCurrentLocalTests.coeff_sum, hsm, hW,
        hzero f' z' (image_eq_zero_of_notMem_tsupport hK), smul_zero, Finset.sum_const_zero,
        add_zero]
  rw [hsplit]
  -- the normal terms vanish
  have hg0 : ∀ a, ∀ x ∈ Set.diagonal X, chartExtend E (fun z => χ z * normalRe a z) x = 0 := by
    intro a x hx
    by_cases hxs : x ∈ E.val.source
    · rw [chartExtend_of_mem hxs, normalRe_apply, (diagonal_chart hx).2 a, Complex.zero_re,
        mul_zero]
    · exact chartExtend_of_notMem hxs
  have hpair : ∀ a, IsHoloPairOn (N := n + n) (chartExtend E fun z => χ z * normalRe a z)
      (chartExtend E fun z => χ z * normalIm a z) (chartExtend E fun z => ρb z) := fun a =>
    isHoloPairOn_normal x₀ (χ := fun z => χ z) (ρ := fun z => ρb z) (O := ball z₀ (3 * r))
      isOpen_ball (fun z hz => χ.one_of_mem_closedBall (ball_subset_closedBall hz))
      (by
        rw [ρb.support_eq]
        exact ball_subset_ball (show (5 / 2 * r : ℝ) ≤ 3 * r by linarith)) a
  have hρ0 : ∀ x, 0 ≤ chartExtend E (fun z => ρb z) x :=
    chartExtend_nonneg fun _ => ρb.nonneg
  have hΓρ : ∀ a c' x, chartExtend E (fun z => ρc z * γ a c' z) x ≠ 0 →
      chartExtend E (fun z => ρb z) x = 1 := by
    intro a c' x hx
    have hxs : x ∈ E.val.source := by
      by_contra hxs
      exact hx (chartExtend_of_notMem hxs)
    rw [chartExtend_of_mem hxs] at hx ⊢
    have hρx : E.val x ∈ ball z₀ (3 / 2 * r) := by
      rw [← ρc.support_eq]
      exact left_ne_zero_of_mul hx
    exact ρb.one_of_mem_closedBall (show E.val x ∈ closedBall z₀ (2 * r) from
      ball_subset_closedBall (ball_subset_ball (show (3 / 2 * r : ℝ) ≤ 2 * r by linarith) hρx))
  have h1 : ∀ a c', Θ (smulTest _ (hΓ a c')
      (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hg a) (hS c'))) q R)) = 0 :=
    fun a c' => apply_wedge_normalPair_eq_zero w hΘ (hg a) (hF a) (hS c') hΘc hΔm hcar (hg0 a)
      (hpair a) hρ hρ0 (hΓ a c') (hΓρ a c') R
  -- the remaining terms vanish on the diagonal
  have hΛ0 : ∀ c' d, ∀ x ∈ Set.diagonal X, chartExtend E (fun z => ρc z * η c' d z) x = 0 := by
    intro c' d x hx
    by_cases hxs : x ∈ E.val.source
    · rw [chartExtend_of_mem hxs]
      simp only [hηdef]
      rw [(diagonal_chart hx).1, sub_self]
      simp
    · exact chartExtend_of_notMem hxs
  have h2 : ∀ c' d, Θ (smulTest _ (hΛ c' d)
      (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hS c') (hS d))) q R)) = 0 :=
    fun c' d => apply_smulTest_eq_zero w hΘ hΔm hcar _ (hΛ c' d) (hΛ0 c' d)
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

end Core

/-! ### The tangential reduction -/

section Reduction

open ProductComplexManifold SkodaElMirSubmanifold ChartPartition
open scoped ProductComplexManifold

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace (X × X)] [BorelSpace (X × X)]
  (w : KahlerBackground (n + n) (X × X)) {q : ℕ} {Θ : ProductCurrent (n + n) (X × X) (q + 1)}
  (hΘ : IsPositive Θ)

/-- The pulled-back slots. -/
abbrev pullSlots (b : Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2) :
    Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2 :=
  fun i => SmoothRealForm.pullback contMDiff_diagProjMap (b i)

omit [CompactSpace X] [MeasurableSpace (X × X)] [BorelSpace (X × X)] in
include hΘ in
/-- Permuting the slots of an elementary form does not change the value of a positive current. -/
theorem apply_elemTest_comp_perm {h : X × X → ℝ} (hh : ChartSmooth (n := n + n) h)
    (b : Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2) (hb : ∀ i, (b i).IsTypeOneOne)
    (σ : Equiv.Perm (Fin (q + 1))) :
    Θ (elemTest h hh (q + 1) (fun j => b (σ j)) fun j => hb (σ j)) =
      Θ (elemTest h hh (q + 1) b hb) := by
  refine hΘ.apply_eq_of_coeff_eqOn fun e z _ => ?_
  rw [coe_elemTest, coe_elemTest, elemForm_coeff, elemForm_coeff]
  exact congrArg _ (wedgeProd_comp_perm (q + 1) (fun j => (b j).coeff e z) σ)

omit [CompactSpace X] [MeasurableSpace (X × X)] [BorelSpace (X × X)] in
include hΘ in
/-- **Replacing one slot `bᵢ` by `Φ^*bᵢ`.** -/
theorem apply_elemTest_update_pullback {U : Set (X × X)}
    (hU : ∀ (h : X × X → ℝ) (hh : ChartSmooth (n := n + n) h), tsupport h ⊆ U →
      ∀ (c : Fin q → SmoothRealForm (n + n) (X × X) 2) (hc : ∀ i, (c i).IsTypeOneOne)
        (b : SmoothRealForm (n + n) (X × X) 2) (hb : b.IsTypeOneOne),
        Θ (wedgeTestLM (isTypeOneOne_sub_pullback hb) q (elemTest h hh q c hc)) = 0)
    {h : X × X → ℝ} (hh : ChartSmooth (n := n + n) h) (hhU : tsupport h ⊆ U)
    (b : Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2) (hb : ∀ i, (b i).IsTypeOneOne)
    (i : Fin (q + 1)) (hb' : ∀ j, (Function.update b i
      (SmoothRealForm.pullback contMDiff_diagProjMap (b i)) j).IsTypeOneOne) :
    Θ (elemTest h hh (q + 1) b hb) =
      Θ (elemTest h hh (q + 1) (Function.update b i
        (SmoothRealForm.pullback contMDiff_diagProjMap (b i))) hb') := by
  classical
  set σ := Equiv.swap i (Fin.last q)
  set b' := SmoothRealForm.pullback contMDiff_diagProjMap (b i)
  rw [← apply_elemTest_comp_perm hΘ hh b hb σ,
    ← apply_elemTest_comp_perm hΘ hh (Function.update b i b') hb' σ]
  have hupd : (fun j => Function.update b i b' (σ j)) =
      Function.update (fun j => b (σ j)) (Fin.last q) b' := by
    have h1 := Function.update_comp_equiv b σ i b'
    have h2 : σ.symm i = Fin.last q := by
      rw [Equiv.symm_swap, Equiv.swap_apply_left]
    rw [h2] at h1
    exact h1
  have hlast : b (σ (Fin.last q)) = b i := by rw [Equiv.swap_apply_right]
  have hdiff : elemTest h hh (q + 1) (fun j => b (σ j)) (fun j => hb (σ j)) -
      elemTest h hh (q + 1) (fun j => Function.update b i b' (σ j)) (fun j => hb' (σ j)) =
      wedgeTestLM (isTypeOneOne_sub_pullback (hb i)) q
        (elemTest h hh q (fun j => b (σ j.castSucc)) fun j => hb (σ j.castSucc)) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, coe_elemTest, coe_elemTest, coe_wedgeTestLM, coe_elemTest, hupd,
      elemForm_succ, elemForm_succ]
    have hinit : (fun j : Fin q => Function.update (fun j => b (σ j)) (Fin.last q) b'
        j.castSucc) = fun j => b (σ j.castSucc) := by
      funext j
      rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne]
    rw [hinit, Function.update_self, hlast]
    refine smoothRealForm_ext fun e z => ?_
    simp only [coeff_sub, wedgeTwo_coeff]
    rw [← wedgeCLM_apply, ← wedgeCLM_apply, ← wedgeCLM_apply, map_sub]
  have h0 := hU h hh hhU _ (fun j => hb (σ j.castSucc)) (b i) (hb i)
  rw [← hdiff, map_sub] at h0
  exact sub_eq_zero.mp h0

omit [CompactSpace X] [MeasurableSpace (X × X)] [BorelSpace (X × X)] in
theorem elemTest_congr {h : X × X → ℝ} (hh : ChartSmooth (n := n + n) h) {k : ℕ}
    {b b' : Fin k → SmoothRealForm (n + n) (X × X) 2} (hbb : b = b')
    (hb : ∀ i, (b i).IsTypeOneOne) (hb' : ∀ i, (b' i).IsTypeOneOne) :
    elemTest h hh k b hb = elemTest h hh k b' hb' := by
  subst hbb
  rfl

omit [CompactSpace X] [MeasurableSpace (X × X)] [BorelSpace (X × X)] in
include hΘ in
/-- **Replacing all the slots `bᵢ` by `Φ^*bᵢ`.** -/
theorem apply_elemTest_pullSlots {U : Set (X × X)}
    (hU : ∀ (h : X × X → ℝ) (hh : ChartSmooth (n := n + n) h), tsupport h ⊆ U →
      ∀ (c : Fin q → SmoothRealForm (n + n) (X × X) 2) (hc : ∀ i, (c i).IsTypeOneOne)
        (b : SmoothRealForm (n + n) (X × X) 2) (hb : b.IsTypeOneOne),
        Θ (wedgeTestLM (isTypeOneOne_sub_pullback hb) q (elemTest h hh q c hc)) = 0)
    {h : X × X → ℝ} (hh : ChartSmooth (n := n + n) h) (hhU : tsupport h ⊆ U)
    (b : Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2) (hb : ∀ i, (b i).IsTypeOneOne) :
    Θ (elemTest h hh (q + 1) b hb) =
      Θ (elemTest h hh (q + 1) (pullSlots b)
        fun i => isTypeOneOne_pullback contMDiff_diagProjMap (hb i)) := by
  classical
  set bk : ℕ → Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2 := fun k j =>
    if (j : ℕ) < k then SmoothRealForm.pullback contMDiff_diagProjMap (b j) else b j with hbkdef
  have hbk : ∀ k j, (bk k j).IsTypeOneOne := fun k j => by
    simp only [hbkdef]
    split_ifs
    · exact isTypeOneOne_pullback contMDiff_diagProjMap (hb j)
    · exact hb j
  have hstep : ∀ k, k < q + 1 → Θ (elemTest h hh (q + 1) (bk k) (hbk k)) =
      Θ (elemTest h hh (q + 1) (bk (k + 1)) (hbk (k + 1))) := by
    intro k hk
    have hkk : bk k ⟨k, hk⟩ = b ⟨k, hk⟩ := by simp [hbkdef]
    have hupd : Function.update (bk k) ⟨k, hk⟩
        (SmoothRealForm.pullback contMDiff_diagProjMap (bk k ⟨k, hk⟩)) = bk (k + 1) := by
      funext j
      by_cases hj : j = ⟨k, hk⟩
      · subst hj
        rw [Function.update_self, hkk]
        simp [hbkdef]
      · rw [Function.update_of_ne hj]
        have hjk : (j : ℕ) ≠ k := fun h' => hj (Fin.ext h')
        simp only [hbkdef]
        split_ifs with h1 h2 h2 <;> first | rfl | omega
    rw [apply_elemTest_update_pullback hΘ hU hh hhU (bk k) (hbk k) ⟨k, hk⟩
      (by rw [hupd]; exact hbk (k + 1))]
    exact congrArg Θ (elemTest_congr hh hupd _ _)
  have hall : ∀ k, k ≤ q + 1 → Θ (elemTest h hh (q + 1) b hb) =
      Θ (elemTest h hh (q + 1) (bk k) (hbk k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact congrArg Θ (elemTest_congr hh (funext fun j => by simp [hbkdef]) _ _)
    | succ k ih =>
      intro hk
      rw [ih (Nat.le_of_succ_le hk), hstep k (Nat.lt_of_succ_le hk)]
  rw [hall (q + 1) le_rfl]
  exact congrArg Θ (elemTest_congr hh (funext fun j => by simp [hbkdef, j.isLt]) _ _)

include hΘ in
/-- **`h` may be replaced by `h ∘ Φ`** (they agree on `Δ`). -/
theorem apply_elemTest_comp_diagProjMap (hcar : traceMeasure w Θ hΘ (Set.diagonal X)ᶜ = 0)
    {h : X × X → ℝ} (hh : ChartSmooth (n := n + n) h)
    (c : Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2) (hc : ∀ i, (c i).IsTypeOneOne) :
    Θ (elemTest (fun x => h (diagProjMap X x)) (chartSmooth_comp contMDiff_diagProjMap hh)
      (q + 1) c hc) = Θ (elemTest h hh (q + 1) c hc) := by
  have hΔm : MeasurableSet (Set.diagonal X) := isClosed_diagonal.measurableSet
  have hd : ChartSmooth (n := n + n) (fun x => h (diagProjMap X x) - h x) := fun e =>
    ((chartSmooth_comp contMDiff_diagProjMap hh) e).sub (hh e)
  have hsplit : elemTest (fun x => h (diagProjMap X x)) (chartSmooth_comp contMDiff_diagProjMap hh)
      (q + 1) c hc = elemTest h hh (q + 1) c hc +
        smulTest _ hd (elemTest (fun _ => 1) (chartSmooth_const 1) (q + 1) c hc) := by
    refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
    simp only [Submodule.coe_add, coeff_add, coe_elemTest, elemForm_coeff]
    change _ = _ + (fun x => h (diagProjMap X x) - h x) (e.val.symm z) •
      (elemForm (fun _ => 1) (chartSmooth_const 1) (q + 1) c).coeff e z
    rw [elemForm_coeff, one_smul, ← add_smul, add_sub_cancel]
  rw [hsplit, map_add, apply_smulTest_eq_zero w hΘ hΔm hcar _ hd, add_zero]
  rintro ⟨x, y⟩ (hxy : x = y)
  subst hxy
  simp [diagProjMap]

include hΘ in
/-- **The tangential reduction** (`bou:diagonal-support`, step S3): a closed positive current
carried by the diagonal of `X × X` satisfies `Θ (Φ^*φ) = Θ φ` for every test form `φ`,
`Φ(x, y) = (x, x)`. -/
theorem apply_pullback_diagProjMap_eq (hΘc : IsClosedCurrent Θ)
    (hcar : traceMeasure w Θ hΘ (Set.diagonal X)ᶜ = 0)
    (φ : testSpace (n + n) (X × X) (q + 1)) :
    Θ (pullbackTestLM contMDiff_diagProjMap (q + 1) φ) = Θ φ := by
  classical
  have hΔm : MeasurableSet (Set.diagonal X) := isClosed_diagonal.measurableSet
  choose U hUo hUmem hUvan using
    exists_nhds_apply_wedge_sub_pullback_eq_zero w hΘ hΘc hcar (q := q)
  suffices hsuff : Θ ∘ₗ pullbackTestLM contMDiff_diagProjMap (q + 1) = Θ from
    LinearMap.congr_fun hsuff φ
  refine linearMap_ext_elem fun h hh b hb => ?_
  set S : X × X → TopologicalSpace.Opens (X × X) := fun p =>
    if p ∈ Set.diagonal X then ⟨U p.1, hUo p.1⟩
    else ⟨(Set.diagonal X)ᶜ, isClosed_diagonal.isOpen_compl⟩ with hSdef
  have hcover : ∀ p : X × X, ∃ i, p ∈ S i := by
    intro p
    refine ⟨p, ?_⟩
    by_cases hp : p ∈ Set.diagonal X
    · simp only [hSdef, hp, if_true, TopologicalSpace.Opens.mem_mk]
      obtain ⟨x, y⟩ := p
      obtain rfl : x = y := hp
      exact hUmem x
    · simp only [hSdef, hp, if_false, TopologicalSpace.Opens.mem_mk]
      exact hp
  obtain ⟨N, χ, idx, hχs, -, hχS, -, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n + n) S hcover
  have hdecomp : elemTest h hh (q + 1) b hb =
      ∑ a, elemTest (fun x => χ a x * h x) (chartSmooth_mul (hχs a) hh) (q + 1) b hb := by
    refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
    simp only [Submodule.coe_sum, ClosedCurrentLocalTests.coeff_sum, coe_elemTest, elemForm_coeff]
    rw [← Finset.sum_smul, ← Finset.sum_mul, hsum, one_mul]
  rw [LinearMap.comp_apply, hdecomp, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  set ha := chartSmooth_mul (hχs a) hh
  have hpull : pullbackTestLM contMDiff_diagProjMap (q + 1)
      (elemTest (fun x => χ a x * h x) ha (q + 1) b hb) =
      elemTest (fun x => (fun x => χ a x * h x) (diagProjMap X x))
        (chartSmooth_comp contMDiff_diagProjMap ha) (q + 1) (pullSlots b)
        (fun i => isTypeOneOne_pullback contMDiff_diagProjMap (hb i)) :=
    Subtype.ext (pullback_elemForm contMDiff_diagProjMap _ ha (q + 1) b)
  rw [hpull, apply_elemTest_comp_diagProjMap w hΘ hcar ha]
  by_cases hp : idx a ∈ Set.diagonal X
  · have hsub : tsupport (fun x => χ a x * h x) ⊆ U (idx a).1 := by
      refine tsupport_mul_subset_left.trans ?_
      have h' := hχS a
      simp only [hSdef, hp, if_true, TopologicalSpace.Opens.coe_mk] at h'
      exact h'
    exact (apply_elemTest_pullSlots hΘ (hUvan (idx a).1) ha hsub b hb).symm
  · have hsub : tsupport (χ a) ⊆ (Set.diagonal X)ᶜ := by
      have h' := hχS a
      simp only [hSdef, hp, if_false, TopologicalSpace.Opens.coe_mk] at h'
      exact h'
    have hvan : ∀ x ∈ Set.diagonal X, χ a x * h x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hsub h' hx), zero_mul]
    have hz : ∀ (c : Fin (q + 1) → SmoothRealForm (n + n) (X × X) 2)
        (hc : ∀ i, (c i).IsTypeOneOne), Θ (elemTest _ ha (q + 1) c hc) = 0 := by
      intro c hc
      have he : elemTest _ ha (q + 1) c hc =
          smulTest _ ha (elemTest (fun _ => 1) (chartSmooth_const 1) (q + 1) c hc) := by
        refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
        change (elemForm _ ha (q + 1) c).coeff e z =
          (fun x => χ a x * h x) (e.val.symm z) •
            (elemForm (fun _ => 1) (chartSmooth_const 1) (q + 1) c).coeff e z
        rw [elemForm_coeff, elemForm_coeff, one_smul]
      rw [he]
      exact apply_smulTest_eq_zero w hΘ hΔm hcar _ ha hvan
    rw [hz, hz]

end Reduction

end SGPT.Foundations.Analysis.Pending.DiagonalTangentialReduction
