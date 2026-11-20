import SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon
import SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# independent local equations of a submanifold among given generators

Source: `rmk:bdiv:L749` (algebraization of the book's blow-up models; analytic input of the
Jacobian criterion).

Let `A` be a subset of a complex manifold `M` of dimension `N`, regular of dimension `k` at
`x ∈ A` (`RegularAtDim`), and let `G₁, …, G_K` be holomorphic functions which generate the ideal
`𝓘_A` of germs vanishing on `A` at `x`.  Then (`exists_selected_equations_bd5`) one can select
`c = N - k` of them, `G_{s(1)}, …, G_{s(c)}`, which

* still generate `𝓘_A` at `x`, and
* have linearly independent differentials at `x`: there are tangent vectors `v₁, …, v_c` (in the
  preferred chart) with `dG_{s(l)}(v_j) = δ_{jl}`.

Proof: in a flattening chart `Φ` of `A`, Hadamard's lemma (`exists_eq_sum_flatCoord`) writes
`G_j = ∑_m β_{jm} φ_m` in the normal coordinates `φ_m`, and conversely every `φ_m` is a
combination of the `G_j`; hence the matrix `B = β(x)` has rank `c`, a `c × c` minor `β_sel(x)` is
invertible, and `φ = β_sel⁻¹ G_sel` near `x` (the entries of the inverse are holomorphic: adjugate
over determinant).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace SGPT.BDivisor.BD5

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open BlowupFlatCoordinates RelativePrincipalizationSpan

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-! ### Holomorphy of determinants and inverse matrices -/

omit [IsComplexManifold N M] in
theorem holomorphicAt_finset_prod_bd5 {ι : Type*} (s : Finset ι) {F : ι → M → ℂ} {x : M}
    (hF : ∀ i ∈ s, HolomorphicAt N (F i) x) :
    HolomorphicAt N (fun y => ∏ i ∈ s, F i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holomorphicAt_const (n := N) (x := x) (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

omit [IsComplexManifold N M] in
theorem holomorphicAt_det_bd5 {c : ℕ} {B : M → Matrix (Fin c) (Fin c) ℂ} {x : M}
    (hB : ∀ i j, HolomorphicAt N (fun y => B y i j) x) :
    HolomorphicAt N (fun y => (B y).det) x := by
  have h : (fun y => (B y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin c), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, B y (σ i) i := by
    funext y
    rw [Matrix.det_apply']
  rw [h]
  exact HolomorphicAt.sum _ fun σ _ => (holomorphicAt_const _).mul
    (holomorphicAt_finset_prod_bd5 _ fun i _ => hB _ _)

theorem holomorphicAt_inv_entry_bd5 {c : ℕ} {B : M → Matrix (Fin c) (Fin c) ℂ} {x : M}
    (hB : ∀ i j, HolomorphicAt N (fun y => B y i j) x) (hdet : (B x).det ≠ 0) (i j : Fin c) :
    HolomorphicAt N (fun y => (B y)⁻¹ i j) x := by
  classical
  have h : (fun y => (B y)⁻¹ i j) =
      fun y => ((B y).det)⁻¹ * ((B y).updateRow j (Pi.single i 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv',
      smul_eq_mul]
  rw [h]
  refine (HolomorphicAt.inv (holomorphicAt_det_bd5 hB) hdet).mul ?_
  apply holomorphicAt_det_bd5
  intro a b
  by_cases ha : a = j
  · subst ha
    simp only [Matrix.updateRow_self]
    exact holomorphicAt_const _
  · simp only [Matrix.updateRow_ne ha]
    exact hB a b

omit [IsComplexManifold N M] in
theorem isInSpanAt_of_eventuallyEq_bd5 {S : (M → ℂ) → Prop} {x : M} {f g : M → ℂ}
    (hf : IsInSpanAt (n := N) S x f) (h : f =ᶠ[𝓝 x] g) : IsInSpanAt (n := N) S x g := by
  obtain ⟨hhol, K, s, a, hs, ha, hsum⟩ := hf
  exact ⟨hhol.congr h, K, s, a, hs, ha, h.symm.trans hsum⟩

/-! ### Derivatives in the preferred chart -/

/-- The complex derivative of `f` at `x`, read in the preferred chart at `x`. -/
def chartDeriv (x : M) (f : M → ℂ) : ComplexModel N →L[ℂ] ℂ :=
  fderiv ℂ (fun z => f ((chartAt (ComplexModel N) x).symm z)) (chartAt (ComplexModel N) x x)

theorem differentiableAt_chart_bd5 {x : M} {f : M → ℂ} (hf : HolomorphicAt N f x) :
    DifferentiableAt ℂ (fun z => f ((chartAt (ComplexModel N) x).symm z))
      (chartAt (ComplexModel N) x x) :=
  ((CoherentIdealColon.holomorphicAt_iff_holAt_chart (mem_chart_source (ComplexModel N) x)).mp hf).self_of_nhds

omit [IsComplexManifold N M] in
theorem tendsto_chart_symm_bd5 (x : M) :
    Tendsto (chartAt (ComplexModel N) x).symm (𝓝 (chartAt (ComplexModel N) x x)) (𝓝 x) := by
  have h := (chartAt (ComplexModel N) x).continuousAt_symm
    ((chartAt (ComplexModel N) x).map_source (mem_chart_source (ComplexModel N) x))
  rwa [ContinuousAt, (chartAt (ComplexModel N) x).left_inv (mem_chart_source (ComplexModel N) x)] at h

omit [IsComplexManifold N M] in
theorem chartDeriv_congr_bd5 {x : M} {f g : M → ℂ} (h : f =ᶠ[𝓝 x] g) :
    chartDeriv (N := N) x f = chartDeriv (N := N) x g := by
  unfold chartDeriv
  have h' : (fun z => f ((chartAt (ComplexModel N) x).symm z)) =ᶠ[𝓝 (chartAt (ComplexModel N) x x)]
      (fun z => g ((chartAt (ComplexModel N) x).symm z)) :=
    (tendsto_chart_symm_bd5 (N := N) x).eventually h
  exact h'.fderiv_eq

/-- The derivative of a combination `∑ aᵢ sᵢ` with `sᵢ(x) = 0` is `∑ aᵢ(x) dsᵢ`. -/
theorem chartDeriv_sum_mul_bd5 {x : M} {K : ℕ} (a s : Fin K → M → ℂ)
    (ha : ∀ i, HolomorphicAt N (a i) x) (hs : ∀ i, HolomorphicAt N (s i) x)
    (hs0 : ∀ i, s i x = 0) :
    chartDeriv (N := N) x (fun y => ∑ i, a i y * s i y) =
      ∑ i, a i x • chartDeriv (N := N) x (s i) := by
  unfold chartDeriv
  have hx : (chartAt (ComplexModel N) x).symm (chartAt (ComplexModel N) x x) = x :=
    (chartAt (ComplexModel N) x).left_inv (mem_chart_source (ComplexModel N) x)
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin K)),
      DifferentiableAt ℂ (fun z => a i ((chartAt (ComplexModel N) x).symm z) *
        s i ((chartAt (ComplexModel N) x).symm z)) (chartAt (ComplexModel N) x x) := fun i _ =>
    (differentiableAt_chart_bd5 (ha i)).mul (differentiableAt_chart_bd5 (hs i))
  show fderiv ℂ (fun z => ∑ i, a i ((chartAt (ComplexModel N) x).symm z) *
    s i ((chartAt (ComplexModel N) x).symm z)) (chartAt (ComplexModel N) x x) = _
  rw [fderiv_fun_sum hd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_fun_mul (differentiableAt_chart_bd5 (ha i)) (differentiableAt_chart_bd5 (hs i))]
  ext v
  simp [hx, hs0 i]

section Flat

variable {x : M} (Φ : LocalHolomorphicEquivAt (n := N) (chartAt (ComplexModel N) x x))

omit [IsComplexManifold N M] in
theorem chartDeriv_flatCoord_bd5 (hsrc : Φ.source ⊆ (chartAt (ComplexModel N) x).target)
    (i : Fin N) :
    chartDeriv (N := N) x (flatCoord Φ i) =
      (EuclideanSpace.proj i : ComplexModel N →L[ℂ] ℂ).comp
        (fderiv ℂ Φ.toFun (chartAt (ComplexModel N) x x)) := by
  unfold chartDeriv
  have hΦ : DifferentiableAt ℂ Φ.toFun (chartAt (ComplexModel N) x x) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have heq : (fun z => flatCoord Φ i ((chartAt (ComplexModel N) x).symm z)) =ᶠ[𝓝 (chartAt (ComplexModel N) x x)]
      fun z => Φ.toFun z i := by
    filter_upwards [Φ.isOpen_source.mem_nhds Φ.center_mem_source] with z hz
    simp only [flatCoord]
    rw [(chartAt (ComplexModel N) x).right_inv (hsrc hz)]
  rw [heq.fderiv_eq]
  exact ((EuclideanSpace.proj i : ComplexModel N →L[ℂ] ℂ).hasFDerivAt.comp _
    hΦ.hasFDerivAt).fderiv

omit [IsComplexManifold N M] in
theorem fderiv_flat_surjective_bd5 :
    Function.Surjective (fderiv ℂ Φ.toFun (chartAt (ComplexModel N) x x)) := by
  have hΦ : DifferentiableAt ℂ Φ.toFun (chartAt (ComplexModel N) x x) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hq : Φ.toFun (chartAt (ComplexModel N) x x) ∈ Φ.target :=
    Φ.mapsTo_toFun Φ.center_mem_source
  have hΨ : DifferentiableAt ℂ Φ.invFun (Φ.toFun (chartAt (ComplexModel N) x x)) :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hq)
  have hid : (Φ.invFun ∘ Φ.toFun) =ᶠ[𝓝 (chartAt (ComplexModel N) x x)] id := by
    filter_upwards [Φ.isOpen_source.mem_nhds Φ.center_mem_source] with z hz
    exact Φ.left_inv z hz
  have hcomp := (hΨ.hasFDerivAt.comp (chartAt (ComplexModel N) x x) hΦ.hasFDerivAt).fderiv
  rw [hid.fderiv_eq, fderiv_id] at hcomp
  have hinj : Function.Injective (fderiv ℂ Φ.toFun (chartAt (ComplexModel N) x x)) := by
    intro u w huw
    have h1 := congrArg (fderiv ℂ Φ.invFun (Φ.toFun (chartAt (ComplexModel N) x x))) huw
    have h2 := congrArg (fun L : ComplexModel N →L[ℂ] ComplexModel N => L u) hcomp
    have h3 := congrArg (fun L : ComplexModel N →L[ℂ] ComplexModel N => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h2 h3
    rw [h2, h3]
    exact h1
  exact (LinearMap.injective_iff_surjective
    (f := (fderiv ℂ Φ.toFun (chartAt (ComplexModel N) x x)).toLinearMap)).mp hinj

end Flat

/-! ### Linear algebra -/

/-- A `K × c` matrix whose rows span `(ℂ^c)*` has an invertible `c × c` minor. -/
theorem exists_invertible_minor_bd5 {K c : ℕ} (B : Matrix (Fin K) (Fin c) ℂ)
    (hspan : Submodule.span ℂ (Set.range B) = ⊤) :
    ∃ sel : Fin c → Fin K, (B.submatrix sel id).det ≠ 0 := by
  classical
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent ℂ (Set.range B)
  have : Fintype t := ((Set.finite_range B).subset htsub).fintype
  have htspan' : Submodule.span ℂ t = ⊤ := htspan.trans hspan
  let bas : Module.Basis t ℂ (Fin c → ℂ) := Module.Basis.mk htli (by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, htspan'])
  have hcard : Fintype.card t = c := by
    have := Module.finrank_eq_card_basis bas
    simpa using this.symm
  have hfin : Nonempty (t ≃ Fin c) := ⟨Fintype.equivFinOfCardEq hcard⟩
  obtain ⟨eq⟩ := hfin
  have hpre : ∀ w : t, ∃ j, B j = w.1 := fun w => htsub w.2
  choose sel0 hsel0 using hpre
  refine ⟨fun l => sel0 (eq.symm l), ?_⟩
  have hrows : LinearIndependent ℂ (fun l : Fin c => (B.submatrix (fun l => sel0 (eq.symm l)) id) l) := by
    have : (fun l : Fin c => (B.submatrix (fun l => sel0 (eq.symm l)) id) l) =
        (fun w : t => w.1) ∘ eq.symm := by
      funext l
      simp only [Function.comp_apply]
      rw [← hsel0 (eq.symm l)]
      rfl
    rw [this]
    exact htli.comp _ eq.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

/-! ### Selection of independent generators -/

/-- **Independent local equations among given generators.**  If `A ⊆ M` is regular of dimension
`k` at `x` and the holomorphic `G₁, …, G_K` (vanishing on `A` near `x`) generate `𝓘_A` at `x`,
then `N - k` of them still generate `𝓘_A` at `x` and have independent differentials. -/
theorem exists_selected_equations_bd5 {A : Set M} {x : M} {k : ℕ}
    (hreg : RegularAtDim (n := N) A x k)
    {K : ℕ} (G : Fin K → M → ℂ)
    (hGA : ∀ j, (vanishingIdeal (n := N) A).mem x (G j))
    (hgen : ∀ g, (vanishingIdeal (n := N) A).mem x g →
      IsInSpanAt (n := N) (· ∈ range G) x g) :
    ∃ (sel : Fin (N - k) → Fin K) (v : Fin (N - k) → ComplexModel N),
      (∀ j l, chartDeriv (N := N) x (G (sel l)) (v j) = if j = l then 1 else 0) ∧
      ∀ g, (vanishingIdeal (n := N) A).mem x g →
        IsInSpanAt (n := N) (· ∈ range (fun l => G (sel l))) x g := by
  classical
  obtain ⟨hk, hxA, Φ, hsrc, h0, hflat⟩ := hreg
  set e := chartAt (ComplexModel N) x with he
  set c := N - k with hc
  let idx : Fin c → Fin N := fun l => ⟨k + l, by omega⟩
  let φ : Fin c → M → ℂ := fun l => flatCoord Φ (idx l)
  have hxdom : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hflat' : ∀ {y : M}, y ∈ e.source → e y ∈ Φ.source →
      (y ∈ A ↔ Φ.toFun (e y) ∈ complexCoordinatePlane N k) := fun hy hy' => hflat hy hy'
  have hφA : ∀ l, (vanishingIdeal (n := N) A).mem x (φ l) := fun l =>
    flatCoord_mem_vanishingIdeal Φ hflat' (by simp [idx]) hxdom
  have hflat0 : ∀ i, flatCoord Φ i x = 0 := by
    intro i
    simp only [flatCoord]
    have h0' : Φ.toFun (e x) = 0 := h0
    change Φ.toFun (e x) i = 0
    rw [h0']
    rfl
  -- Hadamard: every germ of `𝓘_A` is a combination of the normal coordinates
  have hHad : ∀ g, (vanishingIdeal (n := N) A).mem x g →
      ∃ b : Fin c → M → ℂ, (∀ l, HolomorphicAt N (b l) x) ∧
        g =ᶠ[𝓝 x] fun y => ∑ l, b l y * φ l y := by
    intro g hg
    obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hsrc hflat' hxdom hg
    refine ⟨fun l => b (idx l), fun l => hbhol _, ?_⟩
    filter_upwards [hbeq] with y hy
    rw [hy]
    -- the terms with `i < k` vanish
    have hsplit : ∑ i : Fin N, b i y * flatCoord Φ i y =
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ i.1), b i y * flatCoord Φ i y := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · rw [hb0 i (by omega), Pi.zero_apply, zero_mul]
    rw [hsplit]
    refine Finset.sum_bij' (fun i hi => (⟨i.1 - k, by
        have := (Finset.mem_filter.mp hi).2; omega⟩ : Fin c))
      (fun l _ => idx l) (fun _ _ => Finset.mem_univ _)
      (fun l _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [idx]⟩)
      (fun i hi => by
        have := (Finset.mem_filter.mp hi).2
        ext; simp only [idx]; omega)
      (fun l _ => by ext; simp [idx]) (fun i hi => ?_)
    have := (Finset.mem_filter.mp hi).2
    have hidx : idx ⟨i.1 - k, by omega⟩ = i := by ext; simp only [idx]; omega
    simp only [φ, hidx]
  -- the derivatives of the normal coordinates
  set T := fderiv ℂ Φ.toFun (e x) with hT
  have hdφ : ∀ l, chartDeriv (N := N) x (φ l) =
      (EuclideanSpace.proj (idx l) : ComplexModel N →L[ℂ] ℂ).comp T := fun l =>
    chartDeriv_flatCoord_bd5 Φ hsrc (idx l)
  have hTsurj := fderiv_flat_surjective_bd5 Φ
  -- dual vectors of the normal coordinates
  have hw : ∀ m : Fin c, ∃ w : ComplexModel N, ∀ l, chartDeriv (N := N) x (φ l) w = if l = m then 1 else 0 := by
    intro m
    obtain ⟨w, hw⟩ := hTsurj (EuclideanSpace.single (idx m) 1)
    refine ⟨w, fun l => ?_⟩
    rw [hdφ l, ContinuousLinearMap.comp_apply, hw]
    show (EuclideanSpace.single (idx m) (1 : ℂ)).ofLp (idx l) = _
    rw [PiLp.single_apply]
    by_cases hlm : l = m
    · subst hlm; simp
    · have : idx l ≠ idx m := fun h => hlm (by ext; have := congrArg Fin.val h; simp [idx] at this; omega)
      simp [this, hlm]
  choose w hw using hw
  -- Hadamard coefficients of the generators
  have hG : ∀ j, ∃ b : Fin c → M → ℂ, (∀ l, HolomorphicAt N (b l) x) ∧
      G j =ᶠ[𝓝 x] fun y => ∑ l, b l y * φ l y := fun j => hHad (G j) (hGA j)
  choose β hβhol hβeq using hG
  have hφhol : ∀ l, HolomorphicAt N (φ l) x := fun l => holomorphicAt_flatCoord Φ _ hxdom
  have hdG : ∀ j, chartDeriv (N := N) x (G j) = ∑ l, β j l x • chartDeriv (N := N) x (φ l) := by
    intro j
    rw [chartDeriv_congr_bd5 (hβeq j)]
    exact chartDeriv_sum_mul_bd5 (β j) φ (hβhol j) hφhol (fun l => hflat0 _)
  -- the matrix `B = β(x)`
  let B : Matrix (Fin K) (Fin c) ℂ := fun j l => β j l x
  have hBw : ∀ j m, chartDeriv (N := N) x (G j) (w m) = B j m := by
    intro j m
    rw [hdG j]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, hw, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  -- the rows of `B` span: every normal coordinate is a combination of the generators
  have hspan : Submodule.span ℂ (Set.range B) = ⊤ := by
    apply eq_top_iff.mpr
    have hbasis : ∀ m : Fin c, (Pi.single m 1 : Fin c → ℂ) ∈ Submodule.span ℂ (Set.range B) := by
      intro m
      obtain ⟨-, R, s, a, hs, ha, hsum⟩ := hgen (φ m) (hφA m)
      choose t ht using hs
      have hs' : s = fun r => G (t r) := funext fun r => (ht r).symm
      subst hs'
      have hsA : ∀ r, G (t r) x = 0 := fun r => (hGA (t r)).2.self_of_nhds hxA
      have hshol : ∀ r, HolomorphicAt N (G (t r)) x := fun r => (hGA (t r)).1
      have hd := chartDeriv_congr_bd5 (N := N) hsum
      rw [chartDeriv_sum_mul_bd5 a (fun r => G (t r)) ha hshol hsA] at hd
      have hrow : (Pi.single m 1 : Fin c → ℂ) = ∑ r, a r x • B (t r) := by
        funext l
        have := congrArg (fun L : ComplexModel N →L[ℂ] ℂ => L (w l)) hd
        simp only [hw, FunLike.coe_sum, Finset.sum_apply,
          FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        simp only [hBw] at this
        by_cases hlm : l = m
        · subst hlm; simpa using this
        · have hml : ¬ m = l := Ne.symm hlm
          simp only [hlm, hml, if_false] at this ⊢
          exact this
      rw [hrow]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t r, rfl⟩)
    intro u _
    have hu : u = ∑ m, u m • (Pi.single m 1 : Fin c → ℂ) := by
      funext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hu]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hbasis m)
  obtain ⟨sel, hdet⟩ := exists_invertible_minor_bd5 B hspan
  let Bs : Matrix (Fin c) (Fin c) ℂ := B.submatrix sel id
  have hBs : IsUnit Bs := (Matrix.isUnit_iff_isUnit_det Bs).mpr (Ne.isUnit hdet)
  -- dual vectors of the selected generators
  let v : Fin c → ComplexModel N := fun j => ∑ m, Bs⁻¹ m j • w m
  refine ⟨sel, v, fun j l => ?_, fun g hg => ?_⟩
  · simp only [v, map_sum, map_smul, hBw, smul_eq_mul]
    have h1 : ∑ m, Bs⁻¹ m j * B (sel l) m = (Bs * Bs⁻¹) l j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    rw [h1, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det Bs).mp hBs), Matrix.one_apply]
    by_cases hjl : j = l
    · subst hjl; simp
    · simp [hjl, Ne.symm hjl]
  · -- the normal coordinates lie in the span of the selected generators
    let Bf : M → Matrix (Fin c) (Fin c) ℂ := fun y l m => β (sel l) m y
    have hBfhol : ∀ l m, HolomorphicAt N (fun y => Bf y l m) x := fun l m => hβhol _ _
    have hBfx : Bf x = Bs := rfl
    have hdetx : (Bf x).det ≠ 0 := by rw [hBfx]; exact hdet
    have hφspan : ∀ m, IsInSpanAt (n := N) (· ∈ range (fun l => G (sel l))) x (φ m) := by
      intro m
      have hdetev : ∀ᶠ y in 𝓝 x, (Bf y).det ≠ 0 :=
        (holomorphicAt_det_bd5 hBfhol).continuousAt.eventually_ne hdetx
      have heq : φ m =ᶠ[𝓝 x] fun y => ∑ l, (Bf y)⁻¹ m l * G (sel l) y := by
        have hall : ∀ᶠ y in 𝓝 x, ∀ l, G (sel l) y = ∑ m', β (sel l) m' y * φ m' y :=
          eventually_all.mpr fun l => hβeq (sel l)
        filter_upwards [hdetev, hall] with y hy hGy
        have hmv : (fun l => G (sel l) y) = (Bf y).mulVec (fun m' => φ m' y) := by
          funext l
          rw [hGy l]
          rfl
        have hinv : (Bf y)⁻¹.mulVec ((Bf y).mulVec (fun m' => φ m' y)) = fun m' => φ m' y := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hy), Matrix.one_mulVec]
        have := congrFun hinv m
        rw [← hmv] at this
        rw [← this]
        rfl
      refine isInSpanAt_of_eventuallyEq_bd5 ?_ heq.symm
      have hsum := IsInSpanAt.sum (n := N) (S := (· ∈ range (fun l => G (sel l)))) (x := x)
        Finset.univ (F := fun l y => (Bf y)⁻¹ m l * G (sel l) y) (fun l _ =>
          IsInSpanAt.mul_left (holomorphicAt_inv_entry_bd5 (N := N) hBfhol hdetx m l)
            ⟨(hGA (sel l)).1, 1, fun _ => G (sel l), fun _ => 1, fun _ => ⟨l, rfl⟩,
              fun _ => holomorphicAt_const _, Eventually.of_forall fun y => by simp⟩)
      exact hsum
    obtain ⟨b, hbhol, hbeq⟩ := hHad g hg
    refine isInSpanAt_of_eventuallyEq_bd5 ?_ hbeq.symm
    exact IsInSpanAt.sum (n := N) Finset.univ fun m _ =>
      IsInSpanAt.mul_left (hbhol m) (hφspan m)

end SGPT.BDivisor.BD5
