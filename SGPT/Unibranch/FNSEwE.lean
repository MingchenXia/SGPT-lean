import SGPT.Unibranch.FNSHull
import SGPT.GAGA.CoreCLaurent
import SGPT.Foundations.Analysis.Pending.RiemannExtension

/-!
# Extension with estimates by the resolvent trick

Source: the Stein neighbourhood step of Fornæss–Narasimhan, *The Levi problem on complex spaces
with singularities*, Math. Ann. 248 (1980), Theorem 5.3.1 (`[FN80]`; there quoted from Siu),
for `thm:FN` (2) ⇒ (1) (`appendix_unibranch.tex`).

Let `Y = {h₁ = … = h_r = 0}` (the `hₗ` holomorphic on an open `O ⊆ ℂᴺ`), `K = pbox R p` a compact
polynomial polyhedron `{|xᵢ| ≤ R, |pⱼ(x)| ≤ 1} ⊆ O` and `g` holomorphic on `O` with `|g| < θ` on
`Y ∩ K`. Then `g^m` agrees on `Y` with a function of size `O(θ^m)` on `K`:

`exists_extension_estimate`: there are an open `U ⊇ K`, a constant `C` and, for every `m`,
functions `Q_{m,l}` holomorphic on `U` with `|g^m - ∑ₗ hₗ Q_{m,l}| ≤ C θ^m` on `K`.

This is the estimate behind Siu's Stein neighbourhood theorem in the form needed by `[FN80]`
(see `FNSSiu`). Proof (holomorphic functional calculus in `𝒪(K)/(h)`): on the compact slice
`K × {θ ≤ |ζ| ≤ R₀} ⊆ ℂ^{N+1}` the functions `ζ - g(x), h₁(x), …, h_r(x)` have no common zero, so
Theorem B for surjections on slices of polynomial graphs (GAGA `Laurent.exists_decompose_slice`)
gives `1 = a₀(x, ζ) (ζ - g(x)) + ∑ₗ aₗ(x, ζ) hₗ(x)` near the slice. Put
`F_m(x) = (2πi)⁻¹ ∮_{|ζ| = θ} ζ^m a₀(x, ζ) dζ`. Cauchy's theorem on the annulus moves the contour to
`|ζ| = R₀ > sup |g|`, where `a₀ = (1 - ∑ aₗ hₗ)/(ζ - g)`, so that `F_m = g^m - ∑ₗ hₗ Q_{m,l}` with
`Q_{m,l}(x) = (2πi)⁻¹ ∮_{|ζ| = R₀} ζ^m aₗ(x, ζ)/(ζ - g(x)) dζ` holomorphic in `x`
(TN `differentiableAt_circleIntegral_param`), while `|F_m| ≤ θ^{m+1} sup |a₀|` on `K`.
No Fréchet open mapping theorem and no coherence of the ideal sheaf of `Y` are needed.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Complex
open scoped Topology Real
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNS

open E2Nov16FNPolynomialPolyhedron E2Nov16FNPolynomialGraphBox FNR
open SGPT.GAGA.Core
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf (HolAt)

variable {N q r : ℕ}

/-! ### Compact polynomial polyhedra -/

/-- The compact polynomial polyhedron `{x : |xᵢ| ≤ R, |pⱼ(x)| ≤ 1}`. -/
def pbox (R : ℝ) (p : Fin q → Poly N) : Set (ComplexModel N) :=
  {x | (∀ i, ‖x i‖ ≤ R) ∧ ∀ j, ‖polyEval (p j) x‖ ≤ 1}

/-- The Codex slice `Laurent.slice univ (graphFunctions p) (graphBox R)` is `pbox R p`. -/
theorem slice_graphBox_eq_pbox (R : ℝ) (p : Fin q → Poly N) :
    Laurent.slice univ (graphFunctions p) (graphBox R) = pbox R p := by
  ext x
  simp only [Laurent.slice, mem_inter_iff, mem_univ, true_and, mem_preimage, Box.mem_boxSet,
    pbox, mem_setOf_eq]
  rw [Fin.forall_fin_add]
  simp [graphFunctions, mem_closedBall_zero_iff]

theorem isClosed_pbox (R : ℝ) (p : Fin q → Poly N) : IsClosed (pbox R p) := by
  have h : pbox R p = (⋂ i, {x : ComplexModel N | ‖x i‖ ≤ R}) ∩
      ⋂ j, {x | ‖polyEval (p j) x‖ ≤ 1} := by
    ext x; simp [pbox]
  rw [h]
  exact (isClosed_iInter fun i =>
    isClosed_le ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.norm) continuous_const).inter
    (isClosed_iInter fun j => isClosed_le (continuous_polyEval _).norm continuous_const)

theorem isCompact_pbox (R : ℝ) (p : Fin q → Poly N) : IsCompact (pbox R p) := by
  refine (isCompact_closedBall (0 : ComplexModel N) (∑ _i : Fin N, R)).of_isClosed_subset
    (isClosed_pbox R p) fun x hx => ?_
  rw [mem_closedBall_zero_iff]
  exact (Box.norm_le_sum_norm x).trans (Finset.sum_le_sum fun i _ => hx.1 i)

/-! ### Units in the image of a free module -/

/-- If an entry of the row `A` is a unit at `y`, the constant `1` lies in the image of the free
module under `A` at `y`. -/
theorem map_top_mem_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type}
    [Fintype ι] [DecidableEq ι] {A : Unit → ι → E → ℂ} {y : E} (j₀ : ι)
    (hA : HolAt (A () j₀) y) (hne : A () j₀ y ≠ 0) :
    ((GermModule.top E ι).map A).mem y (fun _ _ => 1) := by
  have hcont : ContinuousAt (A () j₀) y := hA.self_of_nhds.continuousAt
  have hne' : ∀ᶠ x in 𝓝 y, A () j₀ x ≠ 0 := hcont.eventually_ne hne
  refine ⟨fun j x => if j = j₀ then (A () j₀ x)⁻¹ else 0, fun j => ?_, fun i => ?_⟩
  · by_cases hj : j = j₀
    · subst hj
      filter_upwards [hA.eventually_nhds, hne'.eventually_nhds] with x hx hx'
      simp only [if_true]
      exact (hx.self_of_nhds).inv hx'.self_of_nhds
    · simp only [hj, if_false]
      exact Eventually.of_forall fun x => differentiableAt_const _
  · filter_upwards [hne'] with x hx
    rcases i
    simp [matApply, hx]

/-! ### The slice `K × {θ ≤ |ζ| ≤ R₀}` -/

section Slice

variable (R R₀ θ : ℝ) (p : Fin q → Poly N)

/-- The graph functions `1/ζ` and `pⱼ(x)` on `ℂ^{N+1} ∋ (ζ, x)`. -/
def annGraph : Fin (q + 1) → ComplexModel (N + 1) → ℂ :=
  Fin.cons (fun y => (y 0)⁻¹) fun j y => polyEval (p j) (zpart y)

/-- The radii of the box: `R₀` for `ζ`, `R` for `x`, `θ⁻¹` for `1/ζ`, `1` for `pⱼ(x)`. -/
def annRadii : Fin ((N + 1) + (q + 1)) → ℝ :=
  Fin.append (Fin.cons R₀ fun _ => R) (Fin.cons θ⁻¹ fun _ => 1)

/-- The box of the slice. -/
def annBox : Fin ((N + 1) + (q + 1)) → Set ℂ := fun l => closedBall 0 (annRadii (N := N) R R₀ θ l)

/-- The domain `{ζ ≠ 0}` of the graph functions. -/
def annDom : Set (ComplexModel (N + 1)) := {y | y 0 ≠ 0}

theorem isBox_annBox : Box.IsBox (annBox (N := N) (q := q) R R₀ θ) :=
  ⟨fun _ => isCompact_closedBall _ _, fun _ => convex_closedBall _ _⟩

theorem isOpen_annDom : IsOpen (annDom (N := N)) :=
  isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (N + 1))).continuous continuous_const

theorem differentiableOn_annGraph (j : Fin (q + 1)) :
    DifferentiableOn ℂ (annGraph (N := N) p j) annDom := by
  refine Fin.cases ?_ (fun j => ?_) j
  · intro y hy
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (N + 1))).differentiableAt.inv hy).differentiableWithinAt
  · exact ((differentiable_polyEval (p j)).comp differentiable_zpart).differentiableOn

theorem mem_annSlice {y : ComplexModel (N + 1)} (hθ : 0 < θ) :
    y ∈ Laurent.slice annDom (annGraph p) (annBox R R₀ θ) ↔
      zpart y ∈ pbox R p ∧ θ ≤ ‖y 0‖ ∧ ‖y 0‖ ≤ R₀ := by
  simp only [Laurent.slice, mem_inter_iff, mem_preimage, Box.mem_boxSet, annBox, annDom,
    mem_setOf_eq]
  rw [Fin.forall_fin_add, Fin.forall_fin_succ, Fin.forall_fin_succ]
  simp only [Graph.graphMap_castAdd, Graph.graphMap_natAdd, annRadii, Fin.append_left,
    Fin.append_right, Fin.cons_zero, Fin.cons_succ, annGraph, mem_closedBall_zero_iff, pbox,
    zpart_apply, mem_setOf_eq, norm_inv]
  constructor
  · rintro ⟨hy0, ⟨hR₀, hR⟩, hθ', hp⟩
    refine ⟨⟨hR, hp⟩, ?_, hR₀⟩
    have hpos : 0 < ‖y 0‖ := norm_pos_iff.mpr hy0
    rwa [inv_le_inv₀ hpos hθ] at hθ'
  · rintro ⟨⟨hR, hp⟩, hθ', hR₀⟩
    have hpos : 0 < ‖y 0‖ := hθ.trans_le hθ'
    refine ⟨norm_pos_iff.mp hpos, ⟨hR₀, hR⟩, ?_, hp⟩
    rwa [inv_le_inv₀ hpos hθ]

theorem isClosed_annGraph :
    IsClosed (Graph.graphMap (annGraph (N := N) p) '' annDom) := by
  have hset : Graph.graphMap (annGraph (N := N) p) '' annDom =
      {v : EuclideanSpace ℂ (Fin ((N + 1) + (q + 1))) |
        v (Fin.castAdd (q + 1) 0) * v (Fin.natAdd (N + 1) 0) = 1} ∩
          ⋂ j : Fin q, {v | v (Fin.natAdd (N + 1) j.succ) = polyEval (p j) (zpart (Graph.proj v))} := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, mem_iInter.mpr fun j => ?_⟩
      · simp only [mem_setOf_eq, Graph.graphMap_castAdd, Graph.graphMap_natAdd, annGraph,
          Fin.cons_zero]
        exact mul_inv_cancel₀ hy
      · simp [annGraph]
    · rintro ⟨h0, hj⟩
      have hj : ∀ j : Fin q, v (Fin.natAdd (N + 1) j.succ) = polyEval (p j) (zpart (Graph.proj v)) :=
        fun j => mem_iInter.mp hj j
      have h0 : v (Fin.castAdd (q + 1) 0) * v (Fin.natAdd (N + 1) 0) = 1 := h0
      refine ⟨Graph.proj v, ?_, ?_⟩
      · show Graph.proj v 0 ≠ 0
        rw [Graph.proj_apply]
        exact left_ne_zero_of_mul_eq_one h0
      · ext l
        refine Fin.addCases (fun i => ?_) (fun j => ?_) l
        · simp
        · rw [Graph.graphMap_natAdd]
          refine Fin.cases ?_ (fun j => ?_) j
          · simp only [annGraph, Fin.cons_zero, Graph.proj_apply]
            exact (eq_inv_of_mul_eq_one_right h0).symm
          · simp only [annGraph, Fin.cons_succ]
            exact (hj j).symm
  rw [hset]
  have hc0 : Continuous fun v : EuclideanSpace ℂ (Fin ((N + 1) + (q + 1))) =>
      v (Fin.castAdd (q + 1) 0) * v (Fin.natAdd (N + 1) 0) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) _).continuous).mul (EuclideanSpace.proj (𝕜 := ℂ) _).continuous
  have hproj : Continuous (Graph.proj (N := N + 1) (m := q + 1)) := Graph.continuous_proj
  refine (isClosed_eq hc0 continuous_const).inter (isClosed_iInter fun j => ?_)
  exact isClosed_eq (EuclideanSpace.proj (𝕜 := ℂ) _).continuous
    ((continuous_polyEval _).comp (continuous_zpart.comp hproj))

end Slice

/-! ### The decomposition `1 = a₀ (ζ - g) + ∑ aₗ hₗ` -/

/-- **Theorem B on the slice.** Near `K × {θ ≤ |ζ| ≤ R₀}` the constant `1` is
`a₀(x, ζ) (ζ - g(x)) + ∑ₗ aₗ(x, ζ) hₗ(x)` with `aᵢ` holomorphic. -/
theorem exists_decompose_one {O : Set (ComplexModel N)} (hO : IsOpen O)
    {h : Fin r → ComplexModel N → ℂ} (hh : ∀ l, DifferentiableOn ℂ (h l) O)
    {g : ComplexModel N → ℂ} (hg : DifferentiableOn ℂ g O)
    {R : ℝ} {p : Fin q → Poly N} (hKO : pbox R p ⊆ O)
    {θ R₀ : ℝ} (hθ : 0 < θ) (hY : ∀ x ∈ pbox R p, (∀ l, h l x = 0) → ‖g x‖ < θ) :
    ∃ V : Set (ComplexModel (N + 1)), IsOpen V ∧
      Laurent.slice annDom (annGraph p) (annBox R R₀ θ) ⊆ V ∧
      ∃ (a₀ : ComplexModel (N + 1) → ℂ) (a : Fin r → ComplexModel (N + 1) → ℂ),
        DifferentiableOn ℂ a₀ V ∧ (∀ l, DifferentiableOn ℂ (a l) V) ∧
        ∀ z ∈ V, (z 0 - g (zpart z)) * a₀ z + ∑ l, h l (zpart z) * a l z = 1 := by
  classical
  set W : Set (ComplexModel (N + 1)) := zpart ⁻¹' O with hWdef
  have hW : IsOpen W := hO.preimage continuous_zpart
  set A : Unit → Fin (r + 1) → ComplexModel (N + 1) → ℂ := fun _ =>
    Fin.cons (fun y => y 0 - g (zpart y)) fun l y => h l (zpart y) with hAdef
  have hdz : ∀ {f : ComplexModel N → ℂ}, DifferentiableOn ℂ f O →
      DifferentiableOn ℂ (fun y : ComplexModel (N + 1) => f (zpart y)) W :=
    fun hf => hf.comp differentiable_zpart.differentiableOn fun _ hy => hy
  have hA : ∀ i j, DifferentiableOn ℂ (A i j) W := by
    intro i j
    refine Fin.cases ?_ (fun l => ?_) j
    · exact ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (N + 1))).differentiable.differentiableOn).sub
        (hdz hg)
    · exact hdz (hh l)
  set V₀ : Set (ComplexModel (N + 1)) := ⋃ j, W ∩ A () j ⁻¹' {0}ᶜ with hV₀def
  have hV₀ : IsOpen V₀ :=
    isOpen_iUnion fun j => (hA () j).continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hKW : Laurent.slice annDom (annGraph p) (annBox R R₀ θ) ⊆ W := by
    intro y hy
    exact hKO ((mem_annSlice R R₀ θ p hθ).mp hy).1
  have hKV₀ : Laurent.slice annDom (annGraph p) (annBox R R₀ θ) ⊆ V₀ := by
    intro y hy
    have hy' := (mem_annSlice R R₀ θ p hθ).mp hy
    by_cases hz : ∀ l, h l (zpart y) = 0
    · refine mem_iUnion.mpr ⟨0, hKW hy, ?_⟩
      have hlt := hY _ hy'.1 hz
      simp only [hAdef, mem_preimage, mem_compl_iff, mem_singleton_iff, Fin.cons_zero]
      intro h0
      rw [sub_eq_zero] at h0
      rw [← h0] at hlt
      linarith [hy'.2.1]
    · push Not at hz
      obtain ⟨l, hl⟩ := hz
      refine mem_iUnion.mpr ⟨l.succ, hKW hy, ?_⟩
      simpa [hAdef] using hl
  have hb : ∀ y ∈ V₀, ((GermModule.bot (ComplexModel (N + 1)) Unit).sup
      ((GermModule.top (ComplexModel (N + 1)) (Fin (r + 1))).map A)).mem y (fun _ _ => 1) := by
    intro y hy
    obtain ⟨j, hyW, hyj⟩ := mem_iUnion.mp hy
    have hhol : HolAt (A () j) y := by
      filter_upwards [hW.mem_nhds hyW] with x hx
      exact (hA () j).differentiableAt (hW.mem_nhds hx)
    refine ⟨fun _ _ => 0, fun _ _ => 1, fun _ => EventuallyEq.rfl,
      map_top_mem_one j hhol hyj, fun _ => Eventually.of_forall fun _ => by simp⟩
  obtain ⟨V, hV, hKV, pp, aa, -, haa, hppm, -, hdec⟩ :=
    Laurent.exists_decompose_slice (isBox_annBox R R₀ θ) isOpen_annDom
      (differentiableOn_annGraph p) (isClosed_annGraph p)
      (P := GermModule.bot (ComplexModel (N + 1)) Unit)
      (Q := GermModule.top (ComplexModel (N + 1)) (Fin (r + 1))) hW hKW
      (GermModule.bot_isCoherentOn W) (GermModule.top_isCoherentOn W) hA hV₀ hKV₀ hb
  refine ⟨V, hV, hKV, aa 0, fun l => aa l.succ, haa 0, fun l => haa l.succ, fun z hz => ?_⟩
  have h1 := hdec z hz ()
  have hp0 : pp () z = 0 := (hppm z hz ()).eq_of_nhds
  rw [hp0, zero_add, matApply_apply, Fin.sum_univ_succ] at h1
  simpa [hAdef] using h1.symm

/-! ### The estimate -/

/-- **Extension with estimates** (resolvent trick). Let `hₗ` and `g` be holomorphic on an open
`O ⊇ K = pbox R p` and `|g| < θ` on `K ∩ {h = 0}`. Then there are an open `U ⊇ K`, a constant
`C` and, for every `m`, functions `Q_{m,l}` holomorphic on `U` with
`‖g^m - ∑ₗ hₗ Q_{m,l}‖ ≤ C θ^m` on `K`. -/
theorem exists_extension_estimate {O : Set (ComplexModel N)} (hO : IsOpen O)
    {h : Fin r → ComplexModel N → ℂ} (hh : ∀ l, DifferentiableOn ℂ (h l) O)
    {g : ComplexModel N → ℂ} (hg : DifferentiableOn ℂ g O)
    {R : ℝ} {p : Fin q → Poly N} (hKO : pbox R p ⊆ O)
    {θ : ℝ} (hθ : 0 < θ) (hY : ∀ x ∈ pbox R p, (∀ l, h l x = 0) → ‖g x‖ < θ) :
    ∃ U : Set (ComplexModel N), IsOpen U ∧ pbox R p ⊆ U ∧ ∃ C : ℝ, ∀ m : ℕ,
      ∃ Q : Fin r → ComplexModel N → ℂ, (∀ l, DifferentiableOn ℂ (Q l) U) ∧
        ∀ x ∈ pbox R p, ‖g x ^ m - ∑ l, h l x * Q l x‖ ≤ C * θ ^ m := by
  classical
  set K := pbox R p with hKdef
  have hK : IsCompact K := isCompact_pbox R p
  -- the outer radius
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKO).norm
  set R₀ : ℝ := max (M + 1) (θ + 1) with hR₀def
  have hθR₀ : θ < R₀ := by rw [hR₀def]; linarith [le_max_right (M + 1) (θ + 1)]
  have hR₀ : 0 < R₀ := hθ.trans hθR₀
  have hgR₀ : ∀ x ∈ K, ‖g x‖ < R₀ := by
    intro x hx
    have := hM x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)] at this
    rw [hR₀def]; linarith [le_max_left (M + 1) (θ + 1)]
  obtain ⟨V, hV, hKV, a₀, a, ha₀, ha, hdec⟩ :=
    exists_decompose_one (R₀ := R₀) hO hh hg hKO hθ hY
  -- the tube `u × v`
  set Ann : Set ℂ := closedBall 0 R₀ \ ball 0 θ with hAnndef
  have hAnn : IsCompact Ann := (isCompact_closedBall 0 R₀).diff isOpen_ball
  obtain ⟨u, v, hu, hv, hKu, hAv, huv⟩ := generalized_tube_lemma hK hAnn
    (hV.preimage continuous_mkPt) (by
      rintro ⟨x, ζ⟩ ⟨hx, hζ⟩
      apply hKV
      rw [mem_annSlice R R₀ θ p hθ]
      simp only [zpart_mkPt, mkPt_zero]
      refine ⟨hx, ?_, mem_closedBall_zero_iff.mp hζ.1⟩
      have := hζ.2
      rw [mem_ball_zero_iff, not_lt] at this
      exact this)
  have hmk : ∀ x ∈ u, ∀ ζ ∈ v, mkPt x ζ ∈ V := fun x hx ζ hζ => @huv (x, ζ) ⟨hx, hζ⟩
  have hsph : ∀ R' : ℝ, θ ≤ R' → R' ≤ R₀ → sphere (0 : ℂ) R' ⊆ v := by
    intro R' h1 h2 ζ hζ
    apply hAv
    rw [mem_sphere_zero_iff_norm] at hζ
    refine ⟨mem_closedBall_zero_iff.mpr (hζ.trans_le h2), ?_⟩
    rw [mem_ball_zero_iff, not_lt, hζ]
    exact h1
  -- the open set `U`
  set U : Set (ComplexModel N) := u ∩ (O ∩ g ⁻¹' ball 0 R₀) with hUdef
  have hU : IsOpen U := hu.inter (hg.continuousOn.isOpen_inter_preimage hO isOpen_ball)
  have hKU : K ⊆ U := fun x hx => ⟨hKu hx, hKO hx, mem_ball_zero_iff.mpr (hgR₀ x hx)⟩
  -- differentiability of the coefficients along the tube
  have hda : ∀ {f : ComplexModel (N + 1) → ℂ}, DifferentiableOn ℂ f V →
      ∀ x ∈ u, ∀ ζ ∈ v, DifferentiableAt ℂ (fun t : ℂ => f (mkPt x t)) ζ := by
    intro f hf x hx ζ hζ
    have h1 : DifferentiableAt ℂ f (mkPt x ζ) := hf.differentiableAt (hV.mem_nhds (hmk x hx ζ hζ))
    have h2 : DifferentiableAt ℂ (fun t : ℂ => mkPt x t) ζ :=
      (differentiable_mkPt (n := N)).differentiableAt.comp ζ
        ((differentiableAt_const x).prodMk differentiableAt_id)
    exact h1.comp ζ h2
  have hid : ∀ x ∈ U, ∀ ζ ∈ v, (ζ - g x) * a₀ (mkPt x ζ) + ∑ l, h l x * a l (mkPt x ζ) = 1 := by
    intro x hx ζ hζ
    simpa using hdec (mkPt x ζ) (hmk x hx.1 ζ hζ)
  -- a bound for `a₀` on `K × sphere θ`
  have hcont0 : ContinuousOn (fun pt : ComplexModel N × ℂ => a₀ (mkPt pt.1 pt.2))
      (K ×ˢ sphere (0 : ℂ) θ) := by
    refine ha₀.continuousOn.comp continuous_mkPt.continuousOn ?_
    rintro ⟨x, ζ⟩ ⟨hx, hζ⟩
    exact hmk x (hKu hx) ζ (hsph θ le_rfl hθR₀.le hζ)
  obtain ⟨C₀, hC₀⟩ := (hK.prod (isCompact_sphere (0 : ℂ) θ)).exists_bound_of_continuousOn hcont0
  set C₁ : ℝ := max C₀ 0
  refine ⟨U, hU, hKU, θ * C₁, fun m => ?_⟩
  set Q : Fin r → ComplexModel N → ℂ := fun l x =>
    (2 * π * I)⁻¹ * ∮ ζ in C(0, R₀), ζ ^ m * a l (mkPt x ζ) / (ζ - g x) with hQdef
  refine ⟨Q, ?_, ?_⟩
  · -- holomorphy of `Q` (holomorphic dependence of circle integrals on parameters)
    intro l x₀ hx₀
    set O' : Set (ComplexModel N × ℂ) :=
      (U ×ˢ v) ∩ (fun pt : ComplexModel N × ℂ => pt.2 - g pt.1) ⁻¹' {0}ᶜ with hO'def
    have hgU : DifferentiableOn ℂ g U := hg.mono fun x hx => hx.2.1
    have hO' : IsOpen O' := by
      refine ContinuousOn.isOpen_inter_preimage ?_ (hU.prod hv) isOpen_compl_singleton
      exact (continuous_snd.continuousOn).sub (hgU.continuousOn.comp continuous_fst.continuousOn
        fun pt hpt => hpt.1)
    have hΨ : DifferentiableOn ℂ
        (fun pt : ComplexModel N × ℂ => pt.2 ^ m * a l (mkPt pt.1 pt.2) / (pt.2 - g pt.1)) O' := by
      intro pt hpt
      have hpU : pt.1 ∈ U := hpt.1.1
      have hpv : pt.2 ∈ v := hpt.1.2
      have hne : pt.2 - g pt.1 ≠ 0 := hpt.2
      have hgd : DifferentiableAt ℂ (fun pt : ComplexModel N × ℂ => g pt.1) pt :=
        (hg.differentiableAt (hO.mem_nhds hpU.2.1)).comp pt differentiableAt_fst
      have had : DifferentiableAt ℂ (fun pt : ComplexModel N × ℂ => a l (mkPt pt.1 pt.2)) pt :=
        ((ha l).differentiableAt (hV.mem_nhds (hmk _ hpU.1 _ hpv))).comp pt
          (differentiable_mkPt (n := N)).differentiableAt
      have hnum : DifferentiableAt ℂ
          (fun pt : ComplexModel N × ℂ => pt.2 ^ m * a l (mkPt pt.1 pt.2)) pt :=
        (differentiableAt_snd.pow m).mul had
      have hden : DifferentiableAt ℂ (fun pt : ComplexModel N × ℂ => pt.2 - g pt.1) pt :=
        differentiableAt_snd.sub hgd
      have h3 := hnum.mul (hden.inv hne)
      simp only [← div_eq_mul_inv] at h3
      exact h3.differentiableWithinAt
    have hp₀ : ∀ τ ∈ sphere (0 : ℂ) R₀, (x₀, τ) ∈ O' := by
      intro τ hτ
      refine ⟨⟨hx₀, hsph R₀ hθR₀.le le_rfl hτ⟩, ?_⟩
      simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
      intro h0
      rw [sub_eq_zero] at h0
      have h1 : ‖g x₀‖ < R₀ := mem_ball_zero_iff.mp hx₀.2.2
      rw [mem_sphere_zero_iff_norm] at hτ
      rw [← h0, hτ] at h1
      exact lt_irrefl _ h1
    have hdiff := SGPT.Foundations.Analysis.Pending.RiemannExtension.differentiableAt_circleIntegral_param
      (c := 0) hO' hΨ hR₀.le hp₀
    exact (hdiff.const_mul ((2 * π * I)⁻¹)).differentiableWithinAt
  · -- the estimate
    intro x hx
    have hxU := hKU hx
    have hgx : ‖g x‖ < R₀ := hgR₀ x hx
    set f : ℂ → ℂ := fun ζ => ζ ^ m * a₀ (mkPt x ζ) with hfdef
    have hfd : ∀ ζ ∈ v, DifferentiableAt ℂ f ζ := fun ζ hζ =>
      (differentiableAt_id.pow m).mul (hda ha₀ x hxU.1 ζ hζ)
    -- Cauchy on the annulus
    have hann : (∮ ζ in C(0, R₀), f ζ) = ∮ ζ in C(0, θ), f ζ :=
      circleIntegral_eq_of_differentiable_on_annulus_off_countable hθ hθR₀.le countable_empty
        (fun ζ hζ => (hfd ζ (hAv hζ)).continuousAt.continuousWithinAt)
        (fun ζ hζ => hfd ζ (hAv ⟨ball_subset_closedBall hζ.1.1,
          fun h' => hζ.1.2 (ball_subset_closedBall h')⟩))
    -- the integrand on the outer circle
    have hne : ∀ ζ ∈ sphere (0 : ℂ) R₀, ζ - g x ≠ 0 := by
      intro ζ hζ h0
      rw [sub_eq_zero] at h0
      rw [mem_sphere_zero_iff_norm] at hζ
      rw [← h0, hζ] at hgx
      exact lt_irrefl _ hgx
    have hcongr : EqOn f (fun ζ => (ζ - g x)⁻¹ • ζ ^ m -
        ∑ l, h l x * (ζ ^ m * a l (mkPt x ζ) / (ζ - g x))) (sphere (0 : ℂ) R₀) := by
      intro ζ hζ
      have h1 := hid x hxU ζ (hsph R₀ hθR₀.le le_rfl hζ)
      have h2 := hne ζ hζ
      have hsum : ∑ l, h l x * (ζ ^ m * a l (mkPt x ζ) / (ζ - g x)) =
          ζ ^ m / (ζ - g x) * ∑ l, h l x * a l (mkPt x ζ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        field_simp
      simp only [hfdef, smul_eq_mul]
      rw [hsum]
      field_simp
      linear_combination ζ ^ m * h1
    have hcontS : ∀ {F : ℂ → ℂ}, (∀ ζ ∈ v, DifferentiableAt ℂ F ζ) →
        CircleIntegrable (fun ζ => F ζ / (ζ - g x)) 0 R₀ := by
      intro F hF
      refine ContinuousOn.circleIntegrable hR₀.le fun ζ hζ => ?_
      exact ((hF ζ (hsph R₀ hθR₀.le le_rfl hζ)).continuousAt.div
        (continuousAt_id.sub continuousAt_const) (hne ζ hζ)).continuousWithinAt
    have hint1 : CircleIntegrable (fun ζ => (ζ - g x)⁻¹ • ζ ^ m) 0 R₀ := by
      refine ContinuousOn.circleIntegrable hR₀.le fun ζ hζ => ?_
      exact (((continuousAt_id.sub continuousAt_const).inv₀ (hne ζ hζ)).smul
        (continuousAt_id.pow m)).continuousWithinAt
    have hint2 : ∀ l ∈ (Finset.univ : Finset (Fin r)),
        CircleIntegrable (fun ζ => h l x * (ζ ^ m * a l (mkPt x ζ) / (ζ - g x))) 0 R₀ := by
      intro l _
      have := hcontS (F := fun ζ => ζ ^ m * a l (mkPt x ζ))
        (fun ζ hζ => (differentiableAt_id.pow m).mul (hda (ha l) x hxU.1 ζ hζ))
      exact this.const_mul (h l x)
    have hint3 : CircleIntegrable
        (fun ζ => ∑ l, h l x * (ζ ^ m * a l (mkPt x ζ) / (ζ - g x))) 0 R₀ := by
      have := CircleIntegrable.sum _ hint2
      convert this using 1
      funext ζ
      simp [Finset.sum_apply]
    have hcauchy : (2 * π * I)⁻¹ • (∮ ζ in C(0, R₀), (ζ - g x)⁻¹ • ζ ^ m) = g x ^ m :=
      DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
        ((differentiable_id.pow m).diffContOnCl) (mem_ball_zero_iff.mpr hgx)
    have hmain : (2 * π * I)⁻¹ * (∮ ζ in C(0, θ), f ζ) = g x ^ m - ∑ l, h l x * Q l x := by
      rw [← hann, circleIntegral.integral_congr hR₀.le hcongr,
        circleIntegral.integral_sub hint1 hint3,
        circleIntegral.integral_fun_sum hint2, mul_sub, ← smul_eq_mul, hcauchy]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [circleIntegral.integral_const_mul, hQdef]
      ring
    rw [← hmain]
    have hbound : ∀ ζ ∈ sphere (0 : ℂ) θ, ‖f ζ‖ ≤ θ ^ m * C₁ := by
      intro ζ hζ
      have hζn : ‖ζ‖ = θ := mem_sphere_zero_iff_norm.mp hζ
      have h1 : ‖a₀ (mkPt x ζ)‖ ≤ C₁ :=
        (hC₀ (x, ζ) ⟨hx, hζ⟩).trans (le_max_left _ _)
      simp only [hfdef, norm_mul, norm_pow, hζn]
      exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hθ.le m)
    have hI := circleIntegral.norm_integral_le_of_norm_le_const hθ.le hbound
    rw [norm_mul, norm_inv]
    have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    rw [h2pi]
    have hpos : 0 < 2 * π := by positivity
    calc (2 * π)⁻¹ * ‖∮ ζ in C(0, θ), f ζ‖ ≤ (2 * π)⁻¹ * (2 * π * θ * (θ ^ m * C₁)) :=
          mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hpos.le)
      _ = θ * C₁ * θ ^ m := by field_simp

end SGPT.Unibranch.FNS
