import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic

/-!
# Schwartz's theorem on compact perturbations of surjections (Banach form)

Infrastructure of lane SERRE-PN (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145): the functional-analytic input of the
Cartan--Serre finiteness theorem `dim H¹(ℙᴺ, 𝓕) < ∞`.

Let `E`, `F` be Banach spaces over `ℝ` or `ℂ`, `u : E → F` a continuous linear surjection and
`v : E → F` a compact operator. Then `u + v` has closed range of finite codimension
(L. Schwartz, *Homomorphismes et applications complètement continues*, 1953; Cartan--Serre
1953). Mathlib has compact operators, the open mapping theorem and the first steps of the
theory of Fredholm operators, but not this theorem.

The proof avoids duality. By the open mapping theorem every `y` has a preimage `x` under `u`
with `‖x‖ ≤ C ‖y‖`. By compactness, `v` maps the unit ball into the `ε`-neighbourhood of a
finite-dimensional subspace `G` (`exists_finiteDimensional_approx`). With `ε = 1/(2C)`, every
`y` is `(u + v) x + g` up to an error of norm `≤ ‖y‖/2`, with `x` and `g ∈ G` bounded by a
multiple of `‖y‖`. The iteration of the open mapping theorem
(`surjective_of_approx_preimage`) makes `(x, g) ↦ (u + v) x + g` surjective on `E × G`, so
`range (u + v) + G = F` (`exists_finiteDimensional_range_sup_eq_top`). A range of finite
codimension is closed (`isClosed_range_of_finiteDimensional_quotient`).

`finiteDimensional_quotient_range_of_compact` is the form used for finiteness of cohomology:
if `r : Z' → Z` is compact, `δ : C → Z` is continuous and `r(Z') + δ(C) = Z`, then `Z/δ(C)` is
finite-dimensional.

Blueprint: `claude-serre-pn.tex`, node `claude-serre-pn:schwartz`.
-/

set_option autoImplicit false

open Filter Topology Metric Function

namespace SGPT.GAGA.PN

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Iteration step of the open mapping theorem.** A continuous linear map `f : E → F` from
a Banach space such that every `y` is the image of some `x` with `‖x‖ ≤ C ‖y‖` up to an
error of norm at most `‖y‖/2` is surjective. -/
theorem surjective_of_approx_preimage [CompleteSpace E] (f : E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y, ∃ x, ‖y - f x‖ ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) : Surjective f := by
  intro y
  choose g hg using h
  let hh : F → F := fun z => z - f (g z)
  have hle : ∀ z, ‖hh z‖ ≤ 1 / 2 * ‖z‖ := fun z => (hg z).1
  have hnle : ∀ n : ℕ, ‖hh^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let w : ℕ → E := fun n => g (hh^[n] y)
  have wle : ∀ n, ‖w n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n => by
    apply le_trans (hg _).2
    calc C * ‖hh^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNw : Summable fun n => ‖w n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) wle ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have sw : Summable w := sNw.of_norm
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, w i) = y - hh^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH => rw [Finset.sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, w i)) atTop (𝓝 (f (tsum w))) :=
    (f.continuous.tendsto _).comp sw.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - hh^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f (tsum w) = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨tsum w, feq⟩

/-- **A compact operator is uniformly close to a finite-dimensional subspace.** For a compact
operator `v : E → F` and `ε > 0` there is a finite-dimensional subspace `G ⊆ F` such that
every `v x` is within `ε ‖x‖` of `G`. -/
theorem exists_finiteDimensional_approx {v : E →L[𝕜] F} (hv : IsCompactOperator v) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ G : Submodule 𝕜 F, FiniteDimensional 𝕜 G ∧ ∀ x, ∃ g ∈ G, ‖v x - g‖ ≤ ε * ‖x‖ := by
  have hK : IsCompact (closure (v '' closedBall 0 1)) :=
    hv.isCompact_closure_image_closedBall 1
  obtain ⟨t, -, htfin, htcov⟩ := hK.finite_cover_balls hε
  refine ⟨Submodule.span 𝕜 t, FiniteDimensional.span_of_finite 𝕜 htfin, fun x => ?_⟩
  by_cases hx : x = 0
  · exact ⟨0, Submodule.zero_mem _, by simp [hx]⟩
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  set x' : E := ((‖x‖ : 𝕜)⁻¹) • x with hx'
  have hx'1 : x' ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, hx', norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
      inv_mul_cancel₀ hnx]
  have hmem : v x' ∈ closure (v '' closedBall 0 1) := subset_closure ⟨x', hx'1, rfl⟩
  obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (htcov hmem)
  refine ⟨(‖x‖ : 𝕜) • c, Submodule.smul_mem _ _ (Submodule.subset_span hct), ?_⟩
  have hxx : (‖x‖ : 𝕜) • x' = x := by
    rw [hx', smul_smul, mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 hnx), one_smul]
  have hvx : v x = (‖x‖ : 𝕜) • v x' := by rw [← map_smul, hxx]
  calc ‖v x - (‖x‖ : 𝕜) • c‖ = ‖(‖x‖ : 𝕜) • (v x' - c)‖ := by rw [smul_sub, ← hvx]
    _ = ‖x‖ * ‖v x' - c‖ := by rw [norm_smul, RCLike.norm_ofReal, abs_norm]
    _ ≤ ‖x‖ * ε := by
        gcongr
        rw [← dist_eq_norm]
        exact (mem_ball.1 hc).le
    _ = ε * ‖x‖ := mul_comm _ _

variable [CompleteSpace E] [CompleteSpace F]

/-- **Schwartz's theorem, algebraic form.** If `u : E → F` is a continuous linear surjection
of Banach spaces and `v : E → F` is compact, then the range of `u + v` together with some
finite-dimensional subspace spans `F`. -/
theorem exists_finiteDimensional_range_sup_eq_top {u v : E →L[𝕜] F} (hu : Surjective u)
    (hv : IsCompactOperator v) :
    ∃ G : Submodule 𝕜 F, FiniteDimensional 𝕜 G ∧
      LinearMap.range (u + v : E →L[𝕜] F).toLinearMap ⊔ G = ⊤ := by
  obtain ⟨C, hC, hpre⟩ := u.exists_preimage_norm_le hu
  obtain ⟨G, hG, happ⟩ := exists_finiteDimensional_approx hv (ε := 1 / (2 * C)) (by positivity)
  have : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  let S : (E × G) →L[𝕜] F := (u + v).coprod G.subtypeL
  have hSapp : ∀ (x : E) (g : G), S (x, g) = u x + v x + (g : F) := fun x g => by
    simp [S]
  have hS : Surjective S := by
    refine surjective_of_approx_preimage S (C := C + (‖v‖ * C + 1)) (by positivity) fun y => ?_
    obtain ⟨x, hx, hxn⟩ := hpre y
    obtain ⟨g, hg, hgn⟩ := happ x
    have h1 : ‖v x - g‖ ≤ 1 / 2 * ‖y‖ := by
      calc ‖v x - g‖ ≤ 1 / (2 * C) * ‖x‖ := hgn
        _ ≤ 1 / (2 * C) * (C * ‖y‖) := by gcongr
        _ = 1 / 2 * ‖y‖ := by field_simp
    have hg' : ‖g‖ ≤ (‖v‖ * C + 1) * ‖y‖ := by
      calc ‖g‖ = ‖v x - (v x - g)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖v x‖ + ‖v x - g‖ := norm_sub_le _ _
        _ ≤ ‖v‖ * (C * ‖y‖) + 1 / 2 * ‖y‖ := by
            gcongr
            exact (v.le_opNorm x).trans (by gcongr)
        _ ≤ (‖v‖ * C + 1) * ‖y‖ := by nlinarith [norm_nonneg y]
    refine ⟨(x, -⟨g, hg⟩), ?_, ?_⟩
    · have : y - S (x, -⟨g, hg⟩) = -(v x - g) := by
        rw [hSapp, ← hx]
        simp only [Submodule.coe_neg]
        abel
      rw [this, norm_neg]
      exact h1
    · rw [Prod.norm_def]
      refine max_le ?_ ?_
      · calc ‖x‖ ≤ C * ‖y‖ := hxn
          _ ≤ (C + (‖v‖ * C + 1)) * ‖y‖ := by
            nlinarith [norm_nonneg y, norm_nonneg v, mul_nonneg (norm_nonneg v) hC.le]
      · rw [norm_neg, Submodule.coe_norm]
        calc ‖g‖ ≤ (‖v‖ * C + 1) * ‖y‖ := hg'
          _ ≤ (C + (‖v‖ * C + 1)) * ‖y‖ := by nlinarith [norm_nonneg y]
  refine ⟨G, hG, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨⟨x, g⟩, hxg⟩ := hS y
  rw [← hxg, hSapp]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ g.2

/-- **Schwartz's theorem: finite codimension.** If `u : E → F` is a continuous linear
surjection of Banach spaces and `v : E → F` is compact, then the cokernel of `u + v` is
finite-dimensional. -/
theorem finiteDimensional_quotient_range_add {u v : E →L[𝕜] F} (hu : Surjective u)
    (hv : IsCompactOperator v) :
    FiniteDimensional 𝕜 (F ⧸ LinearMap.range (u + v : E →L[𝕜] F).toLinearMap) := by
  obtain ⟨G, hG, hsup⟩ := exists_finiteDimensional_range_sup_eq_top hu hv
  set R := LinearMap.range (u + v : E →L[𝕜] F).toLinearMap
  have hsurj : Surjective (R.mkQ.comp G.subtype) := by
    intro q
    obtain ⟨y, rfl⟩ := R.mkQ_surjective q
    have hy : y ∈ R ⊔ G := hsup ▸ Submodule.mem_top
    obtain ⟨r, hr, g, hg, rfl⟩ := Submodule.mem_sup.1 hy
    refine ⟨⟨g, hg⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_add]
    rw [(Submodule.Quotient.mk_eq_zero R).2 hr, zero_add]
  exact Module.Finite.of_surjective _ hsurj

/-- **A range of finite codimension is closed.** A continuous linear map between Banach
spaces whose cokernel is finite-dimensional has closed range. -/
theorem isClosed_range_of_finiteDimensional_quotient (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (F ⧸ LinearMap.range T.toLinearMap)] :
    IsClosed (LinearMap.range T.toLinearMap : Set F) := by
  set R := LinearMap.range T.toLinearMap
  obtain ⟨G, hG⟩ := Submodule.exists_isCompl R
  have hGfd : FiniteDimensional 𝕜 G :=
    (Submodule.quotientEquivOfIsCompl R G hG).finiteDimensional
  have : CompleteSpace G := FiniteDimensional.complete 𝕜 G
  let S : (E × G) →L[𝕜] F := T.coprod G.subtypeL
  have hSapp : ∀ (x : E) (g : G), S (x, g) = T x + (g : F) := fun x g => by simp [S]
  have hS : Surjective S := by
    intro y
    have hy : y ∈ R ⊔ G := hG.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨r, ⟨x, rfl⟩, g, hg, rfl⟩ := Submodule.mem_sup.1 hy
    exact ⟨(x, ⟨g, hg⟩), hSapp x ⟨g, hg⟩⟩
  have hopen : IsOpen (S '' {p : E × G | p.2 ≠ 0}) :=
    S.isOpenMap hS _ (isOpen_ne_fun continuous_snd continuous_const)
  have hcompl : (R : Set F)ᶜ = S '' {p : E × G | p.2 ≠ 0} := by
    ext y
    constructor
    · intro hy
      obtain ⟨⟨x, g⟩, rfl⟩ := hS y
      refine ⟨(x, g), ?_, rfl⟩
      intro hg0
      have hg0' : g = 0 := hg0
      have hSx : S (x, g) = T x := by rw [hSapp, hg0']; simp
      exact hy (hSx ▸ ⟨x, rfl⟩)
    · rintro ⟨⟨x, g⟩, hg, rfl⟩ hmem
      have hgR : (g : F) ∈ R := by
        have h2 : (g : F) = S (x, g) - T x := by rw [hSapp]; abel
        rw [h2]
        exact R.sub_mem hmem ⟨x, rfl⟩
      have : (g : F) ∈ R ⊓ G := ⟨hgR, g.2⟩
      rw [hG.inf_eq_bot, Submodule.mem_bot] at this
      exact hg (Subtype.ext this)
  exact isOpen_compl_iff.1 (hcompl ▸ hopen)

/-- **Schwartz's theorem: closed range.** If `u : E → F` is a continuous linear surjection of
Banach spaces and `v : E → F` is compact, then the range of `u + v` is closed. -/
theorem isClosed_range_add {u v : E →L[𝕜] F} (hu : Surjective u) (hv : IsCompactOperator v) :
    IsClosed (LinearMap.range (u + v : E →L[𝕜] F).toLinearMap : Set F) := by
  have := finiteDimensional_quotient_range_add hu hv
  exact isClosed_range_of_finiteDimensional_quotient (u + v)

/-- **The finiteness lemma of Cartan and Serre.** Let `Z'`, `C`, `Z` be Banach spaces,
`r : Z' → Z` a compact operator and `δ : C → Z` a continuous linear map with
`r(Z') + δ(C) = Z`. Then `Z/δ(C)` is finite-dimensional. (For `Z', Z` the spaces of bounded
`1`-cocycles of a coherent sheaf on two covers, `r` the restriction and `δ` the coboundary,
this is the finiteness of `H¹`.) -/
theorem finiteDimensional_quotient_range_of_compact {Z' C : Type*} [NormedAddCommGroup Z']
    [NormedSpace 𝕜 Z'] [CompleteSpace Z'] [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    [CompleteSpace C] {r : Z' →L[𝕜] F} {δ : C →L[𝕜] F} (hr : IsCompactOperator r)
    (hsurj : LinearMap.range r.toLinearMap ⊔ LinearMap.range δ.toLinearMap = ⊤) :
    FiniteDimensional 𝕜 (F ⧸ LinearMap.range δ.toLinearMap) := by
  let u : (Z' × C) →L[𝕜] F := r.coprod δ
  let v : (Z' × C) →L[𝕜] F := -(r.comp (ContinuousLinearMap.fst 𝕜 Z' C))
  have hu : Surjective u := by
    intro y
    have hy : y ∈ LinearMap.range r.toLinearMap ⊔ LinearMap.range δ.toLinearMap :=
      hsurj ▸ Submodule.mem_top
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    exact ⟨(a, b), by simp [u]⟩
  have hv : IsCompactOperator v :=
    (hr.comp_clm (ContinuousLinearMap.fst 𝕜 Z' C)).neg
  have hrange : LinearMap.range (u + v : (Z' × C) →L[𝕜] F).toLinearMap =
      LinearMap.range δ.toLinearMap := by
    ext y
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨b, by simp [u, v]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(0, b), by simp [u, v]⟩
  have h := finiteDimensional_quotient_range_add hu hv
  rwa [hrange] at h

end SGPT.GAGA.PN
