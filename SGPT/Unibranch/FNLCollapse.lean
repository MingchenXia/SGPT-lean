import SGPT.Unibranch.FNLSheet

/-!
# FN80 Lemma 5.2: a plurisubharmonic function with poles exactly over the collapsed fibres

Source: `[FN80]` Lemma 5.2, proof: "Let `Y = {p ∈ X ; π⁻¹π(p) = p}`. Then `Y` is a complex
subvariety of `X`; let `f₁, …, f_m` be holomorphic functions on `X` such that
`Y = {f₁ = ⋯ = f_m = 0}`", used through the plurisubharmonic function `ε log ∑ |f_j|²`.

Instead of global defining functions of `Y` (which would need Theorems A/B) we use directly a
plurisubharmonic function on the base with poles exactly over the points whose fibre is a
single point: `collapse X π δ c` is the upper regularized extension across `{δ = 0}` of
`c · log V(z)`, `V(z) = ∑_{x, y ∈ π⁻¹(z)} ‖x - y‖²`; over `{δ ≠ 0}` it is locally
`c · log ∑ |h_j|²` with `h_j` holomorphic (differences of coordinates of the local sections).

* `IsBranchedCovering.plurisubharmonicOn_collapse`;
* `IsBranchedCovering.collapse_eq_bot`: `= -∞` at `π p` when `π⁻¹(π p) = {p}`;
* `IsBranchedCovering.le_collapse`: `≥ c log (‖p - q‖²/4)` when `p ≠ q` lie in one fibre;
* `IsBranchedCovering.collapse_le`: `≤ c log (λ² R² + 1)` when `X` has diameter `≤ R`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {n k : ℕ}
variable {X : Set (ComplexModel n)} {π : ComplexModel n →L[ℂ] ComplexModel k}
  {D : Set (ComplexModel k)} {deg : ℕ} {δ : ComplexModel k → ℂ}

/-- `V(z) = ∑_{x, y ∈ π⁻¹(z)} ‖x - y‖²`. -/
def fibreSpread (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (z : ComplexModel k) : ℝ :=
  ∑ᶠ x ∈ fibre X π z, ∑ᶠ y ∈ fibre X π z, ‖x - y‖ ^ 2

/-- The collapse function: the extension across `{δ = 0}` of `c · log V`. -/
def collapse (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (δ : ComplexModel k → ℂ) (c : ℝ) : ComplexModel k → EReal :=
  PshCodimTwoExtension.extension {w | δ w = 0}
    (fun z => (c : EReal) * ENNReal.log (ENNReal.ofReal (fibreSpread X π z)))

theorem fibreSpread_eq_sum {z : ComplexModel k} (hz : (fibre X π z).Finite) :
    fibreSpread X π z = ∑ x ∈ hz.toFinset, ∑ y ∈ hz.toFinset, ‖x - y‖ ^ 2 := by
  rw [fibreSpread, finsum_mem_eq_finite_toFinset_sum _ hz]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hz]

namespace IsBranchedCovering

variable (hX : IsBranchedCovering X π D deg δ)
include hX

/-- Over a generic neighbourhood, `c log V` is `c · log ∑ |h_j|²` with `h_j` holomorphic. -/
theorem plurisubharmonicOn_log_fibreSpread {c : ℝ} (hc : 0 < c) :
    PlurisubharmonicOn (fun z => (c : EReal) * ENNReal.log (ENNReal.ofReal (fibreSpread X π z)))
      (D \ {w | δ w = 0}) := by
  classical
  intro z₁ hz₁
  have hδ : δ z₁ ≠ 0 := hz₁.2
  obtain ⟨W, hWo, hz₁W, hWD, -, g, -, hgd, hbij⟩ := hX.exists_local_sections hz₁.1 hδ
  have hS := hX.finite_fibre z₁ hz₁.1
  set S := hS.toFinset with hSdef
  set ι := ↥S × ↥S × Fin n
  set N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι
  let G : Fin N → ComplexModel k → ℂ := fun j w =>
    (g (e.symm j).1.val w - g (e.symm j).2.1.val w) (e.symm j).2.2
  have hGd : ∀ j, DifferentiableOn ℂ (G j) W := by
    intro j
    have h1 := hgd _ ((hS.mem_toFinset).mp (e.symm j).1.property)
    have h2 := hgd _ ((hS.mem_toFinset).mp (e.symm j).2.1.property)
    exact (EuclideanSpace.proj (𝕜 := ℂ) (e.symm j).2.2).differentiable.comp_differentiableOn
      (h1.sub h2)
  have hsum : ∀ w ∈ W, ∑ j, ‖G j w‖ ^ 2 = fibreSpread X π w := by
    intro w hw
    have hb := hbij w hw
    have hfw : (fibre X π w).Finite := hS.image (fun x => g x w) |>.subset (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hb.2.2 hy
      exact ⟨x, hx, rfl⟩)
    rw [fibreSpread, ← Equiv.sum_comp e.symm.symm]
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply, G]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    have hinner : ∀ x x' : ↥S, ∑ l : Fin n, ‖(g x.val w - g x'.val w) l‖ ^ 2 =
        ‖g x.val w - g x'.val w‖ ^ 2 := by
      intro x x'
      rw [EuclideanSpace.norm_sq_eq]
    simp only [hinner]
    rw [Finset.sum_coe_sort S (fun x => ∑ x' : ↥S, ‖g x w - g x'.val w‖ ^ 2)]
    have hS' : (S : Set (ComplexModel n)) = fibre X π z₁ := hS.coe_toFinset
    rw [← finsum_mem_coe_finset, hS']
    apply finsum_mem_eq_of_bijOn (fun x => g x w) hb
    intro x _
    rw [Finset.sum_coe_sort S (fun x' => ‖g x w - g x' w‖ ^ 2), ← finsum_mem_coe_finset, hS']
    apply finsum_mem_eq_of_bijOn (fun x => g x w) hb
    intro x' _
    rfl
  have hpsh := plurisubharmonicAt_scaled_generatorLog (f := G) ⟨W, hWo, hz₁W, hGd⟩ hc
  obtain ⟨U, hU, hz₁U, hU'⟩ := hpsh
  refine ⟨U ∩ W, hU.inter hWo, ⟨hz₁U, hz₁W⟩, (hU'.mono inter_subset_left).congr ?_⟩
  intro w hw
  simp only
  rw [generatorLog_eq_log_sum, hsum w hw.2]

/-- Over a neighbourhood of `z₀`, the generic values of `c log V` are `≤ c log (λ²R² + 1)`. -/
theorem log_fibreSpread_le {c : ℝ} (hc : 0 < c) {R : ℝ} (hR : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ R)
    {z : ComplexModel k} (hz : z ∈ D) (hδ : δ z ≠ 0) :
    (c : EReal) * ENNReal.log (ENNReal.ofReal (fibreSpread X π z)) ≤
      ((c * Real.log (deg ^ 2 * R ^ 2 + 1) : ℝ) : EReal) := by
  have hf := hX.finite_fibre z hz
  have hle : fibreSpread X π z ≤ deg ^ 2 * R ^ 2 := by
    rw [fibreSpread_eq_sum hf]
    calc ∑ x ∈ hf.toFinset, ∑ y ∈ hf.toFinset, ‖x - y‖ ^ 2
        ≤ ∑ x ∈ hf.toFinset, ∑ y ∈ hf.toFinset, R ^ 2 := by
          refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
          have h := hR x ((hf.mem_toFinset).mp hx).1 y ((hf.mem_toFinset).mp hy).1
          exact pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = deg ^ 2 * R ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hf,
            hX.ncard_fibre z hz hδ]
          simp [nsmul_eq_mul]
          ring
  have hpos : (0 : ℝ) < deg ^ 2 * R ^ 2 + 1 := by positivity
  have hlog : ENNReal.log (ENNReal.ofReal (fibreSpread X π z)) ≤
      ((Real.log (deg ^ 2 * R ^ 2 + 1) : ℝ) : EReal) := by
    rw [← ENNReal.log_ofReal_of_pos hpos]
    exact ENNReal.log_le_log (ENNReal.ofReal_le_ofReal (by linarith))
  rw [EReal.coe_mul]
  exact mul_le_mul_of_nonneg_left hlog (EReal.coe_nonneg.mpr hc.le)

/-- **The collapse function is plurisubharmonic.** -/
theorem plurisubharmonicOn_collapse {c : ℝ} (hc : 0 < c) {R : ℝ}
    (hR : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ R) : PlurisubharmonicOn (collapse X π δ c) D := by
  refine PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus hX.isOpen_base
    (hX.plurisubharmonicOn_log_fibreSpread hc) ?_ (g := fun _ : Fin 1 => δ)
    (fun _ => hX.differentiableOn_disc) (fun y _ => by simp)
  intro z hz
  exact ⟨D, hX.isOpen_base.mem_nhds hz, c * Real.log (deg ^ 2 * R ^ 2 + 1),
    fun y hy hyA => hX.log_fibreSpread_le hc hR hy hyA⟩

/-- The collapse function is `-∞` over a point whose fibre is a single point. -/
theorem collapse_eq_bot {c : ℝ} (hc : 0 < c) {p : ComplexModel n} (hp : p ∈ X)
    (hY : fibre X π (π p) = {p}) : collapse X π δ c (π p) = ⊥ := by
  classical
  have hz₀ : π p ∈ D := hX.mem_base hp
  rw [collapse, PshCodimTwoExtension.extension_eq_uscRegularization]
  refine le_antisymm ?_ bot_le
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  -- choose `ε` with `c log (4 λ² ε²) < b`
  obtain ⟨b', -, hb'⟩ := EReal.exists_between_coe_real hb
  have hdeg : (0 : ℝ) ≤ deg := Nat.cast_nonneg _
  obtain ⟨ε, hε, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ c * Real.log (4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε) < b' := by
    have ht : Tendsto (fun ε : ℝ => c * Real.log (4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε)) (𝓝[>] 0)
        Filter.atBot := by
      have h0 : Tendsto (fun ε : ℝ => 4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Continuous (fun ε : ℝ => 4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε) := by fun_prop
          simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          have hε' : (0 : ℝ) < ε := hε
          show 0 < 4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε
          positivity
      exact (Real.tendsto_log_nhdsGT_zero.comp h0).const_mul_atBot hc
    obtain ⟨ε, h1, h2⟩ := ((ht.eventually (eventually_lt_atBot b')).and
      self_mem_nhdsWithin).exists
    exact ⟨ε, h2, h1⟩
  have hfib := hX.eventually_fibre_subset hz₀ hε
  have hev : ∀ᶠ z in 𝓝 (π p), z ∈ D ∧ fibre X π z ⊆ ⋃ q ∈ fibre X π (π p), ball q ε :=
    Filter.Eventually.and (hX.isOpen_base.mem_nhds hz₀ : ∀ᶠ z in 𝓝 (π p), z ∈ D) hfib
  refine le_trans ((uscRegularization_le_localSup _ hev).trans (iSup₂_le fun z hz => ?_)) hb'.le
  by_cases hzA : z ∈ {w | δ w = 0}
  · simp only [if_pos hzA]; exact bot_le
  simp only [if_neg hzA]
  have hδz : δ z ≠ 0 := hzA
  have hf := hX.finite_fibre z hz.1
  have hsub : ∀ x ∈ fibre X π z, x ∈ ball p ε := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hz.2 hx)
    rw [hY] at hq
    rw [mem_singleton_iff.mp hq] at hxq
    exact hxq
  have hle : fibreSpread X π z ≤ 4 * (deg : ℝ) ^ 2 * ε ^ 2 := by
    rw [fibreSpread_eq_sum hf]
    calc ∑ x ∈ hf.toFinset, ∑ y ∈ hf.toFinset, ‖x - y‖ ^ 2
        ≤ ∑ x ∈ hf.toFinset, ∑ y ∈ hf.toFinset, (2 * ε) ^ 2 := by
          refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
          have hx' := mem_ball.mp (hsub x ((hf.mem_toFinset).mp hx))
          have hy' := mem_ball.mp (hsub y ((hf.mem_toFinset).mp hy))
          have h : ‖x - y‖ ≤ 2 * ε := by
            rw [← dist_eq_norm]
            linarith [dist_triangle x p y, dist_comm p y]
          exact pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = 4 * (deg : ℝ) ^ 2 * ε ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hf,
            hX.ncard_fibre z hz.1 hδz]
          simp [nsmul_eq_mul]
          ring
  have hpos : (0 : ℝ) < 4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε := by positivity
  have hlog : ENNReal.log (ENNReal.ofReal (fibreSpread X π z)) ≤
      ((Real.log (4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε) : ℝ) : EReal) := by
    rw [← ENNReal.log_ofReal_of_pos hpos]
    exact ENNReal.log_le_log (ENNReal.ofReal_le_ofReal (by linarith))
  calc (c : EReal) * ENNReal.log (ENNReal.ofReal (fibreSpread X π z))
      ≤ (c : EReal) * ((Real.log (4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left hlog (EReal.coe_nonneg.mpr hc.le)
    _ = ((c * Real.log (4 * (deg : ℝ) ^ 2 * ε ^ 2 + ε) : ℝ) : EReal) := by rw [EReal.coe_mul]
    _ ≤ b' := EReal.coe_le_coe_iff.mpr hεb.le

/-- The collapse function is finite over a point whose fibre has another point. -/
theorem le_collapse {c : ℝ} (hc : 0 < c) {p q : ComplexModel n} (hp : p ∈ X)
    (hq : q ∈ fibre X π (π p)) (hpq : q ≠ p) :
    ((c * Real.log (‖p - q‖ ^ 2 / 4) : ℝ) : EReal) ≤ collapse X π δ c (π p) := by
  classical
  have hz₀ : π p ∈ D := hX.mem_base hp
  have hd : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hpq))
  set ε := ‖p - q‖ / 4 with hεdef
  have hε : 0 < ε := by positivity
  -- generic points near `π p` have fibre points near `p` and near `q`
  have hnear : ∀ x ∈ X, π x = π p → ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] (π p),
      (fibre X π z ∩ ball x ε).Nonempty := by
    intro x hx hxπ
    obtain ⟨m, hm⟩ := hX.exists_isSheetNumber hx
    have hm1 : 1 ≤ m := by
      rw [← sheetNumber_eq (hX.neBot_generic (hX.mem_base hx)) hm]
      exact hX.one_le_sheetNumber hx
    rw [IsSheetNumber, hxπ] at hm
    obtain ⟨ε', hε'm, hε'pos⟩ := ((hm.and (Ioo_mem_nhdsGT hε)).and self_mem_nhdsWithin).exists
    filter_upwards [hε'm.1] with z hz
    have hne : (fibre X π z ∩ ball x ε').Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [h, ncard_empty] at hz
      omega
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy.1, ball_subset_ball hε'm.2.2.le hy.2⟩
  have hev := (hnear p hp rfl).and (hnear q hq.1 hq.2)
  rw [collapse, PshCodimTwoExtension.extension_eq_uscRegularization]
  apply le_iInf₂
  intro U hU
  have := hX.neBot_generic hz₀
  obtain ⟨z, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hzU, hzδ⟩ :=
    (hev.and (Filter.Eventually.and
      (nhdsWithin_le_nhds hU : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] (π p), z ∈ U)
      (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] (π p), z ∈ {w | δ w ≠ 0}))).exists
  refine le_iSup₂_of_le z hzU ?_
  have hzA : z ∉ {w | δ w = 0} := hzδ
  simp only [if_neg hzA]
  have hzD : z ∈ D := hX.mapsTo hx.1.1 |> fun h => by rw [show π x = z from hx.1.2] at h; exact h
  have hf := hX.finite_fibre z hzD
  have hxy : ‖p - q‖ / 2 ≤ ‖x - y‖ := by
    have h1 : dist x p < ε := hx.2
    have h2 : dist y q < ε := hy.2
    have h3 : dist p q ≤ dist p x + dist x y + dist y q := by
      linarith [dist_triangle p x y, dist_triangle p y q]
    have hεd : ε = dist p q / 4 := by rw [hεdef, dist_eq_norm]
    rw [← dist_eq_norm, ← dist_eq_norm]
    linarith [dist_comm p x]
  have hge : (‖p - q‖ / 2) ^ 2 ≤ fibreSpread X π z := by
    rw [fibreSpread_eq_sum hf]
    have hxm : x ∈ hf.toFinset := (hf.mem_toFinset).mpr hx.1
    have hym : y ∈ hf.toFinset := (hf.mem_toFinset).mpr hy.1
    calc (‖p - q‖ / 2) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hxy 2
      _ ≤ ∑ y' ∈ hf.toFinset, ‖x - y'‖ ^ 2 :=
          Finset.single_le_sum (f := fun y' => ‖x - y'‖ ^ 2) (fun _ _ => by positivity) hym
      _ ≤ ∑ x' ∈ hf.toFinset, ∑ y' ∈ hf.toFinset, ‖x' - y'‖ ^ 2 :=
          Finset.single_le_sum (f := fun x' => ∑ y' ∈ hf.toFinset, ‖x' - y'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hxm
  have hpos : (0 : ℝ) < ‖p - q‖ ^ 2 / 4 := by positivity
  have hlog : ((Real.log (‖p - q‖ ^ 2 / 4) : ℝ) : EReal) ≤
      ENNReal.log (ENNReal.ofReal (fibreSpread X π z)) := by
    rw [← ENNReal.log_ofReal_of_pos hpos]
    refine ENNReal.log_le_log (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hge]
  rw [EReal.coe_mul]
  exact mul_le_mul_of_nonneg_left hlog (EReal.coe_nonneg.mpr hc.le)

end IsBranchedCovering

end SGPT.Unibranch.FNL
