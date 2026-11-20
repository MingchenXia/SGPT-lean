import SGPT.GAGA.H0SConeGraph

/-!
# Holomorphic embeddings into `ℙᴺ` from local homogeneous lifts; the Segre embedding


A map `Ψ : M → ℙᴺ` is often given, near each point, by a holomorphic *homogeneous lift*
`F : ℂⁿ → ℂ^{N+1} ∖ 0` in the chart of `M`: `Ψ(e⁻¹ z) = [F z]`.  The immersion condition of
`SGPT.GAGA.H0S.IsHolomorphicEmbedding` (injective derivative in every affine chart of `ℙᴺ`)
is then the chart-free condition `IsProjImmersionAt F z₀`: no nonzero vector `v` has
`dF(z₀) v ∈ ℂ F(z₀)`.

* `isHolomorphicEmbedding_of_lifts`: an injective map with such lifts at every point is a
  holomorphic embedding (continuity included);
* `exists_lift_of_isHolomorphicEmbedding`: conversely a holomorphic embedding has such lifts
  (`affineLift i ∘ chartMap Ψ p i`);
* the Segre map `segreMap : ℙᴺ × ℙʳ → ℙ^{(N+1)(r+1)-1}`, `([a], [b]) ↦ [aₐ b_β]`, is injective
  (`segreMap_injective`), and the Segre product of two lifts satisfying the joint condition
  "`dF v ∈ ℂ F` and `dG v ∈ ℂ G` imply `v = 0`" is a projective immersion
  (`isProjImmersionAt_segreVec`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.GAGA.H0S
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

noncomputable section

namespace SGPT.GAGA.ChowBl

/-! ### The total quotient map -/

section Pmk

variable {N : ℕ}

open Classical in
/-- The quotient map `ℂ^{N+1} ∖ 0 → ℙᴺ`, extended (arbitrarily) by a point at `0`. -/
def pmk (v : Fin (N + 1) → ℂ) : ComplexProjectiveSpace N :=
  if h : v ≠ 0 then mk v h else affinePoint 0 0

theorem pmk_eq_mk {v : Fin (N + 1) → ℂ} (h : v ≠ 0) : pmk v = mk v h := by
  simp [pmk, h]

theorem continuousAt_pmk {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) : ContinuousAt (pmk (N := N)) v := by
  have hopen : IsOpen {w : Fin (N + 1) → ℂ | w ≠ 0} := isOpen_ne
  have h1 : Continuous fun w : {w : Fin (N + 1) → ℂ // w ≠ 0} => pmk (N := N) w.1 := by
    have : (fun w : {w : Fin (N + 1) → ℂ // w ≠ 0} => pmk (N := N) w.1) =
        fun w : {w : Fin (N + 1) → ℂ // w ≠ 0} => ComplexProjectiveSpace.mk w.1 w.2 :=
      funext fun w => pmk_eq_mk w.2
    rw [this]
    exact continuous_mk_subtype
  have hon : ContinuousOn (pmk (N := N)) {w | w ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact h1
  exact hon.continuousAt (hopen.mem_nhds hv)

theorem pmk_smul {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    pmk (c • v) = pmk v := by
  rw [pmk_eq_mk hv, pmk_eq_mk (smul_ne_zero hc hv), mk_smul hv hc]

theorem pmk_eq_pmk_iff {v w : Fin (N + 1) → ℂ} (hv : v ≠ 0) (hw : w ≠ 0) :
    pmk v = pmk w ↔ ∃ c : ℂ, c ≠ 0 ∧ v = c • w := by
  rw [pmk_eq_mk hv, pmk_eq_mk hw]
  constructor
  · intro h
    obtain ⟨c, hc, hcv⟩ := exists_eq_smul_of_mk_eq h
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    rw [hcv, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro ⟨c, hc, rfl⟩
    exact mk_smul hw hc

theorem pmk_rep (x : ComplexProjectiveSpace N) : pmk x.rep = x := by
  rw [pmk_eq_mk x.rep_ne_zero, mk_rep]

theorem mem_affineChart_source_pmk_iff (i : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) :
    pmk v ∈ (affineChart i).source ↔ v i ≠ 0 := by
  rw [pmk_eq_mk hv]
  exact mk_mem_affineChart_source_iff i hv

end Pmk

/-! ### Projective immersions -/

section Immersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} [Fintype ι]

/-- The homogeneous lift `F` is a *projective immersion* at `z₀`: no nonzero vector is mapped by
`dF(z₀)` into the line `ℂ F(z₀)` (the derivative of `[F]` is injective). -/
def IsProjImmersionAt (F : E → ι → ℂ) (z₀ : E) : Prop :=
  ∀ v, (∃ c : ℂ, fderiv ℂ F z₀ v = c • F z₀) → v = 0

/-- The `i`-th coordinate of the derivative of a vector-valued map. -/
theorem fderiv_apply_coord {F : E → ι → ℂ} {z₀ : E} (hF : DifferentiableAt ℂ F z₀) (i : ι)
    (v : E) : fderiv ℂ F z₀ v i = fderiv ℂ (fun z => F z i) z₀ v := by
  have h := hasFDerivAt_pi'.mp hF.hasFDerivAt i
  rw [h.fderiv]
  rfl

end Immersion

section Criterion

variable {n N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- In the affine chart `U_i`, `v = vᵢ · (insertNth i 1 (v/vᵢ))`. -/
theorem eq_smul_affineLift_affineRatio (i : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hvi : v i ≠ 0) :
    v = v i • affineLift i (affineRatio i v) := by
  rw [affineLift_affineRatio i hvi, smul_smul, mul_inv_cancel₀ hvi, one_smul]

/-- If `R = affineRatio i ∘ F` has `dR(z₀) w = 0`, then `dF(z₀) w ∈ ℂ F(z₀)`. -/
theorem exists_fderiv_eq_smul_of_fderiv_affineRatio_eq_zero {F : ComplexModel n → Fin (N + 1) → ℂ}
    {z₀ : ComplexModel n} {i : Fin (N + 1)} (hF : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ F z)
    (hFi : ∀ᶠ z in 𝓝 z₀, F z i ≠ 0) {w : ComplexModel n}
    (hw : fderiv ℂ (fun z => affineRatio i (F z)) z₀ w = 0) :
    ∃ c : ℂ, fderiv ℂ F z₀ w = c • F z₀ := by
  set R : ComplexModel n → ComplexModel N := fun z => affineRatio i (F z) with hR
  have hRd : DifferentiableAt ℂ R z₀ :=
    (differentiableAt_affineRatio i hFi.self_of_nhds).comp z₀ hF.self_of_nhds
  have hFid : DifferentiableAt ℂ (fun z => F z i) z₀ :=
    differentiableAt_pi.mp hF.self_of_nhds i
  have hG : DifferentiableAt ℂ (fun z => affineLift i (R z)) z₀ :=
    (differentiable_affineLift i _).comp z₀ hRd
  have heq : F =ᶠ[𝓝 z₀] fun z => F z i • affineLift i (R z) := by
    filter_upwards [hFi] with z hz
    exact eq_smul_affineLift_affineRatio i hz
  have hderiv : HasFDerivAt (fun z => F z i • affineLift i (R z)) _ z₀ :=
    hFid.hasFDerivAt.smul hG.hasFDerivAt
  rw [heq.fderiv_eq, hderiv.fderiv]
  have hGw : fderiv ℂ (fun z => affineLift i (R z)) z₀ w = 0 := by
    rw [fderiv_fun_comp z₀ (differentiable_affineLift i _) hRd, ContinuousLinearMap.comp_apply, hw,
      map_zero]
  refine ⟨fderiv ℂ (fun z => F z i) z₀ w / F z₀ i, ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hGw, smul_zero, zero_add]
  have hF₀ : F z₀ = F z₀ i • affineLift i (R z₀) :=
    eq_smul_affineLift_affineRatio i hFi.self_of_nhds
  calc _ = (fderiv ℂ (fun z => F z i) z₀ w / F z₀ i) • (F z₀ i • affineLift i (R z₀)) := by
        rw [smul_smul, div_mul_cancel₀ _ hFi.self_of_nhds]
    _ = _ := by rw [← hF₀]

/-- **Holomorphic embeddings from local homogeneous lifts.** An injective map `Ψ : M → ℙᴺ`
which near every point `p` is `Ψ(e⁻¹ z) = [F z]` for a holomorphic projective immersion `F`
(`e` the preferred chart at `p`) is a holomorphic embedding. -/
theorem isHolomorphicEmbedding_of_lifts {Ψ : M → ComplexProjectiveSpace N}
    (hinj : Function.Injective Ψ)
    (hlift : ∀ p : M, ∃ F : ComplexModel n → Fin (N + 1) → ℂ,
      (∀ᶠ z in 𝓝 ((complexChartAt (n := n) p).val p),
        DifferentiableAt ℂ F z ∧ F z ≠ 0 ∧ Ψ ((complexChartAt (n := n) p).val.symm z) = pmk (F z)) ∧
      IsProjImmersionAt F ((complexChartAt (n := n) p).val p)) :
    IsHolomorphicEmbedding (n := n) Ψ := by
  have hcont : Continuous Ψ := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    obtain ⟨F, hF, -⟩ := hlift p
    set e := (complexChartAt (n := n) p).val
    have hp : p ∈ e.source := mem_complexChartAt_source p
    obtain ⟨hFd, hF0, -⟩ := hF.self_of_nhds
    have h1 : ContinuousAt (fun z => pmk (F z)) (e p) :=
      (continuousAt_pmk hF0).comp hFd.continuousAt
    have h2 : ContinuousAt (fun q => pmk (F (e q))) p := h1.comp (e.continuousAt hp)
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hp, (e.continuousAt hp).eventually hF] with q hq hFq
    rw [← hFq.2.2, e.left_inv hq]
  refine ⟨hcont, hinj, fun p i hpi => ?_, fun p i hpi => ?_⟩
  · -- holomorphic
    obtain ⟨F, hF, himm⟩ := hlift p
    set e := (complexChartAt (n := n) p).val
    have hp : p ∈ e.source := mem_complexChartAt_source p
    obtain ⟨hFd₀, hF0₀, hΨ₀⟩ := hF.self_of_nhds
    have hFi₀ : F (e p) i ≠ 0 := by
      rw [e.left_inv hp] at hΨ₀
      rw [hΨ₀] at hpi
      exact (mem_affineChart_source_pmk_iff i hF0₀).mp hpi
    have hFi : ∀ᶠ z in 𝓝 (e p), F z i ≠ 0 :=
      (differentiableAt_pi.mp hFd₀ i).continuousAt.eventually_ne hFi₀
    have hchart : ∀ᶠ z in 𝓝 (e p), chartMap (n := n) Ψ p i z = affineRatio i (F z) := by
      filter_upwards [hF, hFi] with z hz hzi
      show affineChart i (Ψ (e.symm z)) = _
      rw [hz.2.2, pmk_eq_mk hz.2.1, affineChart_mk i hz.2.1 hzi]
    filter_upwards [Filter.Eventually.eventually_nhds hchart, hF, hFi] with z hz hzF hzi
    exact ((differentiableAt_affineRatio i hzi).comp z hzF.1).congr_of_eventuallyEq hz
  · -- immersion
    obtain ⟨F, hF, himm⟩ := hlift p
    set e := (complexChartAt (n := n) p).val
    have hp : p ∈ e.source := mem_complexChartAt_source p
    obtain ⟨hFd₀, hF0₀, hΨ₀⟩ := hF.self_of_nhds
    have hFi₀ : F (e p) i ≠ 0 := by
      rw [e.left_inv hp] at hΨ₀
      rw [hΨ₀] at hpi
      exact (mem_affineChart_source_pmk_iff i hF0₀).mp hpi
    have hFi : ∀ᶠ z in 𝓝 (e p), F z i ≠ 0 :=
      (differentiableAt_pi.mp hFd₀ i).continuousAt.eventually_ne hFi₀
    have hchart : ∀ᶠ z in 𝓝 (e p), chartMap (n := n) Ψ p i z = affineRatio i (F z) := by
      filter_upwards [hF, hFi] with z hz hzi
      show affineChart i (Ψ (e.symm z)) = _
      rw [hz.2.2, pmk_eq_mk hz.2.1, affineChart_mk i hz.2.1 hzi]
    have hchart' : chartMap (n := n) Ψ p i =ᶠ[𝓝 (e p)] fun z => affineRatio i (F z) := hchart
    rw [hchart'.fderiv_eq]
    refine (injective_iff_map_eq_zero _).mpr fun w hw => himm w ?_
    exact exists_fderiv_eq_smul_of_fderiv_affineRatio_eq_zero
      (hF.mono fun _ h => h.1) hFi hw

/-- **Lifts of a holomorphic embedding**: near `p`, `Ψ(e⁻¹ z) = [insertNth i 1 (chartMap Ψ p i z)]`
for any affine chart `U_i ∋ Ψ p`, and this lift is a holomorphic projective immersion. -/
theorem exists_lift_of_isHolomorphicEmbedding {Ψ : M → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (p : M) {i : Fin (N + 1)}
    (hpi : Ψ p ∈ (affineChart i).source) :
    (∀ᶠ z in 𝓝 ((complexChartAt (n := n) p).val p),
        DifferentiableAt ℂ (fun z => affineLift i (chartMap (n := n) Ψ p i z)) z ∧
        affineLift i (chartMap (n := n) Ψ p i z) ≠ 0 ∧
        Ψ ((complexChartAt (n := n) p).val.symm z) = pmk (affineLift i (chartMap (n := n) Ψ p i z))) ∧
      IsProjImmersionAt (fun z => affineLift i (chartMap (n := n) Ψ p i z))
        ((complexChartAt (n := n) p).val p) := by
  set e := (complexChartAt (n := n) p).val
  have hp : p ∈ e.source := mem_complexChartAt_source p
  have hsrc : ∀ᶠ z in 𝓝 (e p), Ψ (e.symm z) ∈ (affineChart i).source := by
    have hc : ContinuousAt (fun z => Ψ (e.symm z)) (e p) :=
      hΨ.continuous.continuousAt.comp (e.continuousAt_symm (e.map_source hp))
    have h0 : Ψ (e.symm (e p)) ∈ (affineChart i).source := by rw [e.left_inv hp]; exact hpi
    exact hc.eventually ((affineChart i).open_source.mem_nhds h0)
  refine ⟨?_, ?_⟩
  · filter_upwards [hΨ.holomorphic p i hpi, hsrc] with z hz hzs
    refine ⟨(differentiable_affineLift i _).comp z hz, affineLift_ne_zero i _, ?_⟩
    rw [pmk_eq_mk (affineLift_ne_zero i _)]
    exact ((affineChart i).left_inv hzs).symm
  · intro w ⟨c, hc⟩
    set F := fun z => affineLift i (chartMap (n := n) Ψ p i z)
    have hd : DifferentiableAt ℂ (chartMap (n := n) Ψ p i) (e p) :=
      (hΨ.holomorphic p i hpi).self_of_nhds
    have hFd : DifferentiableAt ℂ F (e p) := (differentiable_affineLift i _).comp _ hd
    -- the `i`-th coordinate of `F` is constant
    have hci : c = 0 := by
      have h1 := fderiv_apply_coord hFd i w
      have h2 : (fun z => F z i) = fun _ => (1 : ℂ) := funext fun z => affineLift_same i _
      rw [h2, (hasFDerivAt_const (1 : ℂ) (e p)).fderiv, hc] at h1
      simpa [F] using h1
    have hFw : fderiv ℂ F (e p) w = 0 := by rw [hc, hci, zero_smul]
    have hR : chartMap (n := n) Ψ p i = fun z => affineRatio i (F z) :=
      funext fun z => (affineRatio_affineLift i _).symm
    apply hΨ.immersion p i hpi
    rw [map_zero, hR, fderiv_fun_comp (e p) (differentiableAt_affineRatio i (by simp [F])) hFd,
      ContinuousLinearMap.comp_apply, hFw, map_zero]

end Criterion

/-! ### The Segre embedding -/

section Segre

variable {N r : ℕ}

/-- The dimension `(N+1)(r+1) - 1` of the Segre target. -/
def segreDim (N r : ℕ) : ℕ := N * r + N + r

/-- The indices of `ℙ^{segreDim N r}` are the pairs of indices. -/
def segreIdx (N r : ℕ) : Fin (segreDim N r + 1) ≃ Fin (N + 1) × Fin (r + 1) :=
  (finCongr (by simp only [segreDim]; ring)).trans finProdFinEquiv.symm

/-- The Segre vector `a ⊗ b`. -/
def segreVec (a : Fin (N + 1) → ℂ) (b : Fin (r + 1) → ℂ) : Fin (segreDim N r + 1) → ℂ :=
  fun k => a (segreIdx N r k).1 * b (segreIdx N r k).2

theorem segreVec_apply (a : Fin (N + 1) → ℂ) (b : Fin (r + 1) → ℂ) (α : Fin (N + 1))
    (β : Fin (r + 1)) : segreVec a b ((segreIdx N r).symm (α, β)) = a α * b β := by
  simp [segreVec]

theorem segreVec_ne_zero {a : Fin (N + 1) → ℂ} {b : Fin (r + 1) → ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    segreVec a b ≠ 0 := by
  obtain ⟨α, hα⟩ := Function.ne_iff.mp ha
  obtain ⟨β, hβ⟩ := Function.ne_iff.mp hb
  intro h
  have := congrFun h ((segreIdx N r).symm (α, β))
  rw [segreVec_apply] at this
  exact mul_ne_zero hα hβ this

theorem segreVec_smul (s t : ℂ) (a : Fin (N + 1) → ℂ) (b : Fin (r + 1) → ℂ) :
    segreVec (s • a) (t • b) = (s * t) • segreVec a b := by
  funext k
  simp only [segreVec, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Segre map `ℙᴺ × ℙʳ → ℙ^{(N+1)(r+1)-1}`. -/
def segreMap (x : ComplexProjectiveSpace N) (u : ComplexProjectiveSpace r) :
    ComplexProjectiveSpace (segreDim N r) :=
  pmk (segreVec x.rep u.rep)

theorem segreMap_pmk {a : Fin (N + 1) → ℂ} {b : Fin (r + 1) → ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    segreMap (pmk a) (pmk b) = pmk (segreVec a b) := by
  unfold segreMap
  obtain ⟨s, hs, hsa⟩ := (pmk_eq_pmk_iff (pmk a).rep_ne_zero ha).mp (by rw [pmk_rep])
  obtain ⟨t, ht, htb⟩ := (pmk_eq_pmk_iff (pmk b).rep_ne_zero hb).mp (by rw [pmk_rep])
  rw [hsa, htb, segreVec_smul, pmk_smul (segreVec_ne_zero ha hb) (mul_ne_zero hs ht)]

/-- If `a ⊗ b = c (a' ⊗ b')` with all vectors nonzero, then `[a] = [a']` and `[b] = [b']`. -/
theorem pmk_eq_of_segreVec_eq {a a' : Fin (N + 1) → ℂ} {b b' : Fin (r + 1) → ℂ}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : pmk (segreVec a b) = pmk (segreVec a' b')) : pmk a = pmk a' ∧ pmk b = pmk b' := by
  obtain ⟨c, hc, hcab⟩ := (pmk_eq_pmk_iff (segreVec_ne_zero ha hb)
    (segreVec_ne_zero ha' hb')).mp h
  have hab : ∀ α β, a α * b β = c * (a' α * b' β) := fun α β => by
    have := congrFun hcab ((segreIdx N r).symm (α, β))
    simpa [segreVec_apply] using this
  obtain ⟨α₀, hα₀⟩ := Function.ne_iff.mp ha
  obtain ⟨β₀, hβ₀⟩ := Function.ne_iff.mp hb
  have hα₀' : a' α₀ ≠ 0 := by
    intro h0; have := hab α₀ β₀; rw [h0, zero_mul, mul_zero] at this
    exact mul_ne_zero hα₀ hβ₀ this
  have hβ₀' : b' β₀ ≠ 0 := by
    intro h0; have := hab α₀ β₀; simp only [h0, mul_zero] at this
    exact mul_ne_zero hα₀ hβ₀ this
  constructor
  · refine (pmk_eq_pmk_iff ha ha').mpr ⟨c * b' β₀ / b β₀, by
      refine div_ne_zero (mul_ne_zero hc hβ₀') hβ₀, ?_⟩
    funext α
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hβ₀]
    linear_combination hab α β₀
  · refine (pmk_eq_pmk_iff hb hb').mpr ⟨c * a' α₀ / a α₀, by
      refine div_ne_zero (mul_ne_zero hc hα₀') hα₀, ?_⟩
    funext β
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hα₀]
    linear_combination hab α₀ β

theorem segreMap_injective : Function.Injective fun xu : ComplexProjectiveSpace N ×
    ComplexProjectiveSpace r => segreMap xu.1 xu.2 := by
  rintro ⟨x, u⟩ ⟨x', u'⟩ h
  have h' := pmk_eq_of_segreVec_eq x.rep_ne_zero x'.rep_ne_zero u.rep_ne_zero u'.rep_ne_zero h
  simp only [pmk_rep] at h'
  rw [h'.1, h'.2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Segre product of two lifts satisfying the joint condition is a projective immersion. -/
theorem isProjImmersionAt_segreVec {F : E → Fin (N + 1) → ℂ} {G : E → Fin (r + 1) → ℂ} {z₀ : E}
    (hF : DifferentiableAt ℂ F z₀) (hG : DifferentiableAt ℂ G z₀) (hF0 : F z₀ ≠ 0)
    (hG0 : G z₀ ≠ 0)
    (hjoint : ∀ v, (∃ c : ℂ, fderiv ℂ F z₀ v = c • F z₀) →
      (∃ c : ℂ, fderiv ℂ G z₀ v = c • G z₀) → v = 0) :
    IsProjImmersionAt (fun z => segreVec (F z) (G z)) z₀ := by
  intro v ⟨c, hc⟩
  -- the derivative of the Segre vector
  have hcomp : ∀ k, HasFDerivAt (fun z => segreVec (F z) (G z) k)
      (F z₀ (segreIdx N r k).1 • (ContinuousLinearMap.proj (segreIdx N r k).2 ∘L fderiv ℂ G z₀) +
        G z₀ (segreIdx N r k).2 •
          (ContinuousLinearMap.proj (segreIdx N r k).1 ∘L fderiv ℂ F z₀)) z₀ := by
    intro k
    have h1 := hasFDerivAt_pi'.mp hF.hasFDerivAt (segreIdx N r k).1
    have h2 := hasFDerivAt_pi'.mp hG.hasFDerivAt (segreIdx N r k).2
    exact h1.mul h2
  have hS : DifferentiableAt ℂ (fun z => segreVec (F z) (G z)) z₀ :=
    differentiableAt_pi.mpr fun k => (hcomp k).differentiableAt
  have hcoord : ∀ α β, fderiv ℂ F z₀ v α * G z₀ β + F z₀ α * fderiv ℂ G z₀ v β =
      c * (F z₀ α * G z₀ β) := by
    intro α β
    have h1 := fderiv_apply_coord hS ((segreIdx N r).symm (α, β)) v
    rw [hc, (hcomp _).fderiv] at h1
    simp only [Pi.smul_apply, smul_eq_mul, Equiv.apply_symm_apply, segreVec_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h1
    linear_combination -h1
  obtain ⟨α₀, hα₀⟩ := Function.ne_iff.mp hF0
  obtain ⟨β₀, hβ₀⟩ := Function.ne_iff.mp hG0
  refine hjoint v ⟨c - fderiv ℂ G z₀ v β₀ / G z₀ β₀, ?_⟩ ⟨c - fderiv ℂ F z₀ v α₀ / F z₀ α₀, ?_⟩
  · funext α
    simp only [Pi.smul_apply, smul_eq_mul]
    apply mul_right_cancel₀ hβ₀
    have h1 : fderiv ℂ G z₀ v β₀ / G z₀ β₀ * G z₀ β₀ = fderiv ℂ G z₀ v β₀ :=
      div_mul_cancel₀ _ hβ₀
    linear_combination hcoord α β₀ + F z₀ α * h1
  · funext β
    simp only [Pi.smul_apply, smul_eq_mul]
    apply mul_right_cancel₀ hα₀
    have h1 : fderiv ℂ F z₀ v α₀ / F z₀ α₀ * F z₀ α₀ = fderiv ℂ F z₀ v α₀ :=
      div_mul_cancel₀ _ hα₀
    linear_combination hcoord α₀ β + G z₀ β * h1

end Segre

end SGPT.GAGA.ChowBl
