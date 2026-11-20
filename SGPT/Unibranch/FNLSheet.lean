import SGPT.Unibranch.FNLTrace

/-!
# FN80 §5: sheet numbers and restrictions of branched coverings

Source: `[FN80]` Lemma 5.2, proof ("if we replace `X` by `X ∩ Δ'` with a small polydisc `Δ'`
centred at `p₀` [...] then `π|X'` is a branched covering of `Δ'ᵏ` with sheet number `< λ`").

* `IsBranchedCovering.one_le_sheetNumber`: every point of `X` has sheet number `≥ 1` (pure
  dimensionality);
* `IsBranchedCovering.sum_sheetNumber`: the sheet numbers along a fibre add up to `λ`;
* `IsBranchedCovering.restrict`: the part of `X` over an open connected `D' ⊆ D` and inside an
  open set `V` whose frontier meets no fibre over `D'` is again a finite branched covering.
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

namespace IsBranchedCovering

variable (hX : IsBranchedCovering X π D deg δ)
include hX

/-- Every point of `X` has sheet number at least one (`X ⊆ closure` of its generic part). -/
theorem one_le_sheetNumber {p : ComplexModel n} (hp : p ∈ X) : 1 ≤ sheetNumber X π δ p := by
  obtain ⟨m, hm⟩ := hX.exists_isSheetNumber hp
  rw [sheetNumber_eq (hX.neBot_generic (hX.mem_base hp)) hm]
  by_contra h0
  have hm0 : m = 0 := by omega
  subst hm0
  obtain ⟨ε, hε, hεpos⟩ := (hm.and self_mem_nhdsWithin).exists
  have hε' : (0 : ℝ) < ε := hεpos
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hε
  obtain ⟨η, hη, hηh⟩ := hε
  -- a generic point of `X` close to `p`
  have hcl := hX.subset_closure_generic hp
  have hnhd : ball p ε ∩ π ⁻¹' ball (π p) η ∈ 𝓝 p :=
    inter_mem (ball_mem_nhds p hε') (π.continuous.continuousAt.preimage_mem_nhds
      (ball_mem_nhds _ hη))
  obtain ⟨x, hxU, hxX, hxδ⟩ := mem_closure_iff_nhds.mp hcl _ hnhd
  have hcount := hηh hxU.2 hxδ
  have hmem : x ∈ fibre X π (π x) ∩ ball p ε := ⟨⟨hxX, rfl⟩, hxU.1⟩
  have hfin : (fibre X π (π x) ∩ ball p ε).Finite :=
    (hX.finite_fibre _ (hX.mem_base hxX)).subset inter_subset_left
  rw [Set.ncard_eq_zero hfin] at hcount
  rw [hcount] at hmem
  exact hmem

/-- The trace of the constant `1` is the number of sheets. -/
theorem trace_one {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D) :
    trace X π δ (fun _ => (1 : EReal)) z₀ = deg := by
  have hφ : IsWeaklyPSHOn X (fun _ => (1 : EReal)) :=
    ⟨fun _ _ => by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1, upperSemicontinuousOn_const,
      fun _ _ _ => discPshOn_const (1 : EReal) (by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1) _⟩
  have hgen : ∀ z ∈ D, δ z ≠ 0 → trace X π δ (fun _ => (1 : EReal)) z = deg := by
    intro z hz hδ
    have hf := hX.finite_fibre z hz
    rw [hX.trace_eq_sum_of_bijOn hδ _ hf.toFinset id (by rw [hf.coe_toFinset]; exact bijOn_id _)]
    rw [Finset.sum_const, nsmul_one, ← Set.ncard_eq_toFinset_card _ hf, hX.ncard_fibre z hz hδ]
  have hev : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀, trace X π δ (fun _ => (1 : EReal)) z = deg :=
    Filter.Eventually.and (nhdsWithin_le_nhds (hX.isOpen_base.mem_nhds hz₀) :
        ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀, z ∈ D) self_mem_nhdsWithin |>.mono
      fun z hz => hgen z hz.1 hz.2
  have := hX.neBot_generic hz₀
  apply le_antisymm
  · have h := hX.trace_le_of_eventually_le hz₀ hφ (C := (deg : ℝ))
      (hev.mono fun z hz => by rw [hz]; rfl)
    exact h
  · by_contra hlt
    push Not at hlt
    have h := hX.eventually_trace_lt hz₀ hφ hlt
    obtain ⟨z, hz1, hz2⟩ := (h.and hev).exists
    rw [hz2] at hz1
    exact lt_irrefl _ hz1

/-- **The sheet numbers along a fibre add up to `λ`.** -/
theorem sum_sheetNumber {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D) :
    ∑ p ∈ (hX.finite_fibre z₀ hz₀).toFinset, sheetNumber X π δ p = deg := by
  have h := hX.trace_one hz₀
  rw [trace, finsum_mem_eq_finite_toFinset_sum _ (hX.finite_fibre z₀ hz₀)] at h
  have h2 : ∑ p ∈ (hX.finite_fibre z₀ hz₀).toFinset, sheetNumber X π δ p • (1 : EReal) =
      ((∑ p ∈ (hX.finite_fibre z₀ hz₀).toFinset, sheetNumber X π δ p : ℕ) : EReal) := by
    simp only [nsmul_one]
    push_cast
    rfl
  rw [h2] at h
  have h3 : (((∑ p ∈ (hX.finite_fibre z₀ hz₀).toFinset, sheetNumber X π δ p : ℕ) : ℝ) : EReal) =
      ((deg : ℝ) : EReal) := by
    rw [EReal.coe_natCast, EReal.coe_natCast]; exact h
  exact_mod_cast EReal.coe_injective h3

/-- The complement of `{δ = 0}` in an open connected subset of the base is connected. -/
theorem isPreconnected_inter_generic {W : Set (ComplexModel k)} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWD : W ⊆ D) : IsPreconnected (W ∩ {w | δ w ≠ 0}) := by
  rcases (W ∩ {w | δ w ≠ 0}).eq_empty_or_nonempty with he | ⟨w, hw, hδw⟩
  · rw [he]; exact isPreconnected_empty
  let W' : Opens (ComplexModel k) := ⟨W, hWo⟩
  have : ConnectedSpace W' := isConnected_iff_connectedSpace.mp ⟨⟨w, hw⟩, hWc⟩
  let pres : ∀ x : ComplexModel k, x ∈ D →
      ComplexAnalyticPresentationAt (n := k) {w : ComplexModel k | δ w = 0} x :=
    fun x hx =>
    { generatorCount := 1
      generator := fun _ => δ
      coordinateNeighborhood := D
      isOpen_coordinateNeighborhood := hX.isOpen_base
      center_mem_coordinateNeighborhood := by
        simpa [complexChartAt, chartAt_self_eq] using hx
      coordinateNeighborhood_subset_target := by
        simp [complexChartAt, chartAt_self_eq]
      generator_holomorphic := fun _ => hX.differentiableOn_disc
      zeroLocus := by
        intro y _ _
        simp [complexChartAt, chartAt_self_eq] }
  have hT : IsComplexAnalyticSubset (n := k)
      (((↑) : W' → ComplexModel k) ⁻¹' {w : ComplexModel k | δ w = 0}) := fun x =>
    ⟨AnalyticSubsetOpens.presentationPreimageVal x (pres x.val (hWD x.property))⟩
  have hTne : (((↑) : W' → ComplexModel k) ⁻¹' {w : ComplexModel k | δ w = 0}) ≠ univ := by
    intro h
    have : (⟨w, hw⟩ : W') ∈ (((↑) : W' → ComplexModel k) ⁻¹' {w : ComplexModel k | δ w = 0}) := by
      rw [h]; trivial
    exact hδw this
  have hpre := AnalyticComplementConnected.isPreconnected_compl hT hTne
  have himg := hpre.image ((↑) : W' → ComplexModel k) continuous_subtype_val.continuousOn
  convert himg using 1
  ext z
  constructor
  · rintro ⟨hz, hδz⟩
    exact ⟨⟨z, hz⟩, hδz, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

/-- **Restriction of a branched covering** to the part of `X` inside an open set `V` and over
an open connected `D' ⊆ D`, provided no fibre over `D'` meets the frontier of `V`. -/
theorem restrict {V : Set (ComplexModel n)} {D' : Set (ComplexModel k)} (hV : IsOpen V)
    (hD' : IsOpen D') (hD'c : IsPreconnected D') (hD'D : D' ⊆ D)
    (hfront : ∀ z ∈ D', ∀ x ∈ fibre X π z, x ∉ frontier V) {m : ℕ}
    (hm : ∃ z ∈ D', δ z ≠ 0 ∧ (fibre X π z ∩ V).ncard = m) :
    IsBranchedCovering (X ∩ V ∩ π ⁻¹' D') π D' m δ := by
  classical
  have hfib : ∀ z, fibre (X ∩ V ∩ π ⁻¹' D') π z = if z ∈ D' then fibre X π z ∩ V else ∅ := by
    intro z
    split_ifs with hz
    · ext x
      simp only [fibre, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨⟨⟨hx, hxV⟩, -⟩, hxz⟩; exact ⟨⟨hx, hxz⟩, hxV⟩
      · rintro ⟨⟨hx, hxz⟩, hxV⟩; exact ⟨⟨⟨hx, hxV⟩, by rw [hxz]; exact hz⟩, hxz⟩
    · refine eq_empty_iff_forall_notMem.mpr ?_
      rintro x ⟨⟨⟨-, -⟩, hxD'⟩, hxz⟩
      have hπx : π x = z := hxz
      exact hz (hπx ▸ hxD')
  have hfib' : ∀ z ∈ D', fibre (X ∩ V ∩ π ⁻¹' D') π z = fibre X π z ∩ V := fun z hz => by
    rw [hfib z, if_pos hz]
  -- points of fibres over `D'` outside `V` are outside `closure V`
  have hout : ∀ z ∈ D', ∀ x ∈ fibre X π z, x ∉ V → x ∉ closure V := by
    intro z hz x hx hxV hxc
    exact hfront z hz x hx ⟨hxc, by rwa [hV.interior_eq]⟩
  -- local constancy of the count
  have hloc : ∀ z₁ ∈ D' ∩ {w | δ w ≠ 0}, ∀ᶠ w in 𝓝 z₁,
      (fibre X π w ∩ V).ncard = (fibre X π z₁ ∩ V).ncard := by
    intro z₁ hz₁
    have hz₁D : z₁ ∈ D := hD'D hz₁.1
    obtain ⟨W, hWo, hz₁W, -, -, g, hgx, hgd, hbij⟩ := hX.exists_local_sections hz₁D hz₁.2
    set S₁ := fibre X π z₁
    have hS₁ : S₁.Finite := hX.finite_fibre z₁ hz₁D
    have hcont : ∀ x ∈ S₁, ContinuousAt (g x) z₁ := fun x hx =>
      ((hgd x hx).differentiableAt (hWo.mem_nhds hz₁W)).continuousAt
    have hiff : ∀ᶠ w in 𝓝 z₁, ∀ x ∈ S₁, (g x w ∈ V ↔ x ∈ V) := by
      refine (hS₁.eventually_all).mpr fun x hx => ?_
      by_cases hxV : x ∈ V
      · have h := (hcont x hx).preimage_mem_nhds (by rw [hgx x hx]; exact hV.mem_nhds hxV)
        exact Filter.mem_of_superset h fun w hw => iff_of_true hw hxV
      · have hxc := hout z₁ hz₁.1 x hx hxV
        have h := (hcont x hx).preimage_mem_nhds
          (by rw [hgx x hx]; exact isClosed_closure.isOpen_compl.mem_nhds hxc)
        exact Filter.mem_of_superset h fun w hw => iff_of_false (fun h' => hw (subset_closure h'))
          hxV
    filter_upwards [hiff, hWo.mem_nhds hz₁W] with w hw hwW
    have hset : ∀ v ∈ W, (∀ x ∈ S₁, (g x v ∈ V ↔ x ∈ V)) →
        fibre X π v ∩ V = (fun x => g x v) '' (S₁ ∩ V) := by
      intro v hv hvi
      ext y
      constructor
      · rintro ⟨hy, hyV⟩
        obtain ⟨x, hx, rfl⟩ := (hbij v hv).2.2 hy
        exact ⟨x, ⟨hx, (hvi x hx).mp hyV⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxV⟩, rfl⟩
        exact ⟨(hbij v hv).1 hx, (hvi x hx).mpr hxV⟩
    rw [hset w hwW hw, ((hbij w hwW).2.1.mono inter_subset_left).ncard_image]
  have hconst : ∀ z ∈ D' ∩ {w | δ w ≠ 0}, (fibre X π z ∩ V).ncard = m := by
    obtain ⟨z₀, hz₀, hδz₀, hm₀⟩ := hm
    have hcont : ContinuousOn (fun z => (fibre X π z ∩ V).ncard) (D' ∩ {w | δ w ≠ 0}) :=
      fun z hz => by
        have h : (fun _ : ComplexModel k => (fibre X π z ∩ V).ncard) =ᶠ[𝓝 z]
            (fun z => (fibre X π z ∩ V).ncard) := (hloc z hz).mono fun w hw => hw.symm
        exact ContinuousAt.continuousWithinAt (tendsto_const_nhds.congr' h)
    intro z hz
    rw [← hm₀]
    exact (hX.isPreconnected_inter_generic hD' hD'c hD'D).constant hcont hz ⟨hz₀, hδz₀⟩
  refine ⟨hD', fun x hx => hx.2, ?_, ?_, hX.differentiableOn_disc.mono hD'D,
    fun z hz => hX.frequently_disc_ne z (hD'D hz), ?_, ?_, ?_⟩
  · -- properness
    intro K hKD' hK
    have hKD : K ⊆ D := hKD'.trans hD'D
    have hc := hX.isCompact_inter_preimage K hKD hK
    have heq : X ∩ V ∩ π ⁻¹' D' ∩ π ⁻¹' K = (X ∩ π ⁻¹' K) ∩ closure V := by
      ext x
      constructor
      · rintro ⟨⟨⟨hx, hxV⟩, -⟩, hxK⟩
        exact ⟨⟨hx, hxK⟩, subset_closure hxV⟩
      · rintro ⟨⟨hx, hxK⟩, hxc⟩
        have hπx : π x ∈ D' := hKD' hxK
        by_cases hxV : x ∈ V
        · exact ⟨⟨⟨hx, hxV⟩, hπx⟩, hxK⟩
        · exact absurd hxc (hout (π x) hπx x ⟨hx, rfl⟩ hxV)
    rw [heq]
    exact hc.inter_right isClosed_closure
  · intro z hz
    rw [hfib' z hz]
    exact (hX.finite_fibre z (hD'D hz)).subset inter_subset_left
  · intro z hz hδz
    rw [hfib' z hz]
    exact hconst z ⟨hz, hδz⟩
  · -- local graphs
    rintro x ⟨⟨hx, hxV⟩, hxD'⟩ hδx
    obtain ⟨U, W, g, hU, hW, hxU, hxW, -, hgd, hgX, huniq⟩ := hX.local_graph x hx hδx
    have hgx : g (π x) = x := (huniq x ⟨hx, hxW⟩).2
    have hU' : IsOpen (U ∩ D' ∩ g ⁻¹' V) := by
      have h := (hgd.continuousOn.isOpen_inter_preimage hU hV).inter hD'
      have heq : U ∩ D' ∩ g ⁻¹' V = U ∩ g ⁻¹' V ∩ D' := by
        ext w; simp only [mem_inter_iff, mem_preimage]; tauto
      rw [heq]
      exact h
    refine ⟨U ∩ D' ∩ g ⁻¹' V, W ∩ V, g, hU', hW.inter hV, ⟨⟨hxU, hxD'⟩, by
      rw [mem_preimage, hgx]; exact hxV⟩, ⟨hxW, hxV⟩, fun w hw => hw.1.2,
      hgd.mono fun w hw => hw.1.1, fun w hw => ⟨⟨⟨(hgX w hw.1.1).1, hw.2⟩, by
        rw [mem_preimage, (hgX w hw.1.1).2]; exact hw.1.2⟩, (hgX w hw.1.1).2⟩, ?_⟩
    rintro y ⟨⟨⟨hy, -⟩, hyD'⟩, hyW, hyV⟩
    obtain ⟨hyU, hgy⟩ := huniq y ⟨hy, hyW⟩
    exact ⟨⟨⟨hyU, hyD'⟩, by rw [mem_preimage, hgy]; exact hyV⟩, hgy⟩
  · -- pure dimensionality
    rintro x ⟨⟨hx, hxV⟩, hxD'⟩
    have hO : IsOpen (V ∩ π ⁻¹' D') := hV.inter (hD'.preimage π.continuous)
    have h := hO.inter_closure ⟨⟨hxV, hxD'⟩, hX.subset_closure_generic hx⟩
    refine closure_mono ?_ h
    rintro y ⟨⟨hyV, hyD'⟩, hy, hyδ⟩
    exact ⟨⟨⟨hy, hyV⟩, hyD'⟩, hyδ⟩

end IsBranchedCovering

end SGPT.Unibranch.FNL
