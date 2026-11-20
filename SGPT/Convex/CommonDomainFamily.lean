import SGPT.Convex.FiniteQualifiedConjugation
import SGPT.Convex.WeightedRooftop

/-!
# Actual common-domain-closure finite-family conjugation

Intrinsic interiors are transported through the actual affine spans and closures.
The epigraph-indicator split is obtained from the checked qualified finite sum,
then zero-weight covectors are absorbed using actual continuous halfspace bounds
on the coincident domain closures.
-/

namespace SGPT.Convex

open Set Filter Topology
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual convex intrinsic interiors are unchanged by actual closure. -/
theorem intrinsicInterior_closure_eq {C : Set E} (hC : Convex ℝ C) :
    intrinsicInterior ℝ (closure C) = intrinsicInterior ℝ C := by
  by_cases hEmpty : C = ∅
  · simp [hEmpty]
  have hne : C.Nonempty := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hC hne
  let A := affineSpan ℝ C
  let xA : A := ⟨x, subset_affineSpan ℝ _ (intrinsicInterior_subset hx)⟩
  let : Nonempty A := ⟨xA⟩
  let eA := AffineIsometryEquiv.vaddConst ℝ xA
  let FA := A.subtype.comp eA.toAffineEquiv.toAffineMap
  let CA : Set A.direction := FA ⁻¹' C
  let P : Set A := (↑) ⁻¹' C
  have hxA : xA ∈ interior P := by
    obtain ⟨y, hy, heq⟩ := mem_intrinsicInterior.mp hx
    have hyx : y = xA := Subtype.ext heq
    simpa only [hyx] using hy
  have hzero : (0 : A.direction) ∈ interior CA := by
    change (0 : A.direction) ∈ interior (eA.toHomeomorph ⁻¹' P)
    rw [← eA.toHomeomorph.preimage_interior]
    change eA 0 ∈ interior P
    simpa [eA] using hxA
  have hconv : Convex ℝ CA := hC.affine_preimage FA
  have hIntCA : interior (closure CA) = interior CA :=
    hconv.interior_closure_eq_interior_of_nonempty_interior ⟨0, hzero⟩
  have hIntA : interior (closure P) = interior P := by
    apply eA.toHomeomorph.surjective.preimage_injective
    rw [eA.toHomeomorph.preimage_interior, eA.toHomeomorph.preimage_interior,
      eA.toHomeomorph.preimage_closure]
    exact hIntCA
  have hImage : ((↑) : A → E) '' P = C := by
    change ((↑) : A → E) '' ((↑) ⁻¹' C) = C
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.mpr (subset_affineSpan ℝ C)
  have hclA : closure P = ((↑) ⁻¹' closure C : Set A) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hImage]
  have hspan : affineSpan ℝ (closure C) = affineSpan ℝ C := by
    simpa only [intrinsicClosure_eq_closure] using
      (affineSpan_intrinsicClosure (𝕜 := ℝ) C)
  unfold intrinsicInterior
  rw [hspan]
  congr 1
  change interior ((↑) ⁻¹' closure C : Set A) = interior P
  rw [← hclA, hIntA]

/-- Actual coincident closures give actual coincident intrinsic interiors. -/
theorem intrinsicInterior_eq_of_closure_eq {C D : Set E}
    (hC : Convex ℝ C) (hD : Convex ℝ D) (hcl : closure C = closure D) :
    intrinsicInterior ℝ C = intrinsicInterior ℝ D := by
  rw [← intrinsicInterior_closure_eq hC, hcl, intrinsicInterior_closure_eq hD]

omit [FiniteDimensional ℝ E] in
/-- Actual set inclusion transports intrinsic interior when the actual affine spans coincide. -/
theorem mem_intrinsicInterior_of_subset_of_affineSpan_eq {C D : Set E}
    (hCD : C ⊆ D) (hspan : affineSpan ℝ C = affineSpan ℝ D) {x : E}
    (hx : x ∈ intrinsicInterior ℝ C) : x ∈ intrinsicInterior ℝ D := by
  unfold intrinsicInterior at hx ⊢
  rw [← hspan]
  exact image_mono (interior_mono (preimage_mono hCD)) hx

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Every actual epigraph point is a limit of its actual strictly higher heights. -/
theorem epigraph_subset_closure_strictEpigraph (f : E → EReal) :
    epigraph f ⊆ closure (strictEpigraph f) := by
  intro p hp
  have hcont : Continuous (fun t : ℝ ↦ (p.1, p.2 + t)) :=
    continuous_const.prodMk (continuous_const.add continuous_id)
  have htend : Tendsto (fun t : ℝ ↦ (p.1, p.2 + t)) (𝓝[>] 0) (𝓝 p) := by
    simpa only [add_zero, Prod.eta] using
      (hcont.continuousAt.tendsto (x := 0)).mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  change f p.1 < ((p.2 + t : ℝ) : EReal)
  exact hp.trans_lt (EReal.coe_lt_coe (by linarith))

/-- The actual strict and non-strict real-height epigraphs have the same actual affine span. -/
theorem affineSpan_strictEpigraph_eq_epigraph (f : E → EReal) :
    affineSpan ℝ (strictEpigraph f) = affineSpan ℝ (epigraph f) := by
  apply le_antisymm
  · apply affineSpan_mono ℝ
    intro p hp
    change f p.1 ≤ (p.2 : EReal)
    exact hp.le
  · apply affineSpan_le.mpr
    exact (epigraph_subset_closure_strictEpigraph f).trans
      (closure_minimal (subset_affineSpan ℝ (strictEpigraph f))
        (affineSpan ℝ (strictEpigraph f)).closed_of_finiteDimensional)

/-- A genuine strict real height over an actual relative-domain interior point
qualifies the actual non-strict epigraph. -/
theorem mem_intrinsicInterior_epigraph_of_strict_height {f : E → EReal}
    (hf : IsProper f) {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    {r : ℝ} (hr : f x < (r : EReal)) :
    (x, r) ∈ intrinsicInterior ℝ (epigraph f) :=
  mem_intrinsicInterior_of_subset_of_affineSpan_eq (by
    intro p hp
    change f p.1 ≤ (p.2 : EReal)
    exact hp.le)
    (affineSpan_strictEpigraph_eq_epigraph f) (mem_intrinsicInterior_strictEpigraph hf hx hr)

/-- Actual coincident convex domain closures produce an actual common relative-interior point. -/
theorem exists_common_intrinsicInterior_of_closure_eq {I : Type*} [Nonempty I]
    {f : I → E → EReal} (hf : ∀ i, IsProper (f i))
    (hclosure : ∀ i j, closure (effectiveDomain (f i)) = closure (effectiveDomain (f j))) :
    ∃ x : E, ∀ i, x ∈ intrinsicInterior ℝ (effectiveDomain (f i)) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_effectiveDomain (hf i₀).1) (hf i₀).2.1
  refine ⟨x, fun i ↦ ?_⟩
  rw [← intrinsicInterior_eq_of_closure_eq (convex_effectiveDomain (hf i₀).1)
    (convex_effectiveDomain (hf i).1) (hclosure i₀ i)]
  exact hx

/-- An actual finite common-domain-closure family has a genuine common epigraph qualification. -/
theorem exists_common_intrinsicInterior_epigraph_of_closure_eq {I : Type*}
    [Fintype I] [Nonempty I] {f : I → E → EReal} (hf : ∀ i, IsProper (f i))
    (hclosure : ∀ i j, closure (effectiveDomain (f i)) = closure (effectiveDomain (f j))) :
    ∃ p : E × ℝ, ∀ i, p ∈ intrinsicInterior ℝ (epigraph (f i)) := by
  obtain ⟨x, hx⟩ := exists_common_intrinsicInterior_of_closure_eq hf hclosure
  let t : ℝ := (∑ i, |(f i x).toReal|) + 1
  refine ⟨(x, t), fun i ↦ ?_⟩
  apply mem_intrinsicInterior_epigraph_of_strict_height (hf i) (hx i)
  have hxD : x ∈ effectiveDomain (f i) := intrinsicInterior_subset (hx i)
  have hvalue : f i x = ((f i x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hxD) ((hf i).2.2 _)).symm
  have hbound : |(f i x).toReal| ≤ ∑ j, |(f j x).toReal| :=
    Finset.single_le_sum (f := fun j ↦ |(f j x).toReal|)
      (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  rw [hvalue]
  apply EReal.coe_lt_coe
  dsimp [t]
  have h := le_abs_self (f i x).toReal
  linarith

omit [FiniteDimensional ℝ E] in
/-- Actual horizontal covector obtained by restriction to height zero. -/
noncomputable def epigraphHorizontal (L : StrongDual ℝ (E × ℝ)) : StrongDual ℝ E :=
  L.comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [FiniteDimensional ℝ E] in
/-- The actual height coefficient of an actual product covector. -/
def epigraphHeight (L : StrongDual ℝ (E × ℝ)) : ℝ := L (0, 1)

omit [FiniteDimensional ℝ E] in
/-- Actual horizontal and height coefficients decompose the actual product covector. -/
theorem epigraph_covector_decompose (L : StrongDual ℝ (E × ℝ)) (x : E) (r : ℝ) :
    L (x, r) = epigraphHorizontal L x + epigraphHeight L * r := by
  have heq : (x, r) = (x, (0 : ℝ)) + r • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  rw [heq, map_add, map_smul]
  simp only [epigraphHorizontal, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, epigraphHeight, smul_eq_mul]
  rw [mul_comm]

omit [FiniteDimensional ℝ E] in
/-- Actual product covector with its specified horizontal and height coefficients. -/
noncomputable def epigraphCovector (m : StrongDual ℝ E) (a : ℝ) : StrongDual ℝ (E × ℝ) :=
  m.comp (ContinuousLinearMap.fst ℝ E ℝ) + a • ContinuousLinearMap.snd ℝ E ℝ

omit [FiniteDimensional ℝ E] in
theorem epigraphCovector_apply (m : StrongDual ℝ E) (a : ℝ) (x : E) (r : ℝ) :
    epigraphCovector m a (x, r) = m x + a * r := rfl

omit [FiniteDimensional ℝ E] in
/-- Actual finite support bounds are precisely actual real epigraph inequalities. -/
theorem support_epigraph_le_coe_iff (f : E → EReal) (L : StrongDual ℝ (E × ℝ)) (c : ℝ) :
    support continuousDualPairing (epigraph f) L ≤ (c : EReal) ↔
      ∀ (x : E) (r : ℝ), f x ≤ (r : EReal) → L (x, r) ≤ c := by
  change (⨆ p : epigraph f, (L p : EReal)) ≤ (c : EReal) ↔ _
  rw [iSup_le_iff]
  constructor
  · intro h x r hxr
    exact EReal.coe_le_coe_iff.mp (h ⟨(x, r), hxr⟩)
  · intro h p
    exact EReal.coe_le_coe (h p.val.1 p.val.2 p.property)

omit [FiniteDimensional ℝ E] in
/-- Upward actual epigraph heights force the actual height coefficient to be nonpositive. -/
theorem epigraphHeight_nonpos_of_support_le {f : E → EReal} (hf : IsProper f)
    (L : StrongDual ℝ (E × ℝ)) {c : ℝ}
    (hbound : support continuousDualPairing (epigraph f) L ≤ (c : EReal)) :
    epigraphHeight L ≤ 0 := by
  obtain ⟨x, hx⟩ := hf.2.1
  let u := (f x).toReal
  have hfx : f x = (u : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 _)).symm
  have h := (support_epigraph_le_coe_iff f L c).mp hbound
  by_contra hn
  have ha : 0 < epigraphHeight L := lt_of_not_ge hn
  let r := max u ((c - epigraphHorizontal L x) / epigraphHeight L + 1)
  have hxr : f x ≤ (r : EReal) := by
    rw [hfx]
    exact EReal.coe_le_coe (le_max_left _ _)
  have hupper := h x r hxr
  rw [epigraph_covector_decompose] at hupper
  have hlower := mul_le_mul_of_nonneg_left
    (le_max_right u ((c - epigraphHorizontal L x) / epigraphHeight L + 1)) ha.le
  have heq : epigraphHeight L *
      ((c - epigraphHorizontal L x) / epigraphHeight L + 1) =
        c - epigraphHorizontal L x + epigraphHeight L := by
    field_simp
  rw [heq] at hlower
  change c - epigraphHorizontal L x + epigraphHeight L ≤ epigraphHeight L * r at hlower
  linarith

omit [FiniteDimensional ℝ E] in
/-- The actual negative-unit-height epigraph support is the actual conjugate,
including both original infinite obstacle values. -/
theorem support_epigraph_negative_one (f : E → EReal) (m : StrongDual ℝ E) :
    support continuousDualPairing (epigraph f) (epigraphCovector m (-1)) =
      conjugate continuousDualPairing f m := by
  apply le_antisymm
  · apply iSup_le
    intro p
    change (epigraphCovector m (-1) p.val : EReal) ≤ _
    rw [epigraphCovector_apply, neg_one_mul, ← sub_eq_add_neg]
    have h := EReal.sub_le_sub (le_refl (m p.val.1 : EReal)) p.property
    rw [← EReal.coe_sub] at h
    exact h.trans (le_iSup (fun x ↦ (m x : EReal) - f x) p.val.1)
  · apply iSup_le
    intro x
    change (m x : EReal) - f x ≤ _
    cases hfx : f x using EReal.rec with
    | bot =>
      rw [EReal.coe_sub_bot]
      apply EReal.ge_of_forall_gt_iff_ge.mp
      intro c _
      have hp : (x, m x - c) ∈ epigraph f := by simp [epigraph, hfx]
      have heq : epigraphCovector m (-1) (x, m x - c) = c := by
        rw [epigraphCovector_apply]
        ring
      apply le_iSup_of_le (⟨(x, m x - c), hp⟩ : epigraph f)
      change (c : EReal) ≤ (epigraphCovector m (-1) (x, m x - c) : EReal)
      rw [heq]
    | coe u =>
      have hp : (x, u) ∈ epigraph f := hfx.le
      apply le_iSup_of_le (⟨(x, u), hp⟩ : epigraph f)
      change (m x : EReal) - (u : EReal) ≤
        (epigraphCovector m (-1) (x, u) : EReal)
      rw [epigraphCovector_apply, neg_one_mul, ← sub_eq_add_neg, EReal.coe_sub]
    | top => simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The actual epigraph of a maximum is the actual intersection of epigraphs. -/
theorem epigraph_convexSup {I : Type*} (f : I → E → EReal) :
    epigraph (convexSup f) = ⋂ i, epigraph (f i) := by
  ext p
  rw [mem_iInter]
  change (⨆ i, f i p.1) ≤ (p.2 : EReal) ↔ ∀ i, f i p.1 ≤ (p.2 : EReal)
  exact iSup_le_iff

/-- The actual finite sum of set indicators is the actual intersection indicator. -/
theorem sum_indicator_eq_indicator_iInter {V : Type*} {I : Type*} [Fintype I]
    (A : I → Set V) : (fun x ↦ ∑ i, indicator (A i) x) = indicator (⋂ i, A i) := by
  classical
  funext x
  by_cases hx : ∀ i, x ∈ A i
  · simp [indicator, hx]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hsingle := Finset.single_le_sum (f := fun j ↦ indicator (A j) x)
      (fun j _ ↦ by simp [indicator]; split_ifs <;> simp) (Finset.mem_univ i)
    have htop : indicator (A i) x = ⊤ := by simp [indicator, hi]
    have hnot : x ∉ ⋂ i, A i := by simpa only [mem_iInter] using hx
    rw [htop] at hsingle
    simp only [indicator, if_neg hnot]
    exact top_unique hsingle

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Actual epigraph indicators sum to the actual maximum epigraph indicator. -/
theorem sum_indicator_epigraph {I : Type*} [Fintype I] (f : I → E → EReal) :
    (fun p ↦ ∑ i, indicator (epigraph (f i)) p) = indicator (epigraph (convexSup f)) := by
  rw [sum_indicator_eq_indicator_iInter, epigraph_convexSup]

omit [FiniteDimensional ℝ E] in
/-- The actual epigraph of a proper convex function has a proper indicator. -/
theorem isProper_indicator_epigraph {f : E → EReal} (hf : IsProper f) :
    IsProper (indicator (epigraph f)) := by
  apply (isProper_indicator_iff hf.1).mpr
  obtain ⟨x, hx⟩ := hf.2.1
  refine ⟨(x, (f x).toReal), ?_⟩
  change f x ≤ ((f x).toReal : EReal)
  exact (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 _)).symm.le

/-- True qualified indicator conjugation produces actual finite epigraph
covectors, not assumed support-cost witnesses. -/
theorem exists_finite_epigraph_split {I : Type*} [Fintype I] [Nonempty I]
    {f : I → E → EReal} (hf : ∀ i, IsProper (f i))
    (hclosure : ∀ i j, closure (effectiveDomain (f i)) = closure (effectiveDomain (f j)))
    (m : StrongDual ℝ E) (htop : conjugate continuousDualPairing (convexSup f) m ≠ ⊤) :
    ∃ (L : I → StrongDual ℝ (E × ℝ)) (c : I → ℝ),
      (∑ i, L i) = epigraphCovector m (-1) ∧
      (∀ i, support continuousDualPairing (epigraph (f i)) (L i) = (c i : EReal)) ∧
      ((∑ i, c i : ℝ) : EReal) = conjugate continuousDualPairing (convexSup f) m := by
  classical
  obtain ⟨p, hp⟩ := exists_common_intrinsicInterior_epigraph_of_closure_eq hf hclosure
  have hi : ∀ i, IsProper (indicator (epigraph (f i))) :=
    fun i ↦ isProper_indicator_epigraph (hf i)
  have hpi : ∀ i, p ∈ intrinsicInterior ℝ (effectiveDomain (indicator (epigraph (f i)))) := by
    simpa only [effectiveDomain_indicator] using hp
  have hconj : conjugate continuousDualPairing
      (fun p ↦ ∑ i, indicator (epigraph (f i)) p) (epigraphCovector m (-1)) =
        conjugate continuousDualPairing (convexSup f) m := by
    rw [sum_indicator_epigraph, conjugate_indicator, support_epigraph_negative_one]
  obtain ⟨L, hL, hcost⟩ := exists_split_finset_of_conjugate_ne_top
    (fun i ↦ indicator (epigraph (f i))) Finset.univ Finset.univ_nonempty
    (fun i _ ↦ hi i) (fun i _ ↦ hpi i) (epigraphCovector m (-1)) (hconj.trans_ne htop)
  have hcost' : (∑ i, support continuousDualPairing (epigraph (f i)) (L i)) =
      conjugate continuousDualPairing (convexSup f) m := by
    simpa only [conjugate_indicator, hconj] using hcost
  have hnobot : ∀ i, support continuousDualPairing (epigraph (f i)) (L i) ≠ ⊥ := by
    intro i
    exact ((isProper_support_iff_nonempty continuousDualPairing (epigraph (f i))).mpr
      ⟨p, intrinsicInterior_subset (hp i)⟩).2.2 _
  have hnotop := forall_ne_top_of_sum_ne_top _ hnobot (hcost'.trans_ne htop)
  let c : I → ℝ := fun i ↦ (support continuousDualPairing (epigraph (f i)) (L i)).toReal
  have hc : ∀ i, support continuousDualPairing (epigraph (f i)) (L i) = (c i : EReal) :=
    fun i ↦ (EReal.coe_toReal (hnotop i) (hnobot i)).symm
  refine ⟨L, c, hL, hc, ?_⟩
  rw [← hcost']
  simp only [hc]
  exact map_sum (⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) c Finset.univ

omit [FiniteDimensional ℝ E] in
/-- True finite support bounds hold at the actual finite graph heights. -/
theorem epigraph_coeff_bound {f : E → EReal} (hf : IsProper f)
    (L : StrongDual ℝ (E × ℝ)) {c : ℝ}
    (hc : support continuousDualPairing (epigraph f) L ≤ (c : EReal))
    {x : E} (hx : x ∈ effectiveDomain f) :
    epigraphHorizontal L x + epigraphHeight L * (f x).toReal ≤ c := by
  have hfx : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 _)).symm
  have h := (support_epigraph_le_coe_iff f L c).mp hc x (f x).toReal hfx.le
  simpa only [epigraph_covector_decompose] using h

omit [FiniteDimensional ℝ E] in
/-- A genuine continuous linear halfspace bound persists on the actual domain closure. -/
theorem linear_bound_on_closure_effectiveDomain {f : E → EReal}
    (n : StrongDual ℝ E) (c : ℝ)
    (hb : ∀ x ∈ effectiveDomain f, n x ≤ c) {x : E}
    (hx : x ∈ closure (effectiveDomain f)) : n x ≤ c := by
  exact (closure_minimal (by intro y hy; exact hb y hy)
    (isClosed_le n.continuous continuous_const)) hx

omit [FiniteDimensional ℝ E] in
/-- Actual coincident domain closures transport actual continuous halfspace bounds. -/
theorem linear_bound_transfer_of_closure_eq {f g : E → EReal}
    (n : StrongDual ℝ E) (c : ℝ)
    (hcl : closure (effectiveDomain f) = closure (effectiveDomain g))
    (hb : ∀ x ∈ effectiveDomain f, n x ≤ c) {x : E}
    (hx : x ∈ effectiveDomain g) : n x ≤ c := by
  apply linear_bound_on_closure_effectiveDomain n c hb
  rw [hcl]
  exact subset_closure hx

omit [FiniteDimensional ℝ E] in
/-- Positive epigraph weight bounds produce an actual conjugate-domain point. -/
theorem conjugate_le_of_weighted_domain_bound {f : E → EReal} (hf : IsProper f)
    (n : StrongDual ℝ E) {w c : ℝ} (hw : 0 < w)
    (hb : ∀ x ∈ effectiveDomain f, n x - w * (f x).toReal ≤ c) :
    conjugate continuousDualPairing f (w⁻¹ • n) ≤ ((c / w : ℝ) : EReal) := by
  apply (conjugate_le_coe_iff continuousDualPairing f (w⁻¹ • n) (c / w)).mpr
  intro x
  by_cases hx : x ∈ effectiveDomain f
  · have hfx : f x = ((f x).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 _)).symm
    change (((w⁻¹ • n) x - c / w : ℝ) : EReal) ≤ f x
    rw [hfx]
    apply EReal.coe_le_coe
    have heq : (w⁻¹ • n) x - c / w = (n x - c) / w := by
      simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [heq]
    apply (div_le_iff₀ hw).mpr
    have h := hb x hx
    linarith
  · have htop : f x = ⊤ := eq_top_iff.mpr (le_of_not_gt hx)
    rw [htop]
    exact le_top

/-- Actual zero-weight contributions are retained in one designated positive slot. -/
noncomputable def absorbZeroWeights {I W : Type*} [Fintype I] [AddCommMonoid W]
    (w : I → ℝ) (i₀ : I) (a : I → W) (i : I) : W := by
  classical
  exact (if w i = 0 then 0 else a i) +
    (if i = i₀ then ∑ j ∈ Finset.univ.filter (fun j ↦ w j = 0), a j else 0)

/-- Actual absorption preserves the actual total, including all zero-weight contributions. -/
theorem sum_absorbZeroWeights {I W : Type*} [Fintype I] [AddCommMonoid W]
    (w : I → ℝ) (i₀ : I) (a : I → W) :
    (∑ i, absorbZeroWeights w i₀ a i) = ∑ i, a i := by
  classical
  unfold absorbZeroWeights
  rw [Finset.sum_add_distrib]
  have hleft : (∑ i, if w i = 0 then 0 else a i) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ w i ≠ 0), a i := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add]
  have hright : (∑ i, if i = i₀ then
      ∑ j ∈ Finset.univ.filter (fun j ↦ w j = 0), a j else 0) =
        ∑ j ∈ Finset.univ.filter (fun j ↦ w j = 0), a j := by simp
  rw [hleft, hright, add_comm]
  exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ w i = 0) a

/-- A zero-weight slot is genuinely zero after absorption into a positive slot. -/
theorem absorbZeroWeights_eq_zero {I W : Type*} [Fintype I] [AddCommMonoid W]
    (w : I → ℝ) {i₀ i : I} (a : I → W) (hi₀ : 0 < w i₀) (hi : w i = 0) :
    absorbZeroWeights w i₀ a i = 0 := by
  classical
  have hne : i ≠ i₀ := by intro h; subst i; linarith
  simp [absorbZeroWeights, hi, hne]

/-- Positive slots retain their original contribution and the designated slot receives the zeros. -/
theorem absorbZeroWeights_eq_of_pos {I W : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid W]
    (w : I → ℝ) (i₀ : I) (a : I → W) {i : I} (hi : 0 < w i) :
    absorbZeroWeights w i₀ a i = a i +
      (if i = i₀ then ∑ j ∈ Finset.univ.filter (fun j ↦ w j = 0), a j else 0) := by
  classical
  by_cases h : i = i₀
  · subst i
    simp [absorbZeroWeights, ne_of_gt hi]
  · simp [absorbZeroWeights, ne_of_gt hi, h]

omit [FiniteDimensional ℝ E] in
/-- A true product-covector split gives the actual horizontal sum and total weight one. -/
theorem epigraph_coefficients_sum {I : Type*} [Fintype I]
    (L : I → StrongDual ℝ (E × ℝ)) (m : StrongDual ℝ E)
    (hL : (∑ i, L i) = epigraphCovector m (-1)) :
    (∑ i, epigraphHorizontal (L i)) = m ∧ (∑ i, -epigraphHeight (L i)) = 1 := by
  constructor
  · ext x
    have h := congrArg (fun ℓ : StrongDual ℝ (E × ℝ) ↦ ℓ (x, 0)) hL
    simpa [epigraphHorizontal, epigraphCovector_apply] using h
  · have h := congrArg (fun ℓ : StrongDual ℝ (E × ℝ) ↦ ℓ (0, 1)) hL
    have hs : (∑ i, epigraphHeight (L i)) = -1 := by
      simpa [epigraphHeight, epigraphCovector_apply] using h
    rw [Finset.sum_neg_distrib, hs]
    norm_num

omit [FiniteDimensional ℝ E] in
/-- Every genuine zero-weight epigraph covector bound transfers through the
actual common domain closures and is absorbed into the actual positive slot. -/
theorem absorb_epigraph_weighted_bound {I : Type*} [Fintype I]
    {f : I → E → EReal} (hf : ∀ i, IsProper (f i))
    (hclosure : ∀ i j, closure (effectiveDomain (f i)) = closure (effectiveDomain (f j)))
    (L : I → StrongDual ℝ (E × ℝ)) (c : I → ℝ)
    (hc : ∀ i, support continuousDualPairing (epigraph (f i)) (L i) ≤ (c i : EReal))
    (i₀ : I) {i : I}
    (hi : 0 < -epigraphHeight (L i)) {x : E} (hx : x ∈ effectiveDomain (f i)) :
    (absorbZeroWeights (fun j ↦ -epigraphHeight (L j)) i₀
      (fun j ↦ epigraphHorizontal (L j)) i) x -
        (-epigraphHeight (L i)) * (f i x).toReal ≤
      absorbZeroWeights (fun j ↦ -epigraphHeight (L j)) i₀ c i := by
  classical
  rw [absorbZeroWeights_eq_of_pos (fun j ↦ -epigraphHeight (L j)) i₀
    (fun j ↦ epigraphHorizontal (L j)) hi,
    absorbZeroWeights_eq_of_pos (fun j ↦ -epigraphHeight (L j)) i₀ c hi]
  by_cases hii₀ : i = i₀
  · subst i
    simp only [ite_true, add_apply, sum_apply]
    have hz : (∑ j ∈ Finset.univ.filter (fun j ↦ -epigraphHeight (L j) = 0),
        epigraphHorizontal (L j) x) ≤
          ∑ j ∈ Finset.univ.filter (fun j ↦ -epigraphHeight (L j) = 0), c j := by
      apply Finset.sum_le_sum
      intro j hj
      have hheight : epigraphHeight (L j) = 0 := by
        have hzero := (Finset.mem_filter.mp hj).2
        linarith
      apply linear_bound_transfer_of_closure_eq (epigraphHorizontal (L j)) (c j)
        (hclosure j i₀) ?_ hx
      intro y hy
      have h := epigraph_coeff_bound (hf j) (L j) (hc j) hy
      simpa only [hheight, zero_mul, add_zero] using h
    have h := epigraph_coeff_bound (hf i₀) (L i₀) (hc i₀) hx
    linarith
  · simp only [if_neg hii₀, add_zero]
    have h := epigraph_coeff_bound (hf i) (L i) (hc i) hx
    linarith

/-- Actual finite epigraph support witnesses construct an actual weighted
rooftop tuple, with zero weights absorbed through genuine domain closures. -/
theorem exists_rooftopData_of_epigraph_split {I : Type*} [Fintype I]
    {f : I → E → EReal} (hf : ∀ i, IsProper (f i))
    (hclosure : ∀ i j, closure (effectiveDomain (f i)) = closure (effectiveDomain (f j)))
    (m : StrongDual ℝ E) (L : I → StrongDual ℝ (E × ℝ)) (c : I → ℝ)
    (hL : (∑ i, L i) = epigraphCovector m (-1))
    (hc : ∀ i, support continuousDualPairing (epigraph (f i)) (L i) ≤ (c i : EReal)) :
    ∃ d : RooftopData (fun i ↦ conjugate continuousDualPairing (f i)),
      d.barycenter = m ∧ d.cost ≤ ∑ i, c i := by
  classical
  let w : I → ℝ := fun i ↦ -epigraphHeight (L i)
  obtain ⟨hn_sum, hw_sum⟩ := epigraph_coefficients_sum L m hL
  have hw_nonneg (i : I) : 0 ≤ w i :=
    neg_nonneg.mpr (epigraphHeight_nonpos_of_support_le (hf i) (L i) (hc i))
  have hpos : 0 < ∑ i, w i := by rw [hw_sum]; norm_num
  obtain ⟨i₀, _, hi₀⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hw_nonneg i)).mp hpos
  let n : I → StrongDual ℝ E := absorbZeroWeights w i₀ (fun i ↦ epigraphHorizontal (L i))
  let b : I → ℝ := absorbZeroWeights w i₀ c
  let g : I → StrongDual ℝ E → EReal := fun i ↦ conjugate continuousDualPairing (f i)
  have hg (i : I) : IsProper (g i) :=
    isProper_conjugate_of_isContPerfPair continuousDualPairing (hf i)
  choose q hq using fun i ↦ (hg i).2.1
  have hbound (i : I) (hi : 0 < w i) : g i ((w i)⁻¹ • n i) ≤ ((b i / w i : ℝ) : EReal) := by
    apply conjugate_le_of_weighted_domain_bound (hf i) (n i) hi
    intro x hx
    exact absorb_epigraph_weighted_bound hf hclosure L c hc i₀ hi hx
  let z : I → StrongDual ℝ E := fun i ↦ if 0 < w i then (w i)⁻¹ • n i else q i
  have hz (i : I) : z i ∈ effectiveDomain (g i) := by
    by_cases hi : 0 < w i
    · dsimp only [z]
      rw [if_pos hi]
      exact (hbound i hi).trans_lt (EReal.coe_lt_top _)
    · simpa only [z, if_neg hi] using hq i
  have hweighted (i : I) : w i • z i = n i := by
    by_cases hi : 0 < w i
    · simp only [z, if_pos hi, smul_smul, mul_inv_cancel₀ (ne_of_gt hi), one_smul]
    · have hi0 : w i = 0 := le_antisymm (le_of_not_gt hi) (hw_nonneg i)
      have hn0 : n i = 0 := absorbZeroWeights_eq_zero w _ hi₀ hi0
      simp only [hi0, zero_smul, hn0]
  have hcost (i : I) : w i * (g i (z i)).toReal ≤ b i := by
    by_cases hi : 0 < w i
    · have hreal : g i (z i) = ((g i (z i)).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt (hz i)) ((hg i).2.2 _)).symm
      have h : g i (z i) ≤ ((b i / w i : ℝ) : EReal) := by
        simpa only [z, if_pos hi] using hbound i hi
      rw [hreal] at h
      have h' := mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) hi.le
      have heq : w i * (b i / w i) = b i := by field_simp
      rwa [heq] at h'
    · have hi0 : w i = 0 := le_antisymm (le_of_not_gt hi) (hw_nonneg i)
      have hb0 : b i = 0 := absorbZeroWeights_eq_zero w _ hi₀ hi0
      simp only [hi0, zero_mul, hb0, le_refl]
  let d : RooftopData g := ⟨w, z, hw_nonneg, hw_sum, hz⟩
  refine ⟨d, ?_, ?_⟩
  · change (∑ i, w i • z i) = m
    rw [Finset.sum_congr rfl (fun i _ ↦ hweighted i)]
    exact (sum_absorbZeroWeights w i₀ _).trans hn_sum
  · change (∑ i, w i * (g i (z i)).toReal) ≤ ∑ i, c i
    exact (Finset.sum_le_sum (fun i _ ↦ hcost i)).trans_eq (sum_absorbZeroWeights w i₀ c)

/-- The source third finite-family identity uses coincident effective-domain
closures; the domains themselves can differ and need not be closed. -/
theorem conjugate_convexSup_eq_convexInf_of_closure_eq {I : Type*}
    [Fintype I] [Nonempty I] {f : I → E → EReal} (hf : ∀ i, IsProper (f i))
    (hclosure : ∀ i j, closure (effectiveDomain (f i)) = closure (effectiveDomain (f j))) :
    conjugate continuousDualPairing (convexSup f) =
      convexInf (fun i ↦ conjugate continuousDualPairing (f i)) := by
  apply le_antisymm
  · apply le_convexInf (isConvex_conjugate continuousDualPairing (convexSup f))
    intro i
    exact conjugate_antitone continuousDualPairing (fun x ↦ le_iSup (fun j ↦ f j x) i)
  · intro m
    by_cases htop : conjugate continuousDualPairing (convexSup f) m = ⊤
    · rw [htop]
      exact le_top
    obtain ⟨L, c, hL, hc, hcost⟩ := exists_finite_epigraph_split hf hclosure m htop
    obtain ⟨d, hd, hdcost⟩ := exists_rooftopData_of_epigraph_split hf hclosure m L c hL
      (fun i ↦ (hc i).le)
    rw [convexInf_eq_weightedRooftop (fun i ↦
      isProper_conjugate_of_isContPerfPair continuousDualPairing (hf i))]
    have h := weightedRooftop_le_cost d
    rw [hd] at h
    exact h.trans ((EReal.coe_le_coe hdcost).trans_eq hcost)

/-- Actual convex epigraphs pull back under the actual product linear map. -/
theorem isConvex_comp_linearMap {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {f : W → EReal} (hf : IsConvex f)
    (T : V →ₗ[ℝ] W) : IsConvex (fun x ↦ f (T x)) := by
  change Convex ℝ ((T.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ⁻¹' epigraph f)
  exact hf.linear_preimage _

/-- The actual convex rooftop transports through an actual linear equivalence. -/
theorem convexInf_comp_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {I : Type*} (f : I → W → EReal)
    (e : V ≃ₗ[ℝ] W) :
    convexInf (fun i x ↦ f i (e x)) = fun x ↦ convexInf f (e x) := by
  apply le_antisymm
  · have h : (fun y ↦ convexInf (fun i x ↦ f i (e x)) (e.symm y)) ≤ convexInf f := by
      apply le_convexInf (isConvex_comp_linearMap (isConvex_convexInf _) e.symm.toLinearMap)
      intro i y
      convert! convexInf_le (fun i x ↦ f i (e x)) i (e.symm y) using 1
      exact (congrArg (f i) (e.apply_symm_apply y)).symm
    intro x
    simpa only [e.symm_apply_apply] using h (e x)
  · apply le_convexInf (isConvex_comp_linearMap (isConvex_convexInf f) e.toLinearMap)
    intro i x
    exact convexInf_le f i (e x)

/-- Exact third source family identity for the actual arbitrary continuous
perfect pairing, transported through its genuine dual equivalence. -/
theorem conjugate_convexSup_eq_convexInf_of_isContPerfPair_of_closure_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {I : Type*} [Fintype I] [Nonempty I] {f : I → E → EReal}
    (hf : ∀ i, IsProper (f i))
    (hclosure : ∀ i j, closure (effectiveDomain (f i)) = closure (effectiveDomain (f j))) :
    conjugate B (convexSup f) = convexInf (fun i ↦ conjugate B (f i)) := by
  let e : F ≃ₗ[ℝ] StrongDual ℝ E := B.flip.toContPerfPair
  have hreindex (g : E → EReal) : conjugate B g =
      fun y ↦ conjugate continuousDualPairing g (e y) := rfl
  rw [hreindex, conjugate_convexSup_eq_convexInf_of_closure_eq hf hclosure]
  simpa only [hreindex] using
    (convexInf_comp_linearEquiv (fun i ↦ conjugate continuousDualPairing (f i)) e).symm

end SGPT.Convex
