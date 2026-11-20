import SGPT.Convex.RelativeInterior
import SGPT.Convex.FamilyOperations

/-!
# Actual supporting affine minorants and subgradients

Strict epigraph separation is carried out in its actual affine span. Thus
relative-interior points of lower-dimensional effective domains are included.
-/

namespace SGPT.Convex

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual strict epigraph, using real heights. -/
def strictEpigraph (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 < (p.2 : EReal)}

/-- Actual epigraph convexity also makes the actual strict epigraph convex. -/
theorem convex_strictEpigraph {f : E → EReal} (hf : IsConvex f) :
    Convex ℝ (strictEpigraph f) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hp
  exact isConvex_iff_strict_combo.mp hf p.1 q.1 p.2 q.2 a b hp hq
    (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)) hab

variable [FiniteDimensional ℝ E]

/-- A strict real height over an actual intrinsic-interior domain point is an
actual intrinsic-interior point of the strict epigraph. -/
theorem mem_intrinsicInterior_strictEpigraph {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    {r : ℝ} (hr : f x < (r : EReal)) :
    (x, r) ∈ intrinsicInterior ℝ (strictEpigraph f) := by
  let A := affineSpan ℝ (effectiveDomain f)
  let B := affineSpan ℝ (strictEpigraph f)
  let xA : A := ⟨x, subset_affineSpan ℝ _ (intrinsicInterior_subset hx)⟩
  let pB : B := ⟨(x, r), subset_affineSpan ℝ _ hr⟩
  have hBA : B ≤ A.prod ⊤ := by
    apply affineSpan_le.mpr
    intro p hp
    exact ⟨subset_affineSpan ℝ _ (hp.trans (EReal.coe_lt_top p.2)), by trivial⟩
  let P : B → A := fun p ↦ ⟨(p : E × ℝ).1, (hBA p.property).1⟩
  have hP : Continuous P :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hPx : P pB = xA := Subtype.ext rfl
  have hxA : xA ∈ interior ((↑) ⁻¹' effectiveDomain f : Set A) := by
    obtain ⟨y, hy, heq⟩ := mem_intrinsicInterior.mp hx
    have hyx : y = xA := Subtype.ext heq
    simpa only [hyx] using hy
  have hD : ∀ᶠ p : B in 𝓝 pB, (P p : E) ∈ effectiveDomain f := by
    have hxP : P pB ∈ interior ((↑) ⁻¹' effectiveDomain f : Set A) := hPx ▸ hxA
    exact hP.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hxP)
  have hfcont : ContinuousAt (fun p : B ↦ (f (P p)).toReal) pB := by
    apply ContinuousAt.comp (g := fun z : A ↦ (f z).toReal)
    · rw [hPx]
      exact continuousAt_toReal_affineSpan_of_mem_intrinsicInterior hf xA hx
    · exact hP.continuousAt
  have hheight : ContinuousAt (fun p : B ↦ (p : E × ℝ).2) pB :=
    (continuous_snd.comp continuous_subtype_val).continuousAt
  have hxD : x ∈ effectiveDomain f := intrinsicInterior_subset hx
  have hfinite : ((f x).toReal : EReal) = f x :=
    EReal.coe_toReal (ne_of_lt hxD) (hf.2.2 x)
  have hlt : (f (P pB)).toReal < (pB : E × ℝ).2 := by
    change (f x).toReal < r
    exact EReal.coe_lt_coe_iff.mp (by rwa [hfinite])
  have hstrict := hfcont.eventually_lt hheight hlt
  apply mem_intrinsicInterior.mpr
  refine ⟨pB, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  filter_upwards [hD, hstrict] with p hpD hpstrict
  change f (p : E × ℝ).1 < ((p : E × ℝ).2 : EReal)
  have hpfin : f (p : E × ℝ).1 = ((f (p : E × ℝ).1).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hpD) (hf.2.2 _)).symm
  rw [hpfin, EReal.coe_lt_coe_iff]
  exact hpstrict

/-- Strict-epigraph separation constructs a genuine continuous affine minorant
touching the obstacle at the actual intrinsic-interior domain point. -/
theorem exists_touching_continuous_affine_minorant {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) :
    ∃ (m : E →L[ℝ] ℝ) (b : ℝ),
      (∀ z, ((m z + b : ℝ) : EReal) ≤ f z) ∧ ((m x + b : ℝ) : EReal) = f x := by
  let u : ℝ := (f x).toReal
  have hxD : x ∈ effectiveDomain f := intrinsicInterior_subset hx
  have hfx : f x = (u : EReal) :=
    (EReal.coe_toReal (ne_of_lt hxD) (hf.2.2 x)).symm
  have hp : (x, u + 1) ∈ intrinsicInterior ℝ (strictEpigraph f) := by
    apply mem_intrinsicInterior_strictEpigraph hf hx
    rw [hfx, EReal.coe_lt_coe_iff]
    linarith
  let B := affineSpan ℝ (strictEpigraph f)
  have hpB : (x, u + 1) ∈ B := subset_affineSpan ℝ _ (intrinsicInterior_subset hp)
  have hp2B : (x, u + 2) ∈ B := by
    apply subset_affineSpan ℝ (strictEpigraph f)
    change f x < ((u + 2 : ℝ) : EReal)
    rw [hfx, EReal.coe_lt_coe_iff]
    linarith
  have hvertical : ((0 : E), (1 : ℝ)) ∈ B.direction := by
    have h := B.vsub_mem_direction hp2B hpB
    have h' : ((0 : E), (2 - 1 : ℝ)) ∈ B.direction := by
      simpa [vsub_eq_sub] using h
    norm_num at h'
    exact h'
  have hqB : (x, u) ∈ B := by
    have h := B.vadd_mem_of_mem_direction (B.direction.smul_mem (-1 : ℝ) hvertical) hpB
    convert h using 1
    ext <;> simp [vadd_eq_add]
  have hqnot : (x, u) ∉ strictEpigraph f := by
    change ¬ f x < (u : EReal)
    rw [hfx]
    exact lt_irrefl _
  obtain ⟨L, hstrict, hsep⟩ := exists_functional_of_mem_intrinsicInterior
    (convex_strictEpigraph hf.1) hp hqB hqnot
  let a : ℝ := L (0, 1)
  have hsplit (z : E) (r : ℝ) : L (z, r) = L (z, 0) + r * a := by
    have heq : (z, r) = (z, (0 : ℝ)) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [heq, map_add, map_smul]
    rfl
  have ha : 0 < a := by
    rw [hsplit x u, hsplit x (u + 1)] at hstrict
    linarith
  let ℓ : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let m : E →L[ℝ] ℝ := (-a⁻¹) • ℓ
  let b : ℝ := L (x, u) / a
  have hvalue (z : E) : m z + b = (L (x, u) - L (z, 0)) / a := by
    simp only [m, b, ℓ, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  refine ⟨m, b, ?_, ?_⟩
  · intro z
    cases hz : f z using EReal.rec with
    | bot => exact False.elim (hf.2.2 z hz)
    | top => exact le_top
    | coe c =>
      rw [EReal.coe_le_coe_iff]
      apply le_of_not_gt
      intro hc
      obtain ⟨r, hcr, hrm⟩ := exists_between hc
      have hzr : (z, r) ∈ strictEpigraph f := by
        change f z < (r : EReal)
        rw [hz, EReal.coe_lt_coe_iff]
        exact hcr
      have h := hsep (z, r) hzr
      rw [hsplit z r] at h
      have hbound : m z + b ≤ r := by
        rw [hvalue, div_le_iff₀ ha]
        linarith
      exact not_le_of_gt hrm hbound
  · rw [hvalue, hsplit x u]
    have heq : (L (x, 0) + u * a - L (x, 0)) / a = u := by
      field_simp
      ring
    rw [heq, hfx]

section Subdifferential

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- Exact source `def:subgrad`, with its displayed raw inequality at every basepoint. -/
def rawSubdifferential (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) : Set M :=
  {m | ∀ y, f x + (B (y - x) m : EReal) ≤ f y}

/-- Exact source union of raw subdifferentials over actual primal points. -/
def rawSubgradientImage (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) : Set M :=
  ⋃ x, rawSubdifferential B f x

/-- Exact source subgradient image over every actual subset of primal points. -/
def rawSubgradientImageOn (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) (A : Set E) : Set M :=
  ⋃ x ∈ A, rawSubdifferential B f x

omit [FiniteDimensional ℝ E] in
/-- The full actual source image is its actual subset image over the whole space. -/
theorem rawSubgradientImageOn_univ (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) :
    rawSubgradientImageOn B f univ = rawSubgradientImage B f := by
  simp only [rawSubgradientImageOn, rawSubgradientImage, mem_univ, iUnion_true]

/-- Actual subgradients, with an explicit finite-domain basepoint convention.
The source uses this convention in its outside-domain emptiness theorem. -/
def subdifferential (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) : Set M :=
  {m | x ∈ effectiveDomain f ∧ ∀ y, f x + (B (y - x) m : EReal) ≤ f y}

/-- The actual union of subdifferentials over actual primal points. -/
def subgradientImage (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) : Set M :=
  ⋃ x, subdifferential B f x

omit [FiniteDimensional ℝ E] in
/-- The disclosed domain convention gives actual outside-domain emptiness. -/
theorem subdifferential_eq_empty_of_not_mem_effectiveDomain
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) (f : E → EReal) {x : E}
    (hx : x ∉ effectiveDomain f) : subdifferential B f x = ∅ := by
  ext m
  simp [subdifferential, hx]

omit [FiniteDimensional ℝ E] in
/-- For proper obstacles the explicit domain guard is redundant: an actual
finite domain witness rules out the raw inequality at a top-valued basepoint. -/
theorem mem_subdifferential_iff_raw_of_isProper (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ)
    {f : E → EReal} (hf : IsProper f) {x : E} {m : M} :
    m ∈ subdifferential B f x ↔ ∀ y, f x + (B (y - x) m : EReal) ≤ f y := by
  constructor
  · exact fun hm ↦ hm.2
  · intro h
    refine ⟨?_, h⟩
    change f x < ⊤
    by_contra hx
    have hxtop : f x = ⊤ := top_unique (le_of_not_gt hx)
    obtain ⟨y, hy⟩ := hf.2.1
    have hbad : (⊤ : EReal) ≤ f y := by
      simpa only [hxtop, EReal.top_add_coe] using h y
    exact not_le_of_gt hy hbad

omit [FiniteDimensional ℝ E] in
/-- Properness identifies the exact raw source definition with the finite-domain API. -/
theorem rawSubdifferential_eq_subdifferential_of_isProper
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f : E → EReal} (hf : IsProper f) (x : E) :
    rawSubdifferential B f x = subdifferential B f x := by
  ext m
  exact (mem_subdifferential_iff_raw_of_isProper B hf).symm

omit [FiniteDimensional ℝ E] in
/-- The exact raw source image equals the finite-domain image for every proper obstacle. -/
theorem rawSubgradientImage_eq_subgradientImage_of_isProper
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f : E → EReal} (hf : IsProper f) :
    rawSubgradientImage B f = subgradientImage B f := by
  simp only [rawSubgradientImage, subgradientImage,
    rawSubdifferential_eq_subdifferential_of_isProper B hf]

omit [FiniteDimensional ℝ E] in
/-- Source `thm:nablaF` outside-domain emptiness for the exact raw definition. -/
theorem rawSubdifferential_eq_empty_of_not_mem_effectiveDomain
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∉ effectiveDomain f) : rawSubdifferential B f x = ∅ := by
  rw [rawSubdifferential_eq_subdifferential_of_isProper B hf]
  exact subdifferential_eq_empty_of_not_mem_effectiveDomain B f hx

omit [FiniteDimensional ℝ E] in
/-- At an actual finite basepoint, subgradients are exactly actual Fenchel equality. -/
theorem mem_subdifferential_iff_fenchel (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ)
    {f : E → EReal} (hf : IsProper f) {x : E} (hx : x ∈ effectiveDomain f) {m : M} :
    m ∈ subdifferential B f x ↔ conjugate B f m = (B x m : EReal) - f x := by
  let u : ℝ := (f x).toReal
  have hfx : f x = (u : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 x)).symm
  have hvalue (y : E) :
      f x + (B (y - x) m : EReal) = ((B y m - (B x m - u) : ℝ) : EReal) := by
    rw [hfx, ← EReal.coe_add]
    congr 1
    simp only [map_sub, LinearMap.sub_apply]
    ring
  constructor
  · intro hm
    have hbound : conjugate B f m ≤ ((B x m - u : ℝ) : EReal) := by
      apply (conjugate_le_coe_iff B f m (B x m - u)).mpr
      intro y
      rw [← hvalue]
      exact hm.2 y
    apply le_antisymm
    · simpa only [hfx, ← EReal.coe_sub] using hbound
    · exact le_iSup (fun y ↦ (B y m : EReal) - f y) x
  · intro hm
    refine ⟨hx, ?_⟩
    have hbound : conjugate B f m ≤ ((B x m - u : ℝ) : EReal) := by
      rw [hm, hfx, ← EReal.coe_sub]
    have h := (conjugate_le_coe_iff B f m (B x m - u)).mp hbound
    intro y
    rw [hvalue]
    exact h y

omit [FiniteDimensional ℝ E] in
/-- Every actual subgradient lies in the actual effective domain of the conjugate. -/
theorem subgradientImage_subset_effectiveDomain_conjugate
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f : E → EReal} (hf : IsProper f) :
    subgradientImage B f ⊆ effectiveDomain (conjugate B f) := by
  intro m hm
  obtain ⟨x, hx⟩ := mem_iUnion.mp hm
  change conjugate B f m < ⊤
  rw [(mem_subdifferential_iff_fenchel B hf hx.1).mp hx]
  have hfx : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx.1) (hf.2.2 x)).symm
  rw [hfx, ← EReal.coe_sub]
  exact EReal.coe_lt_top _

omit [FiniteDimensional ℝ E] in
/-- Source `prop:gradDomFstar` first clause for the exact raw subgradient image. -/
theorem rawSubgradientImage_subset_effectiveDomain_conjugate
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) {f : E → EReal} (hf : IsProper f) :
    rawSubgradientImage B f ⊆ effectiveDomain (conjugate B f) := by
  rw [rawSubgradientImage_eq_subgradientImage_of_isProper B hf]
  exact subgradientImage_subset_effectiveDomain_conjugate B hf

end Subdifferential

section PerfectPairing

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- Actual touching affine minorants give actual covectors under a genuine
continuous perfect pairing. -/
theorem subdifferential_nonempty_of_mem_intrinsicInterior
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) :
    (subdifferential B f x).Nonempty := by
  obtain ⟨ℓ, b, hminor, htouch⟩ := exists_touching_continuous_affine_minorant hf hx
  obtain ⟨m, hm⟩ := B.flip.toContPerfPair.surjective ℓ
  have hvalue (y : E) : B y m = ℓ y := by
    simpa only [LinearMap.toContPerfPair_apply, LinearMap.flip_apply] using
      congrArg (fun L : StrongDual ℝ E ↦ L y) hm
  refine ⟨m, intrinsicInterior_subset hx, ?_⟩
  intro y
  convert hminor y using 1
  rw [← htouch, ← EReal.coe_add, hvalue, map_sub]
  congr 1
  ring

/-- Source relative-interior nonemptiness for the exact raw subdifferential. -/
theorem rawSubdifferential_nonempty_of_mem_intrinsicInterior
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) :
    (rawSubdifferential B f x).Nonempty := by
  rw [rawSubdifferential_eq_subdifferential_of_isProper B hf]
  exact subdifferential_nonempty_of_mem_intrinsicInterior B hf hx

/-- Properness of the actual conjugate for a genuine continuous perfect pairing. -/
theorem isProper_conjugate_of_isContPerfPair
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f) : IsProper (conjugate B f) := by
  obtain ⟨ℓ, b, hminor⟩ := exists_continuous_affine_minorant_of_isProper hf
  obtain ⟨m, hm⟩ := B.flip.toContPerfPair.surjective ℓ
  have hvalue (y : E) : B y m = ℓ y := by
    simpa only [LinearMap.toContPerfPair_apply, LinearMap.flip_apply] using
      congrArg (fun L : StrongDual ℝ E ↦ L y) hm
  have hbound : conjugate B f m ≤ ((-b : ℝ) : EReal) := by
    apply (conjugate_le_coe_iff B f m (-b)).mpr
    intro y
    simpa only [hvalue y, sub_neg_eq_add] using hminor y
  obtain ⟨x, hx⟩ := hf.2.1
  exact ⟨isConvex_conjugate B f,
    ⟨m, hbound.trans_lt (EReal.coe_lt_top _)⟩,
    conjugate_ne_bot_of_exists_ne_top B f ⟨x, ne_of_lt hx⟩⟩

variable [FiniteDimensional ℝ M]

/-- The actual relative interior of the conjugate domain is represented by
actual original subgradients for proper lower semicontinuous obstacles. -/
theorem intrinsicInterior_effectiveDomain_conjugate_subset_subgradientImage
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    intrinsicInterior ℝ (effectiveDomain (conjugate B f)) ⊆ subgradientImage B f := by
  intro m hm
  have hg := isProper_conjugate_of_isContPerfPair B hf
  obtain ⟨x, hx⟩ := subdifferential_nonempty_of_mem_intrinsicInterior B.flip hg hm
  have hb : conjugate B.flip (conjugate B f) = f :=
    (biconjugate_eq_convexClosure_of_isContPerfPair B hf.1).trans
      (convexClosure_eq_self_of_isClosedConvex (Or.inr (Or.inr ⟨hf, hlsc⟩)))
  have hxf : f x = (B x m : EReal) - conjugate B f m := by
    simpa only [hb, LinearMap.flip_apply] using
      (mem_subdifferential_iff_fenchel B.flip hg hx.1).mp hx
  let v : ℝ := (conjugate B f m).toReal
  have hmD : m ∈ effectiveDomain (conjugate B f) := intrinsicInterior_subset hm
  have hgm : conjugate B f m = (v : EReal) :=
    (EReal.coe_toReal (ne_of_lt hmD) (hg.2.2 m)).symm
  have hxvalue : f x = ((B x m - v : ℝ) : EReal) := by
    rw [hxf, hgm, ← EReal.coe_sub]
  have hxD : x ∈ effectiveDomain f := by
    change f x < ⊤
    rw [hxvalue]
    exact EReal.coe_lt_top _
  apply mem_iUnion.mpr
  refine ⟨x, (mem_subdifferential_iff_fenchel B hf hxD).mpr ?_⟩
  rw [hxvalue, hgm, ← EReal.coe_sub]
  congr 1
  ring

/-- Source `prop:gradDomFstar` reverse relative-interior inclusion for its exact raw image. -/
theorem intrinsicInterior_effectiveDomain_conjugate_subset_rawSubgradientImage
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    intrinsicInterior ℝ (effectiveDomain (conjugate B f)) ⊆ rawSubgradientImage B f := by
  rw [rawSubgradientImage_eq_subgradientImage_of_isProper B hf]
  exact intrinsicInterior_effectiveDomain_conjugate_subset_subgradientImage B hf hlsc

end PerfectPairing

/-- Actual convex open segments make the actual intrinsic interior dense in
the actual convex set, including the empty set. -/
theorem closure_intrinsicInterior_eq_closure_of_convex {C : Set E} (hC : Convex ℝ C) :
    _root_.closure (intrinsicInterior ℝ C) = _root_.closure C := by
  apply subset_antisymm (_root_.closure_mono intrinsicInterior_subset)
  by_cases hne : C.Nonempty
  · obtain ⟨w, hw⟩ := hne.intrinsicInterior hC
    apply closure_minimal _ isClosed_closure
    intro y hy
    have hseg : openSegment ℝ y w ⊆ intrinsicInterior ℝ C := by
      rintro z ⟨a, b, ha, hb, hab, rfl⟩
      simpa only [add_comm] using
        combo_mem_intrinsicInterior hC hw hy hb ha.le (by linarith : b + a = 1)
    exact _root_.closure_mono hseg
      (segment_subset_closure_openSegment (left_mem_segment ℝ y w))
  · have h_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [h_empty]

/-- Exact source closure equality for the actual subgradient image, with the
explicit finite-domain basepoint convention. -/
theorem closure_subgradientImage_eq_closure_effectiveDomain_conjugate
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    _root_.closure (subgradientImage B f) = _root_.closure (effectiveDomain (conjugate B f)) := by
  apply subset_antisymm (_root_.closure_mono (subgradientImage_subset_effectiveDomain_conjugate B hf))
  rw [← closure_intrinsicInterior_eq_closure_of_convex
    (convex_effectiveDomain (isConvex_conjugate B f))]
  exact _root_.closure_mono
    (intrinsicInterior_effectiveDomain_conjugate_subset_subgradientImage B hf hlsc)

/-- Exact final closure equality in source `prop:gradDomFstar`, using its raw image. -/
theorem closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : E → EReal} (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    _root_.closure (rawSubgradientImage B f) =
      _root_.closure (effectiveDomain (conjugate B f)) := by
  rw [rawSubgradientImage_eq_subgradientImage_of_isProper B hf]
  exact closure_subgradientImage_eq_closure_effectiveDomain_conjugate B hf hlsc

end SGPT.Convex
