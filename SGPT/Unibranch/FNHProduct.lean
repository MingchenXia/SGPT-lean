import SGPT.Unibranch.FNHCore
import SGPT.Unibranch.FNSHull

/-!
# Branched-covering charts of `X × ℂ`

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), proof of Theorem 5.3.1 (`[FN80]`): "In a small neighborhood of `p`, we can
represent `S_j × ℂ` as a branched covering of `Δ^{j+1}` relative to suitable coordinates in
`ℂ^{n+1}` (as in Lemma 5.2)". Used for SGPT `thm:FN` (2) ⇒ (1) (`appendix_unibranch.tex`).

We realize `ℂ × ℂⁿ` as `ComplexModel (n + 1)` with `w` the coordinate `0` and `z` the coordinates
`i.succ` (the `zpart`, `mkPt`). For `B ⊆ ℂ` and `S ⊆ ℂᵐ` put
`wprod B S = {x | x 0 ∈ B, zpart x ∈ S} = B × S`.

* `IsBranchedCovering.wprod`: if `Z → D` is a `λ`-sheeted branched covering under the projection
  to the first `d` coordinates, then `B × Z → B × D` is a `λ`-sheeted branched covering under the
  projection to the first `d + 1` coordinates (discriminant `δ ∘ zpart`).
* `hasCoveringChartAt_zpart_preimage`: a branched-covering chart (`FNL.HasCoveringChartAt`) of
  `X ⊆ ℂⁿ` at `z` gives one of `X × ℂ = zpart⁻¹(X)` at every point `(w, z)`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Unibranch.FNR SGPT.Unibranch.FNL
open SGPT.Unibranch.FNS (zpart mkPt zpart_apply mkPt_zero mkPt_succ zpart_mkPt mkPt_zpart
  continuous_zpart differentiable_zpart continuous_mkPt differentiable_mkPt)

variable {n d : ℕ}

/-! ### Coordinates -/

theorem zpart_add (x y : ComplexModel (n + 1)) : zpart (x + y) = zpart x + zpart y := by
  ext i; simp

theorem zpart_smul (c : ℂ) (x : ComplexModel (n + 1)) : zpart (c • x) = c • zpart x := by
  ext i; simp

theorem ext_zpart {x y : ComplexModel (n + 1)} (h0 : x 0 = y 0) (h : zpart x = zpart y) :
    x = y := by
  rw [← mkPt_zpart x, ← mkPt_zpart y, h0, h]

theorem mkPt_injective_left (w : ℂ) : Function.Injective fun z : ComplexModel n => mkPt z w := by
  intro z z' h
  have := congrArg zpart h
  simpa using this

theorem continuous_coord0 : Continuous fun x : ComplexModel (n + 1) => x 0 :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).continuous

theorem differentiable_coord0 : Differentiable ℂ fun x : ComplexModel (n + 1) => x 0 :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).differentiable

theorem continuous_mkPt_left (w : ℂ) : Continuous fun z : ComplexModel n => mkPt z w :=
  continuous_mkPt.comp (continuous_id.prodMk continuous_const)

@[simp] theorem coordinateProjection_succ_zero (x : ComplexModel (n + 1)) :
    coordinateProjection (n + 1) (d + 1) x 0 = x 0 := by
  rw [coordinateProjection_apply, dif_pos (by simp)]
  rfl

@[simp] theorem zpart_coordinateProjection_succ (x : ComplexModel (n + 1)) :
    zpart (coordinateProjection (n + 1) (d + 1) x) = coordinateProjection n d (zpart x) := by
  ext i
  rw [zpart_apply, coordinateProjection_apply, coordinateProjection_apply]
  by_cases h : (i : ℕ) < n
  · rw [dif_pos (by simpa using h), dif_pos h]
    rfl
  · rw [dif_neg (by simpa using h), dif_neg h]

theorem coordinateProjection_succ_mkPt (z : ComplexModel n) (w : ℂ) :
    coordinateProjection (n + 1) (d + 1) (mkPt z w) = mkPt (coordinateProjection n d z) w :=
  ext_zpart (by simp) (by simp)

/-! ### Products `B × S` -/

/-- `B × S ⊆ ℂ × ℂᵐ = ℂ^{m+1}`. -/
def wprod {m : ℕ} (B : Set ℂ) (S : Set (ComplexModel m)) : Set (ComplexModel (m + 1)) :=
  {x | x 0 ∈ B ∧ zpart x ∈ S}

theorem mem_wprod {m : ℕ} {B : Set ℂ} {S : Set (ComplexModel m)} {x : ComplexModel (m + 1)} :
    x ∈ wprod B S ↔ x 0 ∈ B ∧ zpart x ∈ S :=
  Iff.rfl

theorem mkPt_mem_wprod {m : ℕ} {B : Set ℂ} {S : Set (ComplexModel m)} {z : ComplexModel m}
    {w : ℂ} : mkPt z w ∈ wprod B S ↔ w ∈ B ∧ z ∈ S := by
  simp [mem_wprod]

theorem isOpen_wprod {m : ℕ} {B : Set ℂ} {S : Set (ComplexModel m)} (hB : IsOpen B)
    (hS : IsOpen S) : IsOpen (wprod B S) :=
  (hB.preimage continuous_coord0).inter (hS.preimage continuous_zpart)

theorem mapsTo_wprod {B : Set ℂ} {Ω : Set (ComplexModel n)} {D : Set (ComplexModel d)}
    (h : MapsTo (coordinateProjection n d) Ω D) :
    MapsTo (coordinateProjection (n + 1) (d + 1)) (wprod B Ω) (wprod B D) := fun x hx =>
  ⟨by simpa using hx.1, by simpa using h hx.2⟩

theorem hasLocalEquationsOn_wprod {B : Set ℂ} (hB : IsOpen B) {Z Ω : Set (ComplexModel n)}
    (h : HasLocalEquationsOn Z Ω) : HasLocalEquationsOn (wprod B Z) (wprod B Ω) := by
  intro x hx
  obtain ⟨W, hW, hxW, M, g, hg, hiff⟩ := h (zpart x) hx.2
  refine ⟨wprod B W, isOpen_wprod hB hW, ⟨hx.1, hxW⟩, M, fun i y => g i (zpart y),
    fun i => (hg i).comp differentiable_zpart.differentiableOn fun y hy => hy.2, ?_⟩
  intro y hy
  rw [← hiff (zpart y) hy.2]
  exact ⟨fun h => h.2, fun h => ⟨hy.1, h⟩⟩

theorem fibre_wprod {B : Set ℂ} {Z : Set (ComplexModel n)} {y : ComplexModel (d + 1)}
    (hy : y 0 ∈ B) :
    fibre (wprod B Z) (coordinateProjection (n + 1) (d + 1)) y =
      (fun z => mkPt z (y 0)) '' fibre Z (coordinateProjection n d) (zpart y) := by
  ext x
  simp only [mem_fibre, mem_wprod, mem_image]
  constructor
  · rintro ⟨⟨-, hxZ⟩, hxy⟩
    refine ⟨zpart x, ⟨hxZ, by rw [← zpart_coordinateProjection_succ, hxy]⟩, ?_⟩
    rw [← hxy, coordinateProjection_succ_zero, mkPt_zpart]
  · rintro ⟨z, ⟨hzZ, hzy⟩, rfl⟩
    refine ⟨⟨by simpa using hy, by simpa using hzZ⟩, ?_⟩
    rw [coordinateProjection_succ_mkPt, hzy, mkPt_zpart]

/-- **Products of branched coverings with a domain of `ℂ`.** -/
theorem isBranchedCovering_wprod {B : Set ℂ} (hB : IsOpen B) {Z : Set (ComplexModel n)}
    {D : Set (ComplexModel d)} {deg : ℕ} {δ : ComplexModel d → ℂ}
    (h : IsBranchedCovering Z (coordinateProjection n d) D deg δ) :
    IsBranchedCovering (FNH.wprod B Z) (coordinateProjection (n + 1) (d + 1)) (FNH.wprod B D)
      deg (fun y => δ (zpart y)) where
  isOpen_base := isOpen_wprod hB h.isOpen_base
  mapsTo := fun x hx => ⟨by simpa using hx.1, by simpa using h.mapsTo hx.2⟩
  isCompact_inter_preimage := by
    intro K hKD hK
    set K₁ : Set (ComplexModel d) := zpart '' K
    have hK₁ : IsCompact K₁ := hK.image continuous_zpart
    have hK₁D : K₁ ⊆ D := by rintro _ ⟨y, hy, rfl⟩; exact (hKD hy).2
    set C := Z ∩ coordinateProjection n d ⁻¹' K₁
    have hC : IsCompact C := h.isCompact_inter_preimage K₁ hK₁D hK₁
    have hK0 : IsCompact ((fun y : ComplexModel (d + 1) => y 0) '' K) :=
      hK.image continuous_coord0
    have hbig : IsCompact ((fun q : ComplexModel n × ℂ => mkPt q.1 q.2) ''
        (C ×ˢ ((fun y : ComplexModel (d + 1) => y 0) '' K))) :=
      (hC.prod hK0).image continuous_mkPt
    refine hbig.of_isClosed_subset ?_ ?_
    · have heq : FNH.wprod B Z ∩ coordinateProjection (n + 1) (d + 1) ⁻¹' K =
          zpart ⁻¹' C ∩ coordinateProjection (n + 1) (d + 1) ⁻¹' K := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_wprod]
        constructor
        · rintro ⟨⟨-, hxZ⟩, hxK⟩
          exact ⟨⟨hxZ, ⟨_, hxK, zpart_coordinateProjection_succ x⟩⟩, hxK⟩
        · rintro ⟨⟨hxZ, -⟩, hxK⟩
          exact ⟨⟨by simpa using (hKD hxK).1, hxZ⟩, hxK⟩
      rw [heq]
      exact (hC.isClosed.preimage continuous_zpart).inter
        (hK.isClosed.preimage (coordinateProjection (n + 1) (d + 1)).continuous)
    · rintro x ⟨⟨-, hxZ⟩, hxK⟩
      refine ⟨(zpart x, x 0), ⟨⟨hxZ, _, hxK, zpart_coordinateProjection_succ x⟩, ?_⟩,
        mkPt_zpart x⟩
      exact ⟨_, hxK, coordinateProjection_succ_zero x⟩
  finite_fibre := by
    intro y hy
    rw [fibre_wprod hy.1]
    exact (h.finite_fibre _ hy.2).image _
  differentiableOn_disc :=
    h.differentiableOn_disc.comp differentiable_zpart.differentiableOn fun y hy => hy.2
  frequently_disc_ne := by
    intro y hy
    have h1 := h.frequently_disc_ne (zpart y) hy.2
    have ht : Tendsto (fun z : ComplexModel d => mkPt z (y 0)) (𝓝 (zpart y)) (𝓝 y) := by
      have := (continuous_mkPt_left (n := d) (y 0)).tendsto (zpart y)
      rwa [mkPt_zpart] at this
    exact ht.frequently (p := fun v => δ (zpart v) ≠ 0) (by simpa using h1)
  ncard_fibre := by
    intro y hy hδ
    rw [fibre_wprod hy.1, Set.ncard_image_of_injective _ (mkPt_injective_left _)]
    exact h.ncard_fibre _ hy.2 hδ
  local_graph := by
    intro x hx hδ
    rw [zpart_coordinateProjection_succ] at hδ
    obtain ⟨U, V, g, hU, hV, hxU, hxV, hUD, hg, hgU, hgV⟩ := h.local_graph (zpart x) hx.2 hδ
    refine ⟨FNH.wprod B U, FNH.wprod B V, fun y => mkPt (g (zpart y)) (y 0),
      isOpen_wprod hB hU, isOpen_wprod hB hV, ⟨by simpa using hx.1, by simpa using hxU⟩,
      ⟨hx.1, hxV⟩, fun y hy => ⟨hy.1, hUD hy.2⟩, ?_, ?_, ?_⟩
    · exact differentiable_mkPt.comp_differentiableOn
        ((hg.comp differentiable_zpart.differentiableOn fun y hy => hy.2).prodMk
          differentiable_coord0.differentiableOn)
    · intro y hy
      obtain ⟨hgZ, hgπ⟩ := hgU (zpart y) hy.2
      refine ⟨mkPt_mem_wprod.mpr ⟨hy.1, hgZ⟩, ?_⟩
      rw [coordinateProjection_succ_mkPt, hgπ, mkPt_zpart]
    · rintro y ⟨⟨hy0, hyZ⟩, -, hyV⟩
      obtain ⟨hπU, hgy⟩ := hgV (zpart y) ⟨hyZ, hyV⟩
      refine ⟨⟨by simpa using hy0, by simpa using hπU⟩, ?_⟩
      simp only [zpart_coordinateProjection_succ, coordinateProjection_succ_zero, hgy]
      exact mkPt_zpart y
  subset_closure_generic := by
    intro x hx
    have h1 := h.subset_closure_generic hx.2
    have hsub : (fun z => mkPt z (x 0)) ''
        (Z ∩ coordinateProjection n d ⁻¹' {w | δ w ≠ 0}) ⊆
        FNH.wprod B Z ∩ coordinateProjection (n + 1) (d + 1) ⁻¹'
          {w | δ (zpart w) ≠ 0} := by
      rintro _ ⟨z, ⟨hzZ, hzδ⟩, rfl⟩
      refine ⟨mkPt_mem_wprod.mpr ⟨hx.1, hzZ⟩, ?_⟩
      simpa [coordinateProjection_succ_mkPt] using hzδ
    have h2 := image_closure_subset_closure_image (continuous_mkPt_left (n := n) (x 0))
      (mem_image_of_mem (fun z => mkPt z (x 0)) h1)
    rw [mkPt_zpart] at h2
    exact closure_mono hsub h2

/-! ### Charts of `X × ℂ` -/

/-- `(w, z) ↦ (w, T z)`. -/
def wprodCLE (T : ComplexModel n ≃L[ℂ] ComplexModel n) :
    ComplexModel (n + 1) ≃L[ℂ] ComplexModel (n + 1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => mkPt (T (zpart x)) (x 0)
      invFun := fun x => mkPt (T.symm (zpart x)) (x 0)
      map_add' := fun x y => ext_zpart (by simp) (by
        ext i
        simp [zpart_add])
      map_smul' := fun c x => ext_zpart (by simp) (by
        ext i
        simp [zpart_smul])
      left_inv := fun x => ext_zpart (by simp) (by simp)
      right_inv := fun x => ext_zpart (by simp) (by simp) }

@[simp] theorem wprodCLE_zero (T : ComplexModel n ≃L[ℂ] ComplexModel n) (x : ComplexModel (n + 1)) :
    wprodCLE T x 0 = x 0 := by
  simp [wprodCLE]

@[simp] theorem zpart_wprodCLE (T : ComplexModel n ≃L[ℂ] ComplexModel n)
    (x : ComplexModel (n + 1)) : zpart (wprodCLE T x) = T (zpart x) := by
  simp [wprodCLE]

theorem pdisc_cons (c : ComplexModel (n + 1)) (ρ : ℝ) (r : Fin n → ℝ) :
    pdisc c (Fin.cons ρ r : Fin (n + 1) → ℝ) = FNH.wprod (ball (c 0) ρ) (pdisc (zpart c) r) := by
  ext x
  simp only [mem_ofPred_eq, mem_wprod, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    mem_ball, dist_eq_norm, zpart_apply]

theorem image_wprodCLE_inter (T : ComplexModel n ≃L[ℂ] ComplexModel n) (X : Set (ComplexModel n))
    (B : Set ℂ) (P : Set (ComplexModel n)) :
    wprodCLE T '' (zpart ⁻¹' X) ∩ FNH.wprod B P = FNH.wprod B (T '' X ∩ P) := by
  ext x
  simp only [mem_inter_iff, mem_image, mem_preimage, mem_wprod]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h0, hP⟩
    exact ⟨h0, ⟨zpart y, hy, by simp⟩, hP⟩
  · rintro ⟨h0, ⟨z, hz, hzx⟩, hP⟩
    refine ⟨⟨mkPt z (x 0), by simpa using hz, ext_zpart (by simp) (by simp [hzx])⟩, h0, hP⟩

/-- **Charts of `X × ℂ`.** A branched-covering chart of `X ⊆ ℂⁿ` at `zpart x` gives a
branched-covering chart of `X × ℂ = zpart⁻¹(X) ⊆ ℂ^{n+1}` at `x`. -/
theorem hasCoveringChartAt_zpart_preimage {X : Set (ComplexModel n)} {x : ComplexModel (n + 1)}
    (h : HasCoveringChartAt X (zpart x) univ) :
    HasCoveringChartAt (zpart ⁻¹' X) x univ := by
  obtain ⟨T, d, hdn, r, D, deg, δ, hr, -, hπ, hcov, heq⟩ := h
  set B : Set ℂ := ball (x 0) 1 with hBdef
  have hB : IsOpen B := isOpen_ball
  have hpd : pdisc (wprodCLE T x) (Fin.cons (1 : ℝ) r : Fin (n + 1) → ℝ) =
      FNH.wprod B (pdisc (T (zpart x)) r) := by
    rw [pdisc_cons, wprodCLE_zero, zpart_wprodCLE]
  have hZ : wprodCLE T '' (zpart ⁻¹' X) ∩ pdisc (wprodCLE T x) (Fin.cons (1 : ℝ) r) =
      FNH.wprod B (T '' X ∩ pdisc (T (zpart x)) r) := by
    rw [hpd, image_wprodCLE_inter]
  refine ⟨wprodCLE T, d + 1, by omega, Fin.cons (1 : ℝ) r, FNH.wprod B D, deg,
    fun y => δ (zpart y), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using hr j
  · rw [image_univ, (wprodCLE T).surjective.range_eq]
    exact subset_univ _
  · rw [hpd]
    exact mapsTo_wprod hπ
  · rw [hZ]
    exact isBranchedCovering_wprod hB hcov
  · rw [hZ, hpd]
    exact hasLocalEquationsOn_wprod hB heq

end SGPT.Unibranch.FNH
