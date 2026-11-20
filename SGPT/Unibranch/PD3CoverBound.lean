import SGPT.Unibranch.FNLSheet
import SGPT.Unibranch.FNASuspension
import SGPT.Unibranch.LocalParamGerm
import SGPT.Unibranch.PDLimsup
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem
import SGPT.Foundations.Analysis.Pending.AnalyticImageDimension
import SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound

/-!
# Psh functions off a codimension-two set on a branched covering are locally bounded

Source `thm:GRexten2` (Appendix B, `appendix_unibranch.tex`), proof of item (1): "By the local
description of complex spaces we may assume that there is a domain `Ω ⊆ ℂ^n`, a finite `s`-sheet
branched covering `Φ : X → Ω` [...]. It suffices to show that `φ` is locally bounded from above near
`Z` [...] Since `Φ` is finite, `Φ(Z)` still has codimension at least `2` in `Ω`."

Here the local boundedness is proved for a finite branched covering `π : X → D ⊆ ℂ^d` (lane FNL's
`IsBranchedCovering`) and an analytic `Z ⊆ X` whose regular points have dimension `≤ d - 2`
(`exists_bound_of_isBranchedCovering`): if `f` is locally the restriction of ambient psh functions
at the points of `X \ Z`, then `f` is bounded above near every point of `X`, off `Z`.

Instead of the book's slicing by complex lines we use the trace of `[FN80]` Lemma 5.1
and the manifold codimension-two bound (`LocalParam.exists_bound_of_codimTwo`, which is itself
proved by line slicing):

1. `S = π(Z)` (over a small ball `B` of the base) is analytic by Remmert's proper mapping theorem
   (`ProperMappingTheorem.isComplexAnalyticSubset_image`) and has dimension `≤ d - 2`
   (`AnalyticImageDimension.dimLE_image`); so `B \ S` is connected.
2. Over `B \ S` the covering avoids `Z`, and `u = max(f, 0)` is weakly psh there; by `[FN80]`
   Lemma 5.1 (`IsBranchedCovering.discPshOn_trace`) its trace `∑_{π(x) = t} m(x) u(x)` is psh on
   `B \ S`, hence bounded above near the centre off `S` (codimension two). Since all terms are
   `≥ 0`, each `f(x) ≤ u(x)` is bounded by the trace.
3. At points of `X \ Z` over `S`: by curve selection (`PDCurveSelection`) there is a holomorphic
   disc in `X` through the point leaving `π⁻¹(S)` at once, and the maximum principle on small
   circles (`PD.le_limsup_punctured`) bounds `f` there by the bound of step 2.

Lane PD3, blueprint `pd3.tex`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ContDiff

noncomputable section

namespace SGPT.Unibranch.PD3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Unibranch.FNL SGPT.Unibranch.FNR

variable {N : ℕ}

/-- Plurisubharmonic germs pull back along holomorphic maps from `ℂ`. -/
theorem plurisubharmonicAt_comp_of_complex {ψ : ComplexModel N → EReal}
    {O : Set (ComplexModel N)} (hψ : PlurisubharmonicOn ψ O) {f : ℂ → ComplexModel N}
    {W : Set ℂ} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) (hfO : MapsTo f W O) {t : ℂ}
    (ht : t ∈ W) : PlurisubharmonicAt (fun s => ψ (f s)) t := by
  let P : ComplexModel 1 →L[ℂ] ℂ := EuclideanSpace.proj (0 : Fin 1)
  let L : ℂ →L[ℂ] ComplexModel 1 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))
  have hPL : ∀ s, P (L s) = s := fun s => by simp [P, L]
  have hU : IsOpen (P ⁻¹' W) := hW.preimage P.continuous
  have hg : DifferentiableOn ℂ (fun z => f (P z)) (P ⁻¹' W) :=
    hf.comp P.differentiable.differentiableOn fun z hz => hz
  have h := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hU hg (fun z hz => hfO hz) hψ
  have hLt : L t ∈ P ⁻¹' W := by
    change P (L t) ∈ W
    rw [hPL]
    exact ht
  have h2 := (h (L t) hLt).comp_continuousLinearMap L
  simpa only [hPL] using h2

/-- **Weak plurisubharmonicity is local.** A function which near every point of `Y` is the
restriction of an ambient psh function is weakly psh on `Y` (`[FN80]` §5). -/
theorem isWeaklyPSHOn_of_local {Y : Set (ComplexModel N)} {u : ComplexModel N → EReal}
    (h : ∀ x ∈ Y, ∃ O : Set (ComplexModel N), IsOpen O ∧ x ∈ O ∧ ∃ ψ : ComplexModel N → EReal,
      PlurisubharmonicOn ψ O ∧ ∀ y ∈ Y ∩ O, u y = ψ y) :
    IsWeaklyPSHOn Y u := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun f hf hfY => ?_⟩
  · obtain ⟨O, -, hxO, ψ, hψ, heq⟩ := h x hx
    obtain ⟨W, -, hxW, hW⟩ := hψ x hxO
    rw [heq x ⟨hx, hxO⟩]
    exact hW.ne_top x hxW
  · obtain ⟨O, hO, hxO, ψ, hψ, heq⟩ := h x hx
    obtain ⟨W, hW, hxW, hWψ⟩ := hψ x hxO
    intro c hc
    rw [heq x ⟨hx, hxO⟩] at hc
    have h1 := hWψ.upperSemicontinuousOn x hxW c hc
    rw [nhdsWithin_eq_nhds.mpr (hW.mem_nhds hxW)] at h1
    have h2 : ∀ᶠ y in 𝓝[Y] x, y ∈ O := mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hxO)
    filter_upwards [nhdsWithin_le_nhds h1, h2, self_mem_nhdsWithin] with y hy hyO hyY
    rw [heq y ⟨hyY, hyO⟩]
    exact hy
  · apply SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn
    intro t ht
    obtain ⟨O, hO, hxO, ψ, hψ, heq⟩ := h (f t) (hfY ht)
    set W := ball (0 : ℂ) 1 ∩ f ⁻¹' O with hWdef
    have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage isOpen_ball hO
    have htW : t ∈ W := ⟨ht, hxO⟩
    have hpsh := plurisubharmonicAt_comp_of_complex hψ hW (hf.mono inter_subset_left)
      (fun s hs => hs.2) htW
    obtain ⟨V, hV, htV, hVψ⟩ := hpsh
    refine ⟨V ∩ W, hV.inter hW, ⟨htV, htW⟩, (hVψ.mono inter_subset_left).congr ?_⟩
    intro s hs
    exact (heq (f s) ⟨hfY hs.2.1, hs.2.2⟩).symm

/-- Sets with local holomorphic equations on an open set `Ω` are relatively closed in `Ω`. -/
theorem eventually_notMem_of_hasLocalEquationsOn {A Ω : Set (ComplexModel N)}
    (hA : HasLocalEquationsOn A Ω) {x : ComplexModel N} (hxΩ : x ∈ Ω) (hxA : x ∉ A) :
    ∀ᶠ y in 𝓝 x, y ∉ A := by
  obtain ⟨W, hW, hxW, m, g, hg, hgA⟩ := hA x hxΩ
  obtain ⟨i, hi⟩ : ∃ i, g i x ≠ 0 := by
    by_contra! h
    exact hxA ((hgA x hxW).mpr h)
  have hc : ContinuousAt (g i) x := ((hg i).differentiableAt (hW.mem_nhds hxW)).continuousAt
  filter_upwards [hW.mem_nhds hxW, hc.eventually_ne hi] with y hyW hy hyA
  exact hy ((hgA y hyW).mp hyA i)

/-- A set whose regular points all have codimension `≥ 2` in `ℂ^m` has empty interior. -/
theorem interior_eq_empty_of_codim {m : ℕ} {S : Set (ComplexModel m)}
    (h : ∀ t k, RegularAtDim (n := m) (M := ComplexModel m) S t k → k + 2 ≤ m) :
    interior S = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro t ht
  have hset : (univ : Set (ComplexModel m)) ∩ interior S = S ∩ interior S := by
    ext y
    simp only [mem_inter_iff, mem_univ, true_and]
    exact ⟨fun hy => ⟨interior_subset hy, hy⟩, fun hy => hy.2⟩
  have hreg : RegularAtDim (n := m) (M := ComplexModel m) S t m :=
    RegularPointDimension.regularAtDim_of_inter_eq isOpen_interior ht hset
      (AnalyticIrreducibleComponents.regularAtDim_univ (n := m) (M := ComplexModel m) t)
  have := h t m hreg
  omega

section Covering

variable {d : ℕ} {X : Set (ComplexModel N)} {π : ComplexModel N →L[ℂ] ComplexModel d}
  {D : Set (ComplexModel d)} {deg : ℕ} {δ : ComplexModel d → ℂ}

/-- Over a set with empty interior, the points of a branched covering are not isolated from the
rest: `X ⊆ closure (X \ π⁻¹ S)`. -/
theorem subset_closure_diff_preimage (hX : IsBranchedCovering X π D deg δ)
    {S : Set (ComplexModel d)} (hS : interior S = ∅) : X ⊆ closure (X \ π ⁻¹' S) := by
  have h1 : X ∩ π ⁻¹' {w | δ w ≠ 0} ⊆ closure (X \ π ⁻¹' S) := by
    rintro y ⟨hy, hyδ⟩
    obtain ⟨U, V, g, hU, hV, hyU, hyV, -, hg, hgX, hXg⟩ := hX.local_graph y hy hyδ
    rw [mem_closure_iff_nhds]
    intro Nb hNb
    have hgy : g (π y) = y := (hXg y ⟨hy, hyV⟩).2
    have hcont : ContinuousAt g (π y) := (hg.differentiableAt (hU.mem_nhds hyU)).continuousAt
    have hNb' : Nb ∈ 𝓝 (g (π y)) := by rw [hgy]; exact hNb
    have hpre : g ⁻¹' Nb ∩ U ∈ 𝓝 (π y) :=
      inter_mem (hcont.preimage_mem_nhds hNb') (hU.mem_nhds hyU)
    obtain ⟨w, hwN, hwS⟩ : ∃ w ∈ g ⁻¹' Nb ∩ U, w ∉ S := by
      by_contra! hsub
      have : π y ∈ interior S := mem_interior_iff_mem_nhds.mpr (mem_of_superset hpre hsub)
      rw [hS] at this
      exact this
    refine ⟨g w, hwN.1, (hgX w hwN.2).1, ?_⟩
    change π (g w) ∉ S
    rw [(hgX w hwN.2).2]
    exact hwS
  intro y hy
  exact closure_minimal h1 isClosed_closure (hX.subset_closure_generic hy)

/-- The trace of a nonnegative function dominates each of its values on the fibre. -/
theorem le_trace_of_nonneg (hX : IsBranchedCovering X π D deg δ)
    {u : ComplexModel N → EReal} (hu : ∀ x ∈ X, 0 ≤ u x) {x : ComplexModel N} (hx : x ∈ X) :
    u x ≤ trace X π δ u (π x) := by
  classical
  have hfin := hX.finite_fibre (π x) (hX.mem_base hx)
  have hxF : x ∈ fibre X π (π x) := ⟨hx, rfl⟩
  rw [trace, finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc u x = 1 • u x := (one_nsmul _).symm
    _ ≤ sheetNumber X π δ x • u x := nsmul_le_nsmul_left (hu x hx) (hX.one_le_sheetNumber hx)
    _ ≤ ∑ p ∈ hfin.toFinset, sheetNumber X π δ p • u p :=
        Finset.single_le_sum (f := fun p => sheetNumber X π δ p • u p)
          (fun p hp => nsmul_nonneg (hu p ((hfin.mem_toFinset.mp hp).1)) _)
          (hfin.mem_toFinset.mpr hxF)

/-- **Local upper bound off a codimension-two set on a branched covering.** Let `π : X → D` be a
finite branched covering (`X ⊆ P` with local equations on the open set `P`, `π(P) ⊆ D`), `Z ⊆ X`
analytic in `P` with all regular points of dimension `≤ d - 2`, and `f` locally the restriction
of ambient psh functions at the points of `X \ Z`. Then `f` is bounded above near every point of
`X`, off `Z`. -/
theorem exists_bound_of_isBranchedCovering (hX : IsBranchedCovering X π D deg δ)
    {P : Set (ComplexModel N)} (hP : IsOpen P) (hXP : X ⊆ P) (hXeq : HasLocalEquationsOn X P)
    {Z : Set (ComplexModel N)} (hZX : Z ⊆ X) (hZeq : HasLocalEquationsOn Z P)
    (hZdim : ∀ w k, RegularAtDim (n := N) (M := ComplexModel N) Z w k → k + 2 ≤ d)
    {f : ComplexModel N → EReal}
    (hf : ∀ x ∈ X, x ∉ Z → ∃ O : Set (ComplexModel N), IsOpen O ∧ x ∈ O ∧
      ∃ ψ : ComplexModel N → EReal, PlurisubharmonicOn ψ O ∧ ∀ y ∈ X ∩ O, f y = ψ y)
    {p : ComplexModel N} (hp : p ∈ X) :
    ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ x ∈ X ∩ U, x ∉ Z → f x ≤ C := by
  classical
  -- a ball in the base
  obtain ⟨ρ, hρ, hρD⟩ := hX.exists_closedBall_subset (hX.mem_base hp)
  set B : Set (ComplexModel d) := ball (π p) ρ with hBdef
  have hBD : B ⊆ D := ball_subset_closedBall.trans hρD
  let PB : Opens (ComplexModel N) := ⟨P ∩ π ⁻¹' B, hP.inter (isOpen_ball.preimage π.continuous)⟩
  let BO : Opens (ComplexModel d) := ⟨B, isOpen_ball⟩
  let F : PB → BO := fun x => ⟨π x.val, x.property.2⟩
  have hF : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel d) ∞ F := by
    apply (ContMDiff.subtypeVal_comp_iff BO F).mp
    exact π.contDiff.contMDiff.comp contMDiff_subtype_val
  let A : Set PB := Subtype.val ⁻¹' Z
  have hA : IsComplexAnalyticSubset (n := N) A :=
    FNA.isComplexAnalyticSubset_of_hasLocalEquationsOn (Ω := PB) (hZeq.mono inter_subset_left)
  -- properness of `π` on `Z` over `B`
  have hprop : AnalyticDimensionBasics.ProperOn F A := by
    intro K hK
    set K' : Set (ComplexModel d) := Subtype.val '' K with hK'def
    have hK' : IsCompact K' := hK.image continuous_subtype_val
    have hK'D : K' ⊆ D := by
      rintro _ ⟨k, -, rfl⟩
      exact hBD k.property
    have hc := hX.isCompact_inter_preimage K' hK'D hK'
    have hZc : IsCompact (Z ∩ π ⁻¹' K') := by
      have hset : Z ∩ π ⁻¹' K' = (X ∩ π ⁻¹' K') ∩ closure Z := by
        ext y
        constructor
        · rintro ⟨hyZ, hyK⟩
          exact ⟨⟨hZX hyZ, hyK⟩, subset_closure hyZ⟩
        · rintro ⟨⟨hyX, hyK⟩, hycl⟩
          refine ⟨?_, hyK⟩
          by_contra hyZ
          have hev := eventually_notMem_of_hasLocalEquationsOn hZeq (hXP hyX) hyZ
          obtain ⟨w, hw1, hw2⟩ := ((mem_closure_iff_frequently.mp hycl).and_eventually hev).exists
          exact hw2 hw1
      rw [hset]
      exact hc.inter_right isClosed_closure
    rw [Subtype.isCompact_iff]
    convert hZc using 1
    ext y
    constructor
    · rintro ⟨x, ⟨hxZ, hxK⟩, rfl⟩
      exact ⟨hxZ, ⟨F x, hxK, rfl⟩⟩
    · rintro ⟨hyZ, k, hkK, hky⟩
      have hyB : π y ∈ B := by
        rw [← hky]
        exact k.property
      refine ⟨⟨y, hXP (hZX hyZ), hyB⟩, ⟨hyZ, ?_⟩, rfl⟩
      have hFk : F ⟨y, hXP (hZX hyZ), hyB⟩ = k := Subtype.ext hky.symm
      change F ⟨y, hXP (hZX hyZ), hyB⟩ ∈ K
      rw [hFk]
      exact hkK
  -- Remmert: the image `S = π(Z ∩ π⁻¹ B)` is analytic in `B`
  have hS' : IsComplexAnalyticSubset (n := d) (F '' A) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hF hA hprop
  set S : Set (ComplexModel d) := Subtype.val '' (F '' A) with hSdef
  have hSeq : HasLocalEquationsOn S B := hasLocalEquationsOn_of_isComplexAnalyticSubset hS'
  have hSchar : ∀ z ∈ Z, z ∈ P → π z ∈ B → π z ∈ S := fun z hz hzP hzB =>
    ⟨F (⟨z, ⟨hzP, hzB⟩⟩ : PB), ⟨(⟨z, ⟨hzP, hzB⟩⟩ : PB), hz, rfl⟩, rfl⟩
  have hSB : S ⊆ B := by
    rintro _ ⟨t, -, rfl⟩
    exact t.property
  -- dimension of `S`
  have hdimA : AnalyticDimensionBasics.DimLE (n := N) A (d - 2) := by
    intro x k hx
    have h1 : RegularAtDim (n := N) (M := ComplexModel N) Z x k :=
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hx
    have := hZdim x.val k h1
    omega
  have hfib : ∀ x ∈ A, AnalyticDimensionBasics.LocDimGE (n := N) (A ∩ F ⁻¹' {F x}) x 0 := by
    intro x hx
    have hmem : x ∈ A ∩ F ⁻¹' {F x} := ⟨hx, rfl⟩
    exact AnalyticDimensionBasics.locDimGE_zero
      (hA.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hF
        (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton _))) hmem
  have hdimS := AnalyticImageDimension.dimLE_image hF hA hdimA hfib
  have hScodim : ∀ t k, RegularAtDim (n := d) (M := ComplexModel d) S t k → k + 2 ≤ d := by
    intro t k ht
    have htB : t ∈ BO := AnalyticSubsetOpens.mem_opens_of_regularAtDim_image_val ht
    have ht' := (AnalyticSubsetOpens.regularAtDim_image_val_iff (x := (⟨t, htB⟩ : BO))).mp ht
    have hk := hdimS _ _ ht'
    obtain ⟨x, hxA, -⟩ := ht'.2.1
    obtain ⟨y, -, j, hy⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds hA hxA univ_mem
    have := hZdim y.val j (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hy)
    omega
  have hSint : interior S = ∅ := interior_eq_empty_of_codim hScodim
  -- the base `B \ S`
  have hD'open : IsOpen (B \ S) := by
    rw [isOpen_iff_mem_nhds]
    rintro t ⟨htB, htS⟩
    filter_upwards [isOpen_ball.mem_nhds htB,
      eventually_notMem_of_hasLocalEquationsOn hSeq htB htS] with s hs1 hs2
    exact ⟨hs1, hs2⟩
  have hD'conn : IsPreconnected (B \ S) := by
    have hBc : ConnectedSpace BO := isConnected_iff_connectedSpace.mp
      ((convex_ball (π p) ρ).isConnected (nonempty_ball.mpr hρ))
    have hTne : F '' A ≠ univ := by
      intro hT
      have hSB' : S = B := by
        apply Subset.antisymm hSB
        intro t ht
        exact ⟨⟨t, ht⟩, hT ▸ mem_univ _, rfl⟩
      have : π p ∈ interior S := by
        rw [hSB', isOpen_ball.interior_eq]
        exact mem_ball_self hρ
      rw [hSint] at this
      exact this
    have h := AnalyticComplementConnected.isPreconnected_compl (M := BO) hS' hTne
    have himg : Subtype.val '' (F '' A)ᶜ = B \ S := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨s.property, ?_⟩
        rintro ⟨s', hs', hss'⟩
        exact hs (Subtype.ext hss' ▸ hs')
      · rintro ⟨htB, htS⟩
        exact ⟨⟨t, htB⟩, fun h' => htS ⟨_, h', rfl⟩, rfl⟩
    rw [← himg]
    exact h.image _ continuous_subtype_val.continuousOn
  -- a generic point of `B \ S`
  obtain ⟨z₀, ⟨hz₀B, hz₀S⟩, hz₀δ⟩ : ∃ z ∈ B \ S, δ z ≠ 0 := by
    have hfreq := hX.frequently_disc_ne (π p) (hX.mem_base hp)
    obtain ⟨w, hwδ, hwB⟩ :=
      (hfreq.and_eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))).exists
    have hO : IsOpen (B ∩ δ ⁻¹' {c : ℂ | c ≠ 0}) :=
      (hX.differentiableOn_disc.continuousOn.mono hBD).isOpen_inter_preimage isOpen_ball
        isOpen_ne
    by_contra! hall
    have hsub : B ∩ δ ⁻¹' {c : ℂ | c ≠ 0} ⊆ S := by
      intro t ht
      by_contra htS
      exact ht.2 (hall t ⟨ht.1, htS⟩)
    have hwO : w ∈ B ∩ δ ⁻¹' {c : ℂ | c ≠ 0} := ⟨hwB, hwδ⟩
    have : w ∈ interior S := interior_mono hsub (by rw [hO.interior_eq]; exact hwO)
    rw [hSint] at this
    exact this
  -- the covering over `B \ S`
  have hres := hX.restrict (V := univ) isOpen_univ hD'open hD'conn (fun t ht => hBD ht.1)
    (fun z _ x _ => by simp) ⟨z₀, ⟨hz₀B, hz₀S⟩, hz₀δ, rfl⟩
  set X'' := X ∩ univ ∩ π ⁻¹' (B \ S) with hX''def
  set u : ComplexModel N → EReal := fun x => max (f x) 0 with hudef
  have hu : IsWeaklyPSHOn X'' u := by
    apply isWeaklyPSHOn_of_local
    intro x hx
    have hxZ : x ∉ Z := fun hxZ => hx.2.2 (hSchar x hxZ (hXP hx.1.1) hx.2.1)
    obtain ⟨O, hO, hxO, ψ, hψ, heq⟩ := hf x hx.1.1 hxZ
    refine ⟨O, hO, hxO, fun y => max (ψ y) 0,
      hψ.max (fun y _ => plurisubharmonicAt_const 0 (by simp) y), fun y hy => ?_⟩
    change max (f y) 0 = max (ψ y) 0
    rw [heq y ⟨hy.1.1.1, hy.2⟩]
  have htr := hres.discPshOn_trace hu
  have hpsh : PlurisubharmonicOn (trace X'' π δ u) (B \ S) := htr.plurisubharmonicOn hD'open
  -- the codimension-two bound on the base
  obtain ⟨U₀, hU₀, C, hC⟩ := LocalParam.exists_bound_of_codimTwo (Ω := B) (S := S) isOpen_ball
    (fun z hz => hSeq z hz) (fun y _ k hk => hScodim y k hk) hpsh (mem_ball_self hρ)
  have hgood : ∀ x ∈ X, π x ∈ U₀ → π x ∈ B → π x ∉ S → f x ≤ C := by
    intro x hx hxU hxB hxS
    have hx'' : x ∈ X'' := ⟨⟨hx, trivial⟩, hxB, hxS⟩
    calc f x ≤ u x := le_max_left _ _
      _ ≤ trace X'' π δ u (π x) := le_trace_of_nonneg hres (fun y _ => le_max_right _ _) hx''
      _ ≤ C := hC (π x) hxU hxS
  set U₁ : Set (ComplexModel d) := interior U₀ ∩ B with hU₁def
  have hU₁ : IsOpen U₁ := isOpen_interior.inter isOpen_ball
  have hpU₁ : π p ∈ U₁ := ⟨mem_interior_iff_mem_nhds.mpr hU₀, mem_ball_self hρ⟩
  -- points over `S`: curve selection and the maximum principle
  have hall : ∀ x ∈ X, π x ∈ U₁ → x ∉ Z → f x ≤ C := by
    intro x hx hxU hxZ
    by_cases hxS : π x ∉ S
    · exact hgood x hx (interior_subset hxU.1) hxU.2 hxS
    push Not at hxS
    have hxPB : x ∈ (PB : Set (ComplexModel N)) := ⟨hXP hx, hxU.2⟩
    let Cs : Set PB := Subtype.val ⁻¹' X
    have hCs : IsComplexAnalyticSubset (n := N) Cs :=
      FNA.isComplexAnalyticSubset_of_hasLocalEquationsOn (Ω := PB) (hXeq.mono inter_subset_left)
    let As : Set PB := F ⁻¹' (F '' A)
    have hAs : IsComplexAnalyticSubset (n := N) As :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hF hS'
    have hAsiff : ∀ y : PB, y ∈ As ↔ π y.val ∈ S := by
      intro y
      constructor
      · intro hy
        exact ⟨F y, hy, rfl⟩
      · rintro ⟨t, ht, hty⟩
        change F y ∈ F '' A
        have : t = F y := Subtype.ext hty
        rw [← this]
        exact ht
    have hcl : (⟨x, hxPB⟩ : PB) ∈ closure (Cs \ As) := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      change x ∈ closure (Subtype.val '' (Cs \ As))
      have h0 := subset_closure_diff_preimage hX hSint hx
      rw [mem_closure_iff_nhds] at h0 ⊢
      intro Nb hNb
      obtain ⟨y, ⟨hyN, hyPB⟩, hyX, hyS⟩ := h0 (Nb ∩ PB)
        (inter_mem hNb (PB.isOpen.mem_nhds hxPB))
      exact ⟨y, hyN, ⟨y, hyPB⟩, ⟨hyX, fun h' => hyS ((hAsiff _).mp h')⟩, rfl⟩
    obtain ⟨G, hG, hG0, hGC, hGA⟩ := PDCurveSelection.exists_avoiding_disc_of_mem_closure hCs hAs hcl
    obtain ⟨O, hO, hxO, ψ, hψ, heq⟩ := hf x hx hxZ
    set Q : Set (ComplexModel N) := O ∩ PB ∩ π ⁻¹' U₁ with hQdef
    have hQ : IsOpen Q := (hO.inter PB.isOpen).inter (hU₁.preimage π.continuous)
    have hxQ : x ∈ Q := ⟨⟨hxO, hxPB⟩, hxU⟩
    have hGc : ContinuousAt G 0 :=
      hG.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    have hG0' : G 0 = x := hG0
    obtain ⟨ε, hε, hεQ⟩ := Metric.eventually_nhds_iff.mp
      (hGc.preimage_mem_nhds (by rw [hG0']; exact hQ.mem_nhds hxQ))
    set r : ℝ := min ε 1 / 2 with hrdef
    have hr : 0 < r := by positivity
    have hrε : r < ε := by
      have := min_le_left ε 1
      rw [hrdef]
      linarith
    have hr1 : r < 1 := by
      have := min_le_right ε 1
      rw [hrdef]
      linarith
    set L := SourceReducedComplexSpace.discCoordinate with hLdef
    let g : ℂ → ComplexModel N := fun s => G (L ((r : ℂ) * s))
    have hLs : ∀ s ∈ ball (0 : ℂ) 1, L ((r : ℂ) * s) ∈ ball (0 : ComplexModel 1) (min ε 1) := by
      intro s hs
      rw [mem_ball_zero_iff, SourceReducedComplexSpace.norm_discCoordinate, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hs' : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
      calc r * ‖s‖ ≤ r * 1 := by gcongr
        _ < min ε 1 := by
          have : 0 < min ε 1 := lt_min hε one_pos
          rw [hrdef]
          linarith
    have hgQ : MapsTo g (ball 0 1) Q := by
      intro s hs
      have h1 := hLs s hs
      exact hεQ (lt_of_lt_of_le (mem_ball.mp h1) (min_le_left ε 1))
    have hgd : DifferentiableOn ℂ g (ball 0 1) := by
      have hGd : DifferentiableOn ℂ G (ball 0 1) := hG.differentiableOn (by simp)
      refine hGd.comp ((L.differentiable.comp (differentiable_const _ |>.mul
        differentiable_id)).differentiableOn) ?_
      intro s hs
      exact ball_subset_ball (min_le_right ε 1) (hLs s hs)
    have hD : DiscPshOn (fun s => ψ (g s)) (ball 0 1) :=
      SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn fun t ht =>
        plurisubharmonicAt_comp_of_complex hψ isOpen_ball hgd (fun s hs => (hgQ hs).1.1) ht
    have h1 := PD.le_limsup_punctured hD
    have hg0 : g 0 = x := by
      change G (L ((r : ℂ) * 0)) = x
      rw [mul_zero, map_zero, hG0']
    have hval0 : ψ (g 0) = f x := by
      rw [hg0]
      exact (heq x ⟨hx, hxO⟩).symm
    rw [hval0] at h1
    refine h1.trans (limsup_le_of_le (by isBoundedDefault) ?_)
    have hball : ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    filter_upwards [hball, self_mem_nhdsWithin] with s hs hs0
    have hsQ := hgQ hs
    have hz : L ((r : ℂ) * s) ∈ ball (0 : ComplexModel 1) 1 :=
      ball_subset_ball (min_le_right ε 1) (hLs s hs)
    have hz0 : L ((r : ℂ) * s) ≠ 0 := by
      intro h0
      apply hs0
      have := congrArg norm h0
      rw [SourceReducedComplexSpace.norm_discCoordinate, norm_zero, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr] at this
      exact norm_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hr.ne')
    obtain ⟨y, hyC, hyG⟩ := hGC _ hz
    have hgX : g s ∈ X := by
      change G (L ((r : ℂ) * s)) ∈ X
      rw [← hyG]
      exact hyC
    have hgS : π (g s) ∉ S := by
      intro hS
      have hyA := hGA _ hz hz0 ⟨g s, hsQ.1.2⟩ rfl
      exact hyA ((hAsiff _).mpr hS)
    have heqs : ψ (g s) = f (g s) := (heq (g s) ⟨hgX, hsQ.1.1⟩).symm
    rw [heqs]
    exact hgood (g s) hgX (interior_subset hsQ.2.1) hsQ.2.2 hgS
  refine ⟨P ∩ π ⁻¹' U₁, inter_mem (hP.mem_nhds (hXP hp))
    (π.continuous.continuousAt.preimage_mem_nhds (hU₁.mem_nhds hpU₁)), C, ?_⟩
  rintro x ⟨hx, -, hxU⟩ hxZ
  exact hall x hx hxU hxZ

end Covering

end SGPT.Unibranch.PD3
