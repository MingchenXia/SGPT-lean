import SGPT.Foundations.Analysis.Pending.PshCodimTwoExtension
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull
import SGPT.Foundations.Analysis.PlurisubharmonicAE

/-!
# Slicing two-sheet grids by complex lines

This file contains the line-slicing half of the proof of the Grauert--Remmert
extension theorem across analytic sets of codimension at least two
(SGPT `thm:GRexten`, item (1), and the manifold case of `thm:GRexten2`, item (1)).

A *two-sheet grid* on an open set `V ⊆ ℂⁿ` (`GridData`) is given by two
holomorphic functions `f_a, f_b` on `V` and two directions `v_a, v_b` such that
`f_a` is invariant in the direction `v_b`, `f_b` is invariant in the direction
`v_a`, and along every complex line in the direction `v_a` (resp. `v_b`) the
function `f_a` (resp. `f_b`) has only finitely many zeros.  Its carrier is the
common zero set of `f_a, f_b` in `V`.  In the local parametrization of an
irreducible analytic germ of dimension `d ≤ n - 2`
(`LocalParamGerm`), the functions are the Weierstrass polynomials of two fibre
coordinates over the base `ℂᵈ`, and the directions are the two corresponding
coordinate axes.

* `exists_bound_off_grid`: through a point off the grid, one of the two
  coordinate discs misses the grid; its boundary circle lies in a fixed compact
  set off the grid, and the maximum principle bounds a plurisubharmonic function
  near a grid point (the book's line-slicing argument).
* `GridData.psh_extension`: a plurisubharmonic function off a grid extends
  plurisubharmonically across it.
* `exists_psh_extension_of_grids`: the same across a finite union of grids
  (one grid at a time).
* `exists_bound_of_gridCover`: a plurisubharmonic function off a set covered by
  finitely many grids is locally bounded above (the grids are Lebesgue null).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Unibranch.LocalParam

open Set Filter Metric MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {n : ℕ}

/-- The complex line map `t ↦ t • v`. -/
def lineThrough (v : ComplexModel n) : ℂ →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight v

@[simp] theorem lineThrough_apply (v : ComplexModel n) (t : ℂ) : lineThrough v t = t • v := rfl

/-- A finite set of complex numbers misses the circle of some radius in every interval
`(0, R)`. -/
theorem exists_radius_avoiding {F : Set ℂ} (hF : F.Finite) {R : ℝ} (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ ∀ t ∈ F, ‖t‖ ≠ ρ := by
  have hne : ((Ioo (0 : ℝ) R) \ ((fun t : ℂ => ‖t‖) '' F)).Nonempty :=
    ((Set.Ioo_infinite hR).sdiff (hF.image _)).nonempty
  obtain ⟨ρ, ⟨hρ0, hρR⟩, hρF⟩ := hne
  exact ⟨ρ, hρ0, hρR, fun t ht h => hρF ⟨t, ht, h⟩⟩

/-- A plurisubharmonic function is bounded above near each point of its domain. -/
theorem exists_nhds_bound_of_psh {Ω : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hψ : PlurisubharmonicOn ψ Ω) {x : ComplexModel n} (hx : x ∈ Ω) :
    ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, ψ y ≤ C := by
  obtain ⟨C, hC, _⟩ := EReal.lt_iff_exists_real_btwn.mp
    (lt_top_iff_ne_top.mpr (hψ x hx).ne_top)
  exact ⟨{y | ψ y < C}, (hψ x hx).upperSemicontinuousAt C hC, C, fun y hy => le_of_lt hy⟩

/-- **One-direction slicing bound.**  Let `ψ` be plurisubharmonic off `A` in an open set
`N`, where `A ∩ N` lies in the common zero set of `f` and `g`, and `g` is invariant in the
direction `v`.  If `f` does not vanish on the circle `x₀ + t v`, `‖t‖ = ρ`, then `ψ` is
bounded above near `x₀` at every point where `g ≠ 0`: the disc through such a point in the
direction `v` misses `A`, and its boundary circle stays in a compact set off `A`. -/
theorem exists_bound_along_line {N A : Set (ComplexModel n)} (hN : IsOpen N)
    {f g : ComplexModel n → ℂ} {v : ComplexModel n} (hf : ContinuousOn f N)
    (hinv : ∀ z (t : ℂ), g (z + t • v) = g z)
    (hA : ∀ z ∈ N, z ∈ A → f z = 0 ∧ g z = 0)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (N \ A))
    {x₀ : ComplexModel n} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall x₀ ((1 + ‖v‖) * ρ) ⊆ N)
    (hc : ∀ t : ℂ, ‖t‖ = ρ → f (x₀ + t • v) ≠ 0) :
    ∃ δ > 0, ∃ M : ℝ, ∀ y ∈ ball x₀ δ, g y ≠ 0 → ψ y ≤ M := by
  have htube : ∀ᶠ y in 𝓝 x₀, ∀ t ∈ sphere (0 : ℂ) ρ,
      y + t • v ∈ N ∧ f (y + t • v) ≠ 0 := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun t ht => ?_
    have htρ : ‖t‖ = ρ := by simpa using ht
    have hq : x₀ + t • v ∈ N := hball (by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, htρ]
      nlinarith [norm_nonneg v])
    have hcont : ContinuousAt (fun p : ComplexModel n × ℂ => p.1 + p.2 • v) (x₀, t) :=
      (continuous_fst.add (continuous_snd.smul continuous_const)).continuousAt
    have hN' : ∀ᶠ q in 𝓝 (x₀ + t • v), q ∈ N ∧ f q ≠ 0 :=
      Filter.Eventually.and (hN.mem_nhds hq : ∀ᶠ q in 𝓝 (x₀ + t • v), q ∈ N)
        ((hf.continuousAt (hN.mem_nhds hq)).eventually_ne (hc t htρ))
    exact hcont.eventually hN'
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.mp htube
  set δ := min (ε / 2) ρ with hδ
  have hδ0 : 0 < δ := lt_min (half_pos hε) hρ
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδρ : δ ≤ ρ := min_le_right _ _
  set F : ComplexModel n × ℂ → ComplexModel n := fun p => p.1 + p.2 • v with hF
  set K := F '' (closedBall x₀ δ ×ˢ sphere (0 : ℂ) ρ) with hK
  have hKc : IsCompact K := ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).image
    (continuous_fst.add (continuous_snd.smul continuous_const))
  have hKsub : K ⊆ N \ A := by
    rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
    have h := hεs y (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hδε)) t ht
    exact ⟨h.1, fun hA' => h.2 (hA _ h.1 hA').1⟩
  have hψd := hψ.discPshOn
  obtain ⟨M, hM⟩ := PshCodimTwoExtension.exists_bound_of_isCompact hKc
    (hψd.upperSemicontinuousOn.mono hKsub) fun p hp => hψd.ne_top p (hKsub hp)
  refine ⟨δ, hδ0, M, fun y hy hgy => ?_⟩
  have hy' : ‖y - x₀‖ < δ := by rwa [mem_ball, dist_eq_norm] at hy
  have hpsh := hψ.comp_affine (lineThrough v) y
  have hdisc : closedBall (0 : ℂ) ρ ⊆ (fun t => y + lineThrough v t) ⁻¹' (N \ A) := by
    intro t ht
    have ht' : ‖t‖ ≤ ρ := by simpa using ht
    have hyN : y + t • v ∈ N := hball (by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖y + t • v - x₀‖ ≤ ‖y - x₀‖ + ‖t • v‖ := by
            rw [add_sub_right_comm]; exact norm_add_le _ _
        _ ≤ ρ + ρ * ‖v‖ := by
            rw [norm_smul]
            have := mul_le_mul_of_nonneg_right ht' (norm_nonneg v)
            linarith
        _ = (1 + ‖v‖) * ρ := by ring)
    refine ⟨hyN, fun hA' => hgy ?_⟩
    have h := (hA _ hyN hA').2
    rwa [hinv] at h
  have h := PlurisubharmonicOn.le_const_on_closedBall_of_le_on_sphere hpsh hρ hdisc
    (C := M) (fun t ht => hM _ ⟨(y, t), ⟨mem_closedBall.mpr (le_of_lt (mem_ball.mp hy)), ht⟩,
      rfl⟩) 0 (mem_closedBall_self hρ.le)
  simpa using h

/-- **Two-direction slicing bound** (the line-slicing step of SGPT `thm:GRexten`, item (1)).
Let `A ∩ N` lie in the common zero set of `f_a` and `f_b`, with `f_a` invariant in the
direction `v_b` and `f_b` invariant in the direction `v_a`.  If `f_a` (resp. `f_b`) does not
vanish on the circle of radius `ρ` about `x₀` in the direction `v_a` (resp. `v_b`), then a
function plurisubharmonic off `A` is bounded above near `x₀` off the common zero set. -/
theorem exists_bound_off_grid {N A : Set (ComplexModel n)} (hN : IsOpen N)
    {fa fb : ComplexModel n → ℂ} {va vb : ComplexModel n}
    (hfa : ContinuousOn fa N) (hfb : ContinuousOn fb N)
    (hinva : ∀ z (t : ℂ), fa (z + t • vb) = fa z) (hinvb : ∀ z (t : ℂ), fb (z + t • va) = fb z)
    (hA : ∀ z ∈ N, z ∈ A → fa z = 0 ∧ fb z = 0)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (N \ A))
    {x₀ : ComplexModel n} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall x₀ ((1 + (‖va‖ + ‖vb‖)) * ρ) ⊆ N)
    (hca : ∀ t : ℂ, ‖t‖ = ρ → fa (x₀ + t • va) ≠ 0)
    (hcb : ∀ t : ℂ, ‖t‖ = ρ → fb (x₀ + t • vb) ≠ 0) :
    ∃ δ > 0, ∃ M : ℝ, ∀ y ∈ ball x₀ δ, (fa y ≠ 0 ∨ fb y ≠ 0) → ψ y ≤ M := by
  have hsa : closedBall x₀ ((1 + ‖va‖) * ρ) ⊆ N :=
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right
      (by linarith [norm_nonneg vb]) hρ.le)).trans hball
  have hsb : closedBall x₀ ((1 + ‖vb‖) * ρ) ⊆ N :=
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right
      (by linarith [norm_nonneg va]) hρ.le)).trans hball
  obtain ⟨δa, hδa, Ma, hMa⟩ := exists_bound_along_line hN hfa hinvb hA hψ hρ hsa hca
  obtain ⟨δb, hδb, Mb, hMb⟩ := exists_bound_along_line hN hfb hinva
    (fun z hz hzA => (hA z hz hzA).symm) hψ hρ hsb hcb
  refine ⟨min δa δb, lt_min hδa hδb, max Ma Mb, fun y hy hfy => ?_⟩
  have hya : y ∈ ball x₀ δa := ball_subset_ball (min_le_left _ _) hy
  have hyb : y ∈ ball x₀ δb := ball_subset_ball (min_le_right _ _) hy
  rcases hfy with hfa' | hfb'
  · exact (hMb y hyb hfa').trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
  · exact (hMa y hya hfb').trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))

/-- **Two-sheet grid data** on an open set `V ⊆ ℂⁿ`: two holomorphic functions `f_a, f_b`
on `V` and two directions `v_a, v_b`, with `f_a` invariant in the direction `v_b`, `f_b`
invariant in the direction `v_a`, and only finitely many zeros of `f_a` (resp. `f_b`) on
each complex line through a point of `V` in the direction `v_a` (resp. `v_b`). -/
structure GridData (V : Set (ComplexModel n)) where
  /-- The first equation. -/
  fa : ComplexModel n → ℂ
  /-- The second equation. -/
  fb : ComplexModel n → ℂ
  /-- The slicing direction of the first equation. -/
  va : ComplexModel n
  /-- The slicing direction of the second equation. -/
  vb : ComplexModel n
  differentiableOn_fa : DifferentiableOn ℂ fa V
  differentiableOn_fb : DifferentiableOn ℂ fb V
  fa_add_vb : ∀ z (t : ℂ), fa (z + t • vb) = fa z
  fb_add_va : ∀ z (t : ℂ), fb (z + t • va) = fb z
  finite_fa : ∀ x ∈ V, {t : ℂ | fa (x + t • va) = 0}.Finite
  finite_fb : ∀ x ∈ V, {t : ℂ | fb (x + t • vb) = 0}.Finite

namespace GridData

variable {V : Set (ComplexModel n)} (G : GridData V)

/-- The grid itself: the common zeros of the two equations in `V`. -/
def carrier : Set (ComplexModel n) := {z | z ∈ V ∧ G.fa z = 0 ∧ G.fb z = 0}

/-- Grid data restrict to smaller open sets. -/
def restrict {W : Set (ComplexModel n)} (hWV : W ⊆ V) : GridData W where
  fa := G.fa
  fb := G.fb
  va := G.va
  vb := G.vb
  differentiableOn_fa := G.differentiableOn_fa.mono hWV
  differentiableOn_fb := G.differentiableOn_fb.mono hWV
  fa_add_vb := G.fa_add_vb
  fb_add_va := G.fb_add_va
  finite_fa := fun x hx => G.finite_fa x (hWV hx)
  finite_fb := fun x hx => G.finite_fb x (hWV hx)

theorem restrict_carrier {W : Set (ComplexModel n)} (hWV : W ⊆ V) :
    (G.restrict hWV).carrier = G.carrier ∩ W := by
  ext z
  constructor
  · rintro ⟨hzW, ha, hb⟩
    exact ⟨⟨hWV hzW, ha, hb⟩, hzW⟩
  · rintro ⟨⟨_, ha, hb⟩, hzW⟩
    exact ⟨hzW, ha, hb⟩

/-- The complement of the grid in an open subset of `V` is open. -/
theorem isOpen_diff_carrier {O : Set (ComplexModel n)} (hO : IsOpen O) (hOV : O ⊆ V) :
    IsOpen (O \ G.carrier) := by
  have h1 := (G.differentiableOn_fa.continuousOn.mono hOV).isOpen_inter_preimage hO
    (isOpen_compl_singleton (x := (0 : ℂ)))
  have h2 := (G.differentiableOn_fb.continuousOn.mono hOV).isOpen_inter_preimage hO
    (isOpen_compl_singleton (x := (0 : ℂ)))
  convert h1.union h2 using 1
  ext z
  simp only [carrier, Set.mem_sdiff, mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage,
    mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hzO, hz⟩
    by_cases ha : G.fa z = 0
    · exact Or.inr ⟨hzO, fun hb => hz ⟨hOV hzO, ha, hb⟩⟩
    · exact Or.inl ⟨hzO, ha⟩
  · rintro (⟨hzO, ha⟩ | ⟨hzO, hb⟩)
    · exact ⟨hzO, fun h => ha h.2.1⟩
    · exact ⟨hzO, fun h => hb h.2.2⟩

/-- The first equation does not vanish identically near a point of `V`. -/
theorem exists_fa_ne_zero (hV : IsOpen V) {x : ComplexModel n} (hx : x ∈ V) :
    ∃ y ∈ V, G.fa y ≠ 0 := by
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV x hx
  have hc : 0 < ‖G.va‖ + 1 := by positivity
  obtain ⟨ρ, hρ, hρR, hρF⟩ := exists_radius_avoiding (G.finite_fa x hx) (div_pos hR hc)
  have hnorm : ‖((ρ : ℝ) : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  refine ⟨x + ((ρ : ℝ) : ℂ) • G.va, hRV ?_, fun h => hρF _ h hnorm⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hnorm]
  have h1 : ρ * (‖G.va‖ + 1) < R := (lt_div_iff₀ hc).mp hρR
  nlinarith [norm_nonneg G.va]

/-- A grid in a ball is Lebesgue null. -/
theorem volume_carrier_eq_zero {p : ComplexModel n} {δ : ℝ} (hδ : 0 < δ)
    (G : GridData (ball p δ)) : volume G.carrier = 0 := by
  obtain ⟨x₁, hx₁, hfx₁⟩ := G.exists_fa_ne_zero isOpen_ball (mem_ball_self hδ)
  refine measure_mono_null
    (show G.carrier ⊆ ball p δ ∩ G.fa ⁻¹' {0} from fun z hz => ⟨hz.1, hz.2.1⟩)
    (HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero volume isOpen_ball
      (convex_ball p δ) G.differentiableOn_fa hx₁ hfx₁)

/-- **Extension across one grid.**  A function plurisubharmonic off a grid in an open
subset `O` of `V` extends plurisubharmonically to `O`; the extension is the upper
regularization and keeps the original values off the grid. -/
theorem psh_extension {O : Set (ComplexModel n)} (hO : IsOpen O) (hOV : O ⊆ V)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (O \ G.carrier)) :
    PlurisubharmonicOn (PshCodimTwoExtension.extension G.carrier ψ) O ∧
      EqOn (PshCodimTwoExtension.extension G.carrier ψ) ψ (O \ G.carrier) := by
  have hOc := G.isOpen_diff_carrier hO hOV
  refine ⟨?_, fun y hy => PshCodimTwoExtension.extension_eq hψ hOc hy⟩
  have hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff G.carrier O ψ := by
    intro x hx
    by_cases hxc : x ∈ G.carrier
    · obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp hO x hx
      have hc : 0 < 1 + (‖G.va‖ + ‖G.vb‖) := by positivity
      obtain ⟨ρ, hρ, hρR, hρF⟩ := exists_radius_avoiding
        ((G.finite_fa x (hOV hx)).union (G.finite_fb x (hOV hx))) (div_pos hR hc)
      have hball : closedBall x ((1 + (‖G.va‖ + ‖G.vb‖)) * ρ) ⊆ O := by
        refine (closedBall_subset_ball ?_).trans hRO
        have := (lt_div_iff₀ hc).mp hρR
        linarith
      obtain ⟨δ, hδ, M, hM⟩ := exists_bound_off_grid hO
        (G.differentiableOn_fa.continuousOn.mono hOV) (G.differentiableOn_fb.continuousOn.mono hOV)
        G.fa_add_vb G.fb_add_va (fun z _ hzc => hzc.2) hψ hρ hball
        (fun t ht h => hρF t (Or.inl h) ht) (fun t ht h => hρF t (Or.inr h) ht)
      refine ⟨ball x δ ∩ O, inter_mem (ball_mem_nhds x hδ) (hO.mem_nhds hx), M,
        fun y hy hyc => hM y hy.1 ?_⟩
      by_contra h
      push Not at h
      exact hyc ⟨hOV hy.2, h⟩
    · obtain ⟨U, hU, C, hC⟩ := exists_nhds_bound_of_psh hψ ⟨hx, hxc⟩
      exact ⟨U, hU, C, fun y hy _ => hC y hy⟩
  refine PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus hO hψ hbound
    (g := ![G.fa, G.fb]) (fun i => ?_) (fun y hy => ?_)
  · fin_cases i
    · exact G.differentiableOn_fa.mono hOV
    · exact G.differentiableOn_fb.mono hOV
  · simp only [carrier, mem_ofPred_eq, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact ⟨fun h => h.2, fun h => ⟨hOV hy, h⟩⟩

end GridData

/-- **Extension across finitely many grids.**  A function plurisubharmonic off a finite
union of grids in an open subset `O` of `V` extends plurisubharmonically to `O`, keeping its
values off the grids.  The grids are removed one at a time. -/
theorem exists_psh_extension_of_grids {V : Set (ComplexModel n)} :
    ∀ {r : ℕ} (G : Fin r → GridData V) {O : Set (ComplexModel n)}, IsOpen O → O ⊆ V →
      ∀ {ψ : ComplexModel n → EReal}, PlurisubharmonicOn ψ (O \ ⋃ m, (G m).carrier) →
        ∃ w : ComplexModel n → EReal, PlurisubharmonicOn w O ∧
          EqOn w ψ (O \ ⋃ m, (G m).carrier)
  | 0, G, O, _, _, ψ, hψ => ⟨ψ, by simpa using hψ, fun _ _ => rfl⟩
  | r + 1, G, O, hO, hOV, ψ, hψ => by
    set O' := O \ (G 0).carrier with hO'def
    have hO' : IsOpen O' := (G 0).isOpen_diff_carrier hO hOV
    have hsplit : O' \ ⋃ m : Fin r, (G m.succ).carrier = O \ ⋃ m, (G m).carrier := by
      ext z
      simp only [hO'def, Set.mem_sdiff, mem_iUnion, Fin.exists_fin_succ]
      tauto
    obtain ⟨w', hw', hw'eq⟩ := exists_psh_extension_of_grids (fun m => G m.succ) hO'
      (sdiff_subset.trans hOV) (hsplit ▸ hψ)
    obtain ⟨hw, hweq⟩ := (G 0).psh_extension hO hOV hw'
    refine ⟨_, hw, fun y hy => ?_⟩
    have hy' : y ∈ O' \ ⋃ m : Fin r, (G m.succ).carrier := hsplit ▸ hy
    rw [hweq hy'.1, hw'eq hy']

/-- **Local upper bound off a set covered by grids.**  If `S ∩ B(p, δ)` is covered by
finitely many grids on `B(p, δ)` and `ψ` is plurisubharmonic on `B(p, δ) \ S`, then `ψ` is
bounded above near `p` off `S`.  The extension across the grids bounds `ψ` off the grids;
the grids are null, so the bound holds almost everywhere and hence everywhere off `S`. -/
theorem exists_bound_of_gridCover {p : ComplexModel n} {δ : ℝ} (hδ : 0 < δ) {r : ℕ}
    (G : Fin r → GridData (ball p δ)) {S : Set (ComplexModel n)}
    (hcover : S ∩ ball p δ ⊆ ⋃ m, (G m).carrier) (hSo : IsOpen (ball p δ \ S))
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (ball p δ \ S)) :
    ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ y ∈ U, y ∉ S → ψ y ≤ C := by
  have hsub : ball p δ \ ⋃ m, (G m).carrier ⊆ ball p δ \ S :=
    fun y hy => ⟨hy.1, fun hyS => hy.2 (hcover ⟨hyS, hy.1⟩)⟩
  obtain ⟨w, hw, hweq⟩ := exists_psh_extension_of_grids G isOpen_ball subset_rfl
    (hψ.mono hsub)
  obtain ⟨U₀, hU₀, C, hC⟩ := exists_nhds_bound_of_psh hw (mem_ball_self hδ)
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.mp (inter_mem hU₀ (ball_mem_nhds p hδ))
  refine ⟨ball p η, ball_mem_nhds p hη, C, ?_⟩
  have hnull : volume (⋃ m, (G m).carrier) = 0 :=
    measure_iUnion_null fun m => GridData.volume_carrier_eq_zero hδ (G m)
  have hΩ : IsOpen (ball p η ∩ (ball p δ \ S)) := isOpen_ball.inter hSo
  have h1 : ∀ᵐ y ∂(volume : Measure (ComplexModel n)), y ∉ ⋃ m, (G m).carrier :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  have hae : ∀ᵐ y ∂(volume : Measure (ComplexModel n)).restrict (ball p η ∩ (ball p δ \ S)),
      ψ y ≤ (fun _ => (C : EReal)) y := by
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem hΩ.measurableSet] with y hy1 hy2
    rw [← hweq ⟨hy2.2.1, hy1⟩]
    exact hC y (hηU hy2.1).1
  have hle := (hψ.mono inter_subset_right).le_of_ae_le hΩ upperSemicontinuousOn_const
    volume hae
  intro y hy hyS
  exact hle y ⟨hy, (hηU hy).2, hyS⟩

end SGPT.Unibranch.LocalParam
