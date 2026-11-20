import SGPT.Foundations.Analysis.FirstPass.Subgeodesics
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.FirstPass.PshRealConvexity
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

/-!
# Kiselman's minimum principle, strip instance: the proof

This module proves the statement that `Pending.KiselmanMinimumPrincipleInterface`
recorded as a named classical input: if `Φ` is plurisubharmonic on
`U ×ˢ complexTimeStrip` and depends on the time variable only through its real
part, then `y ↦ inf_{0<t<1} Φ (y, t)` is plurisubharmonic on `U`
(Kiselman 1978; Demailly, *Complex Analytic and Differential Geometry*,
Theorem I.7.5; Xia, SGPT, Proposition 1.2.8, `xia-sgpt:page-0029`).

The argument is the classical holomorphic-disc proof, specialised to the
strip, written in this project's extended-real disc language.

1. *Reduction to one complex line and one continuous majorant.*  The infimum
   `u` is upper semicontinuous and never `⊤`.  On a closed disc in `U`, the
   continuous majorants `uscSupConvolution` decrease to `u` on the boundary
   circle, and `circleSubmean_of_continuous_antitone_majorants` reduces the
   exact deficit inequality to `u c ≤ circleAverage g` for every continuous
   real `g` with `u < g` on the circle (`iInf_slices_le_circleAverage`).
2. *Quasi-convexity in time.*  For fixed `z`, the strict sublevel sets
   `{s ∈ (0,1) | Φ (z, s) < C}` are intervals (`convex_slice_sublevel`): an
   imaginary-translation-invariant PSH function cannot have a strict interior
   maximum (`PlurisubharmonicOn.comp_re_no_finite_strict_interior_max`).  No
   finiteness of `Φ` is needed.
3. *A continuous time selection.*  Compactness of the circle gives finitely
   many times `t_j` with `Φ (z, t_j) < g z` on an open cover; an `infDist`
   partition of unity glues them into a continuous `w`, and step 2 keeps
   `Φ (z, w z) < g z`.  A compact-thickening argument gives a uniform slack
   `δ`.
4. *A holomorphic disc.*  Approximate `w` within `δ` on the circle by a
   global harmonic `h` (`exists_global_harmonic_uniformApproxOn_sphere`),
   write `h = re F` with `F` entire, and keep `h` in `(0,1)` on the closed
   disc by the maximum principle.  Then `ζ ↦ Φ (ζ, F ζ)` is PSH
   (`HolomorphicPullback.plurisubharmonicOn_comp_holomorphic`), equals
   `Φ (ζ, h ζ)` by imaginary-translation invariance, and lies below `g` on
   the circle; so `u c ≤ Φ (c, h c) ≤ circleAverage g`.

Values `⊥` are allowed throughout: the conclusion is the project's
`PlurisubharmonicOn`, which admits `⊥`.
-/

open Filter Set Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrincipleProof

open FirstPass

noncomputable section

/-! ### Semicontinuity bookkeeping -/

/-- Upper semicontinuity is preserved by precomposition with a map continuous
at the point. -/
theorem uscAt_comp {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : Y → EReal} {φ : X → Y} {x : X}
    (hf : UpperSemicontinuousAt f (φ x)) (hφ : ContinuousAt φ x) :
    UpperSemicontinuousAt (fun x' => f (φ x')) x :=
  fun y hy => hφ.tendsto.eventually (hf y hy)

/-- On an open set where `f` is upper semicontinuous, the locus where `f`
lies strictly below a continuous real function is open. -/
theorem isOpen_setOf_lt_of_upperSemicontinuousAt {X : Type*} [TopologicalSpace X]
    {V : Set X} (hV : IsOpen V) {f : X → EReal}
    (hf : ∀ x ∈ V, UpperSemicontinuousAt f x) {g : X → ℝ} (hg : Continuous g) :
    IsOpen {x | x ∈ V ∧ f x < (g x : EReal)} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxV, hlt⟩
  obtain ⟨q, hfq, hqg⟩ := EReal.exists_between_coe_real hlt
  have hqg' : q < g x := EReal.coe_lt_coe_iff.mp hqg
  filter_upwards [hV.mem_nhds hxV, hf x hxV (q : EReal) hfq,
    hg.continuousAt.tendsto.eventually (lt_mem_nhds hqg')] with y hyV hyf hyg
  exact ⟨hyV, hyf.trans (EReal.coe_lt_coe_iff.mpr hyg)⟩

/-! ### Time slices on a product with the strip -/

variable {W : Set ℂ} {Ψ : ℂ × ℂ → EReal}

/-- A time slice of a PSH function on `W ×ˢ complexTimeStrip` is PSH on the
strip. -/
theorem slice_plurisubharmonicOn
    (hΨ : PlurisubharmonicOn Ψ (W ×ˢ complexTimeStrip)) {z : ℂ} (hz : z ∈ W) :
    PlurisubharmonicOn (fun τ : ℂ => Ψ (z, τ)) complexTimeStrip := by
  have h := hΨ.comp_affine (ContinuousLinearMap.inr ℂ ℂ ℂ) ((z, 0) : ℂ × ℂ)
  convert h using 1
  · funext τ
    simp
  · ext τ
    simp [hz]

/-- The same slice, seen as a function of the real part of time. -/
theorem slice_re_plurisubharmonicOn
    (hΨ : PlurisubharmonicOn Ψ (W ×ˢ complexTimeStrip))
    (hinv : ∀ ζ τ σ : ℂ, τ.re = σ.re → Ψ (ζ, τ) = Ψ (ζ, σ)) {z : ℂ} (hz : z ∈ W) :
    PlurisubharmonicOn (fun τ : ℂ => Ψ (z, ((τ.re : ℝ) : ℂ)))
      (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  have h := slice_plurisubharmonicOn hΨ hz
  have hfun : (fun τ : ℂ => Ψ (z, ((τ.re : ℝ) : ℂ))) = fun τ : ℂ => Ψ (z, τ) := by
    funext τ
    exact hinv z _ _ (by simp)
  rw [hfun]
  exact h

/-- **Quasi-convexity in time.**  If the slice lies strictly below `C` at two
real times `a ≤ b` of the strip, it lies strictly below `C` at every time in
between.  No finiteness is assumed: the slice may take the value `⊥`. -/
theorem slice_lt_of_le_of_le
    (hΨ : PlurisubharmonicOn Ψ (W ×ˢ complexTimeStrip))
    (hinv : ∀ ζ τ σ : ℂ, τ.re = σ.re → Ψ (ζ, τ) = Ψ (ζ, σ)) {z : ℂ} (hz : z ∈ W)
    {a b t : ℝ} (ha : 0 < a) (hb : b < 1) (hat : a ≤ t) (htb : t ≤ b) {C : EReal}
    (hCa : Ψ (z, (a : ℂ)) < C) (hCb : Ψ (z, (b : ℂ)) < C) :
    Ψ (z, (t : ℂ)) < C := by
  let v : ℝ → EReal := fun s => Ψ (z, (s : ℂ))
  have hv : PlurisubharmonicOn (fun τ : ℂ => v τ.re) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) :=
    slice_re_plurisubharmonicOn hΨ hinv hz
  rcases eq_or_lt_of_le hat with rfl | hat'
  · exact hCa
  rcases eq_or_lt_of_le htb with rfl | htb'
  · exact hCb
  by_contra hcon
  have hcon' : C ≤ v t := not_lt.mp hcon
  have habI : Icc a b ⊆ Ioo (0 : ℝ) 1 :=
    fun s hs => ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have husc : UpperSemicontinuousOn v (Icc a b) := by
    have hmap : MapsTo (fun s : ℝ => (s : ℂ)) (Icc a b) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
      intro s hs
      simpa using habI hs
    have := hv.upperSemicontinuousOn.comp Complex.continuous_ofReal.continuousOn hmap
    simpa [Function.comp_def, v] using this
  obtain ⟨x, hx, hmax⟩ :=
    husc.exists_isMaxOn ⟨a, left_mem_Icc.mpr (hat'.trans htb').le⟩ isCompact_Icc
  have htx : v t ≤ v x := hmax ⟨hat'.le, htb'.le⟩
  have hxtop : v x ≠ ⊤ := by
    have h := (hv (x : ℂ) (by simpa using habI hx)).ne_top
    simpa [v] using h
  have hCx : C ≤ v x := hcon'.trans htx
  have hax : v a < v x := hCa.trans_le hCx
  have hbx : v b < v x := hCb.trans_le hCx
  have hxbot : v x ≠ ⊥ := ne_bot_of_gt hax
  have hxI : x ∈ Ioo a b := by
    refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
    · rintro rfl
      exact lt_irrefl _ hax
    · rintro rfl
      exact lt_irrefl _ hbx
  have hxcoe : v x = (((v x).toReal : ℝ) : EReal) := (EReal.coe_toReal hxtop hxbot).symm
  exact hv.comp_re_no_finite_strict_interior_max habI hxI
    (fun y hy => (hmax hy).trans hxcoe.le) hxcoe (lt_of_lt_of_eq hax hxcoe)
    (lt_of_lt_of_eq hbx hxcoe)

/-- The strict sublevel sets of a time slice, inside the open unit interval,
are convex. -/
theorem convex_slice_sublevel
    (hΨ : PlurisubharmonicOn Ψ (W ×ˢ complexTimeStrip))
    (hinv : ∀ ζ τ σ : ℂ, τ.re = σ.re → Ψ (ζ, τ) = Ψ (ζ, σ)) {z : ℂ} (hz : z ∈ W)
    (C : EReal) :
    Convex ℝ {s : ℝ | s ∈ Ioo (0 : ℝ) 1 ∧ Ψ (z, (s : ℂ)) < C} := by
  rw [convex_iff_ordConnected]
  refine ⟨fun a ha b hb t ht => ⟨⟨ha.1.1.trans_le ht.1, ht.2.trans_lt hb.1.2⟩, ?_⟩⟩
  exact slice_lt_of_le_of_le hΨ hinv hz ha.1.1 hb.1.2 ht.1 ht.2 ha.2 hb.2

/-! ### Composition with a holomorphic graph -/

/-- A PSH function of two complex variables, restricted to the graph of an
entire function, is PSH.  This transports
`HolomorphicPullback.plurisubharmonicOn_comp_holomorphic` from the model spaces
`ComplexModel 1`, `ComplexModel 2` to `ℂ`, `ℂ × ℂ`. -/
theorem plurisubharmonicOn_comp_graph {V : Set (ℂ × ℂ)}
    (hΨ : PlurisubharmonicOn Ψ V) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hmaps : ∀ ζ ∈ Ω, (ζ, F ζ) ∈ V) :
    PlurisubharmonicOn (fun ζ => Ψ (ζ, F ζ)) Ω := by
  let e1 : ComplexModel 1 ≃L[ℂ] ℂ := PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)
  let e2 : ComplexModel 2 ≃L[ℂ] ℂ × ℂ :=
    (EuclideanSpace.equiv (Fin 2) ℂ).trans
      (ContinuousLinearEquiv.piFinTwo ℂ (fun _ : Fin 2 => ℂ))
  let E2 : ComplexModel 2 →L[ℂ] ℂ × ℂ := e2
  have h2 : PlurisubharmonicOn (fun q => Ψ (E2 q)) (E2 ⁻¹' V) :=
    hΨ.comp_continuousLinearMap E2
  let G : ComplexModel 1 → ComplexModel 2 := fun a => e2.symm (e1 a, F (e1 a))
  have hG : Differentiable ℂ G := by
    have h1 : Differentiable ℂ (fun a : ComplexModel 1 => (e1 a, F (e1 a))) :=
      e1.differentiable.prodMk (hF.comp e1.differentiable)
    exact e2.symm.differentiable.comp h1
  let A : Set (ComplexModel 1) := e1 ⁻¹' Ω
  have hA : IsOpen A := hΩ.preimage e1.continuous
  have hGA : MapsTo G A (E2 ⁻¹' V) := by
    intro a ha
    have hE : E2 (G a) = (e1 a, F (e1 a)) := by
      simp [E2, G]
    simp only [mem_preimage, hE]
    exact hmaps _ ha
  have h3 : PlurisubharmonicOn (fun a => Ψ (E2 (G a))) A :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hA hG.differentiableOn hGA h2
  have h4 := h3.comp_continuousLinearMap (e1.symm : ℂ →L[ℂ] ComplexModel 1)
  convert h4 using 1
  · funext ζ
    simp [E2, G]
  · ext ζ
    simp [A]

/-! ### The core inequality on one complex line -/

/-- **Core of Kiselman's argument.**  Let `Ψ` be PSH on `W ×ˢ complexTimeStrip`
and independent of the imaginary part of time.  If a continuous real `g` lies
strictly above the slice infimum on the boundary of a closed disc in `W`, then
the slice infimum at the centre is at most the circle average of `g`. -/
theorem iInf_slices_le_circleAverage (hW : IsOpen W)
    (hΨ : PlurisubharmonicOn Ψ (W ×ˢ complexTimeStrip))
    (hinv : ∀ ζ τ σ : ℂ, τ.re = σ.re → Ψ (ζ, τ) = Ψ (ζ, σ))
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hD : closedBall c R ⊆ W)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hlt : ∀ z ∈ sphere c R,
      (⨅ t : ↥(Ioo (0 : ℝ) 1), Ψ (z, ((t : ℝ) : ℂ))) < (g z : EReal)) :
    (⨅ t : ↥(Ioo (0 : ℝ) 1), Ψ (c, ((t : ℝ) : ℂ))) ≤
      ((Real.circleAverage g c R : ℝ) : EReal) := by
  classical
  -- Upper semicontinuity of `Ψ` along real times.
  have husc : ∀ p : ℂ × ℝ, p.1 ∈ W → p.2 ∈ Ioo (0 : ℝ) 1 →
      UpperSemicontinuousAt (fun q : ℂ × ℝ => Ψ (q.1, (q.2 : ℂ))) p := by
    intro p hp1 hp2
    have hp2' : (p.2 : ℂ) ∈ complexTimeStrip := by
      rw [mem_complexTimeStrip, Complex.ofReal_re]
      exact hp2
    have hmem : (p.1, (p.2 : ℂ)) ∈ W ×ˢ complexTimeStrip := Set.mk_mem_prod hp1 hp2'
    exact uscAt_comp (φ := fun q : ℂ × ℝ => (q.1, (q.2 : ℂ))) (x := p)
      (hΨ _ hmem).upperSemicontinuousAt
      ((continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd)).continuousAt)
  have hsphereW : sphere c R ⊆ W := sphere_subset_closedBall.trans hD
  -- Step 1: a finite open cover of the circle by good times.
  let O : ↥(Ioo (0 : ℝ) 1) → Set ℂ := fun t =>
    {z | z ∈ W ∩ ball c (R + 1) ∧ Ψ (z, ((t : ℝ) : ℂ)) < (g z : EReal)}
  have hOopen : ∀ t, IsOpen (O t) := by
    intro t
    apply isOpen_setOf_lt_of_upperSemicontinuousAt (hW.inter isOpen_ball) _ hg
    intro z hz
    exact uscAt_comp (φ := fun z : ℂ => ((z, (t : ℝ)) : ℂ × ℝ)) (x := z)
      (husc (z, (t : ℝ)) hz.1 t.2) (continuous_id.prodMk continuous_const).continuousAt
  have hcover : sphere c R ⊆ ⋃ t, O t := by
    intro z hz
    obtain ⟨t, ht⟩ := iInf_lt_iff.mp (hlt z hz)
    refine mem_iUnion.mpr ⟨t, ⟨hsphereW hz, ?_⟩, ht⟩
    rw [mem_ball, mem_sphere.mp hz]
    linarith
  obtain ⟨T, hT⟩ := (isCompact_sphere c R).elim_finite_subcover O hOopen hcover
  -- Step 2: an `infDist` partition of unity subordinate to the cover.
  let d : ↥(Ioo (0 : ℝ) 1) → ℂ → ℝ := fun t z => infDist z (O t)ᶜ
  have hfar : ∀ t, c + ((R + 1 : ℝ) : ℂ) ∈ (O t)ᶜ := by
    intro t hmem
    have hb := hmem.1.2
    rw [mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < R + 1)] at hb
    exact lt_irrefl _ hb
  have hdpos : ∀ t z, z ∈ O t ↔ 0 < d t z := by
    intro t z
    have h := (hOopen t).isClosed_compl.notMem_iff_infDist_pos (x := z) ⟨_, hfar t⟩
    rw [Set.mem_compl_iff, not_not] at h
    exact h
  have hdnonneg : ∀ t z, 0 ≤ d t z := fun t z => infDist_nonneg
  have hdcont : ∀ t, Continuous (d t) := fun t => continuous_infDist_pt _
  let D : ℂ → ℝ := fun z => ∑ t ∈ T, d t z
  have hDpos : ∀ z ∈ sphere c R, 0 < D z := by
    intro z hz
    obtain ⟨t, htT, hzt⟩ := mem_iUnion₂.mp (hT hz)
    exact Finset.sum_pos' (fun t _ => hdnonneg t z) ⟨t, htT, (hdpos t z).mp hzt⟩
  let w : ℂ → ℝ := fun z => (∑ t ∈ T, d t z * (t : ℝ)) / D z
  have hwcont : ContinuousOn w (sphere c R) := by
    apply ContinuousOn.div
    · exact (continuous_finsetSum _ fun t _ => (hdcont t).mul continuous_const).continuousOn
    · exact (continuous_finsetSum _ fun t _ => hdcont t).continuousOn
    · exact fun z hz => (hDpos z hz).ne'
  -- Step 3: by quasi-convexity, the glued time is still good.
  have hwgood : ∀ z ∈ sphere c R,
      w z ∈ Ioo (0 : ℝ) 1 ∧ Ψ (z, ((w z : ℝ) : ℂ)) < (g z : EReal) := by
    intro z hz
    have hconv := convex_slice_sublevel hΨ hinv (hsphereW hz) (g z : EReal)
    have hD0 : D z ≠ 0 := (hDpos z hz).ne'
    have hsupp : ∀ t ∈ T, d t z / D z ≠ 0 → 0 < d t z := by
      intro t _ ht
      refine lt_of_le_of_ne (hdnonneg t z) (fun h0 => ht ?_)
      rw [← h0, zero_div]
    have hsum1 : ∑ t ∈ T.filter (fun t => 0 < d t z), d t z / D z = 1 := by
      rw [Finset.sum_filter_of_ne hsupp, ← Finset.sum_div]
      exact div_self hD0
    have hweq : w z = ∑ t ∈ T.filter (fun t => 0 < d t z), (d t z / D z) • (t : ℝ) := by
      rw [Finset.sum_filter_of_ne]
      · simp only [w, smul_eq_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
      · intro t ht hne
        refine hsupp t ht fun h0 => hne ?_
        rw [h0, zero_smul]
    have hmemS : ∀ t ∈ T.filter (fun t => 0 < d t z),
        (t : ℝ) ∈ {s : ℝ | s ∈ Ioo (0 : ℝ) 1 ∧ Ψ (z, (s : ℂ)) < (g z : EReal)} := by
      intro t ht
      have hzt : z ∈ O t := (hdpos t z).mpr (Finset.mem_filter.mp ht).2
      exact ⟨t.2, hzt.2⟩
    have hwS := hconv.sum_mem
      (fun t _ => div_nonneg (hdnonneg t z) (hDpos z hz).le) hsum1 hmemS
    rw [← hweq] at hwS
    exact hwS
  -- Step 4: uniform slack around the graph of the selection.
  let V : Set (ℂ × ℝ) := {p | p.1 ∈ W ∧ p.2 ∈ Ioo (0 : ℝ) 1}
  have hVopen : IsOpen V :=
    (hW.preimage continuous_fst).inter (isOpen_Ioo.preimage continuous_snd)
  let S : Set (ℂ × ℝ) := {p | p ∈ V ∧ Ψ (p.1, (p.2 : ℂ)) < (g p.1 : EReal)}
  have hSopen : IsOpen S :=
    isOpen_setOf_lt_of_upperSemicontinuousAt hVopen (fun p hp => husc p hp.1 hp.2)
      (g := fun p : ℂ × ℝ => g p.1) (hg.comp continuous_fst)
  let Γ : Set (ℂ × ℝ) := (fun z => (z, w z)) '' sphere c R
  have hΓ : IsCompact Γ :=
    (isCompact_sphere c R).image_of_continuousOn (continuousOn_id.prodMk hwcont)
  have hΓS : Γ ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨hsphereW hz, (hwgood z hz).1⟩, (hwgood z hz).2⟩
  obtain ⟨δ, hδ, hthick⟩ := hΓ.exists_thickening_subset_open hSopen hΓS
  -- Step 5: harmonic approximation of the selection.
  obtain ⟨h, hh, happ⟩ := exists_global_harmonic_uniformApproxOn_sphere c hR hwcont hδ
  have hhS : ∀ z ∈ sphere c R,
      h z ∈ Ioo (0 : ℝ) 1 ∧ Ψ (z, ((h z : ℝ) : ℂ)) < (g z : EReal) := by
    intro z hz
    have hmem : (z, h z) ∈ thickening δ Γ := by
      rw [mem_thickening_iff]
      refine ⟨(z, w z), ⟨z, hz, rfl⟩, ?_⟩
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt hδ (happ z hz)
    have hS := hthick hmem
    exact ⟨hS.1.2, hS.2⟩
  -- Step 6: the maximum principle keeps `h` inside `(0,1)` on the closed disc.
  have hsne : (sphere c R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  have hhcont : Continuous h := continuousOn_univ.mp hh.continuousOn
  obtain ⟨z1, hz1, hmax1⟩ :=
    (isCompact_sphere c R).exists_isMaxOn hsne hhcont.continuousOn
  obtain ⟨z2, hz2, hmin2⟩ :=
    (isCompact_sphere c R).exists_isMinOn hsne hhcont.continuousOn
  have hhpsh : PlurisubharmonicOn (fun z => (h z : EReal)) univ :=
    SGPT.Foundations.Analysis.HarmonicOnNhd.plurisubharmonicOn hh
  have hnegpsh : PlurisubharmonicOn (fun z => ((-h) z : EReal)) univ :=
    SGPT.Foundations.Analysis.HarmonicOnNhd.plurisubharmonicOn hh.neg
  have hup : ∀ z ∈ closedBall c R, h z < 1 := by
    intro z hz
    have hle := hhpsh.le_const_on_closedBall_of_le_on_sphere hR (subset_univ _)
      (C := h z1) (fun y hy => EReal.coe_le_coe_iff.mpr (hmax1 hy)) z hz
    exact (EReal.coe_le_coe_iff.mp hle).trans_lt (hhS z1 hz1).1.2
  have hlow : ∀ z ∈ closedBall c R, 0 < h z := by
    intro z hz
    have hle := hnegpsh.le_const_on_closedBall_of_le_on_sphere hR (subset_univ _)
      (C := -h z2)
      (fun y hy => by
        show (((-h) y : ℝ) : EReal) ≤ ((-h z2 : ℝ) : EReal)
        exact EReal.coe_le_coe_iff.mpr (by simpa using hmin2 hy)) z hz
    have h' : -h z ≤ -h z2 := by simpa using EReal.coe_le_coe_iff.mp hle
    linarith [(hhS z2 hz2).1.1]
  -- Step 7: the holomorphic disc `ζ ↦ (ζ, F ζ)` with `re F = h`.
  obtain ⟨F, hFan, hFre⟩ := hh.exists_analyticOnNhd_univ_re_eq
  have hFdiff : Differentiable ℂ F := fun z => (hFan z (mem_univ z)).differentiableAt
  have hFre' : ∀ z, (F z).re = h z := fun z => congrFun hFre z
  let Ω : Set ℂ := {ζ | (ζ, F ζ) ∈ W ×ˢ complexTimeStrip}
  have hΩopen : IsOpen Ω :=
    (hW.prod isOpen_complexTimeStrip).preimage (continuous_id.prodMk hFdiff.continuous)
  have hDΩ : closedBall c R ⊆ Ω := by
    intro ζ hζ
    refine Set.mk_mem_prod (hD hζ) ?_
    show F ζ ∈ complexTimeStrip
    rw [mem_complexTimeStrip, hFre']
    exact ⟨hlow ζ hζ, hup ζ hζ⟩
  have hψ : PlurisubharmonicOn (fun ζ => Ψ (ζ, F ζ)) Ω :=
    plurisubharmonicOn_comp_graph hΨ hFdiff hΩopen (fun ζ hζ => hζ)
  have hψeq : ∀ ζ, Ψ (ζ, F ζ) = Ψ (ζ, ((h ζ : ℝ) : ℂ)) := fun ζ =>
    hinv ζ _ _ (by rw [Complex.ofReal_re, hFre'])
  have hcenter :=
    SGPT.Foundations.Analysis.FirstPass.PlurisubharmonicOn.le_circleAverage_of_continuous_majorant
      hψ hR hDΩ hg
      (fun z hz => by
        show Ψ (z, F z) ≤ (g z : EReal)
        rw [hψeq]
        exact (hhS z hz).2.le)
      (fun ε hε => exists_global_harmonic_uniformApproxOn_sphere c hR hg.continuousOn hε)
  have hc01 : h c ∈ Ioo (0 : ℝ) 1 :=
    ⟨hlow c (mem_closedBall_self hR.le), hup c (mem_closedBall_self hR.le)⟩
  calc (⨅ t : ↥(Ioo (0 : ℝ) 1), Ψ (c, ((t : ℝ) : ℂ)))
      ≤ Ψ (c, ((h c : ℝ) : ℂ)) :=
        iInf_le (fun t : ↥(Ioo (0 : ℝ) 1) => Ψ (c, ((t : ℝ) : ℂ))) ⟨h c, hc01⟩
    _ = Ψ (c, F c) := (hψeq c).symm
    _ ≤ _ := hcenter

/-! ### Kiselman's minimum principle -/

/-- **Kiselman's minimum principle, strip instance.**  If `Φ` is
plurisubharmonic on `U ×ˢ complexTimeStrip` and depends on the time variable
only through its real part, then the pointwise infimum of its real-time slices
is plurisubharmonic on `U`.  The value `⊥` is allowed, so Xia's dichotomy
"identically `-∞` or PSH" is the single conclusion below.

Source: Demailly, *Complex Analytic and Differential Geometry*, Theorem I.7.5,
as quoted in Xia, SGPT, Proposition 1.2.8 (`xia-sgpt:page-0029`). -/
theorem plurisubharmonicOn_iInf_slices {m : ℕ} {U : Set (ComplexModel m)}
    (hU : IsOpen U) {Φ : ComplexModel m × ℂ → EReal}
    (hΦ : PlurisubharmonicOn Φ (U ×ˢ complexTimeStrip))
    (hinv : ∀ (y : ComplexModel m) (τ σ : ℂ), τ.re = σ.re → Φ (y, τ) = Φ (y, σ)) :
    PlurisubharmonicOn
      (fun y : ComplexModel m => ⨅ t : ↥(Ioo (0 : ℝ) 1), Φ (y, ((t : ℝ) : ℂ))) U := by
  set u : ComplexModel m → EReal :=
    fun y => ⨅ t : ↥(Ioo (0 : ℝ) 1), Φ (y, ((t : ℝ) : ℂ)) with hu_def
  have half : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hne_top : ∀ y ∈ U, u y ≠ ⊤ := by
    intro y hy
    have hmem : (y, (((1 / 2 : ℝ)) : ℂ)) ∈ U ×ˢ complexTimeStrip := by
      refine Set.mk_mem_prod hy ?_
      rw [mem_complexTimeStrip, Complex.ofReal_re]
      exact half
    exact ne_top_of_le_ne_top (hΦ _ hmem).ne_top
      (iInf_le (fun t : ↥(Ioo (0 : ℝ) 1) => Φ (y, ((t : ℝ) : ℂ))) ⟨1 / 2, half⟩)
  have husc_at : ∀ y ∈ U, ∀ t : ↥(Ioo (0 : ℝ) 1),
      UpperSemicontinuousAt (fun y' => Φ (y', ((t : ℝ) : ℂ))) y := by
    intro y hy t
    have hmem : (y, ((t : ℝ) : ℂ)) ∈ U ×ˢ complexTimeStrip := by
      refine Set.mk_mem_prod hy ?_
      rw [mem_complexTimeStrip, Complex.ofReal_re]
      exact t.2
    exact uscAt_comp (φ := fun y' => (y', ((t : ℝ) : ℂ))) (x := y)
      (hΦ _ hmem).upperSemicontinuousAt
      (continuous_id.prodMk continuous_const).continuousAt
  have husc : UpperSemicontinuousOn u U :=
    upperSemicontinuousOn_iInf fun t y hy =>
      (husc_at y hy t).upperSemicontinuousWithinAt U
  refine DiscPshOn.plurisubharmonicOn ⟨hne_top, husc, ?_⟩ hU
  intro x v r hr hDsub C hC
  -- Restrict to the complex line through `x` in the direction `v`.
  let L : ℂ × ℂ →L[ℂ] ComplexModel m × ℂ :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight v).prod (ContinuousLinearMap.snd ℂ ℂ ℂ)
  let Ψ : ℂ × ℂ → EReal := fun p => Φ (x + p.1 • v, p.2)
  let W : Set ℂ := {ζ | x + ζ • v ∈ U}
  have hlinecont : Continuous fun ζ : ℂ => x + ζ • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hWopen : IsOpen W := hU.preimage hlinecont
  have hΨ : PlurisubharmonicOn Ψ (W ×ˢ complexTimeStrip) := by
    have h := hΦ.comp_affine L ((x, 0) : ComplexModel m × ℂ)
    convert h using 1
    · funext p
      simp [Ψ, L]
    · ext p
      simp [W, L]
  have hinvΨ : ∀ ζ τ σ : ℂ, τ.re = σ.re → Ψ (ζ, τ) = Ψ (ζ, σ) :=
    fun ζ τ σ h => hinv _ τ σ h
  let wfun : ℂ → EReal := fun ζ => u (x + ζ • v)
  have hdisc : ∀ ζ ∈ closedBall (0 : ℂ) r, x + ζ • v ∈ affineClosedDisc x v r :=
    fun ζ hζ => ⟨ζ, hζ, rfl⟩
  have hDW : closedBall (0 : ℂ) r ⊆ W := fun ζ hζ => hDsub (hdisc ζ hζ)
  let K : Set ℂ := sphere (0 : ℂ) r
  have hKne : K.Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hKcl : K ⊆ closedBall 0 r := sphere_subset_closedBall
  have htopK : ∀ ζ ∈ K, wfun ζ ≠ ⊤ := fun ζ hζ => hne_top _ (hDW (hKcl hζ))
  have hCK : ∀ ζ ∈ K, wfun ζ ≤ (C : EReal) := fun ζ hζ => hC _ (hdisc ζ (hKcl hζ))
  have huscK : UpperSemicontinuousOn wfun K :=
    husc.comp hlinecont.continuousOn (fun ζ hζ => hDW (hKcl hζ))
  let g : ℕ → ℂ → ℝ := fun n => uscSupConvolution K wfun C n
  have hgcont : ∀ n, Continuous (g n) := fun n =>
    continuous_uscSupConvolution hKne htopK hCK n
  have hcenter : ∀ n, wfun 0 ≤ ((Real.circleAverage (g n) 0 r : ℝ) : EReal) := by
    intro n
    have hε : ∀ ε : ℝ, 0 < ε →
        wfun 0 ≤ ((Real.circleAverage (g n) 0 r + ε : ℝ) : EReal) := by
      intro ε hε
      have hcore := iInf_slices_le_circleAverage hWopen hΨ hinvΨ hr hDW
        (g := fun z => g n z + ε) ((hgcont n).add continuous_const)
        (fun z hz => (le_coe_uscSupConvolution hKne htopK hCK n hz).trans_lt
          (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)))
      have havg : Real.circleAverage (fun z => g n z + ε) 0 r =
          Real.circleAverage (g n) 0 r + ε := by
        rw [Real.circleAverage_fun_add (hgcont n).continuousOn.circleIntegrable'
          (circleIntegrable_const ε 0 r), Real.circleAverage_const]
      rw [havg] at hcore
      exact hcore
    by_contra hlt
    have hlt' : ((Real.circleAverage (g n) 0 r : ℝ) : EReal) < wfun 0 := not_le.mp hlt
    obtain ⟨B, hAB, hBw⟩ := EReal.exists_between_coe_real hlt'
    have hAB' : Real.circleAverage (g n) 0 r < B := EReal.coe_lt_coe_iff.mp hAB
    have hB := hε (B - Real.circleAverage (g n) 0 r) (by linarith)
    have hsimp : Real.circleAverage (g n) 0 r + (B - Real.circleAverage (g n) 0 r) = B := by
      ring
    rw [hsimp] at hB
    exact lt_irrefl _ (hB.trans_lt hBw)
  have hsub := circleSubmean_of_continuous_antitone_majorants (w := wfun) (0 : ℂ)
    (R := r) (C := C) g hgcont
    (fun n z _ => uscSupConvolution_le hKne htopK hCK n z)
    (fun t a b hab =>
      EReal.coe_le_coe_iff.mpr (uscSupConvolution_antitone hKne htopK hCK _ hab))
    (fun t => iInf_coe_uscSupConvolution hKne huscK htopK hCK
      (by rw [zero_add]; exact circleMap_mem_sphere 0 hr.le t))
    hcenter
  have hdef : circleDeficit u x v r C = circleDeficit wfun 0 1 r C := by
    simp only [circleDeficit, wfun, zero_add, smul_eq_mul, mul_one]
  have h0 : wfun 0 = u x := by
    simp [wfun]
  rw [hdef, ← h0]
  exact hsub

end

end SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrincipleProof
