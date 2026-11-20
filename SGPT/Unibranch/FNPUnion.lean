import SGPT.Unibranch.FNLChart
import SGPT.Foundations.Analysis.Pending.IrreducibleGermSheetBound
import SGPT.Foundations.Analysis.Pending.GermComponentDimension

/-!
# FN80 §5.3: the branched covering of a pure-dimensional germ in Noether position

Source: `[FN80]` Theorem 5.3.1, proof ("In a small neighborhood of `p`, we can represent
`S_j × ℂ` as a branched covering of `Δ^{j+1}` relative to suitable coordinates"), i.e. the
local parametrization theorem for pure-dimensional analytic sets (Grauert–Remmert;
Gunning–Rossi III.B; Demailly, *Complex analytic and differential geometry*, II.4.19).

The workspace (`SGPT.Foundations.Analysis.Pending.GermParametrization*`) provides, for an
irreducible analytic germ `A` at `0 ∈ ℂⁿ` in Noether position over the first `d`
coordinates, the pointwise parametrization data `ParametrizationData A` (minimal polynomials
`Q_k` of the fibre coordinates, a discriminant `δ`, …) and the parametrizing sets
`SetsData`.  Here we assemble from it the branched coverings of `[FN80]` §5:

* `CoverData A d`: what one irreducible component in Noether position over `ℂᵈ` provides,
  stated with an explicit `d` (`coverData_of_parametrizationData`): finite fibres and small
  fibre coordinates over small base points (roots of the monic `Q_k`), exactly `deg` points
  and local holomorphic sections over the complement of the discriminant, equations on `ℂᵈ`
  vanishing on `A ∩ B` for analytic germs `B ⊉ A`, and density of `A ∖ π⁻¹{h = 0}` for every
  holomorphic `h ≢ 0` on `ℂᵈ` (thinness of proper subgerms).
* `exists_isBranchedCovering_iUnion`: the union of finitely many irredundant components in
  Noether position over the SAME `ℂᵈ` is, on a small polydisc, a finite branched covering
  (`FNL.IsBranchedCovering`) of a ball of `ℂᵈ`; its discriminant is the product of the
  discriminants of the components and of equations `h_{ij} ∘ π` vanishing on `A_i ∩ A_j`,
  and its number of sheets is the sum of the degrees.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNP

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
open SGPT.Unibranch.FNL

variable {n : ℕ}

/-- A monic polynomial with complex coefficients has finitely many roots. -/
theorem finite_setOf_monicEval_eq_zero {E : Type*} (q : ℕ) (a : ℕ → E → ℂ) (x : E) :
    {t | monicEval q a x t = 0}.Finite := by
  classical
  open Polynomial in
  set p : ℂ[X] := X ^ q + ∑ j : Fin q, C (a j x) * X ^ (j : ℕ) with hp
  have hmonic : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have heval : monicEval q a x = fun t => p.eval t := by
    funext t
    simp [p, monicEval, Polynomial.eval_finsetSum, Finset.sum_range]
  have hset : {t | monicEval q a x t = 0} = (p.roots.toFinset : Set ℂ) := by
    ext t
    simp [heval, Polynomial.mem_roots hp0]
  rw [hset]
  exact Finset.finite_toSet _

theorem coordinateProjection_apply_of_lt {d : ℕ} (z : ComplexModel n) (k : Fin n)
    (hk : k.1 < d) : coordinateProjection n d z ⟨k.1, hk⟩ = z k := by
  rw [coordinateProjection_apply, dif_pos k.2]

theorem polydisc_subset_polydisc' {d : ℕ} {r₁ r₁' r₂ r₂' : ℝ} (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂') :
    polydisc n d r₁ r₂ ⊆ polydisc n d r₁' r₂' :=
  fun _ hz => ⟨hz.1.trans_le h₁, fun k hk => (hz.2 k hk).trans_le h₂⟩

/-- **The data of one irreducible component in Noether position over `ℂᵈ`** (first `d`
coordinates), with the dimension `d` explicit. -/
structure CoverData (A : Set (ComplexModel n)) (d : ℕ) : Prop where
  /-- Equations on the base vanishing on the intersection with an analytic germ `B ⊉ A`. -/
  eqn : ∀ B : Set (ComplexModel n), IsAnalyticGerm B → ¬ A ≤ᶠ[𝓝 0] B →
    ∃ h : ComplexModel d → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) ∧
      ¬ (∀ᶠ x in 𝓝 0, h x = 0) ∧
        ∀ᶠ z in 𝓝 0, z ∈ A → z ∈ B → h (coordinateProjection n d z) = 0
  /-- Density of `A ∖ π⁻¹{h = 0}` for every holomorphic `h ≢ 0` on the base. -/
  dense : ∀ h : ComplexModel d → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) →
    ¬ (∀ᶠ x in 𝓝 0, h x = 0) → ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      ∀ O : Set (ComplexModel n), IsOpen O → (O ∩ (A ∩ Ω)).Nonempty →
        ∃ y ∈ O ∩ (A ∩ Ω), h (coordinateProjection n d y) ≠ 0
  /-- Finite fibres, small fibre coordinates, generic fibres and local sections. -/
  main : ∃ ρ > 0, (∀ x : ComplexModel d,
      (A ∩ ball 0 ρ ∩ coordinateProjection n d ⁻¹' {x}).Finite) ∧
    (∀ ε > 0, ∃ η > 0, ∀ z ∈ A ∩ ball 0 ρ, ‖coordinateProjection n d z‖ < η →
      ∀ k : Fin n, d ≤ k.1 → ‖z k‖ < ε) ∧
    ∃ (deg : ℕ) (r₁ r₂ : ℝ) (disc : ComplexModel d → ℂ), 0 < r₁ ∧ 0 < r₂ ∧
      polydisc n d r₁ r₂ ⊆ ball 0 ρ ∧ DifferentiableOn ℂ disc (ball 0 r₁) ∧
      ¬ (∀ᶠ x in 𝓝 0, disc x = 0) ∧
      (∀ x : ComplexModel d, ‖x‖ < r₁ → disc x ≠ 0 →
        (A ∩ polydisc n d r₁ r₂ ∩ coordinateProjection n d ⁻¹' {x}).ncard = deg) ∧
      ∀ y ∈ A ∩ polydisc n d r₁ r₂, disc (coordinateProjection n d y) ≠ 0 →
        ∃ (U : Set (ComplexModel d)) (V : Set (ComplexModel n))
          (g : ComplexModel d → ComplexModel n),
          IsOpen U ∧ IsOpen V ∧ coordinateProjection n d y ∈ U ∧ y ∈ V ∧
          DifferentiableOn ℂ g U ∧ (∀ x ∈ U, coordinateProjection n d (g x) = x) ∧
          (∀ x ∈ U, g x ∈ A ∩ polydisc n d r₁ r₂) ∧
          ∀ z ∈ V, z ∈ A → coordinateProjection n d z ∈ U ∧ g (coordinateProjection n d z) = z

/-- **Parametrization data give `CoverData`.** -/
theorem coverData_of_parametrizationData {A : Set (ComplexModel n)} (hA : IsIrreducibleGerm A)
    (P : ParametrizationData A) (S : SetsData P) {d : ℕ} (hd : P.dim = d) : CoverData A d := by
  subst hd
  refine ⟨P.exists_eqn_of_not_le, ?_, ?_⟩
  · intro h hhd hh0
    have hπ : Tendsto (coordinateProjection n P.dim) (𝓝 0) (𝓝 0) := by
      simpa using (coordinateProjection n P.dim).continuous.tendsto 0
    have hcd : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
        DifferentiableAt ℂ (fun z => h (coordinateProjection n P.dim z)) z :=
      (hπ.eventually hhd).mono fun z hz =>
        hz.comp z (coordinateProjection n P.dim).differentiableAt
    have hB := isAnalyticGerm_zeroSet hcd
    have hAB : ¬ A ≤ᶠ[𝓝 0] {z | h (coordinateProjection n P.dim z) = 0} := by
      intro hle
      apply hh0
      refine P.base h hhd ?_
      filter_upwards [hle] with z hz hzA using hz hzA
    obtain ⟨Ω, hΩo, hΩ0, hΩ⟩ := IrreducibleGermLocal.exists_thin_nhds hA hB hAB
    exact ⟨Ω, hΩo, hΩ0, fun O hO hne => hΩ O hO hne⟩
  · refine ⟨P.rad, P.rad_pos, ?_, ?_, ?_⟩
    · -- every fibre coordinate is a root of the monic `Q_k(x, ·)`
      intro x
      classical
      set t : Fin n → Set ℂ := fun k =>
        if hk : k.1 < P.dim then {x ⟨k.1, hk⟩} else {s | monicEval (P.s k) (P.e k) x s = 0}
      have ht : (Set.univ.pi t).Finite := by
        refine Set.Finite.pi fun k => ?_
        simp only [t]
        split_ifs
        · exact finite_singleton _
        · exact finite_setOf_monicEval_eq_zero _ _ _
      refine Set.Finite.of_finite_image (f := fun z : ComplexModel n => (WithLp.ofLp z))
        (ht.subset ?_) (WithLp.ofLp_injective 2).injOn
      rintro _ ⟨z, ⟨⟨hzA, hzb⟩, hzx⟩, rfl⟩
      intro k _
      have hzx' : coordinateProjection n P.dim z = x := hzx
      simp only [t]
      split_ifs with hk
      · rw [← hzx', coordinateProjection_apply_of_lt z k hk]
        rfl
      · have := P.e_eq_zero z hzA hzb k (not_lt.mp hk)
        rw [hzx'] at this
        exact this
    · intro ε hε
      obtain ⟨η, hη, hroot⟩ := P.exists_root_bound hε
      exact ⟨η, hη, fun z hz hzη k hk => hroot _ hzη k _ (P.e_eq_zero z hz.1 hz.2 k hk)⟩
    · set r₁ := min S.r₁ P.rad with hr₁
      have hr₁0 : 0 < r₁ := lt_min S.r₁_pos P.rad_pos
      have hr₁S : r₁ ≤ S.r₁ := min_le_left _ _
      have hsub : polydisc n P.dim r₁ S.r₂ ⊆ polydisc n P.dim S.r₁ S.r₂ := polydisc_mono hr₁S
      refine ⟨P.deg, r₁, S.r₂, P.disc, hr₁0, S.r₂_pos, hsub.trans S.polydisc_subset,
        P.differentiableOn_disc.mono (ball_subset_ball (min_le_right _ _)),
        P.disc_not_eventually_zero, ?_, ?_⟩
      · intro x hx hdx
        have hxr : ‖x‖ < S.r₁ := hx.trans_le hr₁S
        rw [← S.ncard_fibre x hxr hdx]
        congr 1
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hzA, hz⟩, hzx⟩
          exact ⟨⟨hzA, hsub hz⟩, hzx⟩
        · rintro ⟨⟨hzA, hz⟩, hzx⟩
          exact ⟨⟨hzA, by rw [hzx]; exact hx, hz.2⟩, hzx⟩
      · intro y hy hdy
        obtain ⟨U, V, g, hU, hV, hyU, hyV, -, -, hg, hgπ, hgA, hVA⟩ :=
          S.local_graph y ⟨hy.1, hsub hy.2⟩ hdy
        refine ⟨U ∩ ball 0 r₁, V ∩ polydisc n P.dim r₁ S.r₂, g, hU.inter isOpen_ball,
          hV.inter (isOpen_polydisc _ _ _ _), ⟨hyU, mem_ball_zero_iff.2 hy.2.1⟩, ⟨hyV, hy.2⟩,
          hg.mono inter_subset_left, fun x hx => hgπ x hx.1, fun x hx => ?_, fun z hz hzA => ?_⟩
        · refine ⟨(hgA x hx.1).1, ?_, (hgA x hx.1).2.2⟩
          rw [hgπ x hx.1]
          exact mem_ball_zero_iff.1 hx.2
        · obtain ⟨h1, h2⟩ := hVA z hz.1 hzA
          exact ⟨⟨h1, mem_ball_zero_iff.2 hz.2.1⟩, h2⟩

/-- A nonzero product of the discriminant factors has nonzero factors. -/
theorem ne_zero_of_mul_prod_ne_zero {r d : ℕ} {disc : Fin r → ComplexModel d → ℂ}
    {h : Fin r → Fin r → ComplexModel d → ℂ} {x : ComplexModel d}
    (hx : (∏ i, disc i x) * ∏ ij : Fin r × Fin r, h ij.1 ij.2 x ≠ 0) :
    (∀ i, disc i x ≠ 0) ∧ ∀ i j, h i j x ≠ 0 := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
  refine ⟨fun i => (Finset.prod_ne_zero_iff.mp h1) i (Finset.mem_univ _), fun i j => ?_⟩
  exact (Finset.prod_ne_zero_iff.mp h2) (i, j) (Finset.mem_univ _)

/-- **The union of irredundant components in Noether position over the same `ℂᵈ` is a finite
branched covering** on a small polydisc, inside any given neighbourhood of `0`. -/
theorem exists_isBranchedCovering_iUnion {r d : ℕ} {A : Fin r → Set (ComplexModel n)}
    (hA : ∀ i, CoverData (A i) d) (hAg : ∀ i, IsAnalyticGerm (A i))
    (hpw : Pairwise fun i j => ¬ (A i ≤ᶠ[𝓝 0] A j)) {N : Set (ComplexModel n)} (hN : N ∈ 𝓝 0) :
    ∃ η s : ℝ, 0 < η ∧ 0 < s ∧ polydisc n d η s ⊆ N ∧ ∃ (deg : ℕ) (δ : ComplexModel d → ℂ),
      IsBranchedCovering ((⋃ i, A i) ∩ polydisc n d η s) (coordinateProjection n d)
        (ball 0 η) deg δ := by
  classical
  set π := coordinateProjection n d with hπ
  -- equations killing the pairwise intersections
  have hh : ∀ i j : Fin r, ∃ h : ComplexModel d → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) ∧
      ¬ (∀ᶠ x in 𝓝 0, h x = 0) ∧
      (i ≠ j → ∀ᶠ z in 𝓝 0, z ∈ A i → z ∈ A j → h (π z) = 0) := by
    intro i j
    by_cases hij : i = j
    · refine ⟨fun _ => 1, Eventually.of_forall fun _ => differentiableAt_const _, ?_,
        fun h => absurd hij h⟩
      intro h0
      obtain ⟨x, hx⟩ := h0.exists
      exact one_ne_zero hx
    · obtain ⟨h, h1, h2, h3⟩ := (hA i).eqn (A j) (hAg j) (hpw hij)
      exact ⟨h, h1, h2, fun _ => h3⟩
  choose h hhd hh0 hhA using hh
  choose ρ hρ hfin hsmall deg r₁ r₂ disc hr₁ hr₂ hsub hdiff hne hcard hgraph using
    fun i => (hA i).main
  -- the discriminant
  set δ : ComplexModel d → ℂ := fun x => (∏ i, disc i x) * ∏ ij : Fin r × Fin r, h ij.1 ij.2 x
    with hδdef
  have hdiscd : ∀ i, ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (disc i) x := fun i =>
    eventually_of_mem (ball_mem_nhds 0 (hr₁ i)) fun x hx =>
      (hdiff i).differentiableAt (isOpen_ball.mem_nhds hx)
  obtain ⟨hP1, hP2⟩ := IrreducibleGermConnected.finset_prod_holomorphic Finset.univ disc hdiscd hne
  obtain ⟨hQ1, hQ2⟩ := IrreducibleGermConnected.finset_prod_holomorphic Finset.univ
    (fun ij : Fin r × Fin r => h ij.1 ij.2) (fun ij => hhd ij.1 ij.2) (fun ij => hh0 ij.1 ij.2)
  have hδd : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ δ x :=
    (hP1.and hQ1).mono fun x hx => hx.1.mul hx.2
  have hδ0 : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel d), δ x = 0 :=
    IrreducibleGermConnected.not_eventually_mul_eq_zero hP1 hQ1 hP2 hQ2
  obtain ⟨ηδ, hηδ, hηδs⟩ := Metric.eventually_nhds_iff_ball.1 hδd
  -- density
  choose Ω hΩo hΩ0 hΩ using fun i => (hA i).dense δ hδd hδ0
  -- relative closedness of the components
  choose ρc hρc hρco using fun i => GermComponentDimension.exists_isOpen_ball_diff (hAg i)
  -- a ball of `ℂⁿ` on which everything holds
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ N ∧ (∀ i, z ∈ ball 0 (ρ i)) ∧
      (∀ i, z ∈ Ω i) ∧ (∀ i, z ∈ ball 0 (ρc i)) ∧
      ∀ i j, i ≠ j → z ∈ A i → z ∈ A j → h i j (π z) = 0 := by
    refine (show ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ N from hN).and ((eventually_all.2 fun i => ball_mem_nhds 0 (hρ i)).and
      ((eventually_all.2 fun i => (hΩo i).mem_nhds (hΩ0 i)).and
      ((eventually_all.2 fun i => ball_mem_nhds 0 (hρc i)).and
      (eventually_all.2 fun i => eventually_all.2 fun j => ?_))))
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hij' => absurd hij hij'
    · exact (hhA i j hij).mono fun z hz _ => hz
  obtain ⟨R, hR, hRs⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- the fibre radius `s`
  have hle : ∀ {a : ℝ}, 0 < a → ∀ᶠ c in 𝓝[>] (0 : ℝ), c ≤ a := fun ha =>
    mem_of_superset (Ioo_mem_nhdsGT ha) fun c hc => hc.2.le
  obtain ⟨s, hs0, hsR, hsr₂⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ R / (n + 1) ∧ ∀ i, s ≤ r₂ i := by
    have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ≤ R / (n + 1) := hle (by positivity)
    have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ i, c ≤ r₂ i := eventually_all.2 fun i => hle (hr₂ i)
    obtain ⟨c, ⟨hc1, hc2⟩, hc0⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
    exact ⟨c, hc0, hc1, hc2⟩
  -- smallness of the fibre coordinates
  choose η' hη' hη's using fun i => hsmall i (s / 2) (by positivity)
  -- the base radius `η`
  obtain ⟨η, hη0, hηs, hηr₁, hηη', hηδ'⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ s ∧ (∀ i, η ≤ r₁ i) ∧
      (∀ i, η ≤ η' i) ∧ η ≤ ηδ := by
    have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ≤ s := hle hs0
    have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ i, c ≤ r₁ i := eventually_all.2 fun i => hle (hr₁ i)
    have h3 : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ i, c ≤ η' i := eventually_all.2 fun i => hle (hη' i)
    have h4 : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ≤ ηδ := hle hηδ
    obtain ⟨c, ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩, hc0⟩ :=
      ((((h1.and h2).and h3).and h4).and self_mem_nhdsWithin).exists
    exact ⟨c, hc0, hc1, hc2, hc3, hc4⟩
  set Δ := polydisc n d η s with hΔdef
  have hΔR : Δ ⊆ ball 0 R := by
    refine (polydisc_subset_polydisc' hηs le_rfl).trans ?_
    refine (polydisc_subset_ball hs0).trans (ball_subset_ball ?_)
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).1 hsR
    linarith
  have hΔi : ∀ i, Δ ⊆ polydisc n d (r₁ i) (r₂ i) := fun i =>
    polydisc_subset_polydisc' (hηr₁ i) (hsr₂ i)
  -- small fibre coordinates
  have hK2 : ∀ i, ∀ z ∈ A i, z ∈ ball (0 : ComplexModel n) (ρ i) → ‖π z‖ < η →
      ∀ k : Fin n, d ≤ k.1 → ‖z k‖ < s / 2 := fun i z hzA hzρ hzη =>
    hη's i z ⟨hzA, hzρ⟩ (hzη.trans_le (hηη' i))
  -- the fibre of a component over a small base point
  have hK3 : ∀ i, ∀ x : ComplexModel d, ‖x‖ < η →
      A i ∩ Δ ∩ π ⁻¹' {x} = A i ∩ polydisc n d (r₁ i) (r₂ i) ∩ π ⁻¹' {x} := by
    intro i x hx
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hzA, hz⟩, hzx⟩
      exact ⟨⟨hzA, hΔi i hz⟩, hzx⟩
    · rintro ⟨⟨hzA, hz⟩, hzx⟩
      have hzη : ‖π z‖ < η := by rw [hzx]; exact hx
      refine ⟨⟨hzA, hzη, fun k hk => ?_⟩, hzx⟩
      have := hK2 i z hzA (hsub i hz) hzη k hk
      linarith
  -- the discriminant does not vanish where a factor does not
  have hδne := fun x (hx : δ x ≠ 0) => ne_zero_of_mul_prod_ne_zero hx
  have hδdiff : DifferentiableOn ℂ δ (ball 0 ηδ) := fun x hx =>
    (hηδs x hx).differentiableWithinAt
  refine ⟨η, s, hη0, hs0, fun z hz => (hRs z (hΔR hz)).1, ∑ i, deg i, δ, ?_⟩
  refine
    { isOpen_base := isOpen_ball
      mapsTo := fun z hz => mem_ball_zero_iff.2 hz.2.1
      isCompact_inter_preimage := ?_
      finite_fibre := ?_
      differentiableOn_disc := hδdiff.mono (ball_subset_ball hηδ')
      frequently_disc_ne := ?_
      ncard_fibre := ?_
      local_graph := ?_
      subset_closure_generic := ?_ }
  · -- properness
    intro K hKD hK
    set F : Set (ComplexModel n) := {z | ∀ k : Fin n, d ≤ k.1 → ‖z k‖ ≤ s / 2} with hFdef
    set G : Set (ComplexModel n) := ⋂ i, (ball 0 (ρc i) \ A i) with hGdef
    have hFc : IsClosed F := by
      have : F = ⋂ k : Fin n, ⋂ (_ : d ≤ k.1), {z : ComplexModel n | ‖z k‖ ≤ s / 2} := by
        ext z; simp [hFdef]
      rw [this]
      exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_le
        (continuous_norm.comp ((continuous_apply k).comp (PiLp.continuous_ofLp 2 _)))
        continuous_const
    have hGo : IsOpen G := isOpen_iInter_of_finite hρco
    have heq : ((⋃ i, A i) ∩ Δ) ∩ π ⁻¹' K = π ⁻¹' K ∩ F ∩ Gᶜ := by
      ext z
      constructor
      · rintro ⟨⟨hzA, hzΔ⟩, hzK⟩
        obtain ⟨i, hzi⟩ := mem_iUnion.1 hzA
        refine ⟨⟨hzK, fun k hk => (hK2 i z hzi ((hRs z (hΔR hzΔ)).2.1 i) hzΔ.1 k hk).le⟩, ?_⟩
        intro hzG
        exact (mem_iInter.1 hzG i).2 hzi
      · rintro ⟨⟨hzK, hzF⟩, hzG⟩
        have hzΔ : z ∈ Δ := ⟨mem_ball_zero_iff.1 (hKD hzK),
          fun k hk => (hzF k hk).trans_lt (by linarith)⟩
        have hzR := hRs z (hΔR hzΔ)
        rw [mem_compl_iff, hGdef, mem_iInter, not_forall] at hzG
        obtain ⟨i, hi⟩ := hzG
        have hzi : z ∈ A i := by
          by_contra hc
          exact hi ⟨hzR.2.2.2.1 i, hc⟩
        exact ⟨⟨mem_iUnion.2 ⟨i, hzi⟩, hzΔ⟩, hzK⟩
    rw [heq]
    refine Metric.isCompact_of_isClosed_isBounded
      (((hK.isClosed.preimage π.continuous).inter hFc).inter hGo.isClosed_compl) ?_
    refine isBounded_ball.subset fun z hz => hΔR ?_
    exact ⟨mem_ball_zero_iff.1 (hKD hz.1.1), fun k hk => (hz.1.2 k hk).trans_lt (by linarith)⟩
  · -- finite fibres
    intro x hx
    refine (Set.finite_iUnion fun i => hfin i x).subset ?_
    rintro z ⟨⟨hzA, hzΔ⟩, hzx⟩
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hzA
    exact mem_iUnion.2 ⟨i, ⟨hzi, (hRs z (hΔR hzΔ)).2.1 i⟩, hzx⟩
  · -- the discriminant is nowhere locally identically zero
    intro z hz
    have hcl := RiemannExtension.dense_compl_zeroSet isOpen_ball
      (convex_ball (0 : ComplexModel d) ηδ).isPreconnected hδdiff (mem_ball_self hηδ) hδ0
      (ball_subset_ball hηδ' hz)
    exact (mem_closure_iff_frequently.1 hcl).mono fun w hw => hw.2
  · -- generic fibres
    intro x hx hδx
    have hxη : ‖x‖ < η := mem_ball_zero_iff.1 hx
    obtain ⟨hdx, hhx⟩ := hδne x hδx
    have hU : FNL.fibre ((⋃ i, A i) ∩ Δ) π x = ⋃ i, (A i ∩ Δ ∩ π ⁻¹' {x}) := by
      ext z
      simp only [FNL.fibre, mem_inter_iff, mem_iUnion, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨⟨⟨i, hzi⟩, hzΔ⟩, hzx⟩
        exact ⟨i, ⟨hzi, hzΔ⟩, hzx⟩
      · rintro ⟨i, ⟨hzi, hzΔ⟩, hzx⟩
        exact ⟨⟨⟨i, hzi⟩, hzΔ⟩, hzx⟩
    have hfinF : ∀ i, (A i ∩ Δ ∩ π ⁻¹' {x}).Finite := fun i =>
      (hfin i x).subset fun z hz => ⟨⟨hz.1.1, (hRs z (hΔR hz.1.2)).2.1 i⟩, hz.2⟩
    have hdisj : Pairwise (Function.onFun Disjoint fun i => A i ∩ Δ ∩ π ⁻¹' {x}) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      rintro z ⟨⟨hzi, hzΔ⟩, hzx⟩ ⟨⟨hzj, -⟩, -⟩
      have h0 := (hRs z (hΔR hzΔ)).2.2.2.2 i j hij hzi hzj
      have hzx' : π z = x := hzx
      rw [hzx'] at h0
      exact hhx i j h0
    rw [hU, Set.ncard_iUnion_of_finite hfinF hdisj, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hK3 i x hxη]
    exact hcard i x (hxη.trans_le (hηr₁ i)) (hdx i)
  · -- local holomorphic sections
    intro x hx hδx
    obtain ⟨hdx, hhx⟩ := hδne _ hδx
    obtain ⟨hxA, hxΔ⟩ := hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hxA
    obtain ⟨U, V, g, hUo, hVo, hxU, hxV, hg, hgπ, hgA, hVA⟩ :=
      hgraph i x ⟨hxi, hΔi i hxΔ⟩ (hdx i)
    set W : Fin r → Set (ComplexModel n) := fun j =>
      if j = i then univ else ball 0 (ρc j) \ A j with hWdef
    have hWo : ∀ j, IsOpen (W j) := fun j => by
      simp only [hWdef]
      split_ifs
      · exact isOpen_univ
      · exact hρco j
    refine ⟨U ∩ ball 0 η, V ∩ Δ ∩ ⋂ j, W j, g, hUo.inter isOpen_ball,
      (hVo.inter (isOpen_polydisc _ _ _ _)).inter (isOpen_iInter_of_finite hWo),
      ⟨hxU, mem_ball_zero_iff.2 hxΔ.1⟩, ⟨⟨hxV, hxΔ⟩, mem_iInter.2 fun j => ?_⟩,
      inter_subset_right, hg.mono inter_subset_left, fun w hw => ?_, fun y hy => ?_⟩
    · simp only [hWdef]
      split_ifs with hji
      · exact mem_univ _
      · refine ⟨(hRs x (hΔR hxΔ)).2.2.2.1 j, fun hxj => ?_⟩
        exact hhx i j ((hRs x (hΔR hxΔ)).2.2.2.2 i j (Ne.symm hji) hxi hxj)
    · obtain ⟨hwU, hwη⟩ := hw
      have hgw := hgA w hwU
      have hπw : π (g w) = w := hgπ w hwU
      have hgwη : ‖π (g w)‖ < η := by rw [hπw]; exact mem_ball_zero_iff.1 hwη
      refine ⟨⟨mem_iUnion.2 ⟨i, hgw.1⟩, hgwη, fun k hk => ?_⟩, hπw⟩
      have := hK2 i (g w) hgw.1 (hsub i hgw.2) hgwη k hk
      linarith
    · obtain ⟨⟨hyA, hyΔ⟩, ⟨hyV, -⟩, hyW⟩ := hy
      obtain ⟨j, hyj⟩ := mem_iUnion.1 hyA
      have hji : j = i := by
        by_contra hji
        have := mem_iInter.1 hyW j
        simp only [hWdef, if_neg hji] at this
        exact this.2 hyj
      subst hji
      obtain ⟨h1, h2⟩ := hVA y hyV hyj
      exact ⟨⟨h1, mem_ball_zero_iff.2 hyΔ.1⟩, h2⟩
  · -- the generic part is dense
    intro x hx
    obtain ⟨hxA, hxΔ⟩ := hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hxA
    rw [_root_.mem_closure_iff]
    intro o ho hxo
    obtain ⟨y, ⟨⟨hyo, hyΔ⟩, hyA, -⟩, hyδ⟩ := hΩ i (o ∩ Δ) (ho.inter (isOpen_polydisc _ _ _ _))
      ⟨x, ⟨hxo, hxΔ⟩, hxi, (hRs x (hΔR hxΔ)).2.2.1 i⟩
    exact ⟨y, hyo, ⟨mem_iUnion.2 ⟨i, hyA⟩, hyΔ⟩, hyδ⟩

end SGPT.Unibranch.FNP
