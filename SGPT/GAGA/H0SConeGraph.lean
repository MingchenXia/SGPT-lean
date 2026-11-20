import SGPT.GAGA.H0SImmersionGraph

/-!
# The affine cone over a projective submanifold is a local graph off the vertex


Let `M` be a compact complex manifold of dimension `n` (in the `SGPT.Foundations.Analysis`
charts) and `Φ : M → ℙᴺ` a *holomorphic embedding* (`IsHolomorphicEmbedding`): continuous,
injective, and in every affine chart `U_i = {Z_i ≠ 0}` of `ℙᴺ` and every preferred chart of `M`
holomorphic with injective derivative.  Its affine cone
`affineCone (range Φ) = {Z ∈ ℂ^{N+1} : Z = 0 or [Z] ∈ Φ(M)}`:

* is closed and stable under complex scalars (`isClosed_affineCone`, `smul_mem_affineCone`);
* near every point `y₀ = (Φ p₀)` of an affine chart, `Φ(M) ∩ U_i` is the graph of a holomorphic
  map in suitable linear coordinates, and the graph points come from points of `M` near `p₀`
  through a holomorphic map (`exists_affine_graph`): compactness of `M` and injectivity of `Φ`
  make `Φ` a closed embedding, so points of `Φ(M)` near `Φ p₀` come from points near `p₀`;
* is, off the vertex, a local holomorphic graph of codimension `N - n`
  (`isLocalGraphAt_affineCone`), in the sense `SGPT.GAGA.H0.IsLocalGraphAt` of lane H0-GAGA.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0S

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.GAGA.H0

variable {n N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The map `Φ` read in the affine chart `U_i` of `ℙᴺ` and the preferred chart of `M` at `p`. -/
def chartMap (Φ : M → ComplexProjectiveSpace N) (p : M) (i : Fin (N + 1)) :
    ComplexModel n → ComplexModel N :=
  fun z => affineChart i (Φ ((complexChartAt (n := n) p).val.symm z))

/-- **Holomorphic embedding into `ℙᴺ`**: `Φ` is continuous and injective, and in the affine
charts of `ℙᴺ` and the preferred charts of `M` it is holomorphic near every point with injective
derivative (an immersion). -/
structure IsHolomorphicEmbedding (Φ : M → ComplexProjectiveSpace N) : Prop where
  continuous : Continuous Φ
  injective : Function.Injective Φ
  holomorphic : ∀ (p : M) (i : Fin (N + 1)), Φ p ∈ (affineChart i).source →
    ∀ᶠ z in 𝓝 ((complexChartAt (n := n) p).val p), DifferentiableAt ℂ (chartMap Φ p i) z
  immersion : ∀ (p : M) (i : Fin (N + 1)), Φ p ∈ (affineChart i).source →
    Function.Injective (fderiv ℂ (chartMap Φ p i) ((complexChartAt (n := n) p).val p))

/-- The affine cone `{Z ∈ ℂ^{N+1} : Z = 0 or [Z] ∈ S}` over a set `S ⊆ ℙᴺ`. -/
def affineCone (S : Set (ComplexProjectiveSpace N)) : Set (ComplexModel (N + 1)) :=
  {Z | ∀ h : WithLp.ofLp Z ≠ 0, mk (WithLp.ofLp Z) h ∈ S}

theorem zero_mem_affineCone (S : Set (ComplexProjectiveSpace N)) : (0 : ComplexModel (N + 1)) ∈
    affineCone S := fun h => absurd rfl h

theorem smul_mem_affineCone {S : Set (ComplexProjectiveSpace N)} (c : ℂ) {Z : ComplexModel (N + 1)}
    (hZ : Z ∈ affineCone S) : c • Z ∈ affineCone S := by
  intro h
  have hc : c ≠ 0 := by rintro rfl; exact h (by simp)
  have hZ0 : WithLp.ofLp Z ≠ 0 := by intro h0; exact h (by simp [h0])
  have := hZ hZ0
  have hs : WithLp.ofLp (c • Z) = c • WithLp.ofLp Z := rfl
  simp only [hs] at h ⊢
  rwa [mk_smul hZ0 hc]

theorem isClosed_affineCone {S : Set (ComplexProjectiveSpace N)} (hS : IsClosed S) :
    IsClosed (affineCone S) := by
  rw [← isOpen_compl_iff]
  have hcompl : (affineCone S)ᶜ = WithLp.ofLp ⁻¹' (Subtype.val ''
      ((fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => mk v.1 v.2) ⁻¹' Sᶜ)) := by
    ext Z
    simp only [affineCone, mem_compl_iff, Set.mem_ofPred_eq, not_forall, mem_preimage, mem_image,
      Subtype.exists, exists_and_right, exists_eq_right]
  rw [hcompl]
  refine IsOpen.preimage (PiLp.continuous_ofLp 2 _) ?_
  exact (isOpen_ne.isOpenMap_subtype_val) _ (hS.isOpen_compl.preimage continuous_mk_subtype)

/-- Membership in the cone off the hyperplane `Z_i = 0`. -/
theorem mem_affineCone_iff {S : Set (ComplexProjectiveSpace N)} {Z : ComplexModel (N + 1)}
    {i : Fin (N + 1)} (hZi : Z i ≠ 0) :
    Z ∈ affineCone S ↔ affinePoint i (affineRatio i (WithLp.ofLp Z)) ∈ S := by
  have hZ0 : WithLp.ofLp Z ≠ 0 := fun h => hZi (by simpa using congrFun h i)
  constructor
  · intro h
    have := h hZ0
    rwa [mk_eq_affinePoint i hZ0 hZi] at this
  · intro h h'
    rwa [mk_eq_affinePoint i h' hZi]

section Graph

variable [CompactSpace M] {Φ : M → ComplexProjectiveSpace N}

/-- **`Φ(M)` is locally a holomorphic graph in the affine charts.**  For `Φ p₀ ∈ U_i`, with
`y₀ = Φ p₀` in the chart `U_i ≅ ℂᴺ` and `e` the preferred chart of `M` at `p₀`: there are linear
coordinates `L₀ : ℂᴺ ≅ ℂⁿ × ℂ^{N-n}` (with `L₀ (Dφ v) = (v, 0)` for the derivative of `Φ` in
these charts), `ε > 0`, an open `O ⊆ ℂⁿ` and holomorphic `g : O → ℂ^{N-n}`, `ψ : O → ℂⁿ` such
that `ψ` maps `O` into the chart image of `Φ⁻¹(U_i)`, and for `y ∈ B(y₀, ε)`: `(L₀ y)₁ ∈ O`,
`[y] ∈ Φ(M) ↔ (L₀ y)₂ = g (L₀ y)₁`, and then `[y] = Φ(e⁻¹(ψ (L₀ y)₁))`. -/
theorem exists_affine_graph (hΦ : IsHolomorphicEmbedding (n := n) Φ) (p₀ : M) (i : Fin (N + 1))
    (hp₀ : Φ p₀ ∈ (affineChart i).source) :
    n ≤ N ∧ ∃ (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n)) (ε : ℝ)
      (O : Set (ComplexModel n)) (g : ComplexModel n → ComplexModel (N - n))
      (ψ : ComplexModel n → ComplexModel n),
      0 < ε ∧ IsOpen O ∧ DifferentiableOn ℂ g O ∧ DifferentiableOn ℂ ψ O ∧
      (∀ x ∈ O, ψ x ∈ (complexChartAt (n := n) p₀).val.target ∧
        Φ ((complexChartAt (n := n) p₀).val.symm (ψ x)) ∈ (affineChart i).source) ∧
      (∀ v, (L0 (fderiv ℂ (chartMap (n := n) Φ p₀ i) ((complexChartAt (n := n) p₀).val p₀) v)).2 = 0) ∧
      ∀ y ∈ ball (affineChart i (Φ p₀)) ε, (L0 y).1 ∈ O ∧
        (affinePoint i y ∈ range Φ ↔ (L0 y).2 = g (L0 y).1) ∧
        ((L0 y).2 = g (L0 y).1 → ψ (L0 y).1 ∈ (complexChartAt (n := n) p₀).val.target ∧
          Φ ((complexChartAt (n := n) p₀).val.symm (ψ (L0 y).1)) = affinePoint i y) := by
  set e := (complexChartAt (n := n) p₀).val with he
  set φ := chartMap (n := n) Φ p₀ i with hφdef
  have hp₀e : p₀ ∈ e.source := mem_complexChartAt_source p₀
  set z₀ := e p₀ with hz₀def
  obtain ⟨S, hSd, hSo, hz₀S⟩ := _root_.eventually_nhds_iff.mp (hΦ.holomorphic p₀ i hp₀)
  have hWo : IsOpen (Φ ⁻¹' (affineChart i).source) :=
    (affineChart i).open_source.preimage hΦ.continuous
  set U := S ∩ (e.target ∩ e.symm ⁻¹' (Φ ⁻¹' (affineChart i).source)) with hUdef
  have hUo : IsOpen U := hSo.inter (e.isOpen_inter_preimage_symm hWo)
  have hz₀U : z₀ ∈ U := ⟨hz₀S, e.map_source hp₀e, by
    simp only [mem_preimage, hz₀def, e.left_inv hp₀e]; exact hp₀⟩
  have hφU : DifferentiableOn ℂ φ U := fun z hz => (hSd z hz.1).differentiableWithinAt
  obtain ⟨hnN, L0, U₀, O, g, ψ, hU₀o, hz₀U₀, hU₀U, hOo, hg, hψ, hL0, hU₀graph, hOinv⟩ :=
    exists_local_graph_of_injective_fderiv hUo hφU hz₀U (hΦ.immersion p₀ i hp₀)
  refine ⟨hnN, L0, ?_⟩
  -- points of `Φ(M)` near `Φ p₀` come from points near `p₀`
  have hemb : Topology.IsClosedEmbedding Φ := hΦ.continuous.isClosedEmbedding hΦ.injective
  have hWnhds : e.source ∩ e ⁻¹' U₀ ∈ 𝓝 p₀ :=
    (e.isOpen_inter_preimage hU₀o).mem_nhds ⟨hp₀e, hz₀U₀⟩
  rw [hemb.isInducing.nhds_eq_comap, Filter.mem_comap] at hWnhds
  obtain ⟨Ow, hOw, hOwW⟩ := hWnhds
  have hy₀ : φ z₀ = affineChart i (Φ p₀) := by
    simp only [hφdef, chartMap, hz₀def, ← he, e.left_inv hp₀e]
  have hnhds1 : affineChart i '' (Ow ∩ (affineChart i).source) ∈ 𝓝 (affineChart i (Φ p₀)) :=
    (affineChart i).image_mem_nhds hp₀
      (Filter.inter_mem hOw ((affineChart i).open_source.mem_nhds hp₀))
  have hnhds2 : {y : ComplexModel N | (L0 y).1 ∈ O} ∈ 𝓝 (affineChart i (Φ p₀)) := by
    have hc : Continuous fun y : ComplexModel N => (L0 y).1 := (L0.continuous).fst
    refine hc.continuousAt.preimage_mem_nhds (hOo.mem_nhds ?_)
    rw [← hy₀]
    exact (hU₀graph z₀ hz₀U₀).1
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hnhds1 hnhds2)
  refine ⟨ε, O, g, ψ, hε, hOo, hg, hψ, fun x hx => ?_, hL0, fun y hy => ?_⟩
  · have hU := hU₀U (hOinv x hx).1
    exact ⟨hU.2.1, hU.2.2⟩
  obtain ⟨⟨o, ⟨hoOw, hosrc⟩, hoy⟩, hyO⟩ := hεsub hy
  -- the backward direction, with the preimage point
  have hback : (L0 y).2 = g (L0 y).1 → ψ (L0 y).1 ∈ e.target ∧
      Φ (e.symm (ψ (L0 y).1)) = affinePoint i y := by
    intro hgy
    obtain ⟨hψU₀, hψx⟩ := hOinv _ hyO
    have hψU := hU₀U hψU₀
    have h2 := (hU₀graph _ hψU₀).2.2
    rw [hψx] at h2
    have hφy : φ (ψ (L0 y).1) = y := by
      apply L0.injective
      exact Prod.ext hψx (h2.trans hgy.symm)
    refine ⟨hψU.2.1, ?_⟩
    have hsrc : Φ (e.symm (ψ (L0 y).1)) ∈ (affineChart i).source := hψU.2.2
    have h3 : affinePoint i (φ (ψ (L0 y).1)) = Φ (e.symm (ψ (L0 y).1)) := by
      change (affineChart i).symm (affineChart i (Φ (e.symm (ψ (L0 y).1)))) = _
      rw [(affineChart i).left_inv hsrc]
    rw [← h3, hφy]
  refine ⟨hyO, ⟨fun hmem => ?_, fun hgy => ⟨_, (hback hgy).2⟩⟩, hback⟩
  -- the forward direction
  obtain ⟨q, hq⟩ := hmem
  have hoq : Φ q = o := by
    rw [hq, ← hoy]
    change (affineChart i).symm (affineChart i o) = o
    exact (affineChart i).left_inv hosrc
  have hqW : q ∈ e.source ∩ e ⁻¹' U₀ := hOwW (show Φ q ∈ Ow by rw [hoq]; exact hoOw)
  have h1 := (hU₀graph (e q) hqW.2).2.2
  have hφq : φ (e q) = y := by
    simp only [hφdef, chartMap, ← he, e.left_inv hqW.1, hoq, hoy]
  rwa [hφq] at h1

/-! ### Linear coordinates adapted to the cone -/

/-- The numerators `Z ↦ (Z_{i.succAbove k})_k` of the affine coordinates of `U_i`. -/
def numer (i : Fin (N + 1)) : ComplexModel (N + 1) →L[ℂ] ComplexModel N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z => WithLp.toLp 2 (fun k => Z (i.succAbove k))
      map_add' := fun Z W => by ext k; simp
      map_smul' := fun c Z => by ext k; simp }

@[simp] theorem numer_apply (i : Fin (N + 1)) (Z : ComplexModel (N + 1)) (k : Fin N) :
    numer i Z k = Z (i.succAbove k) := rfl

theorem affineRatio_eq_smul_numer (i : Fin (N + 1)) (Z : ComplexModel (N + 1)) :
    affineRatio i (WithLp.ofLp Z) = (Z i)⁻¹ • numer i Z := by
  ext k
  simp [div_eq_inv_mul]

/-- The tail `u ↦ (u_{k+1})_k`. -/
def tl : ComplexModel (n + 1) →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 (fun k => u k.succ)
      map_add' := fun u w => by ext k; simp
      map_smul' := fun c u => by ext k; simp }

@[simp] theorem tl_apply (u : ComplexModel (n + 1)) (k : Fin n) : tl u k = u k.succ := rfl

/-- The coordinates `Z ↦ ((Z_i, (L₀ Z')₁), (L₀ Z')₂)`, `Z'` the numerators of `U_i`. -/
def coneCoords (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
    (i : Fin (N + 1)) : ComplexModel (N + 1) →ₗ[ℂ] ComplexModel (n + 1) × ComplexModel (N - n) where
  toFun Z := (WithLp.toLp 2 (Fin.cons (Z i) (fun k => (L0 (numer i Z)).1 k)), (L0 (numer i Z)).2)
  map_add' Z W := by
    refine Prod.ext ?_ ?_
    · ext j
      refine Fin.cases ?_ (fun k => ?_) j <;> simp
    · simp
  map_smul' c Z := by
    refine Prod.ext ?_ ?_
    · ext j
      refine Fin.cases ?_ (fun k => ?_) j <;> simp
    · simp

theorem coneCoords_fst_zero (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
    (i : Fin (N + 1)) (Z : ComplexModel (N + 1)) : (coneCoords L0 i Z).1 0 = Z i := by
  simp [coneCoords]

theorem tl_coneCoords_fst (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
    (i : Fin (N + 1)) (Z : ComplexModel (N + 1)) : tl (coneCoords L0 i Z).1 = (L0 (numer i Z)).1 := by
  ext k
  simp [coneCoords]

theorem coneCoords_snd (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
    (i : Fin (N + 1)) (Z : ComplexModel (N + 1)) : (coneCoords L0 i Z).2 = (L0 (numer i Z)).2 :=
  rfl

theorem coneCoords_injective (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
    (i : Fin (N + 1)) : Function.Injective (coneCoords L0 i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Z hZ
  have h1 : Z i = 0 := by rw [← coneCoords_fst_zero L0 i Z, hZ]; rfl
  have h2 : L0 (numer i Z) = 0 := by
    refine Prod.ext ?_ ?_
    · rw [← tl_coneCoords_fst L0 i Z, hZ]; ext k; simp
    · rw [← coneCoords_snd L0 i Z, hZ]; rfl
  have h3 : numer i Z = 0 := by simpa using h2
  ext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa using h1
  · simpa using congrArg (fun w : ComplexModel N => w k) h3

/-- The adapted coordinates as a linear equivalence (`n ≤ N`). -/
def coneEquiv (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
    (i : Fin (N + 1)) (hnN : n ≤ N) :
    ComplexModel (N + 1) ≃L[ℂ] ComplexModel (n + 1) × ComplexModel (N - n) :=
  (LinearEquiv.ofBijective (coneCoords L0 i) ⟨coneCoords_injective L0 i, by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact coneCoords_injective L0 i
    · rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
        finrank_euclideanSpace_fin]
      omega⟩).toContinuousLinearEquiv

theorem coneEquiv_apply (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
    (i : Fin (N + 1)) (hnN : n ≤ N) (Z : ComplexModel (N + 1)) :
    coneEquiv L0 i hnN Z = coneCoords L0 i Z := rfl

/-- **The affine cone over a holomorphically embedded compact complex manifold is, off the
vertex, a local holomorphic graph of codimension `N - n`.** -/
theorem isLocalGraphAt_affineCone (hΦ : IsHolomorphicEmbedding (n := n) Φ)
    {Z₀ : ComplexModel (N + 1)} (hZ₀ : Z₀ ∈ affineCone (range Φ)) (h0 : Z₀ ≠ 0) :
    IsLocalGraphAt (affineCone (range Φ)) (N - n) Z₀ := by
  obtain ⟨i, hZi⟩ : ∃ i, Z₀ i ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (by ext j; simpa using h j)
  have hv₀ : WithLp.ofLp Z₀ ≠ 0 := fun h => hZi (by simpa using congrFun h i)
  obtain ⟨p₀, hp₀⟩ := hZ₀ hv₀
  have hp₀src : Φ p₀ ∈ (affineChart i).source := by
    rw [hp₀]; exact (mk_mem_affineChart_source_iff i hv₀).mpr hZi
  have hy₀ : affineChart i (Φ p₀) = (Z₀ i)⁻¹ • numer i Z₀ := by
    rw [hp₀, affineChart_mk i hv₀ hZi, affineRatio_eq_smul_numer]
  obtain ⟨hnN, L0, ε, O, g, ψ, hε, hOo, hg, -, -, -, hgraph⟩ := exists_affine_graph hΦ p₀ i hp₀src
  rw [hy₀] at hgraph
  -- the affine point depends continuously on `Z` near `Z₀`
  have hcont : ContinuousAt (fun Z : ComplexModel (N + 1) => (Z i)⁻¹ • numer i Z) Z₀ :=
    ((((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt).inv₀ hZi).smul
      (numer i).continuous.continuousAt)
  have hev : ∀ᶠ Z in 𝓝 Z₀, Z i ≠ 0 ∧ (Z i)⁻¹ • numer i Z ∈ ball ((Z₀ i)⁻¹ • numer i Z₀) ε :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt.eventually_ne hZi).and
      (hcont.eventually (ball_mem_nhds _ hε))
  obtain ⟨ε', hε', hball⟩ := Metric.eventually_nhds_iff.mp hev
  -- the graph map in the cone coordinates
  set G : ComplexModel (n + 1) → ComplexModel (N - n) := fun u => (u 0) • g ((u 0)⁻¹ • tl u)
  have hfc : ContinuousOn (fun u : ComplexModel (n + 1) => (u 0)⁻¹ • tl u) {u | u 0 ≠ 0} :=
    fun u hu => ((((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).continuous.continuousAt).inv₀
      hu).smul tl.continuous.continuousAt).continuousWithinAt
  have hopen0 : IsOpen {u : ComplexModel (n + 1) | u 0 ≠ 0} :=
    isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).continuous continuous_const
  set U' := {u : ComplexModel (n + 1) | u 0 ≠ 0} ∩
    (fun u : ComplexModel (n + 1) => (u 0)⁻¹ • tl u) ⁻¹' O
  have hU' : IsOpen U' := hfc.isOpen_inter_preimage hopen0 hOo
  have hGd : DifferentiableOn ℂ G U' := by
    intro u hu
    have h0' : DifferentiableAt ℂ (fun u : ComplexModel (n + 1) => u 0) u :=
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).differentiableAt
    have h1 : DifferentiableAt ℂ (fun u : ComplexModel (n + 1) => (u 0)⁻¹ • tl u) u :=
      (h0'.inv hu.1).smul tl.differentiableAt
    have h2 : DifferentiableAt ℂ g ((u 0)⁻¹ • tl u) := hg.differentiableAt (hOo.mem_nhds hu.2)
    exact (h0'.smul (h2.comp u h1)).differentiableWithinAt
  have hcoords : ∀ Z : ComplexModel (N + 1),
      (Z i)⁻¹ • tl (coneEquiv L0 i hnN Z).1 = (L0 ((Z i)⁻¹ • numer i Z)).1 := by
    intro Z
    rw [coneEquiv_apply, tl_coneCoords_fst, map_smul]
    rfl
  refine ⟨n + 1, coneEquiv L0 i hnN, ε', U', G, hε', hU', ?_, hGd, fun Z hZ => ?_⟩
  · refine ⟨?_, ?_⟩
    · show (coneEquiv L0 i hnN Z₀).1 0 ≠ 0
      rw [coneEquiv_apply, coneCoords_fst_zero]; exact hZi
    · show ((coneEquiv L0 i hnN Z₀).1 0)⁻¹ • tl (coneEquiv L0 i hnN Z₀).1 ∈ O
      rw [coneEquiv_apply, coneCoords_fst_zero, ← coneEquiv_apply L0 i hnN, hcoords]
      exact (hgraph _ (mem_ball_self hε)).1
  · obtain ⟨hZi', hZb⟩ := hball hZ
    have hZv : WithLp.ofLp Z ≠ 0 := fun h => hZi' (by simpa using congrFun h i)
    rw [mem_affineCone_iff hZi', affineRatio_eq_smul_numer, (hgraph _ hZb).2.1]
    show _ ↔ (coneEquiv L0 i hnN Z).2 = ((coneEquiv L0 i hnN Z).1 0) •
      g (((coneEquiv L0 i hnN Z).1 0)⁻¹ • tl (coneEquiv L0 i hnN Z).1)
    rw [coneEquiv_apply L0 i hnN Z, coneCoords_fst_zero, ← coneEquiv_apply L0 i hnN Z, hcoords,
      coneEquiv_apply, coneCoords_snd, map_smul, Prod.smul_snd]
    exact inv_smul_eq_iff₀ hZi'

end Graph

end SGPT.GAGA.H0S
