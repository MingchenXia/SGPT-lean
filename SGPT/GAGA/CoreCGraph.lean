import SGPT.GAGA.CoreOkaModules
import SGPT.Foundations.Analysis.Pending.CoordinatePlaneDivision

/-!
# Graphs of holomorphic maps and push-forward of coherent modules

Infrastructure of lane SERRE-CORE3 (Serre's GAGA, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), step M2.6 of the plan in
`blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core3.tex`).
Sources: Oka's embedding of analytic polyhedra into polydiscs and the push-forward of coherent
sheaves under closed embeddings (Gunning--Rossi, *Analytic functions of several complex
variables*, I.D and VII.A; Grauert--Remmert, *Coherent analytic sheaves*, 1.1.4).

Let `D ⊆ ℂᴺ` be open and `g = (g_r)_{r < m}` holomorphic on `D`. The graph map
`Φ(w) = (w, g(w)) ∈ ℂ^{N+m}` (`graphMap`) has the left inverse `π(y) = (y_0, …, y_{N-1})`
(`proj`), and its image `Z = Φ(D)` is the common zero set over `π⁻¹(D)` of the functions
`u_r - g_r(w)` (`graphDef`, `mem_graph_iff`).

* `exists_hadamard`: a function holomorphic near a point of `Z` and vanishing on `Z` is a
  holomorphic combination of the `u_r - g_r(w)` (straightening `(w, u) ↦ (w, u - g(w))` and
  Hadamard's lemma for coordinate planes from `SGPT.Foundations.Analysis`).
* `push D g P`: for a module `P ⊆ 𝒪^κ` on `ℂᴺ`, the module on `ℂ^{N+m}` of tuples whose
  restriction to the graph lies in `P` (equal to `𝒪^κ` off `Z`); `𝒪^κ / push P` is the
  push-forward `Φ_*(𝒪^κ / P)`. If `Z` is closed and `P` is coherent on an open `W`, then `push P`
  is coherent on `π⁻¹(W ∩ D) ∪ Zᶜ` (`push_isCoherentOn`), generated near `Φ(w)` by the
  generators of `P` composed with `π` and the tuples `(u_r - g_r(w)) e_i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf

namespace SGPT.GAGA.Core.Graph

open GermModule

variable {N m : ℕ}

/-! ### The graph map and the straightening -/

/-- The projection `ℂ^{N+m} → ℂᴺ` to the first `N` coordinates. -/
def proj (y : EuclideanSpace ℂ (Fin (N + m))) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun j => y (Fin.castAdd m j)

/-- The graph map `Φ(w) = (w, g(w))`. -/
def graphMap (g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ) (w : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin (N + m)) :=
  WithLp.toLp 2 (Fin.append (fun j => w j) fun r => g r w)

/-- The defining functions `u_r - g_r(w)` of the graph. -/
def graphDef (g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ) (r : Fin m)
    (y : EuclideanSpace ℂ (Fin (N + m))) : ℂ :=
  y (Fin.natAdd N r) - g r (proj y)

/-- The straightening `(w, u) ↦ (w, u - g(w))`. -/
def straighten (g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ) (y : EuclideanSpace ℂ (Fin (N + m))) :
    EuclideanSpace ℂ (Fin (N + m)) :=
  WithLp.toLp 2 (Fin.append (fun j => y (Fin.castAdd m j)) fun r => graphDef g r y)

/-- The inverse of the straightening, `(w, u) ↦ (w, u + g(w))`. -/
def unstraighten (g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ)
    (x : EuclideanSpace ℂ (Fin (N + m))) : EuclideanSpace ℂ (Fin (N + m)) :=
  WithLp.toLp 2
    (Fin.append (fun j => x (Fin.castAdd m j)) fun r => x (Fin.natAdd N r) + g r (proj x))

variable {g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ}

@[simp] theorem proj_apply (y : EuclideanSpace ℂ (Fin (N + m))) (j : Fin N) :
    proj y j = y (Fin.castAdd m j) := rfl

@[simp] theorem graphMap_castAdd (w : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    graphMap g w (Fin.castAdd m j) = w j := by
  simp [graphMap]

@[simp] theorem graphMap_natAdd (w : EuclideanSpace ℂ (Fin N)) (r : Fin m) :
    graphMap g w (Fin.natAdd N r) = g r w := by
  simp [graphMap]

@[simp] theorem proj_graphMap (w : EuclideanSpace ℂ (Fin N)) : proj (graphMap g w) = w := by
  ext j; simp

@[simp] theorem graphDef_graphMap (r : Fin m) (w : EuclideanSpace ℂ (Fin N)) :
    graphDef g r (graphMap g w) = 0 := by
  simp [graphDef]

@[simp] theorem straighten_castAdd (y : EuclideanSpace ℂ (Fin (N + m))) (j : Fin N) :
    straighten g y (Fin.castAdd m j) = y (Fin.castAdd m j) := by
  simp [straighten]

@[simp] theorem straighten_natAdd (y : EuclideanSpace ℂ (Fin (N + m))) (r : Fin m) :
    straighten g y (Fin.natAdd N r) = graphDef g r y := by
  simp [straighten]

@[simp] theorem unstraighten_castAdd (x : EuclideanSpace ℂ (Fin (N + m))) (j : Fin N) :
    unstraighten g x (Fin.castAdd m j) = x (Fin.castAdd m j) := by
  simp [unstraighten]

@[simp] theorem unstraighten_natAdd (x : EuclideanSpace ℂ (Fin (N + m))) (r : Fin m) :
    unstraighten g x (Fin.natAdd N r) = x (Fin.natAdd N r) + g r (proj x) := by
  simp [unstraighten]

@[simp] theorem proj_straighten (y : EuclideanSpace ℂ (Fin (N + m))) :
    proj (straighten g y) = proj y := by
  ext j; simp

@[simp] theorem proj_unstraighten (x : EuclideanSpace ℂ (Fin (N + m))) :
    proj (unstraighten g x) = proj x := by
  ext j; simp

theorem graphDef_unstraighten (r : Fin m) (x : EuclideanSpace ℂ (Fin (N + m))) :
    graphDef g r (unstraighten g x) = x (Fin.natAdd N r) := by
  simp [graphDef]

theorem unstraighten_straighten (y : EuclideanSpace ℂ (Fin (N + m))) :
    unstraighten g (straighten g y) = y := by
  ext i
  induction i using Fin.addCases with
  | left j => simp
  | right r => simp [graphDef]

theorem eq_graphMap_of_graphDef {y : EuclideanSpace ℂ (Fin (N + m))}
    (h : ∀ r, graphDef g r y = 0) : graphMap g (proj y) = y := by
  ext i
  induction i using Fin.addCases with
  | left j => simp
  | right r =>
    have := h r
    simp only [graphDef, sub_eq_zero] at this
    simp [this]

/-- The graph `Φ(D)` is the common zero set over `π⁻¹(D)` of the `u_r - g_r(w)`. -/
theorem mem_graph_iff {D : Set (EuclideanSpace ℂ (Fin N))} {y : EuclideanSpace ℂ (Fin (N + m))} :
    y ∈ graphMap g '' D ↔ proj y ∈ D ∧ ∀ r, graphDef g r y = 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp [hw]
  · rintro ⟨hD, h⟩
    exact ⟨proj y, hD, eq_graphMap_of_graphDef h⟩

/-! ### Differentiability -/

theorem differentiable_proj :
    Differentiable ℂ (proj : EuclideanSpace ℂ (Fin (N + m)) → EuclideanSpace ℂ (Fin N)) := by
  refine differentiable_euclidean.2 fun j => ?_
  simp only [proj_apply]
  exact (EuclideanSpace.proj (Fin.castAdd m j) :
    EuclideanSpace ℂ (Fin (N + m)) →L[ℂ] ℂ).differentiable

theorem continuous_proj :
    Continuous (proj : EuclideanSpace ℂ (Fin (N + m)) → EuclideanSpace ℂ (Fin N)) :=
  differentiable_proj.continuous

theorem differentiableAt_coord (i : Fin (N + m)) (y : EuclideanSpace ℂ (Fin (N + m))) :
    DifferentiableAt ℂ (fun x : EuclideanSpace ℂ (Fin (N + m)) => x i) y :=
  (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin (N + m)) →L[ℂ] ℂ).differentiableAt

theorem differentiableAt_graphMap {w : EuclideanSpace ℂ (Fin N)}
    (hg : ∀ r, DifferentiableAt ℂ (g r) w) : DifferentiableAt ℂ (graphMap g) w := by
  refine differentiableAt_euclidean.2 fun i => ?_
  induction i using Fin.addCases with
  | left j =>
    simp only [graphMap_castAdd]
    exact (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin N) →L[ℂ] ℂ).differentiableAt
  | right r =>
    simp only [graphMap_natAdd]
    exact hg r

theorem differentiableAt_graphDef {y : EuclideanSpace ℂ (Fin (N + m))} (r : Fin m)
    (hg : DifferentiableAt ℂ (g r) (proj y)) : DifferentiableAt ℂ (graphDef g r) y :=
  (differentiableAt_coord _ y).sub (hg.comp y differentiable_proj.differentiableAt)

theorem differentiableAt_straighten {y : EuclideanSpace ℂ (Fin (N + m))}
    (hg : ∀ r, DifferentiableAt ℂ (g r) (proj y)) : DifferentiableAt ℂ (straighten g) y := by
  refine differentiableAt_euclidean.2 fun i => ?_
  induction i using Fin.addCases with
  | left j =>
    simp only [straighten_castAdd]
    exact differentiableAt_coord _ y
  | right r =>
    simp only [straighten_natAdd]
    exact differentiableAt_graphDef r (hg r)

theorem differentiableAt_unstraighten {x : EuclideanSpace ℂ (Fin (N + m))}
    (hg : ∀ r, DifferentiableAt ℂ (g r) (proj x)) : DifferentiableAt ℂ (unstraighten g) x := by
  refine differentiableAt_euclidean.2 fun i => ?_
  induction i using Fin.addCases with
  | left j =>
    simp only [unstraighten_castAdd]
    exact differentiableAt_coord _ x
  | right r =>
    simp only [unstraighten_natAdd]
    exact (differentiableAt_coord _ x).add ((hg r).comp x differentiable_proj.differentiableAt)

/-- Holomorphy at a point is preserved by composition with a map differentiable near it. -/
theorem holAt_comp {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] {f : Y → ℂ} {φ : X → Y} {y : X} (hf : HolAt f (φ y))
    (hφ : ∀ᶠ x in 𝓝 y, DifferentiableAt ℂ φ x) : HolAt (fun x => f (φ x)) y :=
  ((hφ.self_of_nhds.continuousAt.eventually hf).and hφ).mono fun x hx => hx.1.comp x hx.2

variable {D : Set (EuclideanSpace ℂ (Fin N))}

theorem eventually_differentiableAt_g (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D)
    {y : EuclideanSpace ℂ (Fin (N + m))} (hy : proj y ∈ D) :
    ∀ᶠ x in 𝓝 y, ∀ r, DifferentiableAt ℂ (g r) (proj x) :=
  (continuous_proj.continuousAt.eventually (hD.eventually_mem hy)).mono fun _ hx r =>
    (hg r).differentiableAt (hD.mem_nhds hx)

theorem holAt_graphDef (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D)
    {y : EuclideanSpace ℂ (Fin (N + m))} (hy : proj y ∈ D) (r : Fin m) :
    HolAt (graphDef g r) y :=
  (eventually_differentiableAt_g hD hg hy).mono fun _ hx => differentiableAt_graphDef r (hx r)

/-! ### Hadamard division along the graph -/

/-- **Hadamard's lemma for a graph.** A function holomorphic near a point `y` of the graph
(`π y ∈ D`, `u = g(w)` at `y`) that vanishes near `y` on the graph is a holomorphic combination
of the defining functions `u_r - g_r(w)` near `y`. -/
theorem exists_hadamard (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D)
    {y : EuclideanSpace ℂ (Fin (N + m))} (hyD : proj y ∈ D) (hyZ : ∀ r, graphDef g r y = 0)
    {F : EuclideanSpace ℂ (Fin (N + m)) → ℂ} (hF : HolAt F y)
    (hvan : ∀ᶠ z in 𝓝 y, (∀ r, graphDef g r z = 0) → F z = 0) :
    ∃ d : Fin m → EuclideanSpace ℂ (Fin (N + m)) → ℂ, (∀ r, HolAt (d r) y) ∧
      F =ᶠ[𝓝 y] fun z => ∑ r, d r z * graphDef g r z := by
  set q := straighten g y with hqdef
  have hq : q ∈ SGPT.Foundations.Analysis.FirstPass.complexCoordinatePlane (N + m) N := by
    intro i hi
    have hi' : i = Fin.natAdd N ⟨i.1 - N, by omega⟩ := Fin.ext (by simp; omega)
    rw [hi', hqdef, straighten_natAdd, hyZ]
  have hqD : proj q ∈ D := by rw [hqdef, proj_straighten]; exact hyD
  have hus : unstraighten g q = y := unstraighten_straighten y
  have hgq := eventually_differentiableAt_g hD hg hqD
  have hH : HolAt (fun x => F (unstraighten g x)) q := by
    exact holAt_comp (by rw [hus]; exact hF) (hgq.mono fun x hx => differentiableAt_unstraighten hx)
  have hcont : ContinuousAt (unstraighten g) q :=
    (differentiableAt_unstraighten hgq.self_of_nhds).continuousAt
  have hvanH : ∀ᶠ u in 𝓝 q, u ∈ SGPT.Foundations.Analysis.FirstPass.complexCoordinatePlane (N + m) N →
      F (unstraighten g u) = 0 := by
    have hvan' : ∀ᶠ z in 𝓝 (unstraighten g q), (∀ r, graphDef g r z = 0) → F z = 0 := by
      rw [hus]; exact hvan
    have h := hcont.eventually hvan'
    refine h.mono fun u hu hplane => hu fun r => ?_
    rw [graphDef_unstraighten]
    exact hplane _ (by simp)
  obtain ⟨Hc, hHc0, hHcd, hHeq⟩ :=
    SGPT.Foundations.Analysis.Pending.CoordinatePlaneDivision.exists_eq_sum_coord_mul
      (n := N + m) m N (by omega) hq hH hvanH
  have hgy := eventually_differentiableAt_g hD hg hyD
  have hsy : ∀ᶠ z in 𝓝 y, DifferentiableAt ℂ (straighten g) z :=
    hgy.mono fun z hz => differentiableAt_straighten hz
  refine ⟨fun r z => Hc (Fin.natAdd N r) (straighten g z), fun r => holAt_comp ?_ hsy, ?_⟩
  · exact hHcd (Fin.natAdd N r)
  · have h := hsy.self_of_nhds.continuousAt.eventually hHeq
    refine h.mono fun z hz => ?_
    simp only [unstraighten_straighten] at hz
    rw [hz, Fin.sum_univ_add]
    have h0 : ∀ j : Fin N, Hc (Fin.castAdd m j) = 0 := fun j => hHc0 _ (by simp)
    simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
      straighten_natAdd]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/-! ### Push-forward of modules -/

variable {κ μ : Type} [Fintype κ] [Fintype μ]

/-- The module on `ℂ^{N+m}` of tuples whose restriction to the graph `Φ(D)` lies in `P`. Off the
graph it is `𝒪^κ`; at `Φ(w)`, the germ of `a` lies in it iff the germ of `a ∘ Φ` at `w` lies in
`P_w`. -/
def push (D : Set (EuclideanSpace ℂ (Fin N))) (g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ)
    (P : GermModule (EuclideanSpace ℂ (Fin N)) κ) :
    GermModule (EuclideanSpace ℂ (Fin (N + m))) κ :=
  ⟨fun y a => HolTupleAt a y ∧
    (y ∈ graphMap g '' D → P.mem (proj y) (fun j w => a j (graphMap g w)))⟩

theorem push_mem_iff {P : GermModule (EuclideanSpace ℂ (Fin N)) κ}
    {y : EuclideanSpace ℂ (Fin (N + m))} {a : κ → EuclideanSpace ℂ (Fin (N + m)) → ℂ} :
    (push D g P).mem y a ↔ HolTupleAt a y ∧
      (y ∈ graphMap g '' D → P.mem (proj y) (fun j w => a j (graphMap g w))) :=
  Iff.rfl

/-- The generators of `push P` near a point of the graph: the generators `σ_k ∘ π` of `P` and
the tuples `(u_r - g_r(w)) e_i`. -/
def pushGen (g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ)
    (σ : μ → κ → EuclideanSpace ℂ (Fin N) → ℂ) [DecidableEq κ] :
    μ ⊕ (Fin m × κ) → κ → EuclideanSpace ℂ (Fin (N + m)) → ℂ
  | Sum.inl k => fun j y => σ k j (proj y)
  | Sum.inr p => fun j y => if p.2 = j then graphDef g p.1 y else 0

theorem pushGen_inl [DecidableEq κ] (σ : μ → κ → EuclideanSpace ℂ (Fin N) → ℂ) (k : μ) (j : κ)
    (y : EuclideanSpace ℂ (Fin (N + m))) : pushGen g σ (Sum.inl k) j y = σ k j (proj y) := rfl

theorem pushGen_inr [DecidableEq κ] (σ : μ → κ → EuclideanSpace ℂ (Fin N) → ℂ) (p : Fin m × κ)
    (j : κ) (y : EuclideanSpace ℂ (Fin (N + m))) :
    pushGen g σ (Sum.inr p) j y = if p.2 = j then graphDef g p.1 y else 0 := rfl

/-- `push P` is generated near a point of the graph over `U₀` by `pushGen`. -/
theorem push_generatedOn [DecidableEq κ] (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D)
    {P : GermModule (EuclideanSpace ℂ (Fin N)) κ} {U₀ : Set (EuclideanSpace ℂ (Fin N))}
    (hU₀ : IsOpen U₀) (hU₀D : U₀ ⊆ D) {σ : μ → κ → EuclideanSpace ℂ (Fin N) → ℂ}
    (hσ : P.GeneratedOn U₀ σ) : (push D g P).GeneratedOn (proj ⁻¹' U₀) (pushGen g σ) := by
  have hUo : IsOpen (proj ⁻¹' U₀ : Set (EuclideanSpace ℂ (Fin (N + m)))) :=
    hU₀.preimage continuous_proj
  have hτd : ∀ x j, DifferentiableOn ℂ (pushGen g σ x j) (proj ⁻¹' U₀) := by
    intro x j z hz
    rcases x with k | ⟨r, i⟩
    · exact ((hσ.1 k j).differentiableAt (hU₀.mem_nhds hz)).comp z
        differentiable_proj.differentiableAt |>.differentiableWithinAt
    · by_cases hij : i = j
      · have h : pushGen g σ (Sum.inr (r, i)) j = graphDef g r := by
          funext y; simp [pushGen_inr, hij]
        rw [h]
        exact (differentiableAt_graphDef r ((hg r).differentiableAt
          (hD.mem_nhds (hU₀D hz)))).differentiableWithinAt
      · have h : pushGen g σ (Sum.inr (r, i)) j = fun _ => 0 := by
          funext y; simp [pushGen_inr, hij]
        rw [h]
        exact differentiableWithinAt_const _
  refine ⟨hτd, fun y hy a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · -- a member of `push P` is a combination of the generators
    obtain ⟨hah, haP⟩ := ha
    by_cases hyZ : ∀ r, graphDef g r y = 0
    · have hyG : y ∈ graphMap g '' D := mem_graph_iff.2 ⟨hU₀D hy, hyZ⟩
      obtain ⟨c, hc, hca⟩ := (hσ.2 (proj y) hy _).1 (haP hyG)
      -- `F_j = a_j - ∑ (c_k ∘ π)(σ_k ∘ π)` vanishes on the graph near `y`
      have hcπ : ∀ k, HolAt (fun z => c k (proj z)) y := fun k =>
        holAt_comp (hc k) (Eventually.of_forall fun z => differentiable_proj z)
      have hσπ : ∀ k j, HolAt (fun z => σ k j (proj z)) y := fun k j =>
        holAt_comp (hσ.holAt hU₀ hy k j) (Eventually.of_forall fun z => differentiable_proj z)
      have hdiv : ∀ j, ∃ d : Fin m → EuclideanSpace ℂ (Fin (N + m)) → ℂ, (∀ r, HolAt (d r) y) ∧
          (fun z => a j z - ∑ k, c k (proj z) * σ k j (proj z)) =ᶠ[𝓝 y]
            fun z => ∑ r, d r z * graphDef g r z := by
        intro j
        refine exists_hadamard hD hg (hU₀D hy) hyZ ((hah j).sub
          (HolAt.fintype_sum fun k => (hcπ k).mul (hσπ k j))) ?_
        have h := continuous_proj.continuousAt.eventually (hca j)
        refine h.mono fun z hz hzZ => ?_
        have hzg := eq_graphMap_of_graphDef hzZ
        simp only [hzg] at hz
        show a j z - ∑ k, c k (proj z) * σ k j (proj z) = 0
        rw [hz, sub_self]
      choose d hd hdeq using hdiv
      refine ⟨Sum.elim (fun k z => c k (proj z)) (fun p z => d p.2 p.1 z), fun x => ?_, fun j => ?_⟩
      · rcases x with k | p
        · exact hcπ k
        · exact hd p.2 p.1
      · filter_upwards [hdeq j] with z hz
        have hz' : a j z - ∑ k, c k (proj z) * σ k j (proj z) =
            ∑ r, d j r z * graphDef g r z := hz
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, pushGen_inl, pushGen_inr, mul_ite, mul_zero,
          Fintype.sum_prod_type, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← hz']
        ring
    · -- off the graph some `u_r - g_r(w)` is invertible
      simp only [not_forall] at hyZ
      obtain ⟨r, hr⟩ := hyZ
      have hGr := holAt_graphDef hD hg (hU₀D hy) r
      have hne : ∀ᶠ z in 𝓝 y, graphDef g r z ≠ 0 := hGr.continuousAt.eventually_ne hr
      have hdivh : ∀ i, HolAt (fun z => a i z / graphDef g r z) y := fun i => by
        simpa [div_eq_mul_inv] using (hah i).mul (hGr.inv hr)
      have hcomb : IsCombinationAt (pushGen g σ) y (fun j z =>
          ∑ i, a i z / graphDef g r z * pushGen g σ (Sum.inr (r, i)) j z) := by
        classical
        exact IsCombinationAt.finset_sum Finset.univ fun i _ =>
          IsCombinationAt.smul (hdivh i) (isCombinationAt_gen _ y (Sum.inr (r, i)))
      refine IsCombinationAt.congr hcomb fun j => ?_
      filter_upwards [hne] with z hz
      simp only [pushGen_inr, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact div_mul_cancel₀ _ hz
  · -- combinations of the generators are members of `push P`
    have hτh : ∀ x j, HolAt (pushGen g σ x j) y := fun x j =>
      holAt_of_differentiableOn hUo (hτd x j) hy
    refine ⟨IsCombinationAt.holTupleAt hτh ha, fun hyG => ?_⟩
    obtain ⟨w, hwD, rfl⟩ := hyG
    have hy' : w ∈ U₀ := by simpa using hy
    rw [proj_graphMap]
    obtain ⟨c, hc, hca⟩ := ha
    have hgw : ∀ᶠ w' in 𝓝 w, DifferentiableAt ℂ (graphMap g) w' :=
      (hD.eventually_mem hwD).mono fun w' hw' =>
        differentiableAt_graphMap fun r => (hg r).differentiableAt (hD.mem_nhds hw')
    refine (hσ.2 w hy' _).2 ⟨fun k w' => c (Sum.inl k) (graphMap g w'), fun k =>
      holAt_comp (hc _) hgw, fun j => ?_⟩
    have h := hgw.self_of_nhds.continuousAt.eventually (hca j)
    refine h.mono fun w' hw' => ?_
    have hw'' : a j (graphMap g w') =
        ∑ x, c x (graphMap g w') * pushGen g σ x j (graphMap g w') := hw'
    show a j (graphMap g w') = ∑ k, c (Sum.inl k) (graphMap g w') * σ k j w'
    rw [hw'', Fintype.sum_sum_type]
    simp [pushGen_inl, pushGen_inr]

/-- **Coherence of the push-forward.** If the graph `Φ(D)` is closed and `P` is coherent on an
open set `W`, then `push P` is coherent on `π⁻¹(W ∩ D) ∪ Φ(D)ᶜ`. -/
theorem push_isCoherentOn (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D)
    (hcl : IsClosed (graphMap g '' D)) {P : GermModule (EuclideanSpace ℂ (Fin N)) κ}
    {W : Set (EuclideanSpace ℂ (Fin N))} (hW : IsOpen W) (hP : P.IsCoherentOn W) :
    (push D g P).IsCoherentOn (proj ⁻¹' (W ∩ D) ∪ (graphMap g '' D)ᶜ) := by
  classical
  intro y₀ hy₀
  by_cases hZ : y₀ ∈ graphMap g '' D
  · have hy₀' : proj y₀ ∈ W ∩ D := by
      rcases hy₀ with h | h
      · exact h
      · exact absurd hZ h
    obtain ⟨U, hU, hxU, μ', _, σ, hσ⟩ := hP (proj y₀) hy₀'.1
    refine ⟨proj ⁻¹' (U ∩ W ∩ D), ((hU.inter hW).inter hD).preimage continuous_proj,
      ⟨⟨hxU, hy₀'.1⟩, hy₀'.2⟩, μ' ⊕ (Fin m × κ), inferInstance, pushGen g σ, ?_⟩
    exact push_generatedOn hD hg ((hU.inter hW).inter hD) inter_subset_right
      (hσ.mono fun z hz => hz.1.1)
  · refine ⟨(graphMap g '' D)ᶜ, hcl.isOpen_compl, hZ, κ, inferInstance, _,
      (top_generatedOn _).congr fun y hy a => ?_⟩
    exact ⟨fun ha => ⟨ha, fun h => absurd h hy⟩, fun ha => ha.1⟩

end SGPT.GAGA.Core.Graph
