import SGPT.Toric.BigToric2Laurent
import SGPT.Toric.BigToricAmple

/-!
# Holomorphic sections of `O(D)` on a smooth projective toric manifold

Source `chapter_toric_big.tex`, proof of `prop:baseloc`:
"`H⁰(X, L) ≅ ⊕_{m ∈ M ∩ P_D} ℂ χ^m`, see `CLS11`, Proposition 4.3.3", and the proof of
`prop:toricusualOko` (sections of `L^k = O(kD)` are combinations of `χ^m`, `m ∈ kP_D ∩ M`).

## The model

`X = PolytopeToricVariety γ hs` with the vertex charts `U_v = U_{σ_v} ≅ ℂ^n` (see
`BigToricDivisor`).  By `eq:DUsigma`, `D|_{U_σ} = Div(χ^{-m_σ})`, so if `s_D` is the rational
section of `L = O_X(D)` with divisor `D`, then `e_v = χ^{m_v} s_D` is a holomorphic frame of
`L` on `U_v` (the frames whose weights are recorded by `BigToricMetric`).  A holomorphic
section `s` of `L` is `s = f_v e_v` on `U_v` with `f_v` holomorphic on `U_v ≅ ℂ^n`; the
rational function `g = s / s_D`, regular on `T(ℂ)`, is `g = f_v χ^{m_v}` on `T(ℂ)` for every
`v`, and determines `s` (`T(ℂ)` is dense).  Conversely a function `g` on `T(ℂ)` such that
`g χ^{-m_v}` extends holomorphically from the torus to the whole chart `U_v` for every `v`
defines a section.  This is the classical identification
`H⁰(X, O(D)) = {g ∈ ℂ(X) : div g + D ≥ 0} ∪ {0}`, with the condition `div g + D ≥ 0` read
on the charts `U_v`, which cover `X`.  We therefore define

* `toricSections D`: the complex vector space `H⁰(X, O(D))`, as the subspace of functions
  `g : T(ℂ) → ℂ` with `g = f_v(z_v) χ^{m_v}` for entire functions `f_v` of the vertex
  coordinates `z_v` of `U_v`;
* `toricLatticePoints D = M ∩ P_D`.

## Main results

* `latticeCharacter_mem_toricSections`: `χ^m ∈ H⁰(X, O(D))` for `m ∈ M ∩ P_D`;
* `toricSections_eq_span`: `H⁰(X, O(D)) = span {χ^m : m ∈ M ∩ P_D}` (Laurent expansion on
  `T(ℂ)` and Cauchy's theorem in the vertex charts);
* `linearIndependent_latticeCharacter`: the characters are linearly independent;
* `finrank_toricSections`: `h⁰(X, O(D)) = #(M ∩ P_D)`;
* `finrank_toricSections_smul`: `h⁰(X, O(kD)) = #(kP_D ∩ M)` for `k ≥ 1`;
* `toricSectionCoeff_unique`: the local coefficients `f_v` of a section are unique.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Pointwise

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Characters -/

theorem latticeCharacter_add (m m' : Fin n → ℤ) (a : Fin n → ℂˣ) :
    latticeCharacter (m + m') a = latticeCharacter m a * latticeCharacter m' a := by
  simp only [latticeCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Pi.add_apply, zpow_add,
    Finset.prod_mul_distrib]

theorem latticeCharacter_zero (a : Fin n → ℂˣ) : latticeCharacter 0 a = 1 := by
  simp [latticeCharacter]

theorem latticeCharacter_zsmul (k : ℤ) (m : Fin n → ℤ) (a : Fin n → ℂˣ) :
    latticeCharacter (k • m) a = latticeCharacter m a ^ k := by
  simp only [latticeCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun j _ => by rw [mul_comm, zpow_mul]

theorem latticeCharacter_sum {ι : Type*} (S : Finset ι) (m : ι → Fin n → ℤ)
    (a : Fin n → ℂˣ) : latticeCharacter (∑ i ∈ S, m i) a = ∏ i ∈ S, latticeCharacter (m i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [latticeCharacter_zero]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, latticeCharacter_add, ih]

theorem intPairing_comm (m u : Fin n → ℤ) : intPairing m u = intPairing u m := by
  unfold intPairing; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable (hs) in
/-- The coordinates of `m` in the edge basis at `v` are the pairings with the rays:
`b(v).repr m j = ⟨m, u_j(v)⟩`. -/
theorem basis_repr_eq_intPairing (v : latticePolytopeVertices γ) (m : Fin n → ℤ) (j : Fin n) :
    (originalPolytopeNativeBasis γ hs v).repr m j =
      intPairing m (polytopeToricRayGenerator γ hs v j) := by
  conv_lhs => rw [← Finset.univ_sum_single m]
  have hs' : (∑ k, (Pi.single k (m k) : Fin n → ℤ)) =
      ∑ k, m k • (Pi.single k (1 : ℤ) : Fin n → ℤ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    ext l
    by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  rw [hs']
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, intPairing, polytopeToricRayGenerator]

variable (hs) in
/-- Every character is a monomial in the vertex coordinates `χ^{b_j(v)}`:
`χ^m = ∏_j (χ^{b_j(v)})^{⟨m, u_j(v)⟩}`. -/
theorem latticeCharacter_eq_prod_basis (v : latticePolytopeVertices γ) (m : Fin n → ℤ)
    (a : Fin n → ℂˣ) :
    latticeCharacter m a = ∏ j, latticeCharacter (originalPolytopeNativeBasis γ hs v j) a ^
      intPairing m (polytopeToricRayGenerator γ hs v j) := by
  conv_lhs => rw [← (originalPolytopeNativeBasis γ hs v).sum_repr m]
  rw [latticeCharacter_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [latticeCharacter_zsmul, basis_repr_eq_intPairing hs v m j]

/-! ### Vertex coordinates of torus points -/

/-- A point of the model `ℂ^n` from its coordinates. -/
def modelPoint (f : Fin n → ℂ) : ComplexModel n := (EuclideanSpace.equiv (Fin n) ℂ).symm f

@[simp] theorem modelPoint_apply (f : Fin n → ℂ) (j : Fin n) : modelPoint f j = f j := rfl

theorem differentiable_modelPoint : Differentiable ℂ (modelPoint (n := n)) :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.differentiable

theorem continuous_modelPoint : Continuous (modelPoint (n := n)) :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous

variable (hs) in
/-- The vertex coordinates of a torus point: `z_v(a) = (χ^{b_j(v)}(a))_j`. -/
theorem vertexChart_embedding (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) =
      modelPoint (fun j => (latticeCharacter (originalPolytopeNativeBasis γ hs v j) a : ℂ)) := by
  ext j
  exact originalPolytopeNativePiChart_orbit γ hs v a j

theorem continuous_latticeCharacter_coe (m : Fin n → ℤ) :
    Continuous fun a : Fin n → ℂˣ => (latticeCharacter m a : ℂ) :=
  Units.continuous_val.comp (continuous_latticeCharacter m)

variable (hs) in
theorem continuous_vertexChart_embedding (v : latticePolytopeVertices γ) :
    Continuous fun a : Fin n → ℂˣ =>
      originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) := by
  simp only [vertexChart_embedding hs v]
  exact continuous_modelPoint.comp (continuous_pi fun j => continuous_latticeCharacter_coe _)

theorem latticeCharacter_mul_torusCocharacter (m u : Fin n → ℤ) (b : Fin n → ℂˣ) (s : ℂˣ) :
    (latticeCharacter m (b * torusCocharacter u s) : ℂ) =
      (latticeCharacter m b : ℂ) * (s : ℂ) ^ intPairing m u := by
  rw [map_mul, latticeCharacter_torusCocharacter, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rfl

variable (hs) in
/-- Along the cocharacter `λ_u`, the vertex coordinates are multiplied by `s^{⟨b_j(v), u⟩}`. -/
theorem vertexChart_embedding_mul_torusCocharacter (v : latticePolytopeVertices γ)
    (u : Fin n → ℤ) (b : Fin n → ℂˣ) (s : ℂˣ) :
    originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs (b * torusCocharacter u s)) =
      modelPoint (fun j => originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs b) j *
        (s : ℂ) ^ intPairing (originalPolytopeNativeBasis γ hs v j) u) := by
  rw [vertexChart_embedding hs v, vertexChart_embedding hs v]
  congr 1
  funext j
  rw [latticeCharacter_mul_torusCocharacter]
  rfl

/-! ### The space of sections -/

variable (D : ToricDivisor γ hs)

/-- Source `prop:baseloc` (proof): the space `H⁰(X, O(D))` of holomorphic sections of
`L = O_X(D)`, realised by the rational functions `g = s / s_D` on `T(ℂ)`: in every vertex chart
`U_v ≅ ℂ^n`, `g = f_v χ^{m_v}` with `f_v` entire (the coefficient of `s` in the frame
`e_v = χ^{m_v} s_D`). -/
def toricSections : Submodule ℂ ((Fin n → ℂˣ) → ℂ) where
  carrier := {g | ∀ v : latticePolytopeVertices γ, ∃ f : ComplexModel n → ℂ,
    Differentiable ℂ f ∧ ∀ a, g a = f (originalPolytopeNativeModelChart γ hs v
      (polytopeToricEmbedding γ hs a)) * latticeCharacter (toricCartierDatum D v) a}
  add_mem' := by
    intro g g' hg hg' v
    obtain ⟨f, hf, hgf⟩ := hg v
    obtain ⟨f', hf', hgf'⟩ := hg' v
    exact ⟨f + f', hf.add hf', fun a => by simp [hgf a, hgf' a, add_mul]⟩
  zero_mem' := fun v => ⟨0, differentiable_const 0, fun a => by simp⟩
  smul_mem' := by
    intro c g hg v
    obtain ⟨f, hf, hgf⟩ := hg v
    exact ⟨c • f, hf.const_smul c, fun a => by simp [hgf a, mul_assoc]⟩

/-- Source `eq:bigPrep`: the lattice points `M ∩ P_D`. -/
def toricLatticePoints : Set (Fin n → ℤ) := {m | latticeVector m ∈ toricDivisorPolytope D}

theorem finite_toricLatticePoints : (toricLatticePoints D).Finite := by
  obtain ⟨R, hR⟩ := (isCompact_toricDivisorPolytope D).isBounded.subset_closedBall 0
  set N : ℤ := ⌈R⌉
  apply (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-N) N)
    fun _ => Set.finite_Icc (-N) N).subset
  intro m hm
  have hb : ∀ k, |(m k : ℝ)| ≤ R := by
    intro k
    have h1 := hR hm
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    calc |(m k : ℝ)| = ‖latticeVector m k‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖latticeVector m‖ := PiLp.norm_apply_le _ k
      _ ≤ R := h1
  intro k _
  refine ⟨?_, ?_⟩
  · have h1 := (abs_le.mp (hb k)).1
    have h2 : (-(N : ℝ)) ≤ m k := by
      have : R ≤ (N : ℝ) := Int.le_ceil R
      linarith
    exact_mod_cast h2
  · have h1 := (abs_le.mp (hb k)).2
    have h2 : (m k : ℝ) ≤ N := h1.trans (Int.le_ceil R)
    exact_mod_cast h2

/-- `m ∈ P_D` iff `⟨m, u_j(v)⟩ ≥ ⟨m_v, u_j(v)⟩` for all rays of all maximal cones. -/
theorem mem_toricLatticePoints_iff (m : Fin n → ℤ) :
    m ∈ toricLatticePoints D ↔ ∀ (v : latticePolytopeVertices γ) (j : Fin n),
      intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v j) ≤
        intPairing m (polytopeToricRayGenerator γ hs v j) := by
  constructor
  · intro hm v j
    have h := hm (polytopeToricRay γ hs v j)
    change -(D (polytopeToricRay γ hs v j) : ℝ) ≤
      latticeFunctional (polytopeToricRayGenerator γ hs v j) (latticeVector m) at h
    rw [latticeFunctional_latticeVector, intPairing_comm] at h
    rw [toricCartierDatum_pairing]
    exact_mod_cast h
  · intro h ρ
    obtain ⟨v, j, hvj⟩ := ρ.property
    have hρ : ρ = polytopeToricRay γ hs v j := Subtype.ext hvj.symm
    subst hρ
    have h1 := h v j
    rw [toricCartierDatum_pairing] at h1
    change -(D (polytopeToricRay γ hs v j) : ℝ) ≤
      latticeFunctional (polytopeToricRayGenerator γ hs v j) (latticeVector m)
    rw [latticeFunctional_latticeVector, intPairing_comm]
    exact_mod_cast h1

/-- The coefficient `∏_j z_j^{⟨m - m_v, u_j(v)⟩}` of the character `χ^m` in the frame `e_v` of
`O(D)` on `U_v` (for `m ∈ P_D` the exponents are nonnegative). -/
def toricMonomial (v : latticePolytopeVertices γ) (m : Fin n → ℤ) (z : ComplexModel n) : ℂ :=
  ∏ j, z j ^ (intPairing m (polytopeToricRayGenerator γ hs v j) -
    intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v j)).toNat

theorem differentiable_toricMonomial (v : latticePolytopeVertices γ) (m : Fin n → ℤ) :
    Differentiable ℂ (toricMonomial D v m) := by
  intro z
  apply AnalyticAt.differentiableAt
  exact Finset.analyticAt_fun_prod _ fun j _ =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).analyticAt z).pow _

/-- For `m ∈ M ∩ P_D`, `χ^m = f_v(z_v) χ^{m_v}` with `f_v = toricMonomial D v m`. -/
theorem latticeCharacter_eq_toricMonomial {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints D)
    (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    (latticeCharacter m a : ℂ) = toricMonomial D v m
      (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
        latticeCharacter (toricCartierDatum D v) a := by
  have hpos := (mem_toricLatticePoints_iff D m).mp hm v
  unfold toricMonomial
  rw [vertexChart_embedding hs v]
  simp only [modelPoint_apply]
  rw [latticeCharacter_eq_prod_basis hs v m, latticeCharacter_eq_prod_basis hs v
    (toricCartierDatum D v)]
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := hpos j
  have hu : (latticeCharacter (originalPolytopeNativeBasis γ hs v j) a : ℂ) ≠ 0 :=
    Units.ne_zero _
  rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ hu]
  congr 1
  ring

/-- Source `prop:baseloc` (proof): for `m ∈ M ∩ P_D`, the character `χ^m` is a section of
`O(D)`; its coefficient in the frame `e_v` is the monomial `∏_j z_j^{⟨m - m_v, u_j(v)⟩}`. -/
theorem latticeCharacter_mem_toricSections {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints D) :
    (fun a => (latticeCharacter m a : ℂ)) ∈ toricSections D := fun v =>
  ⟨toricMonomial D v m, differentiable_toricMonomial D v m,
    latticeCharacter_eq_toricMonomial D hm v⟩

/-! ### The Laurent expansion of a section -/

variable {D}

theorem continuous_of_mem_toricSections {g : (Fin n → ℂˣ) → ℂ} (hg : g ∈ toricSections D) :
    Continuous g := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  obtain ⟨f, hf, hgf⟩ := hg ⟨v, hv⟩
  rw [show g = _ from funext hgf]
  exact (hf.continuous.comp (continuous_vertexChart_embedding hs _)).mul
    (continuous_latticeCharacter_coe _)

/-- The slices of a section along a cocharacter are holomorphic on `ℂ^*`. -/
theorem exists_slice_of_mem_toricSections {g : (Fin n → ℂˣ) → ℂ} (hg : g ∈ toricSections D)
    (u : Fin n → ℤ) (b : Fin n → ℂˣ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {0}ᶜ ∧ ∀ s : ℂˣ, g (b * torusCocharacter u s) = G s := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  obtain ⟨f, hf, hgf⟩ := hg ⟨v, hv⟩
  set ζ := originalPolytopeNativeModelChart γ hs ⟨v, hv⟩ (polytopeToricEmbedding γ hs b)
  set c : Fin n → ℤ := fun j => intPairing (originalPolytopeNativeBasis γ hs ⟨v, hv⟩ j) u
  set q := intPairing (toricCartierDatum D ⟨v, hv⟩) u
  refine ⟨fun s => f (modelPoint fun j => ζ j * s ^ c j) *
    ((latticeCharacter (toricCartierDatum D ⟨v, hv⟩) b : ℂ) * s ^ q), ?_, ?_⟩
  · intro s hs0
    have hs0' : s ≠ 0 := hs0
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · apply (hf _).comp
      apply differentiable_modelPoint.differentiableAt.comp
      apply differentiableAt_pi.mpr
      intro j
      exact (differentiableAt_const _).mul (differentiableAt_zpow.mpr (Or.inl hs0'))
    · exact (differentiableAt_const _).mul (differentiableAt_zpow.mpr (Or.inl hs0'))
  · intro s
    rw [hgf, vertexChart_embedding_mul_torusCocharacter hs, latticeCharacter_mul_torusCocharacter]

/-- The slices of a section along the ray `u_j(v)` are `H(s) s^{⟨m_v, u_j(v)⟩}` with `H`
entire: in the chart `U_v` the cocharacter `λ_{u_j(v)}` only moves the coordinate `z_j`. -/
theorem exists_ray_slice_of_mem_toricSections {g : (Fin n → ℂˣ) → ℂ}
    (hg : g ∈ toricSections D) (v : latticePolytopeVertices γ) (j : Fin n) (b : Fin n → ℂˣ) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ s : ℂˣ,
      g (b * torusCocharacter (polytopeToricRayGenerator γ hs v j) s) =
        H s * (s : ℂ) ^ intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v j) := by
  obtain ⟨f, hf, hgf⟩ := hg v
  set ζ := originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs b)
  refine ⟨fun s => f (modelPoint fun i => ζ i * (if i = j then s else 1)) *
    (latticeCharacter (toricCartierDatum D v) b : ℂ), ?_, ?_⟩
  · apply Differentiable.mul _ (differentiable_const _)
    apply hf.comp
    apply differentiable_modelPoint.comp
    apply differentiable_pi.mpr
    intro i
    apply (differentiable_const _).mul
    split_ifs
    · exact differentiable_id
    · exact differentiable_const _
  · intro s
    rw [hgf, vertexChart_embedding_mul_torusCocharacter hs, latticeCharacter_mul_torusCocharacter]
    have hfun : (fun i => ζ i * (s : ℂ) ^ intPairing (originalPolytopeNativeBasis γ hs v i)
        (polytopeToricRayGenerator γ hs v j)) = fun i => ζ i * (if i = j then (s : ℂ) else 1) := by
      funext i
      rw [intPairing_basis_rayGenerator]
      split_ifs <;> simp
    rw [hfun]
    ring

/-- The Laurent coefficients of a section vanish off `M ∩ P_D`. -/
theorem laurentCoeff_eq_zero_of_mem_toricSections {g : (Fin n → ℂˣ) → ℂ}
    (hg : g ∈ toricSections D) {m : Fin n → ℤ} (hm : m ∉ toricLatticePoints D) :
    UnitAddTorus.mFourierCoeff (fun t => g (compactTorusPoint t)) m = 0 := by
  rw [mem_toricLatticePoints_iff] at hm
  push Not at hm
  obtain ⟨v, j, hvj⟩ := hm
  exact laurentCoeff_eq_zero_of_slice (continuous_of_mem_toricSections hg) hvj
    (exists_ray_slice_of_mem_toricSections hg v j)

/-- Source `prop:baseloc` (proof), `CLS11` Proposition 4.3.3: every section of `O(D)` is a
linear combination of the characters `χ^m`, `m ∈ M ∩ P_D`, namely its Laurent expansion. -/
theorem eq_sum_of_mem_toricSections {g : (Fin n → ℂˣ) → ℂ} (hg : g ∈ toricSections D) (a) :
    g a = ∑ m ∈ (finite_toricLatticePoints D).toFinset,
      UnitAddTorus.mFourierCoeff (fun t => g (compactTorusPoint t)) m *
        (latticeCharacter m a : ℂ) := by
  apply eq_sum_laurentCoeff (continuous_of_mem_toricSections hg)
    (fun k b => exists_slice_of_mem_toricSections hg _ b)
  intro m hm
  rw [Set.Finite.mem_toFinset] at hm
  exact laurentCoeff_eq_zero_of_mem_toricSections hg hm

variable (D)

/-- Source `prop:baseloc` (proof): `H⁰(X, O(D)) = span {χ^m : m ∈ M ∩ P_D}`. -/
theorem toricSections_eq_span :
    toricSections D = Submodule.span ℂ
      (Set.range fun m : toricLatticePoints D => fun a => (latticeCharacter m.val a : ℂ)) := by
  apply le_antisymm
  · intro g hg
    have hg' : g = ∑ m ∈ (finite_toricLatticePoints D).toFinset,
        UnitAddTorus.mFourierCoeff (fun t => g (compactTorusPoint t)) m •
          fun a => (latticeCharacter m a : ℂ) := by
      funext a
      rw [eq_sum_of_mem_toricSections hg a, Finset.sum_apply]
      rfl
    rw [hg']
    apply Submodule.sum_mem
    intro m hm
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Set.Finite.mem_toFinset] at hm
    exact ⟨⟨m, hm⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact latticeCharacter_mem_toricSections D m.property

/-- The characters `χ^m` (`m ∈ M`) are linearly independent functions on `T(ℂ)`
(Dedekind's lemma). -/
theorem linearIndependent_latticeCharacter :
    LinearIndependent ℂ (fun m : Fin n → ℤ => fun a : Fin n → ℂˣ => (latticeCharacter m a : ℂ)) := by
  let χ : (Fin n → ℤ) → ((Fin n → ℂˣ) →* ℂ) := fun m => (Units.coeHom ℂ).comp (latticeCharacter m)
  have hinj : Function.Injective χ := by
    intro m m' h
    funext k
    have hk := DFunLike.congr_fun h (torusCocharacter (Pi.single k 1) (Units.mk0 (2 : ℂ) two_ne_zero))
    simp only [χ, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      latticeCharacter_torusCocharacter, Units.val_zpow_eq_zpow_val, Units.val_mk0] at hk
    have h1 : ∀ m : Fin n → ℤ, ∑ i, m i * (Pi.single k (1 : ℤ) : Fin n → ℤ) i = m k := by
      intro m; simp [Pi.single_apply]
    rw [h1, h1] at hk
    have h2 := congrArg (fun z : ℂ => ‖z‖) hk
    simp only [norm_zpow, Complex.norm_ofNat] at h2
    exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h2
  exact (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp χ hinj

/-- Source `prop:baseloc` (proof): `h⁰(X, O(D)) = #(M ∩ P_D)`. -/
theorem finrank_toricSections :
    Module.finrank ℂ (toricSections D) = (toricLatticePoints D).ncard := by
  have hfin := finite_toricLatticePoints D
  let _ := hfin.fintype
  have h := finrank_span_eq_card
    ((linearIndependent_latticeCharacter).comp (Subtype.val : toricLatticePoints D → Fin n → ℤ)
      Subtype.val_injective)
  simp only [Function.comp_def] at h
  rw [toricSections_eq_span, h, Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- The divisor `kD`. -/
theorem toricCartierDatum_smul (k : ℤ) (v : latticePolytopeVertices γ) :
    toricCartierDatum (k • D) v = k • toricCartierDatum D v := by
  unfold toricCartierDatum
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, smul_smul, mul_neg]

/-- `P_{kD} = k P_D` for `k ≥ 1`. -/
theorem mem_toricDivisorPolytope_smul_iff {k : ℕ} (hk : 0 < k) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ toricDivisorPolytope ((k : ℤ) • D) ↔ x ∈ (k : ℝ) • toricDivisorPolytope D := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hk'.ne']
  simp only [toricDivisorPolytope, Set.mem_ofPred_eq, map_smul, smul_eq_mul, Pi.smul_apply]
  refine forall_congr' fun ρ => ?_
  push_cast
  constructor
  · intro h
    rw [le_inv_mul_iff₀ hk']
    linarith
  · intro h
    rw [le_inv_mul_iff₀ hk'] at h
    linarith

/-- Source `prop:toricusualOko` (proof): `h⁰(X, O(kD)) = #(kP_D ∩ M)` for `k ≥ 1`. -/
theorem finrank_toricSections_smul {k : ℕ} (hk : 0 < k) :
    Module.finrank ℂ (toricSections ((k : ℤ) • D)) =
      {m : Fin n → ℤ | latticeVector m ∈ (k : ℝ) • toricDivisorPolytope D}.ncard := by
  rw [finrank_toricSections]
  congr 1
  ext m
  exact mem_toricDivisorPolytope_smul_iff D hk _

/-! ### Uniqueness of the local coefficients -/

theorem dense_complexTorus : Dense (complexTorus n) := by
  intro z
  let ones : ComplexModel n := modelPoint fun _ => 1
  have htend : Tendsto (fun t : ℝ => z + (t : ℂ) • ones) (𝓝[>] 0) (𝓝 z) := by
    have : Tendsto (fun t : ℝ => z + (t : ℂ) • ones) (𝓝 0) (𝓝 (z + ((0 : ℝ) : ℂ) • ones)) :=
      (continuous_const.add ((Complex.continuous_ofReal).smul continuous_const)).tendsto 0
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto htend
  have hall : ∀ i, ∀ᶠ t : ℝ in 𝓝[>] 0, z i + (t : ℂ) ≠ 0 := by
    intro i
    by_cases hzi : z i = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hzi, zero_add]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    · have hpos : 0 < ‖z i‖ := norm_pos_iff.mpr hzi
      have : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ‖z i‖ := by
        have h := (continuous_abs.tendsto (0 : ℝ))
        simp only [abs_zero] at h
        exact h.eventually (gt_mem_nhds hpos)
      filter_upwards [nhdsWithin_le_nhds this] with t ht
      intro h0
      have : z i = -(t : ℂ) := by linear_combination h0
      have h2 : ‖z i‖ = |t| := by rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      linarith
  filter_upwards [Filter.eventually_all.mpr hall] with t ht
  intro i
  simpa [ones] using ht i

/-- The coefficient `f_v` of a section in the frame `e_v` is uniquely determined by the section
(the coordinate torus is dense in `U_v ≅ ℂ^n`). -/
theorem toricSectionCoeff_unique {g : (Fin n → ℂˣ) → ℂ} (v : latticePolytopeVertices γ)
    {f f' : ComplexModel n → ℂ} (hf : Continuous f) (hf' : Continuous f')
    (hgf : ∀ a, g a = f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
      latticeCharacter (toricCartierDatum D v) a)
    (hgf' : ∀ a, g a = f' (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
      latticeCharacter (toricCartierDatum D v) a) : f = f' := by
  apply hf.ext_on dense_complexTorus hf'
  intro w hw
  obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hw
  have hwt : w ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]; exact mem_univ w
  have hya : originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) = w := by
    rw [ha]; exact (originalPolytopeNativeModelChart γ hs v).right_inv hwt
  have h := (hgf a).symm.trans (hgf' a)
  rw [hya] at h
  exact mul_right_cancel₀ (Units.ne_zero _) h

end SGPT.Toric
