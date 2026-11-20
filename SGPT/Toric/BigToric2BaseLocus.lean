import SGPT.Toric.BigToric2Orbits

/-!
# Base loci of torus-invariant divisors

Source `chapter_toric_big.tex`, section `sec:toricsetup2`: `prop:baseloc` (the base locus
`Bs(D)` is the union of the orbit closures `V(τ)` over the cones `τ` such that every
`m ∈ M ∩ P_D` has `a_ρ + ⟨m, u_ρ⟩ > 0` for some `ρ ∈ τ(1)`) and `cor:stablebl_toric` (the
stable base locus is the union of the `V(τ)` with `Q_τ = ∅`, i.e. the same condition for every
real `m ∈ P_D`).

## Definitions

* `toricBaseLocus D`: the common zeros of all sections of `O(D)`: `p` lies in `Bs(D)` iff for
  every section `s` and every vertex chart `U_v ∋ p`, the coefficient `f_v` of `s` in the frame
  `e_v` vanishes at `p`;
* `toricStableBaseLocus D = ⋂_{k ≥ 1} Bs(kD)`.

## Main results

* `toricBaseLocus_eq`: source `prop:baseloc`;
* `mem_toricBaseLocus_iff_exists`: a point lies in `Bs(D)` iff every section vanishes at it in
  *some* vertex chart (the definition does not depend on the frames);
* `isClosed_toricBaseLocus`, `polytopeToricAction_mem_toricBaseLocus_iff`: `Bs(D)` is closed and
  `T(ℂ)`-invariant;
* `exists_rat_of_extremePoint`: an extreme point of a face of `P_D` is rational;
* `toricStableBaseLocus_eq`: source `cor:stablebl_toric`, and `toricStableBaseLocus_eq_faces`:
  the same with the condition `Q_τ = ∅`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators Pointwise

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

variable (D : ToricDivisor γ hs)

/-- Source `prop:baseloc`: the base locus `Bs(D)` of `D`, the common zero set of the sections of
`O(D)`.  The value of the section `s = g s_D` at `p ∈ U_v` in the frame `e_v` is `f_v(z_v(p))`,
where `g = f_v χ^{m_v}` on `T(ℂ)`. -/
def toricBaseLocus : Set (PolytopeToricVariety γ hs) :=
  {p | ∀ g ∈ toricSections D, ∀ (v : latticePolytopeVertices γ) (f : ComplexModel n → ℂ),
    Differentiable ℂ f →
    (∀ a, g a = f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
      latticeCharacter (toricCartierDatum D v) a) →
    p ∈ (originalPolytopeNativeModelChart γ hs v).source →
    f (originalPolytopeNativeModelChart γ hs v p) = 0}

/-- Source `cor:stablebl_toric`: the stable base locus `B(D) = ⋂_{k ≥ 1} Bs(kD)`. -/
def toricStableBaseLocus : Set (PolytopeToricVariety γ hs) :=
  ⋂ (k : ℕ) (_ : 0 < k), toricBaseLocus ((k : ℤ) • D)

/-! ### The monomials -/

theorem toricMonomial_eq_zero_iff (v : latticePolytopeVertices γ) (m : Fin n → ℤ)
    (z : ComplexModel n) :
    toricMonomial D v m z = 0 ↔ ∃ j, z j = 0 ∧
      0 < D (polytopeToricRay γ hs v j) + intPairing m (polytopeToricRayGenerator γ hs v j) := by
  unfold toricMonomial
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, pow_eq_zero_iff', toricCartierDatum_pairing]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  constructor
  · intro h; omega
  · intro h; omega

/-- Points `p` of `X` at which a section vanishes: the characterization through the orbit cone
`τ_p`.  `p ∈ Bs(D)` iff every `m ∈ M ∩ P_D` has `a_ρ + ⟨m, u_ρ⟩ > 0` for some `ρ ∈ τ_p(1)`. -/
theorem mem_toricBaseLocus_iff_orbitRays (p : PolytopeToricVariety γ hs) :
    p ∈ toricBaseLocus D ↔ ∀ m ∈ toricLatticePoints D, ∃ ρ ∈ orbitRays p,
      0 < D ρ + intPairing m ρ.val := by
  constructor
  · intro hp m hm
    obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs p
    have h0 := hp _ (latticeCharacter_mem_toricSections D hm) v _
      (differentiable_toricMonomial D v m) (latticeCharacter_eq_toricMonomial D hm v) hv
    obtain ⟨j, hzj, hpos⟩ := (toricMonomial_eq_zero_iff D v m _).mp h0
    exact ⟨polytopeToricRay γ hs v j, ⟨v, j, rfl, hv, hzj⟩, hpos⟩
  · intro h g hg v f hf hgf hv
    -- the Laurent expansion of `g` and the uniqueness of the coefficient `f_v`
    set S := (finite_toricLatticePoints D).toFinset
    have hF : f = fun z => ∑ m ∈ S,
        UnitAddTorus.mFourierCoeff (fun t => g (compactTorusPoint t)) m * toricMonomial D v m z := by
      apply toricSectionCoeff_unique (D := D) v hf.continuous
        (continuous_finsetSum _ fun m _ => continuous_const.mul
          (differentiable_toricMonomial D v m).continuous) hgf
      intro a
      rw [eq_sum_of_mem_toricSections hg a]
      simp only [Finset.sum_mul, Pi.mul_apply]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Set.Finite.mem_toFinset] at hm
      rw [latticeCharacter_eq_toricMonomial D hm v a]
      ring
    rw [hF]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Set.Finite.mem_toFinset] at hm
    obtain ⟨ρ, hρp, hρ⟩ := h m hm
    obtain ⟨i, hi, hzi⟩ := (mem_toricPrimeDivisor_iff hv ρ).mp hρp
    have hρi : ρ = polytopeToricRay γ hs v i := Subtype.ext hi.symm
    subst hρi
    rw [(toricMonomial_eq_zero_iff D v m _).mpr ⟨i, hzi, hρ⟩, mul_zero]

/-- Source `prop:baseloc`: the base locus `Bs(D)` is the union of the toric subvarieties `V(τ)`,
`τ ∈ Σ`, such that every `m ∈ M ∩ P_D` satisfies `a_ρ + ⟨m, u_ρ⟩ > 0` for some `ρ ∈ τ(1)`
(`eq:arhononcrit`). -/
theorem toricBaseLocus_eq :
    toricBaseLocus D = ⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
      (_ : ∀ m ∈ toricLatticePoints D, ∃ ρ ∈ R, 0 < D ρ + intPairing m ρ.val),
      toricOrbitClosure R := by
  ext p
  simp only [mem_iUnion, exists_prop]
  rw [mem_toricBaseLocus_iff_orbitRays]
  constructor
  · intro h
    exact ⟨orbitRays p, isToricFanCone_orbitRays p, h, mem_toricOrbitClosure_orbitRays p⟩
  · rintro ⟨R, _, hR, hp⟩ m hm
    obtain ⟨ρ, hρ, hpos⟩ := hR m hm
    exact ⟨ρ, mem_toricOrbitClosure_iff.mp hp hρ, hpos⟩

/-- The base locus does not depend on the frames: `p ∈ Bs(D)` iff every section vanishes at `p`
in some vertex chart containing `p`. -/
theorem mem_toricBaseLocus_iff_exists (p : PolytopeToricVariety γ hs) :
    p ∈ toricBaseLocus D ↔ ∀ g ∈ toricSections D, ∃ (v : latticePolytopeVertices γ)
      (f : ComplexModel n → ℂ), Differentiable ℂ f ∧
      (∀ a, g a = f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
        latticeCharacter (toricCartierDatum D v) a) ∧
      p ∈ (originalPolytopeNativeModelChart γ hs v).source ∧
      f (originalPolytopeNativeModelChart γ hs v p) = 0 := by
  constructor
  · intro hp g hg
    obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs p
    obtain ⟨f, hf, hgf⟩ := hg v
    exact ⟨v, f, hf, hgf, hv, hp g hg v f hf hgf hv⟩
  · intro h
    rw [mem_toricBaseLocus_iff_orbitRays]
    intro m hm
    obtain ⟨v, f, hf, hgf, hv, h0⟩ := h _ (latticeCharacter_mem_toricSections D hm)
    have hfe : f = toricMonomial D v m :=
      toricSectionCoeff_unique (D := D) v hf.continuous
        (differentiable_toricMonomial D v m).continuous hgf
        (latticeCharacter_eq_toricMonomial D hm v)
    rw [hfe] at h0
    obtain ⟨j, hzj, hpos⟩ := (toricMonomial_eq_zero_iff D v m _).mp h0
    exact ⟨polytopeToricRay γ hs v j, ⟨v, j, rfl, hv, hzj⟩, hpos⟩

/-- Source `prop:baseloc`: `Bs(D)` is a closed `T(ℂ)`-invariant subset (a finite union of the
closed, invariant analytic subsets `V(τ)`). -/
theorem isClosed_toricBaseLocus : IsClosed (toricBaseLocus D) := by
  rw [toricBaseLocus_eq]
  have hfin : (Set.univ : Set (Set (PolytopeToricRays γ hs))).Finite := by
    have := (finite_polytopeToricRays γ hs).to_subtype
    exact Set.toFinite _
  have : (⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
      (_ : ∀ m ∈ toricLatticePoints D, ∃ ρ ∈ R, 0 < D ρ + intPairing m ρ.val),
      toricOrbitClosure R) = ⋃ R ∈ {R : Set (PolytopeToricRays γ hs) | IsToricFanCone R ∧
        ∀ m ∈ toricLatticePoints D, ∃ ρ ∈ R, 0 < D ρ + intPairing m ρ.val},
          toricOrbitClosure R := by
    ext p; simp only [mem_iUnion, mem_ofPred_eq, exists_prop, and_assoc]
  rw [this]
  exact (hfin.subset (subset_univ _)).isClosed_biUnion fun R _ => isClosed_toricOrbitClosure R

theorem polytopeToricAction_mem_toricBaseLocus_iff (a : Fin n → ℂˣ)
    (p : PolytopeToricVariety γ hs) :
    polytopeToricAction γ hs a p ∈ toricBaseLocus D ↔ p ∈ toricBaseLocus D := by
  rw [toricBaseLocus_eq]
  simp only [mem_iUnion, exists_prop, polytopeToricAction_mem_toricOrbitClosure_iff]

/-- In the chart `U_v`, the base locus is cut out by the coefficients of the sections
`χ^m`, `m ∈ M ∩ P_D` (the base ideal): `Bs(D) ∩ U_v = {z : ∏_j z_j^{⟨m - m_v, u_j(v)⟩} = 0 ∀ m}`. -/
theorem mem_toricBaseLocus_iff_toricMonomial {v : latticePolytopeVertices γ}
    {p : PolytopeToricVariety γ hs} (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    p ∈ toricBaseLocus D ↔ ∀ m ∈ toricLatticePoints D,
      toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p) = 0 := by
  constructor
  · intro hp m hm
    exact hp _ (latticeCharacter_mem_toricSections D hm) v _
      (differentiable_toricMonomial D v m) (latticeCharacter_eq_toricMonomial D hm v) hv
  · intro h
    rw [mem_toricBaseLocus_iff_orbitRays]
    intro m hm
    obtain ⟨j, hzj, hpos⟩ := (toricMonomial_eq_zero_iff D v m _).mp (h m hm)
    exact ⟨polytopeToricRay γ hs v j, ⟨v, j, rfl, hv, hzj⟩, hpos⟩

/-- Source `prop:baseloc`: `Bs(D)` is an analytic subset of `X` (with its reduced structure): in
every chart it is the common zero set of the holomorphic coefficients of the sections. -/
theorem hasAnalyticChartEquations_toricBaseLocus :
    (ofFixedModel n (PolytopeToricVariety γ hs)).HasAnalyticChartEquations (toricBaseLocus D) := by
  classical
  intro e z _
  obtain ⟨v, hve⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
  subst hve
  set S := (finite_toricLatticePoints D).toFinset
  have hsrc : ∀ y : ComplexModel n, (originalPolytopeNativeModelChart γ hs v).symm y ∈
      (originalPolytopeNativeModelChart γ hs v).source := fun y =>
    (originalPolytopeNativeModelChart γ hs v).map_target
      (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ y)
  have hright : ∀ y : ComplexModel n, originalPolytopeNativeModelChart γ hs v
      ((originalPolytopeNativeModelChart γ hs v).symm y) = y := fun y =>
    (originalPolytopeNativeModelChart γ hs v).right_inv
      (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ y)
  refine ⟨univ, isOpen_univ, mem_univ z, (polytopeToric_chart_target γ hs _).symm.subset,
    S.card, fun i => toricMonomial D v (S.equivFin.symm i).val,
    fun i => (differentiable_toricMonomial D v _).differentiableOn, ?_⟩
  intro y _
  refine Iff.trans (mem_toricBaseLocus_iff_toricMonomial D
    (p := (originalPolytopeNativeModelChart γ hs v).symm y) (hsrc y)) ?_
  have hy := hright y
  rw [hy]
  constructor
  · intro h i
    have hm := (S.equivFin.symm i).property
    rw [Set.Finite.mem_toFinset] at hm
    exact h _ hm
  · intro h m hm
    have hmS : m ∈ S := (Set.Finite.mem_toFinset _).mpr hm
    have := h (S.equivFin ⟨m, hmS⟩)
    dsimp only at this
    rw [Equiv.symm_apply_apply] at this
    exact this

/-! ### Rational points of faces of `P_D` -/

/-- If the real point `x` is the unique solution of the integral linear equations
`⟨u_i, ·⟩ = c_i` (no nonzero direction is orthogonal to all `u_i`), then `x` is rational. -/
theorem exists_rat_of_unique_solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → Fin n → ℤ) (c : ι → ℤ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, latticeFunctional (u i) x = c i)
    (hinj : ∀ d : EuclideanSpace ℝ (Fin n), (∀ i, latticeFunctional (u i) d = 0) → d = 0) :
    ∃ q : Fin n → ℚ, ∀ k, x k = q k := by
  classical
  let U : Matrix ι (Fin n) ℚ := Matrix.of fun i k => (u i k : ℚ)
  let L : (Fin n → ℚ) →ₗ[ℚ] (ι → ℚ) := Matrix.toLin' U
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    let d : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm fun k => (q k : ℝ)
    have hdk : ∀ k, d k = (q k : ℝ) := fun k => rfl
    have hd : d = 0 := by
      apply hinj d
      intro i
      have hqi := congrFun hq i
      simp only [L, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, U, Matrix.of_apply,
        Pi.zero_apply] at hqi
      rw [latticeFunctional_apply]
      have : (∑ k, (u i k : ℝ) * d k) = ((∑ k, (u i k : ℚ) * q k : ℚ) : ℝ) := by
        push_cast; simp only [hdk]
      rw [this, hqi, Rat.cast_zero]
    funext k
    have := congrArg (fun y : EuclideanSpace ℝ (Fin n) => y k) hd
    simp only [hdk, PiLp.zero_apply] at this
    simp only [Pi.zero_apply]
    exact_mod_cast this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L
    (LinearMap.ker_eq_bot.mpr hLinj)
  let V : Matrix (Fin n) ι ℚ := LinearMap.toMatrix' g
  have hVU : V * U = 1 := by
    have h1 : LinearMap.toMatrix' (g.comp L) = V * U := by
      rw [LinearMap.toMatrix'_comp]
      simp only [V, L, LinearMap.toMatrix'_toLin']
    rw [← h1, hg, LinearMap.toMatrix'_id]
  refine ⟨V.mulVec fun i => (c i : ℚ), fun k => ?_⟩
  have hVUr : (V.map (Rat.castHom ℝ)) * (U.map (Rat.castHom ℝ)) = 1 := by
    rw [← Matrix.map_mul, hVU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hUx : (U.map (Rat.castHom ℝ)).mulVec (fun k => x k) = fun i => ((c i : ℚ) : ℝ) := by
    funext i
    have := hx i
    rw [latticeFunctional_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, U, Matrix.of_apply, Rat.coe_castHom,
      Rat.cast_intCast]
    rw [this]
  have hxV : (fun k => x k) = (V.map (Rat.castHom ℝ)).mulVec (fun i => ((c i : ℚ) : ℝ)) := by
    rw [← hUx, Matrix.mulVec_mulVec, hVUr, Matrix.one_mulVec]
  have := congrFun hxV k
  rw [this]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.coe_castHom]
  push_cast
  rfl

/-- A rational point is `m / k` for a lattice point `m` and an integer `k ≥ 1`. -/
theorem exists_nat_int_of_rat (q : Fin n → ℚ) :
    ∃ (k : ℕ) (m : Fin n → ℤ), 0 < k ∧ ∀ i, (m i : ℝ) = k * (q i : ℝ) := by
  classical
  set k : ℕ := ∏ i, (q i).den
  have hk : 0 < k := Finset.prod_pos fun i _ => (q i).den_pos
  refine ⟨k, fun i => (q i).num * ((k / (q i).den : ℕ) : ℤ), hk, fun i => ?_⟩
  have hdvd : (q i).den ∣ k := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_pos.ne'
  have hq : ((q i).num * ((k / (q i).den : ℕ) : ℤ) : ℚ) = (k : ℚ) * q i := by
    rw [Int.cast_natCast, Nat.cast_div hdvd hden]
    conv_rhs => rw [← Rat.num_div_den (q i)]
    field_simp
  have := congrArg (fun r : ℚ => (r : ℝ)) hq
  push_cast at this
  exact_mod_cast this

/-- Source `cor:stablebl_toric` (proof): the face
`Q = {m ∈ P_D : a_ρ + ⟨m, u_ρ⟩ = 0 ∀ ρ ∈ R}` of `P_D`, if nonempty, contains a rational point
(an extreme point, which is the unique solution of its active integral equations). -/
theorem exists_rat_mem_face (R : Set (PolytopeToricRays γ hs))
    (hQ : ∃ x ∈ toricDivisorPolytope D, ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0) :
    ∃ (k : ℕ) (m : Fin n → ℤ), 0 < k ∧ latticeVector m ∈ (k : ℝ) • toricDivisorPolytope D ∧
      ∀ ρ ∈ R, (k : ℤ) * D ρ + intPairing m ρ.val = 0 := by
  classical
  have hfin := finite_polytopeToricRays γ hs
  let _ := hfin.fintype
  set Q := {x ∈ toricDivisorPolytope D | ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0}
  have hQc : IsCompact Q := by
    apply (isCompact_toricDivisorPolytope D).of_isClosed_subset _ (fun x hx => hx.1)
    apply (isClosed_toricDivisorPolytope D).inter
    have : {x : EuclideanSpace ℝ (Fin n) | ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0} =
        ⋂ ρ ∈ R, {x | (D ρ : ℝ) + latticeFunctional ρ.val x = 0} := by ext; simp
    change IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0}
    rw [this]
    apply isClosed_biInter
    intro ρ _
    exact isClosed_eq (continuous_const.add (LinearMap.continuous_of_finiteDimensional _))
      continuous_const
  have hQconv : Convex ℝ Q := by
    apply (convex_toricDivisorPolytope D).inter
    have : {x : EuclideanSpace ℝ (Fin n) | ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0} =
        ⋂ ρ ∈ R, {x | (D ρ : ℝ) + latticeFunctional ρ.val x = 0} := by ext; simp
    change Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0}
    rw [this]
    apply convex_iInter₂
    intro ρ _
    have : {x : EuclideanSpace ℝ (Fin n) | (D ρ : ℝ) + latticeFunctional ρ.val x = 0} =
        {x | latticeFunctional ρ.val x = -(D ρ : ℝ)} := by
      ext x; simp only [mem_ofPred_eq]; constructor <;> intro h <;> linarith
    rw [this]
    exact convex_hyperplane (latticeFunctional ρ.val).isLinear _
  obtain ⟨x, hxQ, _⟩ := hQ
  obtain ⟨x, hxe⟩ := hQc.extremePoints_nonempty ⟨x, hxQ, by assumption⟩
  have hxQ' : x ∈ Q := hxe.1
  -- the active rays at `x`
  let A : Set (PolytopeToricRays γ hs) := {ρ | (D ρ : ℝ) + latticeFunctional ρ.val x = 0}
  have hinj : ∀ d : EuclideanSpace ℝ (Fin n),
      (∀ ρ : A, latticeFunctional ρ.val.val d = 0) → d = 0 := by
    intro d hd
    by_contra hd0
    have hev : ∀ ρ : PolytopeToricRays γ hs, ∀ᶠ t : ℝ in 𝓝 0,
        -(D ρ : ℝ) ≤ latticeFunctional ρ.val (x + t • d) ∧
          (ρ ∈ A → (D ρ : ℝ) + latticeFunctional ρ.val (x + t • d) = 0) := by
      intro ρ
      by_cases hρ : ρ ∈ A
      · refine Eventually.of_forall fun t => ?_
        have h0 := hd ⟨ρ, hρ⟩
        simp only [map_add, map_smul, smul_eq_mul] at h0 ⊢
        rw [h0, mul_zero, add_zero]
        have : (D ρ : ℝ) + latticeFunctional ρ.val x = 0 := hρ
        exact ⟨by linarith, fun _ => this⟩
      · have hgap : -(D ρ : ℝ) < latticeFunctional ρ.val x := by
          have h1 := hxQ'.1 ρ
          have h2 : (D ρ : ℝ) + latticeFunctional ρ.val x ≠ 0 := hρ
          change -(D ρ : ℝ) ≤ latticeFunctional ρ.val x at h1
          rcases h1.lt_or_eq with h | h
          · exact h
          · exact absurd (by linarith) h2
        have hcont : Continuous fun t : ℝ => latticeFunctional ρ.val (x + t • d) :=
          (LinearMap.continuous_of_finiteDimensional _).comp
            (continuous_const.add (continuous_id.smul continuous_const))
        have := hcont.tendsto 0
        simp only [zero_smul, add_zero] at this
        filter_upwards [this.eventually (lt_mem_nhds hgap)] with t ht
        exact ⟨ht.le, fun h => absurd h hρ⟩
    have hall : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ Q := by
      filter_upwards [Filter.eventually_all.mpr hev] with t ht
      refine ⟨fun ρ => (ht ρ).1, fun ρ hρR => (ht ρ).2 (hxQ'.2 ρ hρR)⟩
    have hall' : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ Q ∧ x + (-t) • d ∈ Q := by
      have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg.tendsto (0 : ℝ))
      exact hall.and (hneg.eventually hall)
    obtain ⟨t, ht, htpos⟩ := ((hall'.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi 0)).exists
    have hseg : x ∈ openSegment ℝ (x + t • d) (x + (-t) • d) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [smul_add, smul_smul, neg_smul]
      module
    have := hxe.2 ht.1 ht.2 hseg
    have htd : t • d = 0 := by
      have h' : x + t • d - x = 0 := by rw [this, sub_self]
      simpa using h'
    rcases smul_eq_zero.mp htd with h | h
    · exact absurd h (ne_of_gt htpos)
    · exact hd0 h
  obtain ⟨q, hq⟩ := exists_rat_of_unique_solution (fun ρ : A => ρ.val.val)
    (fun ρ : A => -D ρ.val) (x := x) (fun ρ => by
      have : (D ρ.val : ℝ) + latticeFunctional ρ.val.val x = 0 := ρ.property
      push_cast; linarith) hinj
  obtain ⟨k, m, hk, hm⟩ := exists_nat_int_of_rat q
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmx : latticeVector m = (k : ℝ) • x := by
    ext i
    rw [latticeVector_apply, hm i, PiLp.smul_apply, smul_eq_mul, hq i]
  refine ⟨k, m, hk, ?_, ?_⟩
  · rw [hmx]
    exact Set.smul_mem_smul_set hxQ'.1
  · intro ρ hρ
    have h1 := hxQ'.2 ρ hρ
    have h2 : (intPairing m ρ.val : ℝ) = (k : ℝ) * latticeFunctional ρ.val x := by
      rw [intPairing_comm, ← latticeFunctional_latticeVector, hmx, map_smul, smul_eq_mul]
    have h3 : ((k : ℤ) * D ρ + intPairing m ρ.val : ℝ) = 0 := by
      push_cast
      rw [h2]
      have : (k : ℝ) * ((D ρ : ℝ) + latticeFunctional ρ.val x) = 0 := by rw [h1, mul_zero]
      linarith
    exact_mod_cast h3

/-! ### The stable base locus -/

/-- `p ∈ B(D)` iff every `m ∈ P_D` has `a_ρ + ⟨m, u_ρ⟩ > 0` for some `ρ ∈ τ_p(1)`. -/
theorem mem_toricStableBaseLocus_iff_orbitRays (p : PolytopeToricVariety γ hs) :
    p ∈ toricStableBaseLocus D ↔ ∀ x ∈ toricDivisorPolytope D, ∃ ρ ∈ orbitRays p,
      0 < (D ρ : ℝ) + latticeFunctional ρ.val x := by
  simp only [toricStableBaseLocus, mem_iInter]
  constructor
  · intro h x hx
    by_contra hcon
    push Not at hcon
    have hface : ∃ y ∈ toricDivisorPolytope D, ∀ ρ ∈ orbitRays p,
        (D ρ : ℝ) + latticeFunctional ρ.val y = 0 := by
      refine ⟨x, hx, fun ρ hρ => le_antisymm (hcon ρ hρ) ?_⟩
      have := hx ρ
      change -(D ρ : ℝ) ≤ latticeFunctional ρ.val x at this
      linarith
    obtain ⟨k, m, hk, hmk, hzero⟩ := exists_rat_mem_face D (orbitRays p) hface
    have hpk := h k hk
    rw [mem_toricBaseLocus_iff_orbitRays] at hpk
    have hmP : m ∈ toricLatticePoints ((k : ℤ) • D) :=
      (mem_toricDivisorPolytope_smul_iff D hk _).mpr hmk
    obtain ⟨ρ, hρ, hpos⟩ := hpk m hmP
    have := hzero ρ hρ
    simp only [Pi.smul_apply, smul_eq_mul] at hpos
    omega
  · intro h k hk
    rw [mem_toricBaseLocus_iff_orbitRays]
    intro m hm
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hmk := (mem_toricDivisorPolytope_smul_iff D hk _).mp hm
    obtain ⟨x, hx, hxm⟩ := hmk
    obtain ⟨ρ, hρ, hpos⟩ := h x hx
    refine ⟨ρ, hρ, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    have h2 : (intPairing m ρ.val : ℝ) = (k : ℝ) * latticeFunctional ρ.val x := by
      rw [intPairing_comm, ← latticeFunctional_latticeVector, ← hxm, map_smul, smul_eq_mul]
    have h3 : (0 : ℝ) < ((k : ℤ) * D ρ + intPairing m ρ.val : ℤ) := by
      push_cast
      rw [h2]
      have := mul_pos hkR hpos
      linarith
    exact_mod_cast h3

/-- Source `cor:stablebl_toric`: the stable base locus of `D` is the union of the `V(τ)`,
`τ ∈ Σ`, such that every (real) `m ∈ P_D` has `a_ρ + ⟨m, u_ρ⟩ > 0` for some `ρ ∈ τ(1)`. -/
theorem toricStableBaseLocus_eq :
    toricStableBaseLocus D = ⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
      (_ : ∀ x ∈ toricDivisorPolytope D, ∃ ρ ∈ R, 0 < (D ρ : ℝ) + latticeFunctional ρ.val x),
      toricOrbitClosure R := by
  ext p
  simp only [mem_iUnion, exists_prop]
  rw [mem_toricStableBaseLocus_iff_orbitRays]
  constructor
  · intro h
    exact ⟨orbitRays p, isToricFanCone_orbitRays p, h, mem_toricOrbitClosure_orbitRays p⟩
  · rintro ⟨R, _, hR, hp⟩ x hx
    obtain ⟨ρ, hρ, hpos⟩ := hR x hx
    exact ⟨ρ, mem_toricOrbitClosure_iff.mp hp hρ, hpos⟩

/-- Source `cor:stablebl_toric`: the stable base locus is closed and `T(ℂ)`-invariant. -/
theorem isClosed_toricStableBaseLocus : IsClosed (toricStableBaseLocus D) :=
  isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_toricBaseLocus _

theorem polytopeToricAction_mem_toricStableBaseLocus_iff (a : Fin n → ℂˣ)
    (p : PolytopeToricVariety γ hs) :
    polytopeToricAction γ hs a p ∈ toricStableBaseLocus D ↔ p ∈ toricStableBaseLocus D := by
  simp only [toricStableBaseLocus, mem_iInter, polytopeToricAction_mem_toricBaseLocus_iff]

/-- The condition of `cor:stablebl_toric` is the emptiness of the face `Q_τ`. -/
theorem forall_exists_pos_iff_face_eq_empty (R : Set (PolytopeToricRays γ hs)) :
    (∀ x ∈ toricDivisorPolytope D, ∃ ρ ∈ R, 0 < (D ρ : ℝ) + latticeFunctional ρ.val x) ↔
      {x ∈ toricDivisorPolytope D | ∀ ρ ∈ R, latticeFunctional ρ.val x = -(D ρ : ℝ)} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  refine forall_congr' fun x => ?_
  simp only [mem_ofPred_eq, not_and, not_forall]
  refine imp_congr_right fun hx => exists_congr fun ρ => ?_
  have := hx ρ
  change -(D ρ : ℝ) ≤ latticeFunctional ρ.val x at this
  constructor
  · rintro ⟨hρ, h⟩; exact ⟨hρ, fun h' => by linarith⟩
  · rintro ⟨hρ, h⟩
    refine ⟨hρ, ?_⟩
    rcases this.lt_or_eq with h1 | h1
    · linarith
    · exact absurd h1.symm h

/-- Source `cor:stablebl_toric` ("geometrically, the condition means `Q_τ = ∅`"): the stable base
locus is the union of the `V(τ)` whose face `Q_τ = {m ∈ P_D : ⟨m, u_ρ⟩ = -a_ρ ∀ ρ ∈ τ(1)}`
(`eq:Qsigma`) is empty. -/
theorem toricStableBaseLocus_eq_faces :
    toricStableBaseLocus D = ⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
      (_ : {x ∈ toricDivisorPolytope D | ∀ ρ ∈ R, latticeFunctional ρ.val x = -(D ρ : ℝ)} = ∅),
      toricOrbitClosure R := by
  rw [toricStableBaseLocus_eq]
  ext p
  simp only [mem_iUnion, exists_prop]
  exact exists_congr fun R => and_congr_right fun _ =>
    and_congr_left fun _ => forall_exists_pos_iff_face_eq_empty D R

/-- The stable base locus is the base locus of a sufficiently divisible multiple:
`B(D) = Bs(kD)` for some `k ≥ 1`. -/
theorem exists_toricStableBaseLocus_eq_toricBaseLocus :
    ∃ k : ℕ, 0 < k ∧ toricStableBaseLocus D = toricBaseLocus ((k : ℤ) • D) := by
  classical
  have hfinR := (finite_polytopeToricRays γ hs).to_subtype
  have hfin : (Set.univ : Set (Set (PolytopeToricRays γ hs))).Finite := Set.toFinite _
  choose! kf mf hkf using fun (R : Set (PolytopeToricRays γ hs))
    (hR : ∃ x ∈ toricDivisorPolytope D, ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0) =>
    exists_rat_mem_face D R hR
  set good : Set (PolytopeToricRays γ hs) → Prop := fun R =>
    ∃ x ∈ toricDivisorPolytope D, ∀ ρ ∈ R, (D ρ : ℝ) + latticeFunctional ρ.val x = 0
  set k₀ : ℕ := ∏ R ∈ hfin.toFinset.filter good, kf R
  have hk₀ : 0 < k₀ := Finset.prod_pos fun R hR => (hkf R (Finset.mem_filter.mp hR).2).1
  refine ⟨k₀, hk₀, Set.Subset.antisymm ?_ ?_⟩
  · intro p hp
    exact mem_iInter₂.mp hp k₀ hk₀
  · intro p hp
    rw [mem_toricStableBaseLocus_iff_orbitRays]
    rw [mem_toricBaseLocus_iff_orbitRays] at hp
    intro x hx
    by_contra hcon
    push Not at hcon
    have hgood : good (orbitRays p) := by
      refine ⟨x, hx, fun ρ hρ => le_antisymm (hcon ρ hρ) ?_⟩
      have := hx ρ
      change -(D ρ : ℝ) ≤ latticeFunctional ρ.val x at this
      linarith
    obtain ⟨hkpos, hmk, hzero⟩ := hkf _ hgood
    have hdvd : kf (orbitRays p) ∣ k₀ :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr (mem_univ _), hgood⟩)
    obtain ⟨t, ht⟩ := hdvd
    set m := mf (orbitRays p)
    set k := kf (orbitRays p)
    have hmP : (t : ℤ) • m ∈ toricLatticePoints ((k₀ : ℤ) • D) := by
      apply (mem_toricDivisorPolytope_smul_iff D hk₀ _).mpr
      obtain ⟨y, hy, hym⟩ := hmk
      refine ⟨y, hy, ?_⟩
      have : latticeVector ((t : ℤ) • m) = (t : ℝ) • latticeVector m := by
        ext i; simp [latticeVector_apply]
      rw [this, ← hym, smul_smul, ht]
      push_cast; ring_nf
    obtain ⟨ρ, hρ, hpos⟩ := hp _ hmP
    have h0 := hzero ρ hρ
    simp only [Pi.smul_apply, smul_eq_mul] at hpos
    rw [intPairing_smul, ht] at hpos
    push_cast at hpos
    have : ((k : ℤ) * t) * D ρ + t * intPairing m ρ.val = t * ((k : ℤ) * D ρ + intPairing m ρ.val) := by
      ring
    rw [this, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos

/-- Source `cor:stablebl_toric`: the stable base locus is an analytic subset of `X`. -/
theorem hasAnalyticChartEquations_toricStableBaseLocus :
    (ofFixedModel n (PolytopeToricVariety γ hs)).HasAnalyticChartEquations
      (toricStableBaseLocus D) := by
  obtain ⟨k, -, hk⟩ := exists_toricStableBaseLocus_eq_toricBaseLocus D
  rw [hk]
  exact hasAnalyticChartEquations_toricBaseLocus _

end SGPT.Toric
