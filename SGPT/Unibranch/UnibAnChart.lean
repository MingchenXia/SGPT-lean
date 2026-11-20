import SGPT.Unibranch.UnibAlgAffine
import SGPT.Foundations.Schemes.SchemeAnalyticCountability

/-!
# Embedded affine charts of a complex scheme and their analytic transitions

Let `X` be a scheme with structure morphism `f : X ⟶ Spec ℂ`. An *embedded affine chart* of
`X` (`EmbeddedChart f`) is an open immersion `Spec ℂ[z₁, …, zₙ]/I ⟶ X` over `ℂ`. Its complex
points are the points of `V(I) ⊆ ℂⁿ` (`polynomialZeroSet I`): a point `c ∈ V(I)` gives the
evaluation `ℂ[z]/I → ℂ` and hence the complex point `chartPoint f e c` of `X`
(a morphism `Spec ℂ ⟶ X` over `ℂ`, `SGPT.Foundations.Schemes.SchemeComplexPoint f`).

* `chartPoint_injective`: different points of `V(I)` give different points of `X`.
* `exists_local_transition`: if `c ∈ V(I)` and `d ∈ V(I')` give the same point of `X` in two
  charts `e`, `e'`, there are polynomials `r`, `p_k` and exponents `m_k` with `r(c) ≠ 0` such
  that every `c' ∈ V(I)` with `r(c') ≠ 0` corresponds in the chart `e'` to the point
  `(p_k(c') / r(c')^{m_k})_k ∈ V(I')`. This is the regular (hence holomorphic) transition map
  between two embeddings; it comes from the lift of the basic open `D(r) ⊆ Spec ℂ[z]/I`
  through the open immersion of the second chart.
* `fracMap` and `contDiffAt_fracMap`: the transition `z ↦ (p_k(z) / r(z)^{m_k})_k` is a
  holomorphic map `ℂⁿ → ℂⁿ'` near every point with `r ≠ 0`.
* `exists_chart`, `exists_chartPoint_eq`: if `f` is locally of finite type, embedded affine
  charts cover `X`, and every complex point of `X` is a chart point.

These are the algebraic inputs for the analytification `𝒳^An` of `prop:unibranch_gaga`
(Appendix B of the book). Lane UNIB-AN; blueprint `claude-unib-an.tex`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.UnibAn

noncomputable section

open SGPT.Unibranch SGPT.Foundations.Schemes

/-! ### Points of `V(I)` as evaluations -/

section Points

variable {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}

/-- The evaluation `ℂ[z]/I → ℂ` at a point `c ∈ V(I)`. -/
def pointEval (c : polynomialZeroSet I) : MvPolynomial (Fin n) ℂ ⧸ I →+* ℂ :=
  Ideal.Quotient.lift I (MvPolynomial.eval (complexCoordinates (c.val : ComplexModel n)))
    (fun p hp => c.property p hp)

@[simp]
theorem pointEval_mk (c : polynomialZeroSet I) (p : MvPolynomial (Fin n) ℂ) :
    pointEval c (Ideal.Quotient.mk I p) =
      MvPolynomial.eval (complexCoordinates (c.val : ComplexModel n)) p :=
  Ideal.Quotient.lift_mk _ _ _

theorem algebraMap_coordRing (a : ℂ) :
    algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) a = Ideal.Quotient.mk I (MvPolynomial.C a) := by
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]

theorem pointEval_comp_algebraMap (c : polynomialZeroSet I) :
    (pointEval c).comp (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) = RingHom.id ℂ := by
  ext a
  simp [algebraMap_coordRing]

/-- The point of `ℂⁿ` with given coordinates. -/
def ofCoords (v : Fin n → ℂ) : (⊤ : TopologicalSpace.Opens (ComplexModel n)) :=
  ⟨WithLp.toLp 2 v, trivial⟩

@[simp]
theorem complexCoordinates_ofCoords (v : Fin n → ℂ) :
    complexCoordinates ((ofCoords v).val : ComplexModel n) = v := by
  funext k
  exact PiLp.toLp_apply 2 _ v k

theorem eq_of_complexCoordinates_eq {x y : (⊤ : TopologicalSpace.Opens (ComplexModel n))}
    (h : complexCoordinates (x.val : ComplexModel n) =
      complexCoordinates (y.val : ComplexModel n)) :
    x = y := by
  apply Subtype.ext
  apply PiLp.ext
  intro k
  exact congrFun h k

/-- A `ℂ`-algebra point of `ℂ[z]/I` is the evaluation at a point of `V(I)`. -/
def ofEval (χ : MvPolynomial (Fin n) ℂ ⧸ I →+* ℂ)
    (hχ : χ.comp (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) = RingHom.id ℂ) :
    polynomialZeroSet I :=
  ⟨ofCoords (fun k => χ (Ideal.Quotient.mk I (MvPolynomial.X k))), by
    have hext : χ.comp (Ideal.Quotient.mk I) =
        MvPolynomial.eval (fun k => χ (Ideal.Quotient.mk I (MvPolynomial.X k))) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have := congrArg (fun φ : ℂ →+* ℂ => φ a) hχ
        simpa [algebraMap_coordRing] using this
      · intro k
        simp
    intro p hp
    rw [complexCoordinates_ofCoords, ← hext]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]⟩

theorem pointEval_ofEval (χ : MvPolynomial (Fin n) ℂ ⧸ I →+* ℂ)
    (hχ : χ.comp (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) = RingHom.id ℂ) :
    pointEval (ofEval χ hχ) = χ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    have := congrArg (fun φ : ℂ →+* ℂ => φ a) hχ
    simpa [ofEval, algebraMap_coordRing] using this.symm
  · intro k
    simp [ofEval]

theorem pointEval_injective : Function.Injective (pointEval (I := I)) := by
  intro c d h
  apply Subtype.ext
  apply eq_of_complexCoordinates_eq
  funext k
  have := congrArg (fun φ => φ (Ideal.Quotient.mk I (MvPolynomial.X k))) h
  simpa using this

end Points

/-! ### Embedded affine charts -/

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-- The coordinate ring `ℂ[z₁, …, zₙ]/I` as a commutative ring. -/
abbrev coordRing {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) : CommRingCat :=
  CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I)

/-- An embedded affine chart of a scheme `X` over `ℂ`: an open immersion
`Spec ℂ[z₁, …, zₙ]/I ⟶ X` compatible with the structure morphisms. -/
structure EmbeddedChart where
  /-- The number `n` of coordinates. -/
  dim : ℕ
  /-- The ideal `I ⊆ ℂ[z₁, …, zₙ]`. -/
  ideal : Ideal (MvPolynomial (Fin dim) ℂ)
  /-- The open immersion `Spec ℂ[z]/I ⟶ X`. -/
  map : Spec (coordRing ideal) ⟶ X
  isOpenImmersion : IsOpenImmersion map
  /-- The chart is a morphism over `ℂ`. -/
  isOver : map ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin dim) ℂ ⧸ ideal)))

attribute [instance] EmbeddedChart.isOpenImmersion

variable {f}

/-- The complex point of `X` given by a point `c ∈ V(I)` of an embedded chart. -/
def chartPoint (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) : SchemeComplexPoint f :=
  ⟨Spec.map (CommRingCat.ofHom (pointEval c)) ≫ e.map, by
    rw [Category.assoc, e.isOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      pointEval_comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id]⟩

theorem chartPoint_val (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    (chartPoint e c).val = Spec.map (CommRingCat.ofHom (pointEval c)) ≫ e.map := rfl

/-- Different points of `V(I)` give different complex points of `X`. -/
theorem chartPoint_injective (e : EmbeddedChart f) : Function.Injective (chartPoint e) := by
  intro c d h
  have h1 := (cancel_mono e.map).mp (congrArg Subtype.val h)
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  exact pointEval_injective h2

/-- The underlying scheme point of `chartPoint e c` is the image of the maximal ideal of `c`. -/
theorem chartPoint_image (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    schemeComplexPointImage f (chartPoint e c) =
      e.map (Spec.map (CommRingCat.ofHom (pointEval c)) default) :=
  Scheme.Hom.comp_apply _ _ _

/-- The point `Spec ℂ → Spec ℂ[z]/I` of `c ∈ V(I)` is the kernel of the evaluation. -/
theorem spec_pointEval_asIdeal {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (c : polynomialZeroSet I) (y : Spec (.of ℂ)) :
    (Spec.map (CommRingCat.ofHom (pointEval c)) y).asIdeal = RingHom.ker (pointEval c) := by
  have hy : (y : PrimeSpectrum ℂ).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime ℂ _ _ (PrimeSpectrum.isPrime _)
  change Ideal.comap (pointEval c) (y : PrimeSpectrum ℂ).asIdeal = _
  rw [hy]
  rfl

/-! ### Transitions between two embedded charts -/

/-- A polynomial evaluated at a point of `ℂⁿ`. -/
abbrev polyEval {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (z : ComplexModel n) : ℂ :=
  MvPolynomial.eval (complexCoordinates z) p

/-- **The regular transition between two embedded charts.** If `c ∈ V(I)` (chart `e`) and
`d ∈ V(I')` (chart `e'`) are the same complex point of `X`, then there are a polynomial `r`
with `r(c) ≠ 0`, polynomials `p_k` and exponents `m_k` such that every `c' ∈ V(I)` with
`r(c') ≠ 0` is, in the chart `e'`, the point with coordinates `p_k(c') / r(c')^{m_k}`.
Proof: a basic open `D(r) ∋ c` of `Spec ℂ[z]/I` lies in the second chart; the lift of
`Spec ℂ[z]/I_r ⟶ X` through the second open immersion is `Spec` of a `ℂ`-algebra map
`ψ : ℂ[z']/I' → ℂ[z]/I_r`, and `ψ(z'_k) = p_k / r^{m_k}`. -/
theorem exists_local_transition (e e' : EmbeddedChart f) (c : polynomialZeroSet e.ideal)
    (d : polynomialZeroSet e'.ideal) (h : chartPoint e' d = chartPoint e c) :
    ∃ (r : MvPolynomial (Fin e.dim) ℂ) (p : Fin e'.dim → MvPolynomial (Fin e.dim) ℂ)
      (m : Fin e'.dim → ℕ), polyEval r (c.val : ComplexModel e.dim) ≠ 0 ∧
      ∀ c' : polynomialZeroSet e.ideal, polyEval r (c'.val : ComplexModel e.dim) ≠ 0 →
        ∃ d' : polynomialZeroSet e'.ideal,
          complexCoordinates (d'.val : ComplexModel e'.dim) =
            (fun k => polyEval (p k) (c'.val : ComplexModel e.dim) /
              polyEval r (c'.val : ComplexModel e.dim) ^ m k) ∧
          chartPoint e' d' = chartPoint e c' := by
  classical
  have hP' : e.map (Spec.map (CommRingCat.ofHom (pointEval c)) default) ∈ Set.range e'.map := by
    refine ⟨Spec.map (CommRingCat.ofHom (pointEval d)) default, ?_⟩
    have := congrArg (schemeComplexPointImage f) h
    rwa [chartPoint_image, chartPoint_image] at this
  have hP : Spec.map (CommRingCat.ofHom (pointEval c)) default ∈ e.map ⁻¹' Set.range e'.map :=
    hP'
  have hopen : IsOpen (e.map ⁻¹' Set.range e'.map) :=
    e'.map.isOpenEmbedding.isOpen_range.preimage e.map.continuous
  obtain ⟨_, ⟨r₀, rfl⟩, hPr, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens
      (R := MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal)).exists_subset_of_mem_open hP hopen
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r₀
  have hcr : polyEval r (c.val : ComplexModel e.dim) ≠ 0 := by
    have h1 : Ideal.Quotient.mk e.ideal r ∉
        (Spec.map (CommRingCat.ofHom (pointEval c)) default).asIdeal :=
      (PrimeSpectrum.mem_basicOpen _ _).mp hPr
    rw [spec_pointEval_asIdeal, RingHom.mem_ker, pointEval_mk] at h1
    exact h1
  let L := Localization.Away (Ideal.Quotient.mk e.ideal r)
  let ι : coordRing e.ideal ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap _ L)
  have hrange : Set.range (Spec.map ι ≫ e.map) ⊆ Set.range e'.map := by
    rintro _ ⟨s, rfl⟩
    have hs : Spec.map ι s ∈ (PrimeSpectrum.basicOpen (Ideal.Quotient.mk e.ideal r) :
        Set (PrimeSpectrum (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal))) := by
      rw [← PrimeSpectrum.localization_away_comap_range L]
      exact ⟨s, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hsub hs
  let Λ := IsOpenImmersion.lift e'.map (Spec.map ι ≫ e.map) hrange
  have hΛ : Λ ≫ e'.map = Spec.map ι ≫ e.map := IsOpenImmersion.lift_fac _ _ _
  let ψ : coordRing e'.ideal ⟶ CommRingCat.of L := Spec.preimage Λ
  have hψ : Spec.map ψ = Λ := Spec.map_preimage Λ
  have hψC : CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal)) ≫ ψ =
      CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal)) ≫ ι := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ← e'.isOver, ← e.isOver, hψ, ← Category.assoc, hΛ,
      Category.assoc]
  have hsurj : ∀ k : Fin e'.dim, ∃ (j : ℕ) (a : MvPolynomial (Fin e.dim) ℂ),
      ψ.hom (Ideal.Quotient.mk e'.ideal (MvPolynomial.X k)) *
          algebraMap _ L (Ideal.Quotient.mk e.ideal r) ^ j =
        algebraMap _ L (Ideal.Quotient.mk e.ideal a) := by
    intro k
    obtain ⟨j, a, ha⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk e.ideal r)
      (ψ.hom (Ideal.Quotient.mk e'.ideal (MvPolynomial.X k)))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨j, a, ha⟩
  choose m p hp using hsurj
  refine ⟨r, p, m, hcr, ?_⟩
  intro c' hc'
  have hunit : IsUnit (pointEval c' (Ideal.Quotient.mk e.ideal r)) := by
    rw [pointEval_mk]
    exact isUnit_iff_ne_zero.mpr hc'
  let χ : L →+* ℂ := IsLocalization.Away.lift (Ideal.Quotient.mk e.ideal r) hunit
  have hχ : ∀ a, χ (algebraMap _ L a) = pointEval c' a :=
    IsLocalization.Away.lift_eq (Ideal.Quotient.mk e.ideal r) hunit
  let μ : (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal) →+* ℂ := χ.comp ψ.hom
  have hμ : μ.comp (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal)) = RingHom.id ℂ := by
    apply RingHom.ext
    intro a
    have h1 : ψ.hom (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal) a) =
        algebraMap _ L (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal) a) :=
      congrArg (fun g => g.hom a) hψC
    have h2 : pointEval c' (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal) a) = a :=
      congrArg (fun g : ℂ →+* ℂ => g a) (pointEval_comp_algebraMap c')
    change χ (ψ.hom (algebraMap ℂ (MvPolynomial (Fin e'.dim) ℂ ⧸ e'.ideal) a)) = a
    rw [h1, hχ, h2]
  refine ⟨ofEval μ hμ, ?_, ?_⟩
  · funext k
    simp only [ofEval, complexCoordinates_ofCoords]
    have hk := congrArg χ (hp k)
    rw [map_mul, map_pow, hχ, hχ, pointEval_mk, pointEval_mk] at hk
    rw [eq_div_iff (pow_ne_zero _ hc')]
    exact hk
  · apply Subtype.ext
    rw [chartPoint_val, chartPoint_val, pointEval_ofEval]
    have h1 : CommRingCat.ofHom μ = ψ ≫ CommRingCat.ofHom χ := rfl
    have h2 : CommRingCat.ofHom (pointEval c') = ι ≫ CommRingCat.ofHom χ :=
      CommRingCat.hom_ext (RingHom.ext fun a => (hχ a).symm)
    rw [h1, h2, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hψ, hΛ]

/-- The coordinate transition `z ↦ (p_k(z) / r(z)^{m_k})_k`. -/
def fracMap {n n' : ℕ} (r : MvPolynomial (Fin n) ℂ) (p : Fin n' → MvPolynomial (Fin n) ℂ)
    (m : Fin n' → ℕ) (z : ComplexModel n) : ComplexModel n' :=
  WithLp.toLp 2 (fun k => polyEval (p k) z / polyEval r z ^ m k)

theorem complexCoordinates_fracMap {n n' : ℕ} (r : MvPolynomial (Fin n) ℂ)
    (p : Fin n' → MvPolynomial (Fin n) ℂ) (m : Fin n' → ℕ) (z : ComplexModel n) :
    complexCoordinates (fracMap r p m z) = fun k => polyEval (p k) z / polyEval r z ^ m k := by
  funext k
  exact PiLp.toLp_apply 2 _ _ k

open scoped ContDiff in
/-- Polynomials are holomorphic. -/
theorem contDiff_polyEval {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ ∞ (polyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : polyEval (MvPolynomial.C a : MvPolynomial (Fin n) ℂ) = fun _ => a := by
      funext z
      simp [polyEval]
    rw [this]
    exact contDiff_const
  | add p q hp hq =>
    have : polyEval (p + q) = fun z => polyEval p z + polyEval q z := by
      funext z
      simp [polyEval]
    rw [this]
    exact hp.add hq
  | mul_X p k hp =>
    have : polyEval (p * MvPolynomial.X k) = fun z => polyEval p z * (z : ComplexModel n) k := by
      funext z
      simp [polyEval, complexCoordinates_apply]
    rw [this]
    exact hp.mul (contDiff_piLp_apply 2)

open scoped ContDiff in
/-- The coordinate transition is holomorphic where its denominator does not vanish. -/
theorem contDiffAt_fracMap {n n' : ℕ} (r : MvPolynomial (Fin n) ℂ)
    (p : Fin n' → MvPolynomial (Fin n) ℂ) (m : Fin n' → ℕ) {z : ComplexModel n}
    (hz : polyEval r z ≠ 0) : ContDiffAt ℂ ∞ (fracMap r p m) z := by
  apply contDiffAt_piLp' 2
  intro k
  have : (fun w => (fracMap r p m w).ofLp k) =
      fun w => polyEval (p k) w / polyEval r w ^ m k := by
    funext w
    exact PiLp.toLp_apply 2 _ _ k
  rw [this]
  exact ((contDiff_polyEval (p k)).contDiffAt).div
    (((contDiff_polyEval r).pow (m k)).contDiffAt) (pow_ne_zero _ hz)

/-- The transition of `exists_local_transition`, in coordinates: the chart-`e'` point is
`fracMap r p m` of the chart-`e` point. -/
theorem exists_local_fracMap (e e' : EmbeddedChart f) (c : polynomialZeroSet e.ideal)
    (d : polynomialZeroSet e'.ideal) (h : chartPoint e' d = chartPoint e c) :
    ∃ (r : MvPolynomial (Fin e.dim) ℂ) (p : Fin e'.dim → MvPolynomial (Fin e.dim) ℂ)
      (m : Fin e'.dim → ℕ), polyEval r (c.val : ComplexModel e.dim) ≠ 0 ∧
      ∀ c' : polynomialZeroSet e.ideal, polyEval r (c'.val : ComplexModel e.dim) ≠ 0 →
        ∃ d' : polynomialZeroSet e'.ideal,
          (d'.val : ComplexModel e'.dim) = fracMap r p m (c'.val : ComplexModel e.dim) ∧
          chartPoint e' d' = chartPoint e c' := by
  obtain ⟨r, p, m, hc, H⟩ := exists_local_transition e e' c d h
  refine ⟨r, p, m, hc, fun c' hc' => ?_⟩
  obtain ⟨d', hd', hpt⟩ := H c' hc'
  refine ⟨d', ?_, hpt⟩
  apply PiLp.ext
  intro k
  have h1 := congrFun hd' k
  have h2 := congrFun (complexCoordinates_fracMap r p m (c'.val : ComplexModel e.dim)) k
  exact h1.trans h2.symm

/-! ### Existence of embedded charts -/

/-- If `X` is reduced, the ideal of every embedded chart is radical. -/
theorem EmbeddedChart.ideal_isRadical [IsReduced X] (e : EmbeddedChart f) :
    e.ideal.IsRadical := by
  have : IsReduced (Spec (coordRing e.ideal)) := isReduced_of_isOpenImmersion e.map
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr ((affine_isReduced_iff _).mp this)

/-- If `f` is locally of finite type, every point of `X` lies in an embedded affine chart. -/
theorem exists_chart [LocallyOfFiniteType f] (x : X) :
    ∃ (e : EmbeddedChart f) (q : Spec (coordRing e.ideal)), e.map q = x := by
  obtain ⟨R, g, hg, y, hy⟩ := X.exists_Spec_apply_eq x
  let := affinePointFieldAlgebra (g ≫ f)
  have hft : Algebra.FiniteType ℂ R := complexAffineChart_finiteType f ⟨R, g, hg⟩
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let E := Ideal.quotientKerAlgEquivOfSurjective hφ
  let σ : CommRingCat.of R ≅ coordRing (RingHom.ker φ) := E.symm.toRingEquiv.toCommRingCatIso
  have hover : (Spec.map σ.hom ≫ g) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker φ))) := by
    rw [Category.assoc, ← affinePointFieldAlgebra_structure (g ≫ f), complexAffineStructureMap,
      ← Spec.map_comp]
    congr 1
    ext a
    exact E.symm.commutes a
  refine ⟨⟨n, RingHom.ker φ, Spec.map σ.hom ≫ g, inferInstance, hover⟩, Spec.map σ.inv y, ?_⟩
  change (Spec.map σ.hom ≫ g) (Spec.map σ.inv y) = x
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (Spec.map σ.inv), ← Spec.map_comp,
    σ.hom_inv_id, Spec.map_id]
  exact hy

/-- The point `c ∈ V(I)` as a complex point of the chart scheme `Spec ℂ[z]/I`. -/
def chartSpecPoint (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    SchemeComplexPoint (e.map ≫ f) :=
  ⟨Spec.map (CommRingCat.ofHom (pointEval c)), by
    rw [e.isOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pointEval_comp_algebraMap,
      CommRingCat.ofHom_id, Spec.map_id]⟩

theorem chartPoint_eq_map (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    chartPoint e c = schemeComplexPointMap (e.map ≫ f) f e.map rfl (chartSpecPoint e c) := rfl

theorem specPoint_comp_algebraMap (e : EmbeddedChart f) (p : SchemeComplexPoint (e.map ≫ f)) :
    (Spec.preimage p.val).hom.comp (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal)) =
      RingHom.id ℂ := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin e.dim) ℂ ⧸ e.ideal)) ≫
      Spec.preimage p.val) = Spec.map (𝟙 (CommRingCat.of ℂ)) := by
    rw [Spec.map_comp, Spec.map_preimage, ← e.isOver, Spec.map_id]
    exact p.property
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  simpa using h2

/-- A complex point of the chart scheme `Spec ℂ[z]/I` is a point of `V(I)`. -/
def ofSpecPoint (e : EmbeddedChart f) (p : SchemeComplexPoint (e.map ≫ f)) :
    polynomialZeroSet e.ideal :=
  ofEval (Spec.preimage p.val).hom (specPoint_comp_algebraMap e p)

theorem pointEval_ofSpecPoint (e : EmbeddedChart f) (p : SchemeComplexPoint (e.map ≫ f)) :
    pointEval (ofSpecPoint e p) = (Spec.preimage p.val).hom :=
  pointEval_ofEval _ _

theorem chartSpecPoint_ofSpecPoint (e : EmbeddedChart f) (p : SchemeComplexPoint (e.map ≫ f)) :
    chartSpecPoint e (ofSpecPoint e p) = p := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (pointEval (ofSpecPoint e p))) = p.val
  rw [pointEval_ofSpecPoint, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem ofSpecPoint_chartSpecPoint (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    ofSpecPoint e (chartSpecPoint e c) = c := by
  apply pointEval_injective
  rw [pointEval_ofSpecPoint]
  change (Spec.preimage (Spec.map (CommRingCat.ofHom (pointEval c)))).hom = _
  rw [Spec.preimage_map, CommRingCat.hom_ofHom]

/-- If `f` is locally of finite type, every complex point of `X` is a chart point. -/
theorem exists_chartPoint_eq [LocallyOfFiniteType f] (p : SchemeComplexPoint f) :
    ∃ (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal), chartPoint e c = p := by
  obtain ⟨e, q, hq⟩ := exists_chart (f := f) (schemeComplexPointImage f p)
  let l := schemeComplexPointLift f e.map p ⟨q, hq⟩
  refine ⟨e, ofSpecPoint e l, ?_⟩
  rw [chartPoint_eq_map, chartSpecPoint_ofSpecPoint]
  apply Subtype.ext
  exact schemeComplexPointLift_fac f e.map p ⟨q, hq⟩

/-- The scheme point of `chartPoint e c` is the closed point `e(c)` of `X`. -/
theorem chartPoint_image_eq (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    schemeComplexPointImage f (chartPoint e c) = e.map (UnibAlg.closedPoint c) := by
  rw [chartPoint_image]
  have : Spec.map (CommRingCat.ofHom (pointEval c)) default = UnibAlg.closedPoint c :=
    PrimeSpectrum.ext (spec_pointEval_asIdeal c default)
  rw [this]

/-- If `f` is locally of finite type, every closed point of `X` is the image of the maximal
ideal of a point of `V(I)` in some embedded chart (Hilbert's Nullstellensatz). -/
theorem exists_closedPoint_eq [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal),
      e.map (UnibAlg.closedPoint c) = x := by
  classical
  obtain ⟨e, q, hq⟩ := exists_chart (f := f) x
  have hqc : IsClosed ({q} : Set (Spec (coordRing e.ideal))) := by
    have : ({q} : Set (Spec (coordRing e.ideal))) = e.map ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact hq
      · intro hy
        exact e.map.isOpenEmbedding.injective (hy.trans hq.symm)
    rw [this]
    exact hx.preimage e.map.continuous
  have hmax : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hqc
  let M := Ideal.comap (Ideal.Quotient.mk e.ideal) q.asIdeal
  have hM : M.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨v, hv⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hM
  have hvI : ∀ p ∈ e.ideal, MvPolynomial.eval v p = 0 := by
    intro p hp
    have : p ∈ M := by
      change Ideal.Quotient.mk e.ideal p ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      exact q.asIdeal.zero_mem
    rw [hv] at this
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff v p).mp this
  let c : polynomialZeroSet e.ideal := ⟨ofCoords v, by
    intro p hp
    rw [complexCoordinates_ofCoords]
    exact hvI p hp⟩
  refine ⟨e, c, ?_⟩
  rw [← hq]
  congr 1
  apply PrimeSpectrum.ext
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  ext p
  change Ideal.Quotient.lift e.ideal (MvPolynomial.eval
      (complexCoordinates ((ofCoords v).val : ComplexModel e.dim))) _
        (Ideal.Quotient.mk e.ideal p) = 0 ↔ p ∈ M
  rw [Ideal.Quotient.lift_mk, complexCoordinates_ofCoords, hv,
    MvPolynomial.mem_vanishingIdeal_singleton_iff]
  exact Iff.rfl

end

end SGPT.Unibranch.UnibAn
