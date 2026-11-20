import SGPT.TestCurve.TCLinChart

/-!
# Ample test configurations: coordinates without common zeros and the chart condition

For a test configuration `(𝓧, 𝓛)` with `𝓛^r ≅ ι^* 𝒪(1)`,
`(ι, π) : 𝓧 ↪ ℙᴺ × 𝔸¹` a closed immersion, the coordinate sections `s_i = ι^* X_i` have no
common zeros (`noCommonZero_coordSec`) and satisfy the chart condition
(`chartCondition_coordSec`). Hence (`TCLin.filtrationFinitelyGenerated_of_chartCondition`)
**the filtration of every ample test configuration with a `𝔾_m`-linearization is finitely
generated** (`filtrationFinitelyGenerated_of_isAmple`, [BHJ17, Prop. 2.15], first half).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite SGPT.TestCurve.TestConfig SGPT.TestCurve.TCEnc SGPT.TestCurve.FGRel

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### An algebraic identity -/

theorem prod_mul_pow_eq {R : Type*} [CommRing R] {N : ℕ} (β : Fin (N + 1) →₀ ℕ) (u : R)
    (ρ : Fin (N + 1) → R) :
    (β.prod fun l e => (u * ρ l) ^ e) = u ^ expSum β * β.prod fun l e => ρ l ^ e := by
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, expSum,
    Finsupp.sum]

theorem expSum_some_le {N : ℕ} {Q : MvPolynomial (Option (Fin (N + 1))) ℂ}
    {γ : Option (Fin (N + 1)) →₀ ℕ} (hγ : γ ∈ Q.support) :
    expSum (Finsupp.some γ) ≤ Q.totalDegree := by
  have h1 := MvPolynomial.le_totalDegree hγ
  have h2 : (γ.sum fun _ e => e) = γ none + (Finsupp.some γ).sum fun _ e => e :=
    Finsupp.sum_option_index γ (fun _ e => e) (fun _ => rfl) (fun _ _ _ => rfl)
  rw [expSum]
  omega

/-- The exponent `β_γ = γ|_{Fin (N+1)} + (D₀ + k - |γ|) e_i` of the homogenized monomial. -/
def homExp {N : ℕ} (i : Fin (N + 1)) (D0 k : ℕ) (γ : Option (Fin (N + 1)) →₀ ℕ) :
    Fin (N + 1) →₀ ℕ :=
  Finsupp.some γ + Finsupp.single i (D0 + k - expSum (Finsupp.some γ))

theorem expSum_homExp {N : ℕ} (i : Fin (N + 1)) (D0 k : ℕ) (γ : Option (Fin (N + 1)) →₀ ℕ)
    (h : expSum (Finsupp.some γ) ≤ D0) : expSum (homExp i D0 k γ) = D0 + k := by
  rw [homExp, expSum, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, ← expSum]
  omega

/-- **Homogenization.** If `g = Q(t, ρ)` with `ρ_i = 1` and `D₀ ≥ deg Q`, then
`u^{D₀} (u^k g) = Σ_γ q_γ t^{γ₀} Π_l (u ρ_l)^{β_γ,l}`. -/
theorem homogenize {R : Type*} [CommRing R] {N : ℕ} (κ : ℂ →+* R)
    (v : Option (Fin (N + 1)) → R) (u : R) (i : Fin (N + 1)) (hvi : v (some i) = 1)
    (Q : MvPolynomial (Option (Fin (N + 1))) ℂ) (D0 k : ℕ) (hD0 : Q.totalDegree ≤ D0) :
    u ^ D0 * (u ^ k * MvPolynomial.eval₂ κ v Q) =
      ∑ γ ∈ Q.support, κ (Q.coeff γ) * v none ^ γ none *
        (homExp i D0 k γ).prod fun l e => (u * v (some l)) ^ e := by
  rw [MvPolynomial.eval₂_eq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have hb := (expSum_some_le hγ).trans hD0
  have hp : (∏ o ∈ γ.support, v o ^ γ o) =
      v none ^ γ none * (Finsupp.some γ).prod fun j e => v (some j) ^ e :=
    Finsupp.prod_option_index γ (fun o e => v o ^ e) (fun _ => pow_zero _)
      (fun _ _ _ => pow_add _ _ _)
  rw [hp, prod_mul_pow_eq, expSum_homExp i D0 k γ hb, homExp,
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (by rw [pow_zero]), hvi, one_pow, mul_one]
  ring

/-! ### The coordinate sections of an ample test configuration -/

section Ample

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a) {N r : ℕ} (ι : T.space ⟶ polynomialProj ℂ N)
  (e : bundleTensorPower T.line r ≅
    (Scheme.Modules.pullback ι).obj (polynomialProjTwistingLine ℂ N).sheaf)

theorem exists_mem_chartOpen (x : T.space) : ∃ j : Fin (N + 1), x ∈ chartOpen ι j := by
  have hcover : iSup (polynomialProjCoordinateOpen ℂ N) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates
  have hx : ι x ∈ iSup (polynomialProjCoordinateOpen ℂ N) := by rw [hcover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨j, hj⟩

/-- **The coordinate sections have no common zeros.** -/
theorem noCommonZero_coordSec :
    NoCommonZero T (fun i => (coordSec T.extAtlas ι e i : SectionSpace T.structureMap T.line r)) := by
  intro c x hx
  obtain ⟨j, hj⟩ := exists_mem_chartOpen T ι x
  let V := chartOpen ι j ⊓ T.extAtlas.opens c
  have hxV : x ∈ V := ⟨hj, hx⟩
  have hu := isUnit_locCoeff_coordSec T.extAtlas ι e j c (homOfLE inf_le_left : V ⟶ _)
    (homOfLE inf_le_right)
  rw [locCoeff_eq] at hu
  have hb := T.space.basicOpen_of_isUnit hu
  have hxb : x ∈ T.space.basicOpen
      (T.space.presheaf.map (homOfLE (inf_le_right : V ≤ T.extAtlas.opens c)).op
        (atlasPowerGlobalCoefficients T.extAtlas r c (coordSec T.extAtlas ι e j))) := by
    change x ∈ T.space.basicOpen (T.space.sheaf.obj.map _ _)
    rw [hb]
    exact hxV
  rw [Scheme.basicOpen_res] at hxb
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hxb.2⟩

/-- **The nonvanishing locus of `s_i` is the chart `𝓧_i = ι⁻¹(D₊(X_i))`** (in each chart of the
atlas). -/
theorem basicOpen_coordSec_le (i : Fin (N + 1)) (c : T.extAtlas.I) :
    T.space.basicOpen (atlasPowerGlobalCoefficients T.extAtlas r c (coordSec T.extAtlas ι e i)) ≤
      chartOpen ι i := by
  intro x hx
  have hxc : x ∈ T.extAtlas.opens c := T.space.basicOpen_le _ hx
  obtain ⟨j, hj⟩ := exists_mem_chartOpen T ι x
  let V := chartOpen ι j ⊓ T.extAtlas.opens c
  have hxV : x ∈ V := ⟨hj, hxc⟩
  have hrel := locCoeff_coordSec T.extAtlas ι e j i c (homOfLE inf_le_left : V ⟶ _)
    (homOfLE inf_le_right)
  rw [locCoeff_eq, locCoeff_eq] at hrel
  have hx1 : x ∈ T.space.basicOpen
      (T.space.presheaf.map (homOfLE (inf_le_right : V ≤ T.extAtlas.opens c)).op
        (atlasPowerGlobalCoefficients T.extAtlas r c (coordSec T.extAtlas ι e i))) := by
    rw [Scheme.basicOpen_res]
    exact ⟨hxV, hx⟩
  change x ∈ T.space.basicOpen (T.space.sheaf.obj.map _ _) at hx1
  rw [hrel, Scheme.basicOpen_mul] at hx1
  have hx2 := hx1.2
  change x ∈ T.space.basicOpen (T.space.presheaf.map _ _) at hx2
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen,
    polynomialProjCoordinateRegularRatio_globalBasicOpen] at hx2
  exact hx2.2.2


theorem secRing_of_smul (m : ℕ) (q : ℂ) (x : SectionSpace T.structureMap T.line m) :
    (SecRing.of m (q • x) : SecRing T.structureMap T.extAtlas) = q • SecRing.of m x := by
  refine DFinsupp.ext fun n => ?_
  change SecRing.comp n (SecRing.of m (q • x) : SecRing T.structureMap T.extAtlas) =
    SecRing.comp n (q • (SecRing.of m x : SecRing T.structureMap T.extAtlas))
  rw [SecRing.comp_smul]
  by_cases h : n = m
  · subst h
    rw [SecRing.comp_of_same, SecRing.comp_of_same]
  · rw [SecRing.comp_of_ne h, SecRing.comp_of_ne h, smul_zero]

theorem restrict_restrict_top {V U W : T.space.Opens} (hVU : V ≤ U) (hVW : V ≤ W)
    (x : Γ(T.space, ⊤)) :
    T.space.presheaf.map (homOfLE hVU).op (T.space.presheaf.map (homOfLE le_top).op x) =
      T.space.presheaf.map (homOfLE hVW).op (T.space.presheaf.map (homOfLE le_top).op x) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **The chart condition for the coordinate sections of an ample test configuration.** -/
theorem chartCondition_coordSec [IsIntegral T.space]
    (hι : ι ≫ polynomialProjStructureMap ℂ N = T.toLine ≫ affineLineToBase)
    [IsClosedImmersion (pullback.lift ι T.toLine hι)] :
    ChartCondition T (fun i => (coordSec T.extAtlas ι e i : SectionSpace T.structureMap T.line r)) := by
  classical
  intro i k σ
  let s : Fin (N + 1) → SectionSpace T.structureMap T.line r := fun i => coordSec T.extAtlas ι e i
  obtain ⟨Q, hQ⟩ := exists_mvPolynomial_chart ι T.toLine hι i (chartCoeff T.extAtlas ι e k i σ)
  let D0 := Q.totalDegree
  refine ⟨D0 + 1, ?_⟩
  let M' := r * (D0 + 1) + r * k
  let β' : (Option (Fin (N + 1)) →₀ ℕ) → Fin (N + 1) →₀ ℕ := fun γ =>
    homExp i D0 k γ + Finsupp.single i 1
  have hβ' : ∀ γ ∈ Q.support, expSum (β' γ) = D0 + 1 + k := by
    intro γ hγ
    have h1 := expSum_homExp i D0 k γ (expSum_some_le hγ)
    simp only [β', expSum] at h1 ⊢
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      h1]
    ring
  have hdeg : ∀ γ ∈ Q.support, r * expSum (β' γ) = M' := by
    intro γ hγ
    rw [hβ' γ hγ]
    ring
  -- the monomials are homogeneous, with known coefficients
  have hmon : ∀ γ ∈ Q.support,
      (SecRing.of M' (SecRing.comp M' (secMonomialξ T s (γ none) (β' γ))) :
          SecRing T.structureMap T.extAtlas) = secMonomialξ T s (γ none) (β' γ) ∧
      ∀ c, atlasPowerGlobalCoefficients T.extAtlas M' c
          (SecRing.comp M' (secMonomialξ T s (γ none) (β' γ))) =
        (T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine)) ^ (γ none) *
          (β' γ).prod fun l e => atlasPowerGlobalCoefficients T.extAtlas r c (s l) ^ e := by
    intro γ hγ
    obtain ⟨M, σ0, hM, hz, hc⟩ := exists_monomial_coeff T s (γ none) (β' γ)
    have hMM : M = M' := hM.trans (hdeg γ hγ)
    subst hMM
    rw [hz, SecRing.comp_of_same]
    exact ⟨rfl, hc⟩
  -- the identity of sections
  have hsec : SectionSpace.mul T.structureMap T.extAtlas (r * (D0 + 1)) (r * k)
      (secPow T.extAtlas (s i) (D0 + 1)) σ =
      ∑ γ ∈ Q.support, Q.coeff γ • SecRing.comp M' (secMonomialξ T s (γ none) (β' γ)) := by
    apply atlasPowerGlobalCoefficients_ext T.extAtlas M'
    intro c
    let u := atlasPowerGlobalCoefficients T.extAtlas r c (s i)
    let V : T.space.Opens := chartOpen ι i ⊓ T.extAtlas.opens c
    have hVU : V ≤ T.extAtlas.opens c := inf_le_right
    let kk : V ⟶ T.extAtlas.opens c := homOfLE hVU
    let h : V ⟶ chartOpen ι i := homOfLE inf_le_left
    let res : Γ(T.space, T.extAtlas.opens c) →+* Γ(T.space, V) := (T.space.presheaf.map kk.op).hom
    let κ : ℂ →+* Γ(T.space, V) :=
      (T.space.presheaf.map h.op).hom.comp (chartConstants T.toLine (chartOpen ι i))
    let v : Option (Fin (N + 1)) → Γ(T.space, V) := fun o =>
      T.space.presheaf.map h.op (chartGenerators ι T.toLine i o)
    let u' : Γ(T.space, V) := locCoeff T.extAtlas r c kk (s i)
    have hvi : v (some i) = 1 := by
      change T.space.presheaf.map h.op (ι.app _ (polynomialProjCoordinateRegularRatio ℂ N i i)) = 1
      rw [polynomialProjCoordinateRegularRatio_self, map_one, map_one]
    have hres_u : res u = u' := (locCoeff_eq T.extAtlas r c kk (s i)).symm
    have hres_s : ∀ l, res (atlasPowerGlobalCoefficients T.extAtlas r c (s l)) = u' * v (some l) := by
      intro l
      exact (locCoeff_eq T.extAtlas r c kk (s l)).symm.trans
        (locCoeff_coordSec T.extAtlas ι e i l c h kk)
    have hres_σ : res (atlasPowerGlobalCoefficients T.extAtlas (r * k) c σ) =
        u' ^ k * MvPolynomial.eval₂ κ v Q := by
      refine (locCoeff_eq T.extAtlas (r * k) c kk σ).symm.trans ?_
      rw [locCoeff_eq_chartCoeff T.extAtlas ι e k i c h kk σ, hQ]
      congr 1
      exact MvPolynomial.eval₂_comp_left (T.space.presheaf.map h.op).hom _ _ Q
    have hres_κ : ∀ q : ℂ, res (T.space.sheaf.obj.map (homOfLE le_top).op
        (schemeGlobalConstants T.structureMap q)) = κ q := by
      intro q
      change T.space.presheaf.map kk.op (T.space.presheaf.map (homOfLE le_top).op
          ((T.toLine ≫ affineLineToBase).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv q))) =
        T.space.presheaf.map h.op (T.space.presheaf.map (homOfLE le_top).op
          ((T.toLine ≫ affineLineToBase).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv q)))
      exact restrict_restrict_top T hVU inf_le_left _
    have hres_t : res (T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine)) = v none := by
      change T.space.presheaf.map kk.op (T.space.presheaf.map (homOfLE le_top).op
          (T.toLine.appTop coordT)) =
        T.space.presheaf.map h.op (T.space.presheaf.map (homOfLE le_top).op
          (T.toLine.appTop coordT))
      exact restrict_restrict_top T hVU inf_le_left _
    have hRHS : atlasPowerGlobalCoefficients T.extAtlas M' c
        (∑ γ ∈ Q.support, Q.coeff γ • SecRing.comp M' (secMonomialξ T s (γ none) (β' γ))) =
        (∑ γ ∈ Q.support, T.space.sheaf.obj.map (homOfLE le_top).op
            (schemeGlobalConstants T.structureMap (Q.coeff γ)) *
          ((T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine)) ^ (γ none) *
            (homExp i D0 k γ).prod fun l e =>
              atlasPowerGlobalCoefficients T.extAtlas r c (s l) ^ e)) * u := by
      refine (map_sum (coeffHom T.extAtlas M' c) (fun γ => (Q.coeff γ •
        SecRing.comp M' (secMonomialξ T s (γ none) (β' γ)) : SectionSpace T.structureMap T.line M'))
        Q.support).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      refine (SectionSpace.atlasPowerGlobalCoefficients_smul_const T.structureMap T.extAtlas M' c
        (Q.coeff γ) _).trans ?_
      rw [(hmon γ hγ).2 c]
      simp only [β']
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_single_index (by rw [pow_zero]), pow_one]
      ring
    have hLHS : atlasPowerGlobalCoefficients T.extAtlas M' c
        (SectionSpace.mul T.structureMap T.extAtlas (r * (D0 + 1)) (r * k)
          (secPow T.extAtlas (s i) (D0 + 1)) σ) =
        (u ^ D0 * atlasPowerGlobalCoefficients T.extAtlas (r * k) c σ) * u := by
      rw [SectionSpace.coefficients_mul, coeff_secPow, pow_succ]
      ring
    let A : T.space.sheaf.obj.obj (op (T.extAtlas.opens c)) :=
      u ^ D0 * atlasPowerGlobalCoefficients T.extAtlas (r * k) c σ
    let B : T.space.sheaf.obj.obj (op (T.extAtlas.opens c)) :=
      ∑ γ ∈ Q.support, T.space.sheaf.obj.map (homOfLE le_top).op
          (schemeGlobalConstants T.structureMap (Q.coeff γ)) *
        ((T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine)) ^ (γ none) *
          (homExp i D0 k γ).prod fun l e => atlasPowerGlobalCoefficients T.extAtlas r c (s l) ^ e)
    have hd : res (A - B) = 0 := by
      rw [map_sub, sub_eq_zero]
      have hA : res A = u' ^ D0 * (u' ^ k * MvPolynomial.eval₂ κ v Q) := by
        simp only [A, map_mul, map_pow]
        rw [hres_u, hres_σ]
      rw [hA, homogenize κ v u' i hvi Q D0 k le_rfl]
      simp only [B, map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_mul, map_mul, map_pow, hres_κ, hres_t, map_finsuppProd]
      simp only [map_pow, hres_s]
      rw [mul_assoc]
    have hfin : (A - B) * u = 0 := mul_eq_zero_of_restrict hVU _ _
      (le_inf (basicOpen_coordSec_le T ι e i c) (T.space.basicOpen_le _)) hd
    rw [hLHS, hRHS]
    exact sub_eq_zero.mp ((sub_mul A B u).symm.trans hfin)
  -- conclusion
  have hof : (SecRing.of M' (SectionSpace.mul T.structureMap T.extAtlas (r * (D0 + 1)) (r * k)
      (secPow T.extAtlas (s i) (D0 + 1)) σ) : SecRing T.structureMap T.extAtlas) =
      ∑ γ ∈ Q.support, Q.coeff γ • secMonomialξ T s (γ none) (β' γ) := by
    rw [hsec]
    refine (map_sum (DirectSum.of (SectionSpace T.structureMap T.line) M') (fun γ => (Q.coeff γ •
      SecRing.comp M' (secMonomialξ T s (γ none) (β' γ)) : SectionSpace T.structureMap T.line M'))
      Q.support).trans ?_
    refine Finset.sum_congr rfl fun γ hγ => ?_
    exact (secRing_of_smul T M' _ _).trans (congrArg (Q.coeff γ • ·) (hmon γ hγ).1)
  change (SecRing.of M' _ : SecRing T.structureMap T.extAtlas) ∈ _
  rw [hof]
  refine Submodule.sum_mem _ fun γ hγ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨γ none, β' γ, hβ' γ hγ, rfl⟩


end Ample

end SGPT.TestCurve.TCLin

namespace SGPT.TestCurve.TCLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open SGPT.TestCurve.TCEnc

/-- **[BHJ17, Prop. 2.15], first half, for ample test configurations with a `𝔾_m`-linearized line
bundle**: the filtration of `R(X, L)` induced by an ample test configuration `(𝓧, 𝓛)` of the
integral projective `(X, L)` whose line bundle `𝓛` carries a `𝔾_m`-linearization is finitely
generated (its Rees algebra `⊕_{m, λ} t^{-λ} 𝓕^λ H⁰(X, L^m) = ⊕_m H⁰(𝓧, m𝓛)` is a finitely
generated `ℂ`-algebra). -/
theorem filtrationFinitelyGenerated_of_isAmple {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}
    {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (T : TestConfiguration f a) (P : SectionLinearization T) (hA : T.IsAmple) :
    T.FiltrationFinitelyGenerated E := by
  obtain ⟨r, hr, N, ι, hι, hci, ⟨e⟩⟩ := hA
  have : IsIntegral T.space := T.isIntegral_space_of_embedding E
  have := hci
  exact filtrationFinitelyGenerated_of_chartCondition T P E hr _ (noCommonZero_coordSec T ι e)
    (chartCondition_coordSec T ι e hι)

/-- **The filtration of an ample linearized test configuration is finitely generated**
([BHJ17, Prop. 2.15], first half). -/
theorem LinearizedTestConfiguration.filtrationFinitelyGenerated {X : Scheme.{0}}
    {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (T : LinearizedTestConfiguration f a)
    (hA : T.IsAmple) : T.FiltrationFinitelyGenerated E :=
  filtrationFinitelyGenerated_of_isAmple E T.toTestConfiguration T.linearization hA

end SGPT.TestCurve.TCLin
