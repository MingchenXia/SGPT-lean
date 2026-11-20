import SGPT.BDivisor.BD6Prime
import SGPT.Projective.OriginalProjectivePositiveLine

/-!
# the cycle class of every prime divisor of `V(ℂ)` is algebraic

Source: `rmk:bdiv:L749` (GAGA for divisors on the algebraized models).

Let `V` be an integral smooth projective complex scheme and `P` a prime divisor of `V(ℂ)`.
Chow's theorem gives homogeneous `F_k` of degree `e` cutting out `ι(P)` with its full cone ideal;
by `BD6Prime` and `BD6Morphism`, `F = (F_k)` defines a morphism `φ_F : V → ℙʳ`, `φ_F = [u_k]`
where `F_k(x/xᵢ) = h u_k`, `h` a local equation of `P`.  The family `G = (F_{j₀}, x₀^e, …, x_N^e)`
has no base points and defines `φ_G : V → ℙ^{N+1}`.  For the algebraic line bundles
`L_F = φ_F^*𝒪(1)`, `L_G = φ_G^*𝒪(1)` (Codex's `originalMapHyperplaneBundle`), the pulled-back
coordinate sections `φ_F^*y_{j₀}` and `φ_G^*y_0` have analytic divisors `div(u_{j₀})` and
`div(h u_{j₀}) = P + div(u_{j₀})` (`BD6Divisor`).  Lelong–Poincaré for algebraic sections
(`SchemeLineBundleMetric.sectionMeteredDivisor_isDivisorMetric`) gives
**`cl(P) = c₁(L_G) − c₁(L_F)`** (`cycleClass_prime_eq_sub`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.BDivisor.BD6

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos SGPT.Projective
open SGPT.Projective.ComplexProjectiveSpace
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveReadback
open SGPT.BDivisor.DFAlg

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (EV : ClosedProjectiveEmbedding g) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) g] [IsSeparated g] [QuasiCompact g]

local instance bd6CycTopology {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd6CycCharts {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd6CycManifold {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-- `BD6Divisor.MapData.coordSection_ideal_mem` for an arbitrary structure morphism. -/
theorem coordSection_ideal_mem_of {r : ℕ} (φ : V ⟶ polynomialProj ℂ r)
    (hφ : φ ≫ polynomialProjStructureMap ℂ r = g) (k : Fin (r + 1))
    {Nb : Set (SchemeComplexPoint g)} {u : Fin (r + 1) → SchemeComplexPoint g → ℂ}
    (hNb : IsOpen Nb) (hu : ∀ y ∈ Nb, ∀ k, HolomorphicAt (m + 1) (u k) y)
    (hne : ∀ y ∈ Nb, (fun k => u k y) ≠ 0)
    (hpt : ∀ y (hy : y ∈ Nb), schemeComplexPointMap g (polynomialProjStructureMap ℂ r) φ hφ y =
      polynomialProjNonzeroVectorPoint r ⟨fun k => u k y, hne y hy⟩)
    {z : SchemeComplexPoint g} (hz : z ∈ Nb) (f : SchemeComplexPoint g → ℂ) :
    (schemeSectionAnalyticIdeal g (m + 1) EV (originalMapHyperplaneAtlas φ) 1
        (coordSection φ k)).mem z f ↔ IsInSpanAt (n := m + 1) (· = u k) z f := by
  subst hφ
  exact (MapData.mk Nb u hNb hu hne hpt).coordSection_ideal_mem EV k hz f

/-- A family without base points on the chart `Uᵢ` (`h = 1`). -/
def LocalFactorization.ofNoBase {r : ℕ} (G : Fin (r + 1) → MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ)
    (i : Fin (EV.ambientDimension + 1))
    (hne : ∀ y, schemeComplexPointImage g y ∈ coordOpen EV i →
      (fun k => MvPolynomial.eval (homCoords g EV (m + 1) i y) (G k)) ≠ 0) :
    LocalFactorization g EV (m + 1) G i where
  Nb := schemeComplexPointImage g ⁻¹' (coordOpen EV i : Set V)
  h := fun _ => 1
  u := fun k y => MvPolynomial.eval (homCoords g EV (m + 1) i y) (G k)
  isOpen := isOpen_coordOpen_points g EV i
  chart := fun _ hz => hz
  eq := fun _ _ _ => (one_mul _).symm
  hol := fun z hz k => (schemeOpenRegularFunction_holomorphicAt g (m + 1) EV _
      (chartFn g EV i (G k)) z hz).congr (by
    filter_upwards [(isOpen_coordOpen_points g EV i).mem_nhds hz] with y hy
    exact chartFn_value g EV (m + 1) i (G k) y hy)
  ne := hne
  dense := fun _ _ _ ⟨y, hy⟩ => ⟨y, hy, one_ne_zero⟩

omit [SmoothOfRelativeDimension (m + 1) g] [IsSeparated g] [QuasiCompact g] in
theorem effectiveDivisor_eq_of_ideal_eq {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] {D D' : EffectiveDivisor d M} (h : D.ideal = D'.ideal) :
    D = D' := by
  obtain ⟨I, hI⟩ := D
  obtain ⟨I', hI'⟩ := D'
  subst h
  rfl

omit [SmoothOfRelativeDimension (m + 1) g] [IsSeparated g] [QuasiCompact g] in
/-- **The cycle class is additive.** -/
theorem cycleClass_add {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M] (D D' : EffectiveDivisor (m + 1) M) :
    cycleClass (GermIdealTotalTransform.EffectiveDivisor.add D D') = cycleClass D + cycleClass D' := by
  obtain ⟨E, -, hE⟩ := DivisorMetric.exists_divisorMetric D
  obtain ⟨E', -, hE'⟩ := DivisorMetric.exists_divisorMetric D'
  rw [cycleClass_eq_of_isDivisorMetric _ _ (isDivisorMetric_meteredAdd D D' E E' hE hE'),
    cycleClass_eq_of_isDivisorMetric D E hE, cycleClass_eq_of_isDivisorMetric D' E' hE']
  exact RealBottChern.ofRepresentative_add E.curvature E'.curvature

/-- **Chow equations of a prime divisor**, indexed by `Fin (r + 1)`. -/
theorem exists_chow_family_prime
    (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) (SchemeComplexPoint g)) :
    ∃ (e r : ℕ) (F : Fin (r + 1) → MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ),
      (∀ k, (F k).IsHomogeneous e) ∧
      (coneIdeal (projectivePoint g EV (m + 1) '' P.val)).GeneratedOn
        (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace EV.ambientDimension))
        (fun k => SGPT.GAGA.PN.polyTuple (F k)) := by
  classical
  have : CompactSpace (SchemeComplexPoint g) := EV.analyticCompact
  have hι := isHolomorphicEmbedding_projectivePoint g EV (m + 1)
  have hC : SGPT.Foundations.Analysis.FirstPass.IsComplexAnalyticSubset (n := m + 1) P.val := by
    rw [← P.subvariety_carrier]
    exact P.subvariety.irreducible_carrier.1
  obtain ⟨m₀, hm⟩ := chow_image hι hC
  obtain ⟨μ, hμ, Fμ, hFhom, hgen, -⟩ := hm m₀ le_rfl
  set eμ := Fintype.equivFin μ
  let F : Fin (Fintype.card μ + 1) → MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ :=
    Fin.cons 0 (fun k => Fμ (eμ.symm k))
  refine ⟨m₀, Fintype.card μ, F, fun k => ?_, ?_⟩
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact MvPolynomial.isHomogeneous_zero _ _ _
    · simpa [F] using hFhom (eμ.symm k)
  · refine hgen.of_generators (fun l j => ?_) (fun y hy l => ?_) (fun y _ k => ?_)
    · exact (SGPT.GAGA.PN.differentiable_eval_poly (F l)).differentiableOn
    · refine Fin.cases ?_ (fun k => ?_) l
      · refine ⟨Eventually.of_forall fun z => (SGPT.GAGA.PN.differentiable_eval_poly 0) z,
          Eventually.of_forall fun z _ => ?_⟩
        simp [F, SGPT.GAGA.PN.polyTuple]
      · simpa [F] using hgen.gen_mem hy (eμ.symm k)
    · have h := SGPT.GAGA.Core.isCombinationAt_gen (fun l => SGPT.GAGA.PN.polyTuple (F l)) y
        (Fin.succ (eμ k))
      simpa [F] using h

/-! ### The cycle class of a prime divisor -/

/-- The algebraic line bundle `φ^*𝒪(1)` with its pulled-back atlas (Codex's
`originalMapHyperplaneBundle`). -/
def mapLine {r : ℕ} (φ : V ⟶ polynomialProj ℂ r) : IntrinsicLineBundle V :=
  ⟨originalMapHyperplaneBundle φ, originalMapHyperplaneAtlas φ⟩

/-- The first Chern class `c₁(A) ∈ H^{1,1}_{BC}(V(ℂ), ℝ)` of an algebraic line bundle (computed with
the canonical structural metric; it does not depend on the metric, `chernClass_independent`). -/
abbrev algChern (A : IntrinsicLineBundle V) : RealBottChern (m + 1) (SchemeComplexPoint g) :=
  RealBottChern.ofRepresentative ((schemeLineBundleMetric g (m + 1) EV A.atlas).curvature A.atlas)

variable [IsIntegral V] [CompactSpace (SchemeComplexPoint g)]

/-- Lelong–Poincaré for a coordinate section: `cl(div φ^*y_k) = c₁(φ^*𝒪(1))`. -/
theorem cycleClass_coordSection {r : ℕ} (φ : V ⟶ polynomialProj ℂ r) (k : Fin (r + 1))
    (hs : coordSection φ k ≠ 0) :
    cycleClass (schemeSectionAnalyticDivisor g (m + 1) EV (originalMapHyperplaneAtlas φ) 1
      (coordSection φ k) hs) = algChern g EV m (mapLine φ) := by
  set H := schemeLineBundleMetric g (m + 1) EV (originalMapHyperplaneAtlas φ)
  rw [cycleClass_eq_of_isDivisorMetric _ _ (H.sectionMeteredDivisor_isDivisorMetric _ 1 _ hs),
    RealBottChern.ofRepresentative_eq_of_geometricallyEq (H.sectionMeteredDivisor_curvature _ 1 _ hs),
    Nat.cast_one, one_smul]
  rfl

/-- **The cycle class of a prime divisor of `V(ℂ)` is algebraic**: `cl(P) = c₁(L_G) − c₁(L_F)` for
algebraic line bundles `L_F = φ_F^*𝒪(1)`, `L_G = φ_G^*𝒪(1)` of `V`. -/
theorem cycleClass_prime_eq_sub (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) (SchemeComplexPoint g)) :
    ∃ A B : IntrinsicLineBundle V,
      cycleClass (SGPT.Siu.primeEffectiveDivisor P) = algChern g EV m A - algChern g EV m B := by
  classical
  obtain ⟨e, r, F, hFhom, hgen⟩ := exists_chow_family_prime g EV m P
  have hprime := exists_localFactorization_prime g EV m P F hgen
  have hlocF : ∀ z, ∃ i, ∃ D : LocalFactorization g EV (m + 1) F i, z ∈ D.Nb := fun z => by
    obtain ⟨i, D, hz, -, -⟩ := hprime z
    exact ⟨i, D, hz⟩
  obtain ⟨φF, hφF, hptF⟩ := exists_morphism_of_localFactorization g EV (m + 1) hFhom hlocF
  have hmapF : ∀ {i} (D : LocalFactorization g EV (m + 1) F i) (y) (hy : y ∈ D.Nb),
      schemeComplexPointMap g _ φF hφF y =
        polynomialProjNonzeroVectorPoint r ⟨fun k => D.u k y, D.ne y hy⟩ :=
    fun D y hy => (hptF y).trans (phiPoint_eq g EV (m + 1) hFhom hlocF D hy)
  -- a point off `P` where `u_{j₀} ≠ 0`
  obtain ⟨x, -⟩ := P.nonempty
  obtain ⟨i0, D0, hx0, -, -⟩ := hprime x
  obtain ⟨z0, hz0, hhz0⟩ := D0.dense D0.Nb D0.isOpen subset_rfl ⟨x, hx0⟩
  obtain ⟨j0, hj0⟩ := exists_ne_zero_of_ne_zero (D0.ne z0 hz0)
  -- the comparison family without base points
  let G : Fin (EV.ambientDimension + 1 + 1) → MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ :=
    Fin.cons (F j0) (fun l => MvPolynomial.X l ^ e)
  have hGhom : ∀ k, (G k).IsHomogeneous e := fun k => by
    refine Fin.cases ?_ (fun l => ?_) k
    · simpa [G] using hFhom j0
    · simpa [G] using MvPolynomial.isHomogeneous_X_pow l e
  have hGne : ∀ i y, schemeComplexPointImage g y ∈ coordOpen EV i →
      (fun k => MvPolynomial.eval (homCoords g EV (m + 1) i y) (G k)) ≠ 0 := by
    intro i y hy h0
    have := congrFun h0 (Fin.succ i)
    simp only [G, Fin.cons_succ, map_pow, MvPolynomial.eval_X, homCoords_self g EV (m + 1) i hy,
      one_pow, Pi.zero_apply] at this
    exact one_ne_zero this
  let DG := fun i => LocalFactorization.ofNoBase g EV m G i (hGne i)
  have hlocG : ∀ z, ∃ i, ∃ D : LocalFactorization g EV (m + 1) G i, z ∈ D.Nb :=
    fun z => ⟨frameIndex g EV z, DG _, mem_coordOpen_frameIndex g EV z⟩
  obtain ⟨φG, hφG, hptG⟩ := exists_morphism_of_localFactorization g EV (m + 1) hGhom hlocG
  have hmapG : ∀ i y (hy : y ∈ (DG i).Nb), schemeComplexPointMap g _ φG hφG y =
      polynomialProjNonzeroVectorPoint _ ⟨fun k => (DG i).u k y, (DG i).ne y hy⟩ :=
    fun i y hy => (hptG y).trans (phiPoint_eq g EV (m + 1) hGhom hlocG (DG i) hy)
  -- the two coordinate sections are nonzero
  have hσF : coordSection φF j0 ≠ 0 := by
    have h1 : schemeComplexPointImage _ (schemeComplexPointMap g _ φF hφF z0) ∈
        coordOpen (identityEmbedding r) j0 := by
      rw [hmapF D0 z0 hz0, polynomialProjNonzeroVectorPoint_eq_chart r _ j0 hj0]
      exact nativeVectorPoint_mem r j0 _ hj0
    exact coordSection_ne_zero (φ := φF) j0 (z := ⟨z0.1, by rw [hφF]; exact z0.2⟩) h1
  have hz0G : z0 ∈ (DG i0).Nb := D0.chart z0 hz0
  have hu0 : (DG i0).u 0 z0 ≠ 0 := by
    change MvPolynomial.eval (homCoords g EV (m + 1) i0 z0) (G 0) ≠ 0
    simp only [G, Fin.cons_zero]
    rw [D0.eq z0 hz0 j0]
    exact mul_ne_zero hhz0 hj0
  have hσG : coordSection φG 0 ≠ 0 := by
    have h1 : schemeComplexPointImage _ (schemeComplexPointMap g _ φG hφG z0) ∈
        coordOpen (identityEmbedding _) 0 := by
      rw [hmapG i0 z0 hz0G, polynomialProjNonzeroVectorPoint_eq_chart _ _ 0 hu0]
      exact nativeVectorPoint_mem _ 0 _ hu0
    exact coordSection_ne_zero (φ := φG) 0 (z := ⟨z0.1, by rw [hφG]; exact z0.2⟩) h1
  -- `div(φ_G^*y_0) = P + div(φ_F^*y_{j₀})`
  set DF := schemeSectionAnalyticDivisor g (m + 1) EV (originalMapHyperplaneAtlas φF) 1
    (coordSection φF j0) hσF
  set DGd := schemeSectionAnalyticDivisor g (m + 1) EV (originalMapHyperplaneAtlas φG) 1
    (coordSection φG 0) hσG
  have hdiv : DGd = GermIdealTotalTransform.EffectiveDivisor.add
      (SGPT.Siu.primeEffectiveDivisor P) DF := by
    apply effectiveDivisor_eq_of_ideal_eq
    refine GermIdeal.ext (funext fun y => funext fun f => propext ?_)
    obtain ⟨i, D, hy, hhol, hgenP⟩ := hprime y
    have hDF : ∀ f, DF.ideal.mem y f ↔ IsInSpanAt (n := m + 1) (· = D.u j0) y f :=
      fun f => coordSection_ideal_mem_of g EV m φF hφF j0 D.isOpen D.hol D.ne
        (fun y' hy' => hmapF D y' hy') hy f
    change DGd.ideal.mem y f ↔ ((SGPT.Siu.primeEffectiveDivisor P).ideal.mul DF.ideal).mem y f
    rw [MemberPullback.mul_mem_iff_of_generators (hgenP y hy) hDF (hhol y hy) (D.hol y hy j0) f]
    have hyG : y ∈ (DG i).Nb := D.chart y hy
    rw [show DGd.ideal = schemeSectionAnalyticIdeal g (m + 1) EV (originalMapHyperplaneAtlas φG) 1
      (coordSection φG 0) from rfl, coordSection_ideal_mem_of g EV m φG hφG 0 (DG i).isOpen
        (DG i).hol (DG i).ne (fun y' hy' => hmapG i y' hy') hyG f]
    refine isInSpanAt_eq_congr_unit (c := fun _ => 1) (holomorphicAt_const 1) one_ne_zero ?_ f
    filter_upwards [D.isOpen.mem_nhds hy] with y' hy'
    change MvPolynomial.eval (homCoords g EV (m + 1) i y') (G 0) = 1 * (D.h y' * D.u j0 y')
    simp only [G, Fin.cons_zero, one_mul]
    exact D.eq y' hy' j0
  have hcF := cycleClass_coordSection g EV m φF j0 hσF
  have hcG := cycleClass_coordSection g EV m φG 0 hσG
  have hadd := cycleClass_add m (SGPT.Siu.primeEffectiveDivisor P) DF
  refine ⟨mapLine φG, mapLine φF, ?_⟩
  rw [← hcG, ← hcF]
  change _ = cycleClass DGd - cycleClass DF
  rw [hdiv, hadd, add_sub_cancel_right]

/-- **Every class of the analytic Néron–Severi space of `V(ℂ)` is algebraic**: `NS(V(ℂ))_ℝ` is
the real span of the Chern classes of the algebraic line bundles of `V`. -/
theorem neronSeveri_eq_span_algChern :
    neronSeveri (m + 1) (SchemeComplexPoint g) =
      Submodule.span ℝ (range (algChern g EV m)) := by
  apply le_antisymm
  · rw [SGPT.Projective.BDivNov16.neronSeveri_eq_span_primeCycleClass, Submodule.span_le]
    rintro _ ⟨P, rfl⟩
    obtain ⟨A, B, h⟩ := cycleClass_prime_eq_sub g EV m P
    change cycleClass (SGPT.Siu.primeEffectiveDivisor P) ∈ _
    rw [h]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨A, rfl⟩) (Submodule.subset_span ⟨B, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨A, rfl⟩
    exact originalProjectiveLine_chern_mem_neronSeveri g (m + 1) EV A.atlas _

end SGPT.BDivisor.BD6
