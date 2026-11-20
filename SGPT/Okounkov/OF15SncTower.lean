import SGPT.Okounkov.OF13Tower

/-!
# A log resolution tower with its normal crossings divisor

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr` (a resolution `π : Y → X` carrying a
smooth flag `Y•` with `ν = ν_{Y•} g`) and `rmk:Abhyankar` (existence part of [CFKLRS17, Thm 2.9]).

Lane OF13 (`OF13.exists_tower_isLogResolutionGermAt`) constructs, for nonzero `u₁, …, u_r ∈ ℂ(X)`,
a blow-up tower `π : Y → X(ℂ)` on which the pull-backs of the `u_k` are, at every point, analytic
units times Laurent monomials in the local equations of the members of a simple normal crossings
divisor. Its statement forgets the divisor. To build *smooth* flags out of the members (lane OF15,
`rmk:valcurr`) the divisor `E` is kept here, and the monomial description holds **in every adapted
chart of `E`**:

* `exists_monomial_of_adaptedChart`: for an effective divisor `D` supported on a simple normal
  crossings divisor `E` and **any** adapted chart `Φ` of `E` at `y` (the members through `y` are the
  coordinate hyperplanes `{(Φ ∘ chart)ⱼ = 0}`, `j` with `S i = {j}`), `D` has a local generator at
  `y` all of whose divisors are units times monomials in the flat coordinates of `Φ`, with exponents
  only along the members through `y`;
* **`exists_tower_snc_monomial`**: the tower, its simple normal crossings divisor `E`, and at every
  `y` and in every adapted chart `Φ` of `E` at `y`: `π^* u_k = η_k ∏ⱼ ℓⱼ^{a_{kj}}` with `ℓ` the flat
  coordinates of `Φ`, `a_{kj} = 0` unless the `j`-th coordinate hyperplane is a member, and `π^* u_k`
  or `π^* u_k⁻¹` holomorphic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF15

open CategoryTheory AlgebraicGeometry Set Filter Metric IsLocalRing SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.NormalCrossings
open HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
open HironakaSmoothCentreRelativeIdeal BlowupFlatCoordinates
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.Okounkov.OF9 SGPT.Okounkov.OF13
open scoped Topology Manifold ContDiff

/-! ### Monomial charts in a given adapted chart -/

section Monomial

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- An **adapted chart** of the list `E` at `y`: holomorphic coordinates `Φ ∘ chart` centred at `y`
in which every member `E i` through `y` is the coordinate subspace of `S i`. -/
def IsAdaptedChart {E : List (Set Y)} (y : Y) (S : Fin E.length → Finset (Fin n))
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)) : Prop :=
  Φ.source ⊆ (complexChartAt (n := n) y).val.target ∧
    Φ.toFun ((complexChartAt (n := n) y).val y) = 0 ∧
    (∀ i, y ∈ E.get i → ∀ {z : Y}, z ∈ (complexChartAt (n := n) y).val.source →
      (complexChartAt (n := n) y).val z ∈ Φ.source →
        (z ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) y).val z) ∈ coordSubspace (S i))) ∧
    (∀ i, y ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | y ∈ E.get i}

/-- The germ of the `j`-th flat coordinate of an adapted chart. -/
abbrev flatGerm {y : Y} (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (j : Fin n) : NativeHolGerm n Y y :=
  NativeHolGerm.mk (flatCoord Φ j) (holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ))

/-- **The monomial chart of a principalized divisor, in a given adapted chart.** Let `D` be an
effective divisor whose support lies in a simple normal crossings divisor `E`, and `Φ` an adapted
chart of `E` at `y`. Then `D` has a local generator `g` at `y` every divisor of whose germ is a unit
times a monomial `∏ⱼ ℓⱼ^{αⱼ}` in the flat coordinates `ℓ` of `Φ`, with `αⱼ = 0` unless the `j`-th
coordinate hyperplane is a member of `E` through `y`. -/
theorem exists_monomial_of_adaptedChart (D : EffectiveDivisor n Y) {E : List (Set Y)}
    (hE : IsSNCDivisor n E) (hsupp : D.support ⊆ ⋃ H ∈ E, H) (y : Y)
    (S : Fin E.length → Finset (Fin n))
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hΦ : IsAdaptedChart y S Φ) :
    ∃ (g : Y → ℂ) (hg : HolomorphicAt n g y),
      (∀ f, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      ∀ c : NativeHolGerm n Y y, c ∣ NativeHolGerm.mk g hg →
        ∃ (η : (NativeHolGerm n Y y)ˣ) (α : Fin n → ℕ),
          (∀ j, (¬ ∃ i, y ∈ E.get i ∧ S i = {j}) → α j = 0) ∧
          c = η * ∏ j, (flatGerm Φ j) ^ (α j) := by
  classical
  obtain ⟨hsrc, h0, hflat, hcard, -⟩ := hΦ
  obtain ⟨U, hU, hyU, g, hgd, -, hgen, -, -, -, a, H₀, hH₀, hH₀0, hfac⟩ :=
    SNCSupportedDivisorFixedChartNormalForm.exists_unit_monomial_generator_in_adapted_coordinates
      D E hE hsupp y S Φ hsrc h0 hcard hflat
  let M : Finset (Fin n) := Finset.univ.filter fun j => ∃ i, y ∈ E.get i ∧ S i = {j}
  have hg : HolomorphicAt n g y :=
    SGPT.PSH.IdealRestriction.holomorphicAt_of_mdifferentiableOn hU hgd hyU
  -- the generator in adapted coordinates
  have hθg : flatGermEquiv Φ h0 (NativeHolGerm.mk g hg) =
      HolGerm.mk H₀ hH₀ * ∏ j, coordinateGerm j ^ a j := by
    apply Subtype.ext
    rw [coe_flatGermEquiv_mk, coe_holGerm_unit_monomial]
    exact Germ.coe_eq.mpr hfac
  -- exponents vanish off the members through `y`
  have hT : Tendsto (fun u => (complexChartAt (n := n) y).val.symm (Φ.invFun u)) (𝓝 0) (𝓝 y) := by
    have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
    rwa [show Φ.toFun ((chartAt (ComplexModel n) y) y) = 0 from h0] at h
  have havoid : ∀ᶠ y' in 𝓝 y, ∀ i : Fin E.length, y ∉ E.get i → y' ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hyi : y ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hyi).elim
    · have hi : ∀ᶠ y' in 𝓝 y, y' ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hyi
      exact hi.mono fun _ hy _ => hy
  have hzeroM : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      H₀ z * ∏ j : Fin n, z j ^ a j = 0 → ∃ j ∈ M, z j = 0 := by
    filter_upwards [hfac, Φ.isOpen_target.mem_nhds (zero_mem_target Φ h0),
      hT.eventually (hU.mem_nhds hyU), hT.eventually havoid] with z hz hzT hzU hzav hz0
    rw [← hz] at hz0
    obtain ⟨hdom, hback⟩ := flatInverse_mem Φ hzT hsrc
    set y' := (complexChartAt (n := n) y).val.symm (Φ.invFun z)
    have hsup : y' ∈ D.support :=
      (SNCDivisorLocalGenerator.mem_support_iff_generator_eq_zero D
        (SGPT.PSH.IdealRestriction.holomorphicAt_of_mdifferentiableOn hU hgd hzU)
        (hgen y' hzU)).mpr hz0
    obtain ⟨F, hF⟩ := mem_iUnion.mp (hsupp hsup)
    obtain ⟨hFE, hyF⟩ := mem_iUnion.mp hF
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hFE
    have hyi : y ∈ E.get i := by
      by_contra h
      exact hzav i h hyF
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hcard i hyi)
    have hsub := (hflat i hyi hdom.1 hdom.2).mp hyF
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hyi, hj⟩, ?_⟩
    have hb := congrArg (fun w : ComplexModel n => w j) hback
    simp only at hb
    have h1 := hsub j (by rw [hj]; exact Finset.mem_singleton_self j)
    erw [hb] at h1
    exact h1
  have haM : ∀ j ∉ M, a j = 0 := by
    intro j hj
    by_contra hne
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hzeroM
    obtain ⟨z, hz, hzj, hzi⟩ := HironakaDivisorResidualUnit.exists_coordinate_unit_point j hε
    obtain ⟨j', hj'M, hj'⟩ := hball z hz (by
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hzj]; exact zero_pow hne), mul_zero])
    by_cases hjj : j' = j
    · exact hj (hjj ▸ hj'M)
    · exact hzi j' hjj hj'
  refine ⟨g, hg, hgen y hyU, fun c hc => ?_⟩
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  have hunit : IsUnit (HolGerm.mk H₀ hH₀) :=
    (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa [HolGerm.eval_mk] using hH₀0)
  have hdvd : flatGermEquiv Φ h0 c ∣ ∏ j, coordinateGerm j ^ a j := by
    have h1 := map_dvd (flatGermEquiv Φ h0) hc
    rw [hθg] at h1
    exact (hunit.dvd_mul_left).mp h1
  obtain ⟨α, hαa, hassoc⟩ :=
    HolomorphicCoordinateFactorization.exists_associated_prod_pow_of_dvd_prod_pow
      (fun j => coordinateGerm j) a
      (fun j => HolomorphicCoordinatePrime.prime_coordinate_germ j) hdvd
  obtain ⟨v, hv⟩ := hassoc.symm
  refine ⟨(Units.map (flatGermEquiv Φ h0).symm.toMonoidHom v), α,
    fun j hj => Nat.eq_zero_of_le_zero ((hαa j).trans (haM j (fun hjM => hj
      (Finset.mem_filter.mp hjM).2)).le), ?_⟩
  apply (flatGermEquiv Φ h0).injective
  rw [map_mul, map_prod, ← hv]
  have h1 : (flatGermEquiv Φ h0) ((Units.map (flatGermEquiv Φ h0).symm.toMonoidHom v :
      (NativeHolGerm n Y y)ˣ) : NativeHolGerm n Y y) = v := by simp
  rw [h1, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_pow]
  exact congrArg (· ^ α j) (flatGermEquiv_flatCoord Φ h0 hsrc j).symm

omit [IsComplexManifold n Y] in
/-- Every simple normal crossings divisor has an adapted chart at every point. -/
theorem exists_isAdaptedChart {E : List (Set Y)} (hE : IsSNCDivisor n E) (y : Y) :
    ∃ (S : Fin E.length → Finset (Fin n))
      (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)),
      IsAdaptedChart y S Φ := by
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, hinj⟩ := hE.2 y
  exact ⟨S, Φ, hsrc, h0, hflat, hcard, hinj⟩

end Monomial

/-! ### The tower -/

section Tower

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of15tTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of15tCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of15tManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **An analytic log resolution tower together with its normal crossings divisor.** For an
integral smooth projective complex scheme `X` and nonzero `u₁, …, u_r ∈ ℂ(X)` there are a blow-up
tower `π : Y → X(ℂ)` and a simple normal crossings divisor `E` on `Y` such that at every `y ∈ Y`
and in every adapted chart `Φ` of `E` at `y` (flat coordinates `ℓ`), the pull-back `π^* u_k`
(the `ratGerm`) is `η_k ∏ⱼ ℓⱼ^{a_{kj}}` with `η_k` a unit and `a_{kj} = 0` unless the `j`-th
coordinate hyperplane is a member of `E` through `y`, and `π^* u_k` or `π^* u_k⁻¹` is
holomorphic at `y`. -/
theorem exists_tower_snc_monomial (E : ClosedProjectiveEmbedding f) {r : ℕ}
    (u : Fin r → X.functionField) (hu : ∀ k, u k ≠ 0) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → SchemeComplexPoint f)
      (hseq : IsBlowupSequence n (SchemeComplexPoint f) Y π) (E' : List (Set Y)),
      IsSNCDivisor n E' ∧
      ∀ (y : Y) (S : Fin E'.length → Finset (Fin n))
        (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)),
        IsAdaptedChart y S Φ →
        ∃ (η : Fin r → (NativeHolGerm n Y y)ˣ) (a : Fin r → Fin n → ℤ),
          (∀ k j, (¬ ∃ i, y ∈ E'.get i ∧ S i = {j}) → a k j = 0) ∧
          (∀ k, ratGerm f (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) y
              (u k) =
            algebraMap _ (FractionRing (NativeHolGerm n Y y)) (η k : NativeHolGerm n Y y) *
              ∏ j, (algebraMap _ (FractionRing (NativeHolGerm n Y y)) (flatGerm Φ j)) ^ (a k j)) ∧
          ∀ k, (∃ h : NativeHolGerm n Y y,
              ratGerm f (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) y
                (u k) = algebraMap _ (FractionRing (NativeHolGerm n Y y)) h) ∨
            ∃ h : NativeHolGerm n Y y,
              (ratGerm f (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) y
                (u k))⁻¹ = algebraMap _ (FractionRing (NativeHolGerm n Y y)) h := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let Ψ := projectivePoint f E n
  have hΨ : IsHolomorphicEmbedding (n := n) Ψ := isHolomorphicEmbedding_projectivePoint f E n
  -- numerators and denominators
  have hrat := fun k => exists_homogeneous_ratio f E (u k)
  choose d P Q hP hQ hPQ using hrat
  have hgermFF : ∀ (x : SchemeComplexPoint f) (i : Fin (E.ambientDimension + 1))
      (hi : Ψ x ∈ (affineChart i).source) (A : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ),
      schemeNativeFunctionFieldGerm f n x
          (polyFF f E i (genericPoint_mem_coordOpen f E
            ((projectivePoint_mem_source_iff f E n i x).mp hi)) A) =
        algebraMap _ _ (polyGerm hΨ hi A) := fun x i hi A =>
    schemeNativeFunctionFieldGerm_polyFF f E i _ A x hi
  have hratio : ∀ (x : SchemeComplexPoint f) (i : Fin (E.ambientDimension + 1))
      (hi : Ψ x ∈ (affineChart i).source) (k : Fin r),
      polyGerm hΨ hi (Q k) ≠ 0 ∧ polyGerm hΨ hi (P k) ≠ 0 ∧
      schemeNativeFunctionFieldGerm f n x (u k) * algebraMap _ _ (polyGerm hΨ hi (Q k)) =
        algebraMap _ _ (polyGerm hΨ hi (P k)) := by
    intro x i hi k
    have hgi := genericPoint_mem_coordOpen f E ((projectivePoint_mem_source_iff f E n i x).mp hi)
    obtain ⟨hQ0, heq⟩ := hPQ k i hgi
    have hP0 : polyFF f E i hgi (P k) ≠ 0 := by
      rw [← heq]
      exact mul_ne_zero (hu k) hQ0
    have hinjF := schemeNativeFunctionFieldGerm_injective f n x
    refine ⟨fun h0 => hQ0 (hinjF ?_), fun h0 => hP0 (hinjF ?_), ?_⟩
    · rw [hgermFF x i hi, h0, map_zero, map_zero]
    · rw [hgermFF x i hi, h0, map_zero, map_zero]
    · rw [← hgermFF x i hi, ← hgermFF x i hi, ← map_mul, heq]
  -- principalization
  obtain ⟨Y, tY, cY, mY, π, hseq, D, E', hsnc, hsupp, hmain⟩ :=
    exists_principalization_ratios hΨ P Q d hP hQ fun x i hi k =>
      ⟨(hratio x i hi k).2.1, (hratio x i hi k).1⟩
  refine ⟨Y, tY, cY, mY, π, hseq, E', hsnc, fun y S Φ hΦ => ?_⟩
  set hmod := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
  obtain ⟨gD, hgD, hgen, hmono⟩ := exists_monomial_of_adaptedChart D hsnc hsupp.le y S Φ hΦ
  obtain ⟨i, hi⟩ := exists_mem_affineChart_source (Ψ (π y))
  obtain ⟨-, hk⟩ := hmain y i hi gD hgD hgen
  let p : Fin r → NativeHolGerm n Y y := fun k => pullGerm hΨ hmod.1 hi (P k)
  let q : Fin r → NativeHolGerm n Y y := fun k => pullGerm hΨ hmod.1 hi (Q k)
  have hpm := fun k => hmono (p k) (hk k).2.2.2.1
  have hqm := fun k => hmono (q k) (hk k).2.2.2.2
  choose ηp α hαM hpα using hpm
  choose ηq β hβM hqβ using hqm
  let L := FractionRing (NativeHolGerm n Y y)
  let w : Fin n → NativeHolGerm n Y y := fun j => flatGerm Φ j
  have hγ : ∀ k, ratGerm f hmod y (u k) * algebraMap _ L (q k) = algebraMap _ L (p k) := by
    intro k
    have h := congrArg (fracComap hmod y) (hratio (π y) i hi k).2.2
    rw [map_mul, fracComap_algebraMap, fracComap_algebraMap] at h
    exact h
  have hqL : ∀ k, algebraMap _ L (q k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (hk k).2.1
  have hpL : ∀ k, algebraMap _ L (p k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (hk k).1
  have hspan : Ideal.span (Set.range w) = maximalIdeal (NativeHolGerm n Y y) :=
    span_flatCoord_eq_maximalIdeal Φ hΦ.2.1 hΦ.1
  have hcoordH : Ideal.span (Set.range fun j => NativeHolGerm.chartEquiv y (w j)) =
      maximalIdeal (HolGerm (ComplexModel n)) := by
    have h := congrArg (Ideal.map (NativeHolGerm.chartEquiv (n := n) y)) hspan
    rw [Ideal.map_span, IsLocalRing.map_ringEquiv_maximalIdeal, ← Set.range_comp] at h
    exact h
  obtain ⟨v, hv⟩ := dualVectors_of_span_eq _ hcoordH
  have hw0 : ∀ j, w j ≠ 0 := fun j h => by
    have h1 := hv j j
    change germDeriv (v j) (NativeHolGerm.chartEquiv y (w j)) = _ at h1
    rw [h, map_zero, germDeriv_zero, if_pos rfl] at h1
    exact zero_ne_one h1
  have hwL : ∀ j, algebraMap _ L (w j) ≠ 0 := fun j =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (hw0 j)
  have hratio' : ∀ k, ratGerm f hmod y (u k) = algebraMap _ L (p k) / algebraMap _ L (q k) :=
    fun k => (eq_div_iff (hqL k)).mpr (hγ k)
  refine ⟨fun k => ηp k * (ηq k)⁻¹, fun k j => (α k j : ℤ) - β k j, fun k j hj => by
      show (α k j : ℤ) - β k j = 0
      rw [hαM k j hj, hβM k j hj]
      simp,
    fun k => ?_, fun k => ?_⟩
  · rw [hratio' k]
    have hp' : algebraMap _ L (p k) =
        algebraMap _ L (ηp k : NativeHolGerm n Y y) * ∏ j, algebraMap _ L (w j) ^ α k j := by
      rw [hpα k, map_mul, map_prod]
      simp only [map_pow]
      rfl
    have hq' : algebraMap _ L (q k) =
        algebraMap _ L (ηq k : NativeHolGerm n Y y) * ∏ j, algebraMap _ L (w j) ^ β k j := by
      rw [hqβ k, map_mul, map_prod]
      simp only [map_pow]
      rfl
    rw [hp', hq', Units.val_mul, map_mul, map_units_inv]
    change _ = _ * _ * ∏ j, algebraMap _ L (w j) ^ ((α k j : ℤ) - β k j)
    simp_rw [zpow_sub₀ (hwL _), zpow_natCast]
    rw [Finset.prod_div_distrib, mul_div_mul_comm, div_eq_mul_inv]
  · rcases (hk k).2.2.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · right
      refine ⟨c, ?_⟩
      have hc' : q k = p k * c := hc
      rw [hratio' k, inv_div, hc', map_mul, mul_div_cancel_left₀ _ (hpL k)]
    · left
      refine ⟨c, ?_⟩
      have hc' : p k = q k * c := hc
      rw [hratio' k, hc', map_mul, mul_div_cancel_left₀ _ (hqL k)]

end Tower

end SGPT.Okounkov.OF15
