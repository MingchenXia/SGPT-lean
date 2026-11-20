import SGPT.NAPotential.AlgPrimes2Normal
import SGPT.NAPotential.AlgPrimes2Smooth
import SGPT.GAGA.H0SSchemeJacobian

/-!
# A smooth point of a prime divisor of a smooth complex scheme


Let `X` be an integral scheme, smooth of relative dimension `n` over `ℂ`, and `z ∈ X` a point of
codimension one (the generic point of a prime divisor `Z = {z}‾`).  This file finds an affine
open `V ∋ z` with a submersive presentation of `Γ(V, 𝒪_X)`, a local equation `u` of `Z` on `V`
(`s 𝔮 ⊆ (u)` for some `s ∉ 𝔮`, `𝔮` the prime of `z`, and the germ of `u` a uniformizer of the
discrete valuation ring `𝒪_{X,z}`), and a complex point `y ∈ Z ∩ D(s)` at which the analytic
germ of `u` has a nonzero derivative (`exists_regular_point`).  The analytic input is the
Taylor expansion at complex points (`SGPT.Okounkov.schemeNativeFormalGerm`, injective) and the
tangent derivations `germDeriv v` of the preferred chart, faithful on `𝒪_{X,y}` because the
chart coordinates are regular functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes2

open AlgebraicGeometry CategoryTheory Topology IsLocalRing Opposite
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.Berkovich SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation

/-! ### Affine opens: specialization and closed points -/

section Affine

variable {X : Scheme.{0}}

/-- On an affine open, `z ⤳ x` iff the prime of `z` is contained in the prime of `x`. -/
theorem specializes_iff_primeIdealOf_le {V : X.Opens} (hV : IsAffineOpen V) {x z : X}
    (hx : x ∈ V) (hz : z ∈ V) :
    z ⤳ x ↔ (hV.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  change z ⤳ x ↔ hV.primeIdealOf ⟨z, hz⟩ ≤ hV.primeIdealOf ⟨x, hx⟩
  rw [PrimeSpectrum.le_iff_specializes]
  constructor
  · intro h
    have h1 : (⟨z, hz⟩ : V) ⤳ ⟨x, hx⟩ := by
      exact Topology.IsInducing.subtypeVal.specializes_iff.mp h
    exact h1.map hV.isoSpec.hom.continuous
  · intro h
    have h2 := h.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at h2

/-- The germ at `fromSpec 𝔪` of a section lies in the maximal ideal iff the section lies in `𝔪`. -/
theorem germ_mem_maximalIdeal_iff {V : X.Opens} (hV : IsAffineOpen V) (𝔪 : PrimeSpectrum Γ(X, V))
    (a : Γ(X, V)) {x : X} (hx : x ∈ V) (h𝔪x : hV.fromSpec 𝔪 = x) :
    X.presheaf.germ V x hx a ∈ maximalIdeal (X.presheaf.stalk x) ↔ a ∈ 𝔪.asIdeal := by
  subst h𝔪x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hV.fromSpec 𝔪, hx⟩
  have := hV.isLocalization_stalk' 𝔪 hx
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (hV.fromSpec 𝔪))
    𝔪.asIdeal a

end Affine

/-! ### A local equation of a prime divisor -/

section Equation

variable {X : Scheme.{0}} [IsIntegral X]

/-- **Local equation of a prime divisor.**  If `𝒪_{X,z}` is a discrete valuation ring and `V` an
affine open containing `z` with Noetherian ring, there are `u ∈ 𝔮` whose germ at `z` is a
uniformizer and `s ∉ 𝔮` with `s 𝔮 ⊆ (u)` (`𝔮` the prime of `z`). -/
theorem exists_local_equation {V : X.Opens} (hV : IsAffineOpen V) {z : X} (hzV : z ∈ V)
    [IsNoetherianRing Γ(X, V)] [IsDiscreteValuationRing (X.presheaf.stalk z)] :
    ∃ u s : Γ(X, V), u ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ∧
      s ∉ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ∧
      (∀ a ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal, s * a ∈ Ideal.span {u}) ∧
      Irreducible (X.presheaf.germ V z hzV u) := by
  classical
  set 𝔮 := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with h𝔮
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk z) 𝔮 := hV.isLocalization_stalk ⟨z, hzV⟩
  have halg : ∀ a, algebraMap Γ(X, V) (X.presheaf.stalk z) a = X.presheaf.germ V z hzV a :=
    fun _ => rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  obtain ⟨⟨u, w⟩, hw⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl ϖ
  have hwunit : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk z) w) :=
    IsLocalization.map_units _ w
  have hu_eq : algebraMap Γ(X, V) (X.presheaf.stalk z) u =
      ϖ * algebraMap Γ(X, V) (X.presheaf.stalk z) w := by
    rw [← hw, IsLocalization.mk'_spec]
  have hirr : Irreducible (X.presheaf.germ V z hzV u) := by
    rw [← halg, hu_eq]
    exact (irreducible_mul_isUnit hwunit).mpr hϖ
  have hmax : maximalIdeal (X.presheaf.stalk z) =
      Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk z) u} := by
    rw [halg]
    exact (Irreducible.maximalIdeal_eq hirr)
  have hu𝔮 : u ∈ 𝔮 := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z) 𝔮 u, hmax]
    exact Ideal.mem_span_singleton_self _
  -- one denominator for a finite generating set of `𝔮`
  have hfg : 𝔮.FG := IsNoetherian.noetherian 𝔮
  obtain ⟨G, hG⟩ := hfg
  have hden : ∀ q ∈ 𝔮, ∃ t ∉ 𝔮, t * q ∈ Ideal.span {u} := by
    intro q hq
    have hq' : algebraMap Γ(X, V) (X.presheaf.stalk z) q ∈ maximalIdeal (X.presheaf.stalk z) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z) 𝔮 q).mpr hq
    rw [hmax] at hq'
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hq'
    obtain ⟨⟨a, w'⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
    have h1 : algebraMap Γ(X, V) (X.presheaf.stalk z) (q * w') =
        algebraMap Γ(X, V) (X.presheaf.stalk z) (a * u) := by
      rw [map_mul, ← hx, mul_right_comm, IsLocalization.mk'_spec, map_mul]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔮.primeCompl (X.presheaf.stalk z)).mp h1
    refine ⟨c * w', ?_, ?_⟩
    · exact 𝔮.primeCompl.mul_mem c.2 w'.2
    · refine Ideal.mem_span_singleton'.mpr ⟨c * a, ?_⟩
      calc c * a * u = c * (a * u) := by ring
        _ = c * (q * w') := hc.symm
        _ = ↑c * ↑w' * q := by ring
  choose! t ht𝔮 htq using hden
  refine ⟨u, ∏ q ∈ G, t q, hu𝔮, ?_, ?_, hirr⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨q, hqG, hq⟩
    exact ht𝔮 q (hG ▸ Ideal.subset_span hqG) hq
  · intro a ha
    rw [← hG] at ha
    refine Submodule.span_induction (fun q hqG => ?_) ?_ (fun x y _ _ hx hy => ?_)
      (fun r x _ hx => ?_) ha
    · have hq : q ∈ 𝔮 := hG ▸ Ideal.subset_span hqG
      rw [← Finset.prod_erase_mul _ _ hqG, mul_assoc]
      exact Ideal.mul_mem_left _ _ (htq q hq)
    · rw [mul_zero]; exact Ideal.zero_mem _
    · rw [mul_add]; exact Ideal.add_mem _ hx hy
    · rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx

end Equation

/-! ### The smooth point -/

section Point

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f] [IsIntegral X]

local instance algPrimes2PointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimes2PointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance algPrimes2PointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] [IsIntegral X] in
/-- The `ℂ`-algebra structure on the sections over `V` induced by `f`. -/
@[instance_reducible] def sectionAlgebra (V : X.Opens) : Algebra ℂ Γ(X, V) :=
  ((schemeConstantPresheafMap f).app (op V)).hom.toAlgebra

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] [IsIntegral X] in
/-- The germ of a constant section is the germ of the global constant. -/
theorem germ_sectionAlgebra (V : X.Opens) (c : ℂ) {x : X} (hx : x ∈ V) :
    X.presheaf.germ V x hx (@algebraMap ℂ Γ(X, V) _ _ (sectionAlgebra f V) c) =
      X.presheaf.germ ⊤ x trivial (schemeGlobalConstants f c) := by
  have h := X.presheaf.germ_res_apply (homOfLE (le_top : V ≤ ⊤)) x hx (schemeGlobalConstants f c)
  exact h

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] [IsIntegral X] in
/-- On an affine open, the point of `fromSpec 𝔪` has prime `𝔪`. -/
theorem primeIdealOf_eq_of_fromSpec_eq {V : X.Opens} (hV : IsAffineOpen V)
    (𝔪 : PrimeSpectrum Γ(X, V)) {x : X} (hx : x ∈ V) (h : hV.fromSpec 𝔪 = x) :
    hV.primeIdealOf ⟨x, hx⟩ = 𝔪 := by
  apply hV.fromSpec.isOpenEmbedding.injective
  rw [hV.fromSpec_primeIdealOf, h]

omit [IsSeparated f] [QuasiCompact f] [IsIntegral X] in
/-- Every element of the local ring at the point of a prime `𝔪` of an affine open is a quotient
of sections with denominator outside `𝔪`. -/
theorem exists_germ_mul_eq {V : X.Opens} (hV : IsAffineOpen V) (𝔪 : PrimeSpectrum Γ(X, V))
    {x : X} (hx : x ∈ V) (h𝔪x : hV.fromSpec 𝔪 = x) (r : X.presheaf.stalk x) :
    ∃ a t : Γ(X, V), t ∉ 𝔪.asIdeal ∧ r * X.presheaf.germ V x hx t = X.presheaf.germ V x hx a := by
  subst h𝔪x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hV.fromSpec 𝔪, hx⟩
  have := hV.isLocalization_stalk' 𝔪 hx
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.asIdeal.primeCompl r
  exact ⟨a, t, t.2, IsLocalization.mk'_spec _ a t⟩

/-- **A smooth point of a prime divisor.**  Let `z` be a point of codimension one of the smooth
integral complex scheme `X`.  There are an affine open `V ∋ z`, a local equation `u` of
`{z}‾` on `V` (`u ∈ 𝔮`, `s 𝔮 ⊆ (u)` with `s ∉ 𝔮`, `𝔮` the prime of `z`, the germ of `u` a
uniformizer of `𝒪_{X,z}`) and a complex point `y` of `{z}‾ ∩ D(s)` at which the analytic germ of
`u` has a nonzero derivative in some direction `v` of the preferred chart. -/
theorem exists_regular_point [IsLocallyNoetherian X] {z : X} (hz : Order.coheight z = 1) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hzV : z ∈ V) (u s : Γ(X, V)),
      u ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ∧ s ∉ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ∧
      (∀ a ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal, s * a ∈ Ideal.span {u}) ∧
      Irreducible (X.presheaf.germ V z hzV u) ∧
      ∃ (y : SchemeComplexPoint f) (hy : schemeComplexPointImage f y ∈ V),
        z ⤳ schemeComplexPointImage f y ∧
        s ∉ (hV.primeIdealOf ⟨schemeComplexPointImage f y, hy⟩).asIdeal ∧
        ∃ v : ComplexModel n, germDeriv v (stalkToModel f n y
          (X.presheaf.germ V (schemeComplexPointImage f y) hy u)) ≠ 0 := by
  classical
  obtain ⟨V, hV, hzV, hsm⟩ := smooth_cotangent_affine_chart f n z
  let := sectionAlgebra f V
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(X, V) := hsm
  have : Algebra.IsStandardSmooth ℂ Γ(X, V) := hstd.isStandardSmooth
  obtain ⟨ι, σ, _, _, P, hP⟩ := hstd.out
  have : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : IsJacobsonRing Γ(X, V) := isJacobsonRing_of_finiteType (A := ℂ)
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have : IsDiscreteValuationRing (X.presheaf.stalk z) := isDiscreteValuationRing_stalk f n hz
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : LocallyOfFiniteType f := inferInstance
  set 𝔮 := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with h𝔮
  obtain ⟨u, s, hu, hs𝔮, hsq, hirr⟩ := exists_local_equation hV hzV
  have hu0 : u ≠ 0 := fun h => hirr.ne_zero (by rw [h, map_zero])
  -- the complex point of each maximal ideal
  have hpt : ∀ (𝔪 : Ideal Γ(X, V)) (h𝔪 : 𝔪.IsMaximal), ∃ y : SchemeComplexPoint f,
      schemeComplexPointImage f y = hV.fromSpec ⟨𝔪, h𝔪.isPrime⟩ :=
    fun 𝔪 h𝔪 => exists_schemeComplexPoint_fromSpec f hV 𝔪 h𝔪
  choose yof hyof using hpt
  have hmemV : ∀ 𝔪 h, schemeComplexPointImage f (yof 𝔪 h) ∈ V := fun 𝔪 h => by
    rw [hyof]; exact fromSpec_mem hV _
  -- values and germs at these points
  have heval : ∀ (𝔪 : Ideal Γ(X, V)) (h : 𝔪.IsMaximal) (a : Γ(X, V)),
      pointEval f n (yof 𝔪 h) (X.presheaf.germ V _ (hmemV 𝔪 h) a) = 0 ↔ a ∈ 𝔪 := by
    intro 𝔪 h a
    rw [pointEval_eq_zero_iff, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact germ_mem_maximalIdeal_iff hV ⟨𝔪, h.isPrime⟩ a (hmemV 𝔪 h) (hyof 𝔪 h).symm
  have hconst : ∀ (y : SchemeComplexPoint f) (hy : schemeComplexPointImage f y ∈ V) (c : ℂ),
      stalkToModel f n y (X.presheaf.germ V _ hy (algebraMap ℂ Γ(X, V) c)) =
        algebraMap ℂ (HolGerm (ComplexModel n)) c := by
    intro y hy c
    rw [germ_sectionAlgebra f V c hy, stalkToModel_constants]
  -- the Taylor maps
  let θ : ∀ 𝔪 : Ideal Γ(X, V), 𝔪.IsMaximal → 𝔮 ≤ 𝔪 → s ∉ 𝔪 →
      Γ(X, V) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ := fun 𝔪 h _ _ =>
    { toRingHom := (schemeNativeFormalGerm f n (yof 𝔪 h)).comp
        (X.presheaf.germ V _ (hmemV 𝔪 h)).hom
      commutes' := fun c => by
        change HironakaActualCoefficientPresentationCentrePower.actualUnshiftedTaylorAlgHom n
          (stalkToModel f n (yof 𝔪 h) (X.presheaf.germ V _ (hmemV 𝔪 h) (algebraMap ℂ _ c))) = _
        rw [hconst]
        exact (HironakaActualCoefficientPresentationCentrePower.actualUnshiftedTaylorAlgHom
          n).commutes c }
  have hθinj : ∀ 𝔪 h₁ h₂ h₃, Function.Injective (θ 𝔪 h₁ h₂ h₃) := by
    intro 𝔪 h₁ h₂ h₃
    exact (schemeNativeFormalGerm_faithfullyFlat f n (yof 𝔪 h₁)).injective.comp
      (germ_injective_of_isIntegral X _ (hmemV 𝔪 h₁))
  have hθ0 : ∀ 𝔪 h₁ h₂ h₃ a, MvPowerSeries.constantCoeff (θ 𝔪 h₁ h₂ h₃ a) = 0 ↔ a ∈ 𝔪 := by
    intro 𝔪 h₁ h₂ h₃ a
    change MvPowerSeries.constantCoeff (schemeNativeFormalGerm f n (yof 𝔪 h₁)
      (X.presheaf.germ V _ (hmemV 𝔪 h₁) a)) = 0 ↔ _
    rw [schemeNativeFormalGerm_constantCoeff, ← schemeNativeStalkGerm_eval (f := f) (n := n)]
    exact heval 𝔪 h₁ a
  obtain ⟨𝔪, h𝔪, h𝔮𝔪, hs𝔪, k₀, hk₀⟩ :=
    exists_maximal_partialDeriv_notMem P hu0 hu hs𝔮 hsq θ hθinj hθ0
  set y := yof 𝔪 h𝔪 with hydef
  have hyV : schemeComplexPointImage f y ∈ V := hmemV 𝔪 h𝔪
  have hprime : hV.primeIdealOf ⟨schemeComplexPointImage f y, hyV⟩ = ⟨𝔪, h𝔪.isPrime⟩ :=
    primeIdealOf_eq_of_fromSpec_eq hV _ hyV (hyof 𝔪 h𝔪).symm
  -- the point derivations at `y`
  let ev : Γ(X, V) →ₐ[ℂ] ℂ :=
    { toRingHom := (pointEval f n y).comp (X.presheaf.germ V _ hyV).hom
      commutes' := fun c => by
        change pointEval f n y (X.presheaf.germ V _ hyV (algebraMap ℂ _ c)) = c
        rw [germ_sectionAlgebra f V c hyV, pointEval_germ_const] }
  let F : (Fin n → ℂ) → Γ(X, V) → ℂ := fun v a =>
    germDeriv (WithLp.toLp 2 v) (stalkToModel f n y (X.presheaf.germ V _ hyV a))
  have hgd : ∀ (v : Fin n → ℂ) (h : HolGerm (ComplexModel n)),
      germDeriv (WithLp.toLp 2 v) h = ∑ j, v j * HolGerm.eval (coordinatePartial j h) :=
    fun _ _ => rfl
  obtain ⟨v, hv⟩ := exists_pointDerivation_ne_zero P ev F
    (fun v a b => by simp only [F, map_add, germDeriv_add])
    (fun v a b => by
      simp only [F, map_mul, germDeriv_mul, holGermEval_stalkToModel]
      rfl)
    (fun v c => by simp only [F]; rw [hconst, germDeriv_algebraMap])
    (fun v w a => by
      simp only [F, hgd, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c v a => by
      simp only [F, hgd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun v hv => by
      set w : ComplexModel n := WithLp.toLp 2 v
      have hall : ∀ r, r ∈ tangentKernel f n y w := by
        intro r
        obtain ⟨a, t, ht, hrt⟩ := exists_germ_mul_eq hV ⟨𝔪, h𝔪.isPrime⟩ hyV (hyof 𝔪 h𝔪).symm r
        have htunit : IsUnit (X.presheaf.germ V _ hyV t) := by
          by_contra hnu
          have : X.presheaf.germ V _ hyV t ∈ maximalIdeal (X.presheaf.stalk _) := hnu
          exact ht ((germ_mem_maximalIdeal_iff hV ⟨𝔪, h𝔪.isPrime⟩ t hyV
            (hyof 𝔪 h𝔪).symm).mp this)
        refine tangentKernel_div f n y w r _ (hv t) htunit ?_
        rw [hrt]
        exact hv a
      ext j
      have hj := hall (schemeCoordinateStalkEquiv f n y
        (algebraMap (SchemeCoordinateAffineRing f n y) (SchemeCoordinateLocalRing f n y)
          (standardSmoothComplexChartFreeGenerator f n y j)))
      rw [mem_tangentKernel, stalkToModel_regular, schemeCoordinateModelRegularAlgHom_freeGenerator,
        germDeriv_add, germDeriv_coordinateGerm] at hj
      have hc : germDeriv w (HolGerm.constHom (standardSmoothComplexAlgebraPoint f n y
          (standardSmoothComplexChartFreeGenerator f n y j)) : HolGerm (ComplexModel n)) = 0 :=
        germDeriv_algebraMap w _
      rw [hc, add_zero] at hj
      simpa [w] using hj)
    (by rw [Fintype.card_congr (submersiveFreeIndexEquiv P), Fintype.card_fin, hP])
    (by
      change pointEval f n y (X.presheaf.germ V _ hyV (partialDeriv P k₀ u)) ≠ 0
      rw [ne_eq, heval 𝔪 h𝔪]
      exact hk₀)
  refine ⟨V, hV, hzV, u, s, hu, hs𝔮, hsq, hirr, y, hyV, ?_, ?_, WithLp.toLp 2 v, hv⟩
  · rw [specializes_iff_primeIdealOf_le hV hyV hzV, hprime]
    exact h𝔮𝔪
  · rw [hprime]
    exact hs𝔪

end Point

end SGPT.NAPotential.AlgPrimes2

end
