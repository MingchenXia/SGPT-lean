import SGPT.Okounkov.OF3SiuSections
import SGPT.Okounkov.OFNuOkFirstCoordinate
import SGPT.Projective.OkounkovOriginalCommonMultiplierTwist
import SGPT.NAPotential.BJPrepLelongConvex

/-!
# `thm:nuOk` for every prime divisor `E` (singular, or over `X`)

Source: chapter *The theory of Okounkov bodies*, subsection *Recover Lelong numbers from partial
Okounkov bodies*, `thm:nuOk`: *let `E` be a prime divisor on `X` and `Y•` an admissible flag with
`E = Y₁`; then `ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`.*

The book's proof only uses that the first coordinate of the flag valuation `ν_{Y•}` is the order
of vanishing `ord_E` along `E = Y₁` (*"By definition, `min_{x ∈ Δ_k(θ,φ)} x₁ =
k⁻¹ ord_E H⁰(X, L^k ⊗ 𝓘(kφ))`"*). We prove the formula for **every** surjective rank `n`
valuation `ν` of `ℂ(X)` whose first coordinate on sections is `ord_E` (`IsFirstCoordinateOrder`),
for **every** prime divisor `E` over `X` (source `def:primdiv`: a connected smooth hypersurface of a
resolution of `X(ℂ)`, `SGPT.PSH.CompactPrimeOver.PrimePresentation`). This covers prime divisors
on `X` with arbitrary singularities (realized by their strict transform on an embedded
resolution), in particular the first member of an admissible flag, with no smooth flag through
`E`; here `ν(φ, E)` is the generic Lelong number of `π^* φ` along `E`
(`SGPT.PSH.CompactPrimeOver.presentationReader`, source `def:pshfunctions:L1112`).

## Proof

* Kähler currents (`isLeast_firstCoordinate_partialBody_of_kahler`): by `thm:HCP` (Kähler case,
  twist `T = 𝒪(k_T)`) the polytopes `Δ_{k,T}(θ, φ)` converge to `Δ_ν(θ, φ)`, so their first
  coordinate minima converge (`lma:Hausdorffconvcoordbounds`). The minimum at level `k` is
  `k⁻¹ ord_E 𝓘(kφ)` for `k ≫ 0`: every section of `T ⊗ L^k ⊗ 𝓘(kφ)` vanishes to order at least
  `ord_E 𝓘(kφ)` along `E` (`presentationMultiplierOrder_le_sectionDivisorOrder`), and Siu's uniform
  global generation produces a section of `L^k ⊗ 𝓘(kφ)` of order exactly `ord_E 𝓘(kφ)`
  (`exists_section_sectionDivisorOrder_le`), which twists into `T ⊗ L^k`
  (`OriginalCommonMultiplierTwist`). Finally `k⁻¹ ord_E 𝓘(kφ) → ν(φ, E)`
  (`prop:Lelongnumfrommis`, `tendsto_presentationMultiplierOrder_ratio`). (Siu's theorem replaces
  the log resolution and the global generation of `k(L - F)` of the book's Step 2.)
* `vol θ_φ > 0` (`isLeast_firstCoordinate_partialBody`): perturb `L` by the ample `𝒪_X(1)`
  (`prop:Deltapert`), as in the book; `ν(qφ, E) = q ν(φ, E)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF3

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.Okounkov.ValGen2 SGPT.NAPotential.FSPos
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeMultiplierOrder SGPT.PSH.CompactPrimeMultiplierLimit
open scoped Topology ENNReal Pointwise

/-! ### Coordinate minima of polytopes -/

/-- If every point of `Q k` has `i`-th coordinate at least `t` and some point has `i`-th
coordinate at most `t`, the minimum of the `i`-th coordinate on `poly Q k` is `k⁻¹ t`. -/
theorem sInf_image_coordinate_poly_eq {n : ℕ} (i : Fin n) (Q : ℕ → Set (Fin n → ℤ)) (k : ℕ)
    {t : ℤ} (hlow : ∀ x ∈ Q k, t ≤ x i) (hmem : ∃ x ∈ Q k, x i ≤ t) :
    sInf ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' poly Q k) = (k : ℝ)⁻¹ * t := by
  have himg : (fun x : EuclideanSpace ℝ (Fin n) => x i) '' poly Q k =
      convexHull ℝ ((fun x : Fin n → ℤ => (k : ℝ)⁻¹ * (x i : ℝ)) '' Q k) := by
    unfold poly
    rw [show (fun x : EuclideanSpace ℝ (Fin n) => x i) = OF.coordinateLinearMap i from rfl,
      (OF.coordinateLinearMap i).image_convexHull, Set.image_image]
    congr 1
  rw [himg]
  apply IsLeast.csInf_eq
  constructor
  · obtain ⟨x, hx, hxt⟩ := hmem
    have hxt' : x i = t := le_antisymm hxt (hlow x hx)
    exact subset_convexHull ℝ _ ⟨x, hx, by simp only [hxt']⟩
  · have hsub : convexHull ℝ ((fun x : Fin n → ℤ => (k : ℝ)⁻¹ * (x i : ℝ)) '' Q k) ⊆
        Ici ((k : ℝ)⁻¹ * t) := by
      refine convexHull_min ?_ (convex_Ici _)
      rintro _ ⟨x, hx, rfl⟩
      show (k : ℝ)⁻¹ * (t : ℝ) ≤ (k : ℝ)⁻¹ * (x i : ℝ)
      exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr (hlow x hx))
        (inv_nonneg.mpr (Nat.cast_nonneg k))
    exact fun y hy => hsub hy

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance of3NuOkTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of3NuOkCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of3NuOkManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance of3NuOkMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance of3NuOkBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-! ### Generic Lelong numbers of multiples -/

omit [IsIntegral X] in
/-- `ν(qφ, E) = q ν(φ, E)`. -/
theorem presentationReader_natCast_mul (φ : SchemeComplexPoint f → EReal)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) {q : ℕ} (hq : 0 < q) :
    presentationReader (fun x => (q : EReal) * φ x) p = (q : ℝ≥0∞) * presentationReader φ p := by
  rw [SGPT.NAPotential.BJPrep.presentationReader_eq_sourceGenericLelongNumber,
    SGPT.NAPotential.BJPrep.presentationReader_eq_sourceGenericLelongNumber]
  unfold sourceGenericLelongNumber
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hq.ne') (ENNReal.natCast_ne_top q)]
  refine iInf_congr fun y => ?_
  have h := SGPT.Okounkov.squaredLogLelongNumber_smul_eq (n := m + 1)
    (fun z => φ (p.projection z)) y.val hqR
  rw [ENNReal.ofReal_natCast] at h
  rw [← h]
  rfl

/-! ### The hypothesis on the valuation -/

/-- **The first coordinate of `ν` is `ord_E`**: for every line bundle `M` on `X`, every atlas `b`
of `M` and every nonzero `s ∈ H⁰(X, M)`, the first coordinate of `ν(s)` (read at the centre of
`ν` in a frame of `b`) is the nonnegative integer `ord_E(s)` (`sectionDivisorOrder`). This holds
for `ν = ν_{Y•}` and `E = Y₁` (source: *"`ν₁ = ord_{Y₁}(s)` ... the same construction applies to
a non-zero section `s ∈ H⁰(X, L)` after choosing a local trivialization of `L` near `Yₙ`"*). -/
def IsFirstCoordinateOrder (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) : Prop :=
  letI := E.isProper
  ∀ (M : X.Modules) (b : LineBundleAtlas M) (s : bundleSections M ⊤) (hs : s ≠ 0),
    0 ≤ plainSectionVector v (valuationCenter f v) b s hs 0 ∧
      (((plainSectionVector v (valuationCenter f v) b s hs 0).toNat : ℕ) : ℕ∞) =
        sectionDivisorOrder f E p s

variable [Nonempty (SchemeComplexPoint f)]

/-- **Source `thm:nuOk`, Kähler currents, every prime divisor `E` over `X`.** For every surjective
rank `n` valuation `ν` of `ℂ(X)` whose first coordinate is `ord_E` and every `φ` with `θ_φ` a
Kähler current, `ν(φ, E) = min_{x ∈ Δ_ν(θ, φ)} x₁`. -/
theorem isLeast_firstCoordinate_partialBody_of_kahler
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m + 1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) (hord : IsFirstCoordinateOrder f E v p)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsKahlerCurrentPotential (H.curvature a) φ) :
    letI := E.isProper
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      IsLeast ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)
        (presentationReader φ p).toReal := by
  let := E.isProper
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set c := valuationCenter f v with hcdef
  have hc : IsNonnegAt v c := (isValuationCenter_valuationCenter f v).1
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hq : IsGlobalQuasiPshPotential (n := m + 1) φ := ⟨hφθ.1.quasiPlurisubharmonic, hφθ.2⟩
  have hpos := OriginalBook.original_iVolume_pos_of_kahler_allDimensions f (m + 1) E a H hφ
  -- the twist `T = 𝒪(k_T)` absorbing the sections of `L^k ⊗ 𝓘(kφ)`
  obtain ⟨kT, -, hincl⟩ :=
    OriginalCommonMultiplierTwist.exists_common_fixed_positive_twist_multiplier_inclusions
      f (m + 1) E a a (hyperplaneAtlas E) H H (fubiniStudyMetric f E (m + 1))
      (fubiniStudy_curvature_isKahler f (m + 1) E) rfl
  let aT := (hyperplaneAtlas E).tensorPower kT
  let r : ∀ k, LineBundleAtlas
      (bundleTensor (bundleTensorPower (hyperplaneBundle E) kT) (bundleTensorPower L k)) :=
    fun k => SGPT.IGood.DXMain.twistAtlas aT a k
  let Q : ℕ → Set (Fin (m + 1) → ℤ) := fun k =>
    AlgebraicValuation.twistedMultiplierValues f (m + 1) E v c k (r k) φ
  -- `thm:HCP` for Kähler currents
  obtain ⟨hKc, hKv, hlim⟩ :=
    OriginalBook.tendsto_twistedMultiplierPolytope_kahler_positiveDimension f E a aT H hbig v hv r hφ
  have hev := OriginalBook.eventually_twistedMultiplierPolytope_compact_nonempty_positiveDimension
    f E a aT H hbig v hv c r hφθ hpos
  obtain ⟨_hKc₁, _hKv₁, _hsubv, _hΓv, -, -, hvolv⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig v hv hφθ hpos
  refine ⟨hKc, hKv, ?_⟩
  set K := ValGen.partialBody f (m + 1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ
    with hKdef
  have hIpos : (0 : ℝ≥0∞) <
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφθ /
        ((m + 1).factorial : ℝ≥0∞) :=
    ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)
  have hKn : K.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := volume)
    have h : volume K = _ := hvolv
    rw [h]
    exact hIpos.ne'
  have hKcpt : IsCompact K := ValGen.isCompact_setBody _ _
  have hlimQ : Tendsto (fun k : ℕ => hausdorffDist (poly Q k) K) atTop (𝓝 0) := hlim
  have hmv := OF.tendsto_sInf_image_coordinate 0
    (hev.mono fun k hk => ⟨hk.2, poly_nonempty hk.1⟩) (fun _ => convex_convexHull ℝ _)
    hKcpt (ValGen.convex_setBody _ _) hKn hlimQ
  set r₀ := sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' K) with hr₀
  -- Siu's sections
  obtain ⟨ω', hω'⟩ := hφ
  have hφδ : IsThetaPshPotential (H.curvature a - (1 : ℝ) • ω'.form).val φ := by
    rwa [one_smul]
  obtain ⟨k₀, hk₀⟩ := exists_section_sectionDivisorOrder_le f E a H ω' one_pos
  -- the minimum on the polytope of level `k + 1`
  let g : ℕ → ℝ := fun k =>
    (presentationMultiplierOrder hq (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity) p : ℝ) /
      ((k + 1 : ℕ) : ℝ)
  have hformula : ∀ k : ℕ, k₀ ≤ k + 1 →
      sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' poly Q (k + 1)) = g k := by
    intro k hk
    have hkR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h := sInf_image_coordinate_poly_eq (0 : Fin (m + 1)) Q (k + 1)
      (t := (presentationMultiplierOrder hq hkR p : ℤ)) ?_ ?_
    · rw [h]
      simp only [g, Int.cast_natCast]
      ring
    · rintro x ⟨s, hs, hcond, rfl⟩
      have hI := hcond.resolve_left (Nat.succ_ne_zero k)
      have hle := presentationMultiplierOrder_le_sectionDivisorOrder f E hq hkR p hI
      have hrd := hord _ (r (k + 1)) s hs
      rw [← hcdef] at hrd
      obtain ⟨h0, heq⟩ := hrd
      rw [← heq] at hle
      have h1 := ENat.natCast_le_natCast.mp hle
      have h2 := Int.toNat_of_nonneg h0
      omega
    · obtain ⟨σ, hσ0, hσmult, hσord⟩ := hk₀ (k + 1) hk φ hφδ hq hkR p
      have hmemΓ : sectionVector v c a (k + 1) σ hσ0 ∈
          slice (AlgebraicValuation.multiplierSectionSet f (m + 1) E v c a φ) ((k + 1 : ℕ) : ℤ) :=
        ⟨k + 1, σ, hσ0, hσmult, rfl⟩
      have hx := (hincl (k + 1) (Nat.succ_pos k) v c hc (r (k + 1)) φ φ (fun _ => rfl)).1 hmemΓ
      refine ⟨_, hx, ?_⟩
      have hval := ValGen2.sectionValue_eq_plainSectionValue (a := a) (v := v) hc (k + 1) σ
      have hvec : sectionVector v c a (k + 1) σ hσ0 =
          plainSectionVector v c (a.tensorPower (k + 1)) σ hσ0 := by
        rw [sectionValue_eq_vector c a (k + 1) σ hσ0,
          plainSectionValue_eq_vector c (a.tensorPower (k + 1)) σ hσ0] at hval
        exact toLex.injective (WithTop.coe_injective hval)
      rw [hvec]
      have hrd := hord _ (a.tensorPower (k + 1)) σ hσ0
      rw [← hcdef] at hrd
      obtain ⟨h0, heq⟩ := hrd
      rw [← heq] at hσord
      have h1 := ENat.natCast_le_natCast.mp hσord
      have h2 := Int.toNat_of_nonneg h0
      omega
  -- the limit of the minima
  have hmv' := (tendsto_add_atTop_iff_nat 1).mpr hmv
  have hg : Tendsto g atTop (𝓝 r₀) := by
    refine hmv'.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with k hk
    exact hformula k (hk.trans (Nat.le_succ k))
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  have hr0 : 0 ≤ r₀ := ge_of_tendsto' hg hg0
  -- `prop:Lelongnumfrommis`
  have hR := tendsto_presentationMultiplierOrder_ratio hq p
  have hofReal : Tendsto (fun k => ENNReal.ofReal (g k)) atTop (𝓝 (ENNReal.ofReal r₀)) :=
    (ENNReal.continuous_ofReal.tendsto r₀).comp hg
  have hgE : (fun k => ENNReal.ofReal (g k)) = fun k : ℕ =>
      (presentationMultiplierOrder hq (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity) p :
        ℝ≥0∞) / ((k + 1 : ℕ) : ℝ≥0∞) := by
    funext k
    simp only [g]
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hgE] at hofReal
  have hReq : presentationReader φ p = ENNReal.ofReal r₀ := tendsto_nhds_unique hR hofReal
  rw [hReq, ENNReal.toReal_ofReal hr0, hr₀]
  have hcompact : IsCompact ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' K) :=
    hKcpt.image (BodyExtrema.lipschitzWith_coordinate (0 : Fin (m + 1))).continuous
  exact hcompact.isLeast_sInf (hKn.image _)

/-- **Source `thm:nuOk`, every prime divisor `E` over `X`.** Let `E` be a prime divisor over `X`
(e.g. a prime divisor on `X`, possibly singular) and `ν` a surjective rank `n` valuation of
`ℂ(X)` whose first coordinate is `ord_E` (e.g. `ν = ν_{Y•}` for an admissible flag with
`Y₁ = E`). Then for every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`ν(φ, E) = min_{x ∈ Δ_ν(θ, φ)} x₁`. -/
theorem isLeast_firstCoordinate_partialBody
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) (hord : IsFirstCoordinateOrder f E v p)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)
    (hpos : haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      IsLeast ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)
        (presentationReader φ p).toReal := by
  let := E.isProper
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hbig := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f (m + 1) E a H hφ hpos
  obtain ⟨hKc, hKv, _hsubv, _hΓv, -, -, hvolv⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig v hv hφ hpos
  refine ⟨hKc, hKv, ?_⟩
  set Kv := ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
    (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ with hKvdef
  -- the ample perturbation `𝒪_X(1)` with its Fubini–Study metric
  let aA := hyperplaneAtlas E
  let K := fubiniStudyMetric f E (m + 1)
  have hK := fubiniStudy_curvature_isKahler f (m + 1) E
  let P : SGPT.LineBundle.AmplePolarization f (hyperplaneBundle E) :=
    { power := 1
      power_pos := one_pos
      ambientDimension := E.ambientDimension
      map := E.map
      isClosedImmersion := E.closedImmersion
      over_base := E.over_base
      iso := bundleTensorLeftUnitIso (hyperplaneBundle E) }
  obtain ⟨_, _, hpertv⟩ := OriginalBook.tendsto_normalized_positivePerturb_partialBody_allDimensions
    f (m + 1) E a H aA P K hK hφ hpos v hv
  let q : ℕ → ℕ := fun i => i + 1
  let p' : ℕ → ℕ := fun _ => 1
  have hq : ∀ i, 0 < q i := fun i => Nat.succ_pos i
  have hp : ∀ i, 0 < p' i := fun _ => one_pos
  have hqp : Tendsto (fun i => (p' i : ℝ) / (q i : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine h.congr fun i => ?_
    simp [p', q]
  obtain ⟨hKic, hKiv, hcpt, hne, hlim⟩ := hpertv ℕ atTop q p' hq hp hqp
  have hIpos : (0 : ℝ≥0∞) <
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
        ((m + 1).factorial : ℝ≥0∞) :=
    ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)
  have hKvn : Kv.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := volume)
    have h : volume Kv = _ := hvolv
    rw [h]
    exact hIpos.ne'
  -- the perturbed weights are Kähler currents: the Kähler case applies
  have heq : ∀ i : ℕ,
      sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ((q i : ℝ)⁻¹ • ValGen.partialBody f (m + 1) E v (valuationCenter f v)
            (OkoNS.perturbAtlas a aA (q i) (p' i))
            (SGPT.GAGA.OkoClose.coneOver _ (hKic i) (hKiv i)) (fun x => (q i : EReal) * φ x))) =
        (presentationReader φ p).toReal := by
    intro i
    obtain ⟨hKφ, hbigi⟩ := OriginalBook.original_positivePerturbation_kahler_and_big f (m + 1) E
      a H aA K hK hφ (q i) (p' i) (hq i) (hp i)
    obtain ⟨_, _, hleast⟩ := isLeast_firstCoordinate_partialBody_of_kahler f E p
      (OkoNS.perturbAtlas a aA (q i) (p' i))
      (OriginalBook.originalPerturbMetric f (m + 1) E a H aA K (q i) (p' i)) hbigi v hv hord hKφ
    have hinv : (0 : ℝ) ≤ (q i : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have h2 : sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
        ValGen.partialBody f (m + 1) E v (valuationCenter f v)
          (OkoNS.perturbAtlas a aA (q i) (p' i))
          (SGPT.GAGA.OkoClose.coneOver _ (hKic i) (hKiv i)) (fun x => (q i : EReal) * φ x)) =
        (presentationReader (fun x => (q i : EReal) * φ x) p).toReal := hleast.csInf_eq
    rw [OF.image_coordinate_smul, Real.sInf_smul_of_nonneg hinv, h2,
      presentationReader_natCast_mul f φ p (hq i), ENNReal.toReal_mul, ENNReal.toReal_natCast,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (hq i).ne'), one_mul]
  -- pass to the limit
  have hmv := OF.tendsto_sInf_image_coordinate 0
    (Eventually.of_forall fun i => ⟨hcpt i, hne i⟩)
    (fun i => (ValGen.convex_setBody _ _).smul _)
    (ValGen.isCompact_setBody _ _) (ValGen.convex_setBody _ _) hKvn hlim
  have hlimeq : sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' Kv) =
      (presentationReader φ p).toReal :=
    tendsto_nhds_unique hmv (tendsto_const_nhds.congr fun i => (heq i).symm)
  have hcompact : IsCompact ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' Kv) :=
    (ValGen.isCompact_setBody _ _).image
      (BodyExtrema.lipschitzWith_coordinate (0 : Fin (m + 1))).continuous
  have hleast := hcompact.isLeast_sInf (hKvn.image _)
  rw [hlimeq] at hleast
  exact hleast

end SGPT.Okounkov.OF3
