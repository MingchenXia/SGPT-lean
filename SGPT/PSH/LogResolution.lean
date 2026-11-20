import SGPT.PSH.NativeLogAnyDimension
import SGPT.PSH.NativeCommonCartierWithin
import SGPT.PSH.GeometricQOpenCartierCompatibility
import SGPT.PSH.NativeQPSHPullback
import SGPT.Foundations.Analysis.Pending.HironakaAPI
import SGPT.Foundations.Analysis.Pending.AdmissiblePrincipalizationAnalyticModification
import SGPT.Foundations.Analysis.Pending.DominationLogResolution

/-!
# Simple normal crossing divisors and log resolutions

Source: `chapter_pshfunctions.tex`, `def:logres` (line 1431) and `thm:resolvelogsing`
(line 1437).

* `EffectiveGeometricQDivisor.IsSNC`: an effective geometric `ℚ`-divisor is *simple normal
  crossing* when its support is the union of a locally finite family of closed sets which, at
  every point, are (near the point) distinct coordinate hyperplanes of ONE holomorphic coordinate
  system.  This is the standard notion (Bierstone--Milman 2008, Def. 2.1; the members are smooth
  hypersurfaces, not necessarily connected), stated with TN's `IsCoordinateFamilyAt`.
* `IsLogResolution n φ π` (`def:logres`): `π : Y → X` is a modification in the sense of
  `def:modif` (a finite composition of blow-ups with smooth centres, TN's `IsBlowupSequence`)
  and `φ ∘ π` has log singularities (`NativeHasLogSingularitiesAlongAnyDimension`, the native
  form of `def:pshfunctions:L1393`) along a simple normal crossing effective `ℚ`-divisor.
* `cartierGeometricQDivisor D c`: the geometric `ℚ`-divisor `c · D` of an effective Cartier
  divisor `D` (TN's `EffectiveDivisor`), with coefficients `c · ord_P D`.
* `exists_isLogResolution_of_hasAnalyticSingularitiesOfType` (`thm:resolvelogsing`): on a
  compact native complex manifold, every quasi-psh `φ` with analytic singularities of a global
  type `(c, 𝔞)` admits a log resolution.  The modification is TN's Hironaka principalization
  of `𝔞` (`HironakaAPI.exists_principalization`): `π^*𝔞 = 𝒪(-D)` with `D` of simple normal
  crossing support, and then `φ ∘ π` has log singularities along `c · D`.
* `nativeHasLogSingularitiesAlong_cartierGeometricQDivisor`: the bridge from TN's metered log
  singularities (`HasLogSingularitiesAlong` along `c · EH`, `EH` a smooth metric on `𝒪(D)`) to
  the source's geometric log singularities along `c · D`.
* `exists_kahler_logResolution`: on a compact connected Kähler manifold the resolution is
  compact connected Kähler and the residual class `{π^*θ} - {c · D}` is nef (TN's
  `lem:residual-nef`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NormalCrossings
open SGPT.Foundations.Analysis.Pending.HironakaAdmissibleSequence
open scoped Topology Manifold ContDiff

universe u

/-! ### Simple normal crossing divisors -/

namespace EffectiveGeometricQDivisor

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Source `def:logres` ("simple normal crossing effective `ℚ`-divisor"): the support of `D` is
the union of a locally finite family of closed sets `H i` such that at every point `x` the members
through `x` are, near `x`, DISTINCT coordinate hyperplanes of one holomorphic coordinate system
centred at `x`.  In particular each member is a smooth hypersurface and, `D` being a locally
finite sum of prime divisors, each prime component of `D` is a connected component of a member,
hence smooth, and the components cross normally. -/
def IsSNC (D : EffectiveGeometricQDivisor n M) : Prop :=
  ∃ (ι : Type u) (H : ι → Set M), LocallyFinite H ∧ (∀ i, IsClosed (H i)) ∧
    D.support = ⋃ i, H i ∧
      ∀ x : M, ∃ S : ι → Finset (Fin n),
        IsCoordinateFamilyAt n H S x ∧ (∀ i, x ∈ H i → (S i).card = 1) ∧
          InjOn S {i | x ∈ H i}

/-- TN's simple normal crossings divisors (finite ordered lists of smooth hypersurfaces) give
simple normal crossing geometric divisors with the same support. -/
theorem isSNC_of_isSNCDivisor (D : EffectiveGeometricQDivisor n M) {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hsupp : D.support = ⋃ H ∈ E, H) : D.IsSNC := by
  refine ⟨ULift.{u} (Fin E.length), fun i => E.get i.down, ?_, ?_, ?_, ?_⟩
  · exact locallyFinite_of_finite _
  · exact fun i => hE.1 _ (List.get_mem E i.down)
  · rw [hsupp]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨H, hH, hx⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hH
      exact ⟨⟨i⟩, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨E.get i.down, List.get_mem E i.down, hx⟩
  · intro x
    obtain ⟨S, ⟨Φ, hsrc, h0, hcoord⟩, hcard, hinj⟩ := hE.2 x
    refine ⟨fun i => S i.down, ⟨Φ, hsrc, h0, fun i hi => hcoord i.down hi⟩,
      fun i hi => hcard i.down hi, ?_⟩
    intro i hi j hj hij
    exact ULift.ext _ _ (hinj hi hj hij)

/-- The empty divisor is simple normal crossing. -/
theorem isSNC_of_support_eq_empty (D : EffectiveGeometricQDivisor n M)
    (h : D.support = ∅) : D.IsSNC := by
  refine ⟨PEmpty.{u + 1}, fun i => isEmptyElim i, locallyFinite_of_finite _,
    fun i => isEmptyElim i, ?_, ?_⟩
  · rw [h]
    ext x
    simp
  · intro x
    exact ⟨fun i => isEmptyElim i, isCoordinateFamilyAt_of_isEmpty _ _ x,
      fun i => isEmptyElim i, fun i => isEmptyElim i⟩

end EffectiveGeometricQDivisor

/-! ### The geometric `ℚ`-divisor `c · D` of an effective Cartier divisor -/

section Cartier

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The geometric `ℚ`-divisor `c · D` of an effective Cartier divisor `D`: every prime carrier `P`
gets the coefficient `c · ord_P D` (`cartierGeometricPrimeCoefficient`, the order of `D` along
the global component `P` of its support, and `0` for other primes). -/
def cartierGeometricQDivisor (D : EffectiveDivisor (m + 1) M) (c : ℚ) (hc : 0 ≤ c) :
    EffectiveGeometricQDivisor (m + 1) M where
  coefficient P := c * (cartierGeometricPrimeCoefficient D P : ℚ)
  coefficient_nonneg P := mul_nonneg hc (Nat.cast_nonneg _)
  locallyFinite := by
    classical
    intro x
    obtain ⟨U, hU, hxU, hfin⟩ := GlobalComponents.exists_isOpen_finite_globalComponents
      (cartierSupport_isComplexAnalytic D) x
    refine ⟨U, hU.mem_nhds hxU, ?_⟩
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro P hP
    obtain ⟨y, hyP, hyU⟩ := hP
    by_cases hz : c * (cartierGeometricPrimeCoefficient D P : ℚ) = 0
    · simp only [hz, if_true, mem_empty_iff_false] at hyP
    · simp only [hz, if_false] at hyP
      have hpos : 0 < cartierGeometricPrimeCoefficient D P := by
        rcases Nat.eq_zero_or_pos (cartierGeometricPrimeCoefficient D P) with h | h
        · exact absurd (by rw [h, Nat.cast_zero, mul_zero]) hz
        · exact h
      exact ⟨(cartierGeometricPrimeCoefficient_pos_iff D P).mp hpos, y, hyP, hyU⟩

theorem cartierGeometricQDivisor_coefficient (D : EffectiveDivisor (m + 1) M) (c : ℚ)
    (hc : 0 ≤ c) (P : GeometricPrimeCarrier (m + 1) M) :
    (cartierGeometricQDivisor D c hc).coefficient P =
      c * (cartierGeometricPrimeCoefficient D P : ℚ) := rfl

/-- For `c > 0` the support of `c · D` is the support of `D`. -/
theorem cartierGeometricQDivisor_support (D : EffectiveDivisor (m + 1) M) {c : ℚ}
    (hc : 0 < c) : (cartierGeometricQDivisor D c hc.le).support = D.support := by
  have hA := cartierSupport_isComplexAnalytic D
  ext x
  rw [EffectiveGeometricQDivisor.mem_support]
  constructor
  · rintro ⟨P, hP, hxP⟩
    have hpos : 0 < cartierGeometricPrimeCoefficient D P := by
      rw [cartierGeometricQDivisor_coefficient] at hP
      have h := pos_of_mul_pos_right hP hc.le
      exact_mod_cast h
    exact GlobalComponents.subset_of_mem_globalComponents hA
      ((cartierGeometricPrimeCoefficient_pos_iff D P).mp hpos) hxP
  · intro hx
    rw [← GlobalComponents.sUnion_globalComponents hA] at hx
    obtain ⟨B, hB, hxB⟩ := hx
    refine ⟨cartierComponentGeometricPrime D ⟨B, hB⟩, ?_, hxB⟩
    rw [cartierGeometricQDivisor_coefficient, cartierGeometricPrimeCoefficient_component]
    exact mul_pos hc (by exact_mod_cast regularComponentOrder_pos D ⟨B, hB⟩)

end Cartier

/-! ### Log resolutions -/

section LogResolution

/-- Source `def:logres`: a log resolution of `φ` is a modification `π : Y → X` (`def:modif`: a
finite composition of blow-ups with smooth centres) such that `π^*φ = φ ∘ π` has log
singularities along a simple normal crossing effective `ℚ`-divisor. -/
def IsLogResolution (n : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (φ : X → EReal) {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (π : Y → X) : Prop :=
  IsBlowupSequence n X Y π ∧
    ∃ D : EffectiveGeometricQDivisor n Y, D.IsSNC ∧
      NativeHasLogSingularitiesAlongAnyDimension D (φ ∘ π)

end LogResolution

/-! ### Existence: principalization of the type ideal -/

section Existence

/-- A quasi-psh potential with analytic singularities of type `(c, 𝔞)` has, at every point, a
germ of `𝔞` which does not vanish identically near the point (otherwise the potential would be
`-∞` on a neighbourhood). This is the non-vanishing hypothesis of principalization. -/
theorem exists_nonvanishing_germ_of_hasAnalyticSingularitiesOfType {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {φ : X → EReal} (hφ : (VariableComplexAtlas.ofFixedModel n X).IsQPSH φ) {c : ℚ}
    {𝔞 : GermIdeal n X} (htype : HasAnalyticSingularitiesOfType φ c 𝔞) (x : X) :
    ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0 := by
  obtain ⟨θ, hθ⟩ := hφ
  have hn := (VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential θ φ).mp hθ
  obtain ⟨U, hU, hxU, N, g, hg, hgen, R, C, _hR, heq⟩ := htype.2.2 x
  have hcR : (0 : ℝ) < c := by exact_mod_cast htype.1
  have hexists : ∃ i, ∃ᶠ y in 𝓝 x, g i y ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ᶠ y in 𝓝 x, ∀ i, g i y = 0 := by
      rw [eventually_all]
      intro i
      simpa only [not_frequently, not_not] using hnone i
    obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp hall
    obtain ⟨y, hy, hyne⟩ := hn.2 x (t ∩ U) (htopen.inter hU) ⟨hxt, hxU⟩
    exact hyne ((heq y hy.2).trans
      ((scaled_generatorLog_add_eq_bot_iff g y hcR (R y)).mpr (ht hy.1)))
  obtain ⟨i, hi⟩ := hexists
  refine ⟨g i, (hgen x hxU (g i)).mpr ?_, hi⟩
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩
    (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hg i) hxU)

/-- A function smooth in the charts on an open set is a bounded germ at its points (any
dimension; the positive-dimensional form is `SGPT.Siu.boundedRealGermAt_of_chartSmooth`). -/
private theorem boundedRealGermAt_of_chartSmoothOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {V : Set M} (hV : IsOpen V) {h : M → ℝ}
    (hh : ∀ e : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V))
    {x : M} (hx : x ∈ V) : BoundedRealGermAt h x := by
  let e := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hmem : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' V :=
    ⟨e.val.map_source hxs, by simpa only [mem_preimage, e.val.left_inv hxs] using hx⟩
  have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hV
  have hc : ContinuousAt (fun z => h (e.val.symm z)) (e.val x) :=
    ((hh e).continuousOn).continuousAt (hopen.mem_nhds hmem)
  obtain ⟨C, hC, hCb⟩ :=
    (boundedRealGermAt_of_continuousAt hc).comp_continuousAt (e.val.continuousAt hxs)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCb, e.val.open_source.mem_nhds hxs] with y hy hys
  simpa only [e.val.left_inv hys] using hy

/-- **Bridge from TN's metered log singularities to the source's geometric ones.**  Let `EH` be a
smooth metric on `𝒪(D)` for an effective Cartier divisor `D` (`IsDivisorMetric`), `c > 0`, and
let `u` be quasi-psh with TN log singularities along the metered divisor `c · EH`
(`u = c ψ_D + b`, `b` real and bounded).  Then `u` has log singularities, in the sense of
`def:pshfunctions:L1393`, along the geometric `ℚ`-divisor `c · D`. -/
theorem nativeHasLogSingularitiesAlong_cartierGeometricQDivisor {m : ℕ} {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {D : EffectiveDivisor (m + 1) Y} {EH : MeteredEffectiveQDivisor (m + 1) Y}
    (hEH : DivisorMetric.IsDivisorMetric D EH) {c : ℚ} (hc : 0 < c) {u : Y → EReal}
    (hu : (VariableComplexAtlas.ofFixedModel (m + 1) Y).IsQPSH u)
    (L : ResidualNefReduction.HasLogSingularitiesAlong (MeteredDivisorScaling.smul hc.le EH) u) :
    NativeHasLogSingularitiesAlong (cartierGeometricQDivisor D c hc.le) u := by
  classical
  refine ⟨hu, ?_⟩
  intro y
  obtain ⟨V, hV, hyV, g, hg, hgen, h, hh, hw⟩ := hEH y
  have hgen' : ∀ᶠ z in 𝓝 y, HolomorphicAt (m + 1) g z ∧ ∀ b,
      D.ideal.mem z b ↔ IsInSpanAt (n := m + 1) (· = g) z b := by
    filter_upwards [hV.mem_nhds hyV] with z hz
    exact ⟨InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hV hg hz, hgen z hz⟩
  let R : Y → ℝ := fun z => (c : ℝ) * h z + L.residual z
  have hR : BoundedRealGermAt R y := by
    obtain ⟨C, hC, hCb⟩ := boundedRealGermAt_of_chartSmoothOn hV hh hyV
    refine ⟨|(c : ℝ)| * C + L.bound, ?_, ?_⟩
    · exact add_nonneg (mul_nonneg (abs_nonneg _) hC) ((abs_nonneg _).trans (L.residual_bound y))
    · filter_upwards [hCb] with z hz
      calc |R z| ≤ |(c : ℝ) * h z| + |L.residual z| := abs_add_le _ _
        _ = |(c : ℝ)| * |h z| + |L.residual z| := by rw [abs_mul]
        _ ≤ |(c : ℝ)| * C + L.bound :=
          add_le_add (mul_le_mul_of_nonneg_left hz (abs_nonneg _)) (L.residual_bound z)
  have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc.le
  have hlog : u =ᶠ[𝓝 y] fun z =>
      ((c : ℝ) : EReal) * logNormSq (g z) + (R z : EReal) := by
    filter_upwards [hV.mem_nhds hyV] with z hz
    have hsingle : generatorLog (fun _ : Fin 1 => g) z = logNormSq (g z) := by
      rw [generatorLog_eq_log_sum]
      simp [logNormSq]
    have h1 : u z = (MeteredDivisorScaling.smul hc.le EH).weight z + (L.residual z : EReal) :=
      L.weight_add z
    have h2 : (MeteredDivisorScaling.smul hc.le EH).weight z =
        ((c : ℝ) : EReal) * EH.weight z := rfl
    rw [h2, hw z hz, hsingle,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR) (EReal.coe_ne_top _)]
      at h1
    rw [h1, add_assoc]
    congr 1
  obtain ⟨U, hyU, -, -, r, W, a, p, -, bU, C, hW, ha, hp, hideal, -, -, hCartier, hC,
      hbound, hlogU⟩ :=
    exists_native_common_open_cartier_prime_logarithms_within D y g hgen' c hc u R hR hlog
      univ univ_mem
  refine ⟨U, hyU, r, W, (fun i => c * (a i : ℚ)), p, bU, C, hW,
    (fun i => mul_pos hc (by exact_mod_cast ha i)), hp, hideal, ?_, hC, hbound, hlogU⟩
  intro A
  have hA : (A.val ∩ (Subtype.val : U → Y) ⁻¹' (univ : Set Y)).Nonempty := by
    obtain ⟨z, hz⟩ := A.nonempty
    exact ⟨z, hz, mem_univ _⟩
  have hreader := geometricQDivisorOpenRestriction_coefficient_of_local_cartier_coefficients
    (cartierGeometricQDivisor D c hc.le) D c hc univ (fun P _ => rfl) U A hA
  rw [hreader, hCartier, cartierGeometricPrimeCoefficient_finset_sum, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : W i = A
  · simp [cartierGeometricPrimeCoefficient_reduced, hi]
  · simp [cartierGeometricPrimeCoefficient_reduced, hi, Ne.symm hi]

/-- **Principalization makes analytic singularities logarithmic** (positive dimension).  On a
compact complex manifold, let `φ` be quasi-psh with analytic singularities of type `(c, 𝔞)`.
TN's admissible principalization `π : Y → X` of `𝔞` (Hironaka) gives `π^*𝔞 = 𝒪(-D)` with `D`
of simple normal crossing support `⋃ E = π⁻¹ Z(𝔞)`, `π` an isomorphism over `X \ Z(𝔞)`; then
`φ ∘ π = c ψ_D + O(1)` for a smooth metric `EH` on `𝒪(D)` (TN log singularities along the metered
divisor `c · EH`) and `φ ∘ π` has log singularities along the geometric divisor `c · D`. -/
theorem exists_principalization_logSingularities {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
    {φ : X → EReal} (hφ : (VariableComplexAtlas.ofFixedModel (m + 1) X).IsQPSH φ) {c : ℚ}
    {𝔞 : GermIdeal (m + 1) X} (htype : HasAnalyticSingularitiesOfType φ c 𝔞) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (π : Y → X) (D : EffectiveDivisor (m + 1) Y)
      (E : List (Set Y)),
      IsAdmissibleBlowupSequence (m + 1) X [] 𝔞.zeroLocus Y π E ∧ CompactSpace Y ∧
      GermIdeal.pullback (m := m + 1) π 𝔞 = D.ideal ∧ IsSNCDivisor (m + 1) E ∧
      D.support = ⋃ H ∈ E, H ∧ D.support = π ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver (m + 1) π 𝔞.zeroLocusᶜ ∧
      AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π ∧
      (∃ EH : MeteredEffectiveQDivisor (m + 1) Y, EH.support = D.support ∧
        DivisorMetric.IsDivisorMetric D EH ∧
        Nonempty (ResidualNefReduction.HasLogSingularitiesAlong
          (MeteredDivisorScaling.smul htype.1.le EH) (φ ∘ π))) ∧
      NativeHasLogSingularitiesAlong (cartierGeometricQDivisor D c htype.1.le) (φ ∘ π) := by
  classical
  have hc : 0 < c := htype.1
  obtain ⟨Y, tY, cY, mY, π, D, E, hseq, hpb, hE, hsuppE, hsupp, hiso⟩ :=
    HironakaAPI.exists_principalization htype.2.1
      (exists_nonvanishing_germ_of_hasAnalyticSingularitiesOfType hφ htype)
  have hmod : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π :=
    AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
      htype.2.1 hseq D hsupp
  have hcpt : CompactSpace Y :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective
      hseq.isBlowupSequence).1
  -- `φ ∘ π` has analytic singularities of type `(c, 𝒪(-D))`
  have hφπ : HasAnalyticSingularitiesOfType (n := m + 1) (fun y => φ (π y)) c D.ideal := by
    rw [← hpb]
    exact AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp
      hseq.isBlowupSequence.contMDiff htype
  -- a smooth metric on `𝒪(D)`, and the metered divisor `c · D`
  obtain ⟨EH, hEHs, hEH⟩ := DivisorMetric.exists_divisorMetric D
  have hFtype : HasAnalyticSingularitiesOfType (n := m + 1)
      (MeteredDivisorScaling.smul hc.le EH).weight c D.ideal := by
    have h2 := IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul hc
      (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hEH)
    rw [mul_one] at h2
    exact h2
  have hsame := IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hφπ hFtype
  let L : ResidualNefReduction.HasLogSingularitiesAlong (MeteredDivisorScaling.smul hc.le EH)
      (fun y => φ (π y)) :=
    StepFourLogSingularities.logSingularitiesOfSameSingularityType _ hsame
      (StepFourLogSingularities.weight_ne_top _)
  exact ⟨Y, tY, cY, mY, π, D, E, hseq, hcpt, hpb, hE, hsuppE, hsupp, hiso, hmod,
    ⟨EH, hEHs, hEH, ⟨L⟩⟩,
    nativeHasLogSingularitiesAlong_cartierGeometricQDivisor hEH hc
      (hφ.comp_native_analyticModification hmod) L⟩

/-- In dimension `0` every point is open. -/
private theorem isOpen_singleton_of_dim_zero {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 0) X] (x : X) : IsOpen ({x} : Set X) := by
  have hsub : (chartAt (ComplexModel 0) x).source = {x} := by
    apply Subset.antisymm
    · intro y hy
      have hxs := mem_chart_source (ComplexModel 0) x
      exact (chartAt (ComplexModel 0) x).injOn hy hxs (Subsingleton.elim _ _)
    · exact singleton_subset_iff.mpr (mem_chart_source (ComplexModel 0) x)
  rw [← hsub]
  exact (chartAt (ComplexModel 0) x).open_source

/-- In dimension `0` the identity is a log resolution of every quasi-psh function (along the
empty divisor): points are open and a quasi-psh function is finite. -/
theorem isLogResolution_id_of_dim_zero {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X] {φ : X → EReal}
    (hφ : (VariableComplexAtlas.ofFixedModel 0 X).IsQPSH φ) :
    IsLogResolution 0 φ (id : X → X) := by
  classical
  refine ⟨IsBlowupSequence.refl, emptyGeometricQDivisor 0 X,
    EffectiveGeometricQDivisor.isSNC_of_support_eq_empty _ (emptyGeometricQDivisor_support 0 X),
    hφ, ?_⟩
  intro x
  obtain ⟨θ, hθ⟩ := hφ
  have hn := (VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential θ φ).mp hθ
  have hxo := isOpen_singleton_of_dim_zero x
  obtain ⟨y, hy, hyne⟩ := hn.2 x {x} hxo rfl
  rw [mem_singleton_iff] at hy
  subst hy
  have htop : φ y ≠ ⊤ := hθ.1 y
  let U : Opens X := ⟨{y}, hxo⟩
  refine ⟨U, rfl, 0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
    (fun _ => (φ y).toReal), |(φ y).toReal|, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
    (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), (fun A => isEmptyElim A), abs_nonneg _,
    (fun _ => le_rfl), ?_⟩
  intro z
  have hz : (z : X) = y := z.property
  simp only [Function.comp_apply, id_eq, Finset.univ_eq_empty, Finset.sum_empty, zero_add, hz]
  exact (EReal.coe_toReal htop hyne).symm

/-- Source `thm:resolvelogsing`, for potentials with analytic singularities of a global type
(native form).  On a compact complex manifold `X` (of pure dimension `n`, any `n`), every
quasi-psh `φ` with analytic singularities of type `(c, 𝔞)` admits a log resolution
`π : Y → X`: a finite composition of blow-ups with smooth centres such that `φ ∘ π` has log
singularities along a simple normal crossing effective `ℚ`-divisor.  `Y` is compact. -/
theorem exists_isLogResolution_of_hasAnalyticSingularitiesOfType {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] {φ : X → EReal} (hφ : (VariableComplexAtlas.ofFixedModel n X).IsQPSH φ)
    {c : ℚ} {𝔞 : GermIdeal n X} (htype : HasAnalyticSingularitiesOfType φ c 𝔞) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X), CompactSpace Y ∧ IsLogResolution n φ π := by
  cases n with
  | zero => exact ⟨X, inferInstance, inferInstance, inferInstance, id, inferInstance,
      isLogResolution_id_of_dim_zero hφ⟩
  | succ m =>
    obtain ⟨Y, tY, cY, mY, π, D, E, hseq, hcpt, -, hE, hsuppE, -, -, -, -, hlog⟩ :=
      exists_principalization_logSingularities hφ htype
    refine ⟨Y, tY, cY, mY, π, hcpt, hseq.isBlowupSequence,
      cartierGeometricQDivisor D c htype.1.le, ?_, ?_⟩
    · apply EffectiveGeometricQDivisor.isSNC_of_isSNCDivisor _ hE
      rw [cartierGeometricQDivisor_support D htype.1, hsuppE]
    · exact (nativeHasLogSingularitiesAlongAnyDimension_succ_iff _ _).mpr hlog

/-- Source `thm:resolvelogsing` with the source's type convention `(c, 𝓘)` of
`def:neatanasing` (`HasCoherentRationalAnalyticType`, connected original neighbourhoods). -/
theorem exists_isLogResolution_of_hasCoherentRationalAnalyticType {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] {φ : X → EReal} (hφ : (VariableComplexAtlas.ofFixedModel n X).IsQPSH φ)
    {c : ℚ} {𝓘 : GermIdeal n X}
    (htype : (VariableComplexAtlas.ofFixedModel n X).HasCoherentRationalAnalyticType φ c 𝓘) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X), CompactSpace Y ∧ IsLogResolution n φ π :=
  exists_isLogResolution_of_hasAnalyticSingularitiesOfType hφ
    (VariableComplexAtlas.hasCoherentRationalAnalyticType_iff_native.mp htype)

/-- **Kähler log resolutions with nef residual class.**  On a compact connected Kähler manifold of
positive dimension, a `θ`-psh potential `φ` with analytic singularities of type `(c, 𝔞)` has a log
resolution `π : Y → X` (`Y` compact, connected, Kähler) along the simple normal crossing geometric
divisor `c · D`, `D` an effective Cartier divisor; for a smooth metric `EH` on `𝒪(D)` the TN log
singularities `φ ∘ π = c ψ_D + O(1)` hold along the metered divisor `F = c · EH`, which has the
same support, and the residual class `{π^*θ} - {F}` is nef (`lem:residual-nef` of TN: the
source's `lma:logsingrem` for this log resolution). -/
theorem exists_kahler_logResolution {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
    [ConnectedSpace X] (omegaX : PositiveClasses.KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {c : ℚ} {𝔞 : GermIdeal (m + 1) X} (htype : HasAnalyticSingularitiesOfType φ c 𝔞) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (π : Y → X) (hπ : IsBlowupSequence (m + 1) X Y π)
      (D : EffectiveDivisor (m + 1) Y) (EH : MeteredEffectiveQDivisor (m + 1) Y),
      CompactSpace Y ∧ ConnectedSpace Y ∧ Nonempty (PositiveClasses.KahlerBackground (m + 1) Y) ∧
      GermIdeal.pullback (m := m + 1) π 𝔞 = D.ideal ∧
      (cartierGeometricQDivisor D c htype.1.le).IsSNC ∧
      NativeHasLogSingularitiesAlong (cartierGeometricQDivisor D c htype.1.le) (φ ∘ π) ∧
      DivisorMetric.IsDivisorMetric D EH ∧
      (MeteredDivisorScaling.smul htype.1.le EH).support =
        (cartierGeometricQDivisor D c htype.1.le).support ∧
      Nonempty (ResidualNefReduction.HasLogSingularitiesAlong
        (MeteredDivisorScaling.smul htype.1.le EH) (φ ∘ π)) ∧
      ∀ omega' : PositiveClasses.KahlerBackground (m + 1) Y,
        PositiveClasses.NefWithRespectTo omega'
          (ClosedRealOneOneForm.pullback hπ.contMDiff θ -
            (MeteredDivisorScaling.smul htype.1.le EH).curvature) := by
  classical
  have hc : 0 < c := htype.1
  have hinv : VariableComplexAtlas.atlasClosedFormToNative
      (VariableComplexAtlas.nativeClosedFormToAtlas θ) = θ := by
    rcases θ with ⟨θ, hθ⟩
    cases θ
    rfl
  have hQ : (VariableComplexAtlas.ofFixedModel (m + 1) X).IsQPSH φ :=
    ⟨VariableComplexAtlas.nativeClosedFormToAtlas θ,
      (VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential _ φ).mpr (by rwa [hinv])⟩
  obtain ⟨Y, tY, cY, mY, π, D, E, hseq, hcpt, hpb, hE, hsuppE, -, -, -,
      ⟨EH, hEHs, hEH, ⟨L⟩⟩, hlog⟩ := exists_principalization_logSingularities hQ htype
  have hπ : IsBlowupSequence (m + 1) X Y π := hseq.isBlowupSequence
  have hK : Nonempty (PositiveClasses.KahlerBackground (m + 1) Y) :=
    (DominationLogResolution.compactSpace_and_kahler_of_isBlowupSequence ⟨omegaX⟩ hπ).2
  have hconn : ConnectedSpace Y := BlowupConnected.connectedSpace_of_isBlowupSequence π hπ
  have hsurj : Function.Surjective π :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hπ).2
  have hFsupp : (MeteredDivisorScaling.smul hc.le EH).support =
      (cartierGeometricQDivisor D c hc.le).support := by
    rw [MeteredDivisorScaling.smul_support hc.le hc.ne', hEHs, cartierGeometricQDivisor_support D hc]
  -- `φ ∘ π` is a `π^*θ`-psh potential
  have hpshπ : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hπ.contMDiff θ).val
      (fun y => φ (π y)) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp hπ.contMDiff hφ.1
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨x, -, hx⟩ := hφ.2 x₀ univ isOpen_univ (mem_univ x₀)
  obtain ⟨y₀, hy₀⟩ := hsurj x
  have hpot : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ).val
      (fun y => φ (π y)) :=
    ⟨hpshπ, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpshπ
      ⟨y₀, by rw [hy₀]; exact hx⟩⟩
  refine ⟨Y, tY, cY, mY, π, hπ, D, EH, hcpt, hconn, hK, hpb, ?_, hlog, hEH, hFsupp, ⟨L⟩, ?_⟩
  · apply EffectiveGeometricQDivisor.isSNC_of_isSNCDivisor _ hE
    rw [cartierGeometricQDivisor_support D hc, hsuppE]
  · intro omega'
    exact ResidualNef.nefWithRespectTo_sub_curvature omega' hpot L

end Existence

end SGPT.PSH
