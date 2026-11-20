import SGPT.Okounkov.OF13SncChart
import SGPT.Okounkov.OF13RationalRep

/-!
# An analytic log resolution of finitely many rational functions

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (existence part of
[CFKLRS17, Thm 2.9]: "… a valuation induced by an admissible flag on a modification of `X`"; a
modification is a finite composition of blow-ups with smooth centres, `def:modif`).

`IsLogResolutionGermAt y γ u`: at the point `y` of a complex manifold, the elements `u_k` of a field
`K`, read as meromorphic germs through `γ : K → Frac 𝒪_{Y,y}`, are analytic units times Laurent
monomials in the local equations of the members through `y` of a normal crossings divisor, and
`u_k` or `u_k⁻¹` is holomorphic. For `Y = V(ℂ)` and `γ` the meromorphic germ map of a scheme `V`
this is the shape of the `IsAnalyticLogResolutionAt`.

**Main theorem** (`exists_tower_isLogResolutionGermAt`): for an integral smooth projective complex
scheme `X` and nonzero `u₁, …, u_r ∈ ℂ(X)`, there is a blow-up tower `π : Y → X(ℂ)` (a modification
in the sense of `def:modif`) such that the pull-backs `π^* u_k` (the `ratGerm`) form an
analytic log resolution at **every** point of `Y`. Proof: `u_k = P_k/Q_k` with homogeneous
`P_k, Q_k` of the same degree (`exists_homogeneous_ratio`); principalize `∏ₖ (Pₖ)(Qₖ)(Pₖ,Qₖ)`
(`exists_principalization_ratios`); read the result in the monomial chart of the principalized
divisor (`exists_sncChart_monomial`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF13

open CategoryTheory AlgebraicGeometry Set Filter IsLocalRing SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.Okounkov.OF9
open scoped Topology Manifold ContDiff

/-! ### The predicate -/

section Predicate

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Analytic log resolution data at a point.** The elements `u_k` of `K`, read as meromorphic
germs at `y` through `γ`, are analytic units times Laurent monomials `∏_{j ∈ M} ℓⱼ^{a_{kj}}` in
holomorphic coordinates `ℓ` whose members `ℓⱼ` (`j ∈ M`) are local equations of analytic
hypersurfaces `Hⱼ`, and `u_k` or `u_k⁻¹` is holomorphic. -/
def IsLogResolutionGermAt {K : Type*} [Field K] {r : ℕ} (y : Y)
    (γ : K →+* FractionRing (NativeHolGerm n Y y)) (u : Fin r → K) : Prop :=
  ∃ (ℓ : Fin n → Y → ℂ) (hℓ : ∀ j, HolomorphicAt n (ℓ j) y),
    Ideal.span (Set.range fun j => NativeHolGerm.mk (ℓ j) (hℓ j)) =
      maximalIdeal (NativeHolGerm n Y y) ∧
    ∃ (M : Finset (Fin n)) (H : Fin n → Set Y),
      (∀ j ∈ M, IsComplexAnalyticSubset (n := n) (H j)) ∧
      (∀ j ∈ M, (vanishingIdeal (n := n) (H j)).mem y (ℓ j)) ∧
      (∀ j ∈ M, ∀ (h : Y → ℂ) (hh : HolomorphicAt n h y),
        (vanishingIdeal (n := n) (H j)).mem y h →
          NativeHolGerm.mk h hh ∈ Ideal.span {NativeHolGerm.mk (ℓ j) (hℓ j)}) ∧
      ∃ (η : Fin r → (NativeHolGerm n Y y)ˣ) (a : Fin r → Fin n → ℤ),
        (∀ k, ∀ j ∉ M, a k j = 0) ∧
        (∀ k, γ (u k) =
          algebraMap _ (FractionRing (NativeHolGerm n Y y)) (η k : NativeHolGerm n Y y) *
            ∏ j, (algebraMap _ (FractionRing (NativeHolGerm n Y y))
              (NativeHolGerm.mk (ℓ j) (hℓ j))) ^ (a k j)) ∧
        ∀ k, (∃ h : NativeHolGerm n Y y,
            γ (u k) = algebraMap _ (FractionRing (NativeHolGerm n Y y)) h) ∨
          ∃ h : NativeHolGerm n Y y,
            γ (u k)⁻¹ = algebraMap _ (FractionRing (NativeHolGerm n Y y)) h

end Predicate


/-! ### The tower -/

section Tower

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of13tTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of13tCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of13tManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **An analytic log resolution of finitely many rational functions.** For an integral smooth
projective complex scheme `X` and nonzero `u₁, …, u_r ∈ ℂ(X)` there is a blow-up tower
`π : Y → X(ℂ)` such that at every point of `Y` the pull-backs of the `u_k` are analytic units times
Laurent monomials in normal crossings coordinates (with `u_k` or `u_k⁻¹` holomorphic). -/
theorem exists_tower_isLogResolutionGermAt (E : ClosedProjectiveEmbedding f) {r : ℕ}
    (u : Fin r → X.functionField) (hu : ∀ k, u k ≠ 0) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → SchemeComplexPoint f)
      (hseq : IsBlowupSequence n (SchemeComplexPoint f) Y π),
      ∀ y : Y, IsLogResolutionGermAt y
        (ratGerm f (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) y) u := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let Ψ := projectivePoint f E n
  have hΨ : IsHolomorphicEmbedding (n := n) Ψ := isHolomorphicEmbedding_projectivePoint f E n
  -- numerators and denominators
  have hrat := fun k => exists_homogeneous_ratio f E (u k)
  choose d P Q hP hQ hPQ using hrat
  -- germs of the restrictions at a complex point
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
    have hinjL := IsFractionRing.injective (NativeHolGerm n (SchemeComplexPoint f) x)
      (FractionRing (NativeHolGerm n (SchemeComplexPoint f) x))
    refine ⟨fun h0 => hQ0 (hinjF ?_), fun h0 => hP0 (hinjF ?_), ?_⟩
    · rw [hgermFF x i hi, h0, map_zero, map_zero]
    · rw [hgermFF x i hi, h0, map_zero, map_zero]
    · rw [← hgermFF x i hi, ← hgermFF x i hi, ← map_mul, heq]
  -- principalization
  obtain ⟨Y, tY, cY, mY, π, hseq, D, E', hsnc, hsupp, hmain⟩ :=
    exists_principalization_ratios hΨ P Q d hP hQ fun x i hi k =>
      ⟨(hratio x i hi k).2.1, (hratio x i hi k).1⟩
  refine ⟨Y, tY, cY, mY, π, hseq, fun y => ?_⟩
  set hmod := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
  obtain ⟨ℓ, hℓ, hspan, M, H, hH, hℓmem, hℓgen, gD, hgD, hgen, hmono⟩ :=
    exists_sncChart_monomial D hsnc hsupp.le y
  obtain ⟨i, hi⟩ := exists_mem_affineChart_source (Ψ (π y))
  obtain ⟨-, hk⟩ := hmain y i hi gD hgD hgen
  let p : Fin r → NativeHolGerm n Y y := fun k => pullGerm hΨ hmod.1 hi (P k)
  let q : Fin r → NativeHolGerm n Y y := fun k => pullGerm hΨ hmod.1 hi (Q k)
  -- monomial forms of `p` and `q`
  have hpm := fun k => hmono (p k) (hk k).2.2.2.1
  have hqm := fun k => hmono (q k) (hk k).2.2.2.2
  choose ηp α hαM hpα using hpm
  choose ηq β hβM hqβ using hqm
  let L := FractionRing (NativeHolGerm n Y y)
  let w : Fin n → NativeHolGerm n Y y := fun j => NativeHolGerm.mk (ℓ j) (hℓ j)
  -- the pulled back ratio
  have hγ : ∀ k, ratGerm f hmod y (u k) * algebraMap _ L (q k) = algebraMap _ L (p k) := by
    intro k
    have h := congrArg (fracComap hmod y) (hratio (π y) i hi k).2.2
    rw [map_mul, fracComap_algebraMap, fracComap_algebraMap] at h
    exact h
  have hqL : ∀ k, algebraMap _ L (q k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (hk k).2.1
  have hpL : ∀ k, algebraMap _ L (p k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (hk k).1
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
  refine ⟨ℓ, hℓ, hspan, M, H, hH, hℓmem, hℓgen, fun k => ηp k * (ηq k)⁻¹,
    fun k j => (α k j : ℤ) - β k j, fun k j hj => by
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
    have hηq : algebraMap _ L (ηq k : NativeHolGerm n Y y) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (ηq k).ne_zero
    rw [hp', hq', Units.val_mul, map_mul, map_units_inv]
    change _ = _ * _ * ∏ j, algebraMap _ L (w j) ^ ((α k j : ℤ) - β k j)
    simp_rw [zpow_sub₀ (hwL _), zpow_natCast]
    rw [Finset.prod_div_distrib, mul_div_mul_comm, div_eq_mul_inv]
  · rcases (hk k).2.2.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · right
      refine ⟨c, ?_⟩
      have hc' : q k = p k * c := hc
      rw [map_inv₀, hratio' k, inv_div, hc', map_mul, mul_div_cancel_left₀ _ (hpL k)]
    · left
      refine ⟨c, ?_⟩
      have hc' : p k = q k * c := hc
      rw [hratio' k, hc', map_mul, mul_div_cancel_left₀ _ (hqL k)]

end Tower

end SGPT.Okounkov.OF13
