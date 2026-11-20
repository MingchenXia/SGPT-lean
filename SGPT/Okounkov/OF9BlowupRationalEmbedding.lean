import SGPT.Okounkov.OF9RationalEmbedding
import SGPT.GAGA.ChowBlEmbed
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination

/-!
# `rmk:valcurr`: blow-up towers of `X(ℂ)` have rational projective embeddings

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`, and `def:modif` (appendix: a
modification is a finite composition of blow-ups with smooth centres).

Lane CHOW-BLOWUP proved that a blow-up `g : Z → M` of a projective manifold `Ψ : M ↪ ℙᴺ` along a
smooth centre `C` is projective: with homogeneous `P₀, …, P_r` of degree `m` generating the ideal of
the cone over `Ψ(C)` (Chow), `Ψ' = Segre(Ψ ∘ g, [P(Ψ ∘ g)]) : Z ↪ ℙ^{(N+1)(r+1)-1}`
(`SGPT.GAGA.ChowBl.blowupEmbedding`).  Here we show that this construction keeps the coordinates
rational over `X`:

* `segrePull P A = A(x_a P_b(x))`: a homogeneous `A` of degree `d` in the Segre coordinates gives a
  homogeneous polynomial of degree `(1 + m) d` on `ℙᴺ`;
* `exists_local_segre`: near every `z ∈ Z`, `(segrePull P A)(Ψ ∘ g) = (h S)^d · A(Ψ')`, where
  `h` is a
  local equation of the exceptional divisor (not identically zero) and `S` a unit;
* `isRationalEmbedding_blowupEmbedding`: if `Ψ` is rational for the model `ρ : M → X(ℂ)`, then `Ψ'`
  is rational for `ρ ∘ g` (the ratio `A/B(Ψ')` is `ρ^*q` with `q` the rational function of
  `segrePull P A / segrePull P B`; the factor `(h S)^d` cancels in the field of meromorphic germs);
* **`exists_isRationalEmbedding_of_isBlowupSequence`**: every finite sequence of blow-ups with
  smooth centres `π : M → X(ℂ)` of an integral smooth projective complex scheme `X` is compact and
  carries a rational projective embedding.  In particular `ℂ(X)` separates the points and the
  analytic subsets of `M` (used in `OF9ModelFlagUniqueness`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace SGPT.Okounkov.OF9

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open scoped Topology Manifold ContDiff

/-! ### Pulling Segre polynomials back to `ℙᴺ` -/

section Segre

variable {N r : ℕ}

/-- The substitution `x_{(a,b)} ↦ x_a P_b` of the Segre coordinates. -/
def segreSubst (P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ) (k : Fin (segreDim N r + 1)) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  MvPolynomial.X (segreIdx N r k).1 * P (segreIdx N r k).2

/-- `A(x_a P_b(x))`: a polynomial in the Segre coordinates read on `ℙᴺ` through `[P]`. -/
def segrePull (P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ)
    (A : MvPolynomial (Fin (segreDim N r + 1)) ℂ) : MvPolynomial (Fin (N + 1)) ℂ :=
  MvPolynomial.aeval (segreSubst P) A

theorem isHomogeneous_segrePull {m : ℕ} {P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ}
    (hP : ∀ k, (P k).IsHomogeneous m) {d : ℕ} {A : MvPolynomial (Fin (segreDim N r + 1)) ℂ}
    (hA : A.IsHomogeneous d) : (segrePull P A).IsHomogeneous ((1 + m) * d) :=
  hA.aeval _ fun _ => (MvPolynomial.isHomogeneous_X ℂ _).mul (hP _)

theorem eval_aeval_eq {σ : Type*} (v : Fin (N + 1) → ℂ) (G : σ → MvPolynomial (Fin (N + 1)) ℂ)
    (A : MvPolynomial σ ℂ) :
    MvPolynomial.eval v (MvPolynomial.aeval G A) =
      MvPolynomial.eval (fun k => MvPolynomial.eval v (G k)) A := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) v (MvPolynomial.bind₁ G A) =
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun k => MvPolynomial.eval₂Hom (RingHom.id ℂ) v (G k)) A
  exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _

theorem eval_segrePull (P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ) (v : Fin (N + 1) → ℂ)
    (A : MvPolynomial (Fin (segreDim N r + 1)) ℂ) :
    MvPolynomial.eval v (segrePull P A) =
      MvPolynomial.eval (segreVec v fun b => MvPolynomial.eval v (P b)) A := by
  rw [segrePull, eval_aeval_eq]
  have h : (fun k => MvPolynomial.eval v (segreSubst P k)) =
      segreVec v (fun b => MvPolynomial.eval v (P b)) := by
    funext k
    simp [segreSubst, segreVec]
  rw [h]

end Segre

/-! ### Normalized lifts -/

theorem pmk_affineLift_affineChart {N : ℕ} {p : ComplexProjectiveSpace N} {i : Fin (N + 1)}
    (hp : p ∈ (affineChart i).source) : pmk (affineLift i (affineChart i p)) = p := by
  rw [pmk_eq_mk (affineLift_ne_zero _ _)]
  exact (affineChart i).left_inv hp

theorem affineLift_affineChart_pmk {N : ℕ} {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) {i : Fin (N + 1)}
    (hvi : v i ≠ 0) : affineLift i (affineChart i (pmk v)) = (v i)⁻¹ • v := by
  rw [pmk_eq_mk hv, affineChart_mk i hv hvi, affineLift_affineRatio i hvi]

/-! ### The local form of the Segre coordinates on the blow-up -/

section Local

variable {n N r m : ℕ} {M Z : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [TopologicalSpace Z]
  [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {Ψ : M → ComplexProjectiveSpace N} {C : Set M} {g : Z → M}
  {P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ}

/-- **Local form of the blow-up embedding.** Near `z`, with `i` the chart of `Ψ (g z)` and `i'` a
chart of `Ψ'(z)`, `(segrePull P A)(Ψ ∘ g) = (h S)^d · A(Ψ')` for every homogeneous `A` of degree
`d`, where `h` is a local equation of the exceptional divisor (nonzero somewhere on every open
subset of its domain) and `S` is holomorphic and nonzero at `z`. -/
theorem exists_local_segre (hd : BlData n m Ψ C g P) (z : Z) {i' : Fin (segreDim N r + 1)}
    (hi' : blowupEmbedding Ψ g P z ∈ (affineChart i').source) :
    ∃ (U : Set Z) (h S : Z → ℂ), IsOpen U ∧ z ∈ U ∧
      (∀ W : Set Z, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0) ∧
      HolomorphicAt n h z ∧ HolomorphicAt n S z ∧ S z ≠ 0 ∧
      ∀ (d : ℕ) (A : MvPolynomial (Fin (segreDim N r + 1)) ℂ), A.IsHomogeneous d →
        ∀ᶠ y in 𝓝 z, genFun Ψ (chartIndex (Ψ (g z))) (segrePull P A) (g y) =
          (h y * S y) ^ d * genFun (blowupEmbedding Ψ g P) i' A y := by
  classical
  set i := chartIndex (Ψ (g z)) with hidef
  have hi : Ψ (g z) ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hgs : ∀ y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g y :=
    fun y => hd.blowup.contMDiff y
  obtain ⟨U, hU, hzU, h, hh, hnon, hiff⟩ := hd.blowup.2.2.2.1 z
  have hspan := vanishingIdeal_mem_iff_isInSpanAt_genFun hd.emb hd.gen hi
  obtain ⟨w, hw, hweq, hw0⟩ := exists_coeff_of_generators hd.blowup hU hzU hh hnon hiff
    (g := fun k => genFun Ψ i (P k))
    (fun k => (hspan _).mpr (CoherentIdealColon.isInSpanAt_range_iff.mpr
      ⟨holomorphicAt_genFun hd.emb hi _, fun l _ => if l = k then 1 else 0,
        fun l => holomorphicAt_const _, Eventually.of_forall fun x => by simp⟩))
    (fun a ha => by
      obtain ⟨-, c, hc, hca⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp ((hspan a).mp ha)
      exact ⟨c, hc, hca⟩)
  have hwc : ∀ᶠ y in 𝓝 z, ContinuousAt w y := by
    have : ∀ᶠ y in 𝓝 z, ∀ k, HolomorphicAt n (fun y => w y k) y :=
      eventually_all.2 fun k => (hw k).eventually
    filter_upwards [this] with y hy
    exact continuousAt_pi.mpr fun k => (hy k).continuousAt
  have hhol : HolomorphicAt n h z := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact (hh y hy).mdifferentiableAt (hU.mem_nhds hy)
  have hrep : IsBlRep Ψ g P z i U h w :=
    ⟨hi, hU, hzU, fun y hy =>
      ((hh y hy).mdifferentiableAt (hU.mem_nhds hy)).continuousAt.continuousWithinAt,
      hnon, hwc, hweq, hw0⟩
  have hmap : ∀ᶠ y in 𝓝 z, blowupMap Ψ g P y = pmk (w y) := by
    filter_upwards [hrep.eventually hd.emb hd.blowup.contMDiff.continuous] with y hy
    exact blowupMap_eq hd.emb hd.blowup.contMDiff.continuous hd.hom hy
  set c : Z → Fin (N + 1) → ℂ := fun y => affineLift i (affineChart i (Ψ (g y))) with hcdef
  have hsrc : ∀ᶠ y in 𝓝 z, Ψ (g y) ∈ (affineChart i).source :=
    (hd.emb.continuous.comp hd.blowup.contMDiff.continuous).continuousAt.eventually
      ((affineChart i).open_source.mem_nhds hi)
  have hsrc' : ∀ᶠ y in 𝓝 z, blowupEmbedding Ψ g P y ∈ (affineChart i').source :=
    (isHolomorphicEmbedding_blowupEmbedding hd).continuous.continuousAt.eventually
      ((affineChart i').open_source.mem_nhds hi')
  have hw0' : ∀ᶠ y in 𝓝 z, w y ≠ 0 := hwc.self_of_nhds.eventually_ne hw0
  set s : Z → Fin (segreDim N r + 1) → ℂ := fun y => segreVec (c y) (w y) with hsdef
  have hemb : ∀ᶠ y in 𝓝 z, blowupEmbedding Ψ g P y = pmk (s y) := by
    filter_upwards [hmap, hsrc, hw0'] with y hy1 hy2 hy3
    have hΨc : Ψ (g y) = pmk (c y) := (pmk_affineLift_affineChart hy2).symm
    change segreMap (Ψ (g y)) (blowupMap Ψ g P y) = _
    rw [hy1, hΨc, segreMap_pmk (affineLift_ne_zero _ _) hy3]
  have hs0 : s z ≠ 0 := segreVec_ne_zero (affineLift_ne_zero _ _) hw0
  have hS0 : s z i' ≠ 0 := by
    have := hi'
    rw [hemb.self_of_nhds] at this
    exact (mem_affineChart_source_pmk_iff i' hs0).mp this
  have hShol : HolomorphicAt n (fun y => s y i') z := by
    have hc : HolomorphicAt n (fun y => c y (segreIdx N r i').1) z :=
      HolomorphicAt.comp_contMDiff (b := fun x => coneLift Ψ i x (segreIdx N r i').1)
        (holomorphicAt_comp_coneLift hd.emb hi (c := fun Z => Z (segreIdx N r i').1)
          (Eventually.of_forall fun _ =>
            (EuclideanSpace.proj (𝕜 := ℂ) (segreIdx N r i').1).differentiableAt))
        (Eventually.of_forall hgs)
    exact hc.mul (hw (segreIdx N r i').2)
  refine ⟨U, h, fun y => s y i', hU, hzU, hnon, hhol, hShol, hS0, ?_⟩
  intro d A hA
  filter_upwards [hemb, hsrc', hw0', hweq] with y hy1 hy3 hy4 hy5
  have hsy : s y ≠ 0 := segreVec_ne_zero (affineLift_ne_zero _ _) hy4
  have hsi : s y i' ≠ 0 := by
    rw [hy1] at hy3
    exact (mem_affineChart_source_pmk_iff i' hsy).mp hy3
  have e1 : genFun (blowupEmbedding Ψ g P) i' A y =
      ((s y i')⁻¹) ^ d * MvPolynomial.eval (s y) A := by
    change MvPolynomial.eval
      (fun j => affineLift i' (affineChart i' (blowupEmbedding Ψ g P y)) j) A = _
    rw [hy1, affineLift_affineChart_pmk hsy hsi]
    exact SGPT.GAGA.PN.eval_smul_of_isHomogeneous hA _ _
  have e2 : genFun Ψ i (segrePull P A) (g y) = (h y) ^ d * MvPolynomial.eval (s y) A := by
    change MvPolynomial.eval (fun j => c y j) (segrePull P A) = _
    rw [eval_segrePull]
    have hv : (segreVec (fun j => c y j) fun b => MvPolynomial.eval (fun j => c y j) (P b)) =
        h y • s y := by
      have hw' : (fun b => MvPolynomial.eval (fun j => c y j) (P b)) = h y • w y := by
        funext b
        exact hy5 b
      rw [hw']
      have := segreVec_smul 1 (h y) (c y) (w y)
      rw [one_smul, one_mul] at this
      exact this
    rw [hv]
    exact SGPT.GAGA.PN.eval_smul_of_isHomogeneous hA _ _
  rw [e1, e2]
  have hone : (s y i') ^ d * ((s y i')⁻¹) ^ d = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hsi, one_pow]
  calc h y ^ d * MvPolynomial.eval (s y) A
      = h y ^ d * ((s y i') ^ d * ((s y i')⁻¹) ^ d) * MvPolynomial.eval (s y) A := by
        rw [hone, mul_one]
    _ = (h y * s y i') ^ d * ((s y i')⁻¹ ^ d * MvPolynomial.eval (s y) A) := by
        rw [mul_pow]
        ring

end Local

/-! ### The induction step and blow-up towers -/

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of9BlTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of9BlCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of9BlManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **The blow-up embedding of a rational embedding is rational.** -/
theorem isRationalEmbedding_blowupEmbedding {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    {ρ : M → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := n) ρ) {N : ℕ}
    {Ψ : M → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hR : IsRationalEmbedding f hρ hΨ)
    {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace Z] {C : Set M} {g : Z → M} {r m : ℕ}
    {P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ} (hd : BlData n m Ψ C g P)
    (hρg : IsAnalyticModification (n := n) (ρ ∘ g)) :
    IsRationalEmbedding f hρg (isHolomorphicEmbedding_blowupEmbedding hd) := by
  have hg : IsAnalyticModification (n := n) g :=
    PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hd.blowup
  have hΨ' := isHolomorphicEmbedding_blowupEmbedding hd
  intro d A B hA hB hBne
  have hA'' := isHomogeneous_segrePull hd.hom hA
  have hB'' := isHomogeneous_segrePull hd.hom hB
  -- `segrePull P B` does not vanish identically on `M`
  have hBne'' : ∃ y, MvPolynomial.eval (Ψ y).rep (segrePull P B) ≠ 0 := by
    obtain ⟨z₀, hz₀⟩ := hBne
    set i' := chartIndex (blowupEmbedding Ψ g P z₀)
    have hi' : blowupEmbedding Ψ g P z₀ ∈ (affineChart i').source :=
      mem_affineChart_chartIndex _
    obtain ⟨U, h, S, hU, hzU, hnon, -, hS, hS0, hrel⟩ := exists_local_segre hd z₀ hi'
    set i := chartIndex (Ψ (g z₀))
    have hi : Ψ (g z₀) ∈ (affineChart i).source := mem_affineChart_chartIndex _
    have hG0 : genFun (blowupEmbedding Ψ g P) i' B z₀ ≠ 0 :=
      fun h0 => hz₀ ((eval_rep_eq_zero_iff_genFun _ i' hi' hB).mpr h0)
    have hsrc : ∀ᶠ y in 𝓝 z₀, Ψ (g y) ∈ (affineChart i).source :=
      (hΨ.continuous.comp hd.blowup.contMDiff.continuous).continuousAt.eventually
        ((affineChart i).open_source.mem_nhds hi)
    have hev := (hrel d B hB).and
      (((holomorphicAt_genFun hΨ' hi' B).continuousAt.eventually_ne hG0).and
        ((hS.continuousAt.eventually_ne hS0).and hsrc))
    obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp hev
    obtain ⟨y, hyW, hy⟩ := hnon (W ∩ U) (hWopen.inter hU) inter_subset_right ⟨z₀, hzW, hzU⟩
    obtain ⟨e1, e2, e3, e4⟩ := hWsub hyW.1
    refine ⟨g y, fun h0 => ?_⟩
    have h1 := (eval_rep_eq_zero_iff_genFun Ψ i e4 hB'').mp h0
    rw [e1] at h1
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hy e3)) e2 h1
  obtain ⟨q, hq⟩ := hR _ _ _ hA'' hB'' hBne''
  refine ⟨q, fun z i' hi' => ?_⟩
  obtain ⟨U, h, S, hU, hzU, hnon, hh, hS, hS0, hrel⟩ := exists_local_segre hd z hi'
  set i := chartIndex (Ψ (g z))
  have hi : Ψ (g z) ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have key := congrArg (fracComap hg z) (hq (g z) i hi)
  rw [map_mul, fracComap_algebraMap, fracComap_algebraMap, ← ratGerm_comp f hρ hg hρg] at key
  let H : NativeHolGerm n Z z :=
    NativeHolGerm.mk (fun y => (h y * S y) ^ d) (by
      have h1 := hh.mul hS
      filter_upwards [h1] with y hy
      exact hy.pow d)
  have hcom : ∀ (A : MvPolynomial (Fin (segreDim N r + 1)) ℂ), A.IsHomogeneous d →
      NativeHolGerm.comap g hg.1 z (polyGerm hΨ hi (segrePull P A)) =
        H * polyGerm hΨ' hi' A := by
    intro A hA
    apply Subtype.ext
    change ((genFun Ψ i (segrePull P A) ∘ g : Z → ℂ) : Germ (𝓝 z) ℂ) =
      ((fun y => (h y * S y) ^ d * genFun (blowupEmbedding Ψ g P) i' A y : Z → ℂ) :
        Germ (𝓝 z) ℂ)
    exact Germ.coe_eq.mpr (hrel d A hA)
  have hH0 : H ≠ 0 := by
    intro hH
    have h0 : (fun y => (h y * S y) ^ d) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      have : H = NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0) := hH
      exact NativeHolGerm.mk_eq_mk_iff.mp this
    have hev := h0.and (hS.continuousAt.eventually_ne hS0)
    obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp hev
    obtain ⟨y, hyW, hy⟩ := hnon (W ∩ U) (hWopen.inter hU) inter_subset_right ⟨z, hzW, hzU⟩
    obtain ⟨e1, e2⟩ := hWsub hyW.1
    exact pow_ne_zero d (mul_ne_zero hy e2) e1
  have hHf : algebraMap (NativeHolGerm n Z z) (FractionRing (NativeHolGerm n Z z)) H ≠ 0 :=
    fun h0 => hH0 (IsFractionRing.injective _ (FractionRing (NativeHolGerm n Z z))
      (h0.trans (map_zero _).symm))
  rw [hcom B hB, hcom A hA, map_mul, map_mul] at key
  apply mul_left_cancel₀ hHf
  rw [← key]
  ring

/-- **Blow-up towers of `X(ℂ)` have rational projective embeddings.** Every finite sequence of
blow-ups with smooth centres `π : M → X(ℂ)` (`def:modif`) of an integral smooth projective complex
scheme `X` is compact and admits a holomorphic embedding `Ψ : M ↪ ℙᴺ` which is rational for the
model `π`: every ratio of homogeneous polynomials in `Ψ` is the pull-back of a rational function
of `X`. -/
theorem exists_isRationalEmbedding_of_isBlowupSequence (E : ClosedProjectiveEmbedding f)
    {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {π : M → SchemeComplexPoint f} (hπ : IsBlowupSequence n (SchemeComplexPoint f) M π) :
    CompactSpace M ∧ ∃ (N : ℕ) (Ψ : M → ComplexProjectiveSpace N)
      (hΨ : IsHolomorphicEmbedding (n := n) Ψ), ∀ [CompactSpace M],
        IsRationalEmbedding f (isAnalyticModification_of_isBlowupSequence hπ) hΨ := by
  induction hπ with
  | refl =>
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    exact ⟨E.analyticCompact, _, projectivePoint f E n,
      isHolomorphicEmbedding_projectivePoint f E n, isRationalEmbedding_projectivePoint f E _⟩
  | step ρ C g hρ hg ih =>
    obtain ⟨hc, N, Ψ, hΨ, hR⟩ := ih
    have := hc
    obtain ⟨r, m, P, hd⟩ := exists_blData hΨ hg
    have hZ := BlowupCompact.compactSpace_of_isBlowupAlong hg
    exact ⟨hZ, _, _, isHolomorphicEmbedding_blowupEmbedding hd,
      isRationalEmbedding_blowupEmbedding f (isAnalyticModification_of_isBlowupSequence hρ) hΨ hR
        hd _⟩

end Scheme

end SGPT.Okounkov.OF9
