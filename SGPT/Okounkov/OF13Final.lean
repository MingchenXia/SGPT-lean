import SGPT.Okounkov.OF13Tower
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage

/-!
# `rmk:Abhyankar`: the existence part of [CFKLRS17, Thm 2.9] from algebraized towers

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`:
*if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`, then
[CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a valuation
induced by an admissible flag on a modification of `X`.* (A modification of a compact complex space
is a finite composition of blow-ups with smooth centres, `def:modif`.)

* `isAnalyticModification_of_diffeomorph`: a biholomorphism is an analytic modification;
* `isLogResolutionGermAt_transport`: log resolution data are transported along a biholomorphism
  `φ : V(ℂ) ≃ Y` (coordinates, hypersurfaces `φ⁻¹ Hⱼ`, local equations, monomials);
* `HasRationalAlgebraization f n π`: the blow-up tower `π : Y → X(ℂ)` is biholomorphic to `V(ℂ)` for
  an integral smooth projective complex scheme `V` with `e : ℂ(X) ≃ ℂ(V)` compatible with
  meromorphic germs (`e q` at `v` is the pull-back of `q` along `π ∘ φ`) — the algebraic model of
  the modification;
* **`exists_admissibleFlag_lexEquivalent_of_hasRationalAlgebraization`**: if `X` is integral smooth
  projective and every blow-up tower of `X(ℂ)` has a rational algebraization, then for every
  valuation `ν : ℂ(X)^× → ℤⁿ_lex` with value group `ℤⁿ_lex` there are a blow-up tower `π : Y → X(ℂ)`
  (a modification of `X`), its algebraic model `V` (`V(ℂ) ≃ Y`, `ℂ(V) ≃ ℂ(X)`) and an admissible
  flag `Y•` on `V` with `ν ~ ν_{Y•}`: **`ν = ν_{Y•} G` for a unitriangular `G`**.

Proof: choose `u_k` with `ν(u_k) = e_k`; an analytic log resolution tower of the `u_k`
(`exists_tower_isLogResolutionGermAt`, Hironaka's principalization); its algebraic model `V`;
transport the log resolution data to `V(ℂ)`; conclude on `V` (lanes OF11/OF13,
`exists_admissibleFlag_lexEquivalent_of_isAnalyticLogResolution`).
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
open SGPT.Okounkov SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr SGPT.Okounkov.OF9
open scoped Topology Manifold ContDiff

/-! ### Biholomorphisms -/

section Diffeo

variable {n : ℕ} {Z Y : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- A biholomorphism is an analytic modification. -/
theorem isAnalyticModification_of_diffeomorph
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y) :
    IsAnalyticModification (n := n) φ := by
  refine ⟨φ.contMDiff, φ.toHomeomorph.isProperMap, ∅, ∅, φ.symm,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_, ?_,
    φ.symm.contMDiff.contMDiffOn, fun x _ => φ.apply_symm_apply x,
    fun z _ => φ.symm_apply_apply z⟩ <;> simp

/-- **Transport of log resolution data along a biholomorphism.** -/
theorem isLogResolutionGermAt_transport
    (φ : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y) (z : Z) {K : Type*} [Field K]
    {r : ℕ} (γ : K →+* FractionRing (NativeHolGerm n Y (φ z))) (u : Fin r → K)
    (h : IsLogResolutionGermAt (φ z) γ u) :
    IsLogResolutionGermAt z ((fracComap (isAnalyticModification_of_diffeomorph φ) z).comp γ) u := by
  classical
  obtain ⟨ℓ, hℓ, hspan, M, H, hH, hℓmem, hℓgen, η, a, haM, hu, hreg⟩ := h
  set hmod := isAnalyticModification_of_diffeomorph φ
  let c := NativeHolGerm.comap φ hmod.1 z
  have hφz : ∀ᶠ z' in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ z' :=
    Eventually.of_forall fun z' => φ.contMDiff z'
  have hψ : ∀ᶠ y' in 𝓝 (φ z),
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ.symm y' :=
    Eventually.of_forall fun y' => φ.symm.contMDiff y'
  have hℓ' : ∀ j, HolomorphicAt n (ℓ j ∘ φ) z := fun j => (hℓ j).comp_contMDiff hφz
  have hcmk : ∀ (f : Y → ℂ) (hf : HolomorphicAt n f (φ z)) (hf' : HolomorphicAt n (f ∘ φ) z),
      c (NativeHolGerm.mk f hf) = NativeHolGerm.mk (f ∘ φ) hf' := fun f hf hf' =>
    Subtype.ext (NativeHolGerm.comap_mk φ hmod.1 z f hf)
  -- the pull-back of germs is surjective
  have hcsurj : Function.Surjective c := by
    intro g
    obtain ⟨f, hf, rfl⟩ := NativeHolGerm.exists_eq_mk g
    have hf' : HolomorphicAt n (f ∘ φ.symm) (φ z) := by
      have h1 : HolomorphicAt n f (φ.symm (φ z)) := by rwa [φ.symm_apply_apply]
      exact h1.comp_contMDiff hψ
    refine ⟨NativeHolGerm.mk (f ∘ φ.symm) hf', ?_⟩
    rw [hcmk _ hf' (by
      have : (f ∘ φ.symm) ∘ φ = f := by funext w; simp
      rw [this]; exact hf)]
    apply NativeHolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => by simp
  have hloc : IsLocalHom c := by
    refine ⟨fun g hg => ?_⟩
    rw [NativeHolGerm.isUnit_iff_eval_ne_zero] at hg ⊢
    rwa [NativeHolGerm.eval_comap] at hg
  refine ⟨fun j => ℓ j ∘ φ, hℓ', ?_, M, fun j => φ ⁻¹' H j,
    fun j hj => AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage φ.contMDiff (hH j hj),
    fun j hj => ?_, fun j hj => ?_, fun k => Units.map c (η k), a, haM, fun k => ?_, fun k => ?_⟩
  · have h1 := congrArg (Ideal.map c) hspan
    rw [Ideal.map_span, IsLocalRing.map_maximalIdeal_of_surjective c hcsurj, ← Set.range_comp] at h1
    rw [← h1]
    congr 2
  · obtain ⟨-, hv⟩ := hℓmem j hj
    exact ⟨hℓ' j, φ.continuous.continuousAt.eventually hv⟩
  · intro f hf hfv
    have hf' : HolomorphicAt n (f ∘ φ.symm) (φ z) := by
      have h1 : HolomorphicAt n f (φ.symm (φ z)) := by rwa [φ.symm_apply_apply]
      exact h1.comp_contMDiff hψ
    have hfv' : (vanishingIdeal (n := n) (H j)).mem (φ z) (f ∘ φ.symm) := by
      refine ⟨hf', ?_⟩
      obtain ⟨-, hv⟩ := hfv
      have hv' : ∀ᶠ y' in 𝓝 (φ z), φ.symm y' ∈ φ ⁻¹' H j → f (φ.symm y') = 0 := by
        have hcont : Tendsto φ.symm (𝓝 (φ z)) (𝓝 z) := by
          have := φ.symm.continuous.continuousAt (x := φ z)
          rwa [ContinuousAt, φ.symm_apply_apply] at this
        exact hcont.eventually hv
      filter_upwards [hv'] with y' hy' hy'H
      exact hy' (by simp [hy'H])
    have hmem := hℓgen j hj _ hf' hfv'
    have h2 := Ideal.mem_map_of_mem c hmem
    rw [Ideal.map_span, Set.image_singleton] at h2
    have h3 : c (NativeHolGerm.mk (f ∘ φ.symm) hf') = NativeHolGerm.mk f hf := by
      rw [hcmk _ hf' (by
        have : (f ∘ φ.symm) ∘ φ = f := by funext w; simp
        rw [this]; exact hf)]
      apply NativeHolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun w => by simp
    rw [h3, hcmk _ _ (hℓ' j)] at h2
    exact h2
  · change fracComap hmod z (γ (u k)) = _
    rw [hu k, map_mul, map_prod, fracComap_algebraMap]
    simp only [map_zpow₀, fracComap_algebraMap]
    congr 1
  · rcases hreg k with ⟨g, hg⟩ | ⟨g, hg⟩
    · left
      refine ⟨c g, ?_⟩
      change fracComap hmod z (γ (u k)) = _
      rw [hg, fracComap_algebraMap]
    · right
      refine ⟨c g, ?_⟩
      change fracComap hmod z (γ (u k)⁻¹) = _
      rw [hg, fracComap_algebraMap]

end Diffeo

/-! ### Rational algebraizations of towers and the main theorem -/

section Algebraization

local instance of13fTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance of13fCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance of13fManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

/-- Log resolution data for the meromorphic germ map of a scheme are `IsAnalyticLogResolutionAt`. -/
theorem isAnalyticLogResolutionAt_of_isLogResolutionGermAt {V : Scheme.{0}} [IsIntegral V]
    {g : V ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n g] [IsSeparated g]
    [QuasiCompact g] {X : Scheme.{0}} [IsIntegral X] (e : X.functionField ≃+* V.functionField)
    (u : Fin n → X.functionField) (p : SchemeComplexPoint g)
    (h : IsLogResolutionGermAt p ((schemeNativeFunctionFieldGerm g n p).comp e.toRingHom) u) :
    IsAnalyticLogResolutionAt g n e u p := by
  obtain ⟨ℓ, hℓ, hspan, M, H, hH, hℓmem, hℓgen, η, a, haM, hu, hreg⟩ := h
  refine ⟨ℓ, hℓ, hspan, M, H, hH, hℓmem, hℓgen, η, a, haM, hu, fun k => ?_⟩
  rcases hreg k with hk | ⟨c, hc⟩
  · exact Or.inl hk
  · refine Or.inr ⟨c, ?_⟩
    rw [← map_inv₀ e]
    exact hc

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

/-- **A rational algebraization of a modification** `π : Y → X(ℂ)`: an integral smooth projective
complex scheme `V` with a biholomorphism `φ : V(ℂ) ≃ Y` and an identification `e : ℂ(X) ≃ ℂ(V)` of
function fields compatible with meromorphic germs (`e q` at `v` is the pull-back of `q` along
`π ∘ φ`). -/
def HasRationalAlgebraization {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {π : Y → SchemeComplexPoint f}
    (hπ : IsAnalyticModification (n := n) π) :
    Prop :=
  ∃ (V : Scheme.{0}) (_ : IsIntegral V) (g : V ⟶ Spec (.of ℂ))
    (hsm : SmoothOfRelativeDimension n g) (EV : ClosedProjectiveEmbedding g),
    letI := hsm
    letI := EV.isSeparated
    letI := EV.quasiCompact
    ∃ (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
      (e : X.functionField ≃+* V.functionField),
      ∀ (q : X.functionField) (v : SchemeComplexPoint g),
        schemeNativeFunctionFieldGerm g n v (e q) =
          fracComap (isAnalyticModification_of_diffeomorph φ) v (ratGerm f hπ (φ v) q)

/-- **`rmk:Abhyankar`, existence ([CFKLRS17, Thm 2.9]), modulo rational algebraizations of blow-up
towers.** Let `X` be an integral smooth projective complex scheme of dimension `n` all of whose
blow-up towers `π : Y → X(ℂ)` have rational algebraizations. Then every valuation
`ν : ℂ(X)^× → ℤⁿ_lex` with value group `ℤⁿ_lex` is equivalent to the valuation of an admissible flag
on a modification of `X`: there are a blow-up tower `π : Y → X(ℂ)` (a modification, `def:modif`),
its algebraic model `V` (`φ : V(ℂ) ≃ Y`, `e : ℂ(X) ≃ ℂ(V)` compatible with `π ∘ φ`) and an
admissible flag `Y•` on `V` with `ν = ν_{Y•} G`, `G` unit upper triangular. -/
theorem exists_admissibleFlag_lexEquivalent_of_hasRationalAlgebraization
    (E : ClosedProjectiveEmbedding f)
    (halg : ∀ (Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
      [IsComplexManifold n Y] (π : Y → SchemeComplexPoint f)
      (hseq : IsBlowupSequence n (SchemeComplexPoint f) Y π),
      HasRationalAlgebraization f n
        (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq))
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hν : Function.Surjective ν) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → SchemeComplexPoint f)
      (hseq : IsBlowupSequence n (SchemeComplexPoint f) Y π)
      (V : Scheme.{0}) (_ : IsIntegral V) (g : V ⟶ Spec (.of ℂ))
      (hsm : SmoothOfRelativeDimension n g) (EV : ClosedProjectiveEmbedding g),
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      ∃ (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
        (e : X.functionField ≃+* V.functionField),
        (∀ (q : X.functionField) (v : SchemeComplexPoint g),
          schemeNativeFunctionFieldGerm g n v (e q) =
            fracComap (isAnalyticModification_of_diffeomorph φ) v
              (ratGerm f (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq)
                (φ v) q)) ∧
        ∃ (Yf : Fin (n + 1) → Set V) (hY : IsAdmissibleFlag g n Yf),
          ValuationsLexEquivalent ((admissibleFlagValuation hY).comap e.toRingHom) ν := by
  classical
  have hu : ∀ k : Fin n, ∃ q, ν q = basisValue k := fun k => hν _
  choose u hνu using hu
  have hu0 : ∀ k, u k ≠ 0 := fun k h => by
    have := hνu k
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  obtain ⟨Y, tY, cY, mY, π, hseq, hres⟩ := exists_tower_isLogResolutionGermAt f n E u hu0
  obtain ⟨V, hV, g, hsm, EV, hrest⟩ := halg Y π hseq
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  obtain ⟨φ, e, hcompat⟩ := hrest
  have hres' : ∀ v : SchemeComplexPoint g, IsAnalyticLogResolutionAt g n e u v := by
    intro v
    apply isAnalyticLogResolutionAt_of_isLogResolutionGermAt
    have h := isLogResolutionGermAt_transport φ v _ u (hres (φ v))
    have heq : (fracComap (isAnalyticModification_of_diffeomorph φ) v).comp
        (ratGerm f (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) (φ v)) =
        (schemeNativeFunctionFieldGerm g n v).comp e.toRingHom := by
      ext q
      exact (hcompat q v).symm
    rwa [heq] at h
  obtain ⟨Yf, hY, -, hlex⟩ :=
    exists_admissibleFlag_lexEquivalent_of_isAnalyticLogResolution EV e ν hν u hνu hres'
  exact ⟨Y, tY, cY, mY, π, hseq, V, hV, g, hsm, EV, φ, e, hcompat, Yf, hY, hlex⟩

end Algebraization

end SGPT.Okounkov.OF13
