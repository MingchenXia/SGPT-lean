import SGPT.Okounkov.OF2AbhyankarFlagExample
import SGPT.Okounkov.OF9BlowupRationalEmbedding
import SGPT.Okounkov.OF13RationalRep
import SGPT.Okounkov.OF13Principalize

/-!
# `rmk:Abhyankar`: the rational functions of `X` are ratios on every blow-up tower

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (existence part of
[CFKLRS17, Thm 2.9]); `def:modif` (a modification is a finite composition of blow-ups with smooth
centres).

Lane OF9 proved that every blow-up tower `π : M → X(ℂ)` of an integral smooth projective `X` has a
holomorphic embedding `Ψ : M ↪ ℙᴺ` all of whose ratios `A(Ψ)/B(Ψ)` (homogeneous of the same
degree) are pull-backs `π^* q` of rational functions `q ∈ ℂ(X)` (`OF9.IsRationalEmbedding`).  Here
we prove the converse inclusion, so that `ℂ(X)` is **exactly** the field of ratios of `Ψ`:

* `IsGeneratingEmbedding`: every `q ∈ ℂ(X)` is a ratio: `π^* q · B(Ψ) = A(Ψ)` as meromorphic germs
  at every point, in every affine chart, with `B ∘ Ψ` not identically zero;
* `segrePull_rename_segreColumn`: the column `l` of the Segre coordinates, `A ↦ A(x_{(·,l)})`,
  reads on `ℙᴺ` as `P_l^d · A` (`z_{(a,l)} = x_a P_l(x)`);
* `isGeneratingEmbedding_projectivePoint`: the base `X(ℂ) ⊆ ℙᴺ` (`q = P(x/x_l)/Q(x/x_l)`, lane
  OF13's `exists_homogeneous_ratio`);
* `isGeneratingEmbedding_blowupEmbedding`: the blow-up embedding of a generating embedding is
  generating: `q = A/B` on `M` gives `q = A(x_{(·,l)})/B(x_{(·,l)})` on the blow-up, for a column
  `l` with `P_l(Ψ y) ≠ 0` at a point `y` off the centre where `B(Ψ y) ≠ 0`;
* **`exists_isRationalEmbedding_and_isGeneratingEmbedding`**: every blow-up tower of `X(ℂ)` has a
  projective embedding which is both rational and generating.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF14

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.OF9
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open scoped Topology Manifold ContDiff

/-! ### One column of the Segre coordinates -/

section Segre

variable {N r : ℕ}

/-- The column `l` of the Segre coordinates: `x_a ↦ x_{(a,l)}`. -/
def segreColumn (N r : ℕ) (l : Fin (r + 1)) (a : Fin (N + 1)) : Fin (segreDim N r + 1) :=
  (segreIdx N r).symm (a, l)

/-- `A(x_{(·,l)})` read on `ℙᴺ` through `[P]` is `P_l^d · A`. -/
theorem segrePull_rename_segreColumn (P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ)
    (l : Fin (r + 1)) {d : ℕ} {A : MvPolynomial (Fin (N + 1)) ℂ} (hA : A.IsHomogeneous d) :
    segrePull P (MvPolynomial.rename (segreColumn N r l) A) = P l ^ d * A := by
  apply MvPolynomial.funext
  intro v
  rw [eval_segrePull, MvPolynomial.eval_rename, map_mul, map_pow]
  have h : (segreVec v fun b => MvPolynomial.eval v (P b)) ∘ segreColumn N r l =
      MvPolynomial.eval v (P l) • v := by
    funext a
    simp only [Function.comp, segreColumn, segreVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, SGPT.GAGA.PN.eval_smul_of_isHomogeneous hA]

end Segre

/-! ### Germs of polynomials -/

section Germs

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- A homogeneous polynomial with a nonzero germ along `Ψ` does not vanish on `Ψ(M)`. -/
theorem exists_eval_ne_zero_of_polyGerm_ne_zero {N d : ℕ} {Ψ : M → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {y : M} {i : Fin (N + 1)}
    (hi : Ψ y ∈ (affineChart i).source) {B : MvPolynomial (Fin (N + 1)) ℂ}
    (hB : B.IsHomogeneous d) (h : polyGerm hΨ hi B ≠ 0) :
    ∃ y', MvPolynomial.eval (Ψ y').rep B ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  have hsrc : ∀ᶠ y' in 𝓝 y, Ψ y' ∈ (affineChart i).source :=
    hΨ.continuous.continuousAt.eventually ((affineChart i).open_source.mem_nhds hi)
  have h0 : genFun Ψ i B =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hsrc] with y' hy'
    exact (eval_rep_eq_zero_iff_genFun Ψ i hy' hB).mp (hcon y')
  change NativeHolGerm.mk _ _ = NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0)
  exact NativeHolGerm.mk_eq_mk_iff.mpr h0

end Germs

/-! ### Generating embeddings -/

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of14TrTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of14TrCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of14TrManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Generating embeddings.** A holomorphic embedding `Ψ : M → ℙᴺ` of a model `ρ : M → X(ℂ)`
*generates* `ℂ(X)` if every rational function of `X` is a ratio of `Ψ`: for every `q ∈ ℂ(X)` there
are homogeneous `A, B` of the same degree, `B ∘ Ψ` not identically zero, with
`ρ^* q · B(Ψ) = A(Ψ)` as meromorphic germs at every point of `M`, in every affine chart. -/
def IsGeneratingEmbedding [CompactSpace M] {ρ : M → SchemeComplexPoint f}
    (hρ : IsAnalyticModification (n := n) ρ) {N : ℕ} {Ψ : M → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) : Prop :=
  ∀ q : X.functionField, ∃ (d : ℕ) (A B : MvPolynomial (Fin (N + 1)) ℂ),
    A.IsHomogeneous d ∧ B.IsHomogeneous d ∧ (∃ y, MvPolynomial.eval (Ψ y).rep B ≠ 0) ∧
    ∀ (y : M) (i : Fin (N + 1)) (hi : Ψ y ∈ (affineChart i).source),
      ratGerm f hρ y q * algebraMap _ (FractionRing (NativeHolGerm n M y)) (polyGerm hΨ hi B) =
        algebraMap _ (FractionRing (NativeHolGerm n M y)) (polyGerm hΨ hi A)

variable (E : ClosedProjectiveEmbedding f)

/-- **The base is generating**: every rational function of `X` is `P(x)/Q(x)` on `X(ℂ) ⊆ ℙᴺ`. -/
theorem isGeneratingEmbedding_projectivePoint
    (hid : IsAnalyticModification (n := n) (id : SchemeComplexPoint f → SchemeComplexPoint f)) :
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IsGeneratingEmbedding f hid (isHolomorphicEmbedding_projectivePoint f E n) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro q
  obtain ⟨d, A, B, hA, hB, hrel⟩ := OF13.exists_homogeneous_ratio f E q
  refine ⟨d, A, B, hA, hB, ?_, fun y i hi => ?_⟩
  · obtain ⟨y₀⟩ := OF2.nonempty_schemeComplexPoint f E
    have hi₀ := mem_affineChart_chartIndex (projectivePoint f E n y₀)
    have hx₀ := (projectivePoint_mem_source_iff f E n _ y₀).mp hi₀
    have hg₀ := genericPoint_mem_coordOpen f E hx₀
    refine exists_eval_ne_zero_of_polyGerm_ne_zero (isHolomorphicEmbedding_projectivePoint f E n) hi₀ hB fun h0 => (hrel _ hg₀).1 ?_
    apply schemeNativeFunctionFieldGerm_injective f n y₀
    rw [schemeNativeFunctionFieldGerm_polyFF f E _ hg₀ B y₀ hi₀, h0, map_zero, map_zero]
  · have hx := (projectivePoint_mem_source_iff f E n i y).mp hi
    have hg := genericPoint_mem_coordOpen f E hx
    rw [ratGerm_id, ← schemeNativeFunctionFieldGerm_polyFF f E i hg B y hi,
      ← schemeNativeFunctionFieldGerm_polyFF f E i hg A y hi, ← map_mul, (hrel i hg).2]

/-- **The blow-up embedding of a generating embedding is generating.** -/
theorem isGeneratingEmbedding_blowupEmbedding [CompactSpace M] {ρ : M → SchemeComplexPoint f}
    (hρ : IsAnalyticModification (n := n) ρ) {N : ℕ} {Ψ : M → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (hG : IsGeneratingEmbedding f hρ hΨ)
    {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace Z] {C : Set M} {g : Z → M} {r m : ℕ}
    {P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ} (hd : BlData n m Ψ C g P)
    (hρg : IsAnalyticModification (n := n) (ρ ∘ g)) :
    IsGeneratingEmbedding f hρg (isHolomorphicEmbedding_blowupEmbedding hd) := by
  classical
  have hg : IsAnalyticModification (n := n) g :=
    PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hd.blowup
  have hΨ' := isHolomorphicEmbedding_blowupEmbedding hd
  intro q
  obtain ⟨d, A, B, hA, hB, ⟨y₁, hy₁⟩, hrel⟩ := hG q
  have hCcl : IsClosed C := hd.blowup.1.1
  have hCint : interior C = ∅ := hd.blowup.2.1
  obtain ⟨Ae, Be, s, -, -, -, -, -, hBeint, -, -, hsec, -⟩ := hg.2.2
  -- a point `y₂` off the centre and off the exceptional image where `B ∘ Ψ` does not vanish
  set i₁ := chartIndex (Ψ y₁)
  have hi₁ : Ψ y₁ ∈ (affineChart i₁).source := mem_affineChart_chartIndex _
  have hG₁ : genFun Ψ i₁ B y₁ ≠ 0 :=
    fun h0 => hy₁ ((eval_rep_eq_zero_iff_genFun Ψ i₁ hi₁ hB).mpr h0)
  have hW : ∀ᶠ y in 𝓝 y₁, Ψ y ∈ (affineChart i₁).source ∧ genFun Ψ i₁ B y ≠ 0 :=
    (hΨ.continuous.continuousAt.eventually ((affineChart i₁).open_source.mem_nhds hi₁)).and
      ((holomorphicAt_genFun hΨ hi₁ B).continuousAt.eventually_ne hG₁)
  obtain ⟨W, hWsub, hWo, hy₁W⟩ := mem_nhds_iff.mp hW
  have hint : interior (C ∪ Be) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hCcl hBeint, hCint]
  obtain ⟨y₂, hy₂W, hy₂⟩ : ∃ y₂ ∈ W, y₂ ∉ C ∪ Be := by
    by_contra hcon
    push Not at hcon
    have hsub : W ⊆ interior (C ∪ Be) := interior_maximal hcon hWo
    rw [hint] at hsub
    exact hsub hy₁W
  have hy₂C : y₂ ∉ C := fun h => hy₂ (Or.inl h)
  have hy₂B : y₂ ∉ Be := fun h => hy₂ (Or.inr h)
  have hBy₂ : MvPolynomial.eval (Ψ y₂).rep B ≠ 0 := fun h0 =>
    (hWsub hy₂W).2 ((eval_rep_eq_zero_iff_genFun Ψ i₁ (hWsub hy₂W).1 hB).mp h0)
  -- a column `l` of the Segre embedding not vanishing at `y₂` (`y₂` is off the centre)
  obtain ⟨l, hl⟩ : ∃ l, MvPolynomial.eval (Ψ y₂).rep (P l) ≠ 0 := by
    have hi₂ : Ψ y₂ ∈ (affineChart (chartIndex (Ψ y₂))).source := mem_affineChart_chartIndex _
    have hOffCentre : ∀ᶠ y in 𝓝 y₂, y ∉ C :=
      hCcl.isOpen_compl.mem_nhds hy₂C
    have h1 : (vanishingIdeal (n := n) C).mem y₂ (fun _ => (1 : ℂ)) :=
      ⟨holomorphicAt_const 1, hOffCentre.mono fun y hy hyC => absurd hyC hy⟩
    obtain ⟨c, -, hc⟩ := (genFun_mem_and_generate hd hi₂).2 _ h1
    by_contra hcon
    push Not at hcon
    have h2 := hc.self_of_nhds
    change (1 : ℂ) = ∑ k, c k y₂ * genFun Ψ (chartIndex (Ψ y₂)) (P k) y₂ at h2
    rw [Finset.sum_eq_zero fun k _ => by
      rw [(eval_rep_eq_zero_iff_genFun Ψ _ hi₂ (hd.hom k)).mp (hcon k), mul_zero]] at h2
    exact one_ne_zero h2
  have hA' : (MvPolynomial.rename (segreColumn N r l) A).IsHomogeneous d :=
    hA.rename_isHomogeneous
  have hB' : (MvPolynomial.rename (segreColumn N r l) B).IsHomogeneous d :=
    hB.rename_isHomogeneous
  refine ⟨d, MvPolynomial.rename (segreColumn N r l) A, MvPolynomial.rename (segreColumn N r l) B,
    hA', hB', ?_, fun z i' hi' => ?_⟩
  · -- `B(x_{(·,l)})` does not vanish at the point of the blow-up over `y₂`
    have hgz : g (s y₂) = y₂ := hsec y₂ hy₂B
    have hi₂' : blowupEmbedding Ψ g P (s y₂) ∈
        (affineChart (chartIndex (blowupEmbedding Ψ g P (s y₂)))).source :=
      mem_affineChart_chartIndex _
    obtain ⟨-, h, S, -, -, -, -, -, -, hrelz⟩ := exists_local_segre hd (s y₂) hi₂'
    have hsrc : Ψ (g (s y₂)) ∈ (affineChart (chartIndex (Ψ (g (s y₂))))).source :=
      mem_affineChart_chartIndex _
    have hne : genFun Ψ (chartIndex (Ψ (g (s y₂))))
        (segrePull P (MvPolynomial.rename (segreColumn N r l) B)) (g (s y₂)) ≠ 0 := by
      intro h0
      have h3 := (eval_rep_eq_zero_iff_genFun Ψ _ hsrc (isHomogeneous_segrePull hd.hom hB')).mpr h0
      rw [segrePull_rename_segreColumn P l hB, map_mul, map_pow, hgz] at h3
      exact mul_ne_zero (pow_ne_zero _ hl) hBy₂ h3
    refine ⟨s y₂, fun h0 => hne ?_⟩
    have hz := (hrelz d _ hB').self_of_nhds
    rw [(eval_rep_eq_zero_iff_genFun _ _ hi₂' hB').mp h0, mul_zero] at hz
    exact hz
  · -- the germ identity at `z`
    obtain ⟨U, h, S, hU, hzU, hnon, hh, hS, hS0, hseg⟩ := exists_local_segre hd z hi'
    set i := chartIndex (Ψ (g z))
    have hi : Ψ (g z) ∈ (affineChart i).source := mem_affineChart_chartIndex _
    have key := congrArg (fracComap hg z) (hrel (g z) i hi)
    rw [map_mul, fracComap_algebraMap, fracComap_algebraMap, ← ratGerm_comp f hρ hg hρg] at key
    let H : NativeHolGerm n Z z :=
      NativeHolGerm.mk (fun y => (h y * S y) ^ d) (by
        have h1 := hh.mul hS
        filter_upwards [h1] with y hy
        exact hy.pow d)
    have hcom : ∀ A₀ : MvPolynomial (Fin (N + 1)) ℂ, A₀.IsHomogeneous d →
        H * polyGerm hΨ' hi' (MvPolynomial.rename (segreColumn N r l) A₀) =
          NativeHolGerm.comap g hg.1 z (polyGerm hΨ hi (P l)) ^ d *
            NativeHolGerm.comap g hg.1 z (polyGerm hΨ hi A₀) := by
      intro A₀ hA₀
      have e1 : NativeHolGerm.comap g hg.1 z
          (polyGerm hΨ hi (segrePull P (MvPolynomial.rename (segreColumn N r l) A₀))) =
          H * polyGerm hΨ' hi' (MvPolynomial.rename (segreColumn N r l) A₀) := by
        apply Subtype.ext
        change ((genFun Ψ i (segrePull P (MvPolynomial.rename (segreColumn N r l) A₀)) ∘ g :
            Z → ℂ) : Germ (𝓝 z) ℂ) =
          ((fun y => (h y * S y) ^ d *
            genFun (blowupEmbedding Ψ g P) i' (MvPolynomial.rename (segreColumn N r l) A₀) y :
              Z → ℂ) : Germ (𝓝 z) ℂ)
        exact Germ.coe_eq.mpr (hseg d _ hA₀.rename_isHomogeneous)
      rw [← e1, segrePull_rename_segreColumn P l hA₀, OF13.polyGerm_mul, OF13.polyGerm_pow,
        map_mul, map_pow]
    have hH0 : H ≠ 0 := by
      intro hH
      have h0 : (fun y => (h y * S y) ^ d) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        have : H = NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0) := hH
        exact NativeHolGerm.mk_eq_mk_iff.mp this
      have hev := h0.and (hS.continuousAt.eventually_ne hS0)
      obtain ⟨W', hW'sub, hW'open, hzW'⟩ := mem_nhds_iff.mp hev
      obtain ⟨y, hyW, hy⟩ := hnon (W' ∩ U) (hW'open.inter hU) inter_subset_right ⟨z, hzW', hzU⟩
      obtain ⟨e1, e2⟩ := hW'sub hyW.1
      exact pow_ne_zero d (mul_ne_zero hy e2) e1
    have hHf : algebraMap (NativeHolGerm n Z z) (FractionRing (NativeHolGerm n Z z)) H ≠ 0 :=
      fun h0 => hH0 (IsFractionRing.injective _ (FractionRing (NativeHolGerm n Z z))
        (h0.trans (map_zero _).symm))
    have eA := congrArg (algebraMap (NativeHolGerm n Z z) (FractionRing (NativeHolGerm n Z z)))
      (hcom A hA)
    have eB := congrArg (algebraMap (NativeHolGerm n Z z) (FractionRing (NativeHolGerm n Z z)))
      (hcom B hB)
    rw [map_mul, map_mul, map_pow] at eA eB
    apply mul_left_cancel₀ hHf
    calc algebraMap _ _ H * (ratGerm f hρg z q *
          algebraMap _ _ (polyGerm hΨ' hi' (MvPolynomial.rename (segreColumn N r l) B)))
        = ratGerm f hρg z q * (algebraMap _ _ H *
          algebraMap _ _ (polyGerm hΨ' hi' (MvPolynomial.rename (segreColumn N r l) B))) := by
          ring
      _ = algebraMap _ (FractionRing (NativeHolGerm n Z z))
            (NativeHolGerm.comap g hg.1 z (polyGerm hΨ hi (P l))) ^ d *
          (ratGerm f hρg z q * algebraMap _ _ (NativeHolGerm.comap g hg.1 z (polyGerm hΨ hi B))) := by
          rw [eB]
          ring
      _ = algebraMap _ (FractionRing (NativeHolGerm n Z z))
            (NativeHolGerm.comap g hg.1 z (polyGerm hΨ hi (P l))) ^ d *
          algebraMap _ _ (NativeHolGerm.comap g hg.1 z (polyGerm hΨ hi A)) := by
          rw [key]
      _ = algebraMap _ _ H *
          algebraMap _ _ (polyGerm hΨ' hi' (MvPolynomial.rename (segreColumn N r l) A)) := by
          rw [eA]

include E in
/-- **Blow-up towers of `X(ℂ)` have rational and generating projective embeddings.** Every
finite sequence of blow-ups with smooth centres `π : M → X(ℂ)` of an integral smooth projective
complex scheme `X` is compact and admits a holomorphic embedding `Ψ : M ↪ ℙᴺ` such that `ℂ(X)`,
pulled back to `M`, is exactly the field of ratios `A(Ψ)/B(Ψ)` of homogeneous polynomials of the
same degree: every ratio is the pull-back of a rational function (`OF9.IsRationalEmbedding`) and
every rational function is a ratio (`IsGeneratingEmbedding`). -/
theorem exists_isRationalEmbedding_and_isGeneratingEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {π : M → SchemeComplexPoint f} (hπ : IsBlowupSequence n (SchemeComplexPoint f) M π) :
    CompactSpace M ∧ ∃ (N : ℕ) (Ψ : M → ComplexProjectiveSpace N)
      (hΨ : IsHolomorphicEmbedding (n := n) Ψ), ∀ [CompactSpace M],
        IsRationalEmbedding f (isAnalyticModification_of_isBlowupSequence hπ) hΨ ∧
          IsGeneratingEmbedding f (isAnalyticModification_of_isBlowupSequence hπ) hΨ := by
  induction hπ with
  | refl =>
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    exact ⟨E.analyticCompact, _, projectivePoint f E n,
      isHolomorphicEmbedding_projectivePoint f E n,
      ⟨isRationalEmbedding_projectivePoint f E _, isGeneratingEmbedding_projectivePoint f E _⟩⟩
  | step ρ C g hρ hg ih =>
    obtain ⟨hc, N, Ψ, hΨ, hRG⟩ := ih
    have := hc
    obtain ⟨hR, hG⟩ := hRG
    obtain ⟨r, m, P, hd⟩ := exists_blData hΨ hg
    have hZ := BlowupCompact.compactSpace_of_isBlowupAlong hg
    exact ⟨hZ, _, _, isHolomorphicEmbedding_blowupEmbedding hd,
      ⟨isRationalEmbedding_blowupEmbedding f (isAnalyticModification_of_isBlowupSequence hρ) hΨ
          hR hd _,
        isGeneratingEmbedding_blowupEmbedding f (isAnalyticModification_of_isBlowupSequence hρ) hΨ
          hG hd _⟩⟩

end Scheme

end SGPT.Okounkov.OF14
