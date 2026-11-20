import SGPT.GAGA.CohCircle
import SGPT.NAPotential.GAGAMultSiuGerms
import SGPT.Trace.DirectImgFibre
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem
import SGPT.Foundations.Analysis.Pending.StepFourNoComponentContainsW
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient
import SGPT.Foundations.Analysis.Pending.ConstantRankImage

/-!
# Invariant coherent ideals are determined by their restrictions to a dense set of fibres

Infrastructure of lane COHERENT (source `lma:fibIeq`, `chapter_trace.tex` lines 1166--1193;
blueprint `claude-coherent.tex`, node `claude-coherent:rigidity`).

Let `X` be a complex manifold with a `C¹` circle action `σ` by biholomorphisms, and
`f : X → Δ*` holomorphic and proper, equivariant for rotations: `f(σ_θ x) = e^{iθ} f(x)`.
Let `t = f(·)₀ : X → ℂ` be the coordinate of `f`, so that the fibre `X_z` is cut out by `t - z`.

* `generator_coord`: `D t = i t`; in particular `D (t - z)` is a unit at every point of `X`.
* `stalkIdeal_eq_of_sup_eq` (**local rigidity**): if `I, I'` are coherent invariant ideals and
  `I_y + (t - z) = I'_y + (t - z)` at a point `y` of `X_z`, then `I_y = I'_y`
  (`SGPT.GAGA.Coherent.eq_of_le_sup_span` applied to `J = I + I'`, stable under the generator).
* `stalkIdeal_eq_of_dense` (**global rigidity**): if this holds along `X_z` for a dense set of
  `z`, then `I = I'`. The set `B` of points where the stalks differ is the analytic set
  `V(I' : I) ∪ V(I : I')` (Oka), it is invariant, and it misses the fibres over a dense set;
  its image `f(B)` is analytic (Remmert) with empty interior, hence discrete, and invariant
  under rotations, hence empty.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace SGPT.GAGA.Coherent

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  SGPT.Okounkov SGPT.PSH.IdealRestriction

/-! ### Membership and stalks of coherent ideals -/

namespace CoherentIdeal

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {J : GermIdeal n X}

/-- For a coherent ideal, a germ lies in the stalk ideal iff the function is a member. -/
theorem mem_of_mk_mem_stalkIdeal (hJ : J.IsCoherent) {x : X} {g : X → ℂ}
    (hg : HolomorphicAt n g x) (h : NativeHolGerm.mk g hg ∈ stalkIdeal J x) : J.mem x g := by
  obtain ⟨U, -, hxU, N, s, -, hgen⟩ := hJ x
  have hsp : IsInSpanAt (n := n) (J.mem x) x g :=
    SGPT.NAPotential.GAGAMult.isInSpanAt_of_mk_mem_spanGerms hg h
  obtain ⟨-, K, t, a, ht, ha, heq⟩ := hsp
  have hsum : IsInSpanAt (n := n) (· ∈ range s) x (fun y => ∑ i, a i y * t i y) :=
    RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun i _ =>
      RelativePrincipalizationSpan.IsInSpanAt.mul_left (ha i) ((hgen x hxU _).1 (ht i))
  exact (hgen x hxU g).2 (CoherentIdealColon.isInSpanAt_range_congr (fun _ => EventuallyEq.rfl)
    heq.symm hsum)

/-- Inclusion of stalks of coherent ideals is inclusion of members. -/
theorem stalkIdeal_le_iff {I : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) (x : X) :
    stalkIdeal I x ≤ stalkIdeal J x ↔ ∀ g, I.mem x g → J.mem x g := by
  constructor
  · intro h g hg
    have hhol : HolomorphicAt n g x := holomorphicAt_of_mem hI hg
    exact mem_of_mk_mem_stalkIdeal hJ hhol
      (h (SGPT.NAPotential.GAGAMult.mk_mem_stalkIdeal hhol hg))
  · intro h
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, hg, hmem, rfl⟩
    exact SGPT.NAPotential.GAGAMult.mk_mem_stalkIdeal hg (h g hmem)

/-- Coherent ideals with the same stalks are equal. -/
theorem eq_of_stalkIdeal_eq {I : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (h : ∀ x, stalkIdeal I x = stalkIdeal J x) : I = J := by
  ext x g
  exact ⟨(stalkIdeal_le_iff hI hJ x).1 (h x).le g, (stalkIdeal_le_iff hJ hI x).1 (h x).ge g⟩

/-- **The non-inclusion locus is the zero locus of the colon ideal**: `x ∈ V(J : I)` iff
`I_x ⊄ J_x`. -/
theorem mem_zeroLocus_colon_iff {I : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (x : X) : x ∈ (InvertibleIdealQuotient.colon J I).zeroLocus ↔
      ¬ stalkIdeal I x ≤ stalkIdeal J x := by
  rw [stalkIdeal_le_iff hI hJ x]
  constructor
  · intro hz hle
    have h1 : (InvertibleIdealQuotient.colon J I).mem x (fun _ => (1 : ℂ)) := by
      refine ⟨holomorphicAt_const 1, fun g hg => ?_⟩
      have : (fun y => g y * (1 : ℂ)) = g := funext fun y => mul_one _
      rw [this]
      exact hle g hg
    exact one_ne_zero (hz _ h1)
  · intro hnle
    by_contra hz
    simp only [GermIdeal.zeroLocus, Set.mem_ofPred_eq, not_forall] at hz
    obtain ⟨c, hc, hcx⟩ := hz
    apply hnle
    intro g hg
    have hch : HolomorphicAt n c x := hc.1
    have hgc : J.mem x (fun y => g y * c y) := hc.2 g hg
    have hinv : HolomorphicAt n (fun y => (c y)⁻¹) x :=
      RelativePrincipalizationSpan.holomorphicAt_inv hch hcx
    obtain ⟨U, -, hxU, N, s, -, hgen⟩ := hJ x
    have h2 := RelativePrincipalizationSpan.IsInSpanAt.mul_left hinv ((hgen x hxU _).1 hgc)
    refine (hgen x hxU g).2 (CoherentIdealColon.isInSpanAt_range_congr (fun _ => EventuallyEq.rfl)
      ?_ h2)
    have hcne : ∀ᶠ y in 𝓝 x, c y ≠ 0 :=
      hch.self_of_nhds.continuousAt.eventually_ne hcx
    filter_upwards [hcne] with y hy
    field_simp

end CoherentIdeal

/-! ### The punctured disc and the coordinate of `f` -/

/-- The punctured unit disc `Δ* = {0 < |z| < 1} ⊆ ℂ¹`, an open subset of `ℂ¹`. -/
def puncturedDisc : TopologicalSpace.Opens (ComplexModel 1) :=
  ⟨{z | 0 < ‖z‖ ∧ ‖z‖ < 1}, (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)⟩

theorem mem_puncturedDisc {z : ComplexModel 1} : z ∈ puncturedDisc ↔ 0 < ‖z‖ ∧ ‖z‖ < 1 :=
  Iff.rfl

/-- On `ℂ¹` the norm is the modulus of the coordinate. -/
theorem norm_complexModel_one (z : ComplexModel 1) : ‖z‖ = ‖z 0‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]

/-- The rotation `z ↦ e^{iθ} z` preserves the norm. -/
theorem norm_rotate (θ : ℝ) (z : ComplexModel 1) :
    ‖Complex.exp (θ * Complex.I) • z‖ = ‖z‖ := by
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- The coordinate `t = f(·)₀ : X → ℂ` of a map `f : X → Δ*`. -/
def coord (f : X → puncturedDisc) (x : X) : ℂ := ((f x : ComplexModel 1)) 0

theorem coord_ne_zero (f : X → puncturedDisc) (x : X) : coord f x ≠ 0 := by
  intro h
  have h1 := ((f x).2 : (f x : ComplexModel 1) ∈ puncturedDisc).1
  rw [norm_complexModel_one] at h1
  simp only [coord] at h
  rw [h, norm_zero] at h1
  exact lt_irrefl _ h1

/-- A map `f : X → Δ*` is **rotation-equivariant** for the circle action `σ`:
`f(σ_θ x) = e^{iθ} f(x)`. -/
def IsRotationEquivariant (σ : CircleAction n X) (f : X → puncturedDisc) : Prop :=
  ∀ (θ : ℝ) (x : X), (f (σ.act θ x) : ComplexModel 1) =
    Complex.exp (θ * Complex.I) • (f x : ComplexModel 1)

theorem coord_act {σ : CircleAction n X} {f : X → puncturedDisc}
    (hf : IsRotationEquivariant σ f) (θ : ℝ) (x : X) :
    coord f (σ.act θ x) = Complex.exp (θ * Complex.I) * coord f x := by
  simp only [coord, hf θ x, PiLp.smul_apply, smul_eq_mul]

/-- `D t = i t`. -/
theorem generator_coord {σ : CircleAction n X} {f : X → puncturedDisc}
    (hf : IsRotationEquivariant σ f) (x : X) :
    σ.generator (coord f) x = Complex.I * coord f x := by
  have hfun : (fun θ : ℝ => coord f (σ.act θ x)) =
      fun θ : ℝ => Complex.exp (θ * Complex.I) * coord f x := funext fun θ => coord_act hf θ x
  have hd : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I) * coord f x)
      (Complex.exp ((0 : ℝ) * Complex.I) * (1 * Complex.I) * coord f x) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp).mul_const _
  rw [CircleAction.generator, hfun, hd.deriv]
  simp

/-- `D (t - c) = D t`. -/
theorem generator_sub_const (σ : CircleAction n X) (F : X → ℂ) (c : ℂ) (x : X) :
    σ.generator (fun p => F p - c) x = σ.generator F x := by
  simp only [CircleAction.generator]
  exact deriv_sub_const c

variable [IsComplexManifold n X]

/-- The coordinate of a holomorphic `f : X → Δ*` is holomorphic. -/
theorem holomorphicAt_coord {f : X → puncturedDisc}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f) (x : X) :
    HolomorphicAt n (coord f) x := by
  have hb : HolomorphicAt 1 (fun w : ComplexModel 1 => w 0) ((f x : ComplexModel 1)) := by
    refine Eventually.of_forall fun w => ?_
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).differentiableAt
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞
      (fun x => ((f x : puncturedDisc) : ComplexModel 1)) :=
    contMDiff_subtype_val.comp hf
  exact HolomorphicAt.comp_contMDiff (f := fun x => ((f x : puncturedDisc) : ComplexModel 1)) hb
    (Eventually.of_forall fun y => hval y)

/-- The equation `t - z` of the fibre `X_z`, holomorphic. -/
theorem holomorphicAt_fibreEquation {f : X → puncturedDisc}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f) (c : ℂ) (x : X) :
    HolomorphicAt n (fun p => coord f p - c) x :=
  (holomorphicAt_coord hf x).add (holomorphicAt_const (-c)) |>.congr
    (Eventually.of_forall fun p => by ring)

/-! ### Local rigidity -/

theorem isUnit_natCast_add_one (x : X) (k : ℕ) : IsUnit ((k : NativeHolGerm n X x) + 1) := by
  rw [NativeHolGerm.isUnit_iff_eval_ne_zero, map_add, map_natCast, map_one]
  exact_mod_cast Nat.succ_ne_zero k

/-- **Local rigidity.** Let `I, I'` be coherent ideals invariant under the circle action, `f`
rotation-equivariant and holomorphic, `y ∈ X` with `t(y) = c`. If
`I_y + (t - c) = I'_y + (t - c)`, then `I_y = I'_y`. -/
theorem stalkIdeal_eq_of_sup_eq (σ : CircleAction n X) {f : X → puncturedDisc}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hequiv : IsRotationEquivariant σ f) {I I' : GermIdeal n X} (hI : I.IsCoherent)
    (hI' : I'.IsCoherent) (hinvI : σ.IsInvariantIdeal I) (hinvI' : σ.IsInvariantIdeal I')
    {y : X}
    (h : stalkIdeal I y ⊔ Ideal.span {NativeHolGerm.mk _ (holomorphicAt_fibreEquation hf
        (coord f y) y)} =
      stalkIdeal I' y ⊔ Ideal.span {NativeHolGerm.mk _ (holomorphicAt_fibreEquation hf
        (coord f y) y)}) :
    stalkIdeal I y = stalkIdeal I' y := by
  set s := NativeHolGerm.mk _ (holomorphicAt_fibreEquation hf (coord f y) y) with hs
  have hD := σ.isLeibniz_germGenerator y
  have hJ : IsStable (σ.germGenerator y) (stalkIdeal I y ⊔ stalkIdeal I' y) :=
    IsStable.sup hD (σ.isStable_stalkIdeal hI hinvI y) (σ.isStable_stalkIdeal hI' hinvI' y)
  have hDs : IsUnit (σ.germGenerator y s) := by
    rw [hs, CircleAction.germGenerator_mk, NativeHolGerm.isUnit_iff_eval_ne_zero,
      NativeHolGerm.eval_mk, generator_sub_const, generator_coord hequiv]
    exact mul_ne_zero Complex.I_ne_zero (coord_ne_zero f y)
  have hsm : s ∈ IsLocalRing.maximalIdeal (NativeHolGerm n X y) :=
    SGPT.NAPotential.GAGAMult.mk_mem_maximalIdeal _ (sub_self _)
  have hR := isUnit_natCast_add_one (n := n) y
  have h1 : stalkIdeal I y ⊔ stalkIdeal I' y = stalkIdeal I y :=
    eq_of_le_sup_span hD hJ hDs hsm hR le_sup_left
      (sup_le le_sup_left (le_sup_left.trans (le_of_eq h.symm)))
  have h2 : stalkIdeal I y ⊔ stalkIdeal I' y = stalkIdeal I' y :=
    eq_of_le_sup_span hD hJ hDs hsm hR le_sup_right
      (sup_le (le_sup_left.trans (le_of_eq h)) le_sup_left)
  rw [← h1, h2]

/-! ### Analytic subsets of `Δ*` -/

/-- The embedding `ℂ → ℂ¹`. -/
def lineEmb : ℂ →L[ℂ] ComplexModel 1 :=
  (1 : ℂ →L[ℂ] ℂ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))

theorem lineEmb_coord (w : ComplexModel 1) : lineEmb (w 0) = w := by
  ext i
  fin_cases i
  simp [lineEmb]

/-- **Analytic subsets of `Δ*` with empty interior are discrete.** -/
theorem eventually_notMem_of_isComplexAnalyticSubset {A : Set puncturedDisc}
    (hA : IsComplexAnalyticSubset (n := 1) A) (hint : interior A = ∅) (a : puncturedDisc) :
    ∀ᶠ b in 𝓝[≠] a, b ∉ A := by
  let p := (hA a).some
  set e := (complexChartAt (n := 1) a).val with he
  have he_apply : ∀ y : puncturedDisc, e y = (y : ComplexModel 1) := fun y => by
    simp only [he, complexChartAt, AnalyticSubsetOpens.chartAt_opens_apply, chartAt_self_eq,
      OpenPartialHomeomorph.refl_apply, id]
  have he_src : ∀ y : puncturedDisc, y ∈ e.source := fun y => by
    rw [he, complexChartAt, AnalyticSubsetOpens.mem_chartAt_opens_source, chartAt_self_eq]
    exact mem_univ _
  set W := p.coordinateNeighborhood
  have hW : IsOpen W := p.isOpen_coordinateNeighborhood
  have haW : (a : ComplexModel 1) ∈ W := by
    have := p.center_mem_coordinateNeighborhood
    rwa [← he, he_apply] at this
  have hzl : ∀ y : puncturedDisc, (y : ComplexModel 1) ∈ W →
      (y ∈ A ↔ ∀ i, p.generator i (y : ComplexModel 1) = 0) := by
    intro y hy
    have := p.zeroLocus (y := y) (he_src y) (by rw [← he, he_apply]; exact hy)
    rwa [← he, he_apply] at this
  have hval : Tendsto (fun y : puncturedDisc => (y : ComplexModel 1)) (𝓝 a) (𝓝 a) :=
    continuous_subtype_val.tendsto a
  by_cases hall : ∀ i, p.generator i =ᶠ[𝓝 (a : ComplexModel 1)] 0
  · exfalso
    have hmem : A ∈ 𝓝 a := by
      have h1 : ∀ᶠ w in 𝓝 (a : ComplexModel 1), w ∈ W ∧ ∀ i, p.generator i w = 0 :=
        Filter.Eventually.and (hW.mem_nhds haW) (eventually_all.2 hall)
      filter_upwards [hval.eventually h1] with y hy
      exact (hzl y hy.1).2 hy.2
    have : a ∈ interior A := mem_interior_iff_mem_nhds.2 hmem
    rw [hint] at this
    exact this
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    set c₀ : ℂ := (a : ComplexModel 1) 0
    set h : ℂ → ℂ := fun c => p.generator i (lineEmb c)
    have hlin : lineEmb c₀ = (a : ComplexModel 1) := lineEmb_coord _
    have hdiff : DifferentiableOn ℂ h (lineEmb ⁻¹' W) :=
      (p.generator_holomorphic i).comp lineEmb.differentiableOn fun c hc => hc
    have hmemW : lineEmb ⁻¹' W ∈ 𝓝 c₀ :=
      lineEmb.continuous.continuousAt.preimage_mem_nhds (by rw [hlin]; exact hW.mem_nhds haW)
    have han : AnalyticAt ℂ h c₀ := hdiff.analyticAt hmemW
    rcases han.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
    · exfalso
      apply hi
      have hproj : Tendsto (fun w : ComplexModel 1 => w 0) (𝓝 (a : ComplexModel 1)) (𝓝 c₀) :=
        ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous).tendsto _
      filter_upwards [hproj.eventually hz] with w hw
      have := hw
      simp only [h, lineEmb_coord] at this
      exact this
    · -- off `a`, the generator `i` does not vanish
      have hproj : Tendsto (fun y : puncturedDisc => (y : ComplexModel 1) 0) (𝓝[≠] a)
          (𝓝[≠] c₀) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact ((((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous).comp
            continuous_subtype_val).tendsto a).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with y hy
          intro heq
          apply hy
          apply Subtype.ext
          rw [← lineEmb_coord (y : ComplexModel 1), ← lineEmb_coord (a : ComplexModel 1)]
          exact congrArg lineEmb heq
      filter_upwards [hproj.eventually hnz, (hval.mono_left nhdsWithin_le_nhds)
        (hW.mem_nhds haW)] with y hy hyW hyA
      apply hy
      have := ((hzl y hyW).1 hyA) i
      simp only [h, lineEmb_coord]
      exact this

/-- The rotation of `Δ*` by the angle `θ`. -/
def rotate (θ : ℝ) (z : puncturedDisc) : puncturedDisc :=
  ⟨Complex.exp (θ * Complex.I) • (z : ComplexModel 1),
    mem_puncturedDisc.2 (by rw [norm_rotate]; exact mem_puncturedDisc.1 z.2)⟩

theorem rotate_ne {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 * Real.pi) (z : puncturedDisc) :
    rotate θ z ≠ z := by
  intro h
  have h1 : (Complex.exp (θ * Complex.I) - 1) • (z : ComplexModel 1) = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact congrArg Subtype.val h
  rcases smul_eq_zero.1 h1 with h2 | h2
  · rw [sub_eq_zero, Complex.exp_eq_one_iff] at h2
    obtain ⟨k, hk⟩ := h2
    have hk' : θ = k * (2 * Real.pi) := by
      have := congrArg Complex.im hk
      simp at this
      linarith
    have hpi := Real.pi_pos
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
      nlinarith
    · rw [hk0] at hk'; simp at hk'; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      nlinarith
  · have := ((z : puncturedDisc).2 : (z : ComplexModel 1) ∈ puncturedDisc).1
    rw [h2, norm_zero] at this
    exact lt_irrefl _ this

theorem continuous_rotate (z : puncturedDisc) : Continuous fun θ : ℝ => rotate θ z := by
  refine Continuous.subtype_mk ?_ _
  exact (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).smul
    continuous_const

/-- **A nonempty rotation-invariant analytic subset of `Δ*` has interior points.** -/
theorem interior_nonempty_of_rotate {A : Set puncturedDisc}
    (hA : IsComplexAnalyticSubset (n := 1) A) (hrot : ∀ θ z, z ∈ A → rotate θ z ∈ A)
    {a : puncturedDisc} (ha : a ∈ A) : (interior A).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hiso := eventually_notMem_of_isComplexAnalyticSubset hA hne a
  have ht : Tendsto (fun θ : ℝ => rotate θ a) (𝓝[>] 0) (𝓝[≠] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : rotate 0 a = a := by
        apply Subtype.ext; simp [rotate]
      have := (continuous_rotate a).tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · have hI : Ioo (0 : ℝ) (2 * Real.pi) ∈ 𝓝[>] (0 : ℝ) :=
        Ioo_mem_nhdsGT (by positivity)
      filter_upwards [hI] with θ hθ
      exact rotate_ne hθ.1 hθ.2 a
  obtain ⟨θ, hθ⟩ := (ht.eventually hiso).exists
  exact hθ (hrot θ a ha)

/-! ### Global rigidity -/

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Stalk equality of invariant coherent ideals is invariant under the action. -/
theorem stalkIdeal_eq_act {σ : CircleAction n X} {I I' : GermIdeal n X} (hI : I.IsCoherent)
    (hI' : I'.IsCoherent) (hinvI : σ.IsInvariantIdeal I) (hinvI' : σ.IsInvariantIdeal I')
    {θ : ℝ} {x : X} (h : stalkIdeal I (σ.act θ x) = stalkIdeal I' (σ.act θ x)) :
    stalkIdeal I x = stalkIdeal I' x := by
  have hmem : ∀ g, I.mem x g ↔ I'.mem x g := by
    intro g
    have hg : (fun p => g (σ.act (-θ) (σ.act θ p))) = g :=
      funext fun p => congrArg g (σ.act_neg_act θ p)
    have e1 := hinvI θ x (fun p => g (σ.act (-θ) p))
    have e2 := hinvI' θ x (fun p => g (σ.act (-θ) p))
    rw [hg] at e1 e2
    rw [← e1, ← e2]
    exact ⟨(CoherentIdeal.stalkIdeal_le_iff hI hI' _).1 h.le _,
      (CoherentIdeal.stalkIdeal_le_iff hI' hI _).1 h.ge _⟩
  exact le_antisymm ((CoherentIdeal.stalkIdeal_le_iff hI hI' x).2 fun g => (hmem g).1)
    ((CoherentIdeal.stalkIdeal_le_iff hI' hI x).2 fun g => (hmem g).2)

/-- **Global rigidity of invariant coherent ideals.** Let `f : X → Δ*` be holomorphic, proper and
rotation-equivariant for the `C¹` circle action `σ`, and `I, I'` coherent ideals invariant under
`σ`. If for a dense set of `z ∈ Δ*` we have `I_y + (t - z) = I'_y + (t - z)` at every point `y` of
the fibre `X_z`, then `I = I'`. -/
theorem eq_of_dense_sup_eq (σ : CircleAction n X) {f : X → puncturedDisc}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f) (hprop : IsProperMap f)
    (hequiv : IsRotationEquivariant σ f) {I I' : GermIdeal n X} (hI : I.IsCoherent)
    (hI' : I'.IsCoherent) (hinvI : σ.IsInvariantIdeal I) (hinvI' : σ.IsInvariantIdeal I')
    {G : Set puncturedDisc} (hG : Dense G)
    (h : ∀ y : X, f y ∈ G →
      stalkIdeal I y ⊔ Ideal.span {NativeHolGerm.mk _ (holomorphicAt_fibreEquation hf
          (coord f y) y)} =
        stalkIdeal I' y ⊔ Ideal.span {NativeHolGerm.mk _ (holomorphicAt_fibreEquation hf
          (coord f y) y)}) :
    I = I' := by
  have hloc : ∀ y, f y ∈ G → stalkIdeal I y = stalkIdeal I' y := fun y hy =>
    stalkIdeal_eq_of_sup_eq σ hf hequiv hI hI' hinvI hinvI' (h y hy)
  set B : Set X := (InvertibleIdealQuotient.colon I' I).zeroLocus ∪
    (InvertibleIdealQuotient.colon I I').zeroLocus with hBdef
  have hB : ∀ x, x ∈ B ↔ stalkIdeal I x ≠ stalkIdeal I' x := by
    intro x
    rw [hBdef, mem_union, CoherentIdeal.mem_zeroLocus_colon_iff hI hI' x,
      CoherentIdeal.mem_zeroLocus_colon_iff hI' hI x]
    constructor
    · rintro (h1 | h1) heq
      · exact h1 heq.le
      · exact h1 heq.ge
    · intro hne
      by_contra hc
      push Not at hc
      exact hne (le_antisymm hc.1 hc.2)
  have hBan : IsComplexAnalyticSubset (n := n) B :=
    ConstantRankImage.IsComplexAnalyticSubset.union
      (StepFourNoComponentContainsW.isComplexAnalyticSubset_zeroLocus
        (CoherentIdealColon.isCoherent_colon_of_isCoherent hI' hI))
      (StepFourNoComponentContainsW.isComplexAnalyticSubset_zeroLocus
        (CoherentIdealColon.isCoherent_colon_of_isCoherent hI hI'))
  have hBcl : IsClosed B := hBan.isClosed
  have hproper : AnalyticDimensionBasics.ProperOn f B := fun K hK =>
    (hprop.isCompact_preimage hK).inter_left hBcl
  have himg : IsComplexAnalyticSubset (n := 1) (f '' B) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hf hBan hproper
  have hrot : ∀ θ z, z ∈ f '' B → rotate θ z ∈ f '' B := by
    rintro θ _ ⟨x, hx, rfl⟩
    refine ⟨σ.act θ x, ?_, Subtype.ext (hequiv θ x)⟩
    rw [hB] at hx ⊢
    exact fun heq => hx (stalkIdeal_eq_act hI hI' hinvI hinvI' heq)
  have hempty : B = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨z, hz⟩ := interior_nonempty_of_rotate himg hrot ⟨x, hx, rfl⟩
    obtain ⟨w, hwint, hwG⟩ := hG.inter_open_nonempty _ isOpen_interior ⟨z, hz⟩
    obtain ⟨y, hyB, rfl⟩ := interior_subset hwint
    exact (hB y).1 hyB (hloc y hwG)
  refine CoherentIdeal.eq_of_stalkIdeal_eq hI hI' fun x => ?_
  by_contra hne
  have : x ∈ B := (hB x).2 hne
  rw [hempty] at this
  exact this

end SGPT.GAGA.Coherent
