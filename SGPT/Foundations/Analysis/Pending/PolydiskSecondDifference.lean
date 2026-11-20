import SGPT.Foundations.Analysis.Pending.PolydiskPerronEnvelope
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense

set_option autoImplicit false

/-!
# The Bedford–Taylor second-difference estimate on the polydisk

Let `P` be the open unit polydisk and let `v` be smooth (`C²`) on a
neighbourhood of `P̄` and plurisubharmonic on `P`, with Perron–Bremermann
envelope `u = perronEnvelope v` (see `Pending.PolydiskPerronEnvelope`).  For
`0 < r < 1` there are `K` and `δ > 0` with

`u(a + h) + u(a - h) - 2 u(a) ≤ K ‖h‖²`

for `a` in the polydisk of radius `r` and `‖h‖ < δ`.  This is Bedford–Taylor's
`C^{1,1}` estimate; we follow Z. Błocki, *The complex Monge–Ampère operator in
pluripotential theory*, lecture notes, Theorem 2.3.2 (see also Bedford–Taylor,
Invent. Math. 37 (1976)).

The proof uses the family of holomorphic automorphisms of `P`

`T_{a,h} = M_{-(a+h)} ∘ M_a` coordinatewise, `M_c(z) = (z - c)/(1 - conj c z)`,

which satisfies `T_{a,h}(a) = a + h`, `T_{a,0} = id`, and maps `P̄` to `P̄` and
`∂P` to `∂P`.  Then `w = ½ (u ∘ T_{a,h} + u ∘ T_{a,-h}) - K‖h‖²` is a competitor
for the envelope: it is plurisubharmonic on `P` (plurisubharmonic functions pull
back under holomorphic maps) and on the boundary the second difference of the
`C²` function `v` along the parameter `h` is bounded by `K‖h‖²` uniformly in
`a` and in the boundary point.  Evaluating `w ≤ u` at `z = a` gives the
estimate.
-/

noncomputable section

open Set Filter Metric TopologicalSpace InnerProductSpace
open scoped Topology ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Möbius automorphisms of the unit disc -/

/-- The Möbius transformation `z ↦ (z - c)/(1 - conj c z)` of the unit disc. -/
def discMobius (c z : ℂ) : ℂ := (z - c) / (1 - (starRingEnd ℂ) c * z)

/-- The basic identity `|1 - conj c z|² - |z - c|² = (1 - |c|²)(1 - |z|²)`. -/
theorem normSq_discMobius_denom_sub (c z : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) c * z) - Complex.normSq (z - c) =
      (1 - Complex.normSq c) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
  ring

theorem discMobius_denom_ne_zero {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - (starRingEnd ℂ) c * z ≠ 0 := by
  intro hzero
  have h1 : (starRingEnd ℂ) c * z = 1 := by
    have := sub_eq_zero.mp hzero
    exact this.symm
  have h2 : ‖(starRingEnd ℂ) c * z‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, RCLike.norm_conj] at h2
  nlinarith [norm_nonneg c, norm_nonneg z]

theorem norm_discMobius_le_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖discMobius c z‖ ≤ 1 := by
  have hden := discMobius_denom_ne_zero hc hz
  have hkey := normSq_discMobius_denom_sub c z
  have hcn : Complex.normSq c < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg c]
  have hzn : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hle : Complex.normSq (z - c) ≤ Complex.normSq (1 - (starRingEnd ℂ) c * z) := by
    nlinarith [hkey]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hle
  rw [discMobius, norm_div, div_le_one (by
    simpa [norm_pos_iff] using hden)]
  nlinarith [norm_nonneg (z - c), norm_nonneg (1 - (starRingEnd ℂ) c * z)]

theorem norm_discMobius_lt_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    ‖discMobius c z‖ < 1 := by
  have hden := discMobius_denom_ne_zero hc hz.le
  have hkey := normSq_discMobius_denom_sub c z
  have hcn : Complex.normSq c < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg c]
  have hzn : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hlt : Complex.normSq (z - c) < Complex.normSq (1 - (starRingEnd ℂ) c * z) := by
    nlinarith [hkey]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt
  rw [discMobius, norm_div, div_lt_one (by simpa [norm_pos_iff] using hden)]
  nlinarith [norm_nonneg (z - c), norm_nonneg (1 - (starRingEnd ℂ) c * z)]

theorem norm_discMobius_eq_one {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ = 1) :
    ‖discMobius c z‖ = 1 := by
  have hden := discMobius_denom_ne_zero hc hz.le
  have hkey := normSq_discMobius_denom_sub c z
  have hzn : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have heq : Complex.normSq (z - c) = Complex.normSq (1 - (starRingEnd ℂ) c * z) := by
    rw [hzn] at hkey
    simp at hkey
    linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at heq
  rw [discMobius, norm_div, div_eq_one_iff_eq (by simpa [norm_pos_iff] using hden)]
  nlinarith [norm_nonneg (z - c), norm_nonneg (1 - (starRingEnd ℂ) c * z)]

theorem discMobius_self (c : ℂ) : discMobius c c = 0 := by
  simp [discMobius]

/-- `M_{-c}` inverts `M_c` on the closed unit disc. -/
theorem discMobius_neg_discMobius {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ ≤ 1) :
    discMobius (-c) (discMobius c z) = z := by
  have hden := discMobius_denom_ne_zero hc hz
  have hmul : (starRingEnd ℂ) c * c = (Complex.normSq c : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have hA : (1 : ℂ) - (starRingEnd ℂ) c * c ≠ 0 := by
    rw [hmul]
    have hlt : Complex.normSq c < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg c]
    have : ((1 - Complex.normSq c : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith)
    simpa using this
  have hnum : discMobius c z - (-c) =
      z * (1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * z) := by
    rw [discMobius, sub_neg_eq_add, div_add' _ _ _ hden]
    congr 1
    ring
  have hden2 : (1 : ℂ) - (starRingEnd ℂ) (-c) * discMobius c z =
      (1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * z) := by
    rw [eq_div_iff hden, discMobius, map_neg]
    field_simp
    ring
  rw [discMobius, hnum, hden2, div_div_div_eq]
  rw [mul_comm]
  field_simp

theorem differentiableAt_discMobius {c w : ℂ} (h : 1 - (starRingEnd ℂ) c * w ≠ 0) :
    DifferentiableAt ℂ (discMobius c) w := by
  unfold discMobius
  refine DifferentiableAt.div ?_ ?_ h
  · exact differentiableAt_id.sub_const c
  · exact (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)

theorem continuousAt_discMobius {c w : ℂ} (h : 1 - (starRingEnd ℂ) c * w ≠ 0) :
    ContinuousAt (discMobius c) w := (differentiableAt_discMobius h).continuousAt

/-! ### The automorphisms `T_{a,h}` of the polydisk -/

/-- The coordinatewise automorphism `T_{a,h} = M_{-(a+h)} ∘ M_a` of the unit
polydisk.  It sends `a` to `a + h` and is the identity for `h = 0`. -/
def polydiskAut (a h z : ComplexModel n) : ComplexModel n :=
  FirstPass.RegularLocusDense.assemble (fun i z => discMobius (-(a i + h i)) (discMobius (a i) (z i))) z

theorem polydiskAut_apply (a h z : ComplexModel n) (i : Fin n) :
    polydiskAut a h z i = discMobius (-(a i + h i)) (discMobius (a i) (z i)) := rfl

variable {a h z : ComplexModel n}

theorem polydiskAut_mem_closedUnitPolydisk (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1) (hz : z ∈ closedUnitPolydisk n) :
    polydiskAut a h z ∈ closedUnitPolydisk n := by
  intro i
  rw [polydiskAut_apply]
  exact norm_discMobius_le_one (by rw [norm_neg]; exact hah i)
    (norm_discMobius_le_one (ha i) (hz i))

theorem polydiskAut_mem_unitPolydisk (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1) (hz : z ∈ unitPolydisk n) :
    polydiskAut a h z ∈ unitPolydisk n := by
  intro i
  rw [polydiskAut_apply]
  exact norm_discMobius_lt_one (by rw [norm_neg]; exact hah i)
    (norm_discMobius_lt_one (ha i) (hz i))

theorem polydiskAut_mem_boundary (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1)
    (hz : z ∈ closedUnitPolydisk n \ unitPolydisk n) :
    polydiskAut a h z ∈ closedUnitPolydisk n \ unitPolydisk n := by
  obtain ⟨j, hj⟩ := exists_norm_eq_one_of_mem_boundary hz
  refine ⟨polydiskAut_mem_closedUnitPolydisk ha hah hz.1, fun hmem => ?_⟩
  have hone : ‖polydiskAut a h z j‖ = 1 := by
    rw [polydiskAut_apply]
    exact norm_discMobius_eq_one (by rw [norm_neg]; exact hah j)
      (norm_discMobius_eq_one (ha j) hj)
  have := hmem j
  rw [hone] at this
  exact lt_irrefl 1 this

theorem polydiskAut_self (a h : ComplexModel n) : polydiskAut a h a = a + h := by
  ext i
  rw [polydiskAut_apply, discMobius_self]
  simp [discMobius]

theorem polydiskAut_zero (ha : ∀ i, ‖a i‖ < 1) (hz : z ∈ closedUnitPolydisk n) :
    polydiskAut a 0 z = z := by
  ext i
  rw [polydiskAut_apply]
  have : a i + (0 : ComplexModel n) i = a i := by simp
  rw [this]
  exact discMobius_neg_discMobius (ha i) (hz i)

theorem differentiableOn_polydiskAut (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1) :
    DifferentiableOn ℂ (polydiskAut a h) (unitPolydisk n) := by
  refine FirstPass.RegularLocusDense.differentiableOn_assemble fun i z hz => ?_
  have hcoord : DifferentiableAt ℂ (fun y : ComplexModel n => y i) z :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i)).differentiableAt
  have h1 : 1 - (starRingEnd ℂ) (a i) * z i ≠ 0 :=
    discMobius_denom_ne_zero (ha i) (hz i).le
  have h2 : 1 - (starRingEnd ℂ) (-(a i + h i)) * discMobius (a i) (z i) ≠ 0 :=
    discMobius_denom_ne_zero (by rw [norm_neg]; exact hah i)
      (norm_discMobius_le_one (ha i) (hz i).le)
  have hstep1 : DifferentiableAt ℂ (fun y : ComplexModel n => discMobius (a i) (y i)) z := by
    change DifferentiableAt ℂ (discMobius (a i) ∘ fun y : ComplexModel n => y i) z
    exact (differentiableAt_discMobius h1).comp z hcoord
  have hstep2 : DifferentiableAt ℂ
      (fun y : ComplexModel n => discMobius (-(a i + h i)) (discMobius (a i) (y i))) z := by
    change DifferentiableAt ℂ
      (discMobius (-(a i + h i)) ∘ fun y : ComplexModel n => discMobius (a i) (y i)) z
    exact (differentiableAt_discMobius h2).comp z hstep1
  exact hstep2.differentiableWithinAt

theorem continuousAt_polydiskAut (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1) (hz : z ∈ closedUnitPolydisk n) :
    ContinuousAt (polydiskAut a h) z := by
  have hpi : ContinuousAt
      (fun y : ComplexModel n => fun i =>
        discMobius (-(a i + h i)) (discMobius (a i) (y i))) z := by
    refine continuousAt_pi.mpr fun i => ?_
    have hcoord : ContinuousAt (fun y : ComplexModel n => y i) z :=
      ((EuclideanSpace.proj (𝕜 := ℂ) i)).continuous.continuousAt
    have h1 : 1 - (starRingEnd ℂ) (a i) * z i ≠ 0 :=
      discMobius_denom_ne_zero (ha i) (hz i)
    have h2 : 1 - (starRingEnd ℂ) (-(a i + h i)) * discMobius (a i) (z i) ≠ 0 :=
      discMobius_denom_ne_zero (by rw [norm_neg]; exact hah i)
        (norm_discMobius_le_one (ha i) (hz i))
    have hstep1 : ContinuousAt (fun y : ComplexModel n => discMobius (a i) (y i)) z := by
      change ContinuousAt (discMobius (a i) ∘ fun y : ComplexModel n => y i) z
      exact ContinuousAt.comp (x := z) (continuousAt_discMobius h1) hcoord
    have hstep2 : ContinuousAt
        (fun y : ComplexModel n => discMobius (-(a i + h i)) (discMobius (a i) (y i))) z := by
      change ContinuousAt
        (discMobius (-(a i + h i)) ∘ fun y : ComplexModel n => discMobius (a i) (y i)) z
      exact ContinuousAt.comp (x := z) (continuousAt_discMobius h2) hstep1
    exact hstep2
  exact (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.continuousAt.comp hpi

/-! ### The second-difference estimate for the Perron envelope -/

/-- **The Mobius competitor.**  For `a` in the open polydisk and `h` so small
that `a + h` and `a - h` still are, the balanced average

`w = (u o T_{a,h} + u o T_{a,-h})/2 - K`

of the two Mobius pullbacks of the envelope `u = P(v)` is itself a competitor
for `v`, provided the *boundary* second difference of `v` along the family is
at most `2K`.  Plurisubharmonicity is the holomorphic pullback; the boundary
estimate transports through `T_{a,pm h}`, which maps the distinguished boundary
to itself and is continuous up to it.

This is the whole of Blocki's Theorem 2.3.2 except for the estimate on the
data: what remains for the full `C^{1,1}` statement is that a `C^2` function `v`
satisfies `hbnd` with `K = K_0 ‖h‖^2` uniformly for `a` in a smaller polydisk,
which is a Taylor estimate on the explicit map `(a, h, zeta) ↦ T_{a,h} zeta`
and involves no pluripotential theory. -/
theorem IsPerronData.secondDifference_perronEnvelope_le {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) {a h : ComplexModel n} {K : ℝ}
    (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1)
    (hah' : ∀ i, ‖a i + (-h : ComplexModel n) i‖ < 1)
    (hbnd : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      v (polydiskAut a h ζ) + v (polydiskAut a (-h) ζ) - 2 * v ζ ≤ 2 * K) :
    perronEnvelope v (a + h) + perronEnvelope v (a - h) -
      2 * perronEnvelope v a ≤ 2 * K := by
  classical
  have haP : a ∈ unitPolydisk n := fun i => ha i
  set u : ComplexModel n → ℝ := perronEnvelope v with hudef
  set T₁ : ComplexModel n → ComplexModel n := polydiskAut a h with hT₁
  set T₂ : ComplexModel n → ComplexModel n := polydiskAut a (-h) with hT₂
  have hmaps₁ : MapsTo T₁ (unitPolydisk n) (unitPolydisk n) := fun z hz =>
    polydiskAut_mem_unitPolydisk ha hah hz
  have hmaps₂ : MapsTo T₂ (unitPolydisk n) (unitPolydisk n) := fun z hz =>
    polydiskAut_mem_unitPolydisk ha hah' hz
  have hupsh := hv.plurisubharmonicOn_perronEnvelope
  have hpsh₁ : PlurisubharmonicOn (fun z => ((u (T₁ z) : ℝ) : EReal)) (unitPolydisk n) :=
    SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
      isOpen_unitPolydisk (differentiableOn_polydiskAut ha hah) hmaps₁ hupsh
  have hpsh₂ : PlurisubharmonicOn (fun z => ((u (T₂ z) : ℝ) : EReal)) (unitPolydisk n) :=
    SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
      isOpen_unitPolydisk (differentiableOn_polydiskAut ha hah') hmaps₂ hupsh
  set w : ComplexModel n → ℝ :=
    fun z => (1 / 2 : ℝ) * (u (T₁ z) + u (T₂ z)) + (-K) with hwdef
  have hcomp : IsPerronCompetitor v w := by
    constructor
    · have hsum := hpsh₁.add hpsh₂
      have hhalf := hsum.const_mul (c := (1 / 2 : ℝ)) (by norm_num)
      have hconst : PlurisubharmonicOn
          (fun _ : ComplexModel n => ((-K : ℝ) : EReal)) (unitPolydisk n) :=
        fun x _ => plurisubharmonicAt_const _ (by simp) x
      have hadd := hhalf.add hconst
      refine fun x hx => ?_
      have hfun : ∀ y : ComplexModel n, ((w y : ℝ) : EReal) =
          ((1 / 2 : ℝ) : EReal) * (((u (T₁ y) : ℝ) : EReal) + ((u (T₂ y) : ℝ) : EReal)) +
            ((-K : ℝ) : EReal) := by
        intro y
        simp only [hwdef, EReal.coe_add, EReal.coe_mul]
      have := hadd x hx
      refine this.congr ?_
      filter_upwards with y using (hfun y).symm
    · intro ζ hζ ε hε
      have hξ₁ : T₁ ζ ∈ closedUnitPolydisk n \ unitPolydisk n :=
        polydiskAut_mem_boundary ha hah hζ
      have hξ₂ : T₂ ζ ∈ closedUnitPolydisk n \ unitPolydisk n :=
        polydiskAut_mem_boundary ha hah' hζ
      have htend₁ : Tendsto T₁ (𝓝[unitPolydisk n] ζ) (𝓝[unitPolydisk n] (T₁ ζ)) :=
        ContinuousWithinAt.tendsto_nhdsWithin
          (continuousAt_polydiskAut ha hah hζ.1).continuousWithinAt hmaps₁
      have htend₂ : Tendsto T₂ (𝓝[unitPolydisk n] ζ) (𝓝[unitPolydisk n] (T₂ ζ)) :=
        ContinuousWithinAt.tendsto_nhdsWithin
          (continuousAt_polydiskAut ha hah' hζ.1).continuousWithinAt hmaps₂
      have he₁ : ∀ᶠ z in 𝓝[unitPolydisk n] ζ, u (T₁ z) ≤ v (T₁ ζ) + ε / 2 :=
        htend₁.eventually (hv.eventually_perronEnvelope_le hξ₁ (by linarith))
      have he₂ : ∀ᶠ z in 𝓝[unitPolydisk n] ζ, u (T₂ z) ≤ v (T₂ ζ) + ε / 2 :=
        htend₂.eventually (hv.eventually_perronEnvelope_le hξ₂ (by linarith))
      filter_upwards [he₁, he₂] with z h1 h2
      have hb := hbnd ζ hζ
      simp only [hwdef]
      linarith
  have hle := hv.le_perronEnvelope hcomp haP
  have hT₁a : T₁ a = a + h := polydiskAut_self a h
  have hT₂a : T₂ a = a - h := by
    rw [hT₂, polydiskAut_self]
    ext i
    simp [sub_eq_add_neg]
  simp only [hwdef, hT₁a, hT₂a] at hle
  linarith

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
