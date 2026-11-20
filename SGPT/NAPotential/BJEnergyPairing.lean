import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The energy pairing of Boucksom–Jonsson in a fixed ample class: the algebraic layer

Source: Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field*
([BJ22], `references/bj22-trivval`), §3.2 (`sec:enpairing`), §3.3 (`sec:estimates`), and the
proof of Theorem 12.17 (`thm:moncount`, via Corollary `cor:sameenergy`).

Fix a projective variety `X` of dimension `n` over a trivially valued field and an ample class
`ω`. Boucksom and Jonsson attach to `(n+1)`-tuples of pairs `(θ_i, φ_i)` (a numerical class and a
piecewise linear function on `X^an`) the *energy pairing* `(θ_0, φ_0) ⋯ (θ_n, φ_n)`, an
intersection number on a test configuration ([BJ22, Definition `defi:intpairing`]). Restricted
to the classes `θ_i = s_i ω` (`s_i ∈ ℚ`) it is a symmetric multilinear form on `ℚ × PL`.
Everything in [BJ22, §3.3] (the energy `E(φ) = (ω,φ)^{n+1} / ((n+1) (ω^n))`, its monotonicity and
concavity, the Hodge seminorms, the Cauchy–Schwarz estimates, the quasi-metric `d_ω`) is a formal
consequence of the following properties of that form, which [BJ22] prove geometrically:

* multilinearity and symmetry ([BJ22, Proposition `prop:intpairing`]); we encode the form as a
  function on multisets, linear in the head;
* `(0,1) ⋅ (s_1 ω, φ_1) ⋯ (s_n ω, φ_n) = (∏ s_i) (ω^n)` ([BJ22, `prop:intpairing` (i)]);
* `(ω, 0)^{n+1} = 0` ([BJ22, `prop:intpairing` (iii)]);
* `(0, f) ⋅ (ω, 0)^n = (ω^n) f(v_triv)` for irreducible `X` ([BJ22, `equ:mixedMA0`]);
* positivity: `(0, f) ⋅ (ω, φ_1) ⋯ (ω, φ_n) ≥ 0` for `f ≥ 0` and `ω`-psh PL `φ_i`
  ([BJ22, Lemma `lem:enmono`]);
* the Hodge inequality `(0, f)^2 ⋅ (ω, φ_1) ⋯ (ω, φ_{n-1}) ≤ 0` for `ω`-psh PL `φ_i`
  ([BJ22, Lemma `lem:Hodge`]);
* the `ω`-psh PL functions contain `0` and are stable under adding rational constants and under
  midpoints ([BJ22, §3.1]).

The structure `EnergyPairing` records exactly these properties. This file proves, for any such
structure, the estimates of [BJ22, §3.3] that the proof of [BJ22, Theorem 12.17] needs, and the
**selection theorem** `EnergyPairing.exists_monotone_tendsto_of_antitone`: a uniformly bounded
decreasing net of `ω`-psh PL functions converges, along some increasing sequence of indices, at
every point that is charged by the Monge–Ampère measure of some bounded `ω`-psh PL function (in
particular at `v_triv`). In [BJ22] the argument is: choose indices along which the energies
converge to their infimum; the limit `ψ` of the selected sequence then has the same energy as the
limit `φ` of the net, and `ψ ≥ φ`, so `ψ = φ` ([BJ22, Corollary `cor:sameenergy`]). We give a
direct quantitative version of that argument at the level of PL functions: it uses
[BJ22, `lem:enincr`, `lem:dLconv`, `lem:CS`] in place of the theory of
measures of finite energy.

## Main definitions

* `EnergyPairing T n`: an energy pairing in a fixed ample class on a space of points `T`.
* `EnergyPairing.selfPair`: `P(φ) = (ω, φ)^{n+1}`; `EnergyPairing.energy = P / ((n+1) (ω^n))`.
* `EnergyPairing.hodgeForm`, `EnergyPairing.hodgeQuad`: the Hodge forms
  `-(0,f)⋅(0,g)⋅(ω,φ_1)⋯(ω,φ_{n-1})` and their quadratic forms (squares of the seminorms of
  [BJ22, §3.3, the seminorms after `thm:enconc`]).
* `EnergyPairing.dist`: the sum version of the quasi-metric `d_ω` of [BJ22, Definition]
  (`defi:dtheta`), and `EnergyPairing.jFun`, the right-hand side of [BJ22, `equ:dJ`].
* `EnergyPairing.IsCharged`: `t` carries an atom of the Monge–Ampère measure of a bounded `ω`-psh
  PL function.

## Main results

* `EnergyPairing.selfPair_sub_selfPair`: the telescoping formula [BJ22, `equ:en`].
* `EnergyPairing.selfPair_mono`, `EnergyPairing.selfPair_add_const`: monotonicity and translation
  equivariance of the energy on `ω`-psh PL functions.
* `EnergyPairing.hodgeForm_sq_le`: the Cauchy–Schwarz inequality [BJ22, `equ:CS`].
* `EnergyPairing.dist_le_jFun`, `EnergyPairing.jFun_le_dist`: [BJ22, `equ:dJ`].
* `EnergyPairing.jFun_midpoint_le`: midpoint convexity [BJ22, `equ:dconv`].
* `EnergyPairing.tendsto_hodgeQuad_of_tendsto_dist`: the qualitative form of [BJ22, Lemma
  `lem:CS`].
* `EnergyPairing.exists_monotone_tendsto_of_antitone`: the selection theorem.
* `EnergyPairing.extSelfPair`, `EnergyPairing.extSelfPair_iInf`: the energy extended to decreasing
  limits by monotonicity, and its continuity along decreasing nets ([BJ22, `thm:extint`],
  diagonal case), on a compact space of points with continuous PL functions.
* `EnergyPairing.trivialModel`: the trivial test configuration restricted to constant functions
  is a model of the axioms, in every dimension.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJEnergy

open Filter Topology Multiset

/-- **An energy pairing in a fixed ample class** `ω` on a space of points `T` (for `X^an`), for a
variety of dimension `n`.

* `F` is the `ℚ`-vector space of piecewise linear functions, as real functions on `T`;
* `pair` is the energy pairing `(s_0 ω, φ_0) ⋯ (s_n ω, φ_n)` of [BJ22, Definition `defi:intpairing`], evaluated
  on the multiset `{(s_0, φ_0), …, (s_n, φ_n)}` of elements of `ℚ × F` (only multisets with
  `n + 1` elements matter); it is linear in each entry (`pair_add`, `pair_smul`: linearity in the
  head of the multiset; symmetry is built in);
* `vol` is the volume `(ω^n) > 0`;
* `triv` is the trivial valuation `v_triv`;
* `psh` is the set of `ω`-psh PL functions.

The fields are the properties proved in [BJ22, §3.1–3.3] (see the module docstring). -/
structure EnergyPairing (T : Type*) (n : ℕ) where
  /-- The rational piecewise linear functions. -/
  F : Submodule ℚ (T → ℝ)
  one_mem : (1 : T → ℝ) ∈ F
  /-- The energy pairing, as a function of the multiset of its arguments. -/
  pair : Multiset (ℚ × F) → ℝ
  pair_add : ∀ (x y : ℚ × F) (s : Multiset (ℚ × F)),
    pair ((x + y) ::ₘ s) = pair (x ::ₘ s) + pair (y ::ₘ s)
  pair_smul : ∀ (c : ℚ) (x : ℚ × F) (s : Multiset (ℚ × F)),
    pair ((c • x) ::ₘ s) = c * pair (x ::ₘ s)
  /-- The volume `(ω^n)`. -/
  vol : ℝ
  vol_pos : 0 < vol
  /-- [BJ22, `prop:intpairing` (i)]. -/
  pair_const : ∀ s : Multiset (ℚ × F), card s = n →
    pair (((0 : ℚ), (⟨1, one_mem⟩ : F)) ::ₘ s) = vol * (s.map fun x => (x.1 : ℝ)).prod
  /-- [BJ22, `prop:intpairing` (iii)]. -/
  pair_zero : pair (replicate (n + 1) ((1 : ℚ), (0 : F))) = 0
  /-- The trivial valuation. -/
  triv : T
  /-- [BJ22, `equ:mixedMA0`] for irreducible `X`: `ω^n = (ω^n) δ_{v_triv}`. -/
  pair_triv : ∀ f : F,
    pair (((0 : ℚ), f) ::ₘ replicate n ((1 : ℚ), (0 : F))) = vol * (f : T → ℝ) triv
  /-- The `ω`-psh PL functions. -/
  psh : Set F
  zero_mem_psh : (0 : F) ∈ psh
  add_const_mem_psh : ∀ u ∈ psh, ∀ c : ℚ, u + c • (⟨1, one_mem⟩ : F) ∈ psh
  midpoint_mem_psh : ∀ u ∈ psh, ∀ w ∈ psh, (1 / 2 : ℚ) • (u + w) ∈ psh
  /-- [BJ22, Lemma `lem:enmono`]: mixed Monge–Ampère measures of psh PL functions are
  positive. -/
  positivity : ∀ (f : F) (s : Multiset F), card s = n → (∀ u ∈ s, u ∈ psh) →
    (∀ t, 0 ≤ (f : T → ℝ) t) → 0 ≤ pair (((0 : ℚ), f) ::ₘ s.map fun u => ((1 : ℚ), u))
  /-- [BJ22, Lemma `lem:Hodge`]. -/
  hodge : ∀ (f : F) (s : Multiset F), card s + 1 = n → (∀ u ∈ s, u ∈ psh) →
    pair (((0 : ℚ), f) ::ₘ ((0 : ℚ), f) ::ₘ s.map fun u => ((1 : ℚ), u)) ≤ 0

namespace EnergyPairing

variable {T : Type*} {n : ℕ} (B : EnergyPairing T n)

/-! ### Notation and multilinear algebra -/

/-- The constant function `1` as a PL function. -/
def one : B.F := ⟨1, B.one_mem⟩

/-- The rational constant `c` as a PL function. -/
def cst (c : ℚ) : B.F := c • B.one

/-- The pair `(ω, u)`. -/
def pt (u : B.F) : ℚ × B.F := (1, u)

/-- The pair `(0, f)`. -/
def fn (f : B.F) : ℚ × B.F := (0, f)

/-- The midpoint `(u + w) / 2`. -/
def mid (u w : B.F) : B.F := (1 / 2 : ℚ) • (u + w)

/-- A multiset of `ω`-psh PL functions. -/
def IsPshSet (s : Multiset B.F) : Prop := ∀ u ∈ s, u ∈ B.psh

@[simp] theorem coe_cst (c : ℚ) (t : T) : ((B.cst c : B.F) : T → ℝ) t = c := by
  simp [cst, one]

@[simp] theorem coe_one (t : T) : ((B.one : B.F) : T → ℝ) t = 1 := rfl

theorem coe_mid (u w : B.F) (t : T) :
    ((B.mid u w : B.F) : T → ℝ) t = ((u : T → ℝ) t + (w : T → ℝ) t) / 2 := by
  simp only [mid, Submodule.coe_smul, Submodule.coe_add, Pi.smul_apply, Pi.add_apply]
  rw [Rat.smul_def]
  push_cast
  ring

theorem pair_zero_head (s : Multiset (ℚ × B.F)) : B.pair (0 ::ₘ s) = 0 := by
  have h := B.pair_smul 0 0 s
  rw [zero_smul] at h
  rw [h]
  simp

theorem pair_neg (x : ℚ × B.F) (s : Multiset (ℚ × B.F)) :
    B.pair ((-x) ::ₘ s) = -B.pair (x ::ₘ s) := by
  have h := B.pair_smul (-1) x s
  rw [show ((-1 : ℚ) • x) = -x from neg_one_smul ℚ x] at h
  rw [h]
  push_cast
  ring

theorem pair_sub (x y : ℚ × B.F) (s : Multiset (ℚ × B.F)) :
    B.pair ((x - y) ::ₘ s) = B.pair (x ::ₘ s) - B.pair (y ::ₘ s) := by
  rw [sub_eq_add_neg, B.pair_add, B.pair_neg]
  ring

theorem pair_add_second (z x y : ℚ × B.F) (s : Multiset (ℚ × B.F)) :
    B.pair (z ::ₘ (x + y) ::ₘ s) = B.pair (z ::ₘ x ::ₘ s) + B.pair (z ::ₘ y ::ₘ s) := by
  rw [Multiset.cons_swap, B.pair_add, Multiset.cons_swap z x, Multiset.cons_swap z y]

theorem pair_smul_second (z : ℚ × B.F) (c : ℚ) (x : ℚ × B.F) (s : Multiset (ℚ × B.F)) :
    B.pair (z ::ₘ (c • x) ::ₘ s) = c * B.pair (z ::ₘ x ::ₘ s) := by
  rw [Multiset.cons_swap, B.pair_smul, Multiset.cons_swap z x]

theorem pair_sub_second (z x y : ℚ × B.F) (s : Multiset (ℚ × B.F)) :
    B.pair (z ::ₘ (x - y) ::ₘ s) = B.pair (z ::ₘ x ::ₘ s) - B.pair (z ::ₘ y ::ₘ s) := by
  rw [Multiset.cons_swap, B.pair_sub, Multiset.cons_swap z x, Multiset.cons_swap z y]

theorem pt_sub_pt (u w : B.F) : B.pt u - B.pt w = B.fn (u - w) := by
  simp [pt, fn]

theorem fn_add (f g : B.F) : B.fn (f + g) = B.fn f + B.fn g := by
  simp [fn]

theorem fn_sub (f g : B.F) : B.fn (f - g) = B.fn f - B.fn g := by
  simp [fn]

theorem fn_smul (c : ℚ) (f : B.F) : B.fn (c • f) = c • B.fn f := by
  simp [fn]

theorem pt_add_cst (u : B.F) (c : ℚ) : B.pt (u + B.cst c) = B.pt u + c • B.fn B.one := by
  simp [pt, fn, cst]

theorem pt_mid (u w : B.F) : B.pt (B.mid u w) = (1 / 2 : ℚ) • (B.pt u + B.pt w) := by
  ext
  · simp only [pt, Prod.smul_fst, Prod.fst_add, smul_eq_mul]
    norm_num
  · simp [pt, mid]

theorem cst_mem_psh (c : ℚ) : B.cst c ∈ B.psh := by
  have h := B.add_const_mem_psh 0 B.zero_mem_psh c
  rwa [zero_add] at h

theorem mid_mem_psh {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) : B.mid u w ∈ B.psh :=
  B.midpoint_mem_psh u hu w hw

theorem add_cst_mem_psh {u : B.F} (hu : u ∈ B.psh) (c : ℚ) : u + B.cst c ∈ B.psh :=
  B.add_const_mem_psh u hu c

theorem map_pt (s : Multiset B.F) : s.map (fun u => ((1 : ℚ), u)) = s.map B.pt := rfl

/-- The pairing with the constant function `1` in the head: [BJ22, `prop:intpairing` (i)] for
`n` entries `(ω, φ_i)`. -/
theorem pair_fn_one (s : Multiset B.F) (hs : card s = n) :
    B.pair (B.fn B.one ::ₘ s.map B.pt) = B.vol := by
  have h := B.pair_const (s.map B.pt) (by simp [hs])
  rw [show B.fn B.one = ((0 : ℚ), (⟨1, B.one_mem⟩ : B.F)) from rfl, h]
  simp [pt, Function.comp_def]

theorem pair_fn_cst (c : ℚ) (s : Multiset B.F) (hs : card s = n) :
    B.pair (B.fn (B.cst c) ::ₘ s.map B.pt) = c * B.vol := by
  rw [cst, fn_smul, B.pair_smul, pair_fn_one B s hs]

theorem pair_fn_triv (f : B.F) :
    B.pair (B.fn f ::ₘ replicate n (B.pt 0)) = B.vol * (f : T → ℝ) B.triv :=
  B.pair_triv f

theorem pair_fn_nonneg {f : B.F} (hf : ∀ t, 0 ≤ (f : T → ℝ) t) {s : Multiset B.F}
    (hs : card s = n) (hps : B.IsPshSet s) : 0 ≤ B.pair (B.fn f ::ₘ s.map B.pt) :=
  B.positivity f s hs hps hf

/-- Monotonicity of mixed Monge–Ampère integrals: [BJ22, Lemma `lem:enmono`]. -/
theorem pair_fn_mono {f g : B.F} (hfg : ∀ t, (f : T → ℝ) t ≤ (g : T → ℝ) t) {s : Multiset B.F}
    (hs : card s = n) (hps : B.IsPshSet s) :
    B.pair (B.fn f ::ₘ s.map B.pt) ≤ B.pair (B.fn g ::ₘ s.map B.pt) := by
  have h := B.pair_fn_nonneg (f := g - f) (fun t => by simpa using hfg t) hs hps
  rw [fn_sub, B.pair_sub] at h
  linarith

/-- A uniform bound on a function bounds its mixed Monge–Ampère integrals. -/
theorem pair_fn_le_of_le {f : B.F} {c : ℚ} (hf : ∀ t, (f : T → ℝ) t ≤ c) {s : Multiset B.F}
    (hs : card s = n) (hps : B.IsPshSet s) : B.pair (B.fn f ::ₘ s.map B.pt) ≤ c * B.vol := by
  have h := B.pair_fn_mono (f := f) (g := B.cst c) (fun t => by simpa using hf t) hs hps
  rwa [B.pair_fn_cst c s hs] at h

theorem le_pair_fn_of_le {f : B.F} {c : ℚ} (hf : ∀ t, (c : ℝ) ≤ (f : T → ℝ) t)
    {s : Multiset B.F} (hs : card s = n) (hps : B.IsPshSet s) :
    c * B.vol ≤ B.pair (B.fn f ::ₘ s.map B.pt) := by
  have h := B.pair_fn_mono (f := B.cst c) (g := f) (fun t => by simpa using hf t) hs hps
  rwa [B.pair_fn_cst c s hs] at h

/-! ### Telescoping -/

/-- **Telescoping** ([BJ22, `equ:en`]):
`x^p ⋅ s - y^p ⋅ s = ∑_{j<p} (x - y) ⋅ x^j ⋅ y^{p-1-j} ⋅ s`. -/
theorem pair_replicate_sub (x y : ℚ × B.F) (p : ℕ) (s : Multiset (ℚ × B.F)) :
    B.pair (replicate p x + s) - B.pair (replicate p y + s) =
      ∑ j ∈ Finset.range p, B.pair ((x - y) ::ₘ (replicate j x + replicate (p - 1 - j) y + s)) := by
  induction p generalizing s with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ]
    have h1 : replicate (p + 1) x + s = x ::ₘ (replicate p x + s) := by
      rw [replicate_succ, cons_add]
    have h2 : replicate (p + 1) y + s = y ::ₘ (replicate p y + s) := by
      rw [replicate_succ, cons_add]
    have h3 : y ::ₘ (replicate p x + s) = replicate p x + (y ::ₘ s) := by rw [add_cons]
    have h4 : y ::ₘ (replicate p y + s) = replicate p y + (y ::ₘ s) := by rw [add_cons]
    have hsplit : B.pair (x ::ₘ (replicate p x + s)) - B.pair (y ::ₘ (replicate p y + s)) =
        B.pair ((x - y) ::ₘ (replicate p x + s)) +
          (B.pair (y ::ₘ (replicate p x + s)) - B.pair (y ::ₘ (replicate p y + s))) := by
      rw [B.pair_sub]; ring
    rw [h1, h2, hsplit, h3, h4, ih (y ::ₘ s)]
    have hlast : replicate p x + replicate (p + 1 - 1 - p) y + s = replicate p x + s := by simp
    rw [hlast, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < p := Finset.mem_range.mp hj
    have hrep : replicate (p + 1 - 1 - j) y = y ::ₘ replicate (p - 1 - j) y := by
      rw [← replicate_succ]; congr 1; omega
    rw [hrep]
    simp only [add_cons, cons_add]

/-! ### The energy -/

/-- `P(φ) = (ω, φ)^{n+1}`. -/
def selfPair (u : B.F) : ℝ := B.pair (replicate (n + 1) (B.pt u))

/-- The Monge–Ampère energy `E(φ) = (ω, φ)^{n+1} / ((n+1) (ω^n))` ([BJ22, Definition `defi:E`]). -/
def energy (u : B.F) : ℝ := B.selfPair u / ((n + 1) * B.vol)

/-- The `j`-th term `a_j = (0, u - w) ⋅ (ω, u)^j ⋅ (ω, w)^{n-j}` of [BJ22, Lemma `lem:enincr`]. -/
def aTerm (u w : B.F) (j : ℕ) : ℝ :=
  B.pair (B.fn (u - w) ::ₘ (replicate j (B.pt u) + replicate (n - j) (B.pt w)))

theorem selfPair_sub_selfPair (u w : B.F) :
    B.selfPair u - B.selfPair w = ∑ j ∈ Finset.range (n + 1), B.aTerm u w j := by
  have h := B.pair_replicate_sub (B.pt u) (B.pt w) (n + 1) 0
  simp only [add_zero] at h
  rw [selfPair, selfPair, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aTerm, pt_sub_pt]
  congr 3

theorem aTerm_tuple (u w : B.F) (j : ℕ) :
    replicate j (B.pt u) + replicate (n - j) (B.pt w) =
      (replicate j u + replicate (n - j) w).map B.pt := by
  simp [map_replicate]

theorem isPshSet_replicate_add {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) (a b : ℕ) :
    B.IsPshSet (replicate a u + replicate b w) := by
  intro x hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · rw [eq_of_mem_replicate hx]; exact hu
  · rw [eq_of_mem_replicate hx]; exact hw

theorem aTerm_nonneg {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh)
    (hle : ∀ t, (w : T → ℝ) t ≤ (u : T → ℝ) t) {j : ℕ} (hj : j ≤ n) : 0 ≤ B.aTerm u w j := by
  rw [aTerm, aTerm_tuple]
  refine B.pair_fn_nonneg (fun t => ?_) (by simp; omega) (B.isPshSet_replicate_add hu hw _ _)
  simpa using hle t

/-- **Monotonicity of the energy** on `ω`-psh PL functions ([BJ22, `lem:enmono`, `lem:enincr`]): if
`w ≤ u`, then `P(w) ≤ P(u)`, and every term `a_j` lies between `0` and `P(u) - P(w)`. -/
theorem aTerm_le_selfPair_sub {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh)
    (hle : ∀ t, (w : T → ℝ) t ≤ (u : T → ℝ) t) {j : ℕ} (hj : j ≤ n) :
    B.aTerm u w j ≤ B.selfPair u - B.selfPair w := by
  rw [selfPair_sub_selfPair]
  exact Finset.single_le_sum (fun i hi => B.aTerm_nonneg hu hw hle
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem selfPair_mono {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh)
    (hle : ∀ t, (w : T → ℝ) t ≤ (u : T → ℝ) t) : B.selfPair w ≤ B.selfPair u := by
  have := B.aTerm_le_selfPair_sub hu hw hle (Nat.zero_le n)
  have h0 := B.aTerm_nonneg hu hw hle (Nat.zero_le n)
  linarith

/-- **Translation equivariance**: `P(φ + c) = P(φ) + (n+1) c (ω^n)`
([BJ22, `prop:intpairing` (ii)]). -/
theorem selfPair_add_cst (u : B.F) (c : ℚ) :
    B.selfPair (u + B.cst c) = B.selfPair u + (n + 1) * c * B.vol := by
  have h := B.pair_replicate_sub (B.pt (u + B.cst c)) (B.pt u) (n + 1) 0
  simp only [add_zero] at h
  rw [pt_sub_pt, add_sub_cancel_left] at h
  have hterm : ∀ j ∈ Finset.range (n + 1),
      B.pair (B.fn (B.cst c) ::ₘ (replicate j (B.pt (u + B.cst c)) +
        replicate (n + 1 - 1 - j) (B.pt u))) = c * B.vol := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have ht : replicate j (B.pt (u + B.cst c)) + replicate (n + 1 - 1 - j) (B.pt u) =
        (replicate j (u + B.cst c) + replicate (n + 1 - 1 - j) u).map B.pt := by
      simp [map_replicate]
    rw [ht, B.pair_fn_cst c _ (by simp; omega)]
  rw [Finset.sum_congr rfl hterm] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  rw [selfPair, selfPair]
  push_cast at h ⊢
  linarith

theorem selfPair_zero : B.selfPair 0 = 0 := B.pair_zero

theorem selfPair_cst (c : ℚ) : B.selfPair (B.cst c) = (n + 1) * c * B.vol := by
  have h := B.selfPair_add_cst 0 c
  rw [zero_add, selfPair_zero, zero_add] at h
  exact h

/-- Energies of functions with values in `[lo, hi]` lie in `[(n+1) lo vol, (n+1) hi vol]`. -/
theorem selfPair_le_of_le {u : B.F} (hu : u ∈ B.psh) {c : ℚ} (h : ∀ t, (u : T → ℝ) t ≤ c) :
    B.selfPair u ≤ (n + 1) * c * B.vol := by
  have := B.selfPair_mono (B.cst_mem_psh c) hu (fun t => by simpa using h t)
  rwa [selfPair_cst] at this

theorem le_selfPair_of_le {u : B.F} (hu : u ∈ B.psh) {c : ℚ} (h : ∀ t, (c : ℝ) ≤ (u : T → ℝ) t) :
    (n + 1) * c * B.vol ≤ B.selfPair u := by
  have := B.selfPair_mono hu (B.cst_mem_psh c) (fun t => by simpa using h t)
  rwa [selfPair_cst] at this

/-! ### Hodge forms and the Cauchy–Schwarz inequality -/

/-- The Hodge form `-(0,f)⋅(0,g)⋅(ω,φ_1)⋯(ω,φ_{n-1})` for the multiset `s = {φ_1, …, φ_{n-1}}`
([BJ22, §3.3, the seminorms after `thm:enconc`]). -/
def hodgeForm (s : Multiset B.F) (f g : B.F) : ℝ := -B.pair (B.fn f ::ₘ B.fn g ::ₘ s.map B.pt)

/-- The quadratic form `‖f‖²_s = -(0,f)²⋅(ω,φ_1)⋯(ω,φ_{n-1})` of [BJ22, §3.3, the seminorms after `thm:enconc`]. -/
def hodgeQuad (s : Multiset B.F) (f : B.F) : ℝ := B.hodgeForm s f f

theorem hodgeForm_comm (s : Multiset B.F) (f g : B.F) : B.hodgeForm s f g = B.hodgeForm s g f := by
  rw [hodgeForm, hodgeForm, Multiset.cons_swap]

theorem hodgeForm_add_left (s : Multiset B.F) (f f' g : B.F) :
    B.hodgeForm s (f + f') g = B.hodgeForm s f g + B.hodgeForm s f' g := by
  simp only [hodgeForm, fn_add, B.pair_add]; ring

theorem hodgeForm_smul_left (s : Multiset B.F) (c : ℚ) (f g : B.F) :
    B.hodgeForm s (c • f) g = c * B.hodgeForm s f g := by
  simp only [hodgeForm, fn_smul, B.pair_smul]; ring

theorem hodgeForm_sub_left (s : Multiset B.F) (f f' g : B.F) :
    B.hodgeForm s (f - f') g = B.hodgeForm s f g - B.hodgeForm s f' g := by
  simp only [hodgeForm, fn_sub, B.pair_sub]; ring

theorem hodgeForm_add_right (s : Multiset B.F) (f g g' : B.F) :
    B.hodgeForm s f (g + g') = B.hodgeForm s f g + B.hodgeForm s f g' := by
  rw [B.hodgeForm_comm s f (g + g'), hodgeForm_add_left, B.hodgeForm_comm s g f,
    B.hodgeForm_comm s g' f]

theorem hodgeForm_smul_right (s : Multiset B.F) (c : ℚ) (f g : B.F) :
    B.hodgeForm s f (c • g) = c * B.hodgeForm s f g := by
  rw [B.hodgeForm_comm s f (c • g), hodgeForm_smul_left, B.hodgeForm_comm s g f]

theorem hodgeForm_sub_right (s : Multiset B.F) (f g g' : B.F) :
    B.hodgeForm s f (g - g') = B.hodgeForm s f g - B.hodgeForm s f g' := by
  rw [B.hodgeForm_comm s f (g - g'), hodgeForm_sub_left, B.hodgeForm_comm s g f,
    B.hodgeForm_comm s g' f]

theorem hodgeQuad_neg_sub (s : Multiset B.F) (f g : B.F) :
    B.hodgeQuad s (f - g) = B.hodgeQuad s (g - f) := by
  simp only [hodgeQuad, hodgeForm_sub_left, hodgeForm_sub_right, B.hodgeForm_comm s g f]; ring

/-- [BJ22, Lemma `lem:Hodge`]: the Hodge forms are positive semi-definite. -/
theorem hodgeQuad_nonneg {s : Multiset B.F} (hs : card s + 1 = n) (hps : B.IsPshSet s)
    (f : B.F) : 0 ≤ B.hodgeQuad s f :=
  neg_nonneg.mpr (B.hodge f s hs hps)

theorem hodgeQuad_add_smul (s : Multiset B.F) (f g : B.F) (t : ℚ) :
    B.hodgeQuad s (f + t • g) =
      B.hodgeQuad s f + 2 * t * B.hodgeForm s f g + t ^ 2 * B.hodgeQuad s g := by
  simp only [hodgeQuad, hodgeForm_add_left, hodgeForm_add_right, hodgeForm_smul_left,
    hodgeForm_smul_right, B.hodgeForm_comm s g f]
  ring

/-- **Cauchy–Schwarz** for the Hodge forms ([BJ22, `equ:CS`]). -/
theorem hodgeForm_sq_le {s : Multiset B.F} (hs : card s + 1 = n) (hps : B.IsPshSet s)
    (f g : B.F) : B.hodgeForm s f g ^ 2 ≤ B.hodgeQuad s f * B.hodgeQuad s g := by
  set a := B.hodgeQuad s g
  set b := 2 * B.hodgeForm s f g
  set c := B.hodgeQuad s f
  have hq : ∀ t : ℚ, 0 ≤ a * ((t : ℝ) * t) + b * t + c := by
    intro t
    have h := B.hodgeQuad_nonneg hs hps (f + t • g)
    rw [hodgeQuad_add_smul] at h
    simp only [a, b, c]
    nlinarith [h]
  have hall : ∀ x : ℝ, 0 ≤ a * (x * x) + b * x + c := by
    intro x
    have hclosed : IsClosed {x : ℝ | 0 ≤ a * (x * x) + b * x + c} :=
      isClosed_le continuous_const (by fun_prop)
    have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | 0 ≤ a * (x * x) + b * x + c} := by
      rintro _ ⟨t, rfl⟩
      exact hq t
    have hx : x ∈ closure (Set.range ((↑) : ℚ → ℝ)) := by
      rw [Rat.denseRange_cast.closure_eq]; trivial
    exact hclosed.closure_subset_iff.mpr hsub hx
  have hd := discrim_le_zero hall
  unfold discrim at hd
  simp only [a, b, c] at hd
  nlinarith [hd]

theorem abs_hodgeForm_le {s : Multiset B.F} (hs : card s + 1 = n) (hps : B.IsPshSet s)
    (f g : B.F) : |B.hodgeForm s f g| ≤ √(B.hodgeQuad s f * B.hodgeQuad s g) :=
  Real.abs_le_sqrt (B.hodgeForm_sq_le hs hps f g)

/-- The Hodge quadratic form is affine in each psh slot: replacing `φ` by the midpoint of `φ`
and `φ'` averages the forms. -/
theorem hodgeQuad_mid_cons (u u' : B.F) (s : Multiset B.F) (f : B.F) :
    B.hodgeQuad (B.mid u u' ::ₘ s) f =
      (B.hodgeQuad (u ::ₘ s) f + B.hodgeQuad (u' ::ₘ s) f) / 2 := by
  simp only [hodgeQuad, hodgeForm, Multiset.map_cons]
  have hperm : ∀ x : ℚ × B.F, B.fn f ::ₘ B.fn f ::ₘ x ::ₘ s.map B.pt =
      x ::ₘ B.fn f ::ₘ B.fn f ::ₘ s.map B.pt := by
    intro x
    rw [Multiset.cons_swap (B.fn f) x, Multiset.cons_swap (B.fn f) x]
  rw [hperm, hperm, hperm, pt_mid, B.pair_smul, B.pair_add]
  push_cast
  ring

/-- Slot domination: replacing a psh slot `φ` by `2 ⋅ (φ + φ')/2` can only increase the Hodge
quadratic form (by `lem:Hodge` applied to the slot `φ'`). -/
theorem hodgeQuad_cons_le_two_mul_mid {u u' : B.F} (hu' : u' ∈ B.psh) {s : Multiset B.F}
    (hs : card s + 2 = n) (hps : B.IsPshSet s) (f : B.F) :
    B.hodgeQuad (u ::ₘ s) f ≤ 2 * B.hodgeQuad (B.mid u u' ::ₘ s) f := by
  rw [hodgeQuad_mid_cons]
  have h := B.hodgeQuad_nonneg (s := u' ::ₘ s) (by simp; omega)
    (fun x hx => by
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact hu'
      · exact hps x hx) f
  linarith

theorem isPshSet_cons {u : B.F} (hu : u ∈ B.psh) {s : Multiset B.F} (hs : B.IsPshSet s) :
    B.IsPshSet (u ::ₘ s) := fun x hx => by
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · exact hu
  · exact hs x hx

theorem isPshSet_add {s s' : Multiset B.F} (hs : B.IsPshSet s) (hs' : B.IsPshSet s') :
    B.IsPshSet (s + s') := fun x hx => by
  rcases Multiset.mem_add.mp hx with hx | hx
  · exact hs x hx
  · exact hs' x hx

theorem isPshSet_replicate {u : B.F} (hu : u ∈ B.psh) (k : ℕ) : B.IsPshSet (replicate k u) :=
  fun x hx => by rw [eq_of_mem_replicate hx]; exact hu

/-- Repeated slot domination: a Hodge form whose slots are `φ` or `φ'` is bounded by
`2^{#slots}` times the form with all those slots replaced by `(φ + φ')/2`. -/
theorem hodgeQuad_le_pow_mul_mid {u u' : B.F} (hu : u ∈ B.psh) (hu' : u' ∈ B.psh) (f : B.F) :
    ∀ (s : Multiset B.F) (c : ℕ), (∀ x ∈ s, x = u ∨ x = u') → card s + c + 1 = n →
      B.hodgeQuad (s + replicate c (B.mid u u')) f ≤
        2 ^ card s * B.hodgeQuad (replicate (card s + c) (B.mid u u')) f := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro c _ _; simp
  | cons a s ih =>
    intro c hs hcard
    have hs' : ∀ x ∈ s, x = u ∨ x = u' := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hcard' : card s + (c + 1) + 1 = n := by simp at hcard; omega
    have hmid : B.mid u u' ∈ B.psh := B.mid_mem_psh hu hu'
    have hpsh_s : B.IsPshSet s := fun x hx => by
      rcases hs' x hx with rfl | rfl
      · exact hu
      · exact hu'
    have hZ : B.IsPshSet (s + replicate c (B.mid u u')) :=
      B.isPshSet_add hpsh_s (B.isPshSet_replicate hmid c)
    have hZcard : card (s + replicate c (B.mid u u')) + 2 = n := by simp; omega
    have hstep : B.hodgeQuad (a ::ₘ (s + replicate c (B.mid u u'))) f ≤
        2 * B.hodgeQuad (B.mid u u' ::ₘ (s + replicate c (B.mid u u'))) f := by
      rcases hs a (Multiset.mem_cons_self a s) with rfl | rfl
      · exact B.hodgeQuad_cons_le_two_mul_mid hu' hZcard hZ f
      · have h := B.hodgeQuad_cons_le_two_mul_mid (u := a) (u' := u) hu hZcard hZ f
        have hm : B.mid a u = B.mid u a := by simp only [mid, add_comm]
        rwa [hm] at h
    have hre : B.mid u u' ::ₘ (s + replicate c (B.mid u u')) =
        s + replicate (c + 1) (B.mid u u') := by
      rw [replicate_succ, add_cons]
    rw [hre] at hstep
    have h2 := ih (c + 1) hs' hcard'
    rw [Multiset.cons_add, Multiset.card_cons]
    calc B.hodgeQuad (a ::ₘ (s + replicate c (B.mid u u'))) f
        ≤ 2 * B.hodgeQuad (s + replicate (c + 1) (B.mid u u')) f := hstep
      _ ≤ 2 * (2 ^ card s * B.hodgeQuad (replicate (card s + (c + 1)) (B.mid u u')) f) := by
          linarith
      _ = 2 ^ (card s + 1) * B.hodgeQuad (replicate (card s + 1 + c) (B.mid u u')) f := by
          rw [show card s + 1 + c = card s + (c + 1) by omega, pow_succ]; ring

/-! ### The quasi-metric `d_ω` -/

/-- The multisets `{φ^k, ψ^{n-1-k}}` of [BJ22, Definition]. -/
def ytup (u w : B.F) (k : ℕ) : Multiset B.F := replicate k u + replicate (n - 1 - k) w

/-- The sum version `∑_{k<n} ‖φ - ψ‖²_{(ω,φ)^k (ω,ψ)^{n-1-k}}` of the quasi-metric `d_ω` of
[BJ22, Definition `defi:dtheta`] (equivalent to the max version up to the factor `n`). -/
def dist (u w : B.F) : ℝ := ∑ k ∈ Finset.range n, B.hodgeQuad (B.ytup u w k) (u - w)

/-- The right-hand side `P(ψ) - P(φ) + (n+1) (φ - ψ)⋅(ω,ψ)^n` of [BJ22, `equ:dJ`]. -/
def jFun (u w : B.F) : ℝ := B.selfPair w - B.selfPair u + (n + 1) * B.aTerm u w 0

theorem isPshSet_ytup {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) (k : ℕ) :
    B.IsPshSet (B.ytup u w k) := B.isPshSet_replicate_add hu hw _ _

theorem card_ytup {u w : B.F} {k : ℕ} (hk : k < n) : card (B.ytup u w k) + 1 = n := by
  simp [ytup]; omega

theorem hodgeQuad_ytup_nonneg {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) {k : ℕ} (hk : k < n)
    (f : B.F) : 0 ≤ B.hodgeQuad (B.ytup u w k) f :=
  B.hodgeQuad_nonneg (B.card_ytup hk) (B.isPshSet_ytup hu hw k) f

theorem dist_nonneg {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) : 0 ≤ B.dist u w :=
  Finset.sum_nonneg fun _ hk => B.hodgeQuad_ytup_nonneg hu hw (Finset.mem_range.mp hk) _

theorem hodgeQuad_ytup_le_dist {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) {k : ℕ}
    (hk : k < n) : B.hodgeQuad (B.ytup u w k) (u - w) ≤ B.dist u w :=
  Finset.single_le_sum (f := fun k => B.hodgeQuad (B.ytup u w k) (u - w))
    (fun _ hj => B.hodgeQuad_ytup_nonneg hu hw (Finset.mem_range.mp hj) _)
    (Finset.mem_range.mpr hk)

/-- Consecutive terms of [BJ22, Lemma]: `a_{j+1} = a_j - ‖φ - ψ‖²_{(ω,φ)^j (ω,ψ)^{n-1-j}}`. -/
theorem aTerm_succ (u w : B.F) {j : ℕ} (hj : j < n) :
    B.aTerm u w (j + 1) = B.aTerm u w j - B.hodgeQuad (B.ytup u w j) (u - w) := by
  set Z := (B.ytup u w j).map B.pt with hZ
  have h1 : replicate (j + 1) (B.pt u) + replicate (n - (j + 1)) (B.pt w) = B.pt u ::ₘ Z := by
    rw [hZ, ytup, Multiset.map_add, map_replicate, map_replicate, replicate_succ, cons_add,
      show n - (j + 1) = n - 1 - j by omega]
  have h2 : replicate j (B.pt u) + replicate (n - j) (B.pt w) = B.pt w ::ₘ Z := by
    rw [hZ, ytup, Multiset.map_add, map_replicate, map_replicate,
      show n - j = (n - 1 - j) + 1 by omega, replicate_succ, add_cons]
  rw [aTerm, aTerm, h1, h2, hodgeQuad, hodgeForm]
  have := B.pair_sub_second (B.fn (u - w)) (B.pt u) (B.pt w) Z
  rw [pt_sub_pt] at this
  linarith

theorem aTerm_eq_sub_sum (u w : B.F) {j : ℕ} (hj : j ≤ n) :
    B.aTerm u w j = B.aTerm u w 0 -
      ∑ k ∈ Finset.range j, B.hodgeQuad (B.ytup u w k) (u - w) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [B.aTerm_succ u w (by omega), ih (by omega), Finset.sum_range_succ]
    ring

private theorem sum_range_sum_range (q : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range j, q k =
      ∑ k ∈ Finset.range m, ((m : ℝ) - k) * q k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => ((↑(m + 1) : ℝ) - k) * q k),
      Finset.sum_range_succ (fun k => q k)]
    have h : ∑ x ∈ Finset.range m, ((↑(m + 1) : ℝ) - x) * q x =
        ∑ k ∈ Finset.range m, ((m : ℝ) - k) * q k + ∑ k ∈ Finset.range m, q k := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    rw [h]; push_cast; ring

/-- The identity [BJ22, `equ:Jquad`]:
`P(ψ) - P(φ) + (n+1) (φ-ψ)⋅(ω,ψ)^n = ∑_{k<n} (n-k) ‖φ - ψ‖²_{(ω,φ)^k (ω,ψ)^{n-1-k}}`. -/
theorem jFun_eq (u w : B.F) :
    B.jFun u w = ∑ k ∈ Finset.range n, ((n : ℝ) - k) * B.hodgeQuad (B.ytup u w k) (u - w) := by
  have h := B.selfPair_sub_selfPair u w
  have hsum : ∑ j ∈ Finset.range (n + 1), B.aTerm u w j =
      ∑ j ∈ Finset.range (n + 1), (B.aTerm u w 0 -
        ∑ k ∈ Finset.range j, B.hodgeQuad (B.ytup u w k) (u - w)) :=
    Finset.sum_congr rfl fun j hj =>
      B.aTerm_eq_sub_sum u w (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [hsum, Finset.sum_sub_distrib, sum_range_sum_range] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  rw [jFun]
  push_cast at h ⊢
  linarith

/-- [BJ22, `equ:dJ`], lower bound. -/
theorem dist_le_jFun {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) :
    B.dist u w ≤ B.jFun u w := by
  rw [jFun_eq, dist]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have h0 := B.hodgeQuad_ytup_nonneg hu hw hk' (u - w)
  have : (1 : ℝ) ≤ (n : ℝ) - k := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk'
    linarith
  nlinarith

/-- [BJ22, `equ:dJ`], upper bound. -/
theorem jFun_le_dist {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) :
    B.jFun u w ≤ n * B.dist u w := by
  rw [jFun_eq, dist, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have h0 := B.hodgeQuad_ytup_nonneg hu hw hk' (u - w)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- [BJ22, Lemma `lem:enincr`], upper bound: `P(φ) - P(ψ) ≤ (n+1) (φ - ψ)⋅(ω,ψ)^n`. -/
theorem selfPair_sub_le {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) :
    B.selfPair u - B.selfPair w ≤ (n + 1) * B.aTerm u w 0 := by
  have h := B.dist_le_jFun hu hw
  have h0 := B.dist_nonneg hu hw
  rw [jFun] at h
  linarith

/-- **Midpoint concavity of the energy** ([BJ22, Theorem `thm:enconc`], at `t = 1/2`). -/
theorem selfPair_mid_ge {u u' : B.F} (hu : u ∈ B.psh) (hu' : u' ∈ B.psh) :
    (B.selfPair u + B.selfPair u') / 2 ≤ B.selfPair (B.mid u u') := by
  have hm := B.mid_mem_psh hu hu'
  have h1 := B.selfPair_sub_le hu hm
  have h2 := B.selfPair_sub_le hu' hm
  have hsum : B.aTerm u (B.mid u u') 0 + B.aTerm u' (B.mid u u') 0 = 0 := by
    simp only [aTerm, replicate_zero, zero_add, Nat.sub_zero]
    rw [← B.pair_add, ← fn_add]
    have : u - B.mid u u' + (u' - B.mid u u') = 0 := by simp only [mid]; module
    rw [this, show B.fn 0 = (0 : ℚ × B.F) by simp [fn], B.pair_zero_head]
  nlinarith

/-- The function `J` is bounded on functions with values in `[lo, hi]`. -/
theorem jFun_le_of_bounds {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) {lo hi : ℚ}
    (hulo : ∀ t, (lo : ℝ) ≤ (u : T → ℝ) t) (huhi : ∀ t, (u : T → ℝ) t ≤ hi)
    (hwlo : ∀ t, (lo : ℝ) ≤ (w : T → ℝ) t) (hwhi : ∀ t, (w : T → ℝ) t ≤ hi) :
    B.jFun u w ≤ 2 * (n + 1) * (hi - lo) * B.vol := by
  have h1 := B.selfPair_le_of_le hw hwhi
  have h2 := B.le_selfPair_of_le hu hulo
  have h3 : B.aTerm u w 0 ≤ ((hi - lo : ℚ) : ℝ) * B.vol := by
    rw [aTerm, aTerm_tuple]
    refine B.pair_fn_le_of_le (fun t => ?_) (by simp) (B.isPshSet_replicate_add hu hw _ _)
    simp only [Submodule.coe_sub, Pi.sub_apply]
    push_cast
    linarith [huhi t, hwlo t]
  rw [jFun]
  push_cast at h3 ⊢
  nlinarith [B.vol_pos]

theorem dist_le_of_bounds {u w : B.F} (hu : u ∈ B.psh) (hw : w ∈ B.psh) {lo hi : ℚ}
    (hulo : ∀ t, (lo : ℝ) ≤ (u : T → ℝ) t) (huhi : ∀ t, (u : T → ℝ) t ≤ hi)
    (hwlo : ∀ t, (lo : ℝ) ≤ (w : T → ℝ) t) (hwhi : ∀ t, (w : T → ℝ) t ≤ hi) :
    B.dist u w ≤ 2 * (n + 1) * (hi - lo) * B.vol :=
  (B.dist_le_jFun hu hw).trans (B.jFun_le_of_bounds hu hw hulo huhi hwlo hwhi)

/-! ### The key estimate [BJ22, Lemma `lem:CS`] -/

/-- The base case of [BJ22, Lemma] (from [BJ22, `equ:dtheta2`]): the Hodge form at the
midpoint is bounded by the quasi-metric. -/
theorem hodgeQuad_mid_le_dist {u u' : B.F} (hu : u ∈ B.psh) (hu' : u' ∈ B.psh) (hn : 1 ≤ n) :
    B.hodgeQuad (replicate (n - 1) (B.mid u u')) (u - u') ≤ B.dist u u' := by
  have key : ∀ a b c : ℕ, a + b + c = n - 1 →
      B.hodgeQuad (replicate a (B.mid u u') + replicate b u + replicate c u') (u - u') ≤
        B.dist u u' := by
    intro a
    induction a with
    | zero =>
      intro b c habc
      have hb : b < n := by omega
      have h := B.hodgeQuad_ytup_le_dist hu hu' hb
      have he : replicate 0 (B.mid u u') + replicate b u + replicate c u' = B.ytup u u' b := by
        rw [ytup, replicate_zero, zero_add, show c = n - 1 - b by omega]
      rwa [he]
    | succ a ih =>
      intro b c habc
      have e1 : replicate (a + 1) (B.mid u u') + replicate b u + replicate c u' =
          B.mid u u' ::ₘ (replicate a (B.mid u u') + replicate b u + replicate c u') := by
        simp only [replicate_succ, cons_add]
      have e2 : u ::ₘ (replicate a (B.mid u u') + replicate b u + replicate c u') =
          replicate a (B.mid u u') + replicate (b + 1) u + replicate c u' := by
        simp only [replicate_succ, cons_add, add_cons]
      have e3 : u' ::ₘ (replicate a (B.mid u u') + replicate b u + replicate c u') =
          replicate a (B.mid u u') + replicate b u + replicate (c + 1) u' := by
        simp only [replicate_succ, add_cons]
      rw [e1, hodgeQuad_mid_cons, e2, e3]
      have h1 := ih (b + 1) c (by omega)
      have h2 := ih b (c + 1) (by omega)
      linarith
  have h := key (n - 1) 0 0 (by omega)
  simpa using h

/-- The inductive step of [BJ22, Lemma]: with `τ = (φ + φ')/2`, `f = φ - φ'` and
`b_j = ‖f‖²_{(ω,ψ)^j (ω,τ)^{n-1-j}}`, we have `b_{j+1} ≤ b_j + 2 √(4 b_j d(τ, ψ))`. -/
theorem hodgeQuad_ytup_succ_le {φ φ' ψ : B.F} (hφ : φ ∈ B.psh) (hφ' : φ' ∈ B.psh)
    (hψ : ψ ∈ B.psh) {j : ℕ} (hj : j + 2 ≤ n) :
    B.hodgeQuad (B.ytup ψ (B.mid φ φ') (j + 1)) (φ - φ') ≤
      B.hodgeQuad (B.ytup ψ (B.mid φ φ') j) (φ - φ') +
        2 * √(4 * (B.hodgeQuad (B.ytup ψ (B.mid φ φ') j) (φ - φ') *
          B.dist (B.mid φ φ') ψ)) := by
  set τ := B.mid φ φ' with hτdef
  have hτ : τ ∈ B.psh := B.mid_mem_psh hφ hφ'
  set f := φ - φ' with hf
  set g := ψ - τ with hg
  set Z : Multiset B.F := replicate j ψ + replicate (n - 2 - j) τ with hZ
  have hZpsh : B.IsPshSet Z := B.isPshSet_replicate_add hψ hτ _ _
  have hZcard : card Z + 2 = n := by simp [hZ]; omega
  have hY1 : B.ytup ψ τ (j + 1) = ψ ::ₘ Z := by
    rw [ytup, hZ, replicate_succ, cons_add, show n - 1 - (j + 1) = n - 2 - j by omega]
  have hY0 : B.ytup ψ τ j = τ ::ₘ Z := by
    rw [ytup, hZ, show n - 1 - j = (n - 2 - j) + 1 by omega, replicate_succ, add_cons]
  -- the algebraic identity
  have hid : B.hodgeQuad (ψ ::ₘ Z) f - B.hodgeQuad (τ ::ₘ Z) f =
      B.hodgeForm (φ ::ₘ Z) f g - B.hodgeForm (φ' ::ₘ Z) f g := by
    simp only [hodgeQuad, hodgeForm, Multiset.map_cons]
    set Z' := Z.map B.pt
    have e : ∀ x y z : ℚ × B.F, x ::ₘ y ::ₘ z ::ₘ Z' = z ::ₘ x ::ₘ y ::ₘ Z' := by
      intro x y z
      rw [Multiset.cons_swap y z, Multiset.cons_swap x z]
    rw [e (B.fn f) (B.fn f) (B.pt ψ), e (B.fn f) (B.fn f) (B.pt τ), e (B.fn f) (B.fn g) (B.pt φ),
      e (B.fn f) (B.fn g) (B.pt φ')]
    have h1 := B.pair_sub (B.pt ψ) (B.pt τ) (B.fn f ::ₘ B.fn f ::ₘ Z')
    have h2 := B.pair_sub (B.pt φ) (B.pt φ') (B.fn f ::ₘ B.fn g ::ₘ Z')
    rw [pt_sub_pt] at h1 h2
    rw [← hg] at h1
    have h3 : B.fn f ::ₘ B.fn f ::ₘ B.fn g ::ₘ Z' = B.fn g ::ₘ B.fn f ::ₘ B.fn f ::ₘ Z' :=
      e _ _ _
    rw [← hf, h3] at h2
    linarith
  have hb0 : 0 ≤ B.hodgeQuad (τ ::ₘ Z) f :=
    B.hodgeQuad_nonneg (by simp; omega) (B.isPshSet_cons hτ hZpsh) f
  -- the bound on the `g`-terms
  have hg_le : B.hodgeQuad (τ ::ₘ Z) g ≤ B.dist τ ψ := by
    have hk : n - 1 - j < n := by omega
    have h := B.hodgeQuad_ytup_le_dist hτ hψ hk
    have he : B.ytup τ ψ (n - 1 - j) = τ ::ₘ Z := by
      rw [← hY0, ytup, ytup, show n - 1 - (n - 1 - j) = j by omega, add_comm]
    rw [he, hodgeQuad_neg_sub] at h
    exact h
  have hd0 : 0 ≤ B.dist τ ψ := B.dist_nonneg hτ hψ
  -- Cauchy–Schwarz and slot domination for one psh slot
  have hterm : ∀ v v' : B.F, v ∈ B.psh → v' ∈ B.psh → B.mid v v' = τ →
      |B.hodgeForm (v ::ₘ Z) f g| ≤ √(4 * (B.hodgeQuad (τ ::ₘ Z) f * B.dist τ ψ)) := by
    intro v v' hv hv' hmid
    have hvZ : B.IsPshSet (v ::ₘ Z) := B.isPshSet_cons hv hZpsh
    have hvc : card (v ::ₘ Z) + 1 = n := by simp; omega
    refine (B.abs_hodgeForm_le hvc hvZ f g).trans (Real.sqrt_le_sqrt ?_)
    have hf1 := B.hodgeQuad_cons_le_two_mul_mid (u := v) hv' hZcard hZpsh f
    have hg1 := B.hodgeQuad_cons_le_two_mul_mid (u := v) hv' hZcard hZpsh g
    rw [hmid] at hf1 hg1
    have hf0 := B.hodgeQuad_nonneg hvc hvZ f
    have hg0 := B.hodgeQuad_nonneg hvc hvZ g
    calc B.hodgeQuad (v ::ₘ Z) f * B.hodgeQuad (v ::ₘ Z) g
        ≤ (2 * B.hodgeQuad (τ ::ₘ Z) f) * (2 * B.dist τ ψ) :=
          mul_le_mul hf1 (hg1.trans (by linarith)) hg0 (by linarith)
      _ = 4 * (B.hodgeQuad (τ ::ₘ Z) f * B.dist τ ψ) := by ring
  have hA := hterm φ φ' hφ hφ' rfl
  have hB := hterm φ' φ hφ' hφ (by simp only [hτdef, mid, add_comm])
  rw [hY1, hY0]
  have := abs_le.mp hA
  have := abs_le.mp hB
  linarith

/-- **The qualitative form of [BJ22, Lemma `lem:CS`]**: if `d(φ_k, φ'_k) → 0` and
`d((φ_k + φ'_k)/2, ψ_k)` stays bounded, then `‖φ_k - φ'_k‖²_{(ω,ψ_k)^{n-1}} → 0`. -/
theorem tendsto_hodgeQuad_of_tendsto_dist {ι : Type*} {l : Filter ι} (hn : 1 ≤ n)
    {φ φ' ψ : ι → B.F} (hφ : ∀ k, φ k ∈ B.psh) (hφ' : ∀ k, φ' k ∈ B.psh)
    (hψ : ∀ k, ψ k ∈ B.psh) {K : ℝ} (hK : ∀ k, B.dist (B.mid (φ k) (φ' k)) (ψ k) ≤ K)
    (hd : Tendsto (fun k => B.dist (φ k) (φ' k)) l (𝓝 0)) :
    Tendsto (fun k => B.hodgeQuad (replicate (n - 1) (ψ k)) (φ k - φ' k)) l (𝓝 0) := by
  have hb : ∀ j, j ≤ n - 1 → Tendsto
      (fun k => B.hodgeQuad (B.ytup (ψ k) (B.mid (φ k) (φ' k)) j) (φ k - φ' k)) l (𝓝 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine squeeze_zero (fun k => B.hodgeQuad_ytup_nonneg (hψ k)
        (B.mid_mem_psh (hφ k) (hφ' k)) (by omega) _) (fun k => ?_) hd
      have h := B.hodgeQuad_mid_le_dist (hφ k) (hφ' k) hn
      simpa [ytup] using h
    | succ j ih =>
      intro hj
      have hb := ih (by omega)
      have hlim : Tendsto (fun k => B.hodgeQuad (B.ytup (ψ k) (B.mid (φ k) (φ' k)) j)
          (φ k - φ' k) + 2 * √(4 * (B.hodgeQuad (B.ytup (ψ k) (B.mid (φ k) (φ' k)) j)
            (φ k - φ' k) * max K 0))) l (𝓝 0) := by
        have h1 : Tendsto (fun k => 2 * √(4 * (B.hodgeQuad (B.ytup (ψ k)
            (B.mid (φ k) (φ' k)) j) (φ k - φ' k) * max K 0))) l (𝓝 0) := by
          have := ((hb.mul_const (max K 0)).const_mul 4).sqrt.const_mul 2
          simpa using this
        simpa using hb.add h1
      refine squeeze_zero (fun k => B.hodgeQuad_ytup_nonneg (hψ k)
        (B.mid_mem_psh (hφ k) (hφ' k)) (by omega) _) (fun k => ?_) hlim
      refine (B.hodgeQuad_ytup_succ_le (hφ k) (hφ' k) (hψ k) (by omega)).trans ?_
      have hb0 := B.hodgeQuad_ytup_nonneg (hψ k) (B.mid_mem_psh (hφ k) (hφ' k))
        (show j < n by omega) (φ k - φ' k)
      gcongr
      exact (hK k).trans (le_max_left _ _)
  have h := hb (n - 1) le_rfl
  simpa [ytup] using h

/-! ### Convergence of mixed Monge–Ampère integrals -/

/-- The difference between the Monge–Ampère integral of `φ - ψ` against `(ω + dd^c χ)^n` and
against `ω^n = (ω^n) δ_{v_triv}` is controlled by the Hodge forms (telescoping and
Cauchy–Schwarz). -/
theorem abs_pair_sub_triv_le {u w χ : B.F} (hχ : χ ∈ B.psh) :
    |B.pair (B.fn (u - w) ::ₘ replicate n (B.pt χ)) - B.vol * ((u - w : B.F) : T → ℝ) B.triv| ≤
      ∑ k ∈ Finset.range n,
        √(B.hodgeQuad (B.ytup χ 0 k) (u - w) * B.hodgeQuad (B.ytup χ 0 k) χ) := by
  have htel := B.pair_replicate_sub (B.pt χ) (B.pt 0) n (B.fn (u - w) ::ₘ 0)
  have e : ∀ x : ℚ × B.F, replicate n x + (B.fn (u - w) ::ₘ 0) = B.fn (u - w) ::ₘ replicate n x :=
    fun x => by rw [add_cons, add_zero]
  rw [e, e, pt_sub_pt, sub_zero] at htel
  rw [← B.pair_fn_triv (u - w), htel]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  have he : B.pair (B.fn χ ::ₘ (replicate k (B.pt χ) + replicate (n - 1 - k) (B.pt 0) +
      B.fn (u - w) ::ₘ 0)) = -B.hodgeForm (B.ytup χ 0 k) (u - w) χ := by
    rw [hodgeForm, neg_neg, ytup, Multiset.map_add, map_replicate, map_replicate, add_cons,
      add_zero, Multiset.cons_swap]
  rw [he, abs_neg]
  exact B.abs_hodgeForm_le (B.card_ytup hk') (B.isPshSet_ytup hχ B.zero_mem_psh k) _ _

theorem mid_bounds {u w : B.F} {lo hi : ℚ} (hulo : ∀ t, (lo : ℝ) ≤ (u : T → ℝ) t)
    (huhi : ∀ t, (u : T → ℝ) t ≤ hi) (hwlo : ∀ t, (lo : ℝ) ≤ (w : T → ℝ) t)
    (hwhi : ∀ t, (w : T → ℝ) t ≤ hi) :
    (∀ t, (lo : ℝ) ≤ (B.mid u w : T → ℝ) t) ∧ (∀ t, (B.mid u w : T → ℝ) t ≤ hi) := by
  refine ⟨fun t => ?_, fun t => ?_⟩ <;> rw [coe_mid] <;>
    linarith [hulo t, huhi t, hwlo t, hwhi t]

/-- **Convergence of Monge–Ampère integrals.** For uniformly bounded `ω`-psh PL functions
`u_k, w_k, χ_k` with `d(u_k, w_k) → 0`,
`∫ (u_k - w_k) (ω + dd^c χ_k)^n - (ω^n) (u_k - w_k)(v_triv) → 0`. -/
theorem tendsto_pair_sub_triv {ι : Type*} {l : Filter ι} {u w χ : ι → B.F}
    (hu : ∀ k, u k ∈ B.psh) (hw : ∀ k, w k ∈ B.psh) (hχ : ∀ k, χ k ∈ B.psh) {lo hi : ℚ}
    (hlo0 : lo ≤ 0) (hhi0 : 0 ≤ hi)
    (hulo : ∀ k t, (lo : ℝ) ≤ (u k : T → ℝ) t) (huhi : ∀ k t, (u k : T → ℝ) t ≤ hi)
    (hwlo : ∀ k t, (lo : ℝ) ≤ (w k : T → ℝ) t) (hwhi : ∀ k t, (w k : T → ℝ) t ≤ hi)
    (hχlo : ∀ k t, (lo : ℝ) ≤ (χ k : T → ℝ) t) (hχhi : ∀ k t, (χ k : T → ℝ) t ≤ hi)
    (hd : Tendsto (fun k => B.dist (u k) (w k)) l (𝓝 0)) :
    Tendsto (fun k => B.pair (B.fn (u k - w k) ::ₘ replicate n (B.pt (χ k))) -
      B.vol * ((u k - w k : B.F) : T → ℝ) B.triv) l (𝓝 0) := by
  set D : ℝ := 2 * (n + 1) * (hi - lo) * B.vol
  have h0lo : ∀ t, (lo : ℝ) ≤ ((0 : B.F) : T → ℝ) t := fun t => by simpa using hlo0
  have h0hi : ∀ t, ((0 : B.F) : T → ℝ) t ≤ hi := fun t => by simpa using hhi0
  -- the bound on each summand
  have hsum : Tendsto (fun k => ∑ j ∈ Finset.range n, √(B.hodgeQuad (B.ytup (χ k) 0 j)
      (u k - w k) * B.hodgeQuad (B.ytup (χ k) 0 j) (χ k))) l (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _j ∈ Finset.range n, (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hn : 1 ≤ n := by omega
    set ψ : ι → B.F := fun k => B.mid (χ k) 0
    have hψ : ∀ k, ψ k ∈ B.psh := fun k => B.mid_mem_psh (hχ k) B.zero_mem_psh
    have hψb := fun k => B.mid_bounds (hχlo k) (hχhi k) h0lo h0hi
    have hK : ∀ k, B.dist (B.mid (u k) (w k)) (ψ k) ≤ D := by
      intro k
      have hm := B.mid_bounds (hulo k) (huhi k) (hwlo k) (hwhi k)
      exact B.dist_le_of_bounds (B.mid_mem_psh (hu k) (hw k)) (hψ k) hm.1 hm.2
        (hψb k).1 (hψb k).2
    have hQ := B.tendsto_hodgeQuad_of_tendsto_dist hn hu hw hψ hK hd
    -- domination of the slots `χ` and `0` by their midpoint
    have hdom : ∀ k (f : B.F), B.hodgeQuad (B.ytup (χ k) 0 j) f ≤
        2 ^ (n - 1) * B.hodgeQuad (replicate (n - 1) (ψ k)) f := by
      intro k f
      have h := B.hodgeQuad_le_pow_mul_mid (hχ k) B.zero_mem_psh f (B.ytup (χ k) 0 j) 0
        (fun x hx => by
          rcases Multiset.mem_add.mp hx with hx | hx
          · exact Or.inl (eq_of_mem_replicate hx)
          · exact Or.inr (eq_of_mem_replicate hx))
        (by have := B.card_ytup (u := χ k) (w := 0) hj'; omega)
      have hc : card (B.ytup (χ k) 0 j) = n - 1 := by have := B.card_ytup (u := χ k) (w := 0) hj'; omega
      simpa [hc] using h
    have hχD : ∀ k, B.hodgeQuad (B.ytup (χ k) 0 j) (χ k) ≤ 2 ^ (n - 1) * D := by
      intro k
      refine (hdom k (χ k)).trans ?_
      have h1 := B.hodgeQuad_mid_le_dist (hχ k) B.zero_mem_psh hn
      rw [sub_zero] at h1
      have h2 := B.dist_le_of_bounds (hχ k) B.zero_mem_psh (hχlo k) (hχhi k) h0lo h0hi
      have : (0 : ℝ) ≤ 2 ^ (n - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (h1.trans h2) this
    have hup : Tendsto (fun k => √((2 ^ (n - 1) * B.hodgeQuad (replicate (n - 1) (ψ k))
        (u k - w k)) * (2 ^ (n - 1) * max D 0))) l (𝓝 0) := by
      have := ((hQ.const_mul (2 ^ (n - 1))).mul_const (2 ^ (n - 1) * max D 0)).sqrt
      simpa using this
    refine squeeze_zero (fun k => Real.sqrt_nonneg _) (fun k => Real.sqrt_le_sqrt ?_) hup
    have ha0 := B.hodgeQuad_ytup_nonneg (hχ k) B.zero_mem_psh hj' (u k - w k)
    have hb0 := B.hodgeQuad_ytup_nonneg (hχ k) B.zero_mem_psh hj' (χ k)
    exact mul_le_mul (hdom k _) ((hχD k).trans (by gcongr; exact le_max_left _ _)) hb0
      (by have := hdom k (u k - w k); linarith)
  exact squeeze_zero_norm (fun k => by
    rw [Real.norm_eq_abs]; exact B.abs_pair_sub_triv_le (hχ k)) hsum

/-! ### The selection theorem -/

/-- A point `t` is **charged** if the Monge–Ampère measure `(ω + dd^c χ)^n` of some bounded
`ω`-psh PL function `χ` has an atom at `t`: `(ω + dd^c χ)^n ≥ c δ_t` with `c > 0`, tested
against nonnegative PL functions. In [BJ22], `(ω + dd^c χ)^n` is a positive combination of Dirac
masses at the divisorial points `v_E` of a test configuration ([BJ22, `equ:mixedMAPL`]). -/
def IsCharged (t : T) : Prop :=
  ∃ χ ∈ B.psh, (∃ R : ℚ, ∀ s, |(χ : T → ℝ) s| ≤ R) ∧ ∃ c : ℝ, 0 < c ∧
    ∀ f : B.F, (∀ s, 0 ≤ (f : T → ℝ) s) →
      c * (f : T → ℝ) t ≤ B.pair (B.fn f ::ₘ replicate n (B.pt χ))

/-- `v_triv` is charged: `ω^n = (ω^n) δ_{v_triv}` ([BJ22, `equ:mixedMA0`]). -/
theorem isCharged_triv : B.IsCharged B.triv :=
  ⟨0, B.zero_mem_psh, ⟨0, fun s => by simp⟩, B.vol, B.vol_pos, fun f _ => by
    rw [pair_fn_triv]⟩

/-- In a directed preorder, every sequence is dominated by a monotone sequence. -/
theorem _root_.SGPT.NAPotential.BJEnergy.exists_monotone_ge {I : Type*} [Preorder I]
    [IsDirectedOrder I] (g : ℕ → I) : ∃ j : ℕ → I, Monotone j ∧ ∀ k, g k ≤ j k := by
  choose ub hub using fun a b : I => directed_of (· ≤ ·) a b
  let j : ℕ → I := fun k => Nat.rec (g 0) (fun k jk => ub jk (g (k + 1))) k
  refine ⟨j, monotone_nat_of_le_succ fun k => (hub _ _).1, fun k => ?_⟩
  cases k with
  | zero => exact le_rfl
  | succ k => exact (hub _ _).2

/-- **The selection theorem** (the energy argument of [BJ22, Theorem 12.17 `thm:moncount`] for
decreasing nets, in its PL form). Let `(φ_i)_{i ∈ I}` be a decreasing net of `ω`-psh PL
functions with values in a fixed bounded interval. Then there is an increasing sequence of
indices `j(0) ≤ j(1) ≤ ⋯` such that `φ_{j(k)}(t) → inf_i φ_i(t)` at every charged point `t`
(in particular at `v_triv`).

Proof: choose `j` with `E(φ_{j(k)}) → inf_i E(φ_i)`. For a charged `t` (charged by `χ`), choose
`i'_k ≥ j(k)` with `φ_{i'_k} → inf φ_i` at `t` and at `v_triv`; set `u_k = φ_{j(k)}`,
`w_k = φ_{i'_k} ≤ u_k`. Then `E(u_k) - E(w_k) → 0`, hence `d(u_k, w_k) → 0`
(`equ:dJ` and `lem:enincr`), hence `∫ (u_k - w_k) MA(χ) - (ω^n)(u_k - w_k)(v_triv) → 0`
(`lem:CS`), for `χ` and for `χ = w_k`. The second gives `(u_k - w_k)(v_triv) → 0` since
`∫ (u_k - w_k) MA(w_k) ≤ E(u_k) - E(w_k)`; the first then gives `(u_k - w_k)(t) → 0`. -/
theorem exists_monotone_tendsto_of_antitone {I : Type*} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] (φ : I → B.F) (hφ : ∀ i, φ i ∈ B.psh)
    (hanti : ∀ t, Antitone fun i => (φ i : T → ℝ) t) {lo hi : ℝ}
    (hlo : ∀ i t, lo ≤ (φ i : T → ℝ) t) (hhi : ∀ i t, (φ i : T → ℝ) t ≤ hi) :
    ∃ j : ℕ → I, Monotone j ∧ ∀ t, B.IsCharged t →
      Tendsto (fun k => (φ (j k) : T → ℝ) t) atTop (𝓝 (⨅ i, (φ i : T → ℝ) t)) := by
  -- rational bounds
  obtain ⟨lo', hlo'⟩ := exists_rat_lt (min lo 0)
  obtain ⟨hi', hhi'⟩ := exists_rat_gt (max hi 0)
  have hφlo : ∀ i t, (lo' : ℝ) ≤ (φ i : T → ℝ) t := fun i t =>
    ((hlo'.le.trans (min_le_left _ _)).trans (hlo i t))
  have hφhi : ∀ i t, (φ i : T → ℝ) t ≤ hi' := fun i t =>
    (hhi i t).trans ((le_max_left _ _).trans hhi'.le)
  -- energies
  set e : I → ℝ := fun i => B.selfPair (φ i) with he
  have he_anti : Antitone e := fun i i' hii' =>
    B.selfPair_mono (hφ i) (hφ i') (fun t => hanti t hii')
  have he_bdd : BddBelow (Set.range e) :=
    ⟨(n + 1) * lo' * B.vol, by
      rintro _ ⟨i, rfl⟩
      exact B.le_selfPair_of_le (hφ i) (hφlo i)⟩
  set E := ⨅ i, e i
  have hE_le : ∀ i, E ≤ e i := fun i => ciInf_le he_bdd i
  have hg : ∀ k : ℕ, ∃ i, e i < E + 1 / ((k : ℝ) + 1) := fun k =>
    exists_lt_of_ciInf_lt (lt_add_of_pos_right _ (by positivity))
  choose g hg using hg
  obtain ⟨j, hj, hjg⟩ := exists_monotone_ge g
  have hej : ∀ k, e (j k) < E + 1 / ((k : ℝ) + 1) := fun k => (he_anti (hjg k)).trans_lt (hg k)
  refine ⟨j, hj, fun t ht => ?_⟩
  obtain ⟨χ, hχ, ⟨R, hR⟩, c, hc, hcharge⟩ := ht
  -- pointwise infima
  have hbdd : ∀ s, BddBelow (Set.range fun i => (φ i : T → ℝ) s) := fun s =>
    ⟨lo, by rintro _ ⟨i, rfl⟩; exact hlo i s⟩
  set L := ⨅ i, (φ i : T → ℝ) t
  set L0 := ⨅ i, (φ i : T → ℝ) B.triv
  have hsel : ∀ k : ℕ, ∃ i, j k ≤ i ∧ (φ i : T → ℝ) t < L + 1 / ((k : ℝ) + 1) ∧
      (φ i : T → ℝ) B.triv < L0 + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨i1, hi1⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right L hpos)
    obtain ⟨i2, hi2⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right L0 hpos)
    obtain ⟨a, ha1, ha2⟩ := directed_of (· ≤ ·) i1 i2
    obtain ⟨b, hb1, hb2⟩ := directed_of (· ≤ ·) a (j k)
    exact ⟨b, hb2, (hanti t (ha1.trans hb1)).trans_lt hi1,
      (hanti B.triv (ha2.trans hb1)).trans_lt hi2⟩
  choose i' hi'j hi't hi'0 using hsel
  set u : ℕ → B.F := fun k => φ (j k)
  set w : ℕ → B.F := fun k => φ (i' k)
  have hu : ∀ k, u k ∈ B.psh := fun k => hφ _
  have hw : ∀ k, w k ∈ B.psh := fun k => hφ _
  have hwu : ∀ k s, (w k : T → ℝ) s ≤ (u k : T → ℝ) s := fun k s => hanti s (hi'j k)
  -- the energy gap tends to zero
  have hgap0 : ∀ k, 0 ≤ B.selfPair (u k) - B.selfPair (w k) := fun k =>
    sub_nonneg.mpr (B.selfPair_mono (hu k) (hw k) (hwu k))
  have hgap : ∀ k, B.selfPair (u k) - B.selfPair (w k) ≤ 1 / ((k : ℝ) + 1) := fun k => by
    have := hej k
    have := hE_le (i' k)
    simp only [he] at *
    linarith
  have hgapT : Tendsto (fun k => B.selfPair (u k) - B.selfPair (w k)) atTop (𝓝 0) :=
    squeeze_zero hgap0 hgap tendsto_one_div_add_atTop_nhds_zero_nat
  have ha0 : ∀ k, 0 ≤ B.aTerm (u k) (w k) 0 := fun k =>
    B.aTerm_nonneg (hu k) (hw k) (hwu k) (Nat.zero_le n)
  have ha0le : ∀ k, B.aTerm (u k) (w k) 0 ≤ B.selfPair (u k) - B.selfPair (w k) := fun k =>
    B.aTerm_le_selfPair_sub (hu k) (hw k) (hwu k) (Nat.zero_le n)
  have hdist : Tendsto (fun k => B.dist (u k) (w k)) atTop (𝓝 0) := by
    have hT : Tendsto (fun k => (n : ℝ) * (B.selfPair (u k) - B.selfPair (w k))) atTop
        (𝓝 0) := by simpa using hgapT.const_mul (n : ℝ)
    refine squeeze_zero (fun k => B.dist_nonneg (hu k) (hw k)) (fun k => ?_) hT
    have h1 := B.dist_le_jFun (hu k) (hw k)
    have h2 := ha0le k
    rw [jFun] at h1
    nlinarith
  -- common rational bounds, including `0` and `χ`
  set lo'' : ℚ := min lo' (-R)
  set hi'' : ℚ := max hi' R
  have hlo''0 : lo'' ≤ 0 := (min_le_left _ _).trans (by exact_mod_cast hlo'.le.trans (min_le_right _ _))
  have hhi''0 : 0 ≤ hi'' := le_trans (by exact_mod_cast (le_max_right hi 0).trans hhi'.le) (le_max_left _ _)
  have hb_lo : ∀ i s, (lo'' : ℝ) ≤ (φ i : T → ℝ) s := fun i s =>
    le_trans (by exact_mod_cast min_le_left _ _) (hφlo i s)
  have hb_hi : ∀ i s, (φ i : T → ℝ) s ≤ hi'' := fun i s =>
    (hφhi i s).trans (by exact_mod_cast le_max_left _ _)
  have hχlo : ∀ s, (lo'' : ℝ) ≤ (χ : T → ℝ) s := fun s => by
    have := neg_abs_le ((χ : T → ℝ) s)
    have h2 : ((lo'' : ℚ) : ℝ) ≤ -(R : ℝ) := by exact_mod_cast min_le_right _ _
    linarith [hR s]
  have hχhi : ∀ s, (χ : T → ℝ) s ≤ hi'' := fun s => by
    have := le_abs_self ((χ : T → ℝ) s)
    have h2 : (R : ℝ) ≤ ((hi'' : ℚ) : ℝ) := by exact_mod_cast le_max_right _ _
    linarith [hR s]
  -- `(u_k - w_k)(v_triv) → 0`
  have hT1 := B.tendsto_pair_sub_triv hu hw hw hlo''0 hhi''0 (fun k => hb_lo _) (fun k => hb_hi _)
    (fun k => hb_lo _) (fun k => hb_hi _) (fun k => hb_lo _) (fun k => hb_hi _) hdist
  have hA0 : Tendsto (fun k => B.aTerm (u k) (w k) 0) atTop (𝓝 0) :=
    squeeze_zero ha0 ha0le hgapT
  have htriv : Tendsto (fun k => B.vol * ((u k - w k : B.F) : T → ℝ) B.triv) atTop (𝓝 0) := by
    have hae : ∀ k, B.aTerm (u k) (w k) 0 = B.pair (B.fn (u k - w k) ::ₘ replicate n (B.pt (w k))) :=
      fun k => by simp [aTerm]
    have := hA0.sub hT1
    simp only [hae, sub_sub_cancel, sub_zero] at this
    exact this
  -- `(u_k - w_k)(t) → 0`
  have hT2 := B.tendsto_pair_sub_triv (χ := fun _ => χ) hu hw (fun _ => hχ) hlo''0 hhi''0
    (fun k => hb_lo _) (fun k => hb_hi _) (fun k => hb_lo _) (fun k => hb_hi _)
    (fun _ => hχlo) (fun _ => hχhi) hdist
  have hMA : Tendsto (fun k => B.pair (B.fn (u k - w k) ::ₘ replicate n (B.pt χ))) atTop (𝓝 0) := by
    have := hT2.add htriv
    simp only [sub_add_cancel, add_zero] at this
    exact this
  have hdiff : Tendsto (fun k => ((u k - w k : B.F) : T → ℝ) t) atTop (𝓝 0) := by
    have hc' : Tendsto (fun k => c⁻¹ * B.pair (B.fn (u k - w k) ::ₘ replicate n (B.pt χ)))
        atTop (𝓝 0) := by simpa using hMA.const_mul c⁻¹
    refine squeeze_zero (fun k => ?_) (fun k => ?_) hc'
    · simpa using sub_nonneg.mpr (hwu k t)
    · have h := hcharge (u k - w k) (fun s => by simpa using sub_nonneg.mpr (hwu k s))
      rw [le_inv_mul_iff₀ hc]
      exact h
  -- conclusion
  have hwt : Tendsto (fun k => (w k : T → ℝ) t) atTop (𝓝 L) := by
    have hup : Tendsto (fun k : ℕ => L + 1 / ((k : ℝ) + 1)) atTop (𝓝 L) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add L
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => ciInf_le (hbdd t) _) (fun k => (hi't k).le)
  have := hdiff.add hwt
  simp only [zero_add] at this
  refine this.congr fun k => ?_
  simp [u, w]

/-! ### Extension to decreasing limits and continuity along decreasing nets -/

/-- **The extended energy** `P(φ) = inf {P(u) : u ω-psh PL, u ≥ φ}` of a function
`φ : T → [-∞, +∞]` ([BJ22, `thm:extint`, `equ:extint`], diagonal case; the normalized energy is
`P / ((n+1) (ω^n))`). -/
def extSelfPair (φ : T → EReal) : EReal :=
  ⨅ (u : B.F) (_ : u ∈ B.psh) (_ : ∀ t, φ t ≤ (((u : T → ℝ) t : ℝ) : EReal)),
    ((B.selfPair u : ℝ) : EReal)

theorem extSelfPair_le {φ : T → EReal} {u : B.F} (hu : u ∈ B.psh)
    (hφu : ∀ t, φ t ≤ (((u : T → ℝ) t : ℝ) : EReal)) :
    B.extSelfPair φ ≤ ((B.selfPair u : ℝ) : EReal) :=
  iInf₂_le_of_le u hu (iInf_le_of_le hφu le_rfl)

theorem le_extSelfPair {φ : T → EReal} {a : EReal}
    (h : ∀ u ∈ B.psh, (∀ t, φ t ≤ (((u : T → ℝ) t : ℝ) : EReal)) →
      a ≤ ((B.selfPair u : ℝ) : EReal)) : a ≤ B.extSelfPair φ :=
  le_iInf₂ fun u hu => le_iInf fun hφu => h u hu hφu

/-- The extended energy is increasing. -/
theorem extSelfPair_mono {φ ψ : T → EReal} (h : ∀ t, φ t ≤ ψ t) :
    B.extSelfPair φ ≤ B.extSelfPair ψ :=
  B.le_extSelfPair fun _u hu hψu => B.extSelfPair_le hu fun t => (h t).trans (hψu t)

/-- The extension agrees with `P` on `ω`-psh PL functions. -/
theorem extSelfPair_coe {u : B.F} (hu : u ∈ B.psh) :
    B.extSelfPair (fun t => (((u : T → ℝ) t : ℝ) : EReal)) = ((B.selfPair u : ℝ) : EReal) := by
  refine le_antisymm (B.extSelfPair_le hu fun t => le_rfl) (B.le_extSelfPair fun w hw hle => ?_)
  exact EReal.coe_le_coe_iff.mpr
    (B.selfPair_mono hw hu fun t => EReal.coe_le_coe_iff.mp (hle t))

/-- **Continuity of the energy along decreasing nets** ([BJ22, `thm:extint`]): if `T` is compact,
PL functions are continuous, and `(u_i)` is a decreasing net of `ω`-psh PL functions with
pointwise limit `φ`, then `P(φ) = lim P(u_i) = inf_i P(u_i)`. -/
theorem extSelfPair_iInf [TopologicalSpace T] [CompactSpace T]
    (hcont : ∀ f : B.F, Continuous (f : T → ℝ)) {I : Type*} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] (u : I → B.F) (hu : ∀ i, u i ∈ B.psh)
    (hanti : ∀ t, Antitone fun i => (u i : T → ℝ) t) :
    B.extSelfPair (fun t => ⨅ i, (((u i : T → ℝ) t : ℝ) : EReal)) =
      ⨅ i, ((B.selfPair (u i) : ℝ) : EReal) := by
  set φ : T → EReal := fun t => ⨅ i, (((u i : T → ℝ) t : ℝ) : EReal)
  refine le_antisymm (le_iInf fun i => B.extSelfPair_le (hu i) fun t => iInf_le _ i)
    (B.le_extSelfPair fun w hw hφw => ?_)
  -- for every rational `ε > 0`, some `u_i` lies below `w + ε` (Dini)
  have hstep : ∀ ε : ℚ, 0 < ε → ∃ i, ∀ t, (u i : T → ℝ) t ≤ (w : T → ℝ) t + ε := by
    intro ε hε
    let Z : I → Set T := fun i => {t | (w : T → ℝ) t + ε ≤ (u i : T → ℝ) t}
    have hZc : ∀ i, IsClosed (Z i) := fun i =>
      isClosed_le ((hcont w).add continuous_const) (hcont (u i))
    have hZd : Directed (· ⊇ ·) Z := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      exact ⟨k, fun t ht => (show (w : T → ℝ) t + ε ≤ (u i : T → ℝ) t from
          le_trans ht (hanti t hik)),
        fun t ht => (show (w : T → ℝ) t + ε ≤ (u j : T → ℝ) t from le_trans ht (hanti t hjk))⟩
    have hZe : Set.univ ∩ ⋂ i, Z i = ∅ := by
      rw [Set.univ_inter, Set.eq_empty_iff_forall_notMem]
      intro t ht
      have hall : ∀ i, t ∈ Z i := Set.mem_iInter.mp ht
      have h1 : ((((w : T → ℝ) t + ε : ℝ)) : EReal) ≤ φ t :=
        le_iInf fun i => EReal.coe_le_coe_iff.mpr (hall i)
      have h2 := h1.trans (hφw t)
      have h3 := EReal.coe_le_coe_iff.mp h2
      have : (0 : ℝ) < ε := by exact_mod_cast hε
      linarith
    obtain ⟨i, hi⟩ := isCompact_univ.elim_directed_family_closed Z hZc hZe hZd
    refine ⟨i, fun t => le_of_not_gt fun hlt => ?_⟩
    have : t ∈ Set.univ ∩ Z i := ⟨trivial, hlt.le⟩
    rw [hi] at this
    exact this
  -- hence `inf_i P(u_i) ≤ P(w) + (n+1) ε (ω^n)` for all `ε`
  have hbound : ∀ ε : ℚ, 0 < ε →
      (⨅ i, ((B.selfPair (u i) : ℝ) : EReal)) ≤ ((B.selfPair w + (n + 1) * ε * B.vol : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨i, hi⟩ := hstep ε hε
    refine (iInf_le _ i).trans (EReal.coe_le_coe_iff.mpr ?_)
    rw [← B.selfPair_add_cst]
    exact B.selfPair_mono (B.add_cst_mem_psh hw ε) (hu i) fun t => by simpa using hi t
  -- let `ε → 0`
  set m := ⨅ i, ((B.selfPair (u i) : ℝ) : EReal) with hm
  clear_value m
  induction m using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd ((hbound 1 one_pos).trans_lt (EReal.coe_lt_top _)) (lt_irrefl _)
  | coe x =>
    refine EReal.coe_le_coe_iff.mpr (le_of_forall_pos_le_add fun δ hδ => ?_)
    have hK : (0 : ℝ) < (n + 1) * B.vol := by have := B.vol_pos; positivity
    obtain ⟨ε, hε0, hεlt⟩ := exists_rat_btwn (div_pos hδ hK)
    have hε : (0 : ℚ) < ε := by exact_mod_cast hε0
    have h1 := EReal.coe_le_coe_iff.mp (hbound ε hε)
    rw [lt_div_iff₀ hK] at hεlt
    nlinarith

end EnergyPairing

/-! ### A model: the trivial test configuration

The energy pairing of the trivial test configuration `X × ℙ¹`, restricted to the constant
functions, satisfies all the axioms of `EnergyPairing`, in every dimension. (This only shows
that the axioms are consistent; the pairing needed for [BJ22, Theorem 12.17] is the one on all
PL functions.) -/

namespace EnergyPairing

section TrivialModel

open Polynomial

variable (T : Type*) (n : ℕ) (t₀ : T)

/-- The factor `s + f(t₀) X` of an entry `(s, f)`. -/
def trivialFactor (x : ℚ × (Submodule.span ℚ ({1} : Set (T → ℝ)))) : ℝ[X] :=
  C (x.1 : ℝ) + X * C ((x.2 : T → ℝ) t₀)

/-- The energy pairing of the trivial test configuration, restricted to constant functions:
`(s_0 ω + c_0) ⋯ (s_n ω + c_n) = (ω^n) ∑_i c_i ∏_{k ≠ i} s_k`, the coefficient of `X` in
`∏ (s_i + c_i X)` (with `(ω^n) = 1`). It is a model of `EnergyPairing` in every dimension. -/
def trivialModel : EnergyPairing T n where
  F := Submodule.span ℚ ({1} : Set (T → ℝ))
  one_mem := Submodule.subset_span rfl
  pair m := if card m = n + 1 then ((m.map (trivialFactor T t₀)).prod).coeff 1 else 0
  pair_add x y s := by
    simp only [card_cons, map_cons, prod_cons]
    split_ifs
    · have : trivialFactor T t₀ (x + y) = trivialFactor T t₀ x + trivialFactor T t₀ y := by
        simp only [trivialFactor, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply]
        push_cast
        simp only [C_add]
        ring
      rw [this, add_mul, coeff_add]
    · simp
  pair_smul c x s := by
    simp only [card_cons, map_cons, prod_cons]
    split_ifs
    · have : trivialFactor T t₀ (c • x) = C (c : ℝ) * trivialFactor T t₀ x := by
        simp only [trivialFactor, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
          Pi.smul_apply, smul_eq_mul]
        rw [Rat.smul_def]
        push_cast
        simp only [C_mul]
        ring
      rw [this, mul_assoc, coeff_C_mul]
    · simp
  vol := 1
  vol_pos := one_pos
  pair_const s hs := by
    rw [if_pos (by simp [hs]), map_cons, prod_cons]
    have : trivialFactor T t₀ ((0 : ℚ), ⟨1, Submodule.subset_span rfl⟩) = X := by
      simp [trivialFactor]
    rw [this, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_zero_eq_eval_zero,
      eval_multiset_prod, Multiset.map_map, one_mul]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp [trivialFactor]
  pair_zero := by
    rw [if_pos (by simp), map_replicate]
    have : trivialFactor T t₀ ((1 : ℚ), 0) = 1 := by simp [trivialFactor]
    simp [this, coeff_one]
  triv := t₀
  pair_triv f := by
    rw [if_pos (by simp), map_cons, prod_cons, map_replicate]
    have h1 : trivialFactor T t₀ ((1 : ℚ), 0) = 1 := by simp [trivialFactor]
    have h2 : trivialFactor T t₀ ((0 : ℚ), f) = X * C ((f : T → ℝ) t₀) := by
      simp [trivialFactor]
    rw [h1, h2]
    simp
  psh := Set.univ
  zero_mem_psh := trivial
  add_const_mem_psh _ _ _ := trivial
  midpoint_mem_psh _ _ _ _ := trivial
  positivity f s hs _ hf := by
    rw [if_pos (by simp [hs]), map_cons, prod_cons]
    have h2 : trivialFactor T t₀ ((0 : ℚ), f) = X * C ((f : T → ℝ) t₀) := by
      simp [trivialFactor]
    rw [h2, mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_C_mul,
      coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    have : (s.map ((eval 0 ∘ trivialFactor T t₀) ∘ fun u => ((1 : ℚ), u))) =
        s.map fun _ => (1 : ℝ) := by
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [trivialFactor]
    rw [this, Multiset.map_const', prod_replicate, one_pow, mul_one]
    exact hf t₀
  hodge f s hs _ := by
    rw [if_pos (by simp; omega), map_cons, map_cons, prod_cons, prod_cons]
    have h2 : trivialFactor T t₀ ((0 : ℚ), f) = X * C ((f : T → ℝ) t₀) := by
      simp [trivialFactor]
    rw [h2, show (1 : ℕ) = 0 + 1 from rfl, mul_assoc, coeff_X_mul]
    set a := (f : T → ℝ) t₀
    set P := ((s.map fun u => ((1 : ℚ), u)).map (trivialFactor T t₀)).prod
    rw [show C a * (X * C a * P) = X * (C a * C a * P) by ring, coeff_X_mul_zero]

end TrivialModel

end EnergyPairing

end SGPT.NAPotential.BJEnergy
