import SGPT.Checks.Comparison.ThinApprox.BJAppSeqStatement
import SGPT.Checks.Comparison.BJOriginalRegularity
import SGPT.NAPotential.BJEnergyPairing
import SGPT.NAPotential.BJDivisorialSpecComplex

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# `thm:BJappseq` from the energy pairing in ample classes

Source: `chapter_NApotential.tex`, `thm:BJappseq` (citing [BJ22, Corollary 12.18]), and
Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* ([BJ22]),
Theorem 12.17 (`thm:moncount`) and its proof.

The algebraic layer `SGPT.NAPotential.BJEnergy.EnergyPairing` proves, for any energy pairing in a
fixed ample class `ω` (the properties of [BJ22, §3.2–3.3]), that a uniformly bounded decreasing
net of `ω`-psh PL functions converges along an increasing sequence of indices at every point
charged by a Monge–Ampère measure (`EnergyPairing.exists_monotone_tendsto_of_antitone`).

This file connects that statement to the printed psh metrics of `def:BJpshmetric`:

* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.AmpleEnergyPairing p ω`: an energy pairing on `X^An` in the ample rational Picard class
  `ω`, whose `ω`-psh PL functions contain the truncations `max(φ, c)` (`c ∈ ℚ`) of the rational
  GF functions `φ ∈ 𝓗^gf_ℚ(ω^An)`, and for which every divisorial point is charged. In [BJ22] the
  energy pairing is the intersection pairing on test configurations ([BJ22, Definition `defi:intpairing`]),
  the truncations are Fubini–Study functions (`𝓗(ω) ⊆ PL ∩ PSH(ω)`, [BJ22, §2.4, §3.1]), and a
  divisorial point `v = v_E` is charged by `MA(φ_A)` for a relatively ample line bundle `A` on a
  normal test configuration containing `E` ([BJ22, `equ:mixedMAPL`]).
* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.DivisorialComparison p`: psh metrics are determined by their values on the divisorial
  set together with `v_triv` (`thm:pshdetbydiv`, [BJ22, Theorem 4.22]). It is proved in the
  library `SGPT.Checks.Literature` as `SGPT.NAPotential.BJ.Divisorial.original_le_of_sourceDivisorial_le`,
  which this library cannot import.

## Main results

* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.exists_monotone_tendsto_truncation`: the selection theorem for truncations of a
  bounded-above decreasing net of rational GF functions in an ample class.
* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.decreasingNetSelection_of_ampleEnergyPairing`: `DecreasingNetSelection` (hence
  `thm:BJappseq`, by `SGPT.NAPotential.ThinApprox.BJ.AppSeq.bjAppSeq_of_selection`) follows from the comparison theorem and the
  existence of energy pairings in ample classes.

The existence of the energy pairing (intersection numbers on test configurations, their
multilinearity, `lem:enmono`, the Hodge index inequality `lem:Hodge`) is *not* proved here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
open SGPT.NAPotential.BJ.AppSeq

open AlgebraicGeometry CategoryTheory Filter Topology
open Scheme.Modules SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ.Printed SGPT.NAPotential.ThinApprox.BJ.Printed SGPT.NAPotential.BJEnergy

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **`thm:pshdetbydiv`** ([BJ22, Theorem 4.22]) in the form proved in `SGPT.Checks.Literature`
(`SGPT.NAPotential.BJ.Divisorial.original_le_of_sourceDivisorial_le`): a psh metric lies below an
upper semicontinuous function as soon as it does on the divisorial set and at `v_triv`. -/
def DivisorialComparison : Prop :=
  ∀ (L : RationalPicardSpace X) (φ ψ : BerkovichPoint p → EReal),
    IsModuleTopologyPSH.{0} p L φ → UpperSemicontinuous ψ →
      (∀ v ∈ sourceDivisorialSet p, φ v ≤ ψ v) → φ ≤ ψ

/-- **An energy pairing in the ample class `ω`** on `X^An` (the energy pairing of [BJ22, §3.2]
restricted to the classes `s ω`, `s ∈ ℚ`): an `EnergyPairing` on `X^An` with trivial point
`v_triv`, whose `ω`-psh PL functions contain the truncations at rational levels of the rational
GF functions of class `ω`, and for which every divisorial point is charged. -/
structure AmpleEnergyPairing (ω : RationalPicardSpace X) where
  /-- The dimension of `X`. -/
  dim : ℕ
  pairing : EnergyPairing (BerkovichPoint p) dim
  triv_eq : pairing.triv = BerkovichPoint.trivial p
  truncation : ∀ E : RationalGFPackage X, E.picardClass = ω → ∀ c : ℚ,
    ∃ f ∈ pairing.psh, ∀ v,
      (f : BerkovichPoint p → ℝ) v = (max (E.eval p v) ((c : ℝ) : EReal)).toReal
  charged : ∀ v ∈ divisorialSet p, pairing.IsCharged v

/-- Every point of the determining set of `thm:pshdetbydiv` is charged. -/
theorem AmpleEnergyPairing.isCharged_of_mem {ω : RationalPicardSpace X}
    (B : AmpleEnergyPairing p ω) {v : BerkovichPoint p} (hv : v ∈ sourceDivisorialSet p) :
    B.pairing.IsCharged v := by
  rcases (mem_sourceDivisorialSet_iff p v).mp hv with rfl | hv
  · rw [← B.triv_eq]
    exact B.pairing.isCharged_triv
  · exact B.charged v hv

/-! ### Truncations -/

theorem max_coe_ne_bot (a : EReal) (c : ℝ) : max a (c : EReal) ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) (le_max_right _ _)

theorem max_coe_ne_top {a : EReal} (ha : a ≠ ⊤) (c : ℝ) : max a (c : EReal) ≠ ⊤ :=
  max_ne_top ha (EReal.coe_ne_top c)

theorem coe_toReal_max {a : EReal} (ha : a ≠ ⊤) (c : ℝ) :
    (((max a (c : EReal)).toReal : ℝ) : EReal) = max a (c : EReal) :=
  EReal.coe_toReal (max_coe_ne_top ha c) (max_coe_ne_bot a c)

/-- **Selection for truncations.** Let `(E_j)` be a decreasing net of rational GF functions of
the ample class `ω`, bounded above. For every rational level `c`, there is an increasing
sequence of indices along which `max(E_j, c)` converges to `max(inf_j E_j, c)` at every point
charged by the energy pairing. -/
theorem exists_monotone_tendsto_truncation {ω : RationalPicardSpace X}
    (B : AmpleEnergyPairing p ω) {J : Type*} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (E : J → RationalGFPackage X) (hclass : ∀ j, (E j).picardClass = ω)
    (hanti : ∀ v, Antitone fun j => (E j).eval p v) {C : ℝ}
    (hC : ∀ j v, (E j).eval p v ≤ (C : EReal)) (c : ℚ) :
    ∃ k : ℕ → J, Monotone k ∧ ∀ v, B.pairing.IsCharged v →
      Tendsto (fun n => max ((E (k n)).eval p v) ((c : ℝ) : EReal)) atTop
        (𝓝 (max (⨅ j, (E j).eval p v) ((c : ℝ) : EReal))) := by
  choose f hf hfv using fun j => B.truncation (E j) (hclass j) c
  have hne (j : J) (v : BerkovichPoint p) : (E j).eval p v ≠ ⊤ := (E j).eval_ne_top p v
  have hcoe (j : J) (v : BerkovichPoint p) :
      (((f j : BerkovichPoint p → ℝ) v : ℝ) : EReal) = max ((E j).eval p v) ((c : ℝ) : EReal) := by
    rw [hfv j v]
    have h := coe_toReal_max (hne j v) (c : ℝ)
    simpa using h
  have hmono : ∀ v, Antitone fun j => (f j : BerkovichPoint p → ℝ) v := by
    intro v j j' hjj'
    have h : max ((E j').eval p v) ((c : ℝ) : EReal) ≤ max ((E j).eval p v) ((c : ℝ) : EReal) :=
      max_le_max (hanti v hjj') le_rfl
    rw [← hcoe, ← hcoe] at h
    exact_mod_cast h
  have hlo : ∀ j v, (c : ℝ) ≤ (f j : BerkovichPoint p → ℝ) v := by
    intro j v
    have h : ((c : ℝ) : EReal) ≤ max ((E j).eval p v) ((c : ℝ) : EReal) := le_max_right _ _
    rw [← hcoe] at h
    exact_mod_cast h
  have hhi : ∀ j v, (f j : BerkovichPoint p → ℝ) v ≤ max C c := by
    intro j v
    have h : max ((E j).eval p v) ((c : ℝ) : EReal) ≤ ((max C c : ℝ) : EReal) :=
      max_le ((hC j v).trans (by exact_mod_cast le_max_left C (c : ℝ)))
        (by exact_mod_cast le_max_right C (c : ℝ))
    rw [← hcoe] at h
    exact_mod_cast h
  obtain ⟨k, hk, hlim⟩ := B.pairing.exists_monotone_tendsto_of_antitone f hf hmono hlo hhi
  refine ⟨k, hk, fun v hv => ?_⟩
  -- identify the infimum of the truncations
  have hbdd : BddBelow (Set.range fun j => (f j : BerkovichPoint p → ℝ) v) :=
    ⟨c, by rintro _ ⟨j, rfl⟩; exact hlo j v⟩
  have h1 : Tendsto (fun j => (f j : BerkovichPoint p → ℝ) v) atTop
      (𝓝 (⨅ j, (f j : BerkovichPoint p → ℝ) v)) := tendsto_atTop_ciInf (hmono v) hbdd
  have hinf_ne : (⨅ j, (E j).eval p v) ≠ ⊤ := by
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ne_top_of_le_ne_top (hne j v) (iInf_le _ j)
  have h2 : Tendsto (fun j => (f j : BerkovichPoint p → ℝ) v) atTop
      (𝓝 (max (⨅ j, (E j).eval p v) ((c : ℝ) : EReal)).toReal) := by
    have hE : Tendsto (fun j => (E j).eval p v) atTop (𝓝 (⨅ j, (E j).eval p v)) :=
      tendsto_atTop_iInf (hanti v)
    have hmax := hE.max (tendsto_const_nhds (x := ((c : ℝ) : EReal)))
    have := (EReal.tendsto_toReal (max_coe_ne_top hinf_ne (c : ℝ))
      (max_coe_ne_bot _ (c : ℝ))).comp hmax
    refine this.congr fun j => ?_
    simp only [Function.comp_apply, hfv j v]
  have heq := tendsto_nhds_unique h1 h2
  have h3 := (continuous_coe_real_ereal.tendsto _).comp (hlim v hv)
  rw [heq, coe_toReal_max hinf_ne] at h3
  refine h3.congr fun n => ?_
  simp only [Function.comp_apply, hcoe]

/-! ### Classes -/

omit [IsIntegral X] in
theorem tendsto_numericalClass_add_coeff_smul (θ η : NativeRealNumericalClasses.Space p) :
    Tendsto (fun n : ℕ => θ + (coeff n : ℝ) • η) atTop
      (@nhds _ (numericalModuleTopology p) θ) := by
  let := numericalModuleTopology p
  have : ContinuousSMul ℝ (NativeRealNumericalClasses.Space p) := ModuleTopology.continuousSMul _ _
  have : ContinuousAdd (NativeRealNumericalClasses.Space p) := ModuleTopology.continuousAdd _ _
  have h := tendsto_const_nhds (x := θ) |>.add (tendsto_coeff.smul_const η)
  simpa using h

/-- For an ample class `η`, `θ + (N+1) η` is ample for some `N`. -/
theorem exists_add_nsmul_mem_ampleCone (θ η : NativeRealNumericalClasses.Space p)
    (hη : η ∈ NativeRealNumericalClasses.ampleCone p) :
    ∃ N : ℕ, θ + ((N : ℝ) + 1) • η ∈ NativeRealNumericalClasses.ampleCone p := by
  let := numericalModuleTopology p
  have : ContinuousSMul ℝ (NativeRealNumericalClasses.Space p) := ModuleTopology.continuousSMul _ _
  let : IsTopologicalAddGroup (NativeRealNumericalClasses.Space p) :=
    IsModuleTopology.topologicalAddGroup ℝ (NativeRealNumericalClasses.Space p)
  have hT : Tendsto (fun N : ℕ => -((1 / ((N : ℝ) + 1)) • θ)) atTop
      (@nhds _ (numericalModuleTopology p) 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const θ
    have h' := h.neg
    simpa using h'
  have hA := (ampleTendsto_of_moduleTopology p hT).eventually_sub_mem hη
  obtain ⟨N, hN⟩ := hA.exists
  refine ⟨N, ?_⟩
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h := (NativeRealNumericalClasses.ampleCone p).smul_mem hpos hN
  convert h using 1
  rw [zero_add, sub_neg_eq_add, smul_add, smul_smul]
  field_simp
  rw [one_smul, add_comm]

/-! ### The reduction -/

/-- **`DecreasingNetSelection` from the energy pairing** (the proof of [BJ22, Theorem 12.17] for
the defining nets of psh metrics). Let `(φ_i)` be a decreasing net of rational GF functions with
classes converging to `c₁(L)` and limit `φ ≢ -∞`.

1. Choose an ample class `ω = L + (N+1) S` such that `ω - c₁(φ_i)` is ample for `i ≥ i₀`; then
   `φ_i ∈ 𝓗^gf_ℚ(ω)` for `i ≥ i₀` (`exists_package_picardClass_of_ample_gap`).
2. For every `M ∈ ℕ`, the truncations `max(φ_i, -M)` are uniformly bounded `ω`-psh PL functions,
   so they converge along an increasing sequence `j_M` at every charged point
   (`exists_monotone_tendsto_truncation`).
3. Diagonalize: an increasing `k` with `k(n) ≥ j_M(n)` for `M ≤ n`, and with the class gaps of
   `approximatingSequence_of_selection`. Then `φ_{k(n)} → φ` on the divisorial set and at
   `v_triv`.
4. The limit `ψ` of `φ_{k(n)}` is a psh metric of class `L`, `ψ ≥ φ`, and `ψ = φ` on the
   determining set; by the comparison theorem `ψ = φ`. -/
theorem decreasingNetSelection_of_ampleEnergyPairing (hcomp : DivisorialComparison p)
    (hE : ∀ ω : RationalPicardSpace X,
      SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p →
        Nonempty (AmpleEnergyPairing p ω)) :
    DecreasingNetSelection.{u} p := by
  classical
  intro L φ D hne hclass hlim
  have : IsDirected D.I (· ≤ ·) := D.directed
  have hφeq : φ = D.limit p := D.eq_limit_of_tendsto p hlim
  have hφle (i : D.I) (v : BerkovichPoint p) : φ v ≤ (D.term i).eval p v := by
    rw [hφeq]; exact D.limit_le p i v
  -- 1. an ample class above the tail of the net
  obtain ⟨S, hS⟩ := NativeRealNumericalClasses.exists_geometric_ample_line p
  let s : RationalPicardSpace X := rationalPicardClass (atlasOfInvertible hS.isInvertible)
  let η := NativeRealNumericalClasses.lineClass p S hS.isInvertible
  have hη : η ∈ NativeRealNumericalClasses.ampleCone p :=
    NativeRealNumericalClasses.ampleLineClass_mem_ampleCone p S hS
  have hclassSmul (q : ℚ) : SGPT.NAPotential.BJ.NativePicard.numericalClass p (L + q • s) =
      SGPT.NAPotential.BJ.NativePicard.numericalClass p L + (q : ℝ) • η := by
    rw [map_add, SGPT.NAPotential.BJ.NativePicard.numericalClass_rat_smul, SGPT.NAPotential.BJ.NativePicard.numericalClass_line,
      ← Rat.cast_smul_eq_qsmul ℝ]
  set θ := SGPT.NAPotential.BJ.NativePicard.numericalClass p L
  obtain ⟨N, hN⟩ := exists_add_nsmul_mem_ampleCone p θ η hη
  let ω : RationalPicardSpace X := L + ((N : ℚ) + 1) • s
  have hωclass : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω = θ + ((N : ℝ) + 1) • η := by
    rw [hclassSmul]; push_cast; rfl
  have hωamp : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p := by
    rw [hωclass]; exact hN
  obtain ⟨B⟩ := hE ω hωamp
  have hDamp := ampleTendsto_of_moduleTopology p hclass
  have hNη : ((N : ℝ) + 1) • η ∈ NativeRealNumericalClasses.ampleCone p :=
    (NativeRealNumericalClasses.ampleCone p).smul_mem (by positivity) hη
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp (hDamp.eventually_sub_mem hNη)
  -- the tail as a directed set, promoted into the class `ω`
  let J := {i : D.I // i₀ ≤ i}
  have : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirectedOrder J := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  have hgapω (j : J) : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω - (D.term j.1).numericalClass p ∈
      NativeRealNumericalClasses.ampleCone p := by
    rw [hωclass]; exact hi₀ j.1 j.2
  choose Eω hEωclass hEωeval using fun j : J =>
    exists_package_picardClass_of_ample_gap p (D.term j.1) ω (hgapω j)
  have hEanti : ∀ v, Antitone fun j : J => (Eω j).eval p v := by
    intro v a b hab
    simp only [hEωeval]
    exact D.decreasing v hab
  obtain ⟨r₀, hr₀⟩ := (D.term i₀).eval_trivial_finite p
  have hEbound : ∀ (j : J) v, (Eω j).eval p v ≤ (r₀ : EReal) := by
    intro j v
    rw [hEωeval, ← hr₀]
    exact (D.decreasing v j.2).trans ((D.term i₀).eval_le_trivial p v)
  -- 2. selection for every truncation level
  have hsel (M : ℕ) := exists_monotone_tendsto_truncation p B Eω hEωclass hEanti hEbound
    (-(M : ℚ))
  choose jM hjM hjMlim using hsel
  have hinfJ (v : BerkovichPoint p) : (⨅ j : J, (Eω j).eval p v) = φ v := by
    rw [hφeq]
    simp only [hEωeval]
    refine le_antisymm ?_ (le_iInf fun j => D.limit_le p j.1 v)
    refine le_iInf fun i => ?_
    obtain ⟨c, hc₀, hci⟩ := exists_ge_ge i₀ i
    exact (iInf_le _ (⟨c, hc₀⟩ : J)).trans (D.decreasing v hci)
  -- 3. diagonalization, together with the class gaps for the targets `L + ε_n S`
  have hAmp (n : ℕ) : (coeff n : ℝ) • η ∈ NativeRealNumericalClasses.ampleCone p :=
    (NativeRealNumericalClasses.ampleCone p).smul_mem (by exact_mod_cast coeff_pos n) hη
  choose iN hiN using fun n => eventually_atTop.mp (hDamp.eventually_sub_mem (hAmp n))
  have hbnd (n : ℕ) : ∃ b : D.I, (∀ M ∈ Finset.range (n + 1), (jM M n).1 ≤ b) ∧ iN n ≤ b := by
    obtain ⟨b₁, hb₁⟩ := ((Finset.range (n + 1)).image fun M => (jM M n).1).exists_le
    obtain ⟨b, hb1, hb2⟩ := exists_ge_ge b₁ (iN n)
    exact ⟨b, fun M hM => (hb₁ _ (Finset.mem_image_of_mem _ hM)).trans hb1, hb2⟩
  choose bnd hbndM hbndN using hbnd
  obtain ⟨k, hk, hkb⟩ := exists_monotone_ge bnd bnd
  have hkM (M n : ℕ) (hMn : M ≤ n) : (jM M n).1 ≤ k n :=
    (hbndM n M (Finset.mem_range.mpr (Nat.lt_succ_of_le hMn))).trans (hkb n).1
  have hkN (n : ℕ) : iN n ≤ k n := (hbndN n).trans (hkb n).1
  -- convergence at charged points
  have hcharged : ∀ v, B.pairing.IsCharged v →
      Tendsto (fun n => (D.term (k n)).eval p v) atTop (𝓝 (φ v)) := by
    intro v hv
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hφle _ v), fun b hb => ?_⟩
    have hbbot : (⊥ : EReal) < b := lt_of_le_of_lt bot_le hb
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (((-(M : ℚ) : ℚ) : ℝ) : EReal) < b := by
      induction b using EReal.rec with
      | bot => exact absurd hbbot (lt_irrefl _)
      | top => exact ⟨0, by simp⟩
      | coe r =>
        obtain ⟨M, hM⟩ := exists_nat_gt (-r)
        refine ⟨M, EReal.coe_lt_coe_iff.mpr ?_⟩
        push_cast
        linarith
    have hmaxlt : max (φ v) (((-(M : ℚ) : ℚ) : ℝ) : EReal) < b := max_lt hb hM
    have hlimM := hjMlim M v hv
    rw [hinfJ] at hlimM
    filter_upwards [hlimM.eventually (gt_mem_nhds hmaxlt), eventually_ge_atTop M] with n hn hMn
    calc (D.term (k n)).eval p v ≤ (D.term (jM M n).1).eval p v := D.decreasing v (hkM M n hMn)
      _ = (Eω (jM M n)).eval p v := (hEωeval _ v).symm
      _ ≤ max ((Eω (jM M n)).eval p v) (((-(M : ℚ) : ℚ) : ℝ) : EReal) := le_max_left _ _
      _ < b := hn
  -- 4. the limit of the selected sequence is a psh metric of class `L`
  have hgapT (n : ℕ) : SGPT.NAPotential.BJ.NativePicard.numericalClass p (L + coeff n • s) -
      (D.term (k n)).numericalClass p ∈ NativeRealNumericalClasses.ampleCone p := by
    rw [hclassSmul]
    exact hiN n (k n) (hkN n)
  choose E' hE'class hE'eval using fun n =>
    exists_package_picardClass_of_ample_gap p (D.term (k n)) (L + coeff n • s) (hgapT n)
  let D' : DecreasingGFNet.{0} p :=
    { I := ℕ
      preorder := inferInstance
      nonempty := inferInstance
      directed := inferInstance
      term := E'
      decreasing := fun v a b hab => by
        change (E' b).eval p v ≤ (E' a).eval p v
        rw [hE'eval, hE'eval]
        exact D.decreasing v (hk hab) }
  have hD'class : Tendsto (fun n => (D'.term n).numericalClass p) atTop
      (@nhds _ (numericalModuleTopology p) θ) := by
    have h := tendsto_numericalClass_add_coeff_smul p θ η
    refine h.congr fun n => ?_
    change θ + (coeff n : ℝ) • η = SGPT.NAPotential.BJ.NativePicard.numericalClass p (E' n).picardClass
    rw [hE'class, hclassSmul]
  have hD'eval (n : ℕ) (v : BerkovichPoint p) : (D'.term n).eval p v = (D.term (k n)).eval p v :=
    hE'eval n v
  set ψ := D'.limit p
  have hφψ : ∀ v, φ v ≤ ψ v := fun v => le_iInf fun n => by
    rw [hD'eval]; exact hφle _ v
  obtain ⟨v₀, hv₀⟩ := hne
  have hψ : IsModuleTopologyPSH.{0} p L ψ :=
    ⟨⟨v₀, ne_bot_of_le_ne_bot hv₀ (hφψ v₀)⟩, D', hD'class, D'.limit_tendsto p⟩
  have husc : UpperSemicontinuous φ := by
    rw [hφeq]; exact D.limit_upperSemicontinuous p
  have hψlim (v : BerkovichPoint p) :
      Tendsto (fun n => (D.term (k n)).eval p v) atTop (𝓝 (ψ v)) := by
    have h := D'.limit_tendsto p v
    exact h.congr fun n => hD'eval n v
  have hle : ∀ v ∈ sourceDivisorialSet p, ψ v ≤ φ v := fun v hv =>
    (tendsto_nhds_unique (hψlim v) (hcharged v (B.isCharged_of_mem p hv))).le
  have hψφ : ψ ≤ φ := hcomp L ψ φ hψ husc hle
  refine ⟨k, hk, fun v => ?_⟩
  have heq : ψ v = φ v := le_antisymm (hψφ v) (hφψ v)
  rw [← heq]
  exact hψlim v

/-- **`thm:BJappseq` from the energy pairing**: the comparison theorem `thm:pshdetbydiv` and the
existence of energy pairings in ample classes imply `thm:BJappseq`. -/
theorem bjAppSeq_of_ampleEnergyPairing (hcomp : DivisorialComparison p)
    (hE : ∀ ω : RationalPicardSpace X,
      SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p →
        Nonempty (AmpleEnergyPairing p ω)) :
    BJAppSeqStatement.{u} p :=
  bjAppSeq_of_selection p (decreasingNetSelection_of_ampleEnergyPairing p hcomp hE)

end SGPT.NAPotential.ThinApprox.BJ.AppSeq
