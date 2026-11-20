import SGPT.NPP.DN7Weight
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSet
import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
import SGPT.Foundations.Analysis.Pending.AdmissibleBlowupHolomorphicInverse
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition
import SGPT.Foundations.Analysis.Pending.CodimOneSupport
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient
import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# A gentle Kähler current with poles `nK({θ})` and its log resolution

Lane DN7, `thm:DNT23_C11bar`.  FPT `thm:big-metric-laplacian-rooftop`, "Passage to a modification"
(`chapters/inputs/q10-big-envelope-regularity.tex`): put `Z = E_nK({θ})`; by
`thm:positivity-loci` it is the pole set of `φ₁ ∈ PSH(X, θ)` with analytic singularities and
`θ + ddᶜφ₁ ≥ 2δ₁ω`; the logarithmic cutoff sum `φ₀` of the local Bergman kernels of `𝓘(m₀φ₁)`
(`lem:logarithmic-cutoff-sum`) has gentle analytic singularities of type `(m₀⁻¹, 𝓘(m₀φ₁))`, still
`θ + ddᶜφ₀ ≥ δ₁ω`, and its pole set is `Z`; a log resolution `π : Y → X` of `𝔞 = 𝓘(m₀φ₁)` is an
isomorphism over `X \ Z`, and on `Y` the function `φ₀ ∘ π` is `m₀⁻¹ log |s_D|²` plus a smooth
function.

Here every step is taken from TN, with the same objects:

* `thm:positivity-loci` (Boucksom, Theorem 3.17): TN
  `NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`, shifted to the
  representative `θ` (`exists_reference_potential`);
* the logarithmic cutoff sum and its resolution: TN
  `ActualOriginalSquaredDensityFullQea.exists_uniform_original_density_full_qea` (the cutoff sums
  `v_ℓ = 2^{-ℓ} log density + E 2^{-ℓ}` are `(θ - ω₀ + C 2^{-ℓ} ω₀)`-psh, have analytic
  singularities of type `(2^{-ℓ}, 𝓘(2^ℓ ψ))` and decrease to `ψ`) and
  `ActualResolvedSquaredBergmanDensity.exists_fixed_cover_resolved_smooth_positive_density`
  (an admissible principalization `f : Y → X` of `𝓘(2^ℓ ψ)`, an isomorphism over the complement
  of the zero locus, on which `density ∘ f = |g|² H` locally with `H` smooth and positive: FPT
  `lem:bergman-smoothness-and-resolution`).

New here: the pole set of the cutoff sum is exactly `nK({θ})` (`v ≥ ψ` and the Lelong-number
definition of `nK`), the zero locus of `𝓘(2^ℓψ)` lies in `nK({θ})` (so the principalization is an
isomorphism over `X \ nK({θ})`, with an explicit holomorphic section there), and the local
factorizations of `Q = density ∘ f` glue to a TN `WeightFactorization` — the gentle normal form
`v ∘ f = k⁻¹ log Q + a`, `log Q = log |g|² + smooth`.

## Main results

* `SGPT.NPP.DN7.exists_reference_potential`;
* `SGPT.NPP.DN7.exists_local_factor`;
* `SGPT.NPP.DN7.exists_gentle_resolution`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

universe u

namespace SGPT.NPP.DN7

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.FactorizedWeightForm
open SGPT.Foundations.Analysis.Pending.FactorizedWeightPsh
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.HironakaAdmissibleSequence
open SGPT.Foundations.Analysis.Pending.ActualGlobalSquaredBergmanDensity
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityThetaPsh

/-! ### Boucksom's current, shifted to the representative `θ` -/

section Reference

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **FPT `thm:positivity-loci`** (Boucksom, *Divisorial Zariski decompositions*, Theorem 3.17,
TN `exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`), with potential relative to the given
representative: for a big class `{θ}` there are a Kähler form `ω₀` and a `(θ - ω₀)`-psh potential
`ψ` whose pole set is the non-Kähler locus. -/
theorem exists_reference_potential [CompactSpace X] (hn : 0 < n) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ (ω₀ : KahlerBackground n X) (ψ : X → EReal),
      IsThetaPshPotential (θ - ω₀.form).val ψ ∧
      poleSet ψ = nonKahlerLocus (RealBottChern.ofRepresentative θ) := by
  obtain ⟨T, -, -, hpole⟩ :=
    NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn _ hbig
  obtain ⟨h, hh, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  have hsub : ThetaPlurisubharmonic (θ - T.lowerBound.form).val
      (fun y => T.potential y - (h y : EReal)) := by
    refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh (fun e z hz => ?_)
      T.strictlyPsh.1
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg]
    rw [heq e z hz]
    abel
  have hbot : ∀ y, T.potential y - (h y : EReal) = ⊥ ↔ T.potential y = ⊥ := by
    intro y
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    constructor
    · intro hb
      by_contra hne
      exact (EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩) hb
    · intro hb
      rw [hb, EReal.bot_add]
  refine ⟨T.lowerBound, fun y => T.potential y - (h y : EReal), ⟨hsub, ?_⟩, ?_⟩
  · intro x U hU hxU
    obtain ⟨y, hyU, hy⟩ := T.strictlyPsh.2 x U hU hxU
    exact ⟨y, hyU, fun hb => hy ((hbot y).mp hb)⟩
  · rw [← hpole]
    ext y
    exact hbot y

end Reference

/-! ### Local factorizations glue to a weight factorization -/

section Factor

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- A map which is `Φ ∘ chart` for an atlas chart and a local biholomorphism `Φ` of the model is
holomorphic when read in any atlas chart. -/
theorem differentiableAt_comp_chart_comp_symm {y : Y}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (e : ComplexChart n Y) {u : ComplexModel n} (hu : u ∈ e.val.target)
    (hs : e.val.symm u ∈ (complexChartAt (n := n) y).val.source)
    (hΦ : (complexChartAt (n := n) y).val (e.val.symm u) ∈ Φ.source) :
    DifferentiableAt ℂ (fun w => Φ.toFun ((complexChartAt (n := n) y).val (e.val.symm w))) u := by
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (complexChartAt (n := n) y).val (e.val.symm u) :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) (complexChartAt (n := n) y).property hs
  have hd : DifferentiableAt ℂ Φ.toFun ((complexChartAt (n := n) y).val (e.val.symm u)) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hΦ)
  have hcomp : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (Φ.toFun ∘ (complexChartAt (n := n) y).val) (e.val.symm u) :=
    hd.comp_mdifferentiableAt hc
  exact mdifferentiableAt_iff_differentiableAt.mp
    (hcomp.comp u (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hu))

/-- **A local factorization in adapted coordinates gives one on an open set of `Y`.**  If in the
coordinates `Φ ∘ chart_y` the function `Q` is `|g|² H` with `H` smooth and positive on a ball,
then on an open neighbourhood `S ⊆ V` of `y` we have `Q = |g|² U'` with `U' = H ∘ Φ ∘ chart_y`
smooth in every atlas chart and positive. -/
theorem exists_local_factor {Q : Y → ℝ} {y : Y}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)
    {g : Y → ℂ} {V : Set Y} (hV : IsOpen V) (hyV : y ∈ V)
    {H : ComplexModel n → ℝ} {r : ℝ} (hr : 0 < r) (hH : ContDiffOn ℝ ∞ H (ball 0 r))
    (hall : ∀ z ∈ ball (0 : ComplexModel n) r, 0 < H z ∧
      Q ((complexChartAt (n := n) y).val.symm (Φ.invFun z)) =
        ‖g ((complexChartAt (n := n) y).val.symm (Φ.invFun z))‖ ^ 2 * H z) :
    ∃ (S : Set Y) (U' : Y → ℝ), IsOpen S ∧ y ∈ S ∧ S ⊆ V ∧
      (∀ e : ComplexChart n Y, ContDiffOn ℝ ∞ (fun u => U' (e.val.symm u))
        (e.val.target ∩ e.val.symm ⁻¹' S)) ∧
      (∀ y' ∈ S, 0 < U' y') ∧ (∀ y' ∈ S, Q y' = Complex.normSq (g y') * U' y') := by
  have hΦo : IsOpen (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r) :=
    Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_source isOpen_ball
  have hS1 : IsOpen ((complexChartAt (n := n) y).val.source ∩
      (complexChartAt (n := n) y).val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r)) :=
    (complexChartAt (n := n) y).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) y).val.open_source hΦo
  refine ⟨V ∩ ((complexChartAt (n := n) y).val.source ∩
      (complexChartAt (n := n) y).val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r)),
    fun y' => H (Φ.toFun ((complexChartAt (n := n) y).val y')), hV.inter hS1, ?_,
    inter_subset_left, fun e => ?_, fun y' hy' => (hall _ hy'.2.2.2).1, fun y' hy' => ?_⟩
  · refine ⟨hyV, mem_complexChartAt_source y, Φ.center_mem_source, ?_⟩
    rw [mem_preimage, h0]
    exact mem_ball_self hr
  · have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (V ∩ ((complexChartAt (n := n) y).val.source ∩
        (complexChartAt (n := n) y).val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r)))) :=
      e.val.isOpen_inter_preimage_symm (hV.inter hS1)
    have hGd : DifferentiableOn ℂ
        (fun w => Φ.toFun ((complexChartAt (n := n) y).val (e.val.symm w)))
        (e.val.target ∩ e.val.symm ⁻¹' (V ∩ ((complexChartAt (n := n) y).val.source ∩
          (complexChartAt (n := n) y).val ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 r)))) :=
      fun w hw =>
        (differentiableAt_comp_chart_comp_symm Φ e hw.1 hw.2.2.1 hw.2.2.2.1).differentiableWithinAt
    have hG := contDiffOn_of_differentiableOn_complex hGd hO
    exact hH.comp (hG.restrict_scalars ℝ) fun w hw => hw.2.2.2.2
  · have h := (hall _ hy'.2.2.2).2
    have hinv : (complexChartAt (n := n) y).val.symm
        (Φ.invFun (Φ.toFun ((complexChartAt (n := n) y).val y'))) = y' := by
      rw [Φ.left_inv _ hy'.2.2.1, (complexChartAt (n := n) y).val.left_inv hy'.2.1]
    rw [hinv] at h
    rw [h, Complex.normSq_eq_norm_sq]

end Factor

/-! ### The gentle current and its resolution -/

section Gentle

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- **FPT, passage to a modification: the gentle Kähler current and its log resolution.**  For
a big class `{θ}` on a compact complex manifold of positive dimension there are

* a Kähler form `ω₀` on `X`, a number `0 ≤ s ≤ 1/2` and a `(θ - (1 - s) ω₀)`-psh potential `v`
  (a Kähler current `θ + ddᶜv ≥ (1 - s)ω₀`) whose pole set is exactly `nK({θ})`;
* a finite sequence of blowups with smooth centres `f : Y → X` (`Y` compact), an analytic
  modification, which is an isomorphism over `X \ nK({θ})` with a holomorphic section there;
* a weight `Q ≥ 0` on `Y` with a TN `WeightFactorization` (locally `Q = |g|² × smooth positive`)
  such that `v ∘ f = k⁻¹ log Q + a` for some `k > 0` and real `a`: the gentle normal form of
  FPT `def:gentle-analytic-singularities` on this log resolution. -/
theorem exists_gentle_resolution [CompactSpace X] (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ (ω₀ : KahlerBackground (m + 1) X) (s : ℝ) (v : X → EReal) (k : ℕ) (a : ℝ)
      (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (f : Y → X) (Q : Y → ℝ)
      (_ : WeightFactorization (m + 1) Q),
      0 ≤ s ∧ s ≤ 1 / 2 ∧ 0 < k ∧
      IsThetaPshPotential (θ - ω₀.form + s • ω₀.form).val v ∧
      poleSet v = nonKahlerLocus (RealBottChern.ofRepresentative θ) ∧
      IsBlowupSequence (m + 1) X Y f ∧ CompactSpace Y ∧
      IsAnalyticModification (n := m + 1) f ∧
      IsIsomorphismOver (m + 1) f (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ ∧
      (∃ σ : X → Y, ContMDiffOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ σ
          (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ ∧
        (∀ x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ), f (σ x) = x) ∧
        ∀ y, f y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ) → σ (f y) = y) ∧
      ∀ y, v (f y) = (((k : ℝ)⁻¹ : ℝ) : EReal) * logWeight Q y + (a : EReal) := by
  classical
  set α := RealBottChern.ofRepresentative θ with hαdef
  obtain ⟨ω₀, ψ, hψ, hpoleψ⟩ := exists_reference_potential (Nat.succ_pos m) θ hbig
  obtain ⟨F, hF⟩ :=
    ActualResolvedSquaredBergmanDensity.exists_fixed_cover_resolved_smooth_positive_density
      (m := m) (X := X)
  obtain ⟨C, E, hC, hE, hqea⟩ :=
    ActualOriginalSquaredDensityFullQea.exists_uniform_original_density_full_qea F ω₀
  obtain ⟨ρ, hρ, hres⟩ := hF (θ - ω₀.form) ψ hψ
  obtain ⟨htype, happrox⟩ := hqea (θ - ω₀.form) ρ hρ ψ hψ
  -- a dyadic level with curvature loss at most `1/2`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, C * ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 / 2 := by
    obtain ⟨ℓ, hℓ⟩ := pow_unbounded_of_one_lt (2 * C) (by norm_num : (1 : ℝ) < 2)
    refine ⟨ℓ, ?_⟩
    have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ h2]
    linarith
  set s : ℝ := C * ((2 : ℝ) ^ ℓ)⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  set a : ℝ := E * ((2 : ℝ) ^ ℓ)⁻¹ with ha
  set v : X → EReal := fun x => originalWeight F ρ ψ (2 ^ ℓ) x + (a : EReal) with hvdef
  have hv : IsThetaPshPotential (θ - ω₀.form + s • ω₀.form).val v := happrox.term ℓ
  have hvψ : ∀ x, ψ x ≤ v x := fun x =>
    (happrox.decreasesPointwise.1 x).le_of_tendsto (happrox.decreasesPointwise.2 x) ℓ
  -- the pole set of `v` is the non-Kähler locus
  have hs1 : 0 < 1 - s := by linarith
  have hform : θ - (KahlerBackground.smul hs1 ω₀).form = θ - ω₀.form + s • ω₀.form := by
    rw [KahlerBackground.smul_form, sub_smul, one_smul]
    abel
  have hpole : poleSet v = nonKahlerLocus α := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : v x = ⊥ := hx
      rw [← hpoleψ]
      show ψ x = ⊥
      exact le_bot_iff.mp (hx' ▸ hvψ x)
    · intro x hx
      let T : KahlerCurrent α :=
        { representative := θ
          represents := rfl
          potential := v
          lowerBound := KahlerBackground.smul hs1 ω₀
          strictlyPsh := by rw [hform]; exact hv }
      exact eq_bot_of_lelongNumber_pos (Nat.succ_pos m) T.strictlyPsh.1 (hx T)
  -- the resolution of `𝓘(2^ℓ ψ)`
  obtain ⟨-, Y, tY, chY, mY, f, D, Ediv, hseq, -, -, -, hsupp, hiso, hfactor⟩ :=
    hres (2 ^ ℓ) (by positivity)
  let := tY
  let := chY
  let := mY
  set 𝔞 := multiplierIdeal (n := m + 1) (((2 ^ ℓ : ℕ) : ℕ) : ℝ) ψ with h𝔞
  have hblow : IsBlowupSequence (m + 1) X Y f := hseq.isBlowupSequence
  obtain ⟨hcpt, hsurj⟩ := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hblow
  have hcoh : 𝔞.IsCoherent := (htype ℓ).2.1
  have hmod : IsAnalyticModification (n := m + 1) f :=
    AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
      hcoh hseq D hsupp
  set Q : Y → ℝ := fun y => density F ρ ψ (2 ^ ℓ) (f y) with hQdef
  have hvQ : ∀ y, v (f y) = ((((2 ^ ℓ : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * logWeight Q y + (a : EReal) :=
    fun y => rfl
  -- the zero locus of `𝔞` lies in `nK`
  have hzero : 𝔞.zeroLocus ⊆ nonKahlerLocus α := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    have hyD : y ∈ D.support := by rw [hsupp]; exact hx
    obtain ⟨Φ, -, h0, g, hg, hgen, H, r, hr, -, -, hall⟩ := hfactor y
    have hyD' : ∀ b, D.ideal.mem y b → b y = 0 := hyD
    have hgy : g y = 0 := hyD' g ((hgen g).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hg))
    have hT0 : (complexChartAt (n := m + 1) y).val.symm (Φ.invFun 0) = y := by
      rw [← h0, Φ.left_inv _ Φ.center_mem_source]
      exact (complexChartAt (n := m + 1) y).val.left_inv (mem_complexChartAt_source y)
    have hQ0 := (hall 0 (mem_ball_self hr)).2
    simp only [hT0, hgy, norm_zero] at hQ0
    have hQy : Q y = 0 := by
      show density F ρ ψ (2 ^ ℓ) (f y) = 0
      rw [hQ0]
      ring
    rw [← hpole]
    show v (f y) = ⊥
    rw [hvQ y, logWeight, hQy, ENNReal.ofReal_zero, ENNReal.log_zero,
      EReal.coe_mul_bot_of_pos (inv_pos.mpr (by positivity)), EReal.bot_add]
  have hsub : (nonKahlerLocus α)ᶜ ⊆ 𝔞.zeroLocusᶜ := compl_subset_compl.mpr hzero
  have hiso' : IsIsomorphismOver (m + 1) f (nonKahlerLocus α)ᶜ := by
    refine ⟨⟨fun y hy => hy, hiso.1.injOn.mono (preimage_mono hsub), fun x hx => ?_⟩,
      hiso.2.mono_left (preimage_mono hsub)⟩
    obtain ⟨y, -, rfl⟩ := hiso.1.surjOn (hsub hx)
    exact ⟨y, hx, rfl⟩
  -- the holomorphic section over the complement of the zero locus, restricted to `X \ nK`
  have hzc : IsClosed 𝔞.zeroLocus :=
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hcoh).isClosed
  obtain ⟨s₀, hs₀, hright, hleft⟩ :=
    AdmissibleBlowupHolomorphicInverse.exists_section_compl hzc hseq
  let σ : X → Y := fun x =>
    if hx : x ∈ 𝔞.zeroLocusᶜ then s₀ ⟨x, hx⟩ else Classical.choose (hsurj x)
  have hσ : ContMDiffOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ σ
      𝔞.zeroLocusᶜ := by
    have hrestrict : (fun x : (⟨𝔞.zeroLocusᶜ, hzc.isOpen_compl⟩ :
        TopologicalSpace.Opens X) => σ x) = s₀ := by
      funext x
      change (if hx : x.1 ∈ 𝔞.zeroLocusᶜ then s₀ ⟨x.1, hx⟩ else _) = s₀ x
      exact dif_pos x.2
    have hsd : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
        (fun x : (⟨𝔞.zeroLocusᶜ, hzc.isOpen_compl⟩ : TopologicalSpace.Opens X) => σ x) :=
      hrestrict ▸ hs₀
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hsd ⟨x, hx⟩)).contMDiffWithinAt
  -- the weight factorization of `Q`
  have hloc : ∀ y : Y, ∃ (S : Set Y) (g : Y → ℂ) (U' : Y → ℝ), IsOpen S ∧ y ∈ S ∧
      (∀ y' ∈ S, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g y') ∧
      (∀ e : ComplexChart (m + 1) Y, ContDiffOn ℝ ∞ (fun u => U' (e.val.symm u))
        (e.val.target ∩ e.val.symm ⁻¹' S)) ∧
      (∀ y' ∈ S, 0 < U' y') ∧ (∀ y' ∈ S, Q y' = Complex.normSq (g y') * U' y') ∧
      (∀ W : Set Y, IsOpen W → W ⊆ S → W.Nonempty → ∃ t ∈ W, g t ≠ 0) := by
    intro y
    obtain ⟨Φ, -, h0, g, hg, hgen, H, r, hr, hH, -, hall⟩ := hfactor y
    obtain ⟨V, hV, hyV, hgV, hnon, -⟩ :=
      ActualOriginalSquaredDensityGentle.exists_local_equation_of_germ_generator D hg hgen
    obtain ⟨S, U', hS, hyS, hSV, hsm, hpos, hfac⟩ :=
      exists_local_factor (Q := Q) Φ h0 hV hyV hr hH hall
    exact ⟨S, g, U', hS, hyS, fun y' hy' => hgV.mdifferentiableAt (hV.mem_nhds (hSV hy')),
      hsm, hpos, hfac, fun W hW hWS hne => hnon W hW (hWS.trans hSV) hne⟩
  choose S g U' hS hyS hgd hsm hpos hfac hnon using hloc
  let FQ : WeightFactorization (m + 1) Q :=
    { domain := S
      isOpen_domain := hS
      mem_domain := hyS
      gen := g
      smoothPart := U'
      gen_mdifferentiable := hgd
      smooth := hsm
      pos := hpos
      factor := hfac
      nowhereZero := fun W hW hne => by
        obtain ⟨y, hy⟩ := hne
        obtain ⟨t, ⟨htW, htS⟩, hgt⟩ :=
          hnon y (W ∩ S y) (hW.inter (hS y)) inter_subset_right ⟨y, hy, hyS y⟩
        refine ⟨t, htW, ?_⟩
        rw [hfac y t htS]
        exact mul_ne_zero (Complex.normSq_pos.mpr hgt).ne' (hpos y t htS).ne' }
  refine ⟨ω₀, s, v, 2 ^ ℓ, a, Y, tY, chY, mY, f, Q, FQ, hs0, hℓ, by positivity, hv, hpole,
    hblow, hcpt, hmod, hiso', ⟨σ, hσ.mono hsub, fun x hx => ?_, fun y hy => ?_⟩, hvQ⟩
  · have hx' : x ∈ 𝔞.zeroLocusᶜ := hsub hx
    show f (if hx : x ∈ 𝔞.zeroLocusᶜ then s₀ ⟨x, hx⟩ else _) = x
    rw [dif_pos hx']
    exact congrFun hright ⟨x, hx'⟩
  · have hy' : f y ∈ 𝔞.zeroLocusᶜ := hsub hy
    show (if hx : f y ∈ 𝔞.zeroLocusᶜ then s₀ ⟨f y, hx⟩ else _) = y
    rw [dif_pos hy']
    exact hleft y hy'

end Gentle

end SGPT.NPP.DN7
