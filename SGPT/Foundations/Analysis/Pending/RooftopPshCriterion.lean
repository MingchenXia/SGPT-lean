import SGPT.Foundations.Analysis.Pending.RelativeFullMass
import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

set_option autoImplicit false

/-!
# When is a rooftop not identically `-∞`? (Xia, Proposition 3.1.5)

Xia, SGPT, Proposition 3.1.5 (`xia-sgpt:page-0104`--`page-0105`): if
`φ, ψ ∈ PSH(X, θ)` satisfy

  `∫ θ^n_φ + ∫ θ^n_ψ > ∫ θ^n_{φ ∨ ψ}`,                    (3.12)

then `φ ∧ ψ = P_θ(min(φ, ψ)) ∈ PSH(X, θ)`
(`isThetaPshPotential_rooftopEnvelope_min_of_mass_lt`).

Also proved here, as inputs:

* Xia's Lemma 3.1.1 (`xia-sgpt:page-0099`), in measure form
  (`rooftopMeasure_le_contact`): `θ^n_{φ∧ψ} ≤ 1_{φ∧ψ=φ} θ^n_φ + 1_{φ∧ψ=ψ} θ^n_ψ`;
* a Dini-type compactness lemma (`exists_forall_lt_of_antitone_iInf_eq_bot`).

## The proof (Xia's, step by step)

Put `η = P_θ[φ ∨ ψ]`, a model potential of mass `∫ θ^n_{φ∨ψ} > 0`.  Choose `C`
with `θ^n_φ{φ > η - C} + θ^n_ψ{ψ > η - C} > ∫ θ^n_η` (continuity from below;
the poles are null).  For `C_j = C + 1 + j` let `γ_j = (φ ∨ (η - C_j)) ∧ (ψ ∨ (η - C_j))`,
a decreasing sequence of potentials with the singularity type of `η`.  If
`φ ∧ ψ` were not `θ`-PSH, `γ_j` would decrease to `-∞` everywhere (otherwise its
limit is a `θ`-PSH minorant of `φ` and `ψ`), so by compactness some `γ_j ≤ -C`,
whence `γ_j + C ≤ P_θ[η] = η`.  Lemma 3.1.1 then gives
`∫ θ^n_η = ∫ θ^n_{γ_j} ≤ (∫ θ^n_η - θ^n_φ{φ > η - C}) + (∫ θ^n_η - θ^n_ψ{ψ > η - C}) < ∫ θ^n_η`,
using plurifine locality on `{φ > η - C_j}` and the monotonicity theorem.
Xia's Proposition 3.1.4 enters only through its easy half, which is the
definition of `P_θ[η]` together with `P_θ[η] = η`.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopPshCriterion

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

/-- **Dini for `-∞`.**  An antitone sequence of upper semicontinuous functions on
a compact space whose pointwise infimum is `⊥` everywhere is eventually below
every level `K > ⊥`, uniformly. -/
theorem exists_forall_lt_of_antitone_iInf_eq_bot {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {g : ℕ → X → EReal} (hg : ∀ j, UpperSemicontinuous (g j))
    (hanti : ∀ x, Antitone fun j => g j x) (hbot : ∀ x, ⨅ j, g j x = ⊥)
    {K : EReal} (hK : ⊥ < K) : ∃ j, ∀ x, g j x < K := by
  have hcover : (univ : Set X) ⊆ ⋃ j, g j ⁻¹' Iio K := by
    intro x _
    have hlt : ⨅ j, g j x < K := by rw [hbot x]; exact hK
    obtain ⟨j, hj⟩ := iInf_lt_iff.mp hlt
    exact mem_iUnion.mpr ⟨j, hj⟩
  have hmono : Monotone fun j => g j ⁻¹' Iio K := fun i j hij x hx =>
    lt_of_le_of_lt (hanti x hij) hx
  obtain ⟨j, hj⟩ := isCompact_univ.elim_directed_cover (fun j => g j ⁻¹' Iio K)
    (fun j => (hg j).isOpen_preimage K) hcover hmono.directed_le
  exact ⟨j, fun x => hj (mem_univ x)⟩

/-- An extended real below every `r - j` is `⊥`. -/
theorem eq_bot_of_forall_le_sub_nat {y : EReal} (r : ℝ)
    (h : ∀ j : ℕ, y ≤ ((r - j : ℝ) : EReal)) : y = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro z
  obtain ⟨j, hj⟩ := exists_nat_gt (r - z)
  exact lt_of_le_of_lt (h j) (EReal.coe_lt_coe_iff.mpr (by linarith))

/-- A strict and a non-strict comparison of shifts that cannot both hold. -/
theorem not_lt_of_add_le {a b : EReal} (ha : a ≠ ⊤) (C : ℝ)
    (h1 : a + ((-C : ℝ) : EReal) < b) (h2 : b + (C : EReal) ≤ a) : False := by
  induction a using EReal.rec with
  | bot =>
    simp only [EReal.bot_add] at h1
    rcases EReal.add_eq_bot_iff.mp (le_bot_iff.mp h2) with h | h
    · exact (ne_of_gt h1) h
    · exact EReal.coe_ne_bot C h
  | top => exact ha rfl
  | coe r =>
    induction b using EReal.rec with
    | bot => simp at h1
    | top => simp at h2
    | coe s =>
      rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h1
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2
      linarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- A rooftop with a common `θ`-PSH minorant is `θ`-PSH, lies above the
minorant and below both obstacles. -/
theorem rooftop_min_of_lower [Nonempty M] (theta : ClosedRealOneOneForm n M)
    {u v L : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (hL : IsThetaPshPotential theta.val L)
    (hLu : L ≤ u) (hLv : L ≤ v) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val (fun x => min (u x) (v x))) ∧
      L ≤ rooftopEnvelope theta.val (fun x => min (u x) (v x)) ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ u ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ v := by
  have heq : (fun x => min (u x) (v x + ((0 : ℝ) : EReal))) = fun x => min (u x) (v x) := by
    funext x; simp
  have hpsh := isThetaPshPotential_rooftop_min_add_const_of_common_thetaPsh_lower_qe
    theta u v L hu hL (quasiEverywhere_of_forall fun x => hLu x) 0
    (quasiEverywhere_of_forall fun x => by simpa using hLv x)
  have hobs := rooftopEnvelope_min_add_const_le_obstacles (θ := theta.val) hu.1 hv.1 0
  rw [heq] at hpsh hobs
  refine ⟨hpsh, le_rooftopEnvelope hL (quasiEverywhere_of_forall fun x =>
    le_min (hLu x) (hLv x)), hobs.1, fun x => ?_⟩
  simpa using hobs.2 x

/-- **Xia, Lemma 3.1.1 (`xia-sgpt:page-0099`), measure form.**  The
non-pluripolar measure of a rooftop `w = φ ∧ ψ` is dominated by `θ^n_φ` on the
contact set `{w = φ}` plus `θ^n_ψ` on `{w = ψ}`. -/
theorem rooftopMeasure_le_contact [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))))
    (hwu : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ u)
    (hwv : rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ v)
    {E : Set M} (hE : MeasurableSet E) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hw E ≤
      diagonalPotentialMeasure theta u hu
          (E ∩ {x | rooftopEnvelope theta.val (fun y => min (u y) (v y)) x = u x}) +
        diagonalPotentialMeasure theta v hv
          (E ∩ {x | rooftopEnvelope theta.val (fun y => min (u y) (v y)) x = v x}) := by
  set w := rooftopEnvelope theta.val (fun x => min (u x) (v x)) with hwdef
  have hN : diagonalPotentialMeasure theta w hw {x | w x ≠ u x ∧ w x ≠ v x} = 0 :=
    RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero
      omega theta hu hv hw
  have hsub : E ⊆ ((E ∩ {x | w x = u x}) ∪ (E ∩ {x | w x = v x})) ∪
      {x | w x ≠ u x ∧ w x ≠ v x} := by
    intro x hx
    by_cases h1 : w x = u x
    · exact Or.inl (Or.inl ⟨hx, h1⟩)
    · by_cases h2 : w x = v x
      · exact Or.inl (Or.inr ⟨hx, h2⟩)
      · exact Or.inr ⟨h1, h2⟩
  calc diagonalPotentialMeasure theta w hw E
      ≤ diagonalPotentialMeasure theta w hw (((E ∩ {x | w x = u x}) ∪
          (E ∩ {x | w x = v x})) ∪ {x | w x ≠ u x ∧ w x ≠ v x}) := measure_mono hsub
    _ ≤ diagonalPotentialMeasure theta w hw ((E ∩ {x | w x = u x}) ∪
          (E ∩ {x | w x = v x})) +
        diagonalPotentialMeasure theta w hw {x | w x ≠ u x ∧ w x ≠ v x} :=
        measure_union_le _ _
    _ = diagonalPotentialMeasure theta w hw ((E ∩ {x | w x = u x}) ∪
          (E ∩ {x | w x = v x})) := by rw [hN, add_zero]
    _ ≤ diagonalPotentialMeasure theta w hw (E ∩ {x | w x = u x}) +
        diagonalPotentialMeasure theta w hw (E ∩ {x | w x = v x}) := measure_union_le _ _
    _ ≤ _ := add_le_add (MaxMassDecomposition.contact_measure_le omega hw hu hwu hE)
        (MaxMassDecomposition.contact_measure_le omega hw hv hwv hE)

/-- Two potentials squeezed between translates of each other have the same mass. -/
theorem diagonalPotentialMass_eq_of_le_add (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {a b : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    {c₁ c₂ : ℝ} (h₁ : ∀ x, b x + ((-c₁ : ℝ) : EReal) ≤ a x) (h₂ : ∀ x, a x ≤ b x + (c₂ : EReal)) :
    diagonalPotentialMass theta a ha = diagonalPotentialMass theta b hb := by
  refine le_antisymm (diagonalPotentialMass_mono_of_kahler omega ha hb ⟨c₂, fun x _ => h₂ x⟩)
    (diagonalPotentialMass_mono_of_kahler omega hb ha ⟨c₁, fun x _ => ?_⟩)
  calc b x = b x + ((-c₁ : ℝ) : EReal) + (c₁ : EReal) := by
        rw [add_assoc, ← EReal.coe_add]; simp
    _ ≤ a x + (c₁ : EReal) := add_le_add (h₁ x) le_rfl

/-- **Xia, Proposition 3.1.5 (`xia-sgpt:page-0104`--`page-0105`).**  On a
connected compact Kähler manifold, if
`∫ θ^n_{φ ∨ ψ} < ∫ θ^n_φ + ∫ θ^n_ψ`, then the rooftop `φ ∧ ψ = P_θ(min(φ, ψ))`
is a `θ`-PSH potential.

Implementation note: Xia truncates at `η - C_j` with `η = P_θ[φ ∨ ψ]` and uses
`P_θ[η] = η`, whose proof (Theorem 3.1.2) goes through the domination principle.
We truncate at `(φ ∨ ψ) - C_j` instead, so that the competitor argument only
needs the definition of `P_θ[φ ∨ ψ]`; `η` still measures the levels. -/
theorem isThetaPshPotential_rooftopEnvelope_min_of_mass_lt [ConnectedSpace M] [Nonempty M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hgt : diagonalPotentialMass theta (fun x => max (phi x) (psi x))
        (IsThetaPshPotential.max hphi hpsi) <
      diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) := by
  classical
  by_contra H
  set rho : M → EReal := fun x => max (phi x) (psi x) with hrho_def
  have hrho : IsThetaPshPotential theta.val rho := IsThetaPshPotential.max hphi hpsi
  have hfinite : ∀ {a : M → EReal} (ha : IsThetaPshPotential theta.val a),
      IsFiniteMeasure (diagonalPotentialMeasure theta a ha) := fun ha =>
    GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega (fun _ => ha.1)
  have hrhotop : ∀ x, rho x ≠ ⊤ := fun x => hrho.1.quasiPlurisubharmonic.ne_top x
  -- `η = P_θ[φ ∨ ψ]` measures the levels
  set eta : M → EReal := singularityEnvelope theta.val rho with heta_def
  have heta : IsThetaPshPotential theta.val eta :=
    singularityEnvelope_isThetaPshPotential theta.val theta.property.1 theta.property.2
      hrho.1.hasSmoothLocalPotentials _ hrho
  have hmeta : diagonalPotentialMass theta eta heta = diagonalPotentialMass theta rho hrho :=
    singularityEnvelopeMassPreserving omega theta _ hrho heta
  have hetatop : ∀ x, eta x ≠ ⊤ := fun x => heta.1.quasiPlurisubharmonic.ne_top x
  obtain ⟨c₀, hc₀⟩ := moreSingularOn_singularityEnvelope hrho
  set c : ℝ := max c₀ 0 with hc_def
  have hc0 : 0 ≤ c := le_max_right _ _
  have hrhoeta : ∀ x, rho x ≤ eta x + (c : EReal) := fun x =>
    (hc₀ x (mem_univ x)).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
  have hsh : ∀ {f : M → EReal}, IsThetaPshPotential theta.val f → ∀ t : ℝ,
      IsThetaPshPotential theta.val (fun x => f x + ((-t : ℝ) : EReal)) := fun hf t =>
    hf.add_const (-t)
  have hshmono : ∀ (f : M → EReal) {s t : ℝ}, s ≤ t → ∀ x,
      f x + ((-t : ℝ) : EReal) ≤ f x + ((-s : ℝ) : EReal) := fun f s t hst x =>
    add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (neg_le_neg hst))
  -- Step 1: a level `C` capturing almost all of both masses
  have hlevel : ∀ {u : M → EReal} (hu : IsThetaPshPotential theta.val u),
      Tendsto (fun k : ℕ => diagonalPotentialMeasure theta u hu
        {x | eta x + ((-(k : ℝ) : ℝ) : EReal) < u x}) atTop
        (𝓝 (diagonalPotentialMass theta u hu)) := by
    intro u hu
    have hmonoS : Monotone fun k : ℕ => {x | eta x + ((-(k : ℝ) : ℝ) : EReal) < u x} :=
      fun i j hij x hx => lt_of_le_of_lt (hshmono eta (by exact_mod_cast hij) x) hx
    have hlim := tendsto_measure_iUnion_atTop (μ := diagonalPotentialMeasure theta u hu) hmonoS
    have hunion : diagonalPotentialMeasure theta u hu
        (⋃ k : ℕ, {x | eta x + ((-(k : ℝ) : ℝ) : EReal) < u x}) =
        diagonalPotentialMass theta u hu := by
      refine le_antisymm (measure_mono (subset_univ _)) ?_
      have hpole : diagonalPotentialMeasure theta u hu {x | u x = ⊥} = 0 :=
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate (fun _ => hu.1) hu
      have hcov : (univ : Set M) ⊆
          (⋃ k : ℕ, {x | eta x + ((-(k : ℝ) : ℝ) : EReal) < u x}) ∪ {x | u x = ⊥} := by
        intro x _
        by_cases hux : u x = ⊥
        · exact Or.inr hux
        · left
          have hutop : u x ≠ ⊤ := hu.1.quasiPlurisubharmonic.ne_top x
          by_cases hex : eta x = ⊥
          · refine mem_iUnion.mpr ⟨0, ?_⟩
            show eta x + _ < u x
            rw [hex, EReal.bot_add]
            exact Ne.bot_lt hux
          · obtain ⟨k, hk⟩ := exists_nat_gt ((eta x).toReal - (u x).toReal)
            refine mem_iUnion.mpr ⟨k, ?_⟩
            show eta x + _ < u x
            rw [← EReal.coe_toReal (hetatop x) hex, ← EReal.coe_toReal hutop hux,
              ← EReal.coe_add, EReal.coe_lt_coe_iff]
            linarith
      calc diagonalPotentialMass theta u hu
          = diagonalPotentialMeasure theta u hu univ := rfl
        _ ≤ diagonalPotentialMeasure theta u hu
              ((⋃ k : ℕ, {x | eta x + ((-(k : ℝ) : ℝ) : EReal) < u x}) ∪ {x | u x = ⊥}) :=
            measure_mono hcov
        _ ≤ _ := (measure_union_le _ _).trans (by rw [hpole, add_zero])
    rw [hunion] at hlim
    exact hlim
  have hgt' : diagonalPotentialMass theta eta heta <
      diagonalPotentialMass theta phi hphi + diagonalPotentialMass theta psi hpsi := by
    rw [hmeta]; exact hgt
  obtain ⟨C, hC⟩ := (((hlevel hphi).add (hlevel hpsi)).eventually
    (lt_mem_nhds hgt')).exists
  -- Step 2: the decreasing sequence `γ_j`, truncated at `(φ ∨ ψ) - C_j`
  set Cj : ℕ → ℝ := fun j => (C : ℝ) + c + 1 + j with hCj
  have hCjC : ∀ j, (C : ℝ) + c ≤ Cj j := fun j => by
    simp only [hCj]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hCjmono : Monotone Cj := fun i j hij => by
    simp only [hCj]; have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  set phij : ℕ → M → EReal := fun j x => max (phi x) (rho x + ((-Cj j : ℝ) : EReal))
    with hphij
  set psij : ℕ → M → EReal := fun j x => max (psi x) (rho x + ((-Cj j : ℝ) : EReal))
    with hpsij
  have hphij_psh : ∀ j, IsThetaPshPotential theta.val (phij j) := fun j =>
    IsThetaPshPotential.max hphi (hsh hrho (Cj j))
  have hpsij_psh : ∀ j, IsThetaPshPotential theta.val (psij j) := fun j =>
    IsThetaPshPotential.max hpsi (hsh hrho (Cj j))
  have hroofj := fun j => rooftop_min_of_lower theta (hphij_psh j) (hpsij_psh j)
    (hsh hrho (Cj j)) (fun x => le_max_right _ _) (fun x => le_max_right _ _)
  set gam : ℕ → M → EReal := fun j =>
    rooftopEnvelope theta.val (fun x => min (phij j x) (psij j x)) with hgam
  have hgam_psh : ∀ j, IsThetaPshPotential theta.val (gam j) := fun j => (hroofj j).1
  have hgam_anti : ∀ x, Antitone fun j => gam j x := by
    intro x i j hij
    refine rooftopEnvelope_mono (fun y => min_le_min ?_ ?_) x
    · exact max_le_max le_rfl (hshmono rho (hCjmono hij) y)
    · exact max_le_max le_rfl (hshmono rho (hCjmono hij) y)
  -- below `φ ∨ ψ`
  have hjle : ∀ {u : M → EReal}, (∀ x, u x ≤ rho x) → ∀ j x,
      max (u x) (rho x + ((-Cj j : ℝ) : EReal)) ≤ rho x := by
    intro u hu j x
    refine max_le (hu x) ?_
    calc rho x + ((-Cj j : ℝ) : EReal) ≤ rho x + ((-0 : ℝ) : EReal) :=
          hshmono rho (by linarith [hCjC j, (Nat.cast_nonneg C : (0 : ℝ) ≤ C)]) x
      _ = rho x := by simp
  have hgamrho : ∀ j x, gam j x ≤ rho x := fun j x =>
    ((hroofj j).2.2.1 x).trans (hjle (fun x => le_max_left _ _) j x)
  -- if `φ ∧ ψ` is not `θ`-PSH, the `γ_j` decrease to `-∞` everywhere
  have hbot : ∀ x, ⨅ j, gam j x = ⊥ := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := not_forall.mp hne
    have hLpsh : ThetaPlurisubharmonic theta.val (fun x => ⨅ j, gam j x) :=
      ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
        (fun j => (hgam_psh j).1) hgam_anti
    have hL : IsThetaPshPotential theta.val (fun x => ⨅ j, gam j x) :=
      ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot hLpsh ⟨x₀, hx₀⟩
    have hLle : ∀ {u : M → EReal}, (∀ j x, gam j x ≤ max (u x)
        (rho x + ((-Cj j : ℝ) : EReal))) → ∀ x, (⨅ j, gam j x) ≤ u x := by
      intro u hgu x
      by_contra hlt
      have hlt' : u x < ⨅ i, gam i x := not_le.mp hlt
      have hj : ∀ j, (⨅ i, gam i x) ≤ rho x + ((-Cj j : ℝ) : EReal) := by
        intro j
        have h1 : (⨅ i, gam i x) ≤ max (u x) (rho x + ((-Cj j : ℝ) : EReal)) :=
          (iInf_le (fun i => gam i x) j).trans (hgu j x)
        rcases le_max_iff.mp h1 with h | h
        · exact absurd h (not_le.mpr hlt')
        · exact h
      have hex : rho x ≠ ⊥ := by
        intro hb
        have h0 := hj 0
        rw [hb, EReal.bot_add] at h0
        have h00 : (⨅ i, gam i x) = ⊥ := le_bot_iff.mp h0
        rw [h00] at hlt'
        exact not_lt_bot hlt'
      have hbotL : (⨅ i, gam i x) = ⊥ := by
        refine eq_bot_of_forall_le_sub_nat ((rho x).toReal - C - c - 1) fun j => ?_
        refine (hj j).trans (le_of_eq ?_)
        rw [← EReal.coe_toReal (hrhotop x) hex, ← EReal.coe_add]
        congr 1
        have hCjj : Cj j = (C : ℝ) + c + 1 + j := rfl
        rw [hCjj]
        simp only [EReal.toReal_coe]
        ring
      rw [hbotL] at hlt'
      exact not_lt_bot hlt'
    have hLphi := hLle (u := phi) fun j x => (hroofj j).2.2.1 x
    have hLpsi := hLle (u := psi) fun j x => (hroofj j).2.2.2 x
    exact H (rooftop_min_of_lower theta hphi hpsi hL hLphi hLpsi).1
  -- Step 3: by compactness some `γ_j` lies below `-C`, hence `γ_j + C ≤ P_θ[φ ∨ ψ] = η`
  obtain ⟨j₀, hj₀⟩ := exists_forall_lt_of_antitone_iInf_eq_bot
    (fun j => (hgam_psh j).1.quasiPlurisubharmonic.upperSemicontinuous) hgam_anti hbot
    (K := ((-(C : ℝ) : ℝ) : EReal)) (EReal.bot_lt_coe _)
  have hgamC : ∀ x, gam j₀ x + ((C : ℝ) : EReal) ≤ eta x := by
    refine le_singularityEnvelope ((hgam_psh j₀).add_const C) (fun x => ?_)
      ⟨C, fun x _ => add_le_add (hgamrho j₀ x) le_rfl⟩
    calc gam j₀ x + ((C : ℝ) : EReal) ≤ ((-(C : ℝ) : ℝ) : EReal) + ((C : ℝ) : EReal) :=
          add_le_add (hj₀ x).le le_rfl
      _ = 0 := by rw [← EReal.coe_add]; simp
  -- Step 4: masses
  have hmassj : ∀ {u : M → EReal}, (∀ x, u x ≤ rho x) →
      ∀ (hmu : IsThetaPshPotential theta.val
        (fun x => max (u x) (rho x + ((-Cj j₀ : ℝ) : EReal)))),
      diagonalPotentialMass theta (fun x => max (u x) (rho x + ((-Cj j₀ : ℝ) : EReal))) hmu =
        diagonalPotentialMass theta rho hrho := by
    intro u hu hmu
    refine diagonalPotentialMass_eq_of_le_add omega theta hmu hrho (c₁ := Cj j₀) (c₂ := 0)
      (fun x => le_max_right _ _) (fun x => ?_)
    rw [EReal.coe_zero, add_zero]
    exact hjle hu j₀ x
  have hmgam : diagonalPotentialMass theta (gam j₀) (hgam_psh j₀) =
      diagonalPotentialMass theta rho hrho := by
    refine diagonalPotentialMass_eq_of_le_add omega theta (hgam_psh j₀) hrho
      (c₁ := Cj j₀) (c₂ := 0) (fun x => (hroofj j₀).2.1 x) (fun x => ?_)
    rw [EReal.coe_zero, add_zero]
    exact hgamrho j₀ x
  -- Step 5: the contact estimate on each side
  have hside : ∀ {u : M → EReal} (hu : IsThetaPshPotential theta.val u),
      (∀ x, u x ≤ rho x) →
      ∀ (hmu : IsThetaPshPotential theta.val
        (fun x => max (u x) (rho x + ((-Cj j₀ : ℝ) : EReal)))),
      diagonalPotentialMeasure theta (fun x => max (u x) (rho x + ((-Cj j₀ : ℝ) : EReal))) hmu
          {x | gam j₀ x = max (u x) (rho x + ((-Cj j₀ : ℝ) : EReal))} +
        diagonalPotentialMeasure theta u hu {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < u x} ≤
      diagonalPotentialMass theta rho hrho := by
    intro u hu hur hmu
    have hSm : MeasurableSet {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < u x} :=
      measurableSet_lt (hsh heta C).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
        hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
    have hloc := MaxMassDecomposition.diagonalPotentialMeasure_restrict_max_eq theta hu
      (hsh hrho (Cj j₀)) hmu
    have hSsub : {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < u x} ⊆
        {x | rho x + ((-Cj j₀ : ℝ) : EReal) < u x} := by
      intro x hx
      have hx' : eta x + ((-(C : ℝ) : ℝ) : EReal) < u x := hx
      refine lt_of_le_of_lt ?_ hx'
      calc rho x + ((-Cj j₀ : ℝ) : EReal)
          ≤ eta x + (c : EReal) + ((-Cj j₀ : ℝ) : EReal) := add_le_add (hrhoeta x) le_rfl
        _ = eta x + ((c - Cj j₀ : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add, sub_eq_add_neg]
        _ ≤ eta x + ((-(C : ℝ) : ℝ) : EReal) :=
            add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith [hCjC j₀]))
    have hSeq : diagonalPotentialMeasure theta (fun x => max (u x)
        (rho x + ((-Cj j₀ : ℝ) : EReal))) hmu {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < u x} =
        diagonalPotentialMeasure theta u hu {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < u x} := by
      have h' := congrArg (fun μ : Measure M => μ {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < u x})
        hloc
      simp only [Measure.restrict_apply hSm, inter_eq_left.mpr hSsub] at h'
      exact h'
    rw [← hSeq]
    have hdisj : Disjoint {x | gam j₀ x = max (u x) (rho x + ((-Cj j₀ : ℝ) : EReal))}
        {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < u x} := by
      rw [Set.disjoint_left]
      intro x hA hS
      simp only [mem_ofPred_eq] at hA hS
      have hlt : eta x + ((-(C : ℝ) : ℝ) : EReal) < gam j₀ x :=
        lt_of_lt_of_le hS (hA ▸ le_max_left _ _)
      exact not_lt_of_add_le (hetatop x) C hlt (hgamC x)
    rw [← measure_union hdisj hSm, ← hmassj hur hmu]
    exact measure_mono (subset_univ _)
  have hAφ := hside hphi (fun x => le_max_left _ _) (hphij_psh j₀)
  have hAψ := hside hpsi (fun x => le_max_right _ _) (hpsij_psh j₀)
  have hcontact := rooftopMeasure_le_contact omega theta (hphij_psh j₀) (hpsij_psh j₀)
    (hgam_psh j₀) (hroofj j₀).2.2.1 (hroofj j₀).2.2.2 MeasurableSet.univ
  simp only [univ_inter] at hcontact
  -- Step 6: the contradiction, in real numbers
  set m := diagonalPotentialMass theta rho hrho with hm
  set a := diagonalPotentialMeasure theta phi hphi {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < phi x}
    with ha
  set b := diagonalPotentialMeasure theta psi hpsi {x | eta x + ((-(C : ℝ) : ℝ) : EReal) < psi x}
    with hb
  set A := diagonalPotentialMeasure theta (phij j₀) (hphij_psh j₀)
    {x | gam j₀ x = phij j₀ x} with hA
  set B := diagonalPotentialMeasure theta (psij j₀) (hpsij_psh j₀)
    {x | gam j₀ x = psij j₀ x} with hB
  have hmtop : m ≠ ⊤ := by
    have := hfinite hrho
    exact measure_ne_top _ _
  have hAm : A + a ≤ m := hAφ
  have hBm : B + b ≤ m := hAψ
  have hgamm : m ≤ A + B := by
    rw [← hmgam]
    exact hcontact
  have hCm : m < a + b := lt_of_eq_of_lt hmeta.symm hC
  have hAt : A ≠ ⊤ := ne_top_of_le_ne_top hmtop (le_trans le_self_add hAm)
  have hBt : B ≠ ⊤ := ne_top_of_le_ne_top hmtop (le_trans le_self_add hBm)
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hmtop (le_trans le_add_self hAm)
  have hbt : b ≠ ⊤ := ne_top_of_le_ne_top hmtop (le_trans le_add_self hBm)
  have r1 := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hAt, hat⟩) hmtop).mpr hAm
  have r2 := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hBt, hbt⟩) hmtop).mpr hBm
  have r3 := (ENNReal.toReal_le_toReal hmtop (ENNReal.add_ne_top.mpr ⟨hAt, hBt⟩)).mpr hgamm
  have r4 := (ENNReal.toReal_lt_toReal hmtop (ENNReal.add_ne_top.mpr ⟨hat, hbt⟩)).mpr hCm
  rw [ENNReal.toReal_add hAt hat] at r1
  rw [ENNReal.toReal_add hBt hbt] at r2
  rw [ENNReal.toReal_add hAt hBt] at r3
  rw [ENNReal.toReal_add hat hbt] at r4
  linarith

end

end SGPT.Foundations.Analysis.Pending.RooftopPshCriterion
