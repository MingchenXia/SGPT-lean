import SGPT.Okounkov.TranscendentalBody2Lelong
import SGPT.Okounkov.TranscendentalCoreValuationAnalytic
import SGPT.Okounkov.TranscendentalBodyConvex
import SGPT.Okounkov.TranscendentalBodyBasic

/-!
# The Okounkov body of a big class has nonempty interior

Source: DRWNXZ (Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies*),
Proposition 3.4; blueprint node `tok:body-interior` (sub-lemmas `tok-body2:triangular`,
`tok-body2:simplex`, `tok-body2:kahler` of `claude-tok-body2.tex`).

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag
`Y₀ = X ⊇ Y₁ ⊇ ⋯ ⊇ Yₙ`.

* `flagValuation_triangular`: let `φ ∈ 𝒜(θ)` be continuous (as an extended-real function), finite
  off `Y_{k+1}` and with Lelong numbers `≥ δ > 0` at every point of `Y_{k+1}`. Then the
  coordinates `0, …, k - 1` of `ν(φ)` vanish and the coordinate `k` is positive. Proof by induction
  on the dimension: if `k > 0`, the generic Lelong number along `Y₁` vanishes (`φ` is finite at a
  point of `Y₁ \ Y_{k+1}`), so `ν(φ) = (0, ν(φ|_{Y₁}))`
  (`TranscendentalCore.flagValuation_of_analytic`,
  the residual with coefficient `0` of a continuous potential being the potential), and the
  restriction satisfies the same hypotheses on `Y₁` (Lelong numbers do not decrease under
  restriction); if `k = 0`, the first coordinate is the generic Lelong number along `Y₁`, at least
  `δ / 2` in the squared-logarithmic normalization.
* `interior_nonempty_of_triangular`: a convex set of `ℝⁿ` containing `0` and `n` vectors in
  triangular position (`v_k j = 0` for `j < k`, `v_k k ≠ 0`) has nonempty interior.
* `interior_tradOkounkovBody_kahler_nonempty`: for every Kähler form `κ`, `Δ(κ)` has nonempty
  interior: `ν(ε ψ_{k+1}) ∈ Δ(κ)` for the poles `ψ_{k+1}` of `Y_{k+1}` and small rational `ε`, and
  these vectors are triangular.
* `TranscendentalBody.interior_tradOkounkovBody_nonempty` (**`tok:body-interior`**): for every big
  class `ξ = {θ}`, `Δ(ξ)` has nonempty interior: for a Kähler current `θ + ddᶜ ψ ≥ κ` in `Ω(ξ)`,
  `ν(ψ) + Δ(κ/2) ⊆ Δ(θ - κ/2) + Δ(κ/2) ⊆ Δ(θ)`; `interior_classOkounkovBody_nonempty` is the same
  for the body `classOkounkovBody F α` of a big class `α`.

The last three results are in the namespace `SGPT.Okounkov.TranscendentalBody` of the package BODY
(names planned there); the auxiliary lemmas are in `SGPT.Okounkov.TranscendentalBody2`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalBody2

open Set Filter
open scoped Topology Manifold ENNReal NNReal Pointwise ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Okounkov.TranscendentalCore

section Flag

variable {m : ℕ}

/-- For `k ≥ 1`, the flag member `Y_{k+1}` is strictly smaller than `Y₁`: there is a point of
`Y₁ \ Y_{k+1}` (the dimensions `m` and `m - k` differ). -/
theorem exists_mem_first_not_mem (F : OriginalFlagGeometry.{u} (m + 1)) (k : Fin (m + 1))
    (hk : k ≠ 0) : ∃ y ∈ F.flag (1 : Fin (m + 2)), y ∉ F.flag k.succ := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := F.firstDivisor.2.1.nonempty
  have hle : (1 : Fin (m + 2)) ≤ k.succ := by
    rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_one]
    omega
  have hsub : F.flag k.succ ⊆ F.flag (1 : Fin (m + 2)) := F.smooth.2.1 hle
  have heq : F.flag k.succ = F.flag (1 : Fin (m + 2)) := Subset.antisymm hsub h
  have h1 := F.firstDivisor.2.2 x hx
  have h2 := (F.smooth.2.2 k.succ).2.2 x (h x hx)
  rw [heq] at h2
  have := RegularPointDimension.eq_of_regularAtDim h1 h2
  have hk0 : (k : ℕ) ≠ 0 := fun h0 => hk (Fin.ext h0)
  rw [Fin.val_succ] at this
  omega

end Flag

section Valuation

variable {m : ℕ}

/-- If `φ` has Lelong numbers `≥ δ > 0` at every point of `Y₁`, the first coordinate of `ν(φ)`
(the generic Lelong number along `Y₁`, squared-logarithmic normalization) is positive. -/
theorem flagValuation_first_pos (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (h : ∀ x ∈ F.flag (1 : Fin (m + 2)), δ ≤ lelongNumber (n := m + 1) φ x) :
    0 < flagValuation F φ 0 := by
  rw [flagValuation_eq hφ]
  have h0 := potentialFlagValuation_first F hφ
  have hge : δ / 2 ≤ sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ :=
    le_iInf fun y => half_le_squaredLogLelongNumber (Nat.succ_ne_zero m) (h y.1 y.2)
  have hpos : (0 : ℝ≥0∞) < (potentialFlagValuation F hφ 0 : ℝ≥0∞) := by
    rw [h0]
    exact lt_of_lt_of_le (ENNReal.half_pos hδ.ne') hge
  show (0 : ℝ) < ((potentialFlagValuation F hφ 0 : ℝ≥0) : ℝ)
  exact NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hpos)

/-- If `φ` is finite at a point of `Y₁`, the first coordinate of `ν(φ)` vanishes. -/
theorem flagValuation_first_eq_zero (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {y : F.carrier} (hy : y ∈ F.flag (1 : Fin (m + 2)))
    (hφy : φ y ≠ ⊥) : flagValuation F φ 0 = 0 := by
  rw [flagValuation_eq hφ]
  have h0 := potentialFlagValuation_first F hφ
  have hsg : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ = 0 :=
    le_antisymm ((iInf_le (fun y : F.flag (1 : Fin (m + 2)) =>
      squaredLogLelongNumber (n := m + 1) φ y.val) ⟨y, hy⟩).trans
        (squaredLogLelongNumber_eq_zero_of_ne_bot (Nat.succ_pos m) hφ.1 hφy).le) bot_le
  rw [hsg] at h0
  have h0' : potentialFlagValuation F hφ 0 = 0 := by exact_mod_cast h0
  show ((potentialFlagValuation F hφ 0 : ℝ≥0) : ℝ) = 0
  rw [h0', NNReal.coe_zero]

/-- **Successive restriction for a continuous potential with vanishing first coordinate**: if
`φ ∈ 𝒜(θ)` is continuous and `ν(φ)₀ = 0`, the restriction `φ|_{Y₁}` lies in `𝒜(Y₁, β)` for some
closed `(1,1)`-form `β` of `Y₁`, and the remaining coordinates of `ν(φ)` are
`ν_{Y₁ ⊇ ⋯}(φ|_{Y₁})`. -/
theorem flagValuation_succ_eq_tail_of_continuous (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : φ ∈ analyticCurrents θ) (hc : Continuous φ) (h0 : flagValuation F φ 0 = 0) :
    ∃ β : ClosedRealOneOneForm m F.tail.carrier,
      (fun y : F.tail.carrier => φ y.val) ∈ analyticCurrents β ∧
        (fun i => flagValuation F φ i.succ) =
          flagValuation F.tail (fun y : F.tail.carrier => φ y.val) := by
  obtain ⟨D, hDI, E, hEW, hmetric, -, -⟩ :=
    SGPT.Okounkov.exists_normalized_smooth_divisor_residual_generic_zero hφ.1 F.firstDivisor
  obtain ⟨-, hc0, hw, htail⟩ := flagValuation_of_analytic F hφ D hDI E hEW hmetric
  have hcz : (sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toNNReal = 0 := by
    rw [h0] at hc0
    exact_mod_cast hc0.symm
  rw [hcz, NNReal.coe_zero] at hw htail
  have hint : interior (F.flag (1 : Fin (m + 2))) = ∅ :=
    SGPT.Okounkov.TranscendentalPole.interior_eq_empty_of_lt F.firstDivisor (Nat.lt_succ_self m)
  have hfun : (fun y : F.tail.carrier => extensionAcross (F.flag (1 : Fin (m + 2)))
      (SGPT.Okounkov.smoothDivisorOffResidual E 0 φ) y.val) =
      fun y : F.tail.carrier => φ y.val := by
    funext y
    exact extensionAcross_smoothDivisorOffResidual_zero E hEW hint hc.continuousAt
  rw [hfun] at hw htail
  exact ⟨_, hw, htail⟩

/-- **Triangular valuations** (blueprint `tok-body2:triangular`): let `φ ∈ 𝒜(θ)` be continuous,
finite off `Y_{k+1}`, with Lelong numbers `≥ δ > 0` at every point of `Y_{k+1}`. Then
`ν(φ)_j = 0` for `j < k` and `ν(φ)_k > 0`. -/
theorem flagValuation_triangular : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1))
    (k : Fin (m + 1)) (θ : ClosedRealOneOneForm (m + 1) F.carrier) (φ : F.carrier → EReal),
    φ ∈ analyticCurrents θ → Continuous φ → (∀ x, φ x = ⊥ → x ∈ F.flag k.succ) →
    ∀ δ : ℝ≥0∞, 0 < δ → (∀ x ∈ F.flag k.succ, δ ≤ lelongNumber (n := m + 1) φ x) →
    (∀ j : Fin (m + 1), j < k → flagValuation F φ j = 0) ∧ 0 < flagValuation F φ k := by
  intro m
  induction m with
  | zero =>
      intro F k θ φ hφ _ _ δ hδ hlel
      have hk : k = 0 := Fin.ext (by have := k.isLt; simp only [Fin.val_zero]; omega)
      subst hk
      exact ⟨fun j hj => absurd hj (Fin.not_lt_zero j), flagValuation_first_pos F hφ.1 hδ hlel⟩
  | succ m ih =>
      intro F k θ φ hφ hc hbot δ hδ hlel
      induction k using Fin.cases with
      | zero =>
          exact ⟨fun j hj => absurd hj (Fin.not_lt_zero j),
            flagValuation_first_pos F hφ.1 hδ hlel⟩
      | succ k =>
          obtain ⟨y, hy1, hyk⟩ := exists_mem_first_not_mem F k.succ (Fin.succ_ne_zero k)
          have h0 : flagValuation F φ 0 = 0 :=
            flagValuation_first_eq_zero F hφ.1 hy1 (fun h => hyk (hbot y h))
          obtain ⟨β, hw, htail⟩ := flagValuation_succ_eq_tail_of_continuous F hφ hc h0
          have hcw : Continuous (fun y : F.tail.carrier => φ y.val) :=
            hc.comp continuous_subtype_val
          have hbotw : ∀ y : F.tail.carrier, φ y.val = ⊥ → y ∈ F.tail.flag k.succ :=
            fun y h => hbot _ h
          have hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
              (fun y : F.tail.carrier => (y.val : F.carrier)) :=
            SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ (m + 1)) F.firstDivisor.2.2
          have hlelw : ∀ y ∈ F.tail.flag k.succ,
              δ ≤ lelongNumber (n := m + 1) (fun y : F.tail.carrier => φ y.val) y := by
            intro y hy
            refine (hlel y.val hy).trans ?_
            exact lelongNumber_le_comp ((hι y).mdifferentiableAt (by simp))
              (fun h => eq_bot_of_lelongNumber_pos (Nat.succ_pos _) hφ.1.1 h)
          obtain ⟨hz, hpos⟩ := ih F.tail k β _ hw hcw hbotw δ hδ hlelw
          refine ⟨fun j hj => ?_, ?_⟩
          · induction j using Fin.cases with
            | zero => exact h0
            | succ j =>
                have hj' : j < k := Fin.succ_lt_succ_iff.mp hj
                rw [show flagValuation F φ j.succ = flagValuation F.tail _ j from
                  congrFun htail j]
                exact hz j hj'
          · rw [show flagValuation F φ k.succ = flagValuation F.tail _ k from congrFun htail k]
            exact hpos

end Valuation

section Simplex

/-- **A convex set containing `0` and `n` triangular vectors has nonempty interior** (blueprint
`tok-body2:simplex`): the vectors `v_k` with `v_k j = 0` for `j < k` and `v_k k ≠ 0` form an
upper triangular matrix with nonzero determinant, so they span `ℝⁿ`, and the affine span of the
set is everything. -/
theorem interior_nonempty_of_triangular {n : ℕ} {s : Set (Fin n → ℝ)} (hs : Convex ℝ s)
    (h0 : (0 : Fin n → ℝ) ∈ s) (v : Fin n → Fin n → ℝ) (hv : ∀ k, v k ∈ s)
    (htri : ∀ k j, j < k → v k j = 0) (hdiag : ∀ k, v k k ≠ 0) : (interior s).Nonempty := by
  rw [hs.interior_nonempty_iff_affineSpan_eq_top]
  have hM : (Matrix.of v).IsUpperTriangular := fun i j hij => htri i j hij
  have hdet : (Matrix.of v).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hM]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  have hli : LinearIndependent ℝ v := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hspan : Submodule.span ℝ (range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hdir : (affineSpan ℝ s).direction = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ (hv k)) (mem_affineSpan ℝ h0)
    simpa using this
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, mem_affineSpan ℝ h0⟩).mp hdir

end Simplex

end SGPT.Okounkov.TranscendentalBody2

namespace SGPT.Okounkov.TranscendentalBody

open Set Filter
open scoped Topology Manifold ENNReal NNReal Pointwise ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalBody2

section Body

variable {m : ℕ}

/-- **The body of a Kähler class has nonempty interior** (blueprint `tok-body2:kahler`): for every
Kähler form `κ` and every `k`, `ν(ε ψ_{k+1}) ∈ Δ(κ)` for the pole `ψ_{k+1}` of `Y_{k+1}` and a small
rational `ε > 0`; these `n` vectors are triangular and `0 ∈ Δ(κ)`. -/
theorem interior_tradOkounkovBody_kahler_nonempty (F : OriginalFlagGeometry.{u} (m + 1))
    (κ : KahlerBackground (m + 1) F.carrier) :
    (interior (tradOkounkovBody F κ.form)).Nonempty := by
  have hvec : ∀ k : Fin (m + 1), ∃ v : Fin (m + 1) → ℝ, v ∈ tradOkounkovBody F κ.form ∧
      (∀ j, j < k → v j = 0) ∧ 0 < v k := by
    intro k
    have hY := F.smooth.2.2 k.succ
    have hdim : (m + 1) - (k.succ : ℕ) < m + 1 := by
      rw [Fin.val_succ]
      omega
    obtain ⟨P, hP⟩ :=
      TranscendentalPole.exists_submanifold_pole_of_isClosedConnectedSubmanifold κ hY hdim
    obtain ⟨ε₀, hε₀, hmem⟩ := hP.exists_mem_gentleKahlerCurrents
    obtain ⟨ε, hε, hεle⟩ : ∃ ε : ℚ, 0 < ε ∧ (ε : ℝ) ≤ ε₀ := by
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn hε₀
      exact ⟨q, by exact_mod_cast h1, h2.le⟩
    have hφ := hmem ε hε hεle
    have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
    have hA : (fun x => ((ε : ℝ) : EReal) * P x) ∈ analyticCurrents κ.form :=
      globalAnalyticCurrents_subset_analyticCurrents _
        (gentleKahlerCurrents_subset_globalAnalyticCurrents hφ)
    have hε0 : ((ε : ℝ) : EReal) ≠ 0 := EReal.coe_ne_zero.mpr hεR.ne'
    have hcont : Continuous (fun x => ((ε : ℝ) : EReal) * P x) := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      have hmul := EReal.continuousAt_mul (p := (((ε : ℝ) : EReal), P x)) (Or.inl hε0)
        (Or.inl hε0) (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
      have hg : ContinuousAt (fun y => (((ε : ℝ) : EReal), P y)) x :=
        continuousAt_const.prodMk hP.continuous.continuousAt
      exact ContinuousAt.comp (f := fun y => (((ε : ℝ) : EReal), P y)) (x := x) hmul hg
    have hbot : ∀ x, ((ε : ℝ) : EReal) * P x = ⊥ → x ∈ F.flag k.succ := by
      intro x hx
      rw [EReal.mul_eq_bot] at hx
      rcases hx with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
      · exact absurd h1 (EReal.coe_ne_bot _)
      · exact (hP.eq_bot_iff x).mp h2
      · exact absurd h3 (EReal.coe_ne_top _)
      · exact absurd (EReal.coe_lt_coe_iff.mp (h4.trans_eq EReal.coe_zero.symm)) hεR.not_gt
    have hlel := lelongNumber_smul_ge_of_isSubmanifoldPole hP
      (fun x hx => ⟨_, hY.2.2 x hx⟩) hεR
    have hδ : (0 : ℝ≥0∞) < ((Real.toNNReal (2 * (ε : ℝ)) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_pos, Real.toNNReal_pos]
      positivity
    obtain ⟨hz, hpos⟩ := flagValuation_triangular m F k κ.form _ hA hcont hbot _ hδ hlel
    exact ⟨_, image_gentleKahlerCurrents_subset_tradOkounkovBody _ ⟨_, hφ, rfl⟩, hz, hpos⟩
  choose v hv hz hpos using hvec
  have h0 : (0 : Fin (m + 1) → ℝ) ∈ tradOkounkovBody F κ.form := by
    refine zero_mem_tradOkounkovBody
      (κ := KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) κ) ?_
    have heq : κ.form - (KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) κ).form =
        (1 / 2 : ℝ) • κ.form := by
      rw [KahlerBackground.smul_form]
      module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  exact interior_nonempty_of_triangular (convex_tradOkounkovBody _) h0 v hv
    (fun k j hj => hz k j hj) (fun k => (hpos k).ne')

/-- **`tok:body-interior`** (DRWNXZ Proposition 3.4): the Okounkov body `Δ(ξ)` of a big class
`ξ = {θ}` has nonempty interior. For a Kähler current `θ + ddᶜ ψ ≥ κ` with gentle analytic
singularities (`ψ ∈ Ω(ξ)`), `ψ ∈ Ω(θ - κ/2)`, so
`ν(ψ) + Δ(κ/2) ⊆ Δ(θ - κ/2) + Δ(κ/2) ⊆ Δ(θ)`, and `Δ(κ/2)` has nonempty interior. -/
theorem interior_tradOkounkovBody_nonempty {F : OriginalFlagGeometry.{u} (m + 1)}
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    (interior (tradOkounkovBody F θ)).Nonempty := by
  obtain ⟨ψ, ⟨hψ, hgentle⟩, κ, hκ⟩ := exists_mem_gentleKahlerCurrents_of_isBig hbig
  set κ' : KahlerBackground (m + 1) F.carrier :=
    KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) κ with hκ'
  have hform : (θ - κ'.form) - κ'.form = θ - κ.form := by
    rw [hκ', KahlerBackground.smul_form]
    module
  have hψ' : IsThetaPshPotential (θ - κ'.form).val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hκ κ'.isSemipositive
    have heq : θ - κ.form + κ'.form = θ - κ'.form := by
      rw [hκ', KahlerBackground.smul_form]
      module
    rwa [heq] at h
  have hmem : ψ ∈ gentleKahlerCurrents (θ - κ'.form) :=
    ⟨⟨hψ', hgentle⟩, κ', by rw [hform]; exact hκ⟩
  have hp : flagValuation F ψ ∈ tradOkounkovBody F (θ - κ'.form) :=
    image_gentleKahlerCurrents_subset_tradOkounkovBody _ ⟨ψ, hmem, rfl⟩
  obtain ⟨q, hq⟩ := interior_tradOkounkovBody_kahler_nonempty F κ'
  have hsub : flagValuation F ψ +ᵥ tradOkounkovBody F κ'.form ⊆ tradOkounkovBody F θ := by
    rintro _ ⟨y, hy, rfl⟩
    have h := tradOkounkovBody_add_subset (θ - κ'.form) κ'.form
      (Set.add_mem_add hp hy)
    rwa [sub_add_cancel] at h
  refine ⟨flagValuation F ψ +ᵥ q, interior_mono hsub ?_⟩
  rw [interior_vadd]
  exact Set.vadd_mem_vadd_set hq

/-- **`tok:body-interior` for classes**: the Okounkov body `Δ(α) = classOkounkovBody F α` of every
big class `α` has nonempty interior. -/
theorem interior_classOkounkovBody_nonempty {F : OriginalFlagGeometry.{u} (m + 1)}
    {α : RealBottChern (m + 1) F.carrier} (hα : SGPT.PSH.BookCurrent.IsBig α) :
    (interior (TranscendentalMain.classOkounkovBody F α)).Nonempty := by
  have hrep : RealBottChern.ofRepresentative (Quotient.out α) = α := Quotient.out_eq α
  rw [← hrep] at hα
  exact interior_tradOkounkovBody_nonempty hα

end Body

end SGPT.Okounkov.TranscendentalBody
