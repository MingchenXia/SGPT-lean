import SGPT.Foundations.PublishedEnvelope.Source.PSH
import SGPT.Foundations.PublishedEnvelope.Global.Homogeneous

/-! # Rational weights in the native BJ Fubini–Study nets

The same native line, sections, denominator and numerical class are retained.
This is an auxiliary comparison of the two actual EP notions of weighted data;
it does not identify the SGPT point space or assert a book coverage entry.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Filter Set Topology Scheme.Modules
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.Berkovich
open SGPT.Foundations.PublishedEnvelope.NativeNumericalFubiniStudy
open SGPT.Foundations.PublishedEnvelope.SchemeGlobalSectionModelNormIsometries
open scoped Classical NNReal ENNReal Topology

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of k)) [IsProjective p]

private local instance projectiveProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Reweight the actual original global sections, without changing the line or denominator. -/
def nativeFSReweight (D : FSData X) (ρ : ℝ → ℝ) : FSData X where
  line := D.line
  invertible := D.invertible
  m := D.m
  m_pos := D.m_pos
  terms := D.terms.image fun t => (t.1, ρ t.2)

/-- Reweighting changes neither the actual line nor its numerical class. -/
theorem nativeFSReweight_class (D : FSData X) (ρ : ℝ → ℝ) :
    (nativeFSReweight D ρ).numericalClass p = D.numericalClass p := rfl

/-- A nonzero original section survives the reweighting image. -/
theorem nativeFSReweight_nonzero (D : FSData X) (ρ : ℝ → ℝ) (hD : D.Nonzero) :
    (nativeFSReweight D ρ).Nonzero := by
  obtain ⟨t, ht, ht0⟩ := hD
  exact ⟨(t.1, ρ t.2), Finset.mem_image_of_mem _ ht, ht0⟩

/-- Rational replacements give actual rational weights. -/
theorem nativeFSReweight_rational (D : FSData X) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ D.terms, ∃ q : ℚ, ρ t.2 = q) :
    (nativeFSReweight D ρ).IsRational := by
  intro t ht
  obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht
  exact hρ t₀ h₀

/-- Exact evaluation of the reweighted data at the same native point. -/
theorem nativeFSReweight_eval (D : FSData X) (ρ : ℝ → ℝ) (y : Variety.An p) :
    (nativeFSReweight D ρ).eval p y =
      (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup (fun t =>
        ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible t.1 : ℝ≥0∞)
          + (ρ t.2 : EReal)) := by
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) *
    (D.terms.image (fun t => (t.1, ρ t.2))).sup _ = _
  rw [Finset.sup_image]
  rfl

/-- Enlarging weights enlarges the whole FS function, including common zeros. -/
theorem nativeFSReweight_mono (D : FSData X) {ρ ρ' : ℝ → ℝ}
    (hρ : ∀ t ∈ D.terms, ρ t.2 ≤ ρ' t.2) (y : Variety.An p) :
    (nativeFSReweight D ρ).eval p y ≤ (nativeFSReweight D ρ').eval p y := by
  rw [nativeFSReweight_eval, nativeFSReweight_eval]
  have hinv : 0 ≤ (D.m : ℝ)⁻¹ := le_of_lt (inv_pos.mpr (by exact_mod_cast D.m_pos))
  refine ProjBerk.ereal_coe_mul_monotone hinv (Finset.sup_mono_fun fun t ht => ?_)
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (hρ t ht))

/-- Adding `m c` to every weight adds exactly `c` to the whole function. -/
theorem nativeFSReweight_add (D : FSData X) (c : ℝ) (y : Variety.An p) :
    (nativeFSReweight D (fun x => x + D.m * c)).eval p y = D.eval p y + (c : EReal) := by
  have hinv : 0 ≤ (D.m : ℝ)⁻¹ := le_of_lt (inv_pos.mpr (by exact_mod_cast D.m_pos))
  have hm : (D.m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt D.m_pos
  let z : Γ(D.line, ⊤) × ℝ → EReal := fun t =>
    ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible t.1 : ℝ≥0∞) +
      (t.2 : EReal)
  have hsup : (D.terms.sup fun t =>
      ENNReal.log (globalSectionNorm _root_.Valuation.one_apply_le_one y D.line D.invertible t.1 : ℝ≥0∞) +
        ((t.2 + D.m * c : ℝ) : EReal)) =
      D.terms.sup z + ((D.m * c : ℝ) : EReal) := by
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (s := D.terms)
      (fun x : EReal => x + ((D.m * c : ℝ) : EReal)) (fun _ _ h => add_le_add_left h _)
      (EReal.bot_add _)]
    refine Finset.sup_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, z, EReal.coe_add, add_assoc]
  rw [nativeFSReweight_eval, hsup]
  change (((D.m : ℝ)⁻¹ : ℝ) : EReal) * (D.terms.sup z + ((D.m * c : ℝ) : EReal)) =
    (((D.m : ℝ)⁻¹ : ℝ) : EReal) * D.terms.sup z + (c : EReal)
  rw [ProjBerk.ereal_coe_mul_add hinv, ← EReal.coe_mul, ← mul_assoc,
    inv_mul_cancel₀ hm, one_mul]

/-- The shifted native datum supplies the lower approximation bound. -/
theorem nativeFSReweight_lower (D : FSData X) {ρ : ℝ → ℝ} {c : ℝ}
    (hρ : ∀ t ∈ D.terms, t.2 + D.m * c ≤ ρ t.2) (y : Variety.An p) :
    D.eval p y + (c : EReal) ≤ (nativeFSReweight D ρ).eval p y := by
  rw [← nativeFSReweight_add]
  exact nativeFSReweight_mono p D hρ y

/-- The shifted native datum supplies the upper approximation bound. -/
theorem nativeFSReweight_upper (D : FSData X) {ρ : ℝ → ℝ} {c : ℝ}
    (hρ : ∀ t ∈ D.terms, ρ t.2 ≤ t.2 + D.m * c) (y : Variety.An p) :
    (nativeFSReweight D ρ).eval p y ≤ D.eval p y + (c : EReal) := by
  rw [← nativeFSReweight_add]
  exact nativeFSReweight_mono p D hρ y

/-- Every actual native psh net can be replaced by a decreasing rational-weight
net with identical pointwise infimum and the same convergent numerical classes. -/
theorem varietyPSH_exists_rationalFS_net [IsIntegral X]
    {θ : NativeRealNumericalClasses.Space p} {φ : Variety.An p → EReal}
    (hφ : Variety.IsPSH p θ φ) :
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (D : J → FSData X), (∀ j, (D j).IsRational ∧ (D j).Nonzero) ∧
      Variety.AmpleTendsto p (fun j => (D j).numericalClass p) atTop θ ∧
      (∀ y, Antitone fun j => (D j).eval p y) ∧ ∀ y, φ y = ⨅ j, (D j).eval p y := by
  obtain ⟨_, _, I, _, _, _, D, hD, hconv, hanti, hφ⟩ := hφ
  have hδ : ∀ N : ℕ, (1 : ℝ) / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) := fun N =>
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  choose q hq using fun (i : I) (N : ℕ) (x : ℝ) => exists_rat_btwn
    (show x + (D i).m * (1 / ((N : ℝ) + 2)) < x + (D i).m * (1 / ((N : ℝ) + 1)) by
      have hm : (0 : ℝ) < (D i).m := by exact_mod_cast (D i).m_pos
      have := mul_lt_mul_of_pos_left (hδ N) hm
      linarith)
  let E : RatRoundIndex I → FSData X := fun r =>
    nativeFSReweight (D (r : I × ℕ).1)
      (fun x => (q (r : I × ℕ).1 (r : I × ℕ).2 x : ℝ))
  have hlow (i : I) (N : ℕ) (y : Variety.An p) :
      (D i).eval p y + ((1 / ((N : ℝ) + 2) : ℝ) : EReal) ≤
        (nativeFSReweight (D i) (fun x => (q i N x : ℝ))).eval p y :=
    nativeFSReweight_lower p (D i) (fun t _ => (hq i N t.2).1.le) y
  have hup (i : I) (N : ℕ) (y : Variety.An p) :
      (nativeFSReweight (D i) (fun x => (q i N x : ℝ))).eval p y ≤
        (D i).eval p y + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) :=
    nativeFSReweight_upper p (D i) (fun t _ => (hq i N t.2).2.le) y
  refine ⟨RatRoundIndex I, inferInstance, inferInstance, inferInstance, E, ?_, ?_, ?_, ?_⟩
  · intro r
    refine ⟨nativeFSReweight_rational _ _ (fun t _ => ⟨q _ _ t.2, rfl⟩),
      nativeFSReweight_nonzero _ _ (hD _)⟩
  · change Variety.AmpleTendsto p ((fun i => (D i).numericalClass p) ∘
      (fun r : RatRoundIndex I => (r : I × ℕ).1)) atTop θ
    exact hconv.comp RatRoundIndex.tendsto_fst
  · intro y r r' hrr'
    rcases hrr' with rfl | ⟨h₁, h₂⟩
    · exact le_rfl
    · refine (hup _ _ y).trans (le_trans ?_ (hlow _ _ y))
      refine add_le_add (hanti y h₁) (EReal.coe_le_coe_iff.mpr ?_)
      have hn : ((r : I × ℕ).2 : ℝ) + 1 ≤ ((r' : I × ℕ).2 : ℝ) := by exact_mod_cast h₂
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · intro y
    refine le_antisymm (le_iInf fun r => ?_) (ProjBerk.ereal_le_of_forall_pos_le_add fun ε hε => ?_)
    · rw [hφ y]
      have hnn : (0 : ℝ) ≤ 1 / (((r : I × ℕ).2 : ℝ) + 2) :=
        one_div_nonneg.mpr (by linarith [Nat.cast_nonneg (α := ℝ) (r : I × ℕ).2])
      exact (iInf_le _ _).trans ((ereal_le_add_coe hnn _).trans (hlow _ _ y))
    · obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      calc
        (⨅ r : RatRoundIndex I, (E r).eval p y) ≤
            ⨅ i : I, (nativeFSReweight (D i) (fun x => (q i N x : ℝ))).eval p y :=
          le_iInf fun i => iInf_le (fun r : RatRoundIndex I => (E r).eval p y)
            (show I × ℕ from (i, N))
        _ ≤ ⨅ i, ((D i).eval p y + ((1 / ((N : ℝ) + 1) : ℝ) : EReal)) :=
          iInf_mono fun i => hup i N y
        _ = φ y + ((1 / ((N : ℝ) + 1) : ℝ) : EReal) := by rw [← ereal_iInf_add_coe, hφ y]
        _ ≤ φ y + (ε : EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hN.le)

/-- Native rational-weight definition with the source's nontriviality and
decreasing-net conditions; upper semicontinuity is not assumed. -/
def nativeRationalPSH [IsIntegral X]
    (θ : NativeRealNumericalClasses.Space p) (φ : Variety.An p → EReal) : Prop :=
  (∃ y, φ y ≠ ⊥) ∧
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (D : J → FSData X), (∀ j, (D j).IsRational ∧ (D j).Nonzero) ∧
      Variety.AmpleTendsto p (fun j => (D j).numericalClass p) atTop θ ∧
      (∀ y, Antitone fun j => (D j).eval p y) ∧ ∀ y, φ y = ⨅ j, (D j).eval p y

/-- On the actual native point space, rational weights give exactly the
existing real-weight psh definition. This does not yet identify SGPT points. -/
theorem nativeRationalPSH_iff [IsIntegral X]
    (θ : NativeRealNumericalClasses.Space p) (φ : Variety.An p → EReal) :
    nativeRationalPSH p θ φ ↔ Variety.IsPSH p θ φ := by
  constructor
  · rintro ⟨hfin, J, _, _, _, D, hD, hconv, hanti, hlim⟩
    refine ⟨hfin, ?_, J, inferInstance, inferInstance, inferInstance, D,
      (fun j => (hD j).2), hconv, hanti, hlim⟩
    have heq : φ = fun y => ⨅ j, (D j).eval p y := funext hlim
    rw [heq]
    exact upperSemicontinuous_iInf fun j => ((D j).continuous_eval p).upperSemicontinuous
  · intro h
    exact ⟨h.exists_ne_bot, varietyPSH_exists_rationalFS_net p h⟩

end SGPT.NAPotential.BJ
