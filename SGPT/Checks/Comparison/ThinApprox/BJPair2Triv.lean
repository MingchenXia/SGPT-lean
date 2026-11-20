import SGPT.Checks.Comparison.ThinApprox.BJPair2TrivCentral
import SGPT.Checks.Comparison.ThinApprox.TrivialIdeal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge SGPT.NAPotential.BJ.NativePicard
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open FlagIdealBound

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

section triv

/-- **`φ_𝔞(v_triv) = λ₀`** for the largest weight `λ₀` with `𝔞_{λ₀} ≠ 0`. -/
theorem phi_trivial_eq (𝔞 : FlagIdeal X) {l₀ : ℤ} (hl₀ : 𝔞.ideal l₀ ≠ ⊥)
    (hmax : ∀ l, l₀ < l → 𝔞.ideal l = ⊥) : 𝔞.phi (BerkovichPoint.trivial p) = l₀ := by
  let := isLocallyNoetherian_of_isProjective p
  apply le_antisymm (𝔞.phi_le _ hmax)
  have h := 𝔞.ofReal_sub_phi_le (BerkovichPoint.trivial p) l₀
  rw [SGPT.NAPotential.ThinApprox.TrivialIdeal.trivial_idealVal_eq_zero hl₀, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at h
  linarith

/-- The largest weight `λ₀` with `𝔞_{λ₀} ≠ 0`. -/
theorem exists_max_weight (𝔞 : FlagIdeal X) :
    ∃ l₀ : ℤ, 𝔞.ideal l₀ ≠ ⊥ ∧ ∀ l, l₀ < l → 𝔞.ideal l = ⊥ := by
  classical
  obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound 𝔞
  obtain ⟨a, ha⟩ := 𝔞.exists_eq_top
  have htop : (⊤ : X.IdealSheafData) ≠ ⊥ := by
    intro h
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have h1 := Scheme.IdealSheafData.stalkIdeal_top x
    rw [h, Scheme.IdealSheafData.stalkIdeal_bot] at h1
    exact bot_ne_top h1
  obtain ⟨l₀, hl₀, hmax⟩ := Int.exists_greatest_of_bdd (P := fun l => 𝔞.ideal l ≠ ⊥)
    ⟨b, fun z hz => by
      by_contra h
      exact hz (hb z (lt_of_not_ge h))⟩ ⟨a, by rw [ha a le_rfl]; exact htop⟩
  exact ⟨l₀, hl₀, fun l hl => by
    by_contra h
    exact absurd (hmax l h) (not_le.mpr hl)⟩

end triv

/-! ### `equ:mixedMA0` -/

section pairTriv

variable [CompactSpace X] [X.IsSeparated] (n : ℕ) (hX : topologicalKrullDim X ≤ n)
  (ω : PicQ X)

theorem flagPair_triv_phi (hXn : topologicalKrullDim X = n) (hn : 0 < n) (𝔞 : FlagIdeal X) :
    (flagPair n hX ω (((0 : ℚ), 𝔞.phi) ::ₘ
        Multiset.replicate n ((1 : ℚ), (0 : BerkovichPoint p → ℝ))) : ℝ) =
      volQ p n hX ω * 𝔞.phi (BerkovichPoint.trivial p) := by
  classical
  obtain ⟨l₀, hl₀, hmax⟩ := exists_max_weight 𝔞
  have hb : IsWeightBound 𝔞 l₀ := hmax
  obtain ⟨hgood, hdom⟩ := isGoodModel_mul_monomial p hb
  set 𝔠 := 𝔞 * FlagIdeal.monomial X 0
  set c := l₀ + 1
  let e := FlagDatum.ofDominates hdom hb
  let D : FDiv p 𝔠 c := Finsupp.single (centralDatum hgood) (l₀ : ℚ) - Finsupp.single e 1
  have hD : FDiv.fn D = 𝔞.phi := by
    funext v
    simp only [D, map_sub, FDiv.fn_single, fn_centralDatum, Pi.sub_apply, Pi.smul_apply,
      FlagDatum.fn_vert, e, FlagDatum.ofDominates, Rat.smul_def, one_smul, Rat.cast_intCast,
      mul_one]
    ring
  let R : (BerkovichPoint p → ℝ) → FDiv p 𝔠 c := fun φ => if φ = 𝔞.phi then D else 0
  have hRphi : R 𝔞.phi = D := if_pos rfl
  have hR0 : FDiv.fn (R 0) = 0 := by
    by_cases h0 : (0 : BerkovichPoint p → ℝ) = 𝔞.phi
    · rw [show R 0 = D from if_pos h0, hD, h0]
    · rw [show R 0 = 0 from if_neg h0, map_zero]
  have hR : ∀ x ∈ (((0 : ℚ), 𝔞.phi) ::ₘ
      Multiset.replicate n ((1 : ℚ), (0 : BerkovichPoint p → ℝ))), FDiv.fn (R x.2) = x.2 := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hRphi ▸ hD
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hR0
  rw [flagPair_eq n hX ω hgood _ (fun x hx => ⟨R x.2, hR x hx⟩),
    ← interFormQ_flag_eq_modelValue n hX ω hgood _ R hR]
  simp only [Multiset.map_cons, Multiset.map_replicate]
  -- `R 0` only matters through `ν^*`, where it vanishes
  have hν : picPullbackQ (normModelν p 𝔠 c) ((1 : ℚ) • omegaPullback 𝔠 c ω + FDiv.cls (R 0)) =
      picPullbackQ (normModelν p 𝔠 c) (omegaPullback 𝔠 c ω) := by
    have h0 : picPullbackQ (normModelν p 𝔠 c) (FDiv.cls (R 0)) = 0 :=
      FDiv.ncls_eq_zero hgood.central_isInvertible (R 0) hR0
    rw [map_add, one_smul, h0, add_zero]
  have hzero : ∀ a : PicQ (flagModel p 𝔠 c),
      interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
        (Scheme.Modules.unitObj _) (a ::ₘ Multiset.replicate n
          ((1 : ℚ) • omegaPullback 𝔠 c ω + FDiv.cls (R 0))) =
      interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
        (Scheme.Modules.unitObj _) (a ::ₘ Multiset.replicate n (omegaPullback 𝔠 c ω)) := by
    intro a
    rw [← interFormQ_normModel p 𝔠 c (n + 1), ← interFormQ_normModel p 𝔠 c (n + 1),
      Multiset.map_cons, Multiset.map_cons, Multiset.map_replicate, Multiset.map_replicate, hν]
  rw [hzero, zero_smul, zero_add, hRphi]
  simp only [D, map_sub, FDiv.cls_single, picQ_centralDatum, one_smul]
  rw [MultisetForm.map_sub, MultisetForm.map_smul, interFormQ_central_omega n hX ω,
    interFormQ_flagVert_omega_eq_zero n hX ω hXn hn e hl₀,
    phi_trivial_eq 𝔞 hl₀ hmax, volQ]
  push_cast
  ring

/-- **[BJ22, `equ:mixedMA0`]**: `(0, f) ⋅ (ω, 0)^n = (ω^n) f(v_triv)` for every PL function `f`,
when `dim X = n ≥ 1`. This is the axiom `PairTriv` of lane BJ-PAIR. -/
theorem pairTriv (hXn : topologicalKrullDim X = n) (hn : 0 < n) : PairTriv p n hX ω := by
  intro f hf
  have hrest : ∀ z ∈ Multiset.replicate n ((1 : ℚ), (0 : BerkovichPoint p → ℝ)),
      z.2 ∈ plSubmodule p := fun z hz => by
    rw [Multiset.eq_of_mem_replicate hz]; exact Submodule.zero_mem _
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨𝔞, rfl⟩ := hx
    exact flagPair_triv_phi n hX ω hXn hn 𝔞
  | zero =>
    have h := flagPair_cons_smul n hX ω 0 ((0 : ℚ), (0 : BerkovichPoint p → ℝ)) _
      (Submodule.zero_mem _) hrest
    rw [zero_smul, zero_mul] at h
    rw [show ((0 : ℚ), (0 : BerkovichPoint p → ℝ)) = (0 : ℚ × (BerkovichPoint p → ℝ)) from rfl, h]
    simp
  | add x y hx' hy' hx hy =>
    have h := flagPair_cons_add n hX ω ((0 : ℚ), x) ((0 : ℚ), y) _ hx' hy' hrest
    rw [show ((0 : ℚ), x + y) = ((0 : ℚ), x) + ((0 : ℚ), y) by rw [Prod.mk_add_mk, add_zero], h]
    push_cast
    rw [hx, hy, Pi.add_apply]
    ring
  | smul q x hx' hx =>
    have h := flagPair_cons_smul n hX ω q ((0 : ℚ), x) _ hx' hrest
    rw [show ((0 : ℚ), q • x) = q • ((0 : ℚ), x) by rw [Prod.smul_mk, smul_zero], h]
    push_cast
    rw [hx, Pi.smul_apply, Rat.smul_def]
    ring

end pairTriv

end SGPT.NAPotential.ThinApprox.BJ
