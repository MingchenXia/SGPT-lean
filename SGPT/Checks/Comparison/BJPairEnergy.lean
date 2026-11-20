import SGPT.Checks.Comparison.BJPairModel
import SGPT.Checks.Comparison.BJChargeFS
import SGPT.NAPotential.BJEnergyPairing

/-!
# Positivity of the energy pairing and the `EnergyPairing` of a class (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), Lemma `lem:enmono` (mixed Monge–Ampère measures of
`ω`-psh PL functions are positive), Example `exam:FSpsh`, §3.1–§3.2, and the structure
`SGPT.NAPotential.BJEnergy.EnergyPairing`. Towards `thm:BJappseq` of
`chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

* `flagPair_nonneg` (**[BJ22, `lem:enmono`]**): `(0, f) ⋅ (ω, u₁) ⋯ (ω, u_n) ≥ 0` for a PL function
  `f ≥ 0` and `ω`-psh PL functions `uᵢ`: on the normalized model a positive multiple of `D_f` is an
  effective vertical divisor `K` (`FDiv.exists_effective`), and `[𝒪(K)] ⋅ θ₁ ⋯ θ_n ≥ 0` for classes
  `θᵢ` in the relatively nef cone (BJ-INTERSECT's `interFormQ_effective_nonneg`, expanded over the
  cone by `MultisetForm.nonneg_of_mem_hull`);
* `isFlagPsh_zero`, `isFlagPsh_of_isFlagFS`: `0` and the Fubini–Study functions of `ω`
  ([BJ22, `exam:FSpsh`], following the proof) are `ω`-psh in the flag form;
* `energyPairingOfAxioms`: **the energy pairing of `ω`** as an `EnergyPairing` on `X^An` with
  `F = PL(X)`, `pair = flagPair`, `psh = IsFlagPsh ω`, `triv = v_triv`, `vol = (ω^n)`; all fields
  are proved except the three geometric statements `PairConst` ([BJ22, `prop:intpairing` (i)]),
  `PairTriv` ([BJ22, `equ:mixedMA0`]) and `PairHodge` ([BJ22, `lem:Hodge`]) and `0 < (ω^n)`, which
  are hypotheses;
* `bjAppSeq_of_pairAxioms`: `thm:BJappseq` from `thm:pshdetbydiv`, these axioms and the charging
  of divisorial points (lane BJ-CHARGE, R8), in every ample rational class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge SGPT.NAPotential.BJEnergy
open FlagIdealBound

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### Positivity -/

section positivity

/-- The generic point of a model is not in the central fibre. -/
theorem genericPoint_normModel_not_mem (𝔠 : FlagIdeal X) (c : ℤ) :
    genericPoint (normModel p 𝔠 c) ∉ normModelν p 𝔠 c ⁻¹' centralFibre p 𝔠 c := by
  let := productLine_isIntegral_of_isProjective p
  obtain ⟨V, hV, hiso⟩ := exists_isIso_normModelν_restrict p 𝔠 c
  obtain ⟨h1, -⟩ := genericPoint_eq_and_bijective_of_isIso_restrict (normModelν p 𝔠 c) V
  intro hmem
  change flagModelπ p 𝔠 c (normModelν p 𝔠 c (genericPoint (normModel p 𝔠 c))) ∈
    ((centralIdeal p).support : Set (productLine p)) at hmem
  rw [h1, (flagModelπ_genericPoint p 𝔠 c).1] at hmem
  apply support_centralIdeal_ne_top p
  rw [eq_top_iff]
  intro z _
  have hcl : z ∈ closure ({genericPoint (productLine p)} : Set (productLine p)) := by
    rw [(genericPoint_spec (productLine p)).def]; trivial
  exact (closure_minimal (Set.singleton_subset_iff.mpr hmem)
    (centralIdeal p).support.isClosed) hcl

variable (n : ℕ) (hX : topologicalKrullDim X ≤ n) (ω : PicQ X)

/-- Positivity on one model. -/
theorem modelValue_nonneg {𝔠 : FlagIdeal X} {c : ℤ} (hgood : IsGoodModel p 𝔠 c)
    {f : BerkovichPoint p → ℝ} (hf : IsFlagRep p 𝔠 c f) (hf0 : 0 ≤ f)
    (us : Multiset (BerkovichPoint p → ℝ)) (hcard : Multiset.card us = n)
    (hu : ∀ u ∈ us, IsFlagPshOn p ω 𝔠 c u) :
    0 ≤ modelValue n hX ω 𝔠 c (((0 : ℚ), f) ::ₘ us.map fun u => ((1 : ℚ), u)) := by
  obtain ⟨N, K, hK, hN, hKsupp, hNK⟩ := FDiv.exists_effective hgood.central_isInvertible
    (flagRep 𝔠 c f) (by rw [fn_flagRep hf]; exact hf0)
  set Φ := interFormQ (normModelStructure p 𝔠 c) (n + 1)
    (topologicalKrullDim_normModel_le p 𝔠 c n hX) (Scheme.Modules.unitObj _)
  set W := normModelν p 𝔠 c ⁻¹' centralFibre p 𝔠 c
  -- the classes `ν^*(π^*ω + D_u)`
  have hcls : ∀ u ∈ us, modelClass ω 𝔠 c ((1 : ℚ), u) ∈
      relNefCone (normModelStructure p 𝔠 c) W := by
    intro u hu'
    obtain ⟨D, hD, hDn⟩ := hu u hu'
    rw [modelClass_eq ω hgood _ D hD, one_smul, normOmega, FDiv.ncls, LinearMap.comp_apply,
      ← map_add]
    exact picPullbackQ_mem_relNefCone (flagModelStructure p 𝔠 c) (normModelν p 𝔠 c) hDn
  have hf_cls : modelClass ω 𝔠 c ((0 : ℚ), f) = FDiv.ncls (flagRep 𝔠 c f) := by
    rw [modelClass, zero_smul, zero_add]
  -- the effective divisor `K`
  have hL := cartierLine_isInvertible hK
  have hcart : picQ ⟨cartierLine K, hL⟩ = -picQ ⟨K.toModules, hK.isInvertibleModule_toModules⟩ := by
    rw [picQ, picQ, lineCls_cartierLine hK, TensorProduct.tmul_neg]
  have hzero := zeroIdeal_cartierSection K hK
  have hs0 : cartierSection K hK ≠ 0 := by
    refine ne_zero_of_not_mem_support (cartierLine K) hL _ (genericPoint (normModel p 𝔠 c)) ?_
    rw [hzero]
    exact fun h => genericPoint_normModel_not_mem 𝔠 c (hKsupp h)
  -- the generators of the nef cone
  let I := {N : {N : (normModel p 𝔠 c).Modules // Scheme.Modules.IsInvertible N} //
    IsNefOn (normModelStructure p 𝔠 c) N.1 W}
  let gen : I → PicQ (normModel p 𝔠 c) := fun i => picQ i.1
  have hcone : relNefCone (normModelStructure p 𝔠 c) W ≤ PointedCone.hull ℚ (Set.range gen) :=
    Submodule.span_mono fun θ ⟨N, hN, hθ⟩ => ⟨⟨N, hN⟩, hθ.symm⟩
  have key : 0 ≤ Φ ({picQ ⟨cartierLine K, hL⟩} + us.map fun u => modelClass ω 𝔠 c ((1 : ℚ), u)) := by
    refine MultisetForm.nonneg_of_mem_hull Φ gen _ _ (fun θ hθ => ?_) (fun l hl => ?_)
    · obtain ⟨u, hu', rfl⟩ := Multiset.mem_map.mp hθ
      exact hcone (hcls u hu')
    · have h := interFormQ_effective_nonneg n (normModelStructure p 𝔠 c)
        (topologicalKrullDim_normModel_le p 𝔠 c n hX) (cartierLine K) hL (cartierSection K hK) hs0
        (l.map fun i => (i.1, (1 : ℚ))) (by simpa [hcard] using hl)
        (fun N hN => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hN
          rw [hzero]
          exact i.2.mono hKsupp)
        (fun N hN => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hN
          exact zero_le_one) 1 zero_le_one
      rw [one_smul, List.map_map] at h
      convert h using 2
      rw [Multiset.singleton_add]
      congr 1
      congr 1
      exact List.map_congr_left fun i _ => (one_smul ℚ _).symm
  have hval : (N : ℚ) * modelValue n hX ω 𝔠 c (((0 : ℚ), f) ::ₘ us.map fun u => ((1 : ℚ), u)) =
      Φ ({picQ ⟨cartierLine K, hL⟩} + us.map fun u => modelClass ω 𝔠 c ((1 : ℚ), u)) := by
    rw [modelValue, Multiset.map_cons, Multiset.map_map, hf_cls, ← MultisetForm.map_smul, hNK,
      ← hcart, Multiset.singleton_add]
    rfl
  rw [← hval] at key
  exact nonneg_of_mul_nonneg_right (by linarith) (by exact_mod_cast hN : (0 : ℚ) < N)

/-- **Positivity of the energy pairing** ([BJ22, `lem:enmono`]): for a PL function `f ≥ 0` and
`ω`-psh PL functions `u₁, …, u_n`, `(0, f) ⋅ (ω, u₁) ⋯ (ω, u_n) ≥ 0`. -/
theorem flagPair_nonneg {f : BerkovichPoint p → ℝ} (hf : f ∈ plSubmodule p) (hf0 : 0 ≤ f)
    (us : Multiset (BerkovichPoint p → ℝ)) (hcard : Multiset.card us = n)
    (hu : ∀ u ∈ us, IsFlagPsh p ω u) :
    0 ≤ flagPair n hX ω (((0 : ℚ), f) ::ₘ us.map fun u => ((1 : ℚ), u)) := by
  classical
  obtain ⟨𝔠, c, hgood, hP⟩ := exists_common_goodModel
    (fun 𝔠 c φ => IsFlagRep p 𝔠 c φ ∧ (φ ∈ us → IsFlagPshOn p ω 𝔠 c φ))
    (fun _ _ _ _ g hg _ hφ => ⟨hφ.1.pullback g hg, fun h => (hφ.2 h).pullback g hg⟩)
    (f ::ₘ us) (fun φ hφ => by
      by_cases hφu : φ ∈ us
      · obtain ⟨𝔠, c, hgood, D, hD, hDn⟩ := hu φ hφu
        exact ⟨𝔠, c, hgood, ⟨D, hD⟩, fun _ => ⟨D, hD, hDn⟩⟩
      · have hφf : φ = f := by
          rcases Multiset.mem_cons.mp hφ with h | h
          · exact h
          · exact absurd h hφu
        subst hφf
        obtain ⟨𝔠, c, hgood, hrep⟩ := exists_goodModel_flagRep hf
        exact ⟨𝔠, c, hgood, hrep, fun h => absurd h hφu⟩)
  rw [flagPair_eq n hX ω hgood _ (fun x hx => by
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact (hP _ (Multiset.mem_cons_self _ _)).1
    · obtain ⟨u, hu', rfl⟩ := Multiset.mem_map.mp hx
      exact (hP u (Multiset.mem_cons_of_mem hu')).1)]
  exact modelValue_nonneg n hX ω hgood (hP f (Multiset.mem_cons_self _ _)).1 hf0 us hcard
    fun u hu' => (hP u (Multiset.mem_cons_of_mem hu')).2 hu'

end positivity

/-! ### `ω`-psh functions: `0` and the Fubini–Study functions -/

section psh

omit [IsIntegral X] in
/-- `0` is `ω`-psh when `ω` is a nonnegative combination of nef classes. -/
theorem isFlagPsh_zero [CompactSpace X] {ω : PicQ X} (hω : ω ∈ relNefCone p Set.univ) :
    IsFlagPsh p ω (0 : BerkovichPoint p → ℝ) := by
  obtain ⟨𝔠, c, hgood⟩ := exists_isGoodModel (p := p)
  refine ⟨𝔠, c, hgood, 0, map_zero _, ?_⟩
  rw [map_zero, add_zero]
  have hcomp : (flagModelπ p 𝔠 c ≫ productFst p) ≫ p = flagModelStructure p 𝔠 c := by
    rw [flagModelStructure, Category.assoc]
  have : IsProjective ((flagModelπ p 𝔠 c ≫ productFst p) ≫ p) := by
    rw [hcomp]; infer_instance
  have h := picPullbackQ_mem_relNefCone p (flagModelπ p 𝔠 c ≫ productFst p) hω
  rw [Set.preimage_univ] at h
  have h' := relNefCone_mono ((flagModelπ p 𝔠 c ≫ productFst p) ≫ p)
    (Set.subset_univ (centralFibre p 𝔠 c)) h
  rw [omegaPullback_eq_picPullbackQ, ← hcomp]
  exact h'

open SGPT.NAPotential.BJ.NativePicard in
/-- **Fubini–Study functions are `ω`-psh** ([BJ22, `exam:FSpsh`]), in the flag form: lane
BJ-CHARGE's proof of `isOmegaPshPL_of_isFlagFS`, with the representative `k⁻¹ (b 𝒳₀ - E_{t^b 𝔞})`
written as a combination of flag data. -/
theorem isFlagPsh_of_isFlagFS {ω : RationalPicardSpace X} {φ : BerkovichPoint p → ℝ}
    (h : IsFlagFS p ω φ) : IsFlagPsh p ω φ := by
  obtain ⟨M, a, k, hk, 𝔞, hgen, hcls, hφ⟩ := h
  have hM : Scheme.Modules.IsInvertible M := isInvertible_of_atlas a
  obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound 𝔞
  obtain ⟨hgood, hdom⟩ := isGoodModel_mul_monomial p hb
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  set 𝔠 := 𝔞 * FlagIdeal.monomial X 0
  set c := b + 1
  let D : FDiv p 𝔠 c := ((k : ℚ)⁻¹) • (Finsupp.single (centralDatum hgood) (b : ℚ) -
    Finsupp.single (FlagDatum.ofDominates hdom hb) 1)
  have hflag : picQ (FlagDatum.ofDominates hdom hb).vert.line = picQ (flagVert hdom).line :=
    VertCartier.picQ_line_congr rfl
  refine ⟨_, _, hgood, D, ?_, ?_⟩
  · funext v
    simp only [D, map_smul, map_sub, FDiv.fn_single, Pi.smul_apply, Pi.sub_apply,
      fn_centralDatum, FlagDatum.fn_vert, FlagDatum.ofDominates, hφ v, Rat.smul_def, one_smul]
    push_cast
    ring
  · let π := flagModelπ p 𝔠 c
    have hinv : Scheme.Modules.IsInvertible (flagLine p M 𝔞 b 𝔠 c) :=
      (hdom.1.isInvertibleModule_toModules.tensorObj (hM.pullback (π ≫ productFst p))).of_iso
        (SGPT.Support.ModularCurves.monoidalTensorObjIso _ _)
    have hN : picQ ⟨flagLine p M 𝔞 b 𝔠 c, hinv⟩ ∈
        relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c) :=
      picQ_mem_relNefCone _ _ (isNefOn_flagLine p hM hgen b hdom)
    have hω : ω = ((k : ℚ)⁻¹) • picQ ⟨M, hM⟩ := by
      rw [← rationalPicardClass_eq_picQ a, hcls, smul_smul, inv_mul_cancel₀ hk', one_smul]
    have hline : picQ ⟨flagLine p M 𝔞 b 𝔠 c, hinv⟩ =
        picQ (flagVert hdom).line + omegaPullback 𝔠 c (picQ ⟨M, hM⟩) := by
      rw [omegaPullback, picPullbackQ_picQ]
      exact picQ_tensor hdom.1.isInvertibleModule_toModules (hM.pullback (π ≫ productFst p)) hinv
    have key : omegaPullback 𝔠 c ω + FDiv.cls D =
        ((k : ℚ)⁻¹) • (picQ ⟨flagLine p M 𝔞 b 𝔠 c, hinv⟩ +
          (b : ℚ) • -picQ (centralLine p 𝔠 c)) := by
      simp only [D]
      rw [hline, hω, map_smul, map_smul, map_sub, FDiv.cls_single, FDiv.cls_single,
        picQ_centralDatum, hflag]
      module
    rw [key]
    refine Submodule.smul_mem _ (⟨(k : ℚ)⁻¹, by positivity⟩ : {r : ℚ // 0 ≤ r}) (add_mem hN ?_)
    rcases le_or_gt 0 b with hb0 | hb0
    · exact Submodule.smul_mem _ (⟨(b : ℚ), by exact_mod_cast hb0⟩ : {r : ℚ // 0 ≤ r})
        (neg_picQ_centralLine_mem_relNefCone p 𝔠 c)
    · rw [show (b : ℚ) • -picQ (centralLine p 𝔠 c) = (-(b : ℚ)) • picQ (centralLine p 𝔠 c) by
        rw [smul_neg, neg_smul]]
      exact Submodule.smul_mem _ (⟨-(b : ℚ), by
        have : (b : ℚ) < 0 := by exact_mod_cast hb0
        linarith⟩ : {r : ℚ // 0 ≤ r}) (picQ_centralLine_mem_relNefCone p 𝔠 c)

end psh

/-! ### The energy pairing of a class -/

section energy

variable [CompactSpace X] [X.IsSeparated] (n : ℕ) (hX : topologicalKrullDim X ≤ n) (ω : PicQ X)

variable (p) in
/-- The volume `(ω^n)_X`. -/
def volQ : ℚ :=
  interFormQ p n hX (Scheme.Modules.unitObj X) (Multiset.replicate n ω)

variable (p) in
/-- **[BJ22, `prop:intpairing` (i)]** for the pairing `flagPair`:
`(0, 1) ⋅ (s₁ ω, φ₁) ⋯ (s_n ω, φ_n) = (∏ sᵢ) (ω^n)` (the central fibre is linearly equivalent to
the fibre at infinity). Not proved here. -/
def PairConst : Prop :=
  ∀ s : Multiset (ℚ × (BerkovichPoint p → ℝ)), Multiset.card s = n →
    (∀ x ∈ s, x.2 ∈ plSubmodule p) →
      flagPair n hX ω (((0 : ℚ), (1 : BerkovichPoint p → ℝ)) ::ₘ s) =
        volQ p n hX ω * (s.map Prod.fst).prod

variable (p) in
/-- **[BJ22, `equ:mixedMA0`]** for the pairing `flagPair`:
`(0, f) ⋅ (ω, 0)^n = (ω^n) f(v_triv)`. Not proved here. -/
def PairTriv : Prop :=
  ∀ f ∈ plSubmodule p,
    (flagPair n hX ω (((0 : ℚ), f) ::ₘ Multiset.replicate n ((1 : ℚ), (0 : BerkovichPoint p → ℝ))) :
      ℝ) = volQ p n hX ω * f (BerkovichPoint.trivial p)

variable (p) in
/-- **[BJ22, `lem:Hodge`]** for the pairing `flagPair`:
`(0, f)² ⋅ (ω, u₁) ⋯ (ω, u_{n-1}) ≤ 0` for `ω`-psh `uᵢ`. Not proved here (BJ-HODGE's
`interFormQ_sq_nonpos_of_vertical` needs the fibre at infinity of `ℙ¹`). -/
def PairHodge : Prop :=
  ∀ f ∈ plSubmodule p, ∀ us : Multiset (BerkovichPoint p → ℝ), Multiset.card us + 1 = n →
    (∀ u ∈ us, u ∈ plSubmodule p ∧ IsFlagPsh p ω u) →
      flagPair n hX ω (((0 : ℚ), f) ::ₘ ((0 : ℚ), f) ::ₘ us.map fun u => ((1 : ℚ), u)) ≤ 0

/-- The pairing on multisets of pairs `(s, f)`, `f ∈ PL(X)`. -/
def plPair (s : Multiset (ℚ × plSubmodule p)) : ℝ :=
  (flagPair n hX ω (s.map fun x => (x.1, (x.2 : BerkovichPoint p → ℝ))) : ℝ)

omit [IsIntegral X] [CompactSpace X] [X.IsSeparated] in
theorem mem_of_mem_map_pl {s : Multiset (ℚ × plSubmodule p)} :
    ∀ z ∈ s.map (fun x => (x.1, (x.2 : BerkovichPoint p → ℝ))), z.2 ∈ plSubmodule p := by
  intro z hz
  obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hz
  exact x.2.2

/-- **The energy pairing of `ω`** ([BJ22, `defi:intpairing`, `prop:intpairing`, `lem:enmono`,
`lem:Hodge`, `equ:mixedMA0`]) as an `EnergyPairing` on `X^An`: the PL functions, the pairing
`flagPair`, the volume `(ω^n)`, the trivial valuation and the flag `ω`-psh PL functions. All the
axioms are proved except `PairConst`, `PairTriv`, `PairHodge` and `0 < (ω^n)`, which are
hypotheses. -/
def energyPairingOfAxioms (hω : ω ∈ relNefCone p Set.univ)
    (hvol : 0 < volQ p n hX ω) (hconst : PairConst p n hX ω) (htriv : PairTriv p n hX ω)
    (hhodge : PairHodge p n hX ω) : EnergyPairing (BerkovichPoint p) n where
  F := plSubmodule p
  one_mem := by
    have h : (1 : BerkovichPoint p → ℝ) = fun _ => ((1 : ℚ) : ℝ) := by
      funext v
      simp
    rw [h]
    exact const_mem_plSubmodule (f := p) (1 : ℚ)
  pair := plPair n hX ω
  pair_add x y s := by
    simp only [plPair, Multiset.map_cons]
    rw [show ((x + y).1, ((x + y).2 : BerkovichPoint p → ℝ)) =
      (x.1, (x.2 : BerkovichPoint p → ℝ)) + (y.1, (y.2 : BerkovichPoint p → ℝ)) from rfl,
      flagPair_cons_add n hX ω _ _ _ x.2.2 y.2.2 mem_of_mem_map_pl]
    push_cast
    ring
  pair_smul q x s := by
    simp only [plPair, Multiset.map_cons]
    rw [show ((q • x).1, ((q • x).2 : BerkovichPoint p → ℝ)) =
      q • (x.1, (x.2 : BerkovichPoint p → ℝ)) from rfl,
      flagPair_cons_smul n hX ω _ _ _ x.2.2 mem_of_mem_map_pl]
    push_cast
    ring
  vol := volQ p n hX ω
  vol_pos := by exact_mod_cast hvol
  pair_const s hs := by
    simp only [plPair, Multiset.map_cons]
    rw [hconst _ (by simpa using hs) mem_of_mem_map_pl, Multiset.map_map]
    push_cast
    simp
  pair_zero := by
    simp only [plPair, Multiset.map_replicate]
    exact_mod_cast flagPair_zero n hX ω
  triv := BerkovichPoint.trivial p
  pair_triv f := by
    simp only [plPair, Multiset.map_cons, Multiset.map_replicate]
    exact htriv f f.2
  psh := {f | IsFlagPsh p ω f}
  zero_mem_psh := isFlagPsh_zero hω
  add_const_mem_psh u hu c := by
    have h := IsFlagPsh.add_const hu c
    have e : ((u + c • (⟨1, by
        have h1 : (1 : BerkovichPoint p → ℝ) = fun _ => ((1 : ℚ) : ℝ) := by
          funext v
          simp
        rw [h1]
        exact const_mem_plSubmodule (f := p) (1 : ℚ)⟩ : plSubmodule p) : plSubmodule p) :
          BerkovichPoint p → ℝ) = (u : BerkovichPoint p → ℝ) + fun _ => (c : ℝ) := by
      funext v
      simp [Rat.smul_def]
    change IsFlagPsh p ω _
    rw [e]
    exact h
  midpoint_mem_psh u hu w hw := IsFlagPsh.midpoint hu hw
  positivity f s hs hpsh hf := by
    simp only [plPair, Multiset.map_cons]
    have := flagPair_nonneg n hX ω f.2 (fun v => hf v) (s.map Subtype.val)
      (by simpa using hs) (fun u hu => by
        obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.mp hu
        exact hpsh u' hu')
    have hm' : (s.map fun u => ((1 : ℚ), u)).map (fun x => (x.1, (x.2 : BerkovichPoint p → ℝ))) =
        (s.map Subtype.val).map fun u => ((1 : ℚ), u) := by
      rw [Multiset.map_map, Multiset.map_map]
      rfl
    rw [hm']
    exact_mod_cast this
  hodge f s hs hpsh := by
    simp only [plPair, Multiset.map_cons]
    have hm' : (s.map fun u => ((1 : ℚ), u)).map (fun x => (x.1, (x.2 : BerkovichPoint p → ℝ))) =
        (s.map Subtype.val).map fun u => ((1 : ℚ), u) := by
      rw [Multiset.map_map, Multiset.map_map]
      rfl
    have := hhodge f f.2 (s.map Subtype.val) (by simpa using hs)
      (fun u hu => by
        obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.mp hu
        exact ⟨u'.2, hpsh u' hu'⟩)
    rw [hm']
    exact_mod_cast this

theorem energyPairingOfAxioms_triv (hω : ω ∈ relNefCone p Set.univ)
    (hvol : 0 < volQ p n hX ω) (hconst : PairConst p n hX ω) (htriv : PairTriv p n hX ω)
    (hhodge : PairHodge p n hX ω) :
    (energyPairingOfAxioms n hX ω hω hvol hconst htriv hhodge).triv =
      BerkovichPoint.trivial p := rfl

/-- The Fubini–Study functions of `ω` are `ω`-psh functions of the energy pairing. -/
theorem energyPairingOfAxioms_flagFS {ω : NativePicard.RationalPicardSpace X}
    (hω : ω ∈ relNefCone p Set.univ) (hvol : 0 < volQ p n hX ω) (hconst : PairConst p n hX ω)
    (htriv : PairTriv p n hX ω) (hhodge : PairHodge p n hX ω) (φ : BerkovichPoint p → ℝ)
    (hφ : IsFlagFS p ω φ) :
    ∃ f ∈ (energyPairingOfAxioms n hX ω hω hvol hconst htriv hhodge).psh,
      (f : BerkovichPoint p → ℝ) = φ := by
  have hpl : φ ∈ plSubmodule p := by
    obtain ⟨M, a, k, hk, 𝔞, -, -, hφ⟩ := hφ
    have : φ = ((k : ℚ)⁻¹) • 𝔞.phi := by
      funext v
      rw [hφ v, Pi.smul_apply, Rat.smul_def]
      push_cast
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (phi_mem_plSubmodule (f := p) 𝔞)
  exact ⟨⟨φ, hpl⟩, isFlagPsh_of_isFlagFS hφ, rfl⟩

end energy

/-! ### `thm:BJappseq` from the remaining axioms -/

/-- **`thm:BJappseq` from the energy pairing axioms.** Assume `thm:pshdetbydiv`
(`DivisorialComparison`, proved in `SGPT.Checks.Literature`) and, for every rational class `ω` with
ample numerical class: `ω` is a nonnegative combination of nef classes, `(ω^n) > 0`, the three
axioms `PairConst`, `PairTriv`, `PairHodge` of the pairing `flagPair`, and the charging of the
divisorial points ([BJ22, `equ:mixedMAPL`], step R8 of lane BJ-CHARGE) by the resulting energy
pairing. Then `thm:BJappseq` holds. Everything else (multilinearity and well-definedness of the
pairing, `prop:intpairing` (iii), `lem:enmono`, the `ω`-psh PL functions and the Fubini–Study
functions among them) is proved. -/
theorem bjAppSeq_of_pairAxioms [CompactSpace X] [X.IsSeparated]
    (hcomp : SGPT.NAPotential.BJ.AppSeq.DivisorialComparison p) (n : ℕ)
    (hX : topologicalKrullDim X ≤ n)
    (hE : ∀ ω : NativePicard.RationalPicardSpace X,
      NativePicard.numericalClass p ω ∈ SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p →
        ∃ (hω : ω ∈ relNefCone p Set.univ) (hvol : 0 < volQ p n hX ω)
          (hconst : PairConst p n hX ω) (htriv : PairTriv p n hX ω)
          (hhodge : PairHodge p n hX ω),
          ∀ v ∈ divisorialSet p,
            (energyPairingOfAxioms n hX ω hω hvol hconst htriv hhodge).IsCharged v) :
    SGPT.NAPotential.BJ.AppSeq.BJAppSeqStatement.{u} p := by
  refine bjAppSeq_of_flagFS_pairings p hcomp fun ω hω => ?_
  obtain ⟨hω', hvol, hconst, htriv, hhodge, hcharged⟩ := hE ω hω
  exact ⟨n, energyPairingOfAxioms n hX ω hω' hvol hconst htriv hhodge, rfl,
    energyPairingOfAxioms_flagFS n hX hω' hvol hconst htriv hhodge, hcharged⟩

end SGPT.NAPotential.BJ
