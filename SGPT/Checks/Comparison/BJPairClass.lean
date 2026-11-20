import SGPT.Checks.Comparison.BJPairFlag
import SGPT.Checks.Comparison.BJHodgeLine

/-!
# Well-definedness of `φ_D ↦ [𝒪(D)]` for divisors of flag ideals (lane BJ-PAIR, R5a)

Source: [BJ22] (`references/bj22-trivval`), §2.2 (on a normal test configuration a vertical
divisor is determined by its PL function: `ord_E(D) = b_E φ_D(v_E)`), §3.2 (`defi:intpairing`:
the energy pairing is a function of PL *functions*) and Lemma `lem:enmono` (positivity).
Towards `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

On a blow-up model `𝒳 = flagModel p 𝔠 c` a **flag datum** is a flag ideal `𝔞`
with a weight bound `b` such that `(t^b 𝔞) · 𝒪_𝒳` is invertible; it defines the vertical Cartier
divisor `E_{(𝔞,b)}` with `φ = b - φ_𝔞`. `FDiv p 𝔠 c` is the `ℚ`-vector space of formal
combinations of flag data, with the linear maps `FDiv.fn` (to functions on `X^An`) and
`FDiv.cls` (to `Pic(𝒳)_ℚ`). Every PL function is `FDiv.fn D` on some model (`flagDiv`).

* `FDiv.ncls_eq_zero` (**well-definedness**, [BJ22, §2.2]): if `φ_D = 0` then the pull-back of
  `[𝒪(D)]` to the normalized model is `0`;
* `FDiv.exists_effective` (**positivity**): if `φ_D ≥ 0`, a positive multiple of the pull-back of
  `[𝒪(D)]` is the class `[𝒪(K)] = -[K]` of an invertible ideal sheaf `K` supported in the central
  fibre (an effective vertical Cartier divisor).

Proof: clear denominators and write `N D = D⁺ - D⁻` with `D^±` combinations with coefficients in
`ℕ`; their ideals `J^± = ∏ (t^{b_e} 𝔞_e)^{n_e} · 𝒪` on the normalized model `𝒳̃` have, at every
point `z` with a DVR as local ring, the value `ord_z(J^±) = c_z φ_{D^±}(v_z)`
(`exists_idealVal_ordPoint_flagSheaf`), so `φ_D = 0` (resp. `≥ 0`) gives `J⁺ = J⁻` (resp.
`J⁺ ⊆ J⁻`, and `K = (J⁺ : J⁻)`) by the normality criterion `idealSheaf_le_of_forall_idealVal`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge
open FlagIdealBound
open scoped ENNReal

/-! ### Restrictions of isomorphisms -/

section restrict

universe u

/-- A morphism which is an isomorphism over `U` is an isomorphism over every `V ≤ U`. -/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens}
    (hVU : V ≤ U) [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by
  have hpre : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := fun x hx => hVU hx
  have s : IsPullback (f ∣_ V) (Y.homOfLE hpre ≫ (f ⁻¹ᵁ U).ι) (X.homOfLE hVU ≫ U.ι) f := by
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    exact isPullback_morphismRestrict f V
  have comm : f ∣_ V ≫ X.homOfLE hVU = Y.homOfLE hpre ≫ f ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  exact (IsPullback.of_bot s comm (isPullback_morphismRestrict f U)).isIso_fst_of_isIso

end restrict

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### Domination maps are birational -/

section birational

variable {𝔠 𝔠' : FlagIdeal X} {c c' : ℤ}

/-- **A domination map of blow-up models is an isomorphism over a nonempty open set** (both
blow-downs are isomorphisms off the central fibre). -/
theorem exists_isIso_restrict_of_comp_eq (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') :
    ∃ V : (flagModel p 𝔠 c).Opens, Nonempty V ∧ IsIso (g ∣_ V) := by
  let := productLine_isIntegral_of_isProjective p
  let W : (productLine p).Opens := (flagSheaf p 𝔠 c).support.compl ⊓
    (flagSheaf p 𝔠' c').support.compl
  have hgen : ∀ (𝔞 : FlagIdeal X) (b : ℤ), genericPoint (productLine p) ∈
      ((flagSheaf p 𝔞 b).support.compl : (productLine p).Opens) := by
    intro 𝔞 b
    by_contra hη
    apply support_flagSheaf_ne_top p 𝔞 b
    rw [eq_top_iff]
    intro z _
    by_contra hz
    exact hη (((genericPoint_spec (productLine p)).mem_open_set_iff
      (flagSheaf p 𝔞 b).support.compl.isOpen).mpr ⟨z, trivial, hz⟩)
  have hW : genericPoint (productLine p) ∈ W := ⟨hgen 𝔠 c, hgen 𝔠' c'⟩
  have : IsIso (flagModelπ p 𝔠 c ∣_ (flagSheaf p 𝔠 c).support.compl) :=
    flagModelπ_isIso_restrict p 𝔠 c
  have : IsIso (flagModelπ p 𝔠' c' ∣_ (flagSheaf p 𝔠' c').support.compl) :=
    flagModelπ_isIso_restrict p 𝔠' c'
  have h1 : IsIso (flagModelπ p 𝔠 c ∣_ W) := isIso_morphismRestrict_of_le _ inf_le_left
  have h2 : IsIso ((g ≫ flagModelπ p 𝔠 c) ∣_ W) := by
    rw [hg]
    exact isIso_morphismRestrict_of_le _ inf_le_right
  rw [morphismRestrict_comp] at h2
  refine ⟨flagModelπ p 𝔠 c ⁻¹ᵁ W, ⟨⟨genericPoint (flagModel p 𝔠 c), ?_⟩⟩,
    IsIso.of_isIso_comp_right _ (flagModelπ p 𝔠 c ∣_ W)⟩
  change flagModelπ p 𝔠 c (genericPoint (flagModel p 𝔠 c)) ∈ W
  rw [(flagModelπ_genericPoint p 𝔠 c).1]
  exact hW

omit [IsProjective p] [IsIntegral X] in
theorem comp_flagModelStructure (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') :
    g ≫ flagModelStructure p 𝔠 c = flagModelStructure p 𝔠' c' := by
  rw [flagModelStructure, ← Category.assoc, hg]

/-- `interFormQ` only depends on the structure morphism up to equality. -/
theorem interFormQ_congr {Y : Scheme.{0}} [CompactSpace Y] [Y.IsSeparated]
    {q q' : Y ⟶ Spec (.of ℂ)} [IsProjective q] [IsProjective q'] (h : q = q') (d : ℕ)
    (hd : topologicalKrullDim Y ≤ d) (F : Y.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    interFormQ q d hd F = interFormQ q' d hd F := by
  subst h
  rfl

/-- **Intersection numbers are invariant under domination maps** (BJ-PROJ's birational
invariance). -/
theorem interFormQ_pullback_dominate (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (d : ℕ)
    (hd : topologicalKrullDim (flagModel p 𝔠 c) ≤ d)
    (hd' : topologicalKrullDim (flagModel p 𝔠' c') ≤ d) (s : Multiset (PicQ (flagModel p 𝔠 c))) :
    interFormQ (flagModelStructure p 𝔠' c') d hd' (Scheme.Modules.unitObj _)
        (s.map (picPullbackQ g)) =
      interFormQ (flagModelStructure p 𝔠 c) d hd (Scheme.Modules.unitObj _) s := by
  obtain ⟨V, hV, hiso⟩ := exists_isIso_restrict_of_comp_eq g hg
  have hgp := comp_flagModelStructure g hg
  have : IsProjective (g ≫ flagModelStructure p 𝔠 c) := by rw [hgp]; infer_instance
  rw [← interFormQ_congr hgp]
  exact BJProj.interFormQ_pullback_eq_of_isIso_restrict (flagModelStructure p 𝔠 c) g d hd hd' V s

end birational

/-! ### Flag data and their divisors -/

variable (p) in
/-- **A flag datum on the model `(𝔠, c)`**: a flag ideal `𝔞` with a weight bound `b` such that
`(t^b 𝔞) · 𝒪` is invertible on the model; it is the vertical Cartier divisor `E_{(𝔞, b)}` with
`φ_{E} = b - φ_𝔞` ([BJ22, §2.1]). -/
structure FlagDatum (𝔠 : FlagIdeal X) (c : ℤ) where
  /-- The flag ideal. -/
  ideal : FlagIdeal X
  /-- The weight bound. -/
  bound : ℤ
  isWeightBound : IsWeightBound ideal bound
  isInvertible : ((flagSheaf p ideal bound).comap (flagModelπ p 𝔠 c)).IsInvertible

namespace FlagDatum

variable {𝔠 : FlagIdeal X} {c : ℤ}

/-- The vertical Cartier divisor `E_{(𝔞, b)} = (t^b 𝔞) · 𝒪` of a flag datum. -/
def vert (e : FlagDatum p 𝔠 c) : VertCartier p 𝔠 c where
  ideal := (flagSheaf p e.ideal e.bound).comap (flagModelπ p 𝔠 c)
  isInvertible := e.isInvertible
  support_subset := support_comap_flagSheaf_subset e.ideal e.bound

omit [IsIntegral X] in
/-- `φ_{E_{(𝔞, b)}} = b - φ_𝔞`. -/
theorem fn_vert (e : FlagDatum p 𝔠 c) (v : BerkovichPoint p) :
    e.vert.fn v = e.bound - e.ideal.phi v := by
  have := phi_eq_sub_idealVal_gaussModelPoint_of_model v 𝔠 c e.ideal e.isWeightBound
  simp only [VertCartier.fn, vert]
  linarith

omit [IsIntegral X] in
theorem fn_vert_nonneg (e : FlagDatum p 𝔠 c) (v : BerkovichPoint p) : 0 ≤ e.vert.fn v := by
  rw [fn_vert]
  exact sub_nonneg.mpr (e.ideal.phi_le v e.isWeightBound)

variable {𝔠' : FlagIdeal X} {c' : ℤ}

/-- Pull-back of a flag datum along a domination map. -/
def pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (e : FlagDatum p 𝔠 c) :
    FlagDatum p 𝔠' c' where
  ideal := e.ideal
  bound := e.bound
  isWeightBound := e.isWeightBound
  isInvertible := by
    let := isDominant_of_comp_eq g hg
    have h := e.isInvertible.comap_of_dominant_integral g
    rwa [← Scheme.IdealSheafData.comap_comp, hg] at h

theorem pullback_vert_ideal (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (e : FlagDatum p 𝔠 c) :
    (e.pullback g hg).vert.ideal = (e.vert.pullback g hg).ideal := by
  simp only [vert, pullback, VertCartier.pullback]
  rw [← Scheme.IdealSheafData.comap_comp, hg]

end FlagDatum

omit [IsProjective p] [IsIntegral X] in
theorem VertCartier.picQ_line_congr {𝔠 : FlagIdeal X} {c : ℤ} {E E' : VertCartier p 𝔠 c}
    (h : E.ideal = E'.ideal) : picQ E.line = picQ E'.line := by
  cases E
  cases E'
  simp only at h
  subst h
  rfl

variable (p) in
/-- **Formal `ℚ`-combinations of flag data** on the model `(𝔠, c)`. -/
abbrev FDiv (𝔠 : FlagIdeal X) (c : ℤ) := FlagDatum p 𝔠 c →₀ ℚ

namespace FDiv

variable {𝔠 : FlagIdeal X} {c : ℤ}

/-- The vertical `ℚ`-Cartier divisor of a combination of flag data. -/
def toVDiv : FDiv p 𝔠 c →ₗ[ℚ] VDiv p 𝔠 c := Finsupp.lmapDomain ℚ ℚ FlagDatum.vert

/-- **The PL function `φ_D`** of a combination of flag data. -/
def fn : FDiv p 𝔠 c →ₗ[ℚ] (BerkovichPoint p → ℝ) := VDiv.fn ∘ₗ toVDiv

/-- **The class `[𝒪(D)] ∈ Pic(𝒳)_ℚ`** of a combination of flag data. -/
def cls : FDiv p 𝔠 c →ₗ[ℚ] PicQ (flagModel p 𝔠 c) := VDiv.cls ∘ₗ toVDiv

/-- The class pulled back to the normalized model. -/
def ncls : FDiv p 𝔠 c →ₗ[ℚ] PicQ (normModel p 𝔠 c) :=
  picPullbackQ (normModelν p 𝔠 c) ∘ₗ cls

omit [IsIntegral X] in
@[simp] theorem fn_single (e : FlagDatum p 𝔠 c) (q : ℚ) :
    fn (Finsupp.single e q) = q • e.vert.fn := by
  simp [fn, toVDiv]

omit [IsProjective p] [IsIntegral X] in
@[simp] theorem cls_single (e : FlagDatum p 𝔠 c) (q : ℚ) :
    cls (Finsupp.single e q) = q • -picQ e.vert.line := by
  simp [cls, toVDiv]

omit [IsIntegral X] in
theorem fn_apply (D : FDiv p 𝔠 c) (v : BerkovichPoint p) :
    fn D v = ∑ e ∈ D.support, (D e : ℝ) * e.vert.fn v := by
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [fn_single, Pi.smul_apply, Rat.smul_def]

variable {𝔠' : FlagIdeal X} {c' : ℤ}

/-- Pull-back of combinations of flag data along a domination map. -/
def pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') : FDiv p 𝔠 c →ₗ[ℚ] FDiv p 𝔠' c' :=
  Finsupp.lmapDomain ℚ ℚ (FlagDatum.pullback g hg)

theorem fn_pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (D : FDiv p 𝔠 c) :
    fn (pullback g hg D) = fn D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, hD, hD', map_add]
  | single e q =>
    rw [pullback, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, fn_single, fn_single]
    congr 1
    funext v
    rw [FlagDatum.fn_vert, FlagDatum.fn_vert]
    rfl

theorem cls_pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (D : FDiv p 𝔠 c) :
    cls (pullback g hg D) = picPullbackQ g (cls D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, hD, hD', map_add, map_add]
  | single e q =>
    rw [pullback, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, cls_single, cls_single,
      map_smul, map_neg, VertCartier.picQ_line_congr (FlagDatum.pullback_vert_ideal g hg e),
      VertCartier.picQ_line_pullback]

end FDiv

/-! ### Clearing denominators -/

section denominators

variable {ι : Type*}

/-- Every finitely supported `ℚ`-valued function has a positive integer multiple with integer
values. -/
theorem exists_nsmul_eq_intCast (D : ι →₀ ℚ) :
    ∃ (N : ℕ) (m : ι →₀ ℤ), 0 < N ∧ (N : ℚ) • D = m.mapRange (Int.cast) Int.cast_zero := by
  classical
  induction D using Finsupp.induction with
  | zero => exact ⟨1, 0, one_pos, by simp⟩
  | single_add e q D _ _ ih =>
    obtain ⟨N, m, hN, hm⟩ := ih
    refine ⟨q.den * N, (N : ℤ) • Finsupp.single e q.num + (q.den : ℤ) • m,
      Nat.mul_pos q.den_pos hN, ?_⟩
    ext i
    have hq : (q.den : ℚ) * q = q.num := Rat.den_mul_eq_num q
    have hmi : (N : ℚ) * D i = m i := by
      have := congrArg (fun F : ι →₀ ℚ => F i) hm
      simpa only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply] using this
    simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, Finsupp.mapRange_apply,
      Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Finsupp.single_apply]
    rw [← hmi]
    by_cases hi : e = i
    · subst hi
      rw [if_pos rfl, if_pos rfl, ← hq]
      ring
    · rw [if_neg hi, if_neg hi, Int.cast_zero]
      ring

/-- The `ℚ`-valued function of an `ℕ`-valued one. -/
abbrev natToRat (n : ι →₀ ℕ) : ι →₀ ℚ := n.mapRange (Nat.cast) Nat.cast_zero

/-- An integer-valued function is a difference of two `ℕ`-valued ones. -/
theorem intCast_eq_sub (m : ι →₀ ℤ) :
    m.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero =
      natToRat (m.mapRange Int.toNat (by simp)) - natToRat ((-m).mapRange Int.toNat (by simp)) := by
  ext i
  simp only [Finsupp.mapRange_apply, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_neg,
    Pi.neg_apply]
  have h := congrArg (Int.cast : ℤ → ℚ) (Int.toNat_sub_toNat_neg (m i))
  push_cast at h
  linarith

end denominators

/-! ### The ideals of `ℕ`-combinations of flag data on the normalized model -/

section normal

variable {𝔠 : FlagIdeal X} {c : ℤ}

/-- The ideal sheaf `∏_e ((t^{b_e} 𝔞_e) · 𝒪_{𝒳̃})^{n_e}` of an `ℕ`-combination of flag data on the
normalized model. -/
def idealN (n : FlagDatum p 𝔠 c →₀ ℕ) : (normModel p 𝔠 c).IdealSheafData :=
  ∏ e ∈ n.support, (e.vert.ideal.comap (normModelν p 𝔠 c)) ^ n e

theorem vert_comap_isInvertible (e : FlagDatum p 𝔠 c) :
    (e.vert.ideal.comap (normModelν p 𝔠 c)).IsInvertible :=
  isInvertible_comap_normModelν p 𝔠 c e.isInvertible

theorem idealN_isInvertible (n : FlagDatum p 𝔠 c →₀ ℕ) : (idealN n).IsInvertible :=
  isInvertible_prod_pow _ _ vert_comap_isInvertible _

theorem vert_comap_eq (e : FlagDatum p 𝔠 c) :
    e.vert.ideal.comap (normModelν p 𝔠 c) =
      (flagSheaf p e.ideal e.bound).comap (normModelπ p 𝔠 c) := by
  rw [normModelπ, Scheme.IdealSheafData.comap_comp]
  rfl

/-- The class of a pulled-back vertical Cartier divisor along the normalization. -/
theorem picPullbackQ_normModelν_line (E : VertCartier p 𝔠 c) :
    picPullbackQ (normModelν p 𝔠 c) (picQ E.line) =
      picQ ⟨(E.ideal.comap (normModelν p 𝔠 c)).toModules,
        (isInvertible_comap_normModelν p 𝔠 c E.isInvertible).isInvertibleModule_toModules⟩ := by
  have : IsDominant (normModelν p 𝔠 c) := ⟨(normModelν_surjective p 𝔠 c).denseRange⟩
  have hiso : IsIso (E.ideal.toModulesComapPullbackMap (normModelν p 𝔠 c)) :=
    E.isInvertible.toModulesComapPullbackMap_isIso_of_dominant_integral (normModelν p 𝔠 c)
  rw [picPullbackQ_picQ]
  exact picQ_eq_of_iso _ _ (asIso (E.ideal.toModulesComapPullbackMap (normModelν p 𝔠 c)))

/-- **The class of an `ℕ`-combination**: `ν^*[𝒪(D)] = -[J_D]`. -/
theorem ncls_natToRat (n : FlagDatum p 𝔠 c →₀ ℕ) :
    FDiv.ncls (natToRat n) =
      -picQ ⟨(idealN n).toModules, (idealN_isInvertible n).isInvertibleModule_toModules⟩ := by
  have hsum : natToRat n = ∑ e ∈ n.support, Finsupp.single e (n e : ℚ) := by
    conv_lhs => rw [← Finsupp.sum_single (natToRat n)]
    rw [Finsupp.sum, Finsupp.support_mapRange_of_injective (by simp) _ Nat.cast_injective]
    rfl
  have hprod := lineCls_toModules_prod n.support
    (fun e => e.vert.ideal.comap (normModelν p 𝔠 c)) vert_comap_isInvertible n
  have e1 : picQ ⟨(idealN n).toModules, (idealN_isInvertible n).isInvertibleModule_toModules⟩ =
      (1 : ℚ) ⊗ₜ[ℤ] lineCls ⟨(∏ e ∈ n.support,
        (e.vert.ideal.comap (normModelν p 𝔠 c)) ^ n e).toModules,
        (isInvertible_prod_pow _ _ vert_comap_isInvertible _).isInvertibleModule_toModules⟩ := rfl
  rw [e1, hprod, TensorProduct.tmul_sum, ← Finset.sum_neg_distrib, hsum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [FDiv.ncls, LinearMap.comp_apply, FDiv.cls_single, map_smul, map_neg,
    picPullbackQ_normModelν_line, picQ,
    show (1 : ℚ) ⊗ₜ[ℤ] (n e • lineCls ⟨(e.vert.ideal.comap (normModelν p 𝔠 c)).toModules,
        (vert_comap_isInvertible e).isInvertibleModule_toModules⟩) =
      n e • ((1 : ℚ) ⊗ₜ[ℤ] lineCls ⟨(e.vert.ideal.comap (normModelν p 𝔠 c)).toModules,
        (vert_comap_isInvertible e).isInvertibleModule_toModules⟩) from
      map_nsmul (TensorProduct.mk ℤ ℚ _ (1 : ℚ)) (n e) _,
    smul_neg, Nat.cast_smul_eq_nsmul ℚ]

omit [IsIntegral X] in
/-- The function of an `ℕ`-combination. -/
theorem fn_natToRat (n : FlagDatum p 𝔠 c →₀ ℕ) (v : BerkovichPoint p) :
    FDiv.fn (natToRat n) v = ∑ e ∈ n.support, (n e : ℝ) * (e.bound - e.ideal.phi v) := by
  rw [FDiv.fn_apply, Finsupp.support_mapRange_of_injective (by simp) _ Nat.cast_injective]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [FlagDatum.fn_vert, Finsupp.mapRange_apply]
  push_cast
  rfl

omit [IsIntegral X] in
theorem fn_natToRat_nonneg (n : FlagDatum p 𝔠 c →₀ ℕ) (v : BerkovichPoint p) :
    0 ≤ FDiv.fn (natToRat n) v := by
  rw [fn_natToRat]
  exact Finset.sum_nonneg fun e _ =>
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (e.ideal.phi_le v e.isWeightBound))

/-- **Divisorial values of `ℕ`-combinations**: at a point `z` of the normalized model with a DVR
as local ring, `ord_z(J_D) = c_z φ_D(v_z)`. -/
theorem exists_idealVal_ordPoint_idealN
    (h0 : ((centralIdeal p).comap (flagModelπ p 𝔠 c)).IsInvertible) (z : normModel p 𝔠 c)
    (hz : IsDiscreteValuationRing ((normModel p 𝔠 c).presheaf.stalk z)) :
    ∃ (C : ℝ≥0∞) (v : BerkovichPoint p), C ≠ ⊤ ∧ ∀ n : FlagDatum p 𝔠 c →₀ ℕ,
      (ordPoint (normModelStructure p 𝔠 c) z).idealVal (idealN n) =
        C * ENNReal.ofReal (FDiv.fn (natToRat n) v) := by
  classical
  obtain ⟨C, v, hC, hval⟩ := exists_idealVal_ordPoint_flagSheaf h0 z hz
  refine ⟨C, v, hC, fun n => ?_⟩
  rw [idealN, fn_natToRat]
  have hnn : ∀ e ∈ n.support, 0 ≤ (n e : ℝ) * (e.bound - e.ideal.phi v) := fun e _ =>
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (e.ideal.phi_le v e.isWeightBound))
  rw [ENNReal.ofReal_sum_of_nonneg hnn, Finset.mul_sum]
  generalize n.support = s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, Scheme.IdealSheafData.one_eq_top,
      BerkovichPoint.idealVal_top]
  | insert e s he ih =>
    rw [Finset.prod_insert he, Finset.sum_insert he, BerkovichPoint.idealVal_mul, ih,
      idealVal_pow, vert_comap_eq, hval e.ideal e.bound e.isWeightBound,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    ring

end normal

/-! ### Well-definedness and positivity -/

section main

variable {𝔠 : FlagIdeal X} {c : ℤ}

theorem idealN_le_of_fn_le (h0 : ((centralIdeal p).comap (flagModelπ p 𝔠 c)).IsInvertible)
    (n n' : FlagDatum p 𝔠 c →₀ ℕ) (h : FDiv.fn (natToRat n') ≤ FDiv.fn (natToRat n)) :
    idealN n ≤ idealN n' := by
  apply idealSheaf_le_of_forall_idealVal (normModelStructure p 𝔠 c)
    (normModel_stalk_isIntegrallyClosed p 𝔠 c) (idealN_isInvertible n')
  intro z hz
  obtain ⟨C, v, -, hval⟩ := exists_idealVal_ordPoint_idealN h0 z hz
  rw [hval, hval]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (h v)) C

theorem picQ_toModules_congr {Y : Scheme.{0}} {I J : Y.IdealSheafData} (h : I = J)
    (hI : Scheme.Modules.IsInvertible I.toModules) (hJ : Scheme.Modules.IsInvertible J.toModules) :
    picQ ⟨I.toModules, hI⟩ = picQ ⟨J.toModules, hJ⟩ := by
  subst h
  rfl

/-- **Well-definedness** ([BJ22, §2.2]): on a model on which the central fibre is Cartier, a
combination of flag data with `φ_D = 0` has `ν^*[𝒪(D)] = 0` on the normalized model. -/
theorem FDiv.ncls_eq_zero (h0 : ((centralIdeal p).comap (flagModelπ p 𝔠 c)).IsInvertible)
    (D : FDiv p 𝔠 c) (hD : FDiv.fn D = 0) : FDiv.ncls D = 0 := by
  obtain ⟨N, m, hN, hm⟩ := exists_nsmul_eq_intCast D
  rw [intCast_eq_sub] at hm
  set n := m.mapRange Int.toNat (by simp)
  set n' := (-m).mapRange Int.toNat (by simp)
  have hfn : FDiv.fn (natToRat n) = FDiv.fn (natToRat n') := by
    have := congrArg FDiv.fn hm
    rw [map_smul, hD, smul_zero, map_sub] at this
    exact (sub_eq_zero.mp this.symm)
  have heq : idealN n = idealN n' :=
    le_antisymm (idealN_le_of_fn_le h0 n n' hfn.ge) (idealN_le_of_fn_le h0 n' n hfn.le)
  have hcls : FDiv.ncls ((N : ℚ) • D) = 0 := by
    rw [hm, map_sub, ncls_natToRat, ncls_natToRat, sub_eq_zero, picQ_toModules_congr heq]
  rw [map_smul] at hcls
  exact (smul_eq_zero.mp hcls).resolve_left (by exact_mod_cast hN.ne')

/-- **Two combinations of flag data with the same PL function have the same class** on the
normalized model. -/
theorem FDiv.ncls_eq_of_fn_eq (h0 : ((centralIdeal p).comap (flagModelπ p 𝔠 c)).IsInvertible)
    {D D' : FDiv p 𝔠 c} (h : FDiv.fn D = FDiv.fn D') : FDiv.ncls D = FDiv.ncls D' := by
  have := FDiv.ncls_eq_zero h0 (D - D') (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at this

theorem support_idealN_subset (n : FlagDatum p 𝔠 c →₀ ℕ) :
    ((idealN n).support : Set (normModel p 𝔠 c)) ⊆
      normModelν p 𝔠 c ⁻¹' centralFibre p 𝔠 c := by
  intro x hx
  by_contra hxc
  have htop : ∀ e : FlagDatum p 𝔠 c, (e.vert.ideal.comap (normModelν p 𝔠 c)).stalkIdeal x = ⊤ := by
    intro e
    by_contra hne
    apply hxc
    have hmem : x ∈ (e.vert.ideal.comap (normModelν p 𝔠 c)).support := by
      rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal]
      exact IsLocalRing.le_maximalIdeal hne
    rw [Scheme.IdealSheafData.support_comap] at hmem
    exact e.vert.support_subset hmem
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal, idealN,
    Scheme.IdealSheafData.stalkIdeal_finset_prod] at hx
  have : ∏ e ∈ n.support, ((e.vert.ideal.comap (normModelν p 𝔠 c)) ^ n e).stalkIdeal x = 1 :=
    Finset.prod_eq_one fun e _ => by
      rw [Scheme.IdealSheafData.stalkIdeal_pow, htop e, Ideal.top_pow, Ideal.one_eq_top]
  rw [this, Ideal.one_eq_top] at hx
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hx)

/-- **Positivity** ([BJ22, `lem:enmono`]): on a model on which the central fibre is Cartier, if a
combination of flag data has `φ_D ≥ 0`, a positive multiple of `ν^*[𝒪(D)]` is `-[K] = [𝒪(K)]`
for an invertible ideal sheaf `K` of the normalized model supported in the central fibre. -/
theorem FDiv.exists_effective (h0 : ((centralIdeal p).comap (flagModelπ p 𝔠 c)).IsInvertible)
    (D : FDiv p 𝔠 c) (hD : 0 ≤ FDiv.fn D) :
    ∃ (N : ℕ) (K : (normModel p 𝔠 c).IdealSheafData) (hK : K.IsInvertible), 0 < N ∧
      (K.support : Set (normModel p 𝔠 c)) ⊆ normModelν p 𝔠 c ⁻¹' centralFibre p 𝔠 c ∧
      (N : ℚ) • FDiv.ncls D = -picQ ⟨K.toModules, hK.isInvertibleModule_toModules⟩ := by
  obtain ⟨N, m, hN, hm⟩ := exists_nsmul_eq_intCast D
  rw [intCast_eq_sub] at hm
  set n := m.mapRange Int.toNat (by simp)
  set n' := (-m).mapRange Int.toNat (by simp)
  have hfn : FDiv.fn (natToRat n') ≤ FDiv.fn (natToRat n) := by
    intro v
    have h1 := congrFun (congrArg FDiv.fn hm) v
    rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, Rat.smul_def] at h1
    have h2 := hD v
    have h3 : (0 : ℝ) ≤ (N : ℝ) * FDiv.fn D v := mul_nonneg (Nat.cast_nonneg _) h2
    simp only [Pi.zero_apply] at h2
    rw [Rat.cast_natCast] at h1
    linarith
  have hle := idealN_le_of_fn_le h0 n n' hfn
  have hJ := idealN_isInvertible n
  have hJ' := idealN_isInvertible n'
  refine ⟨N, (idealN n).colon (idealN n'), colon_isInvertible hJ hJ' hle, hN,
    (support_colon_subset hJ hJ' hle).trans (support_idealN_subset n), ?_⟩
  have hmul := eq_mul_colon hJ hJ' hle
  have hcls : FDiv.ncls ((N : ℚ) • D) =
      -picQ ⟨(idealN n).toModules, hJ.isInvertibleModule_toModules⟩ +
        picQ ⟨(idealN n').toModules, hJ'.isInvertibleModule_toModules⟩ := by
    rw [hm, map_sub, ncls_natToRat, ncls_natToRat, sub_neg_eq_add]
  rw [← map_smul, hcls]
  have key : picQ ⟨(idealN n).toModules, hJ.isInvertibleModule_toModules⟩ =
      picQ ⟨(idealN n').toModules, hJ'.isInvertibleModule_toModules⟩ +
        picQ ⟨((idealN n).colon (idealN n')).toModules,
          (colon_isInvertible hJ hJ' hle).isInvertibleModule_toModules⟩ := by
    have e1 : picQ ⟨(idealN n).toModules, hJ.isInvertibleModule_toModules⟩ =
        picQ ⟨((idealN n') * (idealN n).colon (idealN n')).toModules,
          (hJ'.mul (colon_isInvertible hJ hJ' hle)).isInvertibleModule_toModules⟩ :=
      picQ_toModules_congr hmul _ _
    rw [e1, picQ, picQ, picQ, lineCls_toModules_mul hJ' (colon_isInvertible hJ hJ' hle),
      TensorProduct.tmul_add]
  rw [key]
  abel

end main

end SGPT.NAPotential.BJ
