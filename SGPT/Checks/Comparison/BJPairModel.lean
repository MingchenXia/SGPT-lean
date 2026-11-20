import SGPT.Checks.Comparison.BJPairClass
import SGPT.Checks.Comparison.BJHodgeInequality
import SGPT.Checks.Comparison.BJModel3Chart

/-!
# The energy pairing on PL functions (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), Definition `defi:intpairing` (the energy pairing
`(θ₀, φ₀) ⋯ (θ_n, φ_n)` is the intersection number `(θ₀ + D₀) ⋯ (θ_n + D_n)` on a test
configuration on which `φᵢ = φ_{Dᵢ}`), Proposition `prop:intpairing` and Lemma `lem:enmono`.
Towards `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

Fix `X` integral projective over `ℂ` with `dim X ≤ n` and a class `ω ∈ Pic(X)_ℚ`. For a *good* model
`(𝔠, c)` (a blow-up model of `X × ℙ¹` with Cartier central fibre, lane BJ-MODEL3) and a function
`φ` which is `φ_D` for a combination `D` of flag data on it (`IsFlagRep`), the class
`s π^*ω + [𝒪(D)]` pulled back to the normalized model only depends on `(s, φ)`
(`FDiv.ncls_eq_of_fn_eq`, the well-definedness of lane BJ-PAIR). Hence:

* `modelValue n hX ω 𝔠 c s`: the intersection number `∏_{(s, φ) ∈ s} (s π^*ω + D_φ)` on the
  normalized model of `(𝔠, c)`; it equals the intersection number on the blow-up model for any
  choice of representatives (`interFormQ_flag_eq_modelValue`) and is invariant under domination
  maps (`modelValue_dominate`, BJ-PROJ's birational invariance);
* `flagPair n hX ω s`: its common value on all good models representing `s` (`flagPair_eq`), defined
  for every multiset of pairs of PL functions (`exists_goodModel_flagRep`); it is linear in each
  entry (`flagPair_cons_add`, `flagPair_cons_smul`), vanishes on `(ω, 0)^{n+1}` (`flagPair_zero`,
  [BJ22, `prop:intpairing` (iii)]) and is nonnegative on `(0, f) ⋅ (ω, u₁) ⋯ (ω, u_n)` for `f ≥ 0`
  and `ω`-psh `uᵢ` (`flagPair_nonneg`, [BJ22, `lem:enmono`]);
* `IsFlagPsh ω φ`: `φ = φ_D` on a good model with `π^*ω + [𝒪(D)]` relatively nef ([BJ22, §3.1]),
  for combinations `D` of flag data; it implies `IsOmegaPshPL` and is stable
  under adding rational constants and under midpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge
open FlagIdealBound

/-! ### Multilinear forms on cones -/

section cone

variable {V I : Type*} [AddCommGroup V] [Module ℚ V]

/-- **Expansion over a cone**: if a `ℚ`-multilinear symmetric form is nonnegative on
`t + {g(i₁), …, g(i_m)}` for all generators, it is nonnegative on `t + s` for every multiset `s` of
`m` elements of the convex cone spanned by the generators. -/
theorem MultisetForm.nonneg_of_mem_hull (Φ : MultisetForm ℚ V) (gen : I → V) :
    ∀ (s : Multiset V) (t : Multiset V),
      (∀ θ ∈ s, θ ∈ PointedCone.hull ℚ (Set.range gen)) →
      (∀ l : List I, l.length = Multiset.card s → 0 ≤ Φ (t + (l.map gen : Multiset V))) →
      0 ≤ Φ (t + s) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro t _ h
    simpa using h [] rfl
  | cons θ s ih =>
    intro t hs h
    have hθ := hs θ (Multiset.mem_cons_self θ s)
    have hs' : ∀ θ' ∈ s, θ' ∈ PointedCone.hull ℚ (Set.range gen) := fun θ' h' =>
      hs θ' (Multiset.mem_cons_of_mem h')
    have h' : ∀ l : List I, l.length = Multiset.card s + 1 →
        0 ≤ Φ (t + (l.map gen : Multiset V)) := fun l hl => h l (by simpa using hl)
    clear h hs
    rw [Multiset.add_cons]
    induction hθ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← Multiset.add_cons, ← Multiset.singleton_add, ← add_assoc]
      refine ih _ hs' fun l hl => ?_
      have := h' (i :: l) (by simp [hl])
      simpa [add_assoc] using this
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Φ.map_add]
      exact add_nonneg hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : ℚ) • x from rfl, Φ.map_smul]
      exact mul_nonneg a.2 hx

end cone

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### Good models and representatives -/

section rep

variable {𝔠 : FlagIdeal X} {c : ℤ}

omit [IsProjective p] [IsIntegral X] in
/-- On a good model the ideal of the central fibre is invertible. -/
theorem IsGoodModel.central_isInvertible (h : IsGoodModel p 𝔠 c) :
    ((centralIdeal p).comap (flagModelπ p 𝔠 c)).IsInvertible := by
  have := h.2.1
  rwa [flagSheaf_monomial_zero_one] at this

variable (p) in
/-- `φ` is the function of a combination of flag data on the model `(𝔠, c)`. -/
def IsFlagRep (𝔠 : FlagIdeal X) (c : ℤ) (φ : BerkovichPoint p → ℝ) : Prop :=
  ∃ D : FDiv p 𝔠 c, FDiv.fn D = φ

open Classical in
/-- A chosen representative. -/
def flagRep (𝔠 : FlagIdeal X) (c : ℤ) (φ : BerkovichPoint p → ℝ) : FDiv p 𝔠 c :=
  if h : IsFlagRep p 𝔠 c φ then h.choose else 0

omit [IsIntegral X] in
theorem fn_flagRep {φ : BerkovichPoint p → ℝ} (h : IsFlagRep p 𝔠 c φ) :
    FDiv.fn (flagRep 𝔠 c φ) = φ := by
  rw [flagRep, dif_pos h]
  exact h.choose_spec

omit [IsIntegral X] in
theorem IsFlagRep.add {φ ψ : BerkovichPoint p → ℝ} (hφ : IsFlagRep p 𝔠 c φ)
    (hψ : IsFlagRep p 𝔠 c ψ) : IsFlagRep p 𝔠 c (φ + ψ) := by
  obtain ⟨D, rfl⟩ := hφ
  obtain ⟨D', rfl⟩ := hψ
  exact ⟨D + D', map_add _ _ _⟩

omit [IsIntegral X] in
theorem IsFlagRep.smul {φ : BerkovichPoint p → ℝ} (hφ : IsFlagRep p 𝔠 c φ) (q : ℚ) :
    IsFlagRep p 𝔠 c (q • φ) := by
  obtain ⟨D, rfl⟩ := hφ
  exact ⟨q • D, map_smul _ _ _⟩

omit [IsIntegral X] in
theorem IsFlagRep.zero : IsFlagRep p 𝔠 c 0 := ⟨0, map_zero _⟩

variable {𝔠' : FlagIdeal X} {c' : ℤ}

theorem IsFlagRep.pullback (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') {φ : BerkovichPoint p → ℝ}
    (h : IsFlagRep p 𝔠 c φ) : IsFlagRep p 𝔠' c' φ := by
  obtain ⟨D, rfl⟩ := h
  exact ⟨FDiv.pullback g hg D, FDiv.fn_pullback g hg D⟩

omit [IsProjective p] [IsIntegral X] in
/-- Some good model exists. -/
theorem exists_isGoodModel : ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c := by
  obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound (FlagIdeal.monomial X 0)
  exact ⟨_, _, (isGoodModel_mul_monomial p hb).1⟩

/-- **Common good models**: for a property of functions on models which is stable under
domination maps, finitely many functions each having a good model with the property have a common
one. -/
theorem exists_common_goodModel
    (P : FlagIdeal X → ℤ → (BerkovichPoint p → ℝ) → Prop)
    (hP : ∀ (𝔠 𝔠' : FlagIdeal X) (c c' : ℤ) (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c),
      g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c' → ∀ φ, P 𝔠 c φ → P 𝔠' c' φ)
    (s : Multiset (BerkovichPoint p → ℝ))
    (hs : ∀ φ ∈ s, ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c ∧ P 𝔠 c φ) :
    ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c ∧ ∀ φ ∈ s, P 𝔠 c φ := by
  induction s using Multiset.induction_on with
  | empty =>
    obtain ⟨𝔠, c, h⟩ := exists_isGoodModel (p := p)
    exact ⟨𝔠, c, h, by simp⟩
  | cons φ s ih =>
    obtain ⟨𝔠₁, c₁, h₁, hP₁⟩ := ih fun ψ hψ => hs ψ (Multiset.mem_cons_of_mem hψ)
    obtain ⟨𝔠₂, c₂, h₂, hP₂⟩ := hs φ (Multiset.mem_cons_self φ s)
    obtain ⟨g₁, g₂, hg₁, hg₂⟩ := exists_common_dominating p h₁.1 h₂.1
    refine ⟨𝔠₁ * 𝔠₂, c₁ + c₂, ⟨h₁.1.mul h₂.1, h₁.2.of_comp g₁ hg₁⟩, fun ψ hψ => ?_⟩
    rcases Multiset.mem_cons.mp hψ with rfl | hψ
    · exact hP _ _ _ _ g₂ hg₂ _ hP₂
    · exact hP _ _ _ _ g₁ hg₁ _ (hP₁ ψ hψ)

/-- The flag datum of a dominated pair `(𝔞, b)`. -/
def FlagDatum.ofDominates {𝔞 : FlagIdeal X} {b : ℤ} (h : Dominates p 𝔠 c 𝔞 b)
    (hb : IsWeightBound 𝔞 b) : FlagDatum p 𝔠 c :=
  ⟨𝔞, b, hb, h.1⟩

/-- The central fibre `𝒳₀` as a flag datum. -/
def centralDatum (h : IsGoodModel p 𝔠 c) : FlagDatum p 𝔠 c :=
  FlagDatum.ofDominates h.2 ((isWeightBound_monomial 0).mono (by norm_num))

omit [IsIntegral X] in
theorem fn_centralDatum (h : IsGoodModel p 𝔠 c) :
    (centralDatum h).vert.fn = fun _ => 1 := by
  funext v
  rw [FlagDatum.fn_vert]
  simp [centralDatum, FlagDatum.ofDominates, FlagIdeal.phi_monomial]

theorem picQ_centralDatum (h : IsGoodModel p 𝔠 c) :
    picQ (centralDatum h).vert.line = picQ (centralLine p 𝔠 c) := by
  exact (VertCartier.picQ_line_congr rfl).trans (picQ_centralVert_line p h.2)

/-- **Every PL function is represented by flag data on a good model** ([BJ22, `thm:VCarPL`]). -/
theorem exists_goodModel_flagRep {φ : BerkovichPoint p → ℝ} (hφ : φ ∈ plSubmodule p) :
    ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c ∧ IsFlagRep p 𝔠 c φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨𝔞, rfl⟩ := hx
    obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound 𝔞
    obtain ⟨hgood, hdom⟩ := isGoodModel_mul_monomial p hb
    refine ⟨_, _, hgood, Finsupp.single (centralDatum hgood) (b : ℚ) -
      Finsupp.single (FlagDatum.ofDominates hdom hb) 1, ?_⟩
    funext v
    rw [map_sub, FDiv.fn_single, FDiv.fn_single, fn_centralDatum, Pi.sub_apply, Pi.smul_apply,
      Pi.smul_apply, FlagDatum.fn_vert]
    simp only [FlagDatum.ofDominates, Rat.smul_def, one_smul, Rat.cast_intCast, mul_one]
    ring
  | zero =>
    obtain ⟨𝔠, c, h⟩ := exists_isGoodModel (p := p)
    exact ⟨𝔠, c, h, IsFlagRep.zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨𝔠, c, h, hx⟩ := hx
    obtain ⟨𝔠', c', h', hy⟩ := hy
    obtain ⟨g, g', hg, hg'⟩ := exists_common_dominating p h.1 h'.1
    exact ⟨_, _, ⟨h.1.mul h'.1, h.2.of_comp g hg⟩,
      (hx.pullback g hg).add (hy.pullback g' hg')⟩
  | smul q x _ hx =>
    obtain ⟨𝔠, c, h, hx⟩ := hx
    exact ⟨𝔠, c, h, hx.smul q⟩

end rep

/-! ### The value on a model -/

section value

variable (n : ℕ) (hX : topologicalKrullDim X ≤ n) (ω : PicQ X)

/-- `π^*ω` on the normalized model. -/
def normOmega (𝔠 : FlagIdeal X) (c : ℤ) : PicQ (normModel p 𝔠 c) :=
  picPullbackQ (normModelν p 𝔠 c) (omegaPullback 𝔠 c ω)

/-- The class `s π^*ω + ν^*[𝒪(D_φ)]` on the normalized model of `(𝔠, c)`. -/
def modelClass (𝔠 : FlagIdeal X) (c : ℤ) (x : ℚ × (BerkovichPoint p → ℝ)) :
    PicQ (normModel p 𝔠 c) :=
  x.1 • normOmega ω 𝔠 c + FDiv.ncls (flagRep 𝔠 c x.2)

/-- **The energy pairing on a model**: the intersection number of the classes
`s π^*ω + D_φ`, `(s, φ) ∈ s`, on the normalized model. -/
def modelValue (𝔠 : FlagIdeal X) (c : ℤ) (s : Multiset (ℚ × (BerkovichPoint p → ℝ))) : ℚ :=
  interFormQ (normModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_normModel_le p 𝔠 c n hX)
    (Scheme.Modules.unitObj _) (s.map (modelClass ω 𝔠 c))

variable {𝔠 : FlagIdeal X} {c : ℤ}

theorem modelClass_eq (hgood : IsGoodModel p 𝔠 c) (x : ℚ × (BerkovichPoint p → ℝ))
    (D : FDiv p 𝔠 c) (hD : FDiv.fn D = x.2) :
    modelClass ω 𝔠 c x = x.1 • normOmega ω 𝔠 c + FDiv.ncls D := by
  rw [modelClass, FDiv.ncls_eq_of_fn_eq hgood.central_isInvertible
    ((fn_flagRep ⟨D, hD⟩).trans hD.symm)]

/-- **The value on a model is the intersection number on the blow-up model for any choice of
representatives.** -/
theorem interFormQ_flag_eq_modelValue (hgood : IsGoodModel p 𝔠 c)
    (s : Multiset (ℚ × (BerkovichPoint p → ℝ))) (R : (BerkovichPoint p → ℝ) → FDiv p 𝔠 c)
    (hR : ∀ x ∈ s, FDiv.fn (R x.2) = x.2) :
    interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
        (Scheme.Modules.unitObj _) (s.map fun x => x.1 • omegaPullback 𝔠 c ω + FDiv.cls (R x.2)) =
      modelValue n hX ω 𝔠 c s := by
  rw [← interFormQ_normModel p 𝔠 c (n + 1), Multiset.map_map, modelValue]
  congr 1
  refine Multiset.map_congr rfl fun x hx => ?_
  rw [Function.comp_apply, map_add, map_smul, modelClass_eq ω hgood x (R x.2) (hR x hx)]
  rfl

/-- **Invariance under domination maps** (birational invariance of intersection numbers). -/
theorem modelValue_dominate {𝔠' : FlagIdeal X} {c' : ℤ} (hgood : IsGoodModel p 𝔠 c)
    (hgood' : IsGoodModel p 𝔠' c') (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c)
    (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c') (s : Multiset (ℚ × (BerkovichPoint p → ℝ)))
    (hs : ∀ x ∈ s, IsFlagRep p 𝔠 c x.2) :
    modelValue n hX ω 𝔠' c' s = modelValue n hX ω 𝔠 c s := by
  rw [← interFormQ_flag_eq_modelValue n hX ω hgood' s
      (fun φ => FDiv.pullback g hg (flagRep 𝔠 c φ))
      (fun x hx => by rw [FDiv.fn_pullback, fn_flagRep (hs x hx)]),
    ← interFormQ_flag_eq_modelValue n hX ω hgood s (flagRep 𝔠 c)
      (fun x hx => fn_flagRep (hs x hx))]
  have hmap : (s.map fun x => x.1 • omegaPullback 𝔠' c' ω +
      FDiv.cls (FDiv.pullback g hg (flagRep 𝔠 c x.2))) =
      (s.map fun x => x.1 • omegaPullback 𝔠 c ω + FDiv.cls (flagRep 𝔠 c x.2)).map
        (picPullbackQ g) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [Function.comp_apply, map_add, map_smul, FDiv.cls_pullback, omegaPullback_comp g hg]
  rw [hmap, interFormQ_pullback_dominate g hg (n + 1)]

end value

/-! ### The pairing on PL functions -/

section pair

variable (n : ℕ) (hX : topologicalKrullDim X ≤ n) (ω : PicQ X)

variable (p) in
/-- All the functions of a multiset are represented on a common good model. -/
def HasGoodRep (s : Multiset (ℚ × (BerkovichPoint p → ℝ))) : Prop :=
  ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c ∧ ∀ x ∈ s, IsFlagRep p 𝔠 c x.2

open Classical in
/-- **The energy pairing** `(s₀ ω, φ₀) ⋯ (s_n ω, φ_n)` ([BJ22, `defi:intpairing`]): the value on any
good model on which all the `φᵢ` are represented by flag data (`0` if there is none). -/
def flagPair (s : Multiset (ℚ × (BerkovichPoint p → ℝ))) : ℚ :=
  if h : HasGoodRep p s then modelValue n hX ω h.choose h.choose_spec.choose s else 0

/-- **The pairing is computed on any good model representing the functions.** -/
theorem flagPair_eq {𝔠 : FlagIdeal X} {c : ℤ} (hgood : IsGoodModel p 𝔠 c)
    (s : Multiset (ℚ × (BerkovichPoint p → ℝ))) (hs : ∀ x ∈ s, IsFlagRep p 𝔠 c x.2) :
    flagPair n hX ω s = modelValue n hX ω 𝔠 c s := by
  have h : HasGoodRep p s := ⟨𝔠, c, hgood, hs⟩
  rw [flagPair, dif_pos h]
  obtain ⟨hgood₀, hs₀⟩ := h.choose_spec.choose_spec
  set 𝔠₀ := h.choose
  set c₀ := h.choose_spec.choose
  obtain ⟨g₀, g, hg₀, hg⟩ := exists_common_dominating p hgood₀.1 hgood.1
  have hP : IsGoodModel p (𝔠₀ * 𝔠) (c₀ + c) :=
    ⟨hgood₀.1.mul hgood.1, hgood₀.2.of_comp g₀ hg₀⟩
  rw [← modelValue_dominate n hX ω hgood₀ hP g₀ hg₀ s hs₀,
    modelValue_dominate n hX ω hgood hP g hg s hs]

theorem exists_goodModel_of_mem {s : Multiset (ℚ × (BerkovichPoint p → ℝ))}
    (hs : ∀ x ∈ s, x.2 ∈ plSubmodule p) : HasGoodRep p s := by
  obtain ⟨𝔠, c, h, hP⟩ := exists_common_goodModel (fun 𝔠 c φ => IsFlagRep p 𝔠 c φ)
    (fun _ _ _ _ g hg _ hφ => hφ.pullback g hg) (s.map Prod.snd) (fun φ hφ => by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hφ
      exact exists_goodModel_flagRep (hs x hx))
  exact ⟨𝔠, c, h, fun x hx => hP x.2 (Multiset.mem_map_of_mem _ hx)⟩

theorem modelClass_add {𝔠 : FlagIdeal X} {c : ℤ} (hgood : IsGoodModel p 𝔠 c)
    (x y : ℚ × (BerkovichPoint p → ℝ)) (hx : IsFlagRep p 𝔠 c x.2) (hy : IsFlagRep p 𝔠 c y.2) :
    modelClass ω 𝔠 c (x + y) = modelClass ω 𝔠 c x + modelClass ω 𝔠 c y := by
  rw [modelClass_eq ω hgood (x + y) (flagRep 𝔠 c x.2 + flagRep 𝔠 c y.2)
    (by rw [map_add, fn_flagRep hx, fn_flagRep hy]; rfl), modelClass, modelClass, map_add,
    Prod.fst_add, add_smul]
  abel

theorem modelClass_smul {𝔠 : FlagIdeal X} {c : ℤ} (hgood : IsGoodModel p 𝔠 c) (q : ℚ)
    (x : ℚ × (BerkovichPoint p → ℝ)) (hx : IsFlagRep p 𝔠 c x.2) :
    modelClass ω 𝔠 c (q • x) = q • modelClass ω 𝔠 c x := by
  rw [modelClass_eq ω hgood (q • x) (q • flagRep 𝔠 c x.2)
    (by rw [map_smul, fn_flagRep hx]; rfl), modelClass, map_smul, Prod.smul_fst, smul_add,
    smul_smul, smul_eq_mul]

/-- **Additivity in the first entry** ([BJ22, `prop:intpairing`]). -/
theorem flagPair_cons_add (x y : ℚ × (BerkovichPoint p → ℝ))
    (s : Multiset (ℚ × (BerkovichPoint p → ℝ))) (hx : x.2 ∈ plSubmodule p)
    (hy : y.2 ∈ plSubmodule p) (hs : ∀ z ∈ s, z.2 ∈ plSubmodule p) :
    flagPair n hX ω ((x + y) ::ₘ s) = flagPair n hX ω (x ::ₘ s) + flagPair n hX ω (y ::ₘ s) := by
  obtain ⟨𝔠, c, hgood, hrep⟩ := exists_goodModel_of_mem (s := x ::ₘ y ::ₘ s) (by
    intro z hz
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact hx
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact hs z hz)
  have hxr := hrep x (by simp)
  have hyr := hrep y (by simp)
  have hsr : ∀ z ∈ s, IsFlagRep p 𝔠 c z.2 := fun z hz => hrep z (by simp [hz])
  have hcons : ∀ w : ℚ × (BerkovichPoint p → ℝ), IsFlagRep p 𝔠 c w.2 →
      ∀ z ∈ w ::ₘ s, IsFlagRep p 𝔠 c z.2 := fun w hw z hz => by
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact hw
    · exact hsr z hz
  rw [flagPair_eq n hX ω hgood _ (hcons _ (hxr.add hyr)), flagPair_eq n hX ω hgood _ (hcons _ hxr),
    flagPair_eq n hX ω hgood _ (hcons _ hyr), modelValue, modelValue, modelValue,
    Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, modelClass_add ω hgood x y hxr hyr,
    MultisetForm.map_add]

/-- **Homogeneity in the first entry** ([BJ22, `prop:intpairing`]). -/
theorem flagPair_cons_smul (q : ℚ) (x : ℚ × (BerkovichPoint p → ℝ))
    (s : Multiset (ℚ × (BerkovichPoint p → ℝ))) (hx : x.2 ∈ plSubmodule p)
    (hs : ∀ z ∈ s, z.2 ∈ plSubmodule p) :
    flagPair n hX ω ((q • x) ::ₘ s) = q * flagPair n hX ω (x ::ₘ s) := by
  obtain ⟨𝔠, c, hgood, hrep⟩ := exists_goodModel_of_mem (s := x ::ₘ s) (by
    intro z hz
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact hs z hz)
  have hxr := hrep x (by simp)
  have hcons : ∀ w : ℚ × (BerkovichPoint p → ℝ), IsFlagRep p 𝔠 c w.2 →
      ∀ z ∈ w ::ₘ s, IsFlagRep p 𝔠 c z.2 := fun w hw z hz => by
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact hw
    · exact hrep z (by simp [hz])
  rw [flagPair_eq n hX ω hgood _ (hcons _ (hxr.smul q)), flagPair_eq n hX ω hgood _ hrep,
    modelValue, modelValue, Multiset.map_cons, Multiset.map_cons, modelClass_smul ω hgood q x hxr,
    MultisetForm.map_smul]

omit [IsProjective p] [IsIntegral X] in
theorem omegaPullback_eq_picPullbackQ (𝔠 : FlagIdeal X) (c : ℤ) :
    omegaPullback 𝔠 c ω = picPullbackQ (flagModelπ p 𝔠 c ≫ productFst p) ω := rfl

/-- **`(ω, 0)^{n+1} = 0`** ([BJ22, `prop:intpairing` (iii)]): `π^*ω` is pulled back from `X`,
of dimension `≤ n` (BJ-INTERSECT's pull-back vanishing). -/
theorem flagPair_zero :
    flagPair n hX ω (Multiset.replicate (n + 1) ((1 : ℚ), (0 : BerkovichPoint p → ℝ))) = 0 := by
  obtain ⟨𝔠, c, hgood⟩ := exists_isGoodModel (p := p)
  rw [flagPair_eq n hX ω hgood _ (fun x hx => by
    rw [Multiset.eq_of_mem_replicate hx]; exact IsFlagRep.zero), modelValue,
    Multiset.map_replicate]
  have hcl : modelClass ω 𝔠 c ((1 : ℚ), (0 : BerkovichPoint p → ℝ)) =
      picPullbackQ (normModelπ p 𝔠 c ≫ productFst p) ω := by
    rw [modelClass_eq ω hgood _ 0 (map_zero _), map_zero, add_zero, one_smul, normOmega,
      omegaPullback_eq_picPullbackQ, ← picPullbackQ_comp, ← Category.assoc]
  rw [hcl, ← Multiset.map_replicate]
  have hst : (normModelπ p 𝔠 c ≫ productFst p) ≫ p = normModelStructure p 𝔠 c := by
    simp only [normModelπ, Category.assoc]
  have : IsProjective ((normModelπ p 𝔠 c ≫ productFst p) ≫ p) := by rw [hst]; infer_instance
  rw [← interFormQ_congr hst]
  exact interFormQ_pullback_eq_zero p n hX _ _ _ _

end pair

/-! ### `ω`-psh functions -/

section psh

variable {ω : PicQ X}

variable (p) in
/-- On the model `(𝔠, c)`, `φ = φ_D` for a combination `D` of flag data with `π^*ω + [𝒪(D)]`
relatively nef. -/
def IsFlagPshOn (ω : PicQ X) (𝔠 : FlagIdeal X) (c : ℤ) (φ : BerkovichPoint p → ℝ) : Prop :=
  ∃ D : FDiv p 𝔠 c, FDiv.fn D = φ ∧
    omegaPullback 𝔠 c ω + FDiv.cls D ∈ relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c)

variable (p) in
/-- **`ω`-psh PL functions** ([BJ22, §3.1]) in the flag form: `φ = φ_D` on a good model for a
combination `D` of flag data with `π^*ω + [𝒪(D)]` relatively nef. -/
def IsFlagPsh (ω : PicQ X) (φ : BerkovichPoint p → ℝ) : Prop :=
  ∃ (𝔠 : FlagIdeal X) (c : ℤ), IsGoodModel p 𝔠 c ∧ IsFlagPshOn p ω 𝔠 c φ

omit [IsIntegral X] in
/-- Flag `ω`-psh functions are `ω`-psh PL functions in the sense of lane BJ-MODEL3. -/
theorem IsFlagPsh.isOmegaPshPL {φ : BerkovichPoint p → ℝ} (h : IsFlagPsh p ω φ) :
    IsOmegaPshPL ω φ := by
  obtain ⟨𝔠, c, hgood, D, hD, hnef⟩ := h
  exact ⟨𝔠, c, hgood, FDiv.toVDiv D, hD, hnef⟩

theorem IsFlagPshOn.pullback {𝔠 𝔠' : FlagIdeal X} {c c' : ℤ}
    (g : flagModel p 𝔠' c' ⟶ flagModel p 𝔠 c) (hg : g ≫ flagModelπ p 𝔠 c = flagModelπ p 𝔠' c')
    {φ : BerkovichPoint p → ℝ} (h : IsFlagPshOn p ω 𝔠 c φ) : IsFlagPshOn p ω 𝔠' c' φ := by
  obtain ⟨D, rfl, hD⟩ := h
  refine ⟨FDiv.pullback g hg D, FDiv.fn_pullback g hg D, ?_⟩
  have h' := mem_relNefCone_pullback g hg hD
  rwa [map_add, omegaPullback_comp g hg, ← FDiv.cls_pullback g hg] at h'

/-- `ω`-psh functions are stable under adding rational constants ([BJ22, §3.1]). -/
theorem IsFlagPsh.add_const {φ : BerkovichPoint p → ℝ} (h : IsFlagPsh p ω φ) (q : ℚ) :
    IsFlagPsh p ω (φ + fun _ => (q : ℝ)) := by
  obtain ⟨𝔠, c, hgood, D, rfl, hD⟩ := h
  refine ⟨𝔠, c, hgood, D + Finsupp.single (centralDatum hgood) q, ?_, ?_⟩
  · rw [map_add, FDiv.fn_single, fn_centralDatum]
    funext v
    simp [Rat.smul_def]
  · rw [map_add, FDiv.cls_single, picQ_centralDatum, ← add_assoc]
    refine add_mem hD ?_
    rcases le_or_gt 0 q with hq | hq
    · exact Submodule.smul_mem _ (⟨q, hq⟩ : {r : ℚ // 0 ≤ r})
        (neg_picQ_centralLine_mem_relNefCone p 𝔠 c)
    · rw [show q • -picQ (centralLine p 𝔠 c) = (-q) • picQ (centralLine p 𝔠 c) by
        rw [smul_neg, neg_smul]]
      exact Submodule.smul_mem _ (⟨-q, by linarith⟩ : {r : ℚ // 0 ≤ r})
        (picQ_centralLine_mem_relNefCone p 𝔠 c)

/-- `ω`-psh functions are stable under midpoints ([BJ22, §3.1]; common models). -/
theorem IsFlagPsh.midpoint {φ ψ : BerkovichPoint p → ℝ} (hφ : IsFlagPsh p ω φ)
    (hψ : IsFlagPsh p ω ψ) : IsFlagPsh p ω ((1 / 2 : ℚ) • (φ + ψ)) := by
  obtain ⟨𝔠, c, hgood, hφ⟩ := hφ
  obtain ⟨𝔠', c', hgood', hψ⟩ := hψ
  obtain ⟨g, g', hg, hg'⟩ := exists_common_dominating p hgood.1 hgood'.1
  obtain ⟨D, hD, hDn⟩ := hφ.pullback g hg
  obtain ⟨D', hD', hD'n⟩ := hψ.pullback g' hg'
  refine ⟨_, _, ⟨hgood.1.mul hgood'.1, hgood.2.of_comp g hg⟩, (1 / 2 : ℚ) • (D + D'), ?_, ?_⟩
  · rw [map_smul, map_add, hD, hD']
  · have key : omegaPullback (𝔠 * 𝔠') (c + c') ω + FDiv.cls ((1 / 2 : ℚ) • (D + D')) =
        (1 / 2 : ℚ) • ((omegaPullback (𝔠 * 𝔠') (c + c') ω + FDiv.cls D) +
          (omegaPullback (𝔠 * 𝔠') (c + c') ω + FDiv.cls D')) := by
      rw [map_smul, map_add]
      module
    rw [key]
    exact Submodule.smul_mem _ (⟨1 / 2, by norm_num⟩ : {r : ℚ // 0 ≤ r}) (add_mem hDn hD'n)

end psh

end SGPT.NAPotential.BJ
