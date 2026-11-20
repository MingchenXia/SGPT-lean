import SGPT.Checks.Comparison.BJPair2Hodge

/-!
# `lem:Hodge` for the energy pairing, and the pairing of an ample class (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), Lemma `lem:Hodge` and §3.2. Towards `thm:BJappseq` of
`chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

* `picPullbackQ_centralLine_eq_zero`: `𝒪(𝒳₀)` is trivial on every scheme mapping into the central
  fibre (the ideal of `0 ∈ ℙ¹` is principal on the chart `D₊(x₀)`);
* `interFormQ_flag_sq_nonpos_cone`: on a blow-up model, `(D² ⋅ θ₁ ⋯ θ_{n-1}) ≤ 0` for vertical `D`
  and relatively nef `θᵢ` (BJ-HODGE's argument in the form `interFormQ_sq_nonpos_of_vertical_ortho`,
  with the central fibre `𝒳₀` as the fibre class);
* `pairHodge` (**[BJ22, `lem:Hodge`]**): the axiom `PairHodge` of lane BJ-PAIR;
* `energyPairingOfAmple`: the energy pairing of an ample class, with all the axioms proved;
* `bjAppSeq_of_charged`: `thm:BJappseq` from `thm:pshdetbydiv` and the charging of divisorial
  points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### The central fibre as a fibre class -/

section central

variable {𝔠 : FlagIdeal X} {c : ℤ}

variable (p) in
/-- The central fibre `𝒳₀ = π^*(X × {0})` as a vertical effective Cartier divisor. -/
def centralVertCartier (𝔠 : FlagIdeal X) (c : ℤ) : VertCartier p 𝔠 c where
  ideal := (centralIdeal p).comap (flagModelπ p 𝔠 c)
  isInvertible := isInvertible_comap_centralIdeal p 𝔠 c
  support_subset := by
    rw [Scheme.IdealSheafData.support_comap]
    intro x hx
    exact hx

theorem centralFibre_subset_support :
    centralFibre p 𝔠 c ⊆ ((centralVertCartier p 𝔠 c).ideal.support : Set (flagModel p 𝔠 c)) := by
  change _ ⊆ (((centralIdeal p).comap (flagModelπ p 𝔠 c)).support : Set (flagModel p 𝔠 c))
  rw [Scheme.IdealSheafData.support_comap]
  intro x hx
  exact hx

/-- The canonical section of `𝒪(E)` is nonzero for a vertical divisor `E`. -/
theorem VertCartier.cartierSection_ne_zero (E : VertCartier p 𝔠 c) :
    cartierSection E.ideal E.isInvertible ≠ 0 := by
  refine ne_zero_of_not_mem_support _ (cartierLine_isInvertible E.isInvertible) _
    (genericPoint (flagModel p 𝔠 c)) ?_
  rw [zeroIdeal_cartierSection]
  intro hmem
  have h1 := E.support_subset hmem
  change flagModelπ p 𝔠 c (genericPoint (flagModel p 𝔠 c)) ∈ (centralIdeal p).support at h1
  rw [(flagModelπ_genericPoint p 𝔠 c).1] at h1
  exact genericPoint_productLine_not_mem h1

omit [IsProjective p] [IsIntegral X] in
/-- `[𝒪(-E)] = -[𝒪(E)]`. -/
theorem VertCartier.picQ_line_eq (E : VertCartier p 𝔠 c) :
    picQ E.line = -picQ ⟨cartierLine E.ideal, cartierLine_isInvertible E.isInvertible⟩ := by
  rw [picQ, picQ, lineCls_cartierLine E.isInvertible, TensorProduct.tmul_neg, neg_neg]
  rfl

/-- **`𝒪(𝒳₀)` is trivial on the central fibre**: its pull-back along any morphism with image in
the central fibre is trivial (the ideal of `0 ∈ ℙ¹` is `(t)` on the chart `D₊(x₀)`). -/
theorem picPullbackQ_centralLine_eq_zero {T : Scheme.{0}} (h : T ⟶ flagModel p 𝔠 c)
    (hr : Set.range h ⊆ centralFibre p 𝔠 c) :
    picPullbackQ h (picQ (centralLine p 𝔠 c)) = 0 := by
  let q := flagModelπ p 𝔠 c ≫ productSnd p
  have := flagModel_productSnd_isDominant (p := p) 𝔠 c
  have hcomap : (centralIdeal p).comap (flagModelπ p 𝔠 c) = (zeroIdeal ℂ).comap q := by
    rw [Scheme.IdealSheafData.comap_comp]
    rfl
  have hrange : Set.range (h ≫ q) ⊆ Set.range (lineChart ℂ) := by
    rintro _ ⟨x, rfl⟩
    have h1 := hr ⟨x, rfl⟩
    change flagModelπ p 𝔠 c (h x) ∈ ((centralIdeal p).support : Set _) at h1
    rw [support_centralIdeal] at h1
    obtain ⟨z, hz⟩ := h1
    refine ⟨Spec.map (CommRingCat.ofHom (evalZero ℂ)) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← zeroPoint, hz]
    rfl
  obtain ⟨e⟩ := nonempty_pullback_comap_zeroIdeal_iso_unit q h hrange
  rw [picPullbackQ_picQ]
  have h1 : picQ ⟨(Scheme.Modules.pullback h).obj (centralLine p 𝔠 c).1,
      (centralLine p 𝔠 c).2.pullback _⟩ =
      picQ ⟨Scheme.Modules.unitObj T, Scheme.Modules.isInvertible_unit⟩ := by
    have hc : (centralLine p 𝔠 c).1 = ((zeroIdeal ℂ).comap q).toModules := by
      simp only [centralLine, hcomap]
    exact picQ_eq_of_iso _ _ ((Scheme.Modules.pullback h).mapIso (eqToIso hc) ≪≫ e)
  rw [h1, picQ, lineCls_unit, TensorProduct.tmul_zero]

/-- The same for `𝒪(𝒳₀)` with its canonical section: the hypothesis of
`interFormQ_sq_nonpos_of_vertical_ortho`. -/
theorem picPullbackQ_cartierCentral_eq_zero {T : Scheme.{0}} (h : T ⟶ flagModel p 𝔠 c)
    (hr : Set.range h ⊆ (SGPT.Foundations.Envelope.LineSectionZeroIdeal.zeroIdeal
      (cartierLine (centralVertCartier p 𝔠 c).ideal)
      (cartierLine_isInvertible (centralVertCartier p 𝔠 c).isInvertible)
      (cartierSection _ (centralVertCartier p 𝔠 c).isInvertible)).support) :
    picPullbackQ h (picQ ⟨cartierLine (centralVertCartier p 𝔠 c).ideal,
      cartierLine_isInvertible (centralVertCartier p 𝔠 c).isInvertible⟩) = 0 := by
  rw [zeroIdeal_cartierSection] at hr
  rw [← neg_neg (picQ _), ← VertCartier.picQ_line_eq, map_neg, neg_eq_zero]
  exact picPullbackQ_centralLine_eq_zero h (hr.trans (centralVertCartier p 𝔠 c).support_subset)

end central

/-! ### The Hodge inequality on a blow-up model -/

section hodge

variable {𝔠 : FlagIdeal X} {c : ℤ}

omit [IsProjective p] [IsIntegral X] in
/-- The class of a combination of flag data, as a combination of the `[𝒪(E)]`. -/
theorem FDiv.cls_eq_sum (D : FDiv p 𝔠 c) :
    FDiv.cls D = ∑ i : D.support, D i.1 •
      picQ ⟨cartierLine i.1.vert.ideal, cartierLine_isInvertible i.1.vert.isInvertible⟩ := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, ← Finset.sum_coe_sort D.support]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FDiv.cls_single, VertCartier.picQ_line_eq, neg_neg]

/-- **The Hodge inequality on a model**, against line bundles relatively nef over `𝔸¹`. -/
theorem interFormQ_flag_sq_nonpos (m : ℕ)
    (hdim : topologicalKrullDim (flagModel p 𝔠 c) ≤ (m + 2 : ℕ)) (D : FDiv p 𝔠 c)
    (l : List {N : (flagModel p 𝔠 c).Modules // Scheme.Modules.IsInvertible N})
    (hl : l.length = m)
    (hnef : ∀ N ∈ l, IsNefOn (flagModelStructure p 𝔠 c) N.1 (centralFibre p 𝔠 c)) :
    interFormQ (flagModelStructure p 𝔠 c) (m + 2) hdim (Scheme.Modules.unitObj _)
      (FDiv.cls D ::ₘ FDiv.cls D ::ₘ ((l.map picQ : List _) : Multiset _)) ≤ 0 := by
  classical
  set E0 := centralVertCartier p 𝔠 c
  have h := interFormQ_sq_nonpos_of_vertical_ortho m (flagModelStructure p 𝔠 c) hdim
    (cartierLine E0.ideal) (cartierLine_isInvertible E0.isInvertible)
    (cartierSection E0.ideal E0.isInvertible) E0.cartierSection_ne_zero
    (fun h hr => picPullbackQ_cartierCentral_eq_zero h hr)
    (fun i : D.support =>
      (⟨cartierLine i.1.vert.ideal, cartierLine_isInvertible i.1.vert.isInvertible⟩ :
        {M : (flagModel p 𝔠 c).Modules // Scheme.Modules.IsInvertible M}))
    (fun i => cartierSection i.1.vert.ideal i.1.vert.isInvertible)
    (fun i => i.1.vert.cartierSection_ne_zero)
    (fun i x hx => by
      have e1 := zeroIdeal_cartierSection i.1.vert.ideal i.1.vert.isInvertible
      have e2 := zeroIdeal_cartierSection E0.ideal E0.isInvertible
      rw [e1] at hx
      rw [e2]
      exact centralFibre_subset_support (i.1.vert.support_subset hx))
    (centralFibre p 𝔠 c)
    (fun x hx => by
      have e2 := zeroIdeal_cartierSection E0.ideal E0.isInvertible
      rw [e2] at hx
      exact E0.support_subset hx)
    (l.map fun N => (N, (1 : ℚ))) (by simpa using hl)
    (fun N hN => by
      obtain ⟨N', hN', rfl⟩ := List.mem_map.mp hN
      exact hnef N' hN')
    (fun N hN => by
      obtain ⟨N', -, rfl⟩ := List.mem_map.mp hN
      exact zero_le_one)
    (fun i => D i.1)
  have e : ((l.map fun N => (N, (1 : ℚ))).map fun N => N.2 • picQ N.1) = l.map picQ := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ => one_smul ℚ _
  rw [e, ← FDiv.cls_eq_sum] at h
  exact h

/-- **The Hodge inequality on a model** ([BJ22, `lem:Hodge`]), against relatively nef classes. -/
theorem interFormQ_flag_sq_nonpos_cone (m : ℕ)
    (hdim : topologicalKrullDim (flagModel p 𝔠 c) ≤ (m + 2 : ℕ)) (D : FDiv p 𝔠 c)
    (s : Multiset (PicQ (flagModel p 𝔠 c))) (hs : Multiset.card s = m)
    (hnef : ∀ θ ∈ s, θ ∈ relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c)) :
    interFormQ (flagModelStructure p 𝔠 c) (m + 2) hdim (Scheme.Modules.unitObj _)
      (FDiv.cls D ::ₘ FDiv.cls D ::ₘ s) ≤ 0 := by
  set Φ := interFormQ (flagModelStructure p 𝔠 c) (m + 2) hdim (Scheme.Modules.unitObj _)
  let Ψ : MultisetForm ℚ (PicQ (flagModel p 𝔠 c)) :=
    { toFun := fun s => -Φ s
      map_add' := fun x y s => by
        change -Φ _ = -Φ _ + -Φ _
        rw [Φ.map_add, neg_add]
      map_smul' := fun q x s => by
        change -Φ _ = q * -Φ _
        rw [Φ.map_smul, mul_neg] }
  let I := {N : {N : (flagModel p 𝔠 c).Modules // Scheme.Modules.IsInvertible N} //
    IsNefOn (flagModelStructure p 𝔠 c) N.1 (centralFibre p 𝔠 c)}
  let gen : I → PicQ (flagModel p 𝔠 c) := fun i => picQ i.1
  have hcone : relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c) ≤
      PointedCone.hull ℚ (Set.range gen) :=
    Submodule.span_mono fun θ ⟨N, hN, hθ⟩ => ⟨⟨N, hN⟩, hθ.symm⟩
  have key := MultisetForm.nonneg_of_mem_hull Ψ gen s (FDiv.cls D ::ₘ FDiv.cls D ::ₘ 0)
    (fun θ hθ => hcone (hnef θ hθ)) (fun l hl => by
      have h := interFormQ_flag_sq_nonpos m hdim D (l.map Subtype.val) (by simpa [hs] using hl)
        (fun N hN => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hN
          exact i.2)
      rw [List.map_map] at h
      change 0 ≤ -Φ _
      rw [Multiset.cons_add, Multiset.cons_add, zero_add]
      exact neg_nonneg.mpr h)
  change 0 ≤ -Φ _ at key
  rw [Multiset.cons_add, Multiset.cons_add, zero_add] at key
  exact neg_nonneg.mp key

end hodge

/-! ### `lem:Hodge` for the energy pairing -/

section pairHodge

variable (n : ℕ) (hX : topologicalKrullDim X ≤ n) (ω : PicQ X)

/-- **`lem:Hodge` on a good model.** -/
theorem modelValue_hodge {𝔠 : FlagIdeal X} {c : ℤ} (hgood : IsGoodModel p 𝔠 c)
    {f : BerkovichPoint p → ℝ} (hf : IsFlagRep p 𝔠 c f) (us : Multiset (BerkovichPoint p → ℝ))
    (hcard : Multiset.card us + 1 = n) (hu : ∀ u ∈ us, IsFlagPshOn p ω 𝔠 c u) :
    modelValue n hX ω 𝔠 c (((0 : ℚ), f) ::ₘ ((0 : ℚ), f) ::ₘ us.map fun u => ((1 : ℚ), u)) ≤
      0 := by
  classical
  subst hcard
  let R : (BerkovichPoint p → ℝ) → FDiv p 𝔠 c := fun φ =>
    if h : IsFlagPshOn p ω 𝔠 c φ then h.choose else flagRep 𝔠 c φ
  have hRpsh : ∀ u ∈ us, FDiv.fn (R u) = u ∧ omegaPullback 𝔠 c ω + FDiv.cls (R u) ∈
      relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c) := by
    intro u hu'
    have h := hu u hu'
    simp only [R, dif_pos h]
    exact h.choose_spec
  have hRf : FDiv.fn (R f) = f := by
    by_cases h : IsFlagPshOn p ω 𝔠 c f
    · simp only [R, dif_pos h]
      exact h.choose_spec.1
    · simp only [R, dif_neg h]
      exact fn_flagRep hf
  rw [← interFormQ_flag_eq_modelValue _ hX ω hgood _ R (fun x hx => by
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hRf
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hRf
    obtain ⟨u, hu', rfl⟩ := Multiset.mem_map.mp hx
    exact (hRpsh u hu').1)]
  simp only [Multiset.map_cons, Multiset.map_map, Function.comp_def, zero_smul, zero_add,
    one_smul]
  exact interFormQ_flag_sq_nonpos_cone (Multiset.card us)
    (topologicalKrullDim_flagModel_le p 𝔠 c (Multiset.card us + 1) hX) (R f) _
    (Multiset.card_map _ _) (fun θ hθ => by
      obtain ⟨u, hu', rfl⟩ := Multiset.mem_map.mp hθ
      exact (hRpsh u hu').2)

/-- **[BJ22, `lem:Hodge`]**: `(0, f) ⋅ (0, f) ⋅ (ω, u₁) ⋯ (ω, u_{n-1}) ≤ 0` for a PL function `f`
and `ω`-psh PL functions `uᵢ`. This is the axiom `PairHodge` of lane BJ-PAIR. -/
theorem pairHodge : PairHodge p n hX ω := by
  classical
  intro f hf us hcard hu
  obtain ⟨𝔠, c, hgood, hP⟩ := exists_common_goodModel
    (fun 𝔠 c φ => IsFlagRep p 𝔠 c φ ∧ (φ ∈ us → IsFlagPshOn p ω 𝔠 c φ))
    (fun _ _ _ _ g hg _ hφ => ⟨hφ.1.pullback g hg, fun h => (hφ.2 h).pullback g hg⟩)
    (f ::ₘ us) (fun φ hφ => by
      by_cases hφu : φ ∈ us
      · obtain ⟨𝔠, c, hgood, D, hD, hDn⟩ := (hu φ hφu).2
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
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact (hP _ (Multiset.mem_cons_self _ _)).1
    obtain ⟨u, hu', rfl⟩ := Multiset.mem_map.mp hx
    exact (hP u (Multiset.mem_cons_of_mem hu')).1)]
  exact modelValue_hodge n hX ω hgood (hP f (Multiset.mem_cons_self _ _)).1 us hcard
    fun u hu' => (hP u (Multiset.mem_cons_of_mem hu')).2 hu'

end pairHodge

/-! ### The energy pairing of an ample class -/

section ample

open SGPT.NAPotential.BJEnergy

variable [CompactSpace X] [X.IsSeparated]

/-- **The energy pairing of an ample rational class** ([BJ22, §3.2]) for `dim X = n ≥ 1`: all its
axioms (`PairConst`, `PairTriv`, `PairHodge`, `(ω^n) > 0`) are proved. -/
def energyPairingOfAmple (n : ℕ) (hX : topologicalKrullDim X ≤ n)
    (hXn : topologicalKrullDim X = n) (hn : 0 < n) (ω : NativePicard.RationalPicardSpace X)
    (hω : NativePicard.numericalClass p ω ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p) :
    EnergyPairing (BerkovichPoint p) n :=
  energyPairingOfConstHodge n hX hXn hn ω hω (pairConst n hX ω) (pairHodge n hX ω)

/-- **`thm:BJappseq` from `thm:pshdetbydiv` and the charging of divisorial points** ([BJ22,
`thm:BJappseq`]), for `X` of dimension `n ≥ 1`: the energy pairings of ample classes are
constructed, with all their axioms proved. -/
theorem bjAppSeq_of_charged
    (hcomp : SGPT.NAPotential.BJ.AppSeq.DivisorialComparison p) (n : ℕ)
    (hX : topologicalKrullDim X ≤ n) (hXn : topologicalKrullDim X = n) (hn : 0 < n)
    (hE : ∀ (ω : NativePicard.RationalPicardSpace X)
      (hω : NativePicard.numericalClass p ω ∈
        SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p),
        ∀ v ∈ divisorialSet p, (energyPairingOfAmple n hX hXn hn ω hω).IsCharged v) :
    SGPT.NAPotential.BJ.AppSeq.BJAppSeqStatement.{u} p :=
  bjAppSeq_of_constHodge hcomp n hX hXn hn fun ω hω =>
    ⟨pairConst n hX ω, pairHodge n hX ω, hE ω hω⟩

end ample

end SGPT.NAPotential.BJ
