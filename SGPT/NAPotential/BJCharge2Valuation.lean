import SGPT.NAPotential.BJModelFlagIdeal

/-!
# Valuation ideals and the flag ideal of a semi-valuation (lane BJ-CHARGE, step R8(b))

Source: Boucksom–Jonsson ([BJ22], `references/bj22-trivval`), proof of Lemma `lem:divRees` and
[BHJ17, Theorem 4.6]: the valuation ideals `𝔞_μ = {f : v(f) ≥ μ}` of a valuation `v` and the flag
ideal `∑_μ 𝔞_μ t^{-μ}` whose normalized blow-up has `σ(v)` as a Rees valuation. Towards
`thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-charge2.tex`.

For a semi-valuation `v ∈ X^An` with centre `c = c(v)` (SGPT's `BerkovichPoint.center`) and
`μ ∈ ℝ`:

* `valIdeal v μ`: the ideal sheaf with sections `{g ∈ Γ(U, 𝒪) : v(g_c) ≥ μ}` over affine opens `U`
  containing `c` and `Γ(U, 𝒪)` over the others (it is quasi-coherent: `map_ideal_basicOpen`);
* `germ_mem_stalkIdeal_valIdeal`: every germ `g ∈ 𝒪_{X,c}` with `v(g) ≥ μ` lies in its stalk;
* `ofReal_le_idealVal_valIdeal`: `v(𝔞_μ) ≥ μ`;
* `valFlag v N`: the flag ideal `𝔞_λ = 𝒪` (`λ ≤ 0`), `𝔞_λ = valIdeal v λ` (`0 < λ ≤ N`),
  `𝔞_λ = 0` (`λ > N`), with `φ_{valFlag v N}(v) = 0` (`phi_valFlag`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJCharge

open AlgebraicGeometry CategoryTheory Topology IsLocalRing
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BerkovichPoint
open SGPT.NAPotential.BJModel
open scoped ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsProper f] (v : BerkovichPoint f)

/-- The valuation ideal `{g ∈ 𝒪_{X,c(v)} : v(g) ≥ μ}` of the stalk at the centre. -/
def stalkValIdeal (μ : ℝ) : Ideal (X.presheaf.stalk v.center) where
  carrier := {g | ((μ : ℝ) : WithTop ℝ) ≤ v.centerVal g}
  add_mem' {a b} ha hb := (le_min ha hb).trans (v.min_le_centerVal_add a b)
  zero_mem' := by simp
  smul_mem' r a ha := by
    change ((μ : ℝ) : WithTop ℝ) ≤ v.centerVal (r * a)
    rw [centerVal_mul]
    calc ((μ : ℝ) : WithTop ℝ) = 0 + (μ : WithTop ℝ) := (zero_add _).symm
      _ ≤ v.centerVal r + v.centerVal a := add_le_add (v.centerVal_nonneg r) ha

theorem mem_stalkValIdeal {μ : ℝ} {g : X.presheaf.stalk v.center} :
    g ∈ stalkValIdeal v μ ↔ ((μ : ℝ) : WithTop ℝ) ≤ v.centerVal g := Iff.rfl

/-- The valuation ideal on an affine open: the sections whose germ at the centre has value
`≥ μ` (all sections if the open does not contain the centre). -/
def valIdealOn (μ : ℝ) (U : X.affineOpens) : Ideal Γ(X, U) where
  carrier := {g | ∀ h : v.center ∈ (U : X.Opens), (X.presheaf.germ U v.center h).hom g ∈
    stalkValIdeal v μ}
  add_mem' {a b} ha hb h := by rw [map_add]; exact add_mem (ha h) (hb h)
  zero_mem' h := by rw [map_zero]; exact zero_mem _
  smul_mem' r a ha h := by
    rw [smul_eq_mul, map_mul]
    exact Ideal.mul_mem_left _ _ (ha h)

theorem mem_valIdealOn {μ : ℝ} {U : X.affineOpens} {g : Γ(X, U)} :
    g ∈ valIdealOn v μ U ↔
      ∀ h : v.center ∈ (U : X.Opens), (X.presheaf.germ U v.center h).hom g ∈ stalkValIdeal v μ :=
  Iff.rfl

theorem valIdealOn_eq_top {μ : ℝ} {U : X.affineOpens} (h : v.center ∉ (U : X.Opens)) :
    valIdealOn v μ U = ⊤ :=
  eq_top_iff.mpr fun _ _ hc => absurd hc h

/-- Some power of a germ of positive value has value `≥ μ`. -/
theorem exists_pow_mem_stalkValIdeal (μ : ℝ) {g : X.presheaf.stalk v.center}
    (hg : 0 < v.centerVal g) : ∃ k : ℕ, g ^ k ∈ stalkValIdeal v μ := by
  simp only [mem_stalkValIdeal]
  have hpow : ∀ k : ℕ, v.centerVal (g ^ k) = k • v.centerVal g := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, centerVal_mul, ih, succ_nsmul]
  by_cases htop : v.centerVal g = ⊤
  · exact ⟨1, by rw [hpow, htop, one_nsmul]; exact le_top⟩
  · lift v.centerVal g to ℝ using htop with r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hg
    obtain ⟨k, hk⟩ := exists_nat_ge (μ / r)
    refine ⟨k, ?_⟩
    rw [hpow, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]
    rwa [div_le_iff₀ hr0] at hk

/-- **The valuation ideals are quasi-coherent**: compatibility with basic opens. -/
theorem map_valIdealOn_basicOpen (μ : ℝ) (U : X.affineOpens) (g : Γ(X, U)) :
    (valIdealOn v μ U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
      valIdealOn v μ (X.affineBasicOpen g) := by
  by_cases hU : v.center ∈ (U : X.Opens)
  · by_cases hD : v.center ∈ X.basicOpen g
    · apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, mem_valIdealOn]
        intro h
        have e : (X.presheaf.germ (X.basicOpen g) v.center h).hom
            ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom a) =
            (X.presheaf.germ U v.center hU).hom a :=
          congrArg (fun φ => φ.hom a) (X.presheaf.germ_res (homOfLE (X.basicOpen_le g)) _ h)
        change (X.presheaf.germ (X.basicOpen g) v.center h).hom _ ∈ _
        rw [e]
        exact ha hU
      · intro F hF
        let := (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
        have hloc : IsLocalization.Away g Γ(X, X.basicOpen g) := U.2.isLocalization_basicOpen g
        obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) F
        obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
        have hs : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (s : Γ(X, U))) :=
          IsLocalization.map_units _ s
        have hspec := IsLocalization.mk'_spec Γ(X, X.basicOpen g) a s
        have hg0 : v.centerVal ((X.presheaf.germ U v.center hU).hom g) = 0 := by
          rw [centerVal_eq_zero_iff]
          rwa [Scheme.mem_basicOpen _ _ _ hU] at hD
        have e : ∀ t : Γ(X, U), (X.presheaf.germ (X.basicOpen g) v.center hD).hom
            (algebraMap Γ(X, U) Γ(X, X.basicOpen g) t) =
            (X.presheaf.germ U v.center hU).hom t := fun t =>
          congrArg (fun φ => φ.hom t) (X.presheaf.germ_res (homOfLE (X.basicOpen_le g)) _ hD)
        have ha : a ∈ valIdealOn v μ U := by
          intro _
          have hF' := hF hD
          rw [mem_stalkValIdeal] at hF' ⊢
          have h2 := congrArg (fun t => v.centerVal ((X.presheaf.germ (X.basicOpen g) v.center
            hD).hom t)) hspec
          simp only [map_mul, centerVal_mul, e] at h2
          have hpow : ∀ m : ℕ, v.centerVal ((X.presheaf.germ U v.center hU).hom g ^ m) = 0 := by
            intro m
            induction m with
            | zero => simp
            | succ m ih => rw [pow_succ, centerVal_mul, ih, hg0, add_zero]
          rw [← h2, ← hk, map_pow, hpow, add_zero]
          exact hF'
        have hmk : IsLocalization.mk' Γ(X, X.basicOpen g) a s =
            algebraMap Γ(X, U) Γ(X, X.basicOpen g) a * ((hs.unit⁻¹ : Γ(X, X.basicOpen g)ˣ) :
              Γ(X, X.basicOpen g)) :=
          (Units.eq_mul_inv_iff_mul_eq hs.unit).mpr hspec
        change IsLocalization.mk' Γ(X, X.basicOpen g) a s ∈ _
        rw [hmk]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    · rw [valIdealOn_eq_top v (U := X.affineBasicOpen g) hD, eq_top_iff]
      have hmax : (X.presheaf.germ U v.center hU).hom g ∈ maximalIdeal (X.presheaf.stalk v.center) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        rwa [Scheme.mem_basicOpen _ _ _ hU] at hD
      obtain ⟨k, hk⟩ := exists_pow_mem_stalkValIdeal v μ (v.centerVal_pos hmax)
      have hmem : g ^ k ∈ valIdealOn v μ U := fun _ => by rwa [map_pow]
      have hunit : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ k)) := by
        rw [map_pow]
        exact (X.toRingedSpace.isUnit_res_basicOpen g).pow k
      rw [← Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem) hunit]
  · have hD : v.center ∉ X.basicOpen g := fun h => hU (X.basicOpen_le g h)
    rw [valIdealOn_eq_top v hU, Ideal.map_top, valIdealOn_eq_top v (U := X.affineBasicOpen g) hD]

/-- **The valuation ideal sheaf** `𝔞_μ = {g : v(g) ≥ μ}` of `v` ([BJ22, proof of
`lem:divRees`]). -/
def valIdeal (μ : ℝ) : X.IdealSheafData where
  ideal := valIdealOn v μ
  map_ideal_basicOpen := map_valIdealOn_basicOpen v μ

theorem valIdeal_ideal (μ : ℝ) (U : X.affineOpens) : (valIdeal v μ).ideal U = valIdealOn v μ U :=
  rfl

/-- **Germs of large value lie in the stalk of the valuation ideal.** -/
theorem germ_mem_stalkIdeal_valIdeal {μ : ℝ} {g : X.presheaf.stalk v.center}
    (hg : g ∈ stalkValIdeal v μ) : g ∈ stalkIdeal (valIdeal v μ) v.center := by
  obtain ⟨W, hcW, s, rfl⟩ := X.presheaf.exists_germ_eq g
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hcW W.isOpen
  have e : (X.presheaf.germ U v.center hcU).hom ((X.presheaf.map (homOfLE hUW).op).hom s) =
      (X.presheaf.germ W v.center hcW).hom s :=
    congrArg (fun φ => φ.hom s) (X.presheaf.germ_res (homOfLE hUW) _ hcU)
  rw [← e]
  refine germ_mem_stalkIdeal _ ⟨U, hU⟩ hcU ?_
  intro h
  change (X.presheaf.germ U v.center h).hom _ ∈ _
  rwa [e]

/-- The stalk of the valuation ideal at the centre consists of germs of value `≥ μ`. -/
theorem stalkIdeal_valIdeal_le (μ : ℝ) :
    stalkIdeal (valIdeal v μ) v.center ≤ stalkValIdeal v μ := by
  refine iSup₂_le fun U hU => ?_
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  exact hg hU

/-- **`v(𝔞_μ) ≥ μ`.** -/
theorem ofReal_le_idealVal_valIdeal (μ : ℝ) :
    ENNReal.ofReal μ ≤ v.idealVal (valIdeal v μ) := by
  refine le_iInf₂ fun g hg => ?_
  have h := stalkIdeal_valIdeal_le v μ hg
  rw [mem_stalkValIdeal] at h
  unfold centerValENN
  calc ENNReal.ofReal μ = toENNReal ((μ : ℝ) : WithTop ℝ) := (toENNReal_coe μ).symm
    _ ≤ toENNReal (v.centerVal g) := toENNReal_mono h

theorem valIdeal_antitone : Antitone (valIdeal v) := by
  intro μ μ' h U g hg hc
  exact (WithTop.coe_le_coe.mpr h).trans (hg hc)

/-- **The flag ideal of valuation ideals**: `𝔞_λ = 𝒪` for `λ ≤ 0`, `𝔞_λ = {v ≥ λ}` for
`0 < λ ≤ N`, `𝔞_λ = 0` for `λ > N`. -/
def valFlag (N : ℕ) : FlagIdeal X where
  ideal l := if l ≤ 0 then ⊤ else if l ≤ N then valIdeal v l else ⊥
  antitone l l' h := by
    dsimp only
    split_ifs with h1 h2 h3 h4 h5 h6 <;> first
      | exact le_rfl | exact le_top | exact bot_le
      | exact valIdeal_antitone v (by exact_mod_cast h)
      | omega
  exists_eq_top := ⟨0, fun l hl => by simp [hl]⟩
  exists_eq_bot := ⟨N, fun l hl => by
    have h1 : ¬ l ≤ 0 := by omega
    have h2 : ¬ l ≤ (N : ℤ) := by omega
    simp [h1, h2]⟩

theorem valFlag_ideal_of_pos {N : ℕ} {l : ℤ} (h0 : 0 < l) (hN : l ≤ N) :
    (valFlag v N).ideal l = valIdeal v l := by
  simp [valFlag, not_le.mpr h0, hN]

theorem valFlag_ideal_of_nonpos (N : ℕ) {l : ℤ} (h0 : l ≤ 0) : (valFlag v N).ideal l = ⊤ := by
  simp [valFlag, h0]

/-- **`φ_{valFlag}(v) = 0`**: the flag ideal of the valuation ideals of `v` has `φ(v) = 0`. -/
theorem phi_valFlag (N : ℕ) : (valFlag v N).phi v = 0 := by
  apply le_antisymm
  · rw [FlagIdeal.phi_le_iff]
    intro l
    simp only [sub_zero]
    by_cases h0 : l ≤ 0
    · rw [ENNReal.ofReal_eq_zero.mpr (by exact_mod_cast h0)]
      exact zero_le
    · by_cases hN : l ≤ N
      · rw [valFlag_ideal_of_pos v (not_le.mp h0) hN]
        exact ofReal_le_idealVal_valIdeal v l
      · have : (valFlag v N).ideal l = ⊥ := by simp [valFlag, h0, hN]
        rw [this, idealVal_bot]
        exact le_top
  · have := FlagIdeal.le_phi (valFlag v N) v (valFlag_ideal_of_nonpos v N le_rfl)
    simpa using this

end SGPT.NAPotential.BJCharge
