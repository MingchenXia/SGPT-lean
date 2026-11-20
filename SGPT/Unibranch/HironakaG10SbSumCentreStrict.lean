import SGPT.Foundations.Analysis.Pending.HironakaG10ChowArtinReesCentre
import SGPT.Unibranch.HironakaG10SbTorsionSaturation

/-!
# For a sum centre the algebraic strict transform is the total transform divided once by `G`

Lane G10SB, run 0081, towards N5 of `G10SB/G10-02-10b-native-strict-flat-route.md` (Hironaka 1975, Lemma 3.2,
printed pp. 531–532: for the centre `I_S^β + I_Z` with `β` at least an Artin–Rees number, the total transform of `Z`
is its strict transform plus the exceptional divisor once).

At a point of the blowup with pulled centre `(G)`, `G` regular, and `I_Z ⊆ D = I_S^β + I_Z`:

* `strictIdeal_mem_iff_sumCentre` — **`h' ∈ strictIdeal φ I_Z D G ↔ G h' ∈ I_Z R`** (no locality needed);
* `map_eq_span_mul_strictIdeal` — `I_Z R = G · strictIdeal`;
* `isRegular_mk_strictIdeal_iff` — `G` is regular modulo the strict ideal iff `(I_Z R : G²) = (I_Z R : G)`,
  iff the strict ideal is the full `G`-saturation `powerSat (I_Z R) G` (`strictIdeal_eq_powerSat_iff`).

So N5 (regularity of `G` modulo the germ strict ideal) is exactly the single-step saturation `(I_Z R : G²) = (I_Z R : G)`.
Pure commutative algebra, no named input.
-/

set_option autoImplicit false

namespace SGPT.Unibranch.HironakaG10SbSumCentreStrict

open SGPT.Foundations.Analysis.Pending.HironakaG10ChowArtinReesCentre
  SGPT.Unibranch.HironakaG10SbTorsionSaturation

variable {A R : Type*} [CommRing A] [CommRing R]

/-- The image of `h ∈ I_Z ∩ D^(k+1)` lies in `G^k · I_Z R` (Artin–Rees for the sum centre). -/
theorem map_mem_span_pow_mul (φ : A →+* R) (IZ IS : Ideal A) (α β : ℕ)
    (hαβ : α ≤ β) (hAR : ∀ m, α ≤ m → IZ ⊓ IS ^ m ≤ IS ^ (m - α) * (IZ ⊓ IS ^ α))
    (G : R) (hD : Ideal.map φ (IS ^ β ⊔ IZ) = Ideal.span {G})
    (k : ℕ) (h : A) (hhZ : h ∈ IZ) (hhD : h ∈ (IS ^ β ⊔ IZ) ^ (k + 1)) :
    φ h ∈ Ideal.span {G ^ k} * Ideal.map φ IZ := by
  have hSle : Ideal.map φ (IS ^ β) ≤ Ideal.span {G} := hD ▸ Ideal.map_mono le_sup_left
  have hsplit : h ∈ (IS ^ β) ^ (k + 1) ⊔ IZ * (IS ^ β ⊔ IZ) ^ k :=
    pow_succ_sup_le (IS ^ β) IZ k hhD
  obtain ⟨h₁, hh₁, h₂, hh₂, hsum⟩ := Submodule.mem_sup.mp hsplit
  have h₂Z : h₂ ∈ IZ := Ideal.mul_le_left (I := IZ) (J := (IS ^ β ⊔ IZ) ^ k) hh₂
  have h₁Z : h₁ ∈ IZ := by
    have h' : h - h₂ ∈ IZ := IZ.sub_mem hhZ h₂Z
    rwa [← hsum, add_sub_cancel_right] at h'
  have hm : α ≤ β * (k + 1) := le_trans hαβ (Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
  have hh₁' : h₁ ∈ IS ^ (β * (k + 1)) := by rwa [pow_mul]
  have h₁AR : h₁ ∈ IS ^ (β * (k + 1) - α) * (IZ ⊓ IS ^ α) := hAR (β * (k + 1)) hm ⟨h₁Z, hh₁'⟩
  have hpow : IS ^ (β * (k + 1) - α) ≤ (IS ^ β) ^ k := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by rw [Nat.mul_succ]; omega)
  have hGk : Ideal.map φ ((IS ^ β) ^ k) ≤ Ideal.span {G ^ k} := by
    rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hSle k
  have hb1 : Ideal.map φ (IS ^ (β * (k + 1) - α) * (IZ ⊓ IS ^ α)) ≤
      Ideal.span {G ^ k} * Ideal.map φ IZ := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mono ((Ideal.map_mono hpow).trans hGk) (Ideal.map_mono inf_le_left)
  have hb2 : Ideal.map φ (IZ * (IS ^ β ⊔ IZ) ^ k) ≤ Ideal.span {G ^ k} * Ideal.map φ IZ := by
    rw [Ideal.map_mul, Ideal.map_pow, hD, Ideal.span_singleton_pow, mul_comm]
  rw [← hsum, map_add]
  exact Ideal.add_mem _ (hb1 (Ideal.mem_map_of_mem φ h₁AR)) (hb2 (Ideal.mem_map_of_mem φ hh₂))

/-- Every pulled element of `I_Z` is `G` times an element of the strict ideal. -/
theorem map_le_span_mul_strictIdeal (φ : A →+* R) (IZ IS : Ideal A) (β : ℕ) (G : R)
    (hD : Ideal.map φ (IS ^ β ⊔ IZ) = Ideal.span {G}) :
    Ideal.map φ IZ ≤ Ideal.span {G} * strictIdeal φ IZ (IS ^ β ⊔ IZ) G := by
  rw [Ideal.map_le_iff_le_comap]
  intro z hz
  have hzD : φ z ∈ Ideal.span {G} := hD ▸ Ideal.mem_map_of_mem φ (le_sup_right (a := IS ^ β) hz)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hzD
  rw [Ideal.mem_comap, Ideal.mem_span_singleton_mul]
  refine ⟨w, Ideal.subset_span ⟨1, z, ⟨hz, by rw [pow_one]; exact le_sup_right (a := IS ^ β) hz⟩, ?_⟩,
    by rw [mul_comm]; exact hw⟩
  rw [pow_one, ← hw, mul_comm]

/-- **Hironaka's Lemma 3.2 (total = strict + E once).**  For the sum centre `I_S^β + I_Z` with `β` at least an
Artin–Rees number and regular pulled generator `G`: `h' ∈ strictIdeal ↔ G h' ∈ I_Z R`. -/
theorem strictIdeal_mem_iff_sumCentre (φ : A →+* R) (IZ IS : Ideal A) (α β : ℕ)
    (hαβ : α ≤ β) (hAR : ∀ m, α ≤ m → IZ ⊓ IS ^ m ≤ IS ^ (m - α) * (IZ ⊓ IS ^ α))
    (G : R) (hG : IsRegular G) (hD : Ideal.map φ (IS ^ β ⊔ IZ) = Ideal.span {G}) (a : R) :
    a ∈ strictIdeal φ IZ (IS ^ β ⊔ IZ) G ↔ G * a ∈ Ideal.map φ IZ := by
  constructor
  · intro ha
    refine Submodule.span_induction (p := fun a _ => G * a ∈ Ideal.map φ IZ) ?_ ?_ ?_ ?_ ha
    · rintro h' ⟨k, h, hh, hφ⟩
      cases k with
      | zero =>
        rw [pow_zero, one_mul] at hφ
        rw [← hφ]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem φ hh.1)
      | succ k =>
        obtain ⟨c, hc, hcG⟩ := Ideal.mem_span_singleton_mul.mp
          (map_mem_span_pow_mul φ IZ IS α β hαβ hAR G hD k h hh.1 hh.2)
        have : G * h' = c := (hG.pow k).left (show G ^ k * (G * h') = G ^ k * c by
          rw [hcG, hφ, pow_succ, mul_assoc])
        rw [this]
        exact hc
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact Ideal.add_mem _ hx hy
    · intro r x _ hx
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hx
  · intro ha
    obtain ⟨w, hw, hGw⟩ := Ideal.mem_span_singleton_mul.mp
      (map_le_span_mul_strictIdeal φ IZ IS β G hD ha)
    rw [← hG.left hGw]
    exact hw

/-- The total transform of `Z` is `G` times its strict transform. -/
theorem map_eq_span_mul_strictIdeal (φ : A →+* R) (IZ IS : Ideal A) (α β : ℕ)
    (hαβ : α ≤ β) (hAR : ∀ m, α ≤ m → IZ ⊓ IS ^ m ≤ IS ^ (m - α) * (IZ ⊓ IS ^ α))
    (G : R) (hG : IsRegular G) (hD : Ideal.map φ (IS ^ β ⊔ IZ) = Ideal.span {G}) :
    Ideal.map φ IZ = Ideal.span {G} * strictIdeal φ IZ (IS ^ β ⊔ IZ) G := by
  refine le_antisymm (map_le_span_mul_strictIdeal φ IZ IS β G hD) ?_
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
  exact (strictIdeal_mem_iff_sumCentre φ IZ IS α β hαβ hAR G hG hD w).mp hw

/-- **N5 reformulated.**  `G` is regular modulo the strict ideal iff `(I_Z R : G²) = (I_Z R : G)`. -/
theorem isRegular_mk_strictIdeal_iff (φ : A →+* R) (IZ IS : Ideal A) (α β : ℕ)
    (hαβ : α ≤ β) (hAR : ∀ m, α ≤ m → IZ ⊓ IS ^ m ≤ IS ^ (m - α) * (IZ ⊓ IS ^ α))
    (G : R) (hG : IsRegular G) (hD : Ideal.map φ (IS ^ β ⊔ IZ) = Ideal.span {G}) :
    IsRegular (Ideal.Quotient.mk (strictIdeal φ IZ (IS ^ β ⊔ IZ) G) G) ↔
      ∀ a : R, G * (G * a) ∈ Ideal.map φ IZ → G * a ∈ Ideal.map φ IZ := by
  have hmem := strictIdeal_mem_iff_sumCentre φ IZ IS α β hαβ hAR G hG hD
  constructor
  · intro hreg a ha
    have h1 : Ideal.Quotient.mk (strictIdeal φ IZ (IS ^ β ⊔ IZ) G) G *
        Ideal.Quotient.mk (strictIdeal φ IZ (IS ^ β ⊔ IZ) G) a =
        Ideal.Quotient.mk (strictIdeal φ IZ (IS ^ β ⊔ IZ) G) G * 0 := by
      rw [mul_zero, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hmem]
      exact ha
    have h2 := hreg.left h1
    rw [Ideal.Quotient.eq_zero_iff_mem, hmem] at h2
    exact h2
  · intro hsat
    have hl : IsLeftRegular (Ideal.Quotient.mk (strictIdeal φ IZ (IS ^ β ⊔ IZ) G) G) := by
      intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hxy' : Ideal.Quotient.mk (strictIdeal φ IZ (IS ^ β ⊔ IZ) G) (G * (x - y)) = 0 := by
        rw [map_mul, map_sub, mul_sub]
        exact sub_eq_zero.mpr hxy
      rw [Ideal.Quotient.eq_zero_iff_mem, hmem] at hxy'
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hmem]
      exact hsat _ hxy'
    exact ⟨hl, by intro x y hxy; apply hl; simpa only [mul_comm] using hxy⟩

/-- **N5 reformulated, saturation form.**  The strict ideal is the full `G`-saturation of the total transform
exactly when `(I_Z R : G²) = (I_Z R : G)`. -/
theorem strictIdeal_eq_powerSat_iff (φ : A →+* R) (IZ IS : Ideal A) (α β : ℕ)
    (hαβ : α ≤ β) (hAR : ∀ m, α ≤ m → IZ ⊓ IS ^ m ≤ IS ^ (m - α) * (IZ ⊓ IS ^ α))
    (G : R) (hG : IsRegular G) (hD : Ideal.map φ (IS ^ β ⊔ IZ) = Ideal.span {G}) :
    strictIdeal φ IZ (IS ^ β ⊔ IZ) G = powerSat (Ideal.map φ IZ) G ↔
      ∀ a : R, G * (G * a) ∈ Ideal.map φ IZ → G * a ∈ Ideal.map φ IZ := by
  have hmem := strictIdeal_mem_iff_sumCentre φ IZ IS α β hαβ hAR G hG hD
  constructor
  · intro heq a ha
    have : a ∈ powerSat (Ideal.map φ IZ) G := ⟨2, by rw [pow_two, mul_assoc]; exact ha⟩
    rw [← heq, hmem] at this
    exact this
  · intro hsat
    have hstep : ∀ m : ℕ, ∀ a : R, G ^ (m + 1) * a ∈ Ideal.map φ IZ → G * a ∈ Ideal.map φ IZ := by
      intro m
      induction m with
      | zero => intro a ha; simpa using ha
      | succ m ih =>
        intro a ha
        apply hsat
        apply ih (G * a)
        rw [← mul_assoc, ← pow_succ]
        exact ha
    ext a
    rw [hmem]
    constructor
    · intro ha
      exact ⟨1, by rw [pow_one]; exact ha⟩
    · rintro ⟨m, hm⟩
      exact hstep m a (by rw [pow_succ', mul_assoc]; exact Ideal.mul_mem_left _ G hm)

end SGPT.Unibranch.HironakaG10SbSumCentreStrict
