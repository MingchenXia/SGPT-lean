import SGPT.GAGA.PN2Torus
import SGPT.GAGA.PNSections

/-!
# Laurent expansions of homogeneous functions near the sets `K_s`

Infrastructure of lane SERRE-PN2 (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), plan node PN6 of `claude-serre-pn.tex`.

For `ρ > 0` and a finite set `s` of indices, `openCover ρ s = {z ≠ 0 : |z_j| < ρ |z_i|, i ∈ s}`
is an open cone (the cone over an open neighbourhood of `K_s` in `ℙᴺ`), and `radSet ρ s` is the
open convex set of its positive radii.

* `exists_openCover_subset`: every open cone containing the cone over `K_s = coverSet ρ s`
  contains `openCover ρ' s` for some `ρ' > ρ` (compactness of the unit sphere). So every
  section over `K_s` is holomorphic on some `openCover ρ' s`.
* `laurent_of_homogeneous`: a function `f` holomorphic on `openCover ρ s` (`ρ > 1`, `s ≠ ∅`)
  and homogeneous of degree `n` has a **Laurent expansion** `f(z) = ∑_α C_α z^α` at every point
  with nonzero coordinates, where `C_α = lcoeff f α` is the `α`-th Fourier coefficient on the
  unit torus; the family `C` is `IsLaurent ρ s` (`C_α = 0` unless `α_k ≥ 0` for `k ∉ s`, and
  `∑_α |C_α| r^α < ∞` for the radii `r` of `openCover ρ s`), and `C_α = 0` unless
  `∑_k α_k = n`.
* Conversely (`IsLaurent.differentiableOn`, `lser_smul`), a family `c` with `IsLaurent ρ s c`
  defines the holomorphic function `lser c = ∑_α c_α z^α` on `openCover ρ s` (Weierstrass), and
  it is homogeneous of degree `n` if `c` is supported on `∑ α = n`.
* `IsLaurent.extend`: if `c` is `IsLaurent ρ' (s ∪ {k})` and supported on `α_k ≥ 0`, it is
  `IsLaurent ρ'' s` for `1 < ρ'' < ρ'` (monotonicity of `r ↦ r^α` in `r_k`): the series of
  nonnegative powers of `z_k` converges on the larger set. This is the convergence bookkeeping
  of the contracting homotopy of `PN2Cohomology`.

Blueprint: `claude-serre-pn2.tex`, nodes `claude-serre-pn2:normalize`,
`claude-serre-pn2:laurent`, `claude-serre-pn2:series`.
-/

set_option autoImplicit false

open Set Filter Topology Metric Complex
open scoped Real

noncomputable section

namespace SGPT.GAGA.PN

variable {d : ℕ}

/-! ### The open cones `V_s(ρ)` and their radii -/

/-- The open cone `V_s(ρ) = {z ≠ 0 : |z_j| < ρ |z_i| for i ∈ s and all j}`. -/
def openCover (ρ : ℝ) (s : Finset (Fin d)) : Set (EuclideanSpace ℂ (Fin d)) :=
  {z | z ≠ 0 ∧ ∀ i ∈ s, ∀ j, ‖z j‖ < ρ * ‖z i‖}

/-- The positive radii of `V_s(ρ)`. -/
def radSet (ρ : ℝ) (s : Finset (Fin d)) : Set (Fin d → ℝ) :=
  {r | (∀ k, 0 < r k) ∧ ∀ i ∈ s, ∀ j, r j < ρ * r i}

theorem isOpen_openCover (ρ : ℝ) (s : Finset (Fin d)) : IsOpen (openCover ρ s) := by
  have h : openCover ρ s = {z : EuclideanSpace ℂ (Fin d) | z ≠ 0} ∩
      ⋂ i ∈ s, ⋂ j, {z | ‖z j‖ < ρ * ‖z i‖} := by
    ext z
    simp [openCover]
  rw [h]
  refine isOpen_ne.inter (isOpen_biInter_finset fun i _ => isOpen_iInter_of_finite fun j => ?_)
  exact isOpen_lt (EuclideanSpace.proj j).continuous.norm
    (continuous_const.mul (EuclideanSpace.proj i).continuous.norm)

theorem isCone_openCover (ρ : ℝ) (s : Finset (Fin d)) : IsCone (openCover ρ s) := by
  intro c hc z hz
  refine ⟨smul_ne_zero hc hz.1, fun i hi j => ?_⟩
  have h := hz.2 i hi j
  simp only [PiLp.smul_apply, smul_eq_mul, norm_mul]
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  calc ‖c‖ * ‖z j‖ < ‖c‖ * (ρ * ‖z i‖) := mul_lt_mul_of_pos_left h hc'
    _ = ρ * (‖c‖ * ‖z i‖) := by ring

theorem openCover_subset_ne (ρ : ℝ) (s : Finset (Fin d)) :
    openCover ρ s ⊆ {z | z ≠ 0} :=
  fun _ hz => hz.1

theorem openCover_anti {ρ ρ' : ℝ} (hρ : ρ ≤ ρ') {s t : Finset (Fin d)} (hst : s ⊆ t) :
    openCover ρ t ⊆ openCover ρ' s := by
  intro z hz
  refine ⟨hz.1, fun i hi j => (hz.2 i (hst hi) j).trans_le ?_⟩
  exact mul_le_mul_of_nonneg_right hρ (norm_nonneg _)

theorem coord_ne_zero_of_mem_openCover {ρ : ℝ} {s : Finset (Fin d)}
    {z : EuclideanSpace ℂ (Fin d)} (hz : z ∈ openCover ρ s) {i : Fin d} (hi : i ∈ s) :
    z i ≠ 0 := by
  intro h0
  have := hz.2 i hi i
  rw [h0, norm_zero, mul_zero] at this
  exact lt_irrefl _ this

theorem isOpen_radSet (ρ : ℝ) (s : Finset (Fin d)) : IsOpen (radSet ρ s) := by
  have h : radSet ρ s = (⋂ k, {r : Fin d → ℝ | 0 < r k}) ∩
      ⋂ i ∈ s, ⋂ j, {r | r j < ρ * r i} := by
    ext r
    simp [radSet]
  rw [h]
  refine (isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)).inter
    (isOpen_biInter_finset fun i _ => isOpen_iInter_of_finite fun j => ?_)
  exact isOpen_lt (continuous_apply j) (continuous_const.mul (continuous_apply i))

theorem convex_radSet (ρ : ℝ) (s : Finset (Fin d)) : Convex ℝ (radSet ρ s) := by
  intro r hr r' hr' a b ha hb hab
  refine ⟨fun k => ?_, fun i hi j => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hr.1 k)) (mul_nonneg hb (hr'.1 k).le)
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hr'.1 k
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hr.2 i hi j
    have h2 := hr'.2 i hi j
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_lt_mul_of_pos_left h1 ha', mul_le_mul_of_nonneg_left h2.le hb]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h2

theorem radii_mem_radSet {ρ : ℝ} {s : Finset (Fin d)} {z : EuclideanSpace ℂ (Fin d)}
    (hz : z ∈ openCover ρ s) (hz0 : ∀ k, z k ≠ 0) : radii z ∈ radSet ρ s :=
  ⟨fun k => norm_pos_iff.2 (hz0 k), fun i hi j => hz.2 i hi j⟩

theorem isReinhardtIn_openCover (ρ : ℝ) {s : Finset (Fin d)} (hs : s.Nonempty) :
    IsReinhardtIn (openCover ρ s) (radSet ρ s) where
  isOpen := isOpen_radSet ρ s
  convex := convex_radSet ρ s
  pos := fun r hr => hr.1
  sub := fun z hz => by
    refine ⟨fun h0 => ?_, fun i hi j => hz.2 i hi j⟩
    obtain ⟨i, -⟩ := hs
    have := hz.1 i
    simp [radii, h0] at this

theorem one_mem_radSet {ρ : ℝ} (hρ : 1 < ρ) (s : Finset (Fin d)) :
    (fun _ => (1 : ℝ)) ∈ radSet ρ s :=
  ⟨fun _ => one_pos, fun _ _ _ => by simpa using hρ⟩

theorem radSet_anti {ρ ρ' : ℝ} (hρ : ρ ≤ ρ') {s t : Finset (Fin d)} (hst : s ⊆ t) :
    radSet ρ t ⊆ radSet ρ' s :=
  fun _ hr => ⟨hr.1, fun i hi j => (hr.2 i (hst hi) j).trans_le
    (mul_le_mul_of_nonneg_right hρ (hr.1 i).le)⟩

/-! ### Normalization of neighbourhoods of `K_s` -/

section Normalize

variable {N : ℕ}

theorem coverSet_subset_openCover {ρ ρ' : ℝ} (hρ : ρ < ρ') (s : Finset (Fin (N + 1))) :
    coverSet ρ s ⊆ openCover ρ' s := by
  intro z hz
  refine ⟨hz.1, fun i hi j => ?_⟩
  have hzi : z i ≠ 0 := by
    intro h0
    apply hz.1
    ext j
    have := hz.2 i hi j
    rw [h0, norm_zero, mul_zero] at this
    simpa using norm_le_zero_iff.1 this
  exact (hz.2 i hi j).trans_lt (mul_lt_mul_of_pos_right hρ (norm_pos_iff.2 hzi))

/-- **Normalization**: an open cone containing (the cone over) `K_s` contains `V_s(ρ')` for some
`ρ' > ρ`. -/
theorem exists_openCover_subset {ρ : ℝ} {s : Finset (Fin (N + 1))} (hs : s.Nonempty)
    {U : Set (ConeSpace N)} (hU : IsOpen U) (hUc : IsCone U) (hKU : coverSet ρ s ⊆ U) :
    ∃ ρ' > ρ, openCover ρ' s ⊆ U := by
  classical
  set C : Set (ConeSpace N) := sphere 0 1 \ U with hCdef
  have hCc : IsCompact C := (isCompact_sphere 0 1).diff hU
  set φ : ConeSpace N → ℝ := fun z =>
    s.sup' hs fun i => Finset.univ.sup' Finset.univ_nonempty fun j => ‖z j‖ - ρ * ‖z i‖
    with hφdef
  have hφc : Continuous φ :=
    Continuous.finset_sup'_apply hs fun i _ => Continuous.finset_sup'_apply _ fun j _ =>
      (EuclideanSpace.proj j).continuous.norm.sub
        (continuous_const.mul (EuclideanSpace.proj i).continuous.norm)
  have hφpos : ∀ z ∈ C, 0 < φ z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have := hz.1
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
      exact zero_ne_one this
    have hzK : ¬(z ≠ 0 ∧ ∀ i ∈ s, ∀ j, ‖z j‖ ≤ ρ * ‖z i‖) := fun h => hz.2 (hKU h)
    push Not at hzK
    obtain ⟨i, hi, j, hij⟩ := hzK hz0
    calc 0 < ‖z j‖ - ρ * ‖z i‖ := by linarith
      _ ≤ Finset.univ.sup' Finset.univ_nonempty fun j => ‖z j‖ - ρ * ‖z i‖ :=
        Finset.le_sup' (fun j => ‖z j‖ - ρ * ‖z i‖) (Finset.mem_univ j)
      _ ≤ φ z := Finset.le_sup'
        (fun i => Finset.univ.sup' Finset.univ_nonempty fun j => ‖z j‖ - ρ * ‖z i‖) hi
  have hm : ∃ m > 0, ∀ z ∈ C, m ≤ φ z := by
    rcases C.eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, fun z hz => by rw [hC] at hz; exact hz.elim⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hCc.exists_isMinOn hC hφc.continuousOn
      exact ⟨φ z₀, hφpos z₀ hz₀, fun z hz => hmin hz⟩
  obtain ⟨m, hm0, hmC⟩ := hm
  refine ⟨ρ + m, by linarith, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := hz.1
  have hnz : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)
  set w : ConeSpace N := ((‖z‖ : ℂ)⁻¹) • z with hwdef
  have hw : w ∈ openCover (ρ + m) s := isCone_openCover _ s _ (inv_ne_zero hnz) z hz
  have hwz : (‖z‖ : ℂ) • w = z := by rw [hwdef, smul_inv_smul₀ hnz]
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.2 hz0)]
  have hwU : w ∈ U := by
    by_contra hwU
    have hwC : w ∈ C := ⟨by rw [mem_sphere_zero_iff_norm]; exact hw1, hwU⟩
    have h1 := hmC w hwC
    obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup' hs
      (fun i => Finset.univ.sup' Finset.univ_nonempty fun j => ‖w j‖ - ρ * ‖w i‖)
    obtain ⟨j, -, hjeq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => ‖w j‖ - ρ * ‖w i‖)
    have h2 : m ≤ ‖w j‖ - ρ * ‖w i‖ := by
      have : φ w = ‖w j‖ - ρ * ‖w i‖ := by
        simp only [hφdef]
        rw [hieq, hjeq]
      linarith
    have h3 : ‖w i‖ ≤ 1 := (PiLp.norm_apply_le w i).trans hw1.le
    have h4 := hw.2 i hi j
    nlinarith [norm_nonneg (w i)]
  rw [← hwz]
  exact hUc _ hnz w hwU

end Normalize

/-! ### Laurent families -/

/-- `c` is a *Laurent family* for `V_s(ρ)`: `c_α = 0` unless `α_k ≥ 0` for all `k ∉ s`, and
`∑_α |c_α| r^α < ∞` for all radii `r` of `V_s(ρ)`. -/
def IsLaurent (ρ : ℝ) (s : Finset (Fin d)) (c : (Fin d → ℤ) → ℂ) : Prop :=
  (∀ α, c α ≠ 0 → ∀ k ∉ s, 0 ≤ α k) ∧
    ∀ r ∈ radSet ρ s, Summable fun α => ‖c α‖ * rmono α r

/-- The sum `∑_α c_α z^α` of a Laurent family. -/
def lser (c : (Fin d → ℤ) → ℂ) (z : EuclideanSpace ℂ (Fin d)) : ℂ :=
  ∑' α, c α * mono α z

/-- The Laurent coefficients of `f`, computed on the unit torus. -/
def lcoeff (f : EuclideanSpace ℂ (Fin d) → ℂ) (α : Fin d → ℤ) : ℂ :=
  lcoeffAt f (fun _ => 1) α

theorem mono_one_rpt (α : Fin d → ℤ) : mono α (rpt fun _ => 1) = 1 := by
  simp [mono]

theorem lcoeff_eq_tcoeff (f : EuclideanSpace ℂ (Fin d) → ℂ) (α : Fin d → ℤ) :
    lcoeff f α = tcoeff f (rpt fun _ => 1) α := by
  rw [lcoeff, lcoeffAt, mono_one_rpt, mul_one]

theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroupWithZero G] {a : G} (ha : a ≠ 0)
    {ι : Type*} (s : Finset ι) (f : ι → ℤ) : ∏ k ∈ s, a ^ f k = a ^ ∑ k ∈ s, f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.prod_insert hk, Finset.sum_insert hk, ih, zpow_add₀ ha]

theorem mono_smul (α : Fin d → ℤ) {a : ℂ} (ha : a ≠ 0) (z : EuclideanSpace ℂ (Fin d)) :
    mono α (a • z) = a ^ (∑ k, α k) * mono α z := by
  simp only [mono, PiLp.smul_apply, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib,
    prod_zpow_eq_zpow_sum ha]

theorem lser_smul {c : (Fin d → ℤ) → ℂ} {n : ℤ} (hn : ∀ α, c α ≠ 0 → ∑ k, α k = n) {a : ℂ}
    (ha : a ≠ 0) (z : EuclideanSpace ℂ (Fin d)) : lser c (a • z) = a ^ n * lser c z := by
  unfold lser
  rw [← tsum_mul_left]
  congr 1
  funext α
  by_cases hα : c α = 0
  · simp [hα]
  · rw [mono_smul α ha, hn α hα]
    ring

section LaurentFamily

variable {ρ : ℝ} {s : Finset (Fin d)} {c c' : (Fin d → ℤ) → ℂ}

theorem IsLaurent.anti (hc : IsLaurent ρ s c) {ρ' : ℝ} (hρ : ρ' ≤ ρ) {t : Finset (Fin d)}
    (hst : s ⊆ t) : IsLaurent ρ' t c :=
  ⟨fun α hα k hk => hc.1 α hα k fun h => hk (hst h), fun r hr =>
    hc.2 r (radSet_anti hρ hst hr)⟩

theorem IsLaurent.of_subfamily (hc : IsLaurent ρ s c) (h : ∀ α, c' α ≠ 0 → c' α = c α) :
    IsLaurent ρ s c' := by
  refine ⟨fun α hα => hc.1 α (by rw [← h α hα]; exact hα), fun r hr => ?_⟩
  refine (hc.2 r hr).of_nonneg_of_le (fun α => mul_nonneg (norm_nonneg _)
    (rmono_pos α hr.1).le) fun α => ?_
  by_cases hα : c' α = 0
  · rw [hα, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (rmono_pos α hr.1).le
  · rw [h α hα]

theorem IsLaurent.add (hc : IsLaurent ρ s c) (hc' : IsLaurent ρ s c') :
    IsLaurent ρ s (c + c') := by
  refine ⟨fun α hα k hk => ?_, fun r hr => ?_⟩
  · by_cases h1 : c α = 0
    · have h2 : c' α ≠ 0 := by simpa [h1] using hα
      exact hc'.1 α h2 k hk
    · exact hc.1 α h1 k hk
  · refine ((hc.2 r hr).add (hc'.2 r hr)).of_nonneg_of_le (fun α => mul_nonneg (norm_nonneg _)
      (rmono_pos α hr.1).le) fun α => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (rmono_pos α hr.1).le

theorem IsLaurent.const_mul (hc : IsLaurent ρ s c) (a : ℂ) :
    IsLaurent ρ s fun α => a * c α := by
  refine ⟨fun α hα => hc.1 α (right_ne_zero_of_mul hα), fun r hr => ?_⟩
  simp only [norm_mul, mul_assoc]
  exact (hc.2 r hr).mul_left _

theorem isLaurent_zero : IsLaurent ρ s (0 : (Fin d → ℤ) → ℂ) :=
  ⟨fun α hα => (hα rfl).elim, fun r _ => by simp⟩

theorem IsLaurent.sum {κ : Type*} (u : Finset κ) {c : κ → (Fin d → ℤ) → ℂ}
    (hc : ∀ k ∈ u, IsLaurent ρ s (c k)) : IsLaurent ρ s fun α => ∑ k ∈ u, c k α := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact isLaurent_zero
  | insert k u hk ih =>
      have h := (hc k (Finset.mem_insert_self k u)).add
        (ih fun k' hk' => hc k' (Finset.mem_insert_of_mem hk'))
      convert h using 1
      funext α
      simp [Finset.sum_insert hk]

/-- **Extension of the domain of convergence.** A Laurent family for `V_{s ∪ k}(ρ')` with only
nonnegative powers of `z_k` is a Laurent family for `V_s(ρ'')`, `1 < ρ'' < ρ'`. -/
theorem IsLaurent.extend {ρ' ρ'' : ℝ} {k : Fin d} (hc : IsLaurent ρ' (insert k s) c)
    (hk : k ∉ s) (hs : s.Nonempty) (h1 : 1 < ρ'') (h2 : ρ'' < ρ')
    (hck : ∀ α, c α ≠ 0 → 0 ≤ α k) : IsLaurent ρ'' s c := by
  classical
  refine ⟨fun α hα j hj => ?_, fun r hr => ?_⟩
  · by_cases hjk : j = k
    · rw [hjk]
      exact hck α hα
    · exact hc.1 α hα j (by simp [hjk, hj])
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨hs.choose, Finset.mem_univ _⟩
  set m : ℝ := Finset.univ.sup' hne r with hmdef
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' hne r
  have hρ''0 : 0 < ρ'' := by linarith
  set r' : Fin d → ℝ := Function.update r k (max (r k) (m / ρ'')) with hr'def
  have hr'k : r' k = max (r k) (m / ρ'') := by simp [hr'def]
  have hr'j : ∀ j, j ≠ k → r' j = r j := fun j hj => by simp [hr'def, hj]
  have hr'pos : 0 < r' k := (hr.1 k).trans_le (by rw [hr'k]; exact le_max_left _ _)
  have hr' : r' ∈ radSet ρ' (insert k s) := by
    refine ⟨fun j => ?_, fun i hi j => ?_⟩
    · by_cases hj : j = k
      · rw [hj]
        exact hr'pos
      · rw [hr'j j hj]
        exact hr.1 j
    · rcases Finset.mem_insert.1 hi with hik | hi
      · rw [hik]
        by_cases hj : j = k
        · rw [hj]
          exact lt_mul_of_one_lt_left hr'pos (h1.trans h2)
        · rw [hr'j j hj]
          have hjm : r j ≤ m := Finset.le_sup' r (Finset.mem_univ j)
          have : m ≤ ρ'' * r' k := by
            rw [hr'k]
            calc m = ρ'' * (m / ρ'') := by field_simp
              _ ≤ ρ'' * max (r k) (m / ρ'') :=
                mul_le_mul_of_nonneg_left (le_max_right _ _) hρ''0.le
          calc r j ≤ ρ'' * r' k := hjm.trans this
            _ < ρ' * r' k := mul_lt_mul_of_pos_right h2 hr'pos
      · have hik : i ≠ k := fun h => hk (h ▸ hi)
        rw [hr'j i hik]
        have hri := hr.1 i
        by_cases hj : j = k
        · rw [hj, hr'k]
          refine max_lt ?_ ?_
          · exact (hr.2 i hi k).trans_le (mul_le_mul_of_nonneg_right h2.le hri.le)
          · rw [div_lt_iff₀ hρ''0]
            calc m = r j₀ := hj₀
              _ < ρ'' * r i := hr.2 i hi j₀
              _ = r i * ρ'' := by ring
              _ ≤ ρ' * r i * ρ'' := by
                refine mul_le_mul_of_nonneg_right ?_ hρ''0.le
                nlinarith
        · rw [hr'j j hj]
          exact (hr.2 i hi j).trans_le (mul_le_mul_of_nonneg_right h2.le hri.le)
  refine (hc.2 r' hr').of_nonneg_of_le (fun α => mul_nonneg (norm_nonneg _)
    (rmono_pos α hr.1).le) fun α => ?_
  by_cases hα : c α = 0
  · rw [hα, norm_zero, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine Finset.prod_le_prod (fun j _ => (zpow_pos (hr.1 j) _).le) fun j _ => ?_
  by_cases hj : j = k
  · rw [hj, hr'k]
    exact zpow_le_zpow_left₀ (hck α hα) (hr.1 k).le (le_max_left _ _)
  · rw [hr'j j hj]

/-- Points of `V_s(ρ)` and a neighbourhood with a summable dominating sequence. -/
theorem IsLaurent.local_bound (hc : IsLaurent ρ s c) (hρ : 0 ≤ ρ)
    {z₀ : EuclideanSpace ℂ (Fin d)} (hz₀ : z₀ ∈ openCover ρ s) :
    ∃ η > 0, ∃ u : (Fin d → ℤ) → ℝ, Summable u ∧
      ∀ z ∈ ball z₀ η, (∀ k ∈ s, z k ≠ 0) ∧ ∀ α, ‖c α * mono α z‖ ≤ u α := by
  classical
  set a : Fin d → ℝ := radii z₀ with hadef
  have ha0 : ∀ i ∈ s, 0 < a i := fun i hi => norm_pos_iff.2 (coord_ne_zero_of_mem_openCover hz₀ hi)
  -- a small `η`
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), (∀ i ∈ s, η < a i) ∧
      ∀ i ∈ s, ∀ j, a j + η < ρ * (a i - η) := by
    refine Filter.Eventually.and ?_ ?_
    · refine (Filter.eventually_all_finset s).2 fun i hi => ?_
      exact (eventually_lt_nhds (ha0 i hi)).filter_mono nhdsWithin_le_nhds
    · refine (Filter.eventually_all_finset s).2 fun i hi => ?_
      refine Filter.eventually_all.2 fun j => ?_
      have hcont : Continuous fun η : ℝ => ρ * (a i - η) - (a j + η) := by fun_prop
      have h0 : 0 < ρ * (a i - 0) - (a j + 0) := by
        have := hz₀.2 i hi j
        simp only [sub_zero, add_zero]
        show 0 < ρ * ‖z₀ i‖ - ‖z₀ j‖
        linarith
      have : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < ρ * (a i - η) - (a j + η) :=
        ((hcont.tendsto 0).eventually (eventually_gt_nhds h0)).filter_mono nhdsWithin_le_nhds
      exact this.mono fun η hη => by linarith
  obtain ⟨η, hηP, hη0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hη0 : 0 < η := hη0
  set corner : (Fin d → Bool) → Fin d → ℝ := fun ε k =>
    if ε k then a k + η else if k ∈ s then a k - η else a k + η with hcdef
  have hcorner_ge : ∀ ε k, a k - η ≤ corner ε k := fun ε k => by
    simp only [hcdef]; split_ifs <;> linarith
  have hcorner_le : ∀ ε k, corner ε k ≤ a k + η := fun ε k => by
    simp only [hcdef]; split_ifs <;> linarith
  have hcorner : ∀ ε, corner ε ∈ radSet ρ s := by
    intro ε
    refine ⟨fun k => ?_, fun i hi j => ?_⟩
    · have hak : 0 ≤ a k := norm_nonneg _
      simp only [hcdef]
      split_ifs with h1 h2
      · linarith
      · linarith [hηP.1 k h2]
      · linarith
    · calc corner ε j ≤ a j + η := hcorner_le ε j
        _ < ρ * (a i - η) := hηP.2 i hi j
        _ ≤ ρ * corner ε i := mul_le_mul_of_nonneg_left (hcorner_ge ε i) hρ
  refine ⟨η, hη0, fun α => ∑ ε, ‖c α‖ * rmono α (corner ε),
    summable_sum fun ε _ => hc.2 _ (hcorner ε), fun z hz => ?_⟩
  have hzk : ∀ k, |‖z k‖ - a k| < η := fun k => by
    have h1 : ‖z k - z₀ k‖ ≤ ‖z - z₀‖ := by
      simpa using PiLp.norm_apply_le (z - z₀) k
    rw [mem_ball, dist_eq_norm] at hz
    exact (abs_norm_sub_norm_le (z k) (z₀ k)).trans_lt (h1.trans_lt hz)
  have hzs : ∀ k ∈ s, z k ≠ 0 := fun k hk h0 => by
    have := hzk k
    rw [h0, norm_zero, zero_sub, abs_neg, abs_of_pos (ha0 k hk)] at this
    linarith [hηP.1 k hk]
  refine ⟨hzs, fun α => ?_⟩
  by_cases hα : c α = 0
  · rw [hα, zero_mul, norm_zero]
    exact Finset.sum_nonneg fun ε _ => mul_nonneg (norm_nonneg _)
      (rmono_pos α (hcorner ε).1).le
  set ε : Fin d → Bool := fun k => decide (0 ≤ α k)
  refine le_trans ?_ (Finset.single_le_sum (f := fun ε => ‖c α‖ * rmono α (corner ε))
    (fun ε _ => mul_nonneg (norm_nonneg _) (rmono_pos α (hcorner ε).1).le) (Finset.mem_univ ε))
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [mono, rmono, norm_prod, norm_zpow]
  refine Finset.prod_le_prod (fun k _ => zpow_nonneg (norm_nonneg _) _) fun k _ => ?_
  have hk := hzk k
  rw [abs_lt] at hk
  by_cases hαk : 0 ≤ α k
  · have hck : corner ε k = a k + η := by simp [hcdef, ε, hαk]
    rw [hck]
    exact zpow_le_zpow_left₀ hαk (norm_nonneg _) (by linarith)
  · have hks : k ∈ s := by
      by_contra hks
      exact hαk (hc.1 α hα k hks)
    have hck : corner ε k = a k - η := by simp [hcdef, ε, hαk, hks]
    rw [hck]
    push Not at hαk
    have hpos : 0 < a k - η := by linarith [hηP.1 k hks]
    have hle : a k - η ≤ ‖z k‖ := by linarith
    have key : ∀ x : ℝ, x ^ α k = x⁻¹ ^ (-α k) := fun x => by rw [inv_zpow', neg_neg]
    rw [key, key (a k - η)]
    exact zpow_le_zpow_left₀ (by linarith) (inv_nonneg.2 (norm_nonneg _))
      (inv_anti₀ hpos hle)

theorem IsLaurent.summable_at (hc : IsLaurent ρ s c) (hρ : 0 ≤ ρ)
    {z : EuclideanSpace ℂ (Fin d)} (hz : z ∈ openCover ρ s) :
    Summable fun α => c α * mono α z := by
  obtain ⟨η, hη, u, hu, hb⟩ := hc.local_bound hρ hz
  exact Summable.of_norm_bounded hu fun α => (hb z (mem_ball_self hη)).2 α

theorem IsLaurent.hasSum_lser (hc : IsLaurent ρ s c) (hρ : 0 ≤ ρ)
    {z : EuclideanSpace ℂ (Fin d)} (hz : z ∈ openCover ρ s) :
    HasSum (fun α => c α * mono α z) (lser c z) :=
  (hc.summable_at hρ hz).hasSum

theorem differentiableAt_mono' (α : Fin d → ℤ) {w : EuclideanSpace ℂ (Fin d)}
    (hw : ∀ k, w k ≠ 0 ∨ 0 ≤ α k) : DifferentiableAt ℂ (mono α) w := by
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      DifferentiableAt ℂ (fun z : EuclideanSpace ℂ (Fin d) => z k ^ α k) w := fun k _ =>
    (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).differentiableAt.zpow (hw k)
  exact (HasFDerivAt.finsetProd fun k hk' => (hk k hk').hasFDerivAt).differentiableAt

/-- **Weierstrass**: the sum of a Laurent family is holomorphic on `V_s(ρ)`. -/
theorem IsLaurent.differentiableOn (hc : IsLaurent ρ s c) (hρ : 0 ≤ ρ) :
    DifferentiableOn ℂ (lser c) (openCover ρ s) := by
  classical
  intro z₀ hz₀
  obtain ⟨η, hη, u, hu, hb⟩ := hc.local_bound hρ hz₀
  have hunif := tendstoUniformlyOn_tsum hu fun α z hz => (hb z hz).2 α
  set box : ℕ → Finset (Fin d → ℤ) := fun m =>
    Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m with hboxdef
  have hbox : Tendsto box atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun m m' hmm' => ?_) fun α => ?_
    · intro α hα
      rw [Fintype.mem_piFinset] at hα ⊢
      intro k
      have := hα k
      rw [Finset.mem_Icc] at this ⊢
      have : (m : ℤ) ≤ m' := by exact_mod_cast hmm'
      constructor <;> linarith [this]
    · refine ⟨∑ k, (α k).natAbs, Fintype.mem_piFinset.2 fun k => ?_⟩
      have h1 : (α k).natAbs ≤ ∑ k, (α k).natAbs :=
        Finset.single_le_sum (f := fun k => (α k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ k)
      have h2 : |α k| ≤ ((∑ k, (α k).natAbs : ℕ) : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h1
      exact Finset.mem_Icc.2 (abs_le.1 h2)
  have hunif' : TendstoUniformlyOn (fun m z => ∑ α ∈ box m, c α * mono α z) (lser c) atTop
      (ball z₀ η) := fun v hv => hbox.eventually (hunif v hv)
  have hdiff : ∀ m, DifferentiableOn ℂ (fun z => ∑ α ∈ box m, c α * mono α z) (ball z₀ η) := by
    intro m z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun α _ => ?_
    by_cases hα : c α = 0
    · simp only [hα, zero_mul]
      exact differentiableAt_const _
    · refine (differentiableAt_mono' α fun k => ?_).const_mul _
      by_cases hk : k ∈ s
      · exact Or.inl ((hb z hz).1 k hk)
      · exact Or.inr (hc.1 α hα k hk)
  exact (SGPT.Foundations.Analysis.FirstPass.differentiableAt_of_tendstoUniformlyOn_ball hη
    (Eventually.of_forall hdiff) hunif').differentiableWithinAt

end LaurentFamily

/-! ### Laurent expansion of homogeneous functions near `K_s` -/

section Homogeneous

variable {ρ : ℝ} {s : Finset (Fin d)} {f : EuclideanSpace ℂ (Fin d) → ℂ} {n : ℤ}

theorem rmono_update_one (α : Fin d → ℤ) (k : Fin d) (t : ℝ) :
    rmono α (Function.update (fun _ => (1 : ℝ)) k t) = t ^ α k := by
  classical
  unfold rmono
  rw [Finset.prod_eq_single k (fun j _ hj => by simp [Function.update_of_ne hj]) (by simp)]
  simp

/-- **Laurent expansion of homogeneous functions.** Let `ρ > 1`, `s ≠ ∅`, and let `f` be
holomorphic on `V_s(ρ)` and homogeneous of degree `n`. Then the Fourier coefficients
`C_α = lcoeff f α` on the unit torus form a Laurent family for `V_s(ρ)`, `C_α = 0` unless
`∑_k α_k = n`, and `f(z) = ∑_α C_α z^α` at every point of `V_s(ρ)` with nonzero coordinates. -/
theorem laurent_of_homogeneous (hρ : 1 < ρ) (hs : s.Nonempty)
    (hf : DifferentiableOn ℂ f (openCover ρ s))
    (hhom : ∀ z ∈ openCover ρ s, ∀ a : ℂ, a ≠ 0 → f (a • z) = a ^ n * f z) :
    IsLaurent ρ s (lcoeff f) ∧ (∀ α, lcoeff f α ≠ 0 → ∑ k, α k = n) ∧
      ∀ z ∈ openCover ρ s, (∀ k, z k ≠ 0) → HasSum (fun α => lcoeff f α * mono α z) (f z) := by
  classical
  have hU := isOpen_openCover ρ s
  have hS := isReinhardtIn_openCover ρ hs
  have h1 := one_mem_radSet hρ s
  refine ⟨⟨fun α hα k hk => ?_, fun r hr => summable_lcoeffAt hU hf hS h1 hr⟩, fun α hα => ?_,
    fun z hz hz0 => hasSum_lcoeffAt hU hf hS h1 (radii_mem_radSet hz hz0)⟩
  · -- negative powers of `z_k`, `k ∉ s`, do not occur
    by_contra hneg
    push Not at hneg
    obtain ⟨i, hi⟩ := hs
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    set Q : Set (EuclideanSpace ℂ (Fin d)) := {z | ∀ j, z j ∈
      (if j = k then closedBall (0 : ℂ) 1 else sphere (0 : ℂ) 1)} with hQdef
    have hQc : IsCompact Q := by
      have h : IsCompact ((EuclideanSpace.equiv (Fin d) ℂ).toHomeomorph ⁻¹'
          (Set.univ.pi fun j => if j = k then closedBall (0 : ℂ) 1 else sphere (0 : ℂ) 1)) :=
        (EuclideanSpace.equiv (Fin d) ℂ).toHomeomorph.isCompact_preimage.2
          (isCompact_univ_pi fun j => by
            split_ifs
            · exact isCompact_closedBall 0 1
            · exact isCompact_sphere 0 1)
      convert h using 1
      ext z
      simp [hQdef]
    have hQU : Q ⊆ openCover ρ s := by
      intro z hz
      have hzi : ‖z i‖ = 1 := by
        have := hz i
        rw [if_neg hik, mem_sphere_zero_iff_norm] at this
        exact this
      have hzj : ∀ j, ‖z j‖ ≤ 1 := fun j => by
        have := hz j
        split_ifs at this
        · exact mem_closedBall_zero_iff.1 this
        · exact (mem_sphere_zero_iff_norm.1 this).le
      refine ⟨fun h0 => ?_, fun i' hi' j => ?_⟩
      · rw [h0] at hzi
        simp at hzi
      · have hi'k : i' ≠ k := fun h => hk (h ▸ hi')
        have hzi' : ‖z i'‖ = 1 := by
          have := hz i'
          rw [if_neg hi'k, mem_sphere_zero_iff_norm] at this
          exact this
        rw [hzi', mul_one]
        exact (hzj j).trans_lt hρ
    obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuousOn (hf.continuousOn.mono hQU)
    have hbound : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖lcoeff f α‖ * t ^ α k ≤ M := by
      intro t ht0 ht1
      set r : Fin d → ℝ := Function.update (fun _ => (1 : ℝ)) k t
      have hr : r ∈ radSet ρ s := by
        refine ⟨fun j => ?_, fun i' hi' j => ?_⟩
        · by_cases hj : j = k
          · subst hj; simpa [r] using ht0
          · simp [r, hj]
        · have hi'k : i' ≠ k := fun h => hk (h ▸ hi')
          have hrj : r j ≤ 1 := by
            by_cases hj : j = k
            · subst hj; simpa [r] using ht1
            · simp [r, hj]
          simp only [r, Function.update_of_ne hi'k, mul_one]
          exact hrj.trans_lt hρ
      have := norm_lcoeffAt_mul_le hU hf hS h1 hr (M := M) (fun x => hM _ (by
        intro j
        rw [tpt_apply, rpt_apply]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, mem_closedBall_zero_iff, norm_mul, norm_fourier_one, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
          simp only [r, Function.update_self]
          rw [abs_of_pos ht0]
          exact ht1
        · rw [if_neg hj, mem_sphere_zero_iff_norm, norm_mul, norm_fourier_one, mul_one]
          simp [r, hj])) α
      rwa [rmono_update_one] at this
    have hle : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖lcoeff f α‖ ≤ M * t := by
      intro t ht0 ht1
      have h2 := hbound t ht0 ht1
      have h3 : t⁻¹ ≤ t ^ α k := by
        have h4 : t ^ α k = (t⁻¹) ^ (-α k) := by rw [inv_zpow', neg_neg]
        rw [h4]
        have h5 : 1 ≤ t⁻¹ := one_le_inv_iff₀.2 ⟨ht0, ht1⟩
        calc t⁻¹ = t⁻¹ ^ (1 : ℤ) := (zpow_one _).symm
          _ ≤ t⁻¹ ^ (-α k) := zpow_le_zpow_right₀ h5 (by linarith)
      have h6 : ‖lcoeff f α‖ * t⁻¹ ≤ M :=
        (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
      rw [mul_inv_le_iff₀ ht0] at h6
      linarith
    have hlim : Tendsto (fun t : ℝ => M * t) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => M * t) (𝓝 0) (𝓝 (M * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖lcoeff f α‖ ≤ M * t := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      exact hle t ht.1 ht.2.le
    have h0 := ge_of_tendsto hlim hev
    exact hα (norm_le_zero_iff.1 h0)
  · -- homogeneity
    set two : Fin d → ℝ := fun _ => 2
    have h2 : two ∈ radSet ρ s := ⟨fun _ => two_pos, fun _ _ _ => by
      simp only [two]; nlinarith⟩
    have hsmul : rpt two = (2 : ℂ) • rpt (fun _ => (1 : ℝ)) := by
      ext k
      simp [two]
    have hA := tcoeff_eq_lcoeffAt hU hf hS h1 h2 α
    rw [hsmul, tcoeff_smul_real f _ 2 (2 ^ n) (fun x => hhom _ (hS.tpt_mem h1 x) 2 two_ne_zero),
      ← lcoeff_eq_tcoeff, ← hsmul] at hA
    have hm : mono α (rpt two) = 2 ^ (∑ k, α k) := by
      simp only [mono, rpt_apply, two]
      push_cast
      exact prod_zpow_eq_zpow_sum two_ne_zero _ _
    rw [hm, lcoeff, mul_comm] at hA
    have hA' : (2 : ℂ) ^ n = 2 ^ (∑ k, α k) := mul_left_cancel₀ hα hA
    have hn : ((2 : ℝ) ^ n : ℝ) = 2 ^ (∑ k, α k) := by
      have := congrArg norm hA'
      simpa [norm_zpow] using this
    exact (zpow_right_injective₀ two_pos (by norm_num) hn).symm

end Homogeneous

/-! ### Density of the points with nonzero coordinates -/

theorem dense_coord_ne_zero : Dense {z : EuclideanSpace ℂ (Fin d) | ∀ k, z k ≠ 0} := by
  have h : {z : EuclideanSpace ℂ (Fin d) | ∀ k, z k ≠ 0} =
      ⋂ k, (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ) ⁻¹' {0}ᶜ := by
    ext z
    simp
  rw [h]
  refine dense_iInter_of_isOpen (fun k => isOpen_compl_singleton.preimage
    (EuclideanSpace.proj k).continuous) fun k => ?_
  refine (dense_compl_singleton (0 : ℂ)).preimage ?_
  refine LinearMap.isOpenMap_of_finiteDimensional
    (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ).toLinearMap
    fun w => ⟨EuclideanSpace.single k w, by simp⟩

/-- Two functions continuous on an open set which agree at its points with nonzero
coordinates agree on it. -/
theorem eqOn_of_eqOn_coord_ne_zero {f g : EuclideanSpace ℂ (Fin d) → ℂ}
    {W : Set (EuclideanSpace ℂ (Fin d))} (hW : IsOpen W) (hf : ContinuousOn f W)
    (hg : ContinuousOn g W) (h : ∀ z ∈ W, (∀ k, z k ≠ 0) → f z = g z) : EqOn f g W :=
  EqOn.of_subset_closure (s := W ∩ {z | ∀ k, z k ≠ 0}) (fun z hz => h z hz.1 hz.2) hf hg
    inter_subset_left (dense_coord_ne_zero.open_subset_closure_inter hW)

end SGPT.GAGA.PN
