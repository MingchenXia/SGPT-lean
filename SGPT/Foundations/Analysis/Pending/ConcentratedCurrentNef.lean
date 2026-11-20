import SGPT.Foundations.Analysis.Pending.ConcentratedCurrent
import SGPT.Foundations.Analysis.Pending.YauTheoremInterface
import SGPT.Foundations.Analysis.Pending.DiagonalTangentialReduction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A current with the intersection numbers of `a^p` and mass on `Y` (Boucksom, Lemma 4.12)

Blueprint `bou:concentrated-current-connected` (`blueprint/src/analytic.tex`; TN.5, goal 2 of TN-CLASSICAL run 0249), the corrected
form of `bou:concentrated-current`.  Sources: Boucksom, Lemma 4.12 and its proof (`bou02-volume:4.12`); Demailly--Păun,
Proposition 2.6 (`dp04-kahler-cone:2.6`).

Let `(M, ω)` be a compact **connected** Kähler manifold of dimension `N = d + p`, `p ≥ 1`.  For `0 < ε ≤ 1` let
`ω_ε = ω + ddᶜ f_ε ≥ ω/2` and let `V_ε` be sets, decreasing as `ε ↓ 0`, with `⋂_ε closure V_ε ⊆ Y`, and `K` compact with
`∫_{K ∩ V_ε} ω_ε^p ∧ ω^d ≥ δ > 0` for every `ε`.  Then for every nef class `a = {A}` there is a closed positive current `T` of
bidimension `(d, d)` with the intersection numbers of `a^p`,

  `T(β₁ ∧ ⋯ ∧ β_d) = ∫_M β₁ ∧ ⋯ ∧ β_d ∧ A^p` for all closed real `(1,1)`-forms `βᵢ` (`HasClassIntersections`),

and

  `∫_{K ∩ Y} T ∧ ω^d ≥ (1 / (2^{N+1} N!)) · (a^N / ∫_M ω^N) · δ² / ((a + {ω})^d · {ω}^p)`

(`exists_concentratedCurrent_of_nef`).

**Differences with `bou:concentrated-current` as written.**
* Connectedness of `M` is assumed.  Without it the statement is false: on `M₁ ⊔ M₂` with `a = 0` on `M₁` and `a` Kähler on `M₂`,
  and mass of `ω_ε^N` concentrating near a point of `Y ⊆ M₁` (`p = N`), every closed positive current in `a^N` has no mass on `M₁`.
  The proof uses Yau's theorem, which needs connectedness.
* "`T` in `a^p`" is stated through the intersection numbers with products of closed `(1,1)`-forms; the library has no
  cohomology class of a `(p, p)`-current.  This is what Boucksom's use of the lemma needs: the push-forward to `X` of
  `T ∧ p₂^*ω` pairs only with such products.
* The open-ness of `V_ε` and the closedness of `Y` are not needed.

**Route.**  For `ε_k = 1/(k+1)`: the nef correction `h_k` of `A` at `ε_k/2` makes `B_k = A + ε_k ω + ddᶜh_k` Kähler; Yau's theorem
(`YauTheorem.exists_kahler_mongeAmpere_eq_smul`) gives `α_k = B_k + ddᶜφ_k` Kähler with `α_k^N = c_k ω_{ε_k}^N`.  Then
`ConcentratedCurrent.exists_concentratedCurrent` with `S_k = K ∩ V_{ε_k}`, `F_j = K ∩ closure V_{ε_j}`, `P₀ = a^N`,
`M₀ = (a + {ω})^d · {ω}^p`; the slot integrals of nef forms are nonnegative (`NefMixedMass.slotIntegral_nonneg_of_nef`, the
content of `pc:domination-intersection` (2)), which makes `ε ↦ (a + ε{ω})^N` and the mass bounds monotone.  The intersection
numbers of the limit: `[α_k^p](β₁ ∧ ⋯ ∧ β_d) = ∫ β ∧ (A + ε_k ω)^p` by class invariance, which tends to `∫ β ∧ A^p`.

## Main results

* `slotIntegral_add_smul_mono`, `slotIntegral_const_form_eq`, `smoothCurrent_elemTest`, `slotIntegral_append_add_ddc`,
  `tendsto_slotIntegral_append`, `thetaPsh_concSlots`;
* `HasClassIntersections`;
* **`exists_concentratedCurrent_of_nef`**.

Import discipline: this module does not import `Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.ConcentratedCurrentNef

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductTestForms
  PositiveProductCurrents IntegrationCurrent TopDegreeDensity SmoothCurrentTraceMeasure
  ManifoldTubePositivity MixedMassClassInvariance NefMixedMass GlobalNonPluripolar
  NefCoreKahlerCurrent DiagonalTangentialReduction

/-! ### Slot integrals of nef forms -/

section Slots

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Monotonicity of slot integrals of nef forms in a nef direction**: for nef slots `θ` and nef `B`, the slot integral of
`θ + t B` increases with `t ≥ 0` (expand into slot integrals of nef forms with nonnegative polynomial coefficients). -/
theorem slotIntegral_add_smul_mono (w : KahlerBackground N M) {θ B : Fin N → ClosedRealOneOneForm N M}
    (hθ : ∀ i, NefWithRespectTo w (θ i)) (hB : ∀ i, NefWithRespectTo w (B i)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    slotIntegral w (fun i => θ i + s • B i) ≤ slotIntegral w (fun i => θ i + t • B i) := by
  classical
  rw [slotIntegral_add_smul_eq_sum, slotIntegral_add_smul_eq_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  have hI : 0 ≤ slotIntegral w (S.piecewise θ B) := by
    refine slotIntegral_nonneg_of_nef w fun i => ?_
    by_cases hi : i ∈ S
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi]; exact hθ i
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]; exact hB i
  refine mul_le_mul_of_nonneg_right ?_ hI
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
  · split_ifs
    · exact zero_le_one
    · exact hs
  · split_ifs
    · exact le_rfl
    · exact hst

/-- **The slot integral of `(ω, …, ω)` is the volume.** -/
theorem slotIntegral_const_form_eq (w : KahlerBackground N M) :
    slotIntegral w (fun _ => w.form) = (kahlerVolume w).real univ := by
  rw [slotIntegral]
  simp_rw [← topRatio_formPow_eq_slotForm', topRatio_formPow w.isKahler.1]
  simp [integral_const]

/-- `0` is nef. -/
theorem nefWithRespectTo_zero (w : KahlerBackground N M) : NefWithRespectTo w 0 :=
  nefWithRespectTo_of_isSemipositive fun _ _ _ _ => by simp

/-- A Kähler background is nef. -/
theorem nefWithRespectTo_form (w : KahlerBackground N M) : NefWithRespectTo w w.form :=
  nefWithRespectTo_of_isSemipositive w.isSemipositive

/-- **The Kähler volume of a nonempty compact manifold of positive dimension is positive.** -/
theorem kahlerVolume_real_univ_pos [Nonempty M] (hN : 0 < N) (w : KahlerBackground N M) :
    0 < (kahlerVolume w).real univ := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact NefCoreKahlerCurrent.kahlerVolume_real_univ_pos w

end Slots

/-! ### The smooth current on products of closed forms -/

section Products

variable {d p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (d + p)) M]
  [IsComplexManifold (d + p) M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The test form `β₁ ∧ ⋯ ∧ β_d` of closed real `(1,1)`-forms. -/
def prodTest (β : Fin d → ClosedRealOneOneForm (d + p) M) : testSpace (d + p) M d :=
  elemTest (fun _ => (1 : ℝ)) (chartSmooth_const 1) d (fun j => (β j).val) fun j => (β j).2.2

/-- **The current `[M] ∧ α^p` on a product of closed `(1,1)`-forms** is the slot integral of `(β₁, …, β_d, α, …, α)`. -/
theorem smoothCurrent_prodTest (w : KahlerBackground (d + p) M) (α : ClosedRealOneOneForm (d + p) M)
    (β : Fin d → ClosedRealOneOneForm (d + p) M) :
    smoothCurrent w (fun _ : Fin p => α) (prodTest β) = slotIntegral w (Fin.append β fun _ : Fin p => α) := by
  rw [smoothCurrent_apply, slotIntegral]
  show ∫ x, topRatio w.form.val _ x ∂(kahlerVolume w) = _
  congr 1
  funext x
  congr 1
  apply smoothRealForm_ext
  intro e z
  have hφ : ((prodTest β : testSpace (d + p) M d) : SmoothRealForm (d + p) M (2 * d)).coeff e z =
      wedgeProd d fun i => (β i).val.coeff e z := by
    show (elemForm (fun _ => (1 : ℝ)) (chartSmooth_const 1) d (fun j => (β j).val)).coeff e z = _
    rw [elemForm_coeff, one_smul]
  rw [chainTestLM_coeff p (fun _ => α.val) (fun _ => α.2.2) d (prodTest β) e z hφ, slotForm, formProd_coeff]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-- **Class invariance in the last `p` slots.** -/
theorem slotIntegral_append_add_ddc (w : KahlerBackground (d + p) M) (β : Fin d → ClosedRealOneOneForm (d + p) M)
    (θ : ClosedRealOneOneForm (d + p) M) {g : M → ℝ} (hg : ChartSmooth (n := d + p) g) :
    slotIntegral w (Fin.append β fun _ : Fin p => θ + ddcClosedForm g hg) =
      slotIntegral w (Fin.append β fun _ : Fin p => θ) := by
  set f : Fin (d + p) → M → ℝ := Fin.append (fun _ _ => (0 : ℝ)) (fun _ => g) with hfdef
  have hf : ∀ i, ChartSmooth (n := d + p) (f i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [hfdef, Fin.append_left]; exact fun _ => contDiffOn_const
    · simp only [hfdef, Fin.append_right]; exact hg
  rw [← slotIntegral_add_ddc w (Fin.append β fun _ : Fin p => θ) f hf]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    have hz : ∀ (u : M → ℝ) (hu : ChartSmooth (n := d + p) u), u = (fun _ => 0) → ddcClosedForm u hu = 0 := by
      rintro u hu rfl
      exact ddcClosedForm_zero
    rw [hz _ (hf (Fin.castAdd p j)) (by simp only [hfdef, Fin.append_left]), add_zero]
  · simp only [Fin.append_right]
    congr 2
    simp only [hfdef, Fin.append_right]

/-- **Continuity of the intersection numbers in `ε`**: `∫ β ∧ (A + ε ω)^p → ∫ β ∧ A^p` as `ε → 0`. -/
theorem tendsto_slotIntegral_append (w : KahlerBackground (d + p) M) (β : Fin d → ClosedRealOneOneForm (d + p) M)
    (A : ClosedRealOneOneForm (d + p) M) :
    Tendsto (fun t : ℝ => slotIntegral w (Fin.append β fun _ : Fin p => A + t • w.form)) (𝓝 0)
      (𝓝 (slotIntegral w (Fin.append β fun _ : Fin p => A))) := by
  have hfam : ∀ t : ℝ, (Fin.append β fun _ : Fin p => A + t • w.form) =
      fun i => (Fin.append β fun _ : Fin p => A) i +
        t • (Fin.append (fun _ : Fin d => (0 : ClosedRealOneOneForm (d + p) M)) fun _ : Fin p => w.form) i := by
    intro t
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, smul_zero, add_zero]
    · simp only [Fin.append_right]
  simp_rw [hfam]
  have hc := (continuous_slotIntegral_add_smul w (Fin.append β fun _ : Fin p => A)
    (Fin.append (fun _ : Fin d => (0 : ClosedRealOneOneForm (d + p) M)) fun _ : Fin p => w.form)).tendsto 0
  simpa only [zero_smul, add_zero] using hc

end Products

/-! ### The concentrated current of a nef class -/

section Main

variable {d p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (d + p)) M]
  [IsComplexManifold (d + p) M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The slots `(ω_ε, …, ω_ε, ω, …, ω)` are semipositive when `ω_ε ≥ ω/2`. -/
theorem thetaPsh_concSlots (W : KahlerBackground (d + p) M) {f : M → ℝ} (hf : ChartSmooth (n := d + p) f)
    (hhalf : ((1 / 2 : ℝ) • W.form + ddcClosedForm f hf).val.IsSemipositive) (i : Fin (d + p)) :
    ThetaPlurisubharmonic ((fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm f hf else W.form) i).val (fun _ => 0) := by
  have hK := ConcentratedCurrent.isKahler_of_half W hf hhalf
  dsimp only
  split_ifs
  · exact (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr (KahlerBackground.isSemipositive ⟨_, hK⟩)
  · exact (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr W.isSemipositive

variable (W : KahlerBackground (d + p) M) in
/-- **`T` has the intersection numbers of `a^p = {A}^p`**: `T(β₁ ∧ ⋯ ∧ β_d) = ∫_M β₁ ∧ ⋯ ∧ β_d ∧ A^p` for all closed real
`(1,1)`-forms `βᵢ`. -/
def HasClassIntersections (T : ProductCurrent (d + p) M d) (A : ClosedRealOneOneForm (d + p) M) : Prop :=
  ∀ β : Fin d → ClosedRealOneOneForm (d + p) M, T (prodTest β) = slotIntegral W (Fin.append β fun _ : Fin p => A)

/-- **A current with the intersection numbers of `a^p` and mass on `Y`** (Boucksom, Lemma 4.12; Demailly--Păun, Proposition 2.6;
`bou:concentrated-current-connected`): let `(M, ω)` be a compact connected Kähler manifold of dimension `N = d + p`, `p ≥ 1`,
`ω_ε = ω + ddᶜ f_ε ≥ ω/2` for `0 < ε ≤ 1`, `V_ε` decreasing as `ε ↓ 0` with `⋂_ε closure V_ε ⊆ Y`, `K` compact with
`∫_{K ∩ V_ε} ω_ε^p ∧ ω^d ≥ δ > 0`.  For every nef class `a = {A}` there is a closed positive current `T` of bidimension
`(d, d)` with the intersection numbers of `a^p` and
`∫_{K ∩ Y} T ∧ ω^d ≥ (1 / (2^{N+1} N!)) (a^N / ∫ ω^N) δ² / ((a + {ω})^d · {ω}^p)`. -/
theorem exists_concentratedCurrent_of_nef [ConnectedSpace M] (W : KahlerBackground (d + p) M) (hp : 0 < p)
    (f : Set.Ioc (0 : ℝ) 1 → M → ℝ) (hf : ∀ ε, ChartSmooth (n := d + p) (f ε))
    (hhalf : ∀ ε, ((1 / 2 : ℝ) • W.form + ddcClosedForm (f ε) (hf ε)).val.IsSemipositive)
    {Y : Set M} (V : Set.Ioc (0 : ℝ) 1 → Set M) (hVmono : Monotone V) (hVY : ⋂ ε, closure (V ε) ⊆ Y)
    {K : Set M} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hconc : ∀ ε, ENNReal.ofReal δ ≤ globalMixedMeasure (fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm (f ε) (hf ε) else W.form) (fun _ _ => 0)
        (thetaPsh_concSlots W (hf ε) (hhalf ε)) (K ∩ V ε))
    (A : ClosedRealOneOneForm (d + p) M) (hnef : NefWithRespectTo W A) :
    ∃ (T : ProductCurrent (d + p) M d) (hT : IsPositive T),
      ClosedProductCurrents.IsClosedCurrent T ∧ HasClassIntersections W T A ∧
      1 / (2 ^ (d + p + 1) * ((d + p).factorial : ℝ)) * (slotIntegral W (fun _ => A) / (kahlerVolume W).real univ) *
          (δ ^ 2 / slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < d then A + W.form else W.form)) ≤
        (CurrentTraceMeasure.traceMeasure W T hT).real (K ∩ Y) := by
  classical
  have hN : 0 < d + p := by omega
  -- the sequence `ε_k = 1/(k+1)` in `(0, 1]`
  set εs : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεsdef
  have hεpos : ∀ k, 0 < εs k := fun k => by simp only [hεsdef]; positivity
  have hεle : ∀ k, εs k ≤ 1 := fun k => by
    simp only [hεsdef]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  set ε : ℕ → Set.Ioc (0 : ℝ) 1 := fun k => ⟨εs k, hεpos k, hεle k⟩ with hεdef
  have hεanti : Antitone ε := fun j k hjk => by
    show εs k ≤ εs j
    simp only [hεsdef]
    apply one_div_le_one_div_of_le (by positivity)
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  -- the nef corrections: `B_k = (A + ε_k ω) + ddᶜh_k` is Kähler
  have hcorr : ∀ k, ∃ (h : M → ℝ) (hh : ChartSmooth (n := d + p) h),
      ((A + εs k • W.form) + ddcClosedForm h hh).val.IsKahler := by
    intro k
    obtain ⟨h, hh, hpos⟩ := hnef (εs k / 2) (half_pos (hεpos k))
    refine ⟨h, hh, ?_⟩
    set θ : ClosedRealOneOneForm (d + p) M := A + ddcClosedForm h hh + (εs k / 2) • W.form with hθdef
    have hθ : θ.val.IsSemipositive := fun e z hz v => by
      have := hpos e z hz v
      simpa [hθdef, ddcClosedForm_coeff] using this
    have hBeq : θ + (εs k / 2) • W.form = (A + εs k • W.form) + ddcClosedForm h hh := by
      apply ClosedRealOneOneForm.ext
      intro e z
      simp only [hθdef, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
      module
    rw [← hBeq]
    exact isKahler_add_smul_of_isSemipositive W hθ (half_pos (hεpos k))
  choose h hh hBK using hcorr
  set B : ℕ → ClosedRealOneOneForm (d + p) M := fun k => (A + εs k • W.form) + ddcClosedForm (h k) (hh k)
    with hBdef
  have hω'K : ∀ k, (W.form + ddcClosedForm (f (ε k)) (hf (ε k))).val.IsKahler := fun k =>
    ConcentratedCurrent.isKahler_of_half W (hf (ε k)) (hhalf (ε k))
  -- Yau's theorem in the Kähler class `{B_k}` with the target `ω_{ε_k}^N`
  have hyau : ∀ k, ∃ (φ : M → ℝ) (hφ : ChartSmooth (n := d + p) φ),
      (B k + ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart (d + p) M) (z : ComplexModel (d + p)), z ∈ e.val.target →
        actualTopPowerDensity ((B k + ddcClosedForm φ hφ).val.coeff e z) =
          ((kahlerVolume (⟨B k, hBK k⟩ : KahlerBackground (d + p) M)).real univ /
            (kahlerVolume (⟨_, hω'K k⟩ : KahlerBackground (d + p) M)).real univ) *
            actualTopPowerDensity ((W.form + ddcClosedForm (f (ε k)) (hf (ε k))).val.coeff e z) := fun k =>
    YauTheorem.exists_kahler_mongeAmpere_eq_smul hN ⟨B k, hBK k⟩ ⟨_, hω'K k⟩
  choose φ hφ hαK hMA using hyau
  have hc : ∀ k, 0 < (kahlerVolume (⟨B k, hBK k⟩ : KahlerBackground (d + p) M)).real univ /
      (kahlerVolume (⟨_, hω'K k⟩ : KahlerBackground (d + p) M)).real univ := fun k =>
    YauTheorem.kahlerVolume_div_pos hN _ _
  -- monotonicity of the slot integrals in `ε`
  have hAnef : ∀ i : Fin (d + p), NefWithRespectTo W ((fun _ => A) i) := fun _ => hnef
  have hωnef : ∀ i : Fin (d + p), NefWithRespectTo W ((fun _ => W.form) i) := fun _ => nefWithRespectTo_form W
  have hite : ∀ (m : ℕ) (t : ℝ), (fun i : Fin (d + p) => if (i : ℕ) < m then A + t • W.form else W.form) =
      fun i => (fun i : Fin (d + p) => if (i : ℕ) < m then A else W.form) i +
        t • (fun i : Fin (d + p) => if (i : ℕ) < m then W.form else 0) i := by
    intro m t
    funext i
    by_cases hi : (i : ℕ) < m
    · simp only [if_pos hi]
    · simp only [if_neg hi, smul_zero, add_zero]
  have hiteθ : ∀ m : ℕ, ∀ i : Fin (d + p),
      NefWithRespectTo W ((fun i : Fin (d + p) => if (i : ℕ) < m then A else W.form) i) := by
    intro m i
    dsimp only
    split_ifs
    · exact hnef
    · exact nefWithRespectTo_form W
  have hiteB : ∀ m : ℕ, ∀ i : Fin (d + p),
      NefWithRespectTo W ((fun i : Fin (d + p) => if (i : ℕ) < m then W.form else 0) i) := by
    intro m i
    dsimp only
    split_ifs
    · exact nefWithRespectTo_form W
    · exact nefWithRespectTo_zero W
  have hite_mono : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < m then A + t • W.form else W.form) ≤
        slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < m then A + W.form else W.form) := by
    intro m t ht0 ht1
    have h1 := slotIntegral_add_smul_mono W (hiteθ m) (hiteB m) ht0 ht1
    rw [← hite m t, ← hite m 1] at h1
    simpa only [one_smul] using h1
  have hite_ddc : ∀ (m k : ℕ),
      slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < m then B k else W.form) =
        slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < m then A + εs k • W.form else W.form) := by
    intro m k
    have h0 := NefCoreKahlerCurrent.slotIntegral_ite_add_ddc W m (A + εs k • W.form) W.form (hh k)
      (f := fun _ => (0 : ℝ)) (fun _ => contDiffOn_const)
    rw [ddcClosedForm_zero, add_zero] at h0
    exact h0
  set P₀ : ℝ := slotIntegral W (fun _ => A) with hP₀def
  set M₀ : ℝ := slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < d then A + W.form else W.form) with hM₀def
  set M₁ : ℝ := slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < p then A + W.form else W.form) with hM₁def
  have hvol : ∀ k, P₀ ≤ slotIntegral W fun _ => B k := by
    intro k
    have h1 : slotIntegral W (fun _ : Fin (d + p) => B k) = slotIntegral W (fun _ : Fin (d + p) => A + εs k • W.form) :=
      slotIntegral_add_ddc W (fun _ => A + εs k • W.form) (fun _ => h k) (fun _ => hh k)
    rw [h1]
    have h2 := slotIntegral_add_smul_mono W hAnef hωnef le_rfl (hεpos k).le
    simpa only [zero_smul, add_zero] using h2
  have hmass : ∀ k, slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < d then B k else W.form) ≤ M₀ := by
    intro k
    rw [hite_ddc]
    exact hite_mono d (εs k) (hεpos k).le (hεle k)
  have hmassp : ∀ k, slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < p then B k else W.form) ≤ M₁ := by
    intro k
    rw [hite_ddc]
    exact hite_mono p (εs k) (hεpos k).le (hεle k)
  -- `M₀ > 0`: one term of its expansion is `∫ ωᴺ`
  have hvolpos : 0 < (kahlerVolume W).real univ := kahlerVolume_real_univ_pos hN W
  have hM₀ : 0 < M₀ := by
    have hexp := slotIntegral_add_smul_eq_sum W (fun i : Fin (d + p) => if (i : ℕ) < d then A else W.form)
      (fun i : Fin (d + p) => if (i : ℕ) < d then W.form else 0) 1
    rw [← hite d 1] at hexp
    simp only [one_smul] at hexp
    rw [hM₀def, hexp]
    simp only [ite_self, Finset.prod_const_one, one_mul]
    set S₀ : Finset (Fin (d + p)) := Finset.univ.filter fun i => ¬ (i : ℕ) < d with hS₀def
    have hterm : ∀ S : Finset (Fin (d + p)), 0 ≤
        slotIntegral W (S.piecewise (fun i : Fin (d + p) => if (i : ℕ) < d then A else W.form)
          (fun i : Fin (d + p) => if (i : ℕ) < d then W.form else 0)) := by
      intro S
      refine slotIntegral_nonneg_of_nef W fun i => ?_
      by_cases hi : i ∈ S
      · rw [Finset.piecewise_eq_of_mem _ _ _ hi]; exact hiteθ d i
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]; exact hiteB d i
    have hS₀ : S₀.piecewise (fun i : Fin (d + p) => if (i : ℕ) < d then A else W.form)
        (fun i : Fin (d + p) => if (i : ℕ) < d then W.form else 0) = fun _ => W.form := by
      funext i
      by_cases hi : (i : ℕ) < d
      · rw [Finset.piecewise_eq_of_notMem _ _ _
          (by simp only [hS₀def, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; exact hi), if_pos hi]
      · rw [Finset.piecewise_eq_of_mem _ _ _
          (by simp only [hS₀def, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi), if_neg hi]
    have hsingle := Finset.single_le_sum (f := fun S : Finset (Fin (d + p)) =>
        slotIntegral W (S.piecewise (fun i : Fin (d + p) => if (i : ℕ) < d then A else W.form)
          (fun i : Fin (d + p) => if (i : ℕ) < d then W.form else 0))) (fun S _ => hterm S) (Finset.mem_univ S₀)
    simp only [hS₀, slotIntegral_const_form_eq] at hsingle
    exact hvolpos.trans_le hsingle
  -- the sets
  set S : ℕ → Set M := fun k => K ∩ V (ε k) with hSdef
  set F : ℕ → Set M := fun j => K ∩ closure (V (ε j)) with hFdef
  have hF : ∀ j, IsClosed (F j) := fun j => hK.isClosed.inter isClosed_closure
  have hanti : Antitone F := fun j j' hjj' =>
    inter_subset_inter_right K (closure_mono (hVmono (hεanti hjj')))
  have hSF : ∀ j k, j ≤ k → S k ⊆ F j := fun j k hjk =>
    inter_subset_inter_right K ((hVmono (hεanti hjk)).trans subset_closure)
  obtain ⟨U, Θ, hΘ, hUle, hΘc, -, hlim, hbound⟩ := ConcentratedCurrent.exists_concentratedCurrent W B φ hφ
    (fun k => f (ε k)) (fun k => hf (ε k)) hαK (fun k => hhalf (ε k)) _ hc hMA S hδ hM₀
    (fun k => thetaPsh_concSlots W (hf (ε k)) (hhalf (ε k))) (fun k => hconc (ε k)) hvol hmass hmassp
    hF hanti hSF
  refine ⟨Θ, hΘ, hΘc, ?_, ?_⟩
  · -- the intersection numbers of the limit
    intro β
    have hseq : ∀ k, smoothCurrent W (fun _ : Fin p => B k + ddcClosedForm (φ k) (hφ k)) (prodTest β) =
        slotIntegral W (Fin.append β fun _ : Fin p => A + εs k • W.form) := by
      intro k
      rw [smoothCurrent_prodTest, slotIntegral_append_add_ddc]
      exact slotIntegral_append_add_ddc W β (A + εs k • W.form) (hh k)
    have hεlim : Tendsto εs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun k => smoothCurrent W (fun _ : Fin p => B k + ddcClosedForm (φ k) (hφ k)) (prodTest β))
        (U : Filter ℕ) (𝓝 (slotIntegral W (Fin.append β fun _ : Fin p => A))) := by
      simp_rw [hseq]
      exact ((tendsto_slotIntegral_append W β A).comp hεlim).mono_left hUle
    exact tendsto_nhds_unique (hlim (prodTest β)) h1
  · -- the lower bound on `K ∩ Y`
    have hsub : (⋂ j, F j) ⊆ K ∩ Y := by
      intro x hx
      rw [mem_iInter] at hx
      refine ⟨(hx 0).1, hVY (mem_iInter.mpr fun ε' => ?_)⟩
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt ε'.2.1
      have hle : ε j ≤ ε' := by
        show εs j ≤ ε'.1
        exact hj.le
      exact closure_mono (hVmono hle) (hx j).2
    refine le_trans ?_ (hbound.trans (measureReal_mono hsub))
    have hP₀ : 0 ≤ P₀ := slotIntegral_nonneg_of_nef W hAnef
    have hX : 0 ≤ P₀ / (kahlerVolume W).real univ * δ ^ 2 / M₀ := by positivity
    have h2 : (4 : ℝ) * 2 ^ d ≤ 2 ^ (d + p + 1) := by
      have : (4 : ℝ) * 2 ^ d = 2 ^ (d + 2) := by rw [pow_add]; norm_num; ring
      rw [this]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hfac : (0 : ℝ) < (d + p).factorial := by exact_mod_cast Nat.factorial_pos _
    calc 1 / (2 ^ (d + p + 1) * ((d + p).factorial : ℝ)) * (P₀ / (kahlerVolume W).real univ) * (δ ^ 2 / M₀)
        = (P₀ / (kahlerVolume W).real univ * δ ^ 2 / M₀) / (2 ^ (d + p + 1) * ((d + p).factorial : ℝ)) := by
          ring
      _ ≤ (P₀ / (kahlerVolume W).real univ * δ ^ 2 / M₀) / (4 * 2 ^ d * ((d + p).factorial : ℝ)) :=
          div_le_div_of_nonneg_left hX (by positivity) (mul_le_mul_of_nonneg_right h2 hfac.le)
      _ = P₀ / (kahlerVolume W).real univ * δ ^ 2 / (4 * 2 ^ d * ((d + p).factorial : ℝ) * M₀) := by
          ring

end Main

end SGPT.Foundations.Analysis.Pending.ConcentratedCurrentNef
