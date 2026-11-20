import SGPT.Foundations.Analysis.Pending.DivisorialDomination
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact
import SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
import SGPT.Foundations.Analysis.Pending.DecreasingContactMassLimit
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.Envelopes
import SGPT.Foundations.Analysis.Pending.RooftopContactBigClass

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Route F: the trace-free limit `u = lim_j P_{β_j}[φ_j]`

Source: DX24 (`references/dx24-trace-operator/source/main.tex:307-335`, Proposition 2.1) and the
trace-free variant of Copy-4 `sec:setup` recorded in `scratch/tn23-envelopes-qea-plan-0117.md` §5.2
(human decision I-0796, D0 = route F).

On a compact connected complex manifold `Z` with a closed real `(1,1)`-form `γ` and a Kähler form
`ω`, let `ε_j ↓ 0` and `φ_j ∈ PSH(Z, γ + ε_jω)` be pointwise decreasing.  The model envelopes
`P_j := P_{γ+ε_jω}[φ_j]` decrease in `j` (monotonicity of the envelope in the potential and in
the background), each has supremum `0`, and

    u := lim_j P_j = ⨅_j P_j

is a `γ`-psh POTENTIAL (`isThetaPshPotential_traceFreeLimit`): for every `i` the tail `(P_j)_{j ≥ i}`
consists of `(γ + ε_iω)`-psh functions, so `u` is `(γ + ε_iω)`-psh for every `i`
(`ThetaPshDecreasingLimit`), hence `γ`-psh (`thetaPlurisubharmonic_of_forall_add_smul`: a decreasing
limit of the psh functions `u + ρ_γ + ε_i τ`, `τ ≥ 0` a local potential of `ω`); it is not
identically `-∞` by the Hartogs-type compactness of `ThetaPshAntitoneSupNondegenerate`.
By construction `u ≤ P_j` for every `j` ((T2) with `C_j = 0`).
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.TraceFreeLimit

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass

/-! ### A potential of `θ + ε_iω` for every `i` is a potential of `θ` -/

section Psh

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- The infimum of `a + c_i` over a decreasing real sequence `c_i → L` is `a + L`, for every
extended real `a`. -/
theorem iInf_add_coe_eq_of_antitone {a : EReal} {c : ℕ → ℝ} {L : ℝ} (hanti : Antitone c)
    (hlim : Tendsto c atTop (𝓝 L)) : (⨅ i, (a + (c i : EReal))) = a + (L : EReal) := by
  have hc : Tendsto (fun i => (c i : EReal)) atTop (𝓝 (L : EReal)) :=
    (continuous_coe_real_ereal.tendsto L).comp hlim
  have hT : Tendsto (fun i => a + (c i : EReal)) atTop (𝓝 (a + (L : EReal))) :=
    ((EReal.continuousAt_add (p := (a, (L : EReal))) (Or.inr (EReal.coe_ne_bot L))
      (Or.inr (EReal.coe_ne_top L))).tendsto).comp (tendsto_const_nhds.prodMk_nhds hc)
  have hmono : Antitone (fun i => a + (c i : EReal)) := fun i j h =>
    add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (hanti h))
  exact tendsto_nhds_unique (tendsto_atTop_iInf hmono) hT

/-- **A function which is `(θ + ε_iη)`-psh for a sequence `ε_i ↓ 0` is `θ`-psh.**  Near a point
take local potentials `ρ` of `θ` and `σ` of `η`, shift `σ` to `τ = σ - σ(z) + 1 ≥ 0` on a
neighbourhood `W`; then `u + ρ + ε_iτ` are psh on `W` and decrease to `u + ρ`. -/
theorem thetaPlurisubharmonic_of_forall_add_smul {θ η : ClosedRealOneOneForm k Z}
    {u : Z → EReal} {ε : ℕ → ℝ} (hanti : Antitone ε)
    (hlim : Tendsto ε atTop (𝓝 0)) (hu : ∀ i, ThetaPlurisubharmonic (θ + ε i • η).val u) :
    ThetaPlurisubharmonic θ.val u := by
  intro e z hz
  obtain ⟨W₁, ρ, hzW₁, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
  obtain ⟨W₂, σ, hzW₂, hσ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials η e z hz
  set W : Set (ComplexModel k) := W₁ ∩ (W₂ ∩ σ ⁻¹' Ioi (σ z - 1)) with hWdef
  have hWo : IsOpen W :=
    hρ.1.inter (hσ.2.2.1.continuousOn.isOpen_inter_preimage hσ.1 isOpen_Ioi)
  have hzW : z ∈ W := ⟨hzW₁, hzW₂, by simp⟩
  have hW₁ : W ⊆ W₁ := inter_subset_left
  have hW₂ : W ⊆ W₂ := fun y hy => hy.2.1
  set τ : ComplexModel k → ℝ := fun y => σ y + (1 - σ z) with hτdef
  have hτpos : ∀ y ∈ W, 0 ≤ τ y := by
    intro y hy
    have h := hy.2.2
    simp only [mem_preimage, mem_Ioi] at h
    simp only [hτdef]
    linarith
  have hσW := hσ.mono hWo hW₂
  have hτ : IsSmoothLocalPotential η.val e W τ := by
    refine ⟨hWo, hσW.2.1, hσW.2.2.1.add contDiffOn_const, fun y hy => ?_⟩
    rw [smoothDDC_add hWo hσW.2.2.1 contDiffOn_const hy, GlobalPotentialTransforms.smoothDDC_const,
      add_zero]
    exact hσW.2.2.2 hy
  have hρW := hρ.mono hWo hW₁
  have hloc : ∀ i, IsSmoothLocalPotential (θ + ε i • η).val e W
      (fun y => ρ y + ε i • τ y) := fun i =>
    FirstPass.LocalPotentials.localPotential_add hρW
      (FirstPass.LocalPotentials.localPotential_smul hτ (ε i))
  refine ⟨W, ρ, hzW, hρW, ?_⟩
  have hdisc : ∀ i, DiscPshOn
      (fun y => chartFunction u e y + ((ρ y + ε i • τ y : ℝ) : EReal)) W := fun i =>
    (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic (hu i) e
      (hloc i)).discPshOn
  have hantiW : ∀ y ∈ W,
      Antitone fun i => chartFunction u e y + ((ρ y + ε i • τ y : ℝ) : EReal) := by
    intro y hy i j hij
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    have := mul_le_mul_of_nonneg_right (hanti hij) (hτpos y hy)
    simp only [smul_eq_mul]
    linarith
  have hlimW := DiscPshOn.plurisubharmonicOn_iInf_of_antitone hWo hdisc hantiW
  intro x hx
  refine (hlimW x hx).congr ?_
  filter_upwards [hWo.mem_nhds hx] with y hy
  have hcanti : Antitone fun i => ρ y + ε i • τ y := fun i j hij => by
    have := mul_le_mul_of_nonneg_right (hanti hij) (hτpos y hy)
    simp only [smul_eq_mul]
    linarith
  have hclim : Tendsto (fun i => ρ y + ε i • τ y) atTop (𝓝 (ρ y)) := by
    have h := (hlim.smul_const (τ y)).const_add (ρ y)
    simpa using h
  exact iInf_add_coe_eq_of_antitone hcanti hclim

end Psh

/-! ### The trace-free limit -/

section Limit

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [CompactSpace Z]

/-- The model envelope is monotone in the background: enlarging `θ` by a semipositive form enlarges
the competitor set. -/
theorem singularityEnvelope_le_add {θ η : ClosedRealOneOneForm k Z} (hη : η.val.IsSemipositive)
    (φ : Z → EReal) : singularityEnvelope θ.val φ ≤ singularityEnvelope (θ + η).val φ := by
  refine uscRegularization_mono (sSup_le_sSup fun w hw => ?_)
  exact ⟨⟨LocalPotentials.isThetaPshPotential_add_of_semipositive hw.1.1 hη, hw.1.2⟩, hw.2⟩

/-- A model envelope of a potential reaches its supremum `0`: at a maximum point `x` of `φ`,
`P[φ](x) ≥ φ(x) - max φ = 0`. -/
theorem exists_singularityEnvelope_eq_zero [Nonempty Z] {θ : ClosedRealOneOneForm k Z}
    {φ : Z → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    ∃ x, singularityEnvelope θ.val φ x = 0 := by
  obtain ⟨c, hc, x, hx⟩ := DivisorialDomination.exists_eq_max_of_isThetaPshPotential hφ
  refine ⟨x, le_antisymm (singularityEnvelope_le_zero θ.val φ x) ?_⟩
  have hle := le_singularityEnvelope (φ := φ) (hφ.sub_const c) (sub_const_nonpositive_of_le hc)
    ⟨-c, fun y _ => le_of_eq (by
      change φ y - (c : EReal) = φ y + ((-c : ℝ) : EReal)
      rw [sub_eq_add_neg, ← EReal.coe_neg])⟩
  have h0 := hle x
  simp only at h0
  rwa [hx, EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at h0

/-- The trace-free limit `u = ⨅_j P_{θ+ε_jω}[φ_j]`. -/
def traceFreeLimit (θ ω : ClosedRealOneOneForm k Z) (ε : ℕ → ℝ) (φ : ℕ → Z → EReal) :
    Z → EReal :=
  fun x => ⨅ j, singularityEnvelope (θ + ε j • ω).val (φ j) x

variable (θ ω : ClosedRealOneOneForm k Z) (ε : ℕ → ℝ) (φ : ℕ → Z → EReal)

theorem traceFreeLimit_le (j : ℕ) :
    traceFreeLimit θ ω ε φ ≤ singularityEnvelope (θ + ε j • ω).val (φ j) := fun x =>
  iInf_le (fun i => singularityEnvelope (θ + ε i • ω).val (φ i) x) j

variable {θ ω ε φ}

/-- The model envelopes `P_j = P_{θ+ε_jω}[φ_j]` decrease when `ε_j` and `φ_j` do. -/
theorem singularityEnvelope_antitone (homega : ω.val.IsSemipositive) (hanti : Antitone ε)
    (hφ : ∀ x, Antitone fun j => φ j x) {i j : ℕ} (hij : i ≤ j) :
    singularityEnvelope (θ + ε j • ω).val (φ j) ≤ singularityEnvelope (θ + ε i • ω).val (φ i) := by
  calc singularityEnvelope (θ + ε j • ω).val (φ j)
      ≤ singularityEnvelope (θ + ε j • ω).val (φ i) :=
        singularityEnvelope_mono (MoreSingularOn.of_le fun x _ => hφ x hij)
    _ ≤ singularityEnvelope (θ + ε j • ω + (ε i - ε j) • ω).val (φ i) :=
        singularityEnvelope_le_add
          (KahlerDomination.isSemipositive_smul homega (sub_nonneg.2 (hanti hij))) _
    _ = singularityEnvelope (θ + ε i • ω).val (φ i) := by
        rw [show θ + ε j • ω + (ε i - ε j) • ω = θ + ε i • ω by module]

/-- The infimum of an antitone sequence equals the infimum of each of its tails. -/
theorem iInf_add_eq_iInf_of_antitone {f : ℕ → EReal} (hf : Antitone f) (i : ℕ) :
    (⨅ j, f (i + j)) = ⨅ j, f j :=
  le_antisymm (le_iInf fun j => (iInf_le _ j).trans (hf (Nat.le_add_left j i)))
    (le_iInf fun j => iInf_le _ (i + j))

/-- **The trace-free limit is a `θ`-psh potential** (route F, `F-c`): for `ε_j ↓ 0` and pointwise
decreasing `φ_j ∈ PSH(Z, θ + ε_jω)` on a compact connected `Z`, `u = ⨅_j P_{θ+ε_jω}[φ_j]` is
`(θ + ε_iω)`-psh for every `i` (decreasing limit of its tail), hence `θ`-psh, and not identically
`-∞` because every `P_j` reaches `0` (Hartogs-type compactness). -/
theorem isThetaPshPotential_traceFreeLimit [Nonempty Z] [ConnectedSpace Z]
    (omega : KahlerBackground k Z) (hanti : Antitone ε) (hlim : Tendsto ε atTop (𝓝 0))
    (hφ : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val (φ j))
    (hφanti : ∀ x, Antitone fun j => φ j x) :
    IsThetaPshPotential θ.val (traceFreeLimit θ omega.form ε φ) := by
  set P : ℕ → Z → EReal := fun j => singularityEnvelope (θ + ε j • omega.form).val (φ j) with hP
  have hPpsh : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val (P j) := fun j =>
    singularityEnvelope_isThetaPshPotential _ (θ + ε j • omega.form).2.1
      (θ + ε j • omega.form).2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) (φ j) (hφ j)
  have hPanti : ∀ x, Antitone fun j => P j x := fun x i j hij =>
    singularityEnvelope_antitone omega.isSemipositive hanti hφanti hij x
  -- every tail consists of `(θ + ε_iω)`-psh potentials
  have htail : ∀ i j, IsThetaPshPotential (θ + ε i • omega.form).val (P (i + j)) := by
    intro i j
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (hPpsh (i + j))
      (KahlerDomination.isSemipositive_smul omega.isSemipositive
        (sub_nonneg.2 (hanti (Nat.le_add_right i j))))
    rwa [show θ + ε (i + j) • omega.form + (ε i - ε (i + j)) • omega.form =
      θ + ε i • omega.form by module] at h
  have heq : ∀ i, (fun x => ⨅ j, P (i + j) x) = traceFreeLimit θ omega.form ε φ := fun i => by
    funext x
    exact iInf_add_eq_iInf_of_antitone (hPanti x) i
  have hpsh_i : ∀ i, ThetaPlurisubharmonic (θ + ε i • omega.form).val
      (traceFreeLimit θ omega.form ε φ) := fun i => by
    rw [← heq i]
    exact ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
      (fun j => (htail i j).1) fun x a b hab => hPanti x (Nat.add_le_add_left hab i)
  have hpsh : ThetaPlurisubharmonic θ.val (traceFreeLimit θ omega.form ε φ) :=
    thetaPlurisubharmonic_of_forall_add_smul hanti hlim hpsh_i
  -- nondegeneracy: all `P_j` are `(θ + ε_0ω)`-potentials reaching `0`
  have h0 : ∀ j, IsThetaPshPotential (θ + ε 0 • omega.form).val (P j) := fun j => by
    simpa using htail 0 j
  obtain ⟨x₀, hx₀⟩ := ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le
    h0 hPanti (C := 0) fun j => by
      obtain ⟨x, hx⟩ := exists_singularityEnvelope_eq_zero (hφ j)
      exact ⟨x, by simp [hP, hx]⟩
  exact ⟨hpsh, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh ⟨x₀, hx₀⟩⟩

end Limit

/-! ### The mass of a fixed potential is continuous in the background -/

section MassContinuity

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] [CompactSpace Z]

open GlobalNonPluripolar GlobalSlotLinear GlobalDiagonalScaling AmbientMassBackgroundMonotone

/-- **The global mixed measure is monotone in every slot background**: adding semipositive forms
`σ_i` to the backgrounds of a tuple of potentials does not decrease it. -/
theorem globalMixedMeasure_le_of_add_semipositive {θ σ : Fin k → ClosedRealOneOneForm k Z}
    (hσ : ∀ i, (σ i).val.IsSemipositive) {u : Fin k → Z → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (θ i + σ i).val (u i)) :
    globalMixedMeasure θ u (fun i => (hu i).1) ≤ globalMixedMeasure (fun i => θ i + σ i) u hu' := by
  classical
  set T : Finset (Fin k) → Fin k → ClosedRealOneOneForm k Z :=
    fun s i => if i ∈ s then θ i + σ i else θ i with hT
  have hTpsh : ∀ s i, ThetaPlurisubharmonic (T s i).val (u i) := by
    intro s i
    by_cases hi : i ∈ s
    · simpa [hT, hi] using hu' i
    · simpa [hT, hi] using (hu i).1
  have key : ∀ s : Finset (Fin k),
      globalMixedMeasure (T ∅) u (fun i => hTpsh ∅ i) ≤
        globalMixedMeasure (T s) u (fun i => hTpsh s i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact le_rfl
    | insert i₀ s hi₀ ih =>
        refine ih.trans ?_
        have hTs : T s i₀ = θ i₀ := by simp [hT, hi₀]
        have hupd : T (insert i₀ s) = Function.update (T s) i₀ (T s i₀ + (1 : ℝ) • σ i₀) := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hT, hi₀]
          · simp [hT, Finset.mem_insert, hj]
        exact globalMixedMeasure_le_of_eq_update_add_smul i₀ (hσ i₀) one_pos hupd
          (fun i => hTpsh s i) (by rw [hTs]; exact hu i₀) (fun i => hTpsh (insert i₀ s) i)
  have hempty : T ∅ = θ := by funext j; simp [hT]
  have huniv : T Finset.univ = fun i => θ i + σ i := by funext j; simp [hT]
  calc globalMixedMeasure θ u (fun i => (hu i).1)
      = globalMixedMeasure (T ∅) u (fun i => hTpsh ∅ i) :=
        globalMixedMeasure_congr_tuples hempty.symm rfl _ _
    _ ≤ globalMixedMeasure (T Finset.univ) u (fun i => hTpsh Finset.univ i) := key Finset.univ
    _ = globalMixedMeasure (fun i => θ i + σ i) u hu' :=
        globalMixedMeasure_congr_tuples huniv rfl _ _

/-- **The mass of a fixed potential is Lipschitz in the background at `ε = 0⁺`**: for a
`θ`-psh potential `u` there is `K < ∞` with `∫(θ + εω)_u^k ≤ ∫θ_u^k + εK` for `0 < ε ≤ 1`.
Slot by slot, `(θ + εω, u) = (θ, u) + ε(ω, 0)` (slot linearity), and the `(ω, 0)`-terms are
bounded, by slot monotonicity, by the masses `K_i` of the tuples with `(ω, 0)` in slot `i` and
`(θ + ω, u)` elsewhere. -/
theorem exists_diagonalPotentialMass_add_smul_le (omega : KahlerBackground k Z)
    {θ : ClosedRealOneOneForm k Z} {u : Z → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ hu' : IsThetaPshPotential (θ + ε • omega.form).val u,
        diagonalPotentialMass (θ + ε • omega.form) u hu' ≤
          diagonalPotentialMass θ u hu + ENNReal.ofReal ε * K := by
  classical
  have h0ω : IsThetaPshPotential omega.form.val (fun _ : Z => (0 : EReal)) :=
    ⟨(LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr omega.isSemipositive,
      fun x _ _ hx => ⟨x, hx, EReal.zero_ne_bot⟩⟩
  have hu1 : IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
  -- the reference tuples `R_i`: `(ω, 0)` in slot `i`, `(θ + ω, u)` elsewhere
  set R : Fin k → Fin k → ClosedRealOneOneForm k Z :=
    fun i => Function.update (fun _ => θ + (1 : ℝ) • omega.form) i omega.form with hR
  set x : Fin k → Fin k → Z → EReal :=
    fun i => Function.update (fun _ => u) i (fun _ => (0 : EReal)) with hx
  have hRpot : ∀ i j, IsThetaPshPotential (R i j).val (x i j) := by
    intro i j
    by_cases hj : j = i
    · subst hj; simpa [hR, hx] using h0ω
    · simpa [hR, hx, Function.update_of_ne hj] using hu1
  set K : ℝ≥0∞ := ∑ i, globalMixedMeasure (R i) (x i) (fun j => (hRpot i j).1) univ with hK
  refine ⟨K, ?_, fun ε hε hε1 hu' => ?_⟩
  · exact ENNReal.sum_lt_top.2 fun i _ => globalMixedMeasure_apply_lt_top omega _ univ
  -- the tuples `T s`: `θ + εω` in the slots of `s`, `θ` elsewhere, potential `u` everywhere
  set T : Finset (Fin k) → Fin k → ClosedRealOneOneForm k Z :=
    fun s i => if i ∈ s then θ + ε • omega.form else θ with hT
  have hTpot : ∀ s i, IsThetaPshPotential (T s i).val u := by
    intro s i
    by_cases hi : i ∈ s
    · simpa [hT, hi] using hu'
    · simpa [hT, hi] using hu
  have key : ∀ s : Finset (Fin k),
      globalMixedMeasure (T s) (fun _ => u) (fun i => (hTpot s i).1) univ ≤
        globalMixedMeasure (T ∅) (fun _ => u) (fun i => (hTpot ∅ i).1) univ +
          ENNReal.ofReal ε * ∑ i ∈ s, globalMixedMeasure (R i) (x i) (fun j => (hRpot i j).1) univ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i₀ s hi₀ ih =>
        -- slot linearity in slot `i₀`: `(θ + εω, u) = 1·(θ, u) + ε·(ω, 0)`
        have hθi₀ : T (insert i₀ s) i₀ = (1 : ℝ) • θ + ε • omega.form := by simp [hT]
        have hrest : Function.update (T (insert i₀ s)) i₀ θ = T s := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hT, hi₀]
          · simp [hT, Finset.mem_insert, hj]
        have hcomb : Function.update (fun _ : Fin k => u) i₀
            (fun p => ((1 : ℝ) : EReal) * u p + ((ε : ℝ) : EReal) * (0 : EReal)) =
            fun _ => u := by
          funext j
          by_cases hj : j = i₀
          · subst hj; funext p; simp
          · simp [Function.update_of_ne hj]
        have hc : ∀ i, ThetaPlurisubharmonic (T (insert i₀ s) i).val
            (Function.update (fun _ : Fin k => u) i₀
              (fun p => ((1 : ℝ) : EReal) * u p + ((ε : ℝ) : EReal) * (0 : EReal)) i) := by
          rw [hcomb]; exact fun i => (hTpot (insert i₀ s) i).1
        have ha : ∀ i, ThetaPlurisubharmonic (Function.update (T (insert i₀ s)) i₀ θ i).val
            (Function.update (fun _ : Fin k => u) i₀ u i) := by
          rw [hrest, Function.update_eq_self]; exact fun i => (hTpot s i).1
        have hbpot : ∀ i, IsThetaPshPotential
            (Function.update (T (insert i₀ s)) i₀ omega.form i).val
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)) i) := by
          intro i
          by_cases hi : i = i₀
          · subst hi; simpa using h0ω
          · simpa [Function.update_of_ne hi] using hTpot (insert i₀ s) i
        have hb : ∀ i, ThetaPlurisubharmonic
            (Function.update (T (insert i₀ s)) i₀ omega.form i).val
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)) i) :=
          fun i => (hbpot i).1
        have hkey := globalMixedMeasure_update_add_smul (θ := T (insert i₀ s)) i₀ (α := θ)
          (β := omega.form) (s := 1) (r := ε) one_pos hε hθi₀ (x := fun _ => u) (a := u)
          (b := fun _ => (0 : EReal)) hc ha hb
          (globalMixedMeasure_pole_null_of_nondegenerate hb hu) (by simp)
        -- the `(ω, 0)`-term is at most `K_{i₀}`, by slot monotonicity
        set B : Fin k → ClosedRealOneOneForm k Z :=
          Function.update (T (insert i₀ s)) i₀ omega.form with hB
        set σ : Fin k → ClosedRealOneOneForm k Z :=
          Function.update (fun j => (θ + (1 : ℝ) • omega.form) - T (insert i₀ s) j) i₀ 0 with hσdef
        have hσ : ∀ j, (σ j).val.IsSemipositive := by
          intro j
          by_cases hj : j = i₀
          · subst hj
            simpa [hσdef] using
              KahlerDomination.isSemipositive_smul omega.isSemipositive (le_refl (0 : ℝ))
          · simp only [hσdef, Function.update_of_ne hj]
            by_cases hjs : j ∈ insert i₀ s
            · have h1 : (θ + (1 : ℝ) • omega.form) - (θ + ε • omega.form) =
                  (1 - ε) • omega.form := by module
              simp only [hT, hjs, if_true, h1]
              exact KahlerDomination.isSemipositive_smul omega.isSemipositive (by linarith)
            · have h1 : (θ + (1 : ℝ) • omega.form) - θ = (1 : ℝ) • omega.form := by abel
              simp only [hT, hjs, if_false, h1]
              exact KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one
        have hBσ : (fun j => B j + σ j) = R i₀ := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp [hB, hσdef, hR]
          · simp [hB, hσdef, hR, Function.update_of_ne hj]
        have hxi : Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)) = x i₀ := rfl
        have hRpsh' : ∀ j, ThetaPlurisubharmonic (B j + σ j).val
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal)) j) := by
          intro j
          rw [congrFun hBσ j]
          exact (hRpot i₀ j).1
        have hmonoB := globalMixedMeasure_le_of_add_semipositive hσ hbpot hRpsh'
        have hBle : globalMixedMeasure B
            (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ ≤
            globalMixedMeasure (R i₀) (x i₀) (fun j => (hRpot i₀ j).1) univ := by
          calc globalMixedMeasure B
                (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ
              ≤ globalMixedMeasure (fun j => B j + σ j)
                  (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hRpsh' univ :=
                hmonoB univ
            _ = globalMixedMeasure (R i₀) (x i₀) (fun j => (hRpot i₀ j).1) univ := by
                rw [globalMixedMeasure_congr_tuples hBσ hxi hRpsh' (fun j => (hRpot i₀ j).1)]
        -- assemble
        have hstep : globalMixedMeasure (T (insert i₀ s)) (fun _ => u)
            (fun i => (hTpot (insert i₀ s) i).1) univ =
            globalMixedMeasure (T s) (fun _ => u) (fun i => (hTpot s i).1) univ +
              ENNReal.ofReal ε * globalMixedMeasure B
                (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ := by
          have h1 := congrArg (fun μ : Measure Z => μ univ) hkey
          simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_one,
            one_mul] at h1
          rw [globalMixedMeasure_congr_tuples rfl hcomb.symm _ hc, h1,
            globalMixedMeasure_congr_tuples hrest (Function.update_eq_self _ _) ha
              (fun i => (hTpot s i).1)]
        rw [hstep, Finset.sum_insert hi₀, mul_add]
        calc globalMixedMeasure (T s) (fun _ => u) (fun i => (hTpot s i).1) univ +
              ENNReal.ofReal ε * globalMixedMeasure B
                (Function.update (fun _ : Fin k => u) i₀ (fun _ => (0 : EReal))) hb univ
            ≤ (globalMixedMeasure (T ∅) (fun _ => u) (fun i => (hTpot ∅ i).1) univ +
                ENNReal.ofReal ε * ∑ i ∈ s,
                  globalMixedMeasure (R i) (x i) (fun j => (hRpot i j).1) univ) +
              ENNReal.ofReal ε *
                globalMixedMeasure (R i₀) (x i₀) (fun j => (hRpot i₀ j).1) univ :=
              add_le_add ih (by gcongr)
          _ = _ := by ring
  have hempty : T ∅ = fun _ => θ := by funext j; simp [hT]
  have huniv : T Finset.univ = fun _ => θ + ε • omega.form := by funext j; simp [hT]
  have hfin := key Finset.univ
  rw [globalMixedMeasure_congr_tuples huniv rfl _ (fun _ => hu'.1),
    globalMixedMeasure_congr_tuples hempty rfl _ (fun _ => hu.1)] at hfin
  exact hfin

/-- **Continuity of the mass in the background**: for `ε_j → 0⁺`,
`∫(θ + ε_jω)_u^k → ∫θ_u^k`. -/
theorem tendsto_diagonalPotentialMass_add_smul (omega : KahlerBackground k Z)
    {θ : ClosedRealOneOneForm k Z} {u : Z → EReal} (hu : IsThetaPshPotential θ.val u)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (hu' : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val u) :
    Tendsto (fun j => diagonalPotentialMass (θ + ε j • omega.form) u (hu' j)) atTop
      (𝓝 (diagonalPotentialMass θ u hu)) := by
  obtain ⟨K, hK, hle⟩ := exists_diagonalPotentialMass_add_smul_le omega hu
  have hlow : ∀ j, diagonalPotentialMass θ u hu ≤
      diagonalPotentialMass (θ + ε j • omega.form) u (hu' j) := fun j =>
    diagonalPotentialMass_le_add_smul omega.isSemipositive (hε j) hu (hu' j)
  have hup : ∀ᶠ j in atTop, diagonalPotentialMass (θ + ε j • omega.form) u (hu' j) ≤
      diagonalPotentialMass θ u hu + ENNReal.ofReal (ε j) * K :=
    (hlim.eventually (ge_mem_nhds one_pos)).mono fun j hj => hle (ε j) (hε j) hj (hu' j)
  have hT : Tendsto (fun j => diagonalPotentialMass θ u hu + ENNReal.ofReal (ε j) * K) atTop
      (𝓝 (diagonalPotentialMass θ u hu)) := by
    have h1 : Tendsto (fun j => ENNReal.ofReal (ε j)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hlim
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hK.ne)
    simpa using tendsto_const_nhds.add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall hlow) hup

/-- Measure-level monotonicity of the diagonal non-pluripolar measure in the error `ε`. -/
theorem diagonalPotentialMeasure_le_of_le (omega : KahlerBackground k Z)
    {θ : ClosedRealOneOneForm k Z} {ε ε' : ℝ} (hεε' : ε ≤ ε') {P : Z → EReal}
    (hP : IsThetaPshPotential (θ + ε • omega.form).val P)
    (hP' : IsThetaPshPotential (θ + ε' • omega.form).val P) (S : Set Z) :
    diagonalPotentialMeasure (θ + ε • omega.form) P hP S ≤
      diagonalPotentialMeasure (θ + ε' • omega.form) P hP' S := by
  rcases hεε'.eq_or_lt with h | h
  · subst h; exact le_rfl
  · have hform : θ + ε • omega.form + (ε' - ε) • omega.form = θ + ε' • omega.form := by module
    have hP'' : ThetaPlurisubharmonic (θ + ε • omega.form + (ε' - ε) • omega.form).val P := by
      rw [hform]; exact hP'.1
    have h1 := globalMixedMeasure_diagonal_le_add_smul omega.isSemipositive (sub_pos.2 h) hP hP''
    unfold diagonalPotentialMeasure
    refine (h1 S).trans (le_of_eq ?_)
    rw [globalMixedMeasure_congr_tuples (funext fun _ => hform) rfl _ (fun _ => hP'.1)]

end MassContinuity

/-! ### DX24 Proposition 2.1 for the trace-free limit -/

section DX24

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z] [CompactSpace Z] [Nonempty Z]

/-- **Xia SGPT Theorem 3.1.1 (contact) for a big class**: the non-pluripolar measure of a model
envelope `P_θ[φ]` puts no mass on `{P_θ[φ] < 0}` when `{θ}` is big.  The proof of
`SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero`, with Xia's
Corollary 3.1.1 (`RooftopContactBigClass`) and Corollary 2.4.4 (`BigClassEnvelopeContact`) in their
big-class forms instead of the general ones (whose non-big branch uses the Boucksom input). -/
theorem diagonalPotentialMeasure_singularityEnvelope_lt_zero_of_isBigClass (hk : 0 < k)
    (omega : KahlerBackground k Z) (θ : ClosedRealOneOneForm k Z)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {φ : Z → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hP : IsThetaPshPotential θ.val (singularityEnvelope θ.val φ)) :
    diagonalPotentialMeasure θ (singularityEnvelope θ.val φ) hP
      {x | singularityEnvelope θ.val φ x < 0} = 0 := by
  classical
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential θ.val
      θ.2.1 θ.2.2 hφ.1.hasSmoothLocalPotentials ⟨φ, hφ⟩
  have hid : singularityEnvelope θ.val φ =
      ShiftedRooftopLimit.shiftedRooftopLimit θ (thetaPshSupremum θ.val) φ :=
    SingularityEnvelopeContact.singularityEnvelope_eq_shiftedRooftopLimit θ hφ
  revert hP
  rw [hid]
  intro hPlim
  have hsub : {x : Z | ShiftedRooftopLimit.shiftedRooftopLimit θ (thetaPshSupremum θ.val) φ x < 0} ∩
      {x : Z | ShiftedRooftopLimit.shiftedRooftopLimit θ (thetaPshSupremum θ.val) φ x =
        thetaPshSupremum θ.val x} ⊆ {x : Z | thetaPshSupremum θ.val x < 0} := by
    rintro x ⟨hlt, heq⟩
    exact lt_of_eq_of_lt heq.symm hlt
  refine le_antisymm ?_ zero_le
  calc diagonalPotentialMeasure θ
          (ShiftedRooftopLimit.shiftedRooftopLimit θ (thetaPshSupremum θ.val) φ) hPlim
        {x | ShiftedRooftopLimit.shiftedRooftopLimit θ (thetaPshSupremum θ.val) φ x < 0}
      ≤ diagonalPotentialMeasure θ (thetaPshSupremum θ.val) hV
          ({x : Z | ShiftedRooftopLimit.shiftedRooftopLimit θ (thetaPshSupremum θ.val) φ x < 0} ∩
            {x : Z | ShiftedRooftopLimit.shiftedRooftopLimit θ (thetaPshSupremum θ.val) φ x =
              thetaPshSupremum θ.val x}) :=
        RooftopContactBigClass.shiftedRooftopLimit_le_contact_of_potential_of_isBigClass hk omega θ
          hbig hV hφ hPlim _
    _ ≤ diagonalPotentialMeasure θ (thetaPshSupremum θ.val) hV
          {x : Z | thetaPshSupremum θ.val x < 0} := measure_mono hsub
    _ = 0 := BigClassEnvelopeContact.diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_isBigClass
          hk θ hbig hV

/-- **DX24 Proposition 2.1, for the trace-free limit** (route F, `F-a`; (T3) of the trace
package): for `ε_j ↓ 0`, `ε_j > 0`, and pointwise decreasing `φ_j ∈ PSH(Z, θ + ε_jω)` on a compact
connected `Z` of positive dimension, the masses `b_j = ∫(θ + ε_jω)_{φ_j}^k` converge to the mass of
the trace-free limit `u = ⨅_j P_{θ+ε_jω}[φ_j]`.

`≥`: `u ≤ P_j` and `∫P_j = ∫φ_j` (Xia Prop. 3.1.3).  `≤` (DX24): for `j ≥ j₀`,
`b_j = (θ + ε_jω)^k_{P_j}{P_j = 0}` (contact, the class `θ + ε_jω` being big)
`≤ (θ + ε_{j₀}ω)^k_{P_j}{P_j = 0}`, whose `limsup` is at most `(θ + ε_{j₀}ω)^k_u{u = 0}` (Xia
Cor. 2.4.2, `DecreasingContactMassLimit`) `≤ ∫(θ + ε_{j₀}ω)_u^k`, and the latter tends to `∫θ_u^k`
(`tendsto_diagonalPotentialMass_add_smul`). -/
theorem tendsto_diagonalPotentialMass_traceFreeLimit (hk : 0 < k) [ConnectedSpace Z]
    (omega : KahlerBackground k Z) {θ : ClosedRealOneOneForm k Z} {ε : ℕ → ℝ}
    (hε : ∀ j, 0 < ε j) (hanti : Antitone ε) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : ℕ → Z → EReal} (hφ : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val (φ j))
    (hφanti : ∀ x, Antitone fun j => φ j x) :
    Tendsto (fun j => diagonalPotentialMass (θ + ε j • omega.form) (φ j) (hφ j)) atTop
      (𝓝 (diagonalPotentialMass θ (traceFreeLimit θ omega.form ε φ)
        (isThetaPshPotential_traceFreeLimit omega hanti hlim hφ hφanti))) := by
  set u := traceFreeLimit θ omega.form ε φ with hudef
  have hu : IsThetaPshPotential θ.val u := isThetaPshPotential_traceFreeLimit omega hanti hlim hφ hφanti
  set P : ℕ → Z → EReal := fun j => singularityEnvelope (θ + ε j • omega.form).val (φ j) with hPdef
  have hP : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val (P j) := fun j =>
    singularityEnvelope_isThetaPshPotential _ (θ + ε j • omega.form).2.1
      (θ + ε j • omega.form).2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) (φ j) (hφ j)
  have hPanti : ∀ x, Antitone fun j => P j x := fun x i j hij =>
    singularityEnvelope_antitone omega.isSemipositive hanti hφanti hij x
  have hP0 : ∀ j x, P j x ≤ 0 := fun j x => singularityEnvelope_le_zero _ _ x
  have huP : ∀ j, u ≤ P j := traceFreeLimit_le θ omega.form ε φ
  have hmassP : ∀ j, diagonalPotentialMass (θ + ε j • omega.form) (φ j) (hφ j) =
      diagonalPotentialMass (θ + ε j • omega.form) (P j) (hP j) := fun j =>
    (singularityEnvelopeMassPreserving omega (θ + ε j • omega.form) (φ j) (hφ j) (hP j)).symm
  have hu' : ∀ j, IsThetaPshPotential (θ + ε j • omega.form).val u := fun j =>
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (hε j).le)
  -- the lower bound
  have hlow : ∀ j, diagonalPotentialMass θ u hu ≤
      diagonalPotentialMass (θ + ε j • omega.form) (φ j) (hφ j) := fun j => by
    rw [hmassP j]
    exact DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul omega (hε j) hu (hP j)
      (huP j)
  -- the upper bound, for every `j₀`
  have hupper : ∀ j₀, limsup (fun j => diagonalPotentialMass (θ + ε j • omega.form) (φ j) (hφ j))
      atTop ≤ diagonalPotentialMass (θ + ε j₀ • omega.form) u (hu' j₀) := by
    intro j₀
    have htail : ∀ j, IsThetaPshPotential (θ + ε j₀ • omega.form).val (P (j + j₀)) := by
      intro j
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (hP (j + j₀))
        (KahlerDomination.isSemipositive_smul omega.isSemipositive
          (sub_nonneg.2 (hanti (Nat.le_add_left j₀ j))))
      rwa [show θ + ε (j + j₀) • omega.form + (ε j₀ - ε (j + j₀)) • omega.form =
        θ + ε j₀ • omega.form by module] at h
    have hcontact : ∀ j, diagonalPotentialMass (θ + ε (j + j₀) • omega.form) (φ (j + j₀))
        (hφ (j + j₀)) ≤ diagonalPotentialMeasure (θ + ε j₀ • omega.form) (P (j + j₀)) (htail j)
          {x | P (j + j₀) x = 0} := by
      intro j
      have hbig : IsBigClass (RealBottChern.ofRepresentative (θ + ε (j + j₀) • omega.form)) :=
        PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hu (hε _)
      have hzero := diagonalPotentialMeasure_singularityEnvelope_lt_zero_of_isBigClass hk omega
        (θ + ε (j + j₀) • omega.form) hbig (hφ (j + j₀)) (hP (j + j₀))
      have hsplit : (univ : Set Z) ⊆ {x | P (j + j₀) x < 0} ∪ {x | P (j + j₀) x = 0} := by
        intro x _
        rcases (hP0 (j + j₀) x).lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h
      calc diagonalPotentialMass (θ + ε (j + j₀) • omega.form) (φ (j + j₀)) (hφ (j + j₀))
          = diagonalPotentialMeasure (θ + ε (j + j₀) • omega.form) (P (j + j₀)) (hP (j + j₀))
              univ := hmassP (j + j₀)
        _ ≤ diagonalPotentialMeasure (θ + ε (j + j₀) • omega.form) (P (j + j₀)) (hP (j + j₀))
              ({x | P (j + j₀) x < 0} ∪ {x | P (j + j₀) x = 0}) := measure_mono hsplit
        _ ≤ diagonalPotentialMeasure (θ + ε (j + j₀) • omega.form) (P (j + j₀)) (hP (j + j₀))
              {x | P (j + j₀) x < 0} +
            diagonalPotentialMeasure (θ + ε (j + j₀) • omega.form) (P (j + j₀)) (hP (j + j₀))
              {x | P (j + j₀) x = 0} := measure_union_le _ _
        _ = diagonalPotentialMeasure (θ + ε (j + j₀) • omega.form) (P (j + j₀)) (hP (j + j₀))
              {x | P (j + j₀) x = 0} := by rw [hzero, zero_add]
        _ ≤ diagonalPotentialMeasure (θ + ε j₀ • omega.form) (P (j + j₀)) (htail j)
              {x | P (j + j₀) x = 0} :=
            diagonalPotentialMeasure_le_of_le omega (hanti (Nat.le_add_left j₀ j)) _ _ _
    have hlimP : ∀ x, Tendsto (fun j => P (j + j₀) x) atTop (𝓝 (u x)) := by
      intro x
      have hmono : Antitone fun j => P (j + j₀) x := fun a b hab =>
        hPanti x (Nat.add_le_add_right hab j₀)
      have hinf : (⨅ j, P (j + j₀) x) = u x := by
        rw [show (fun j => P (j + j₀) x) = fun j => P (j₀ + j) x by
          funext j; rw [add_comm]]
        exact iInf_add_eq_iInf_of_antitone (hPanti x) j₀
      rw [← hinf]
      exact tendsto_atTop_iInf hmono
    have hcl := DecreasingContactMassLimit.contactMeasure_limsup_le_of_antitone_of_tendsto omega
      (θ + ε j₀ • omega.form) (fun j => P (j + j₀)) htail (fun j x => hP0 _ x) u (hu' j₀)
      (fun a b hab x => hPanti x (Nat.add_le_add_right hab j₀)) hlimP
    calc limsup (fun j => diagonalPotentialMass (θ + ε j • omega.form) (φ j) (hφ j)) atTop
        = limsup (fun j => diagonalPotentialMass (θ + ε (j + j₀) • omega.form) (φ (j + j₀))
            (hφ (j + j₀))) atTop :=
          (limsup_nat_add (fun j => diagonalPotentialMass (θ + ε j • omega.form) (φ j) (hφ j))
            j₀).symm
      _ ≤ limsup (fun j => diagonalPotentialMeasure (θ + ε j₀ • omega.form) (P (j + j₀))
            (htail j) {x | P (j + j₀) x = 0}) atTop :=
          limsup_le_limsup (Eventually.of_forall hcontact)
      _ ≤ diagonalPotentialMeasure (θ + ε j₀ • omega.form) u (hu' j₀) {x | u x = 0} := hcl
      _ ≤ diagonalPotentialMass (θ + ε j₀ • omega.form) u (hu' j₀) := measure_mono (subset_univ _)
  have hT := tendsto_diagonalPotentialMass_add_smul omega hu hε hlim hu'
  have hls := ge_of_tendsto' hT hupper
  exact tendsto_of_le_liminf_of_limsup_le (le_liminf_of_le (h := Eventually.of_forall hlow)) hls

end DX24

end

end SGPT.Foundations.Analysis.Pending.TraceFreeLimit
