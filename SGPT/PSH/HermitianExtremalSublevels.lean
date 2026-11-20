import SGPT.PSH.HermitianExtremalEnvelopeValues
import SGPT.PSH.HermitianExtremalMassLimit

/-!
# The actual compact-sublevel extremal double sequence

The sets and extremals are literal functions. Continuity of the given
real regularizations produces compact sublevels and open strict sublevels.
Their pointwise antitonicity gives the decreasing inner extremals. At a
pole the strict sublevels eventually have nonempty interior, so the
inner limit belongs to the actual nonclosed Hermitian class. Its zero
values on the original poles make it an original extremal competitor.

Source: FPT, `thm:compact-complex-global-josefson`, Step 1.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianExtremalMassLimit
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Source `K_{j,N+1}`; the positive level is indexed by a natural number. -/
def compactSublevel (K : Set M) (f : ℕ → M → ℝ) (j N : ℕ) : Set M :=
  K ∩ {x | f j x ≤ -((N : ℝ) + 1)}

/-- Source `O_{j,N+1}`. -/
def strictSublevel (U : Set M) (f : ℕ → M → ℝ) (j N : ℕ) : Set M :=
  U ∩ {x | f j x < -((N : ℝ) + 1)}

theorem compactSublevel_isCompact {K : Set M} {f : ℕ → M → ℝ}
    (hK : IsCompact K) (hf : ∀ j, ContinuousOn (f j) K) (j N : ℕ) :
    IsCompact (compactSublevel K f j N) :=
  (hf j).lowerSemicontinuousOn.isCompact_inter_preimage_Iic hK _

theorem strictSublevel_isOpen {U : Set M} {f : ℕ → M → ℝ}
    (hU : IsOpen U) (hf : ∀ j, ContinuousOn (f j) U) (j N : ℕ) :
    IsOpen (strictSublevel U f j N) :=
  (hf j).isOpen_inter_preimage hU isOpen_Iio

omit [TopologicalSpace M] in
theorem strictSublevel_subset_compactSublevel {U K : Set M} {f : ℕ → M → ℝ}
    (hUK : U ⊆ K) (j N : ℕ) :
    strictSublevel U f j N ⊆ compactSublevel K f j N := by
  intro x hx
  change x ∈ U ∧ f j x < -((N : ℝ) + 1) at hx
  exact ⟨hUK hx.1, hx.2.le⟩

omit [TopologicalSpace M] in
theorem compactSublevel_mono_j {K : Set M} {f : ℕ → M → ℝ}
    (hf : ∀ x ∈ K, Antitone fun j => f j x) (N : ℕ) :
    Monotone fun j => compactSublevel K f j N := by
  intro j k hjk x hx
  exact ⟨hx.1, (hf x hx.1 hjk).trans hx.2⟩

omit [TopologicalSpace M] in
theorem compactSublevel_antitone_N (K : Set M) (f : ℕ → M → ℝ) (j : ℕ) :
    Antitone fun N => compactSublevel K f j N := by
  intro N P hNP x hx
  change x ∈ K ∧ f j x ≤ -((P : ℝ) + 1) at hx
  change x ∈ K ∧ f j x ≤ -((N : ℝ) + 1)
  refine ⟨hx.1, hx.2.trans ?_⟩
  have h : (N : ℝ) ≤ P := by exact_mod_cast hNP
  linarith

/-- Every finite threshold is eventually crossed at an original pole.
The original open strict sublevel therefore gives genuine interior. -/
theorem eventually_nonempty_interior_compactSublevel {U K : Set M}
    {f : ℕ → M → ℝ} (hU : IsOpen U) (hUK : U ⊆ K)
    (hf : ∀ j, ContinuousOn (f j) U) {x : M} (hx : x ∈ U)
    (hlim : Tendsto (fun j => (f j x : EReal)) atTop (𝓝 ⊥)) (N : ℕ) :
    ∀ᶠ j in atTop, (interior (compactSublevel K f j N)).Nonempty := by
  have hev : ∀ᶠ j in atTop, (f j x : EReal) < (-((N : ℝ) + 1) : ℝ) :=
    (tendsto_order.mp hlim).2 _ (EReal.bot_lt_coe _)
  filter_upwards [hev] with j hj
  exact ⟨x, interior_maximal (strictSublevel_subset_compactSublevel hUK j N)
    (strictSublevel_isOpen hU hf j N) ⟨hx, EReal.coe_lt_coe_iff.mp hj⟩⟩

/-- The actual inner infimum, including all early indices. Antitonicity
will prove that removing any finite prefix leaves it unchanged. -/
def sublevelLimit (ω : Background (m + 1) M) (K : Set M)
    (f : ℕ → M → ℝ) (N : ℕ) : M → EReal :=
  fun x => ⨅ j, regularizedExtremal ω (compactSublevel K f j N) x

theorem sublevelExtremal_antitone_j (ω : Background (m + 1) M)
    {K : Set M} {f : ℕ → M → ℝ}
    (hf : ∀ x ∈ K, Antitone fun j => f j x) (N : ℕ) (x : M) :
    Antitone fun j => regularizedExtremal ω (compactSublevel K f j N) x :=
  fun _ _ hjk => regularizedExtremal_antitone ω (compactSublevel_mono_j hf N hjk) x

theorem sublevelLimit_nonneg (ω : Background (m + 1) M) (K : Set M)
    (f : ℕ → M → ℝ) (N : ℕ) (x : M) : 0 ≤ sublevelLimit ω K f N x :=
  le_iInf fun _j => regularizedExtremal_nonneg ω _ x

theorem sublevelLimit_monotone (ω : Background (m + 1) M) (K : Set M)
    (f : ℕ → M → ℝ) (x : M) : Monotone fun N => sublevelLimit ω K f N x := by
  intro N P hNP
  exact iInf_mono fun j => regularizedExtremal_antitone ω
    (compactSublevel_antitone_N K f j hNP) x

variable [CompactSpace M] [ConnectedSpace M]

/-- Eventual nonempty interior manufactures the actual Hermitian PSH
inner infimum, without assuming membership or a nonpole for that limit. -/
theorem sublevelLimit_isHermitianPSH (ω : Background (m + 1) M)
    {K : Set M} {f : ℕ → M → ℝ}
    (hf : ∀ x ∈ K, Antitone fun j => f j x) (N : ℕ)
    (hinterior : ∀ᶠ j in atTop, (interior (compactSublevel K f j N)).Nonempty) :
    IsHermitianPSH ω (sublevelLimit ω K f N) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hinterior
  have hclass (j : ℕ) :
      IsHermitianPSH ω (regularizedExtremal ω (compactSublevel K f (j + J) N)) :=
    (bounded_regularizedExtremal_of_nonempty_interior ω _
      (hJ (j + J) (Nat.le_add_left J j))).choose_spec.1
  have hanti (x : M) : Antitone fun j =>
      regularizedExtremal ω (compactSublevel K f (j + J) N) x :=
    fun _ _ hjk => sublevelExtremal_antitone_j ω hf N x (Nat.add_le_add_right hjk J)
  have h := (isHermitianPSH_iInf_of_nonneg ω hclass hanti
    (fun j x => regularizedExtremal_nonneg ω _ x)).1
  have heq : (fun x => ⨅ j, regularizedExtremal ω (compactSublevel K f (j + J) N) x) =
      sublevelLimit ω K f N :=
    funext fun x => (sublevelExtremal_antitone_j ω hf N x).iInf_nat_add J
  exact heq ▸ h

/-- An original pole of the convergent real regularizations supplies the
eventual-interior input for every threshold, internally. -/
theorem sublevelLimit_isHermitianPSH_of_pole (ω : Background (m + 1) M)
    {U K : Set M} {f : ℕ → M → ℝ}
    (hU : IsOpen U) (hUK : U ⊆ K) (hf : ∀ j, ContinuousOn (f j) U)
    (hanti : ∀ x ∈ K, Antitone fun j => f j x)
    {x : M} (hx : x ∈ U)
    (hlim : Tendsto (fun j => (f j x : EReal)) atTop (𝓝 ⊥)) (N : ℕ) :
    IsHermitianPSH ω (sublevelLimit ω K f N) :=
  sublevelLimit_isHermitianPSH ω hanti N
    (eventually_nonempty_interior_compactSublevel hU hUK hf hx hlim N)

omit [CompactSpace M] [ConnectedSpace M] in
/-- Actual pointwise convergence to a value below the threshold gives a
zero value of the literal inner extremal. -/
theorem sublevelLimit_eq_zero_of_lt (ω : Background (m + 1) M)
    {U K : Set M} {f : ℕ → M → ℝ} {φ : M → EReal}
    (hU : IsOpen U) (hUK : U ⊆ K) (hf : ∀ j, ContinuousOn (f j) U)
    {x : M} (hx : x ∈ U) (N : ℕ)
    (hlim : Tendsto (fun j => (f j x : EReal)) atTop (𝓝 (φ x)))
    (hlt : φ x < (-((N : ℝ) + 1) : ℝ)) : sublevelLimit ω K f N x = 0 := by
  obtain ⟨j, hj⟩ := ((tendsto_order.mp hlim).2 _ hlt).exists
  have hz := regularizedExtremal_eq_zero_on_open ω
    (strictSublevel_isOpen hU hf j N) (strictSublevel_subset_compactSublevel hUK j N)
    ⟨hx, EReal.coe_lt_coe_iff.mp hj⟩
  exact le_antisymm ((iInf_le _ j).trans hz.le) (sublevelLimit_nonneg ω K f N x)

omit [CompactSpace M] [ConnectedSpace M] in
/-- A genuine inner limit is an original competitor for the pole set, so
the previously manufactured extremal of that pole set bounds it. -/
theorem sublevelLimit_le_regularized_pole_extremal (ω : Background (m + 1) M)
    {U K : Set M} {f : ℕ → M → ℝ} {φ : M → EReal}
    (hU : IsOpen U) (hUK : U ⊆ K) (hf : ∀ j, ContinuousOn (f j) U)
    (hlim : ∀ x ∈ U, Tendsto (fun j => (f j x : EReal)) atTop (𝓝 (φ x)))
    (N : ℕ) (hclass : IsHermitianPSH ω (sublevelLimit ω K f N)) :
    sublevelLimit ω K f N ≤ regularizedExtremal ω (U ∩ {x | φ x = ⊥}) := by
  apply competitor_le_regularizedExtremal ω
  refine ⟨hclass, fun x hx => ?_⟩
  have hlt : φ x < (-((N : ℝ) + 1) : ℝ) := by rw [hx.2]; exact EReal.bot_lt_coe _
  exact (sublevelLimit_eq_zero_of_lt ω hU hUK hf hx.1 N (hlim x hx.1) hlt).le

omit [CompactSpace M] [ConnectedSpace M] in
/-- The actual outer upper envelope is in the same Hermitian class once
one finite bound for the original pole-set extremal is available. -/
theorem sublevel_outer_isHermitianPSH (ω : Background (m + 1) M)
    {U K : Set M} {f : ℕ → M → ℝ} {φ : M → EReal}
    (hU : IsOpen U) (hUK : U ⊆ K) (hf : ∀ j, ContinuousOn (f j) U)
    (hlim : ∀ x ∈ U, Tendsto (fun j => (f j x : EReal)) atTop (𝓝 (φ x)))
    (hclass : ∀ N, IsHermitianPSH ω (sublevelLimit ω K f N))
    (C : ℝ) (hC : ∀ x, regularizedExtremal ω (U ∩ {x | φ x = ⊥}) x ≤ (C : EReal)) :
    IsHermitianPSH ω (uscRegularization (fun x => ⨆ N, sublevelLimit ω K f N x)) ∧
      (∀ x, 0 ≤ uscRegularization (fun x => ⨆ N, sublevelLimit ω K f N x) x) ∧
      ∀ x, uscRegularization (fun x => ⨆ N, sublevelLimit ω K f N x) x ≤ (C : EReal) := by
  have hbound : ∀ N x, sublevelLimit ω K f N x ≤ (C : EReal) :=
    fun N x => (sublevelLimit_le_regularized_pole_extremal ω hU hUK hf hlim N (hclass N) x).trans
      (hC x)
  refine ⟨isHermitianPSH_uscRegularization_iSup_of_uniform_bound ω _ hclass C hbound,
    fun x => ?_, fun x => ?_⟩
  · exact ((sublevelLimit_nonneg ω K f 0 x).trans
      (le_iSup (fun N => sublevelLimit ω K f N x) 0)).trans
      (le_uscRegularization (fun x => ⨆ N, sublevelLimit ω K f N x) x)
  · apply uscRegularization_le_of_eventually_le upperSemicontinuousAt_const
    exact Eventually.of_forall fun x => iSup_le fun N => hbound N x

end SGPT.PSH.HermitianExtremal
