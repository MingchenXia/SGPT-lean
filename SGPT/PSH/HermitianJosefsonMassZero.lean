import SGPT.PSH.HermitianExtremalGlobalCapacity
import SGPT.PSH.HermitianExtremalSublevelTail
import SGPT.PSH.HermitianProductsCanonicalMassContinuity

/-!
# Vanishing of the actual outer-extremal Hermitian mass

The local nonpole branch supplies bounded actual inner extremals and their
bounded USC supremum. Canonical product continuity passes the uniform
radial capacity budget through the two actual limits. The resulting zero
is the total mass of the genuine global Hermitian Monge--Ampère measure.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianGlobalProducts HermitianExtremalMassLimit HermitianExtremalNormalization
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
private theorem globalMixedMeasure_congr_functions
    (omega : Background (m + 1) M) (u v : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i)) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (hbv : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    (heq : u = v) : globalMixedMeasure omega u hu hb = globalMixedMeasure omega v hv hbv := by
  cases heq
  rfl

/-- The literal outer extremal in the radial proof. -/
def chartRadialOuter (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    (a : ComplexModel (m + 1)) (r T : ℝ) (u : ComplexModel (m + 1) → EReal) : M → EReal :=
  uscRegularization (fun x => ⨆ N, sublevelLimit omega (chartClosedBall e a r)
    (chartRadialApproximation e ((T - r) / 2) u) N x)

/-- Under the actual nonpole branch, the genuine bounded outer extremal
has zero canonical global Monge--Ampère mass. No mass functional,
continuity conclusion, support assertion or capacity estimate is assumed. -/
theorem chartRadial_outer_globalMass_eq_zero
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    (Ω : Opens (ComplexModel (m + 1)))
    (hcompact : IsCompact (closure (Ω : Set (ComplexModel (m + 1)))))
    (htarget : closure (Ω : Set (ComplexModel (m + 1))) ⊆ e.val.target)
    (a : ComplexModel (m + 1)) {r R T : ℝ}
    (hR : 0 < R) (hr : r < R / 2) (hRT : 3 * R < T)
    (hΩ : closedBall a (5 * R) ⊆ Ω)
    {u : ComplexModel (m + 1) → EReal} (hu : PlurisubharmonicOn u (ball a T))
    (hne : ∃ z ∈ ball a T, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a T, u z ≤ 0)
    (hpole : ∃ z ∈ ball a r, u z = ⊥)
    (hnot : ¬ ∃ q : M → EReal, IsHermitianPSH omega q ∧
      ∀ x ∈ chartBall e a r ∩ {x | u (e.val x) = ⊥}, q x = ⊥) :
    ∃ (C : ℝ) (hO : IsHermitianPSH omega (chartRadialOuter omega e a r T u))
      (hbO : ∀ x, 0 ≤ chartRadialOuter omega e a r T u x ∧
        chartRadialOuter omega e a r T u x ≤ (C : EReal)),
      globalMixedMeasure omega (fun _ => chartRadialOuter omega e a r T u) (fun _ => hO)
        (fun _ => ⟨0, C, hbO⟩) univ = 0 := by
  classical
  have hrT : r < T := by linarith
  have hballTarget : closedBall a r ⊆ e.val.target :=
    (closedBall_subset_closedBall (by linarith : r ≤ 5 * R)).trans
      (hΩ.trans (subset_closure.trans htarget))
  obtain ⟨C, hInnerBound, hO, hOpos, hOupper⟩ := chartRadial_sublevel_outer_of_not_pole
    omega e a hrT hballTarget hu hne hnonpos hpole hnot
  let K := chartClosedBall e a r
  let f := chartRadialApproximation e ((T - r) / 2) u
  let I := fun N => sublevelLimit omega K f (N + 1)
  have hI (N : ℕ) : IsHermitianPSH omega (I N) :=
    chartRadial_sublevelLimit_isHermitianPSH omega e a hrT hballTarget hu hne hnonpos hpole (N + 1)
  have hIb (N : ℕ) : ∀ x, ((0 : ℝ) : EReal) ≤ I N x ∧ I N x ≤ (C : EReal) := by
    intro x
    exact ⟨by simpa only [EReal.coe_zero] using sublevelLimit_nonneg omega K f (N + 1) x,
      hInnerBound (N + 1) x⟩
  have hImono : Monotone I := by
    intro N P hNP x
    exact sublevelLimit_monotone omega K f x (Nat.add_le_add_right hNP 1)
  have hOuterEq : uscRegularization (fun x => ⨆ N, I N x) =
      chartRadialOuter omega e a r T u := by
    apply congrArg uscRegularization
    funext x
    exact (sublevelLimit_monotone omega K f x).iSup_nat_add 1
  have htail : ∀ N, ∃ J : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      (∀ j, IsHermitianPSH omega (regularizedExtremal omega (compactSublevel K f (j + J) (N + 1)))) ∧
      (∀ j x, 0 ≤ regularizedExtremal omega (compactSublevel K f (j + J) (N + 1)) x ∧
        regularizedExtremal omega (compactSublevel K f (j + J) (N + 1)) x ≤ (B : EReal)) ∧
      (∀ x, Antitone fun j => regularizedExtremal omega (compactSublevel K f (j + J) (N + 1)) x) ∧
      (fun x => ⨅ j, regularizedExtremal omega (compactSublevel K f (j + J) (N + 1)) x) = I N ∧
      Tendsto (fun j => (⨆ x, regularizedExtremal omega
        (compactSublevel K f (j + J) (N + 1)) x).toReal)
        atTop (𝓝 (⨆ x, I N x).toReal) := fun N =>
    exists_chartRadial_bounded_sublevel_tail omega e a hrT hballTarget hu hne hnonpos hpole (N + 1)
  choose J B htail using htail
  let w : ℕ → ℕ → M → EReal := fun j N => regularizedExtremal omega
    (compactSublevel K f (j + J N) (N + 1))
  have hw (N j : ℕ) : IsHermitianPSH omega (w j N) := (htail N).2.1 j
  have hwb (N j : ℕ) : ∀ x, ((0 : ℝ) : EReal) ≤ w j N x ∧ w j N x ≤ (B N : EReal) := by
    intro x
    exact ⟨by simpa only [EReal.coe_zero] using ((htail N).2.2.1 j x).1,
      ((htail N).2.2.1 j x).2⟩
  have hwinf (N : ℕ) : (fun x => ⨅ j, w j N x) = I N := (htail N).2.2.2.2.1
  have hwanti (N : ℕ) : Antitone (fun j => w j N) := by
    intro j k hjk x
    exact (htail N).2.2.2.1 x hjk
  let mass : ℕ → ℕ → ℝ := fun j N =>
    (globalMixedMeasure omega (fun _ => w j N) (fun _ => hw N j)
      (fun _ => ⟨0, B N, hwb N j⟩) univ).toReal
  let sup : ℕ → ℕ → ℝ := fun j N => (⨆ x, w j N x).toReal
  let aMass : ℕ → ℝ := fun N =>
    (globalMixedMeasure omega (fun _ => I N) (fun _ => hI N) (fun _ => ⟨0, C, hIb N⟩) univ).toReal
  let bSup : ℕ → ℝ := fun N => (⨆ x, I N x).toReal
  let hbO : ∀ x, 0 ≤ chartRadialOuter omega e a r T u x ∧
      chartRadialOuter omega e a r T u x ≤ (C : EReal) := fun x => ⟨hOpos x, hOupper x⟩
  let μ := globalMixedMeasure omega (fun _ => chartRadialOuter omega e a r T u)
    (fun _ => hO) (fun _ => ⟨0, C, hbO⟩)
  have hmass (N : ℕ) : Tendsto (fun j => mass j N) atTop (𝓝 (aMass N)) := by
    have h := tendsto_globalMixedMeasure_real_mass_decreasing_iInf omega
      (fun j _ => w j N) (fun j _ => hw N j) 0 (B N) (fun j _ => hwb N j) (fun _ => hwanti N)
    dsimp only at h
    have heq : (fun (_ : Fin (m + 1)) x => ⨅ j, w j N x) = fun _ => I N :=
      funext fun _ => hwinf N
    have hread (hu₀ : ∀ _ : Fin (m + 1), IsHermitianPSH omega (fun x => ⨅ j, w j N x))
        (hb₀ : ∀ _ : Fin (m + 1), ∃ a b : ℝ, ∀ x,
          (a : EReal) ≤ (⨅ j, w j N x) ∧ (⨅ j, w j N x) ≤ (b : EReal)) :
        globalMixedMeasure omega (fun _ x => ⨅ j, w j N x) hu₀ hb₀ =
          globalMixedMeasure omega (fun _ => I N) (fun _ => hI N) (fun _ => ⟨0, C, hIb N⟩) :=
      globalMixedMeasure_congr_functions omega _ _ hu₀ (fun _ => hI N) hb₀
        (fun _ => ⟨0, C, hIb N⟩) heq
    simpa only [hread] using h
  have hsup (N : ℕ) : Tendsto (fun j => sup j N) atTop (𝓝 (bSup N)) :=
    (htail N).2.2.2.2.2
  have hlim : Tendsto aMass atTop (𝓝 (μ univ).toReal) := by
    have h := tendsto_globalMixedMeasure_real_mass_increasing_uscSup omega
      (fun N _ => I N) (fun N _ => hI N) 0 C (fun N _ => hIb N) (fun _ => hImono)
    dsimp only at h
    have hread
        (hu₀ : ∀ _ : Fin (m + 1), IsHermitianPSH omega (uscRegularization (fun x => ⨆ N, I N x)))
        (hb₀ : ∀ _ : Fin (m + 1), ∃ a b : ℝ, ∀ x,
          (a : EReal) ≤ uscRegularization (fun x => ⨆ N, I N x) x ∧
          uscRegularization (fun x => ⨆ N, I N x) x ≤ (b : EReal)) :
        globalMixedMeasure omega (fun _ => uscRegularization (fun x => ⨆ N, I N x)) hu₀ hb₀ = μ :=
      globalMixedMeasure_congr_functions omega _ _ hu₀ (fun _ => hO) hb₀
        (fun _ => ⟨0, C, hbO⟩) (congrArg (fun φ => fun _ : Fin (m + 1) => φ) hOuterEq)
    simpa only [hread] using h
  obtain ⟨D, hD, hbudget⟩ := exists_extremal_globalMass_radial_bound omega e Ω hcompact htarget
    a hR hr hRT hΩ hu hne hnonpos
  have hbound : ∀ N, ∀ᶠ j in atTop,
      mass j N ≤ max 1 (sup j N) ^ (m + 1) * D / ((N : ℝ) + 1) := by
    intro N
    apply Eventually.of_forall
    intro j
    obtain ⟨S, hS, hSupper, _⟩ := exists_real_sup omega (hw N j)
    have hcap := hbudget (j + J N) N S (hw N j) hSupper
    have hcapReal := ENNReal.toReal_mono (by simp) hcap
    rw [ENNReal.toReal_ofReal (by positivity)] at hcapReal
    have hsupReal : sup j N = S := by
      change (⨆ x, w j N x).toReal = S
      rw [hS, EReal.toReal_coe]
    rw [hsupReal]
    convert hcapReal using 1; ring
  have hbSup (N : ℕ) : bSup N ≤ C := by
    have hlow : (0 : EReal) ≤ ⨆ x, I N x := by
      obtain ⟨x⟩ := (inferInstance : Nonempty M)
      exact (sublevelLimit_nonneg omega K f (N + 1) x).trans (le_iSup (I N) x)
    exact EReal.toReal_le_toReal (iSup_le fun x => (hIb N x).2)
      (ne_of_gt ((EReal.bot_lt_coe 0).trans_le hlow)) (EReal.coe_ne_top C)
  have hzero : (μ univ).toReal = 0 := zero_of_double_limit_capacity_bound
    (m + 1) C D hD mass sup aMass bSup (μ univ).toReal hmass hsup hbound hbSup
      (fun _ => ENNReal.toReal_nonneg) hlim
  have hfinite : μ univ ≠ ⊤ := by
    let _ := globalMixedMeasure_isFiniteMeasure (omega := omega)
      (fun _ => chartRadialOuter omega e a r T u) (fun _ => hO) (fun _ => ⟨0, C, hbO⟩)
    exact (measure_lt_top μ univ).ne
  exact ⟨C, hO, hbO, ((ENNReal.toReal_eq_zero_iff (μ univ)).mp hzero).resolve_right hfinite⟩

end SGPT.PSH.HermitianExtremal
