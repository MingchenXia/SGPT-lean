import SGPT.Foundations.Analysis.Pending.SingularModelEnergyLayout
import SGPT.Foundations.Analysis.Pending.FullMixedSingularIntegrationByParts
import SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance

set_option autoImplicit false

/-!
# Actual singular finite-type energy cocycle

Xia SGPT PDF0118, Lemma 3.1.3 and equation (3.32). Induction on actual
layout sums uses proved full singular mixed integration by parts, genuine
slot permutation and integrable canonical differences. The model and every
potential may be unbounded. No integration-by-parts or cocycle premise is used.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyCocycle

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  BoundedMongeAmpereEnergy SingularModelEnergyLayout GlobalDiagonalScaling
  FullMixedSingularIntegrationByParts RelativeDarvasDistance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Cocycle of actual canonical layout integrals for singular same-type endpoints. -/
theorem sum_lay_cocycle (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {a b c : M → EReal} (ha : IsThetaPshPotential θ.val a)
    (hb : IsThetaPshPotential θ.val b) (hc : IsThetaPshPotential θ.val c)
    (hab : SameSingularityTypeOn a b univ) (hbc : SameSingularityTypeOn b c univ) :
    ∀ k, k ≤ n → ∀ (S : Fin n → M → EReal) (hS : ∀ i, IsThetaPshPotential θ.val (S i)),
      (∑ j ∈ Finset.range (k + 1), ∫ x, canonicalERealDiffToReal (a x) (c x)
        ∂layMeasure θ k j a c S ha.1 hc.1 (fun i => (hS i).1)) -
      (∑ j ∈ Finset.range (k + 1), ∫ x, canonicalERealDiffToReal (b x) (c x)
        ∂layMeasure θ k j b c S hb.1 hc.1 (fun i => (hS i).1)) =
      ∑ j ∈ Finset.range (k + 1), ∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂layMeasure θ k j a b S ha.1 hb.1 (fun i => (hS i).1) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ S hS
    simp only [zero_add, Finset.sum_range_one]
    have e : ∀ (x y : M → EReal) (hx : ThetaPlurisubharmonic θ.val x)
        (hy : ThetaPlurisubharmonic θ.val y),
        layMeasure θ 0 0 x y S hx hy (fun i => (hS i).1) =
          globalMixedMeasure (fun _ => θ) S (fun i => (hS i).1) := fun x y hx hy =>
      globalMixedMeasure_congr rfl (lay_zero_zero x y S) _ _
    rw [e, e, e]
    have h := integral_canonicalDiff_add_layMeasure omega θ ha hb hc hab hbc 0 0
      ha.1 hb.1 (fun i => (hS i).1)
    rw [e] at h
    linarith
  | succ k ih =>
    intro hk S hS
    have hkn : k < n := by omega
    let i₀ : Fin n := ⟨k, hkn⟩
    have hSc : ∀ i, IsThetaPshPotential θ.val (Function.update S i₀ c i) := by
      intro i
      by_cases h : i = i₀
      · subst i; simpa using hc
      · simpa [Function.update_of_ne h] using hS i
    have hIH := ih (by omega) (Function.update S i₀ c) hSc
    have hlow : ∀ (x : M → EReal) (hx : ThetaPlurisubharmonic θ.val x) (j : ℕ),
        layMeasure θ (k + 1) j x c S hx hc.1 (fun i => (hS i).1) =
          layMeasure θ k j x c (Function.update S i₀ c) hx hc.1 (fun i => (hSc i).1) :=
      fun x hx j => globalMixedMeasure_congr rfl (lay_succ_eq hkn x c S) _ _
    have htopA : layMeasure θ (k + 1) (k + 1) a c S ha.1 hc.1 (fun i => (hS i).1) =
        layMeasure θ (k + 1) (k + 1) a b S ha.1 hb.1 (fun i => (hS i).1) :=
      globalMixedMeasure_congr rfl (by
        funext i; simp only [lay]; split_ifs <;> rfl) _ _
    have htopB : layMeasure θ (k + 1) (k + 1) b c S hb.1 hc.1 (fun i => (hS i).1) =
        layMeasure θ (k + 1) 0 a b S ha.1 hb.1 (fun i => (hS i).1) :=
      globalMixedMeasure_congr rfl (by
        funext i; simp only [lay]; split_ifs <;> first | rfl | omega) _ _
    have hsA : (∑ j ∈ Finset.range (k + 1 + 1),
        ∫ x, canonicalERealDiffToReal (a x) (c x)
          ∂layMeasure θ (k + 1) j a c S ha.1 hc.1 (fun i => (hS i).1)) =
        (∑ j ∈ Finset.range (k + 1), ∫ x, canonicalERealDiffToReal (a x) (c x)
          ∂layMeasure θ k j a c (Function.update S i₀ c) ha.1 hc.1 (fun i => (hSc i).1)) +
        ∫ x, canonicalERealDiffToReal (a x) (c x)
          ∂layMeasure θ (k + 1) (k + 1) a b S ha.1 hb.1 (fun i => (hS i).1) := by
      rw [Finset.sum_range_succ, htopA]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hlow]
    have hsB : (∑ j ∈ Finset.range (k + 1 + 1),
        ∫ x, canonicalERealDiffToReal (b x) (c x)
          ∂layMeasure θ (k + 1) j b c S hb.1 hc.1 (fun i => (hS i).1)) =
        (∑ j ∈ Finset.range (k + 1), ∫ x, canonicalERealDiffToReal (b x) (c x)
          ∂layMeasure θ k j b c (Function.update S i₀ c) hb.1 hc.1 (fun i => (hSc i).1)) +
        ∫ x, canonicalERealDiffToReal (b x) (c x)
          ∂layMeasure θ (k + 1) 0 a b S ha.1 hb.1 (fun i => (hS i).1) := by
      rw [Finset.sum_range_succ, htopB]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hlow]
    rw [hsA, hsB, Finset.sum_range_succ (fun j =>
      ∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂layMeasure θ (k + 1) j a b S ha.1 hb.1 (fun i => (hS i).1)) (k + 1)]
    let L : ℕ → Measure M := fun j =>
      layMeasure θ (k + 1) j a b S ha.1 hb.1 (fun i => (hS i).1)
    let Lc : ℕ → Measure M := fun j =>
      layMeasure θ k j a b (Function.update S i₀ c) ha.1 hb.1 (fun i => (hSc i).1)
    have hibp : ∀ j ∈ Finset.range (k + 1),
        (∫ x, canonicalERealDiffToReal (a x) (b x) ∂Lc j) =
          (∫ x, canonicalERealDiffToReal (a x) (b x) ∂L j) -
            ((∫ x, canonicalERealDiffToReal (b x) (c x) ∂L (j + 1)) -
              ∫ x, canonicalERealDiffToReal (b x) (c x) ∂L j) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      let w := lay k j a b S
      have hother : ∀ i, i ≠ i₀ →
          IsThetaPshPotential ((fun _ : Fin n => θ) i).val (w i) :=
        fun i _ => lay_genuine ha hb hS i
      have h := integral_sub_mixed_update_symm omega i₀ hother ha hb hb hc hab hbc
      have eupdate (r : M → EReal) (hr : IsThetaPshPotential θ.val r)
          (T : Fin n → M → EReal) (hT : ∀ i, ThetaPlurisubharmonic θ.val (T i))
          (eT : Function.update w i₀ r = T) :
          updatedMixedMeasure i₀ hother hr = globalMixedMeasure (fun _ => θ) T hT :=
        globalMixedMeasure_congr (Function.update_eq_self i₀ _) eT _ _
      have eb : updatedMixedMeasure i₀ hother hb = L j :=
        eupdate b hb _ _ (update_lay_eq hkn hjk a b S)
      have ec : updatedMixedMeasure i₀ hother hc = Lc j :=
        eupdate c hc _ _ (update_lay_eq_lay_update hkn hjk a b c S)
      have ea : updatedMixedMeasure i₀ hother ha = L (j + 1) := by
        have hraw := fun i =>
          (isThetaPshPotential_update i₀ hother ha i).1
        have hperm := GlobalSlotPerm.globalMixedMeasure_perm hraw
          (Equiv.swap (⟨j, by omega⟩ : Fin n) i₀)
        change globalMixedMeasure _ _ _ = L (j + 1)
        rw [← hperm]
        refine globalMixedMeasure_congr ?_ (update_lay_swap hkn hjk a b S) _ _
        funext i
        simp only [Function.update_eq_self]
      rw [eb, ec, ea] at h
      linarith
    rw [Finset.sum_congr rfl hibp] at hIH
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub
      (fun j => ∫ x, canonicalERealDiffToReal (b x) (c x) ∂L j)] at hIH
    have htop := integral_canonicalDiff_add_layMeasure omega θ ha hb hc hab hbc
      (k + 1) (k + 1) ha.1 hb.1 (fun i => (hS i).1)
    change (∫ x, canonicalERealDiffToReal (a x) (c x) ∂L (k + 1)) =
      (∫ x, canonicalERealDiffToReal (a x) (b x) ∂L (k + 1)) +
        ∫ x, canonicalERealDiffToReal (b x) (c x) ∂L (k + 1) at htop
    linarith

/-- The actual finite-type energy cocycle for an arbitrarily singular reference. -/
theorem relativeEnergyOfMinimalType_sub (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : SameSingularityTypeOn u φ univ) (hvφ : SameSingularityTypeOn v φ univ) :
    relativeEnergyOfMinimalType θ φ u hφ hu - relativeEnergyOfMinimalType θ φ v hφ hv =
      relativeEnergyOfMinimalType θ v u hv hu := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := sum_lay_cocycle omega θ hu hv hφ (huφ.trans hvφ.symm) hvφ
    n le_rfl (fun _ => φ) (fun _ => hφ)
  rw [← relativeEnergyOfMinimalType_mul_canonical θ hφ hu,
    ← relativeEnergyOfMinimalType_mul_canonical θ hφ hv] at h
  have h2 := relativeEnergyOfMinimalType_mul_canonical θ hv hu
  have e : ∀ j, layMeasure θ n j u v (fun _ => φ) hu.1 hv.1 (fun _ => hφ.1) =
      layMeasure θ n j u v (fun _ => v) hu.1 hv.1 (fun _ => hv.1) := fun j =>
    globalMixedMeasure_congr rfl (lay_n_eq j u v _ _) _ _
  simp only [e] at h
  rw [← h2] at h
  have h3 : ((n : ℝ) + 1) * (relativeEnergyOfMinimalType θ φ u hφ hu -
      relativeEnergyOfMinimalType θ φ v hφ hv) =
      ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ v u hv hu := by
    rw [mul_sub, h]
  exact mul_left_cancel₀ hpos.ne' h3

/-- Energy differences for singular same-type endpoints satisfy the actual endpoint bounds. -/
theorem integral_le_relativeEnergyOfMinimalType_sub_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : SameSingularityTypeOn u φ univ) (hvφ : SameSingularityTypeOn v φ univ) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun _ => θ) (fun _ => u) (fun _ => hu.1)) ≤
        relativeEnergyOfMinimalType θ φ u hφ hu - relativeEnergyOfMinimalType θ φ v hφ hv ∧
    relativeEnergyOfMinimalType θ φ u hφ hu - relativeEnergyOfMinimalType θ φ v hφ hv ≤
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun _ => θ) (fun _ => v) (fun _ => hv.1) := by
  rw [relativeEnergyOfMinimalType_sub omega θ hφ hu hv huφ hvφ]
  exact RelativeEnergyMixedComparison.integral_le_relativeEnergyOfMinimalType_le
    omega θ hu hv (huφ.trans hvφ.symm)

/-- Genuine same-type potentials have increasing energy, even for a singular reference. -/
theorem relativeEnergyOfMinimalType_mono (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : SameSingularityTypeOn u φ univ) (hvφ : SameSingularityTypeOn v φ univ)
    (huv : u ≤ v) :
    relativeEnergyOfMinimalType θ φ u hφ hu ≤ relativeEnergyOfMinimalType θ φ v hφ hv := by
  have h := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hv hu hvφ huφ).1
  have htype := hvφ.trans huφ.symm
  have hnn : 0 ≤ ∫ x, canonicalERealDiffToReal (v x) (u x)
      ∂globalMixedMeasure (fun _ => θ) (fun _ => v) (fun _ => hv.1) := by
    apply integral_nonneg
    intro x
    change (0 : ℝ) ≤ canonicalERealDiffToReal (v x) (u x)
    by_cases hux : u x = ⊥
    · have hvx : v x = ⊥ :=
        (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mpr hux
      simp [hvx, hux]
    · rw [RelativeEnergyIntegrability.canonicalDiff_eq_sub_toReal
        (hv.1.quasiPlurisubharmonic.ne_top x) (hu.1.quasiPlurisubharmonic.ne_top x)
        (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x))]
      exact sub_nonneg.mpr
        (EReal.toReal_le_toReal (huv x) hux (hv.1.quasiPlurisubharmonic.ne_top x))
  linarith

/-- The actual extended energy agrees with its finite-type formula for singular E-infinity. -/
theorem energy_eq_of_relativeEInfinity (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : RelativeEInfinity θ φ u) :
    energy θ φ hφ u =
      (relativeEnergyOfMinimalType θ φ u hφ.plurisubharmonic hu.plurisubharmonic : EReal) := by
  refine le_antisymm (sInf_le ⟨u, hu, le_rfl, rfl⟩) (le_sInf ?_)
  rintro e ⟨v, hv, huv, rfl⟩
  exact EReal.coe_le_coe_iff.mpr
    (relativeEnergyOfMinimalType_mono omega θ hφ.plurisubharmonic
      hu.plurisubharmonic hv.plurisubharmonic hu.sameSingularityType hv.sameSingularityType huv)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyCocycle
