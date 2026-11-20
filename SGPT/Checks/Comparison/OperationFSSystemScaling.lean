import SGPT.Foundations.Envelope.Global.FSSystemC

/-! Direct ACTUAL FS product net for arbitrary positive REAL scaling.
No nef/cone-closure/PSH2 premise. Blueprint: operation-real-class-scaling.tex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open Set Filter Topology SGPT.Foundations.Envelope

/-- Genuine direct-net real scaling for the existing FSSystemC predicate
in EVERY class. All scaled FS terms/cofinalities/class limits are internal. -/
theorem fsSystemC_positiveScale {K : Type u} [TopologicalSpace K] {r : ℕ}
    (F : FSSystemC K r) {θ : Fin r → ℝ} {u : K → EReal}
    (hu : F.IsPSH θ u) {c : ℝ} (hc : 0 < c) :
    F.IsPSH (c • θ) (fun x => (c : EReal) * u x) := by
  classical
  obtain ⟨I, hI, hdir, hne, a, f, hf, ha, hanti, hlim⟩ := hu.exists_tendsto
  let i₀ : I := Classical.choice hne
  let B : ℝ := (f i₀ F.triv).toReal
  have hB : (B : EReal) = f i₀ F.triv :=
    EReal.coe_toReal (hf i₀).apply_triv_ne_top (hf i₀).apply_triv_ne_bot
  let T := Ici i₀
  have : IsDirected T (· ≤ ·) := by
    constructor
    intro i j
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge (i : I) (j : I)
    exact ⟨⟨k,i.2.trans hik⟩,hik,hjk⟩
  have ht : Tendsto ((↑) : T → I) atTop atTop := by
    change Filter.map ((↑) : Ici i₀ → I) atTop ≤ atTop
    rw [map_val_Ici_atTop]
  have hneg (i : T) (x : K) : f i x + ((-B : ℝ) : EReal) ≤ 0 := by
    have h := ((hf i).le_apply_triv x).trans (hanti F.triv i.2)
    change f i x ≤ f i₀ F.triv at h
    rw [← hB] at h
    have hh : f i x + ((-B : ℝ) : EReal) ≤ (B : EReal) + ((-B : ℝ) : EReal) :=
      add_le_add h le_rfl
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using hh
  obtain ⟨q, hqm, -, hql⟩ := Real.exists_seq_rat_strictMono_tendsto c
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hql.eventually (lt_mem_nhds hc))
  let q' : ℕ → ℚ := fun j => q (j+N)
  have hqp (j : ℕ) : (0 : ℝ) < q' j := hN _ (Nat.le_add_left N j)
  have hqpQ (j : ℕ) : (0 : ℚ) < q' j := by exact_mod_cast hqp j
  have hql' : Tendsto (fun j => (q' j : ℝ)) atTop (𝓝 c) :=
    hql.comp (tendsto_add_atTop_nat N)
  have hqm' : Monotone fun j => (q' j : ℝ) := by
    intro j k hjk
    change (q (j+N) : ℝ) ≤ (q (k+N) : ℝ)
    exact_mod_cast hqm.monotone (Nat.add_le_add_right hjk N)
  let J := T × ℕ
  have : IsDirected J (· ≤ ·) := isDirected_prod
  have hi : Tendsto (fun j : J => (j.1 : I)) atTop atTop := ht.comp ProjBerk.tendsto_prod_fst_atTop
  have hqJ : Tendsto (fun j : J => (q' j.2 : ℝ)) atTop (𝓝 c) :=
    hql'.comp ProjBerk.tendsto_prod_snd_atTop
  have hscaled : F.IsPSH (c • θ)
      (fun x => (c : EReal) * (u x + ((-B : ℝ) : EReal))) := by
    refine SGPT.Foundations.Envelope.FSSystemC.isPSH_of_tendsto
      ⟨F.triv, ProjBerk.ereal_coe_mul_ne_bot hc.le
        (ProjBerk.ereal_add_coe_ne_bot hu.apply_triv_ne_bot (-B))⟩
      (fun j : J => q' j.2 • a j.1)
      (fun j x => ((q' j.2 : ℝ) : EReal) * (f j.1 x + ((-B : ℝ) : EReal)))
      (fun j => ((hf j.1).add_const (-B)).smul (hqpQ j.2)) ?_ ?_ ?_
    · have h := hqJ.smul (ha.comp hi)
      apply h.congr
      intro j
      funext d
      simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Function.comp_apply]
    · intro x j k hjk
      have hjk' := Prod.le_def.mp hjk
      exact (ProjBerk.ereal_coe_mul_le_of_nonpos
        (hqp j.2) (hqm' hjk'.2) (hneg k.1 x)).trans
        (ProjBerk.ereal_coe_mul_monotone (hqp j.2).le
          (add_le_add (hanti x hjk'.1) le_rfl))
    · intro x
      have huf := ((ProjBerk.continuous_ereal_add_coe (-B)).tendsto (u x)).comp
        ((hlim x).comp hi)
      have hqc : Tendsto (fun j : J => ((q' j.2 : ℝ) : EReal)) atTop (𝓝 (c : EReal)) :=
        EReal.tendsto_coe.mpr hqJ
      exact EReal.Tendsto.mul hqc huf
        (Or.inl (EReal.coe_ne_zero.mpr hc.ne'))
        (Or.inl (EReal.coe_ne_zero.mpr hc.ne'))
        (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
  convert hscaled.add_const (c * B) using 2 with x
  rw [ProjBerk.ereal_coe_mul_add hc.le, ← EReal.coe_mul, add_assoc,
    ← EReal.coe_add, mul_neg, neg_add_cancel, EReal.coe_zero, add_zero]

end SGPT.NAPotential.OperationComparison
