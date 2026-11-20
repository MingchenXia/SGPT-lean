import SGPT.Foundations.Analysis.Pending.MixedHessianLocal

set_option autoImplicit false

/-!
# The Chern--Levine--Nirenberg cutoff estimate for a mixed complex Hessian

Let `g₁, …, g_m` be smooth real functions on `ℂ^{m+1}` with positive
semidefinite complex Hessians, and write

  `C(a) = C(ddᶜa, ddᶜg₁, …, ddᶜg_m)`

for the mixed coefficient with `a` in the first slot.  Two facts are proved
here, in increasing strength.

* **Slot comparison.**  If the complex Hessian of `a` is squeezed between
  `-A·1` and `A·1`, then `|Re C(a)| ≤ A·Re C(‖·‖²)`: the first slot may be
  replaced by the flat Kähler form at the cost of the factor `A`.  This is
  multilinearity in the first slot together with nonnegativity of the mixed
  coefficient on positive semidefinite inputs.

* **The integral estimate.**  For a compactly supported cutoff `χ` whose
  Hessian is squeezed as above and a smooth `u` bounded by `C` on the support
  of `χ`,
  \[
   \Bigl|\operatorname{Re}\int \chi\,C(u)\Bigr| \le C\,A
     \int_{\operatorname{supp}\chi} \operatorname{Re} C(\|\cdot\|^{2}).
  \]
  The proof is integration by parts (`integral_mul_mixedCoefficient_swap`),
  which moves both derivatives from `u` onto `χ`, followed by the slot
  comparison.  This is the coordinate form of the integration-by-parts step in
  Demailly's proof of the Chern--Levine--Nirenberg inequalities, *Complex
  Analytic and Differential Geometry*, III, (3.3) (`demailly-cadg:III.3.3`):
  "as `T` and `β` are closed, an integration by parts yields
  `‖ddᶜu ∧ T‖_L ≤ C ∫ u T ∧ ddᶜχ ∧ β^{p-1} ≤ C' ‖u‖_{L^∞(K)} ‖T‖_K`, where `C'`
  is `C` multiplied by a bound for the coefficients of the smooth form
  `ddᶜχ ∧ β^{p-1}`".  Here `A` is that bound and `∫ Re C(‖·‖², g)` over the
  support of `χ` is the comparison mass `‖T‖_K`.

  It is NOT the weighted estimate `demailly-cadg:III.3.11`, which allows an
  unbounded plurisubharmonic weight `V ∈ L¹(K)` in place of the bounded `u`
  here; that statement is strictly stronger and is not proved in this module.

Nothing here assumes that `u` itself is plurisubharmonic; only the `m` fixed
slots are required to be positive semidefinite, which is what makes the
estimate usable for a signed telescope defect.
-/

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MixedHessian

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

noncomputable section

variable {m : ℕ}

/-! ### Linearity of the mixed coefficient in its first slot -/

theorem mixedCoefficient_cons_add (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    mixedCoefficient (Fin.cons (A + B) K :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      mixedCoefficient (Fin.cons A K : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) +
        mixedCoefficient (Fin.cons B K : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  simp only [mixedCoefficient_cons, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem mixedCoefficient_cons_smul (c : ℂ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    mixedCoefficient (Fin.cons (c • A) K :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      c * mixedCoefficient (Fin.cons A K : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  simp only [mixedCoefficient_cons, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Positive semidefiniteness of a cons-tuple, slot by slot. -/
theorem posSemidef_cons {P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hP : P.PosSemidef)
    {K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hK : ∀ i, (K i).PosSemidef) :
    ∀ i, ((Fin.cons P K : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i).PosSemidef := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa using hP
  · intro j
    simpa using hK j

/-! ### The slot comparison -/

/-- **Slot comparison.**  If the first slot is squeezed between `-A·1` and
`A·1` in the positive semidefinite order and all the other slots are positive
semidefinite, the real part of the mixed coefficient is bounded by `A` times
its value at the identity matrix. -/
theorem abs_mixedCoefficient_cons_re_le {A : ℝ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    {K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hK : ∀ i, (K i).PosSemidef)
    (hsub : (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) - B).PosSemidef)
    (hadd : (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) + B).PosSemidef) :
    |(mixedCoefficient (Fin.cons B K :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re| ≤
      A * (mixedCoefficient (Fin.cons (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) K :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re := by
  set X : ℂ :=
    mixedCoefficient (Fin.cons (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) K :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) with hX
  set Y : ℂ :=
    mixedCoefficient (Fin.cons B K : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) with hY
  have hscale : mixedCoefficient (Fin.cons ((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) K :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = (A : ℂ) * X := by
    rw [hX, mixedCoefficient_cons_smul]
  have hneg : mixedCoefficient (Fin.cons (-B) K :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = -Y := by
    have : (-B) = ((-1 : ℂ) • B) := by simp
    rw [hY, this, mixedCoefficient_cons_smul]
    simp
  have h1 : (0 : ℝ) ≤ (A * X - Y).re := by
    have := mixedCoefficient_re_nonneg
      (Fin.cons (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) - B) K :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (posSemidef_cons hsub hK)
    rwa [sub_eq_add_neg, mixedCoefficient_cons_add, hscale, hneg, ← sub_eq_add_neg] at this
  have h2 : (0 : ℝ) ≤ (A * X + Y).re := by
    have := mixedCoefficient_re_nonneg
      (Fin.cons (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) + B) K :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (posSemidef_cons hadd hK)
    rwa [mixedCoefficient_cons_add, hscale] at this
  have hre : ((A : ℂ) * X).re = A * X.re := by simp
  rw [Complex.sub_re, hre] at h1
  rw [Complex.add_re, hre] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The same comparison read on complex Hessians of smooth functions: the flat
Kähler form `ddᶜ‖z‖²` replaces the first slot. -/
theorem abs_mixedC_re_le_of_hessian_squeeze {A : ℝ} {a : ComplexModel (m + 1) → ℝ}
    {g : Fin m → ComplexModel (m + 1) → ℝ} {z : ComplexModel (m + 1)}
    (hg : ∀ i, (complexHessian (g i) z).PosSemidef)
    (hsub : (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) -
      complexHessian a z).PosSemidef)
    (hadd : (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) +
      complexHessian a z).PosSemidef) :
    |(mixedC a g z).re| ≤ A * (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by
  have h := abs_mixedCoefficient_cons_re_le (A := A) (B := complexHessian a z)
    (K := fun i => complexHessian (g i) z) hg hsub hadd
  simpa only [mixedC, complexHessian_norm_sq] using h


/-! ### The weighted Chern--Levine--Nirenberg estimate -/

/-- The flat comparison density: the mixed coefficient with `ddᶜ‖z‖²` in the
first slot.  It is nonnegative wherever the remaining slots are positive
semidefinite. -/
theorem flatDensity_nonneg {g : Fin m → ComplexModel (m + 1) → ℝ} {z : ComplexModel (m + 1)}
    (hg : ∀ i, (complexHessian (g i) z).PosSemidef) :
    0 ≤ (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by
  have h := mixedCoefficient_re_nonneg
    (Fin.cons (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (fun i => complexHessian (g i) z) :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (posSemidef_cons Matrix.PosSemidef.one hg)
  simpa only [mixedC, complexHessian_norm_sq] using h

/-- **Chern--Levine--Nirenberg cutoff estimate, smooth case**
(`demailly-cadg:III.3.3`, the integration-by-parts step of Demailly's proof).
Integration by parts moves both derivatives from
`u` onto the cutoff `χ`; the slot comparison then replaces `ddᶜχ` by `A` times
the flat Kähler form, leaving a flat comparison mass on the support of `χ`. -/
theorem abs_re_integral_mul_mixedC_le
    {g : Fin m → ComplexModel (m + 1) → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {χ : ComplexModel (m + 1) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hgpsd : ∀ i, ∀ z ∈ tsupport χ, (complexHessian (g i) z).PosSemidef)
    {u : ComplexModel (m + 1) → ℝ} (hu : ContDiff ℝ ∞ u)
    {A : ℝ}
    (hsub : ∀ z ∈ tsupport χ, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) -
      complexHessian χ z).PosSemidef)
    (hadd : ∀ z ∈ tsupport χ, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) +
      complexHessian χ z).PosSemidef)
    {C : ℝ} (hC : ∀ z ∈ tsupport χ, |u z| ≤ C) :
    |(∫ z, (χ z : ℂ) * mixedC u g z).re| ≤
      C * A * ∫ z in tsupport χ, (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by
  classical
  have hKc : IsCompact (tsupport χ) := hχc
  set F : ComplexModel (m + 1) → ℂ := fun z => (u z : ℂ) * mixedC χ g z with hFdef
  have hFcont : Continuous F :=
    (Complex.continuous_ofReal.comp hu.continuous).mul (continuous_mixedCoefficient_cons hg hχ)
  have hF0 : ∀ z ∉ tsupport χ, F z = 0 := by
    intro z hz
    simp only [hFdef, mixedC, mixedCoefficient_cons_eq_zero_of_notMem_tsupport (g := g) hz,
      mul_zero]
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro hKc (fun z hz => hF0 z hz)
  have hFint : Integrable F := hFcont.integrable_of_hasCompactSupport hFc
  have hswap := integral_mul_mixedCoefficient_swap (g := g) hg hχ hu hχc
  have hre : (∫ z, F z).re = ∫ z, (F z).re := by
    simpa using (Complex.reCLM.integral_comp_comm hFint).symm
  have hpt : ∀ z, (F z).re = u z * (mixedC χ g z).re := by
    intro z
    simp [hFdef, Complex.mul_re]
  have hgoal : (∫ z, (χ z : ℂ) * mixedC u g z) = ∫ z, F z := by
    simpa only [hFdef, mixedC] using hswap
  have hrestr : ∫ z, (F z).re = ∫ z in tsupport χ, (F z).re :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hF0 z hz, Complex.zero_re])).symm
  have hflatcont : Continuous fun z => (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re :=
    Complex.continuous_re.comp (continuous_mixedCoefficient_cons hg (contDiff_norm_sq ℝ))
  have hbound : ∀ z ∈ tsupport χ, |(F z).re| ≤
      C * A * (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by
    intro z hz
    have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (u z)) (hC z hz)
    have hslot : |(mixedC χ g z).re| ≤
        A * (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re :=
      abs_mixedC_re_le_of_hessian_squeeze (fun i => hgpsd i z hz) (hsub z hz) (hadd z hz)
    calc |(F z).re| = |u z| * |(mixedC χ g z).re| := by
          rw [hpt z, abs_mul]
      _ ≤ C * (A * (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re) :=
          mul_le_mul (hC z hz) hslot (abs_nonneg _) hC0
      _ = C * A * (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by ring
  have hintF : IntegrableOn (fun z => (F z).re) (tsupport χ) :=
    ((Complex.continuous_re.comp hFcont).continuousOn).integrableOn_compact hKc
  have hintflat : IntegrableOn
      (fun z => C * A * (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re)
      (tsupport χ) :=
    ((hflatcont.const_mul (C * A)).continuousOn).integrableOn_compact hKc
  calc |(∫ z, (χ z : ℂ) * mixedC u g z).re|
      = |∫ z in tsupport χ, (F z).re| := by rw [hgoal, hre, hrestr]
    _ ≤ ∫ z in tsupport χ, |(F z).re| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z in tsupport χ, C * A * (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re :=
        setIntegral_mono_on hintF.abs hintflat measurableSet_closure hbound
    _ = C * A * ∫ z in tsupport χ,
          (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by
        rw [integral_const_mul]


/-- **Chern--Levine--Nirenberg cutoff estimate, localized.**  The same bound
when all the data are only smooth on an open set `V` containing the compact
support of the cutoff.

The smoothness hypotheses are those supplied by
`Pending.RegularPieceGoodExhaustion.HasLocalTelescopePotential`: one open
parameter set carrying a smooth local potential, and a test function compactly
supported inside it.  The POSITIVITY hypothesis `hgpsd` is NOT supplied there:
`PatchDensityLocalPotential.exists_localPotential_patchFormDensity_currentForm_sub`
produces only `ContDiffOn` for the local potential and for `v ∘ P.toManifold`.
Feeding the telescope defect through this lemma therefore still needs, and does
not yet have in Lean, plurisubharmonicity of the local potential of `β` and of
its sum with `v ∘ P.toManifold`, together with `mixedCoefficient_perm` to move
the signed slot of `telescopeFunctions` to the front and the `π ^ dim V`
normalization between `mixedDensity` and `mixedC`. -/
theorem abs_re_integral_mul_mixedC_le_of_contDiffOn
    {V : Set (ComplexModel (m + 1))} (hV : IsOpen V)
    {g : Fin m → ComplexModel (m + 1) → ℝ} (hg : ∀ i, ContDiffOn ℝ ∞ (g i) V)
    {χ : ComplexModel (m + 1) → ℝ} (hχ : ContDiffOn ℝ ∞ χ V)
    (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V)
    (hgpsd : ∀ i, ∀ z ∈ tsupport χ, (complexHessian (g i) z).PosSemidef)
    {u : ComplexModel (m + 1) → ℝ} (hu : ContDiffOn ℝ ∞ u V)
    {A : ℝ}
    (hsub : ∀ z ∈ tsupport χ, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) -
      complexHessian χ z).PosSemidef)
    (hadd : ∀ z ∈ tsupport χ, (((A : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) +
      complexHessian χ z).PosSemidef)
    {C : ℝ} (hC : ∀ z ∈ tsupport χ, |u z| ≤ C) :
    |(∫ z, (χ z : ℂ) * mixedC u g z).re| ≤
      C * A * ∫ z in tsupport χ, (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by
  obtain ⟨η, hη1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := ⟨V, hV⟩) hχc hχV
  have hηs : ContDiff ℝ ∞ (η : ComplexModel (m + 1) → ℝ) := η.contDiff
  have hηV : tsupport (η : ComplexModel (m + 1) → ℝ) ⊆ V := η.tsupport_subset
  have hχ' : ContDiff ℝ ∞ χ := contDiff_of_contDiffOn_of_tsupport_subset hV hχ hχV
  have hu' : ContDiff ℝ ∞ (fun y => η y • u y) :=
    _root_.SGPT.Foundations.Analysis.Pending.LocalPotentials.contDiff_smul_of_tsupport_subset
      hV hηs hηV hu
  have hg' (i : Fin m) : ContDiff ℝ ∞ (fun y => η y • g i y) :=
    _root_.SGPT.Foundations.Analysis.Pending.LocalPotentials.contDiff_smul_of_tsupport_subset
      hV hηs hηV (hg i)
  -- near `tsupport χ` the cutoff `η` is one, so nothing below changes there
  have hev (z : ComplexModel (m + 1)) (hz : z ∈ tsupport χ) (f : ComplexModel (m + 1) → ℝ) :
      (fun y => η y • f y) =ᶠ[𝓝 z] f := by
    have : ∀ᶠ y in 𝓝 z, η y = 1 := hη1.filter_mono (nhds_le_nhdsSet hz)
    filter_upwards [this] with y hy
    simp [hy]
  have hHu (z : ComplexModel (m + 1)) (hz : z ∈ tsupport χ) :
      complexHessian (fun y => η y • u y) z = complexHessian u z :=
    complexHessian_congr (hev z hz u)
  have hHg (i : Fin m) (z : ComplexModel (m + 1)) (hz : z ∈ tsupport χ) :
      complexHessian (fun y => η y • g i y) z = complexHessian (g i) z :=
    complexHessian_congr (hev z hz (g i))
  have hmain := abs_re_integral_mul_mixedC_le (g := fun i y => η y • g i y) hg' hχ' hχc
    (fun i z hz => by rw [hHg i z hz]; exact hgpsd i z hz)
    (u := fun y => η y • u y) hu' (A := A) hsub hadd (C := C)
    (fun z hz => by
      have hηz : (η : ComplexModel (m + 1) → ℝ) z = 1 :=
        (hη1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
      simpa [hηz] using hC z hz)
  have hLHS : (∫ z, (χ z : ℂ) * mixedC (fun y => η y • u y) (fun i y => η y • g i y) z) =
      ∫ z, (χ z : ℂ) * mixedC u g z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport χ
    · simp only [mixedC, hHu z hz, fun i => hHg i z hz]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hRHS : (∫ z in tsupport χ,
        (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) (fun i y => η y • g i y) z).re) =
      ∫ z in tsupport χ, (mixedC (fun w : ComplexModel (m + 1) => ‖w‖ ^ 2) g z).re := by
    refine setIntegral_congr_fun measurableSet_closure fun z hz => ?_
    simp only [mixedC, fun i => hHg i z hz]
  rwa [hLHS, hRHS] at hmain

end

end SGPT.Foundations.Analysis.Pending.MixedHessian
