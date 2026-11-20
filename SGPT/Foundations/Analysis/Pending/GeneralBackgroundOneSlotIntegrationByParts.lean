import SGPT.Foundations.Analysis.Pending.CommonBackgroundOneSlotIntegrationByParts
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass

set_option autoImplicit false

/-!
# Actual singular one-slot integration by parts with general weight backgrounds

Lu, arXiv:2005.04264v1, proof of Theorem 1.2. Actual Kähler
domination, exact distinguished-slot background increment cancellation and
the constant coefficient of the actual remaining-background polynomial.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.GeneralBackgroundOneSlotIntegrationByParts

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
open GlobalMultilinearExpansion MixedMassProductCalculus RelativeEnergyIntegrability
open CanonicalBackgroundPolynomial MixedMassBoundedDifference KahlerDomination
open BackgroundPolynomialIntegrationByParts CommonBackgroundOneSlotIntegrationByParts
open NonPluripolarMixedCutoffs

noncomputable section

/-- Expand all reference backgrounds and retain the original distinguished slot. -/
def referenceBackgroundChoices {n : ℕ} (k i : Fin n) : Finset (Option (Fin n)) :=
  if i = k then {some i} else backgroundChoices i

/-- Actual remaining-background polynomial identities recover their original coefficient. -/
theorem original_reference_coefficient_eq_zero {n : ℕ} (k : Fin n)
    (d : (Fin n → Option (Fin n)) → ℝ) (N0 : ℕ)
    (h : ∀ N : ℕ, N0 ≤ N →
      ∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k),
        (N : ℝ) ^ backgroundDegree g * d g = 0) : d (fun i => some i) = 0 := by
  classical
  have hpi : Fintype.piFinset (referenceBackgroundChoices k) =
      (Fintype.piFinset (backgroundChoices (n := n))).filter (fun g => g k = some k) := by
    apply Finset.ext
    intro g
    simp only [Fintype.mem_piFinset, Finset.mem_filter]
    constructor
    · intro hg
      have hk : g k = some k := by simpa [referenceBackgroundChoices] using hg k
      refine ⟨fun i => ?_, hk⟩
      by_cases hi : i = k
      · subst hi
        simp [backgroundChoices, hk]
      · simpa only [referenceBackgroundChoices, hi, if_false] using hg i
    · rintro ⟨hg, hk⟩ i
      by_cases hi : i = k
      · subst hi
        simp [referenceBackgroundChoices, hk]
      · simpa only [referenceBackgroundChoices, hi, if_false] using hg i
  let D (g : Fin n → Option (Fin n)) : ℝ := if g k = some k then d g else 0
  have hzero := original_coefficient_eq_zero D N0 fun N hN => by
    have h' := h N hN
    rw [hpi, Finset.sum_filter] at h'
    refine (Finset.sum_congr rfl fun g _ => ?_).trans h'
    simp only [D]
    split_ifs <;> simp
  simpa [D] using hzero

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The genuine original distinguished current and all genuine reference slots. -/
theorem isThetaPshPotential_referenceTuple {theta alpha : ClosedRealOneOneForm n M}
    {phi r : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hr : IsThetaPshPotential alpha.val r) (k : Fin n) :
    ∀ i, IsThetaPshPotential (Function.update (fun _ => theta) k alpha i).val
      (Function.update (fun _ => phi) k r i) := by
  intro i
  by_cases hi : i = k
  · subst hi
    simpa only [Function.update_self] using hr
  · simpa only [Function.update_of_ne hi] using hphi

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual reference mixed product with its original distinguished form and potential. -/
def referenceMixedMeasure {theta alpha : ClosedRealOneOneForm n M}
    {phi r : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hr : IsThetaPshPotential alpha.val r) (k : Fin n) : Measure M :=
  globalMixedMeasure (Function.update (fun _ => theta) k alpha)
    (Function.update (fun _ => phi) k r)
    (fun i => (isThetaPshPotential_referenceTuple hphi hr k i).1)

/-- Exact actual measure increment from adding a semipositive distinguished background. -/
theorem referenceMixedMeasure_enlarge_distinguished {theta alpha gamma : ClosedRealOneOneForm n M}
    {phi r : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hr : IsThetaPshPotential alpha.val r) (hgamma : gamma.val.IsSemipositive) (k : Fin n) :
    referenceMixedMeasure hphi (LocalPotentials.isThetaPshPotential_add_of_semipositive hr hgamma) k =
      referenceMixedMeasure hphi hr k +
        referenceMixedMeasure hphi ((LocalPotentials.isThetaPshPotential_zero_iff gamma).mpr hgamma) k := by
  classical
  let eta := Function.update (fun _ : Fin n => theta) k alpha
  let pots := Function.update (fun _ : Fin n => phi) k r
  have hbase : ∀ i, ThetaPlurisubharmonic (eta i).val (pots i) :=
    fun i => (isThetaPshPotential_referenceTuple hphi hr k i).1
  have hnd : IsThetaPshPotential (eta k).val (pots k) := by
    simpa only [eta, pots, Function.update_self] using hr
  have hnew : ∀ i, ThetaPlurisubharmonic
      (Function.update eta k (eta k + (1 : ℝ) • gamma) i).val (pots i) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simpa only [eta, pots, Function.update_self, one_smul] using
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hr hgamma).1
    · simpa only [eta, pots, Function.update_of_ne hi] using hphi.1
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff gamma).mpr hgamma
  have h0 : ∀ i, ThetaPlurisubharmonic (Function.update eta k gamma i).val
      (Function.update pots k (fun _ => (0 : EReal)) i) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simpa only [Function.update_self] using hzero.1
    · simpa only [eta, pots, Function.update_of_ne hi] using hphi.1
  have h := NefBoundedMixedMass.globalMixedMeasure_update_add_smul_eq k one_pos hbase hnd hnew h0
  have hforms : Function.update eta k (eta k + (1 : ℝ) • gamma) =
      Function.update (fun _ => theta) k (alpha + gamma) := by simp [eta]
  have h0forms : Function.update eta k gamma = Function.update (fun _ => theta) k gamma :=
    Function.update_idem _ _ _
  have h0pots : Function.update pots k (fun _ => (0 : EReal)) =
      Function.update (fun _ => phi) k (fun _ => (0 : EReal)) := Function.update_idem _ _ _
  calc
    _ = globalMixedMeasure (Function.update eta k (eta k + (1 : ℝ) • gamma)) pots hnew :=
      globalMixedMeasure_congr hforms.symm rfl _ _
    _ = _ := h
    _ = _ := by
      rw [ENNReal.ofReal_one, one_smul]
      exact congrArg₂ (fun mu nu : Measure M => mu + nu) rfl
        (globalMixedMeasure_congr h0forms h0pots _ _)

/-- Actual canonical signed integrals cancel the distinguished background increment. -/
theorem integral_sub_referenceMixedMeasure_enlarge_distinguished (omega : KahlerBackground n M)
    {eta xi : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential eta u) (hv : IsThetaPshPotential xi v)
    (htype : SameSingularityTypeOn u v univ)
    {theta alpha gamma : ClosedRealOneOneForm n M} {phi r s : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hr : IsThetaPshPotential alpha.val r)
    (hs : IsThetaPshPotential alpha.val s) (hgamma : gamma.val.IsSemipositive) (k : Fin n) :
    ((∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂referenceMixedMeasure hphi (LocalPotentials.isThetaPshPotential_add_of_semipositive hr hgamma) k) -
     (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂referenceMixedMeasure hphi (LocalPotentials.isThetaPshPotential_add_of_semipositive hs hgamma) k)) =
    (∫ x, canonicalERealDiffToReal (u x) (v x) ∂referenceMixedMeasure hphi hr k) -
    (∫ x, canonicalERealDiffToReal (u x) (v x) ∂referenceMixedMeasure hphi hs k) := by
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff gamma).mpr hgamma
  have hI (r : M → EReal) (hr : IsThetaPshPotential alpha.val r) :
      Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
        (referenceMixedMeasure hphi hr k) :=
    integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype
      (fun i => (isThetaPshPotential_referenceTuple hphi hr k i).1)
  have hIz : Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (referenceMixedMeasure hphi hzero k) :=
    integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype
      (fun i => (isThetaPshPotential_referenceTuple hphi hzero k i).1)
  rw [referenceMixedMeasure_enlarge_distinguished hphi hr hgamma k,
    referenceMixedMeasure_enlarge_distinguished hphi hs hgamma k,
    integral_add_measure (hI r hr) hIz, integral_add_measure (hI s hs) hIz]
  ring

/-- Expand only the actual reference backgrounds; every coefficient retains
the original distinguished current and a produced integrable canonical weight. -/
theorem integral_canonicalDiff_referenceMixedMeasure_add_background (omega : KahlerBackground n M)
    {eta xi : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential eta u) (hv : IsThetaPshPotential xi v)
    (htype : SameSingularityTypeOn u v univ)
    {theta alpha : ClosedRealOneOneForm n M} {phi r : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hr : IsThetaPshPotential alpha.val r)
    {t : ℝ} (ht : 0 < t) (k : Fin n) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂referenceMixedMeasure
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hphi
          (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)) hr k) =
    ∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), t ^ backgroundDegree g *
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure
          (fun j => optForm omega (Function.update (fun _ => theta) k alpha) (g j))
          (fun j => optPot (Function.update (fun _ => phi) k r) (g j))
          (fun j => optPot_psh omega (isThetaPshPotential_referenceTuple hphi hr k) (g j)) := by
  classical
  let forms := Function.update (fun _ : Fin n => theta) k alpha
  let pots := Function.update (fun _ : Fin n => phi) k r
  have hslots : ∀ i, IsThetaPshPotential (forms i).val (pots i) :=
    isThetaPshPotential_referenceTuple hphi hr k
  have hT (i : Fin n) : (referenceBackgroundChoices k i).Nonempty := by
    refine ⟨some i, ?_⟩
    by_cases hi : i = k <;> simp [referenceBackgroundChoices, backgroundChoices, hi]
  have hexp := globalMixedMeasure_sumPot_slots hT
    (fun _ => optWeight_pos (n := n) ht) (optPot_psh omega hslots) (optPot_quasiPsh hslots)
  have hforms : (fun i => sumForm (referenceBackgroundChoices k i) (optWeight t)
      (optForm omega forms)) = Function.update (fun _ => theta + t • omega.form) k alpha := by
    funext i
    by_cases hi : i = k
    · subst hi
      simp [referenceBackgroundChoices, sumForm, optWeight, optForm, forms]
    · simp only [referenceBackgroundChoices, hi, if_false]
      rw [sumForm_backgroundChoices]
      simp [forms, hi]
  have hpot : (fun i => sumPot (referenceBackgroundChoices k i) (optWeight t) (optPot pots)) =
      pots := by
    funext i
    by_cases hi : i = k
    · simp only [referenceBackgroundChoices, hi, if_true]
      funext x
      simp [sumPot, optWeight, optPot]
    · simpa only [referenceBackgroundChoices, hi, if_false] using sumPot_backgroundChoices pots t i
  have hphi' := LocalPotentials.isThetaPshPotential_add_of_semipositive hphi
    (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
  rw [globalMixedMeasure_congr hforms hpot _
    (fun i => (isThetaPshPotential_referenceTuple hphi' hr k i).1)] at hexp
  change (∫ x, canonicalERealDiffToReal (u x) (v x) ∂globalMixedMeasure _ _ _) = _
  rw [hexp, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_smul_measure, prod_optWeight]
    simp only [backgroundDegree, ENNReal.toReal_ofReal (pow_nonneg ht.le _), smul_eq_mul]
    rfl
  · intro g _
    exact (integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype
      (fun j => optPot_psh omega hslots (g j))).smul_measure ENNReal.ofReal_ne_top

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine Kähler background dominates both actual weight-background differences
at every sufficiently large positive natural parameter. -/
theorem exists_common_background_threshold (omega : KahlerBackground n M)
    (theta alpha beta : ClosedRealOneOneForm n M) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (theta + (N : ℝ) • omega.form - alpha).val.IsSemipositive ∧
      (theta + (N : ℝ) • omega.form - beta).val.IsSemipositive := by
  obtain ⟨A, -, hA⟩ := exists_pos_isSemipositive_add_smul omega (theta - alpha)
  obtain ⟨B, -, hB⟩ := exists_pos_isSemipositive_add_smul omega (theta - beta)
  let N0 : ℕ := ⌈max A B⌉₊ + 1
  refine ⟨N0, by omega, fun N hN => ?_⟩
  have hlarge : max A B ≤ (N : ℝ) := by
    have hceil : (⌈max A B⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    linarith [Nat.le_ceil (max A B)]
  have hAN : A ≤ (N : ℝ) := (le_max_left A B).trans hlarge
  have hBN : B ≤ (N : ℝ) := (le_max_right A B).trans hlarge
  have ha := isSemipositive_add_smul_mono omega.isSemipositive hAN hA
  have hb := isSemipositive_add_smul_mono omega.isSemipositive hBN hB
  have eA : theta - alpha + (N : ℝ) • omega.form =
      theta + (N : ℝ) • omega.form - alpha := by module
  have eB : theta - beta + (N : ℝ) • omega.form =
      theta + (N : ℝ) • omega.form - beta := by module
  rw [eA] at ha
  rw [eB] at hb
  exact ⟨ha, hb⟩

/-- Actual one-slot IBP retains original weight curvatures when the reference
background dominates both; all common-background inputs are produced. -/
theorem integral_sub_referenceMixedMeasure_symm_of_domination (omega : KahlerBackground n M)
    {theta alpha beta : ClosedRealOneOneForm n M} {a b p q phi : M → EReal}
    (ha : IsThetaPshPotential alpha.val a) (hb : IsThetaPshPotential alpha.val b)
    (hp : IsThetaPshPotential beta.val p) (hq : IsThetaPshPotential beta.val q)
    (hphi : IsThetaPshPotential theta.val phi)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ)
    (hA : (theta - alpha).val.IsSemipositive) (hB : (theta - beta).val.IsSemipositive)
    (k : Fin n) :
    ((∫ x, canonicalERealDiffToReal (p x) (q x) ∂referenceMixedMeasure hphi ha k) -
     (∫ x, canonicalERealDiffToReal (p x) (q x) ∂referenceMixedMeasure hphi hb k)) =
    (∫ x, canonicalERealDiffToReal (a x) (b x) ∂referenceMixedMeasure hphi hp k) -
    (∫ x, canonicalERealDiffToReal (a x) (b x) ∂referenceMixedMeasure hphi hq k) := by
  have ha' : IsThetaPshPotential theta.val a := by
    simpa only [add_sub_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive ha hA
  have hb' : IsThetaPshPotential theta.val b := by
    simpa only [add_sub_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive hb hA
  have hp' : IsThetaPshPotential theta.val p := by
    simpa only [add_sub_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive hp hB
  have hq' : IsThetaPshPotential theta.val q := by
    simpa only [add_sub_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive hq hB
  have h := integral_sub_reference_slot_symm omega ha' hb' hp' hq' hphi hab hpq k
  have hmeasure {gamma : ClosedRealOneOneForm n M} {r : M → EReal}
      (hr : IsThetaPshPotential gamma.val r) (hr' : IsThetaPshPotential theta.val r)
      (hmargin : (theta - gamma).val.IsSemipositive) :
      binaryMixedMeasure theta hphi.1 hphi.1 hr'.1 (fun _ => false) k =
      referenceMixedMeasure hphi
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hr hmargin) k := by
    refine globalMixedMeasure_congr ?_ rfl _ _
    funext i
    by_cases hi : i = k <;> simp [hi]
  have hl := (congrArg₂ (fun x y : ℝ => x - y)
    (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (p x) (q x) ∂mu)
      (hmeasure ha ha' hA))
    (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (p x) (q x) ∂mu)
      (hmeasure hb hb' hA))).trans
    (integral_sub_referenceMixedMeasure_enlarge_distinguished omega hp hq hpq hphi ha hb hA k)
  have hr := (congrArg₂ (fun x y : ℝ => x - y)
    (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (a x) (b x) ∂mu)
      (hmeasure hp hp' hB))
    (congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (a x) (b x) ∂mu)
      (hmeasure hq hq' hB))).trans
    (integral_sub_referenceMixedMeasure_enlarge_distinguished omega ha hb hab hphi hp hq hB k)
  exact hl.symm.trans (h.trans hr)

/-- Actual singular one-slot IBP for independent closed weight and reference
backgrounds. Domination and both polynomial inputs are produced, not assumed. -/
theorem integral_sub_referenceMixedMeasure_symm (omega : KahlerBackground n M)
    {theta alpha beta : ClosedRealOneOneForm n M} {a b p q phi : M → EReal}
    (ha : IsThetaPshPotential alpha.val a) (hb : IsThetaPshPotential alpha.val b)
    (hp : IsThetaPshPotential beta.val p) (hq : IsThetaPshPotential beta.val q)
    (hphi : IsThetaPshPotential theta.val phi)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ)
    (k : Fin n) :
    ((∫ x, canonicalERealDiffToReal (p x) (q x) ∂referenceMixedMeasure hphi ha k) -
     (∫ x, canonicalERealDiffToReal (p x) (q x) ∂referenceMixedMeasure hphi hb k)) =
    (∫ x, canonicalERealDiffToReal (a x) (b x) ∂referenceMixedMeasure hphi hp k) -
    (∫ x, canonicalERealDiffToReal (a x) (b x) ∂referenceMixedMeasure hphi hq k) := by
  classical
  obtain ⟨N0, hN0, hlarge⟩ := exists_common_background_threshold omega theta alpha beta
  let I (u v : M → EReal) (gamma : ClosedRealOneOneForm n M) (r : M → EReal)
      (hr : IsThetaPshPotential gamma.val r) (g : Fin n → Option (Fin n)) : ℝ :=
    ∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure
        (fun j => optForm omega (Function.update (fun _ => theta) k gamma) (g j))
        (fun j => optPot (Function.update (fun _ => phi) k r) (g j))
        (fun j => optPot_psh omega (isThetaPshPotential_referenceTuple hphi hr k) (g j))
  let d (g : Fin n → Option (Fin n)) : ℝ :=
    (I p q alpha a ha g - I p q alpha b hb g) - (I a b beta p hp g - I a b beta q hq g)
  have hpoly (N : ℕ) (hN : N0 ≤ N) :
      ∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k),
        (N : ℝ) ^ backgroundDegree g * d g = 0 := by
    have ht : 0 < (N : ℝ) := by exact_mod_cast (hN0.trans_le hN)
    have hphi' := LocalPotentials.isThetaPshPotential_add_of_semipositive hphi
      (KahlerDomination.isSemipositive_smul omega.isSemipositive ht.le)
    have hmargins := hlarge N hN
    have h := integral_sub_referenceMixedMeasure_symm_of_domination omega ha hb hp hq hphi'
      hab hpq hmargins.1 hmargins.2 k
    have hl := congrArg₂ (fun x y : ℝ => x - y)
      (integral_canonicalDiff_referenceMixedMeasure_add_background omega hp hq hpq hphi ha ht k)
      (integral_canonicalDiff_referenceMixedMeasure_add_background omega hp hq hpq hphi hb ht k)
    have hr := congrArg₂ (fun x y : ℝ => x - y)
      (integral_canonicalDiff_referenceMixedMeasure_add_background omega ha hb hab hphi hp ht k)
      (integral_canonicalDiff_referenceMixedMeasure_add_background omega ha hb hab hphi hq ht k)
    have heq := hl.symm.trans (h.trans hr)
    change
      ((∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I p q alpha a ha g) -
       (∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I p q alpha b hb g)) =
      (∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I a b beta p hp g) -
      (∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I a b beta q hq g) at heq
    have hexp :
        (∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * d g) =
        ((∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I p q alpha a ha g) -
         (∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I p q alpha b hb g)) -
        ((∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I a b beta p hp g) -
         (∑ g ∈ Fintype.piFinset (referenceBackgroundChoices k), (N : ℝ) ^ backgroundDegree g * I a b beta q hq g)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      dsimp only [d]
      ring
    exact hexp.trans (sub_eq_zero.mpr heq)
  have h0 := original_reference_coefficient_eq_zero k d N0 hpoly
  change
    ((∫ x, canonicalERealDiffToReal (p x) (q x) ∂referenceMixedMeasure hphi ha k) -
     (∫ x, canonicalERealDiffToReal (p x) (q x) ∂referenceMixedMeasure hphi hb k)) -
    ((∫ x, canonicalERealDiffToReal (a x) (b x) ∂referenceMixedMeasure hphi hp k) -
     (∫ x, canonicalERealDiffToReal (a x) (b x) ∂referenceMixedMeasure hphi hq k)) = 0 at h0
  exact sub_eq_zero.mp h0

end

end SGPT.Foundations.Analysis.Pending.GeneralBackgroundOneSlotIntegrationByParts
