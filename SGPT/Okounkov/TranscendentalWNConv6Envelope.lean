import SGPT.Okounkov.TranscendentalWNConv6Obstacle
import SGPT.Okounkov.TranscendentalWNDeformationBig
import SGPT.Okounkov.TranscendentalWNVolumeFibre
import SGPT.Okounkov.TranscendentalWNRegContact
import SGPT.Okounkov.TranscendentalWNRegDNTEnvelope
import SGPT.Okounkov.TranscendentalWNRestricted

/-!
# The envelopes `u_k = P_{θ̃}(g_k)` and the fibre bound `I_k ≤ vol(ξ)`

Blueprint `tok-wn-conv6:envelope` and `tok-wn-conv6:fibre-bound` (chapter `claude-tok-wn-conv6`);
source WN21 §6 (the envelopes `u_k`; the bound `∫_{X_τ ∩ D_k} θ̃ⁿ ≤ vol(α)` in the proof of
Corollary 6.5).

`MCData F 𝒳` bundles the data of `MeasureControlStatement` (the unit metric `E`, the deformation
`μ`, the metric `Eℰ`, `θ`, `b`, `c`, the bigness hypotheses and the cutoff `χ`).  For such data:

* `isBig_form`, `exists_isThetaPshPotential_form`: `β = {θ̃}` is big, so `PSH(𝒳, θ̃) ≠ ∅`
  (WN-DEF2's `betaBig`);
* `isThetaPshPotential_envelope`: `u_k` is `θ̃`-psh; `envelope_le_obstacle`: `u_k ≤ g_k`;
  `envelope_antitone`: `u_{k+1} ≤ u_k`; `moreSingular_envelope`: `V_θ̃ ≤ u_k + C`
  (minimal singularities, `g_k` being bounded below on the compact `𝒳`);
* `diagonalPotentialMass_envelope`: `∫_𝒳 ⟨(θ̃ + ddᶜu_k)^{n+1}⟩ = vol(β)`;
* `fibreContactMass_le` (`tok-wn-conv6:fibre-bound`, WN21 Cor. 6.5): for `τ ≠ 0` and the section
  `s` over `[τ : 1]`, `I_k(τ) = ∫_{X_τ ∩ D_k} θ̃ⁿ ≤ vol(ξ)`: the restriction `u_k ∘ s` is a
  `s^*θ̃`-psh potential (`tok-wn:formula-fibre`, proved by WN-VF from `betaBig`), it is `≤` the
  constant `g_k(τ)` with contact set `s⁻¹(D_k)`, so Di Nezza–Trapani for constant obstacles
  (WN-REG2's `dntConstantObstacleStatement`) gives `𝟙_{s⁻¹ D_k} (s^*θ̃)ⁿ ≤ ⟨(s^*θ̃ + ddᶜ(u_k∘s))ⁿ⟩`,
  whose mass is at most `vol {s^*θ̃} = vol(ξ)`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.TranscendentalMain

/-- `a + c ≤ b` gives `a ≤ b - c` in `EReal` (for real `c`). -/
theorem ereal_le_add_neg_of_add_le {a b : EReal} {c : ℝ} (h : a + (c : EReal) ≤ b) :
    a ≤ b + ((-c : ℝ) : EReal) := by
  have : a = a + (c : EReal) + ((-c : ℝ) : EReal) := by
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  calc a = _ := this
    _ ≤ _ := add_le_add h le_rfl

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **The data of `MeasureControlStatement`** (WN21 §6): a unit metric `E` of `𝒪(Z)` with
`|s_Z| ≤ 1`, a deformation `μ : 𝒳 → X × ℙ¹` with the metric `Eℰ` of `𝒪(ℰ)`, `θ`, `0 < c`,
`c + 1 < b`, `ξ = {θ}` and `ξ_c` big with Kähler loci meeting `Z`, and a cutoff `χ`. -/
structure MCData (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] where
  E : MeteredEffectiveQDivisor (m + 1) F.carrier
  hE : IsFirstDivisorUnitMetric F E
  hE0 : ∀ x, E.weight x ≤ 0
  μ : 𝒳 → F.carrier × ProjectiveLine
  hμ : IsNormalConeDeformation F μ
  Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳
  hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ
  θ : ClosedRealOneOneForm (m + 1) F.carrier
  b : ℝ
  c : ℝ
  hc : 0 < c
  hcb : c + 1 < b
  hξ : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ)
  hξc : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
    c • RealBottChern.ofRepresentative E.curvature)
  χ : ℝ → ℝ
  hχ : IsWNCutoff χ

namespace MCData

variable {F} {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] (D : MCData F 𝒳)

/-- `θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ`. -/
def form : ClosedRealOneOneForm (m + 1 + 1) 𝒳 := deformationForm F D.hμ.contMDiff D.θ D.b D.c D.Eℰ

/-- `θ̃ - (π_{ℙ¹} μ)^*ω_FS`, a representative of `β - {X₀}` (the parameter `b - 1`). -/
def formPrev : ClosedRealOneOneForm (m + 1 + 1) 𝒳 :=
  deformationForm F D.hμ.contMDiff D.θ (D.b - 1) D.c D.Eℰ

/-- `g_k`. -/
def obstacle (k : ℕ) : 𝒳 → ℝ := cutoffObstacle D.μ D.χ k

/-- `u_k = P_{θ̃}(g_k)`. -/
def envelope (k : ℕ) : 𝒳 → EReal := cutoffEnvelope D.form D.μ D.χ k

/-- `D_k = {u_k = g_k}`. -/
def contact (k : ℕ) : Set 𝒳 := cutoffContactSet D.form D.μ D.χ k

/-- `vol(ξ)`. -/
def vol : ℝ := classVolumeReal F (RealBottChern.ofRepresentative D.θ)

theorem compactSpace (D : MCData F 𝒳) : CompactSpace 𝒳 := compactSpace_normalCone F D.hμ

theorem connectedSpace (D : MCData F 𝒳) : ConnectedSpace 𝒳 := connectedSpace_normalCone F D.hμ

theorem nonempty_kahler (D : MCData F 𝒳) : Nonempty (KahlerBackground (m + 1 + 1) 𝒳) :=
  nonempty_kahler_normalCone F D.hμ

theorem contMDiff_proj (D : MCData F 𝒳) : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel 1) ∞
    fun z => (D.μ z).2 :=
  contMDiff_deformationProjP1 F D.hμ.contMDiff

theorem chartSmooth_obstacle (k : ℕ) : ChartSmooth (n := m + 1 + 1) (D.obstacle k) :=
  chartSmooth_cutoffObstacle D.contMDiff_proj D.hχ k

theorem continuous_obstacle (k : ℕ) : Continuous (D.obstacle k) :=
  continuous_cutoffObstacle D.contMDiff_proj D.hχ k

section Compact

variable [CompactSpace 𝒳] [ConnectedSpace 𝒳]

omit [ConnectedSpace 𝒳] in
/-- `β = {θ̃}` is big (WN21 Prop. 4.1, WN-DEF2's `betaBig`). -/
theorem isBig_form : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative D.form) :=
  (betaBig F D.E D.hE 𝒳 D.μ D.hμ D.Eℰ D.hEℰ.isDivisorMetric D.θ D.b D.c D.hc
    (by linarith [D.hcb]) D.hξ D.hξc.1).1

omit [ConnectedSpace 𝒳] in
theorem exists_isThetaPshPotential_form : ∃ φ : 𝒳 → EReal, IsThetaPshPotential D.form.val φ :=
  exists_isThetaPshPotential_of_isBigClass
    ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp D.isBig_form)

/-- **`u_k` is `θ̃`-psh.** -/
theorem isThetaPshPotential_envelope (k : ℕ) :
    IsThetaPshPotential D.form.val (D.envelope k) := by
  let : MeasurableSpace 𝒳 := borel 𝒳
  have : BorelSpace 𝒳 := ⟨rfl⟩
  obtain ⟨w⟩ := D.nonempty_kahler
  obtain ⟨φ, hφ⟩ := D.exists_isThetaPshPotential_form
  exact SGPT.Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous w
    D.form (D.continuous_obstacle k) hφ

/-- **`u_k ≤ g_k`.** -/
theorem envelope_le_obstacle (k : ℕ) (z : 𝒳) : D.envelope k z ≤ (D.obstacle k z : EReal) := by
  let : MeasurableSpace 𝒳 := borel 𝒳
  have : BorelSpace 𝒳 := ⟨rfl⟩
  exact SGPT.Okounkov.TranscendentalWNReg.rooftopEnvelope_le_of_isThetaPshPotential
    (D.continuous_obstacle k) (D.isThetaPshPotential_envelope k) z

omit [CompactSpace 𝒳] [ConnectedSpace 𝒳] in
/-- **`u_{k+1} ≤ u_k`** (the obstacles decrease). -/
theorem envelope_succ_le (k : ℕ) : D.envelope (k + 1) ≤ D.envelope k :=
  rooftopEnvelope_mono fun z => EReal.coe_le_coe_iff.mpr
    (cutoffObstacle_antitone D.hχ z (Nat.le_succ k))

omit [CompactSpace 𝒳] [ConnectedSpace 𝒳] in
theorem envelope_antitone (z : 𝒳) : Antitone fun k => D.envelope k z :=
  antitone_nat_of_succ_le fun k => D.envelope_succ_le k z

/-- `g_k` is bounded below. -/
theorem exists_le_obstacle (k : ℕ) : ∃ C : ℝ, ∀ z, C ≤ D.obstacle k z := by
  obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (D.continuous_obstacle k).continuousOn
  exact ⟨D.obstacle k z₀, fun z => hz₀ (mem_univ z)⟩

/-- **`V_θ̃ + C ≤ u_k`**: the envelopes have minimal singularities. -/
theorem thetaPshSupremum_add_le_envelope (k : ℕ) :
    ∃ C : ℝ, ∀ z, thetaPshSupremum D.form.val z + (C : EReal) ≤ D.envelope k z := by
  let : MeasurableSpace 𝒳 := borel 𝒳
  have : BorelSpace 𝒳 := ⟨rfl⟩
  obtain ⟨C, hC⟩ := D.exists_le_obstacle k
  obtain ⟨φ, hφ⟩ := D.exists_isThetaPshPotential_form
  obtain ⟨hV, -⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative
    (Classical.choice D.nonempty_kahler) D.form hφ
  refine ⟨C, ?_⟩
  have hle : (fun z => thetaPshSupremum D.form.val z + (C : EReal)) ≤ D.envelope k := by
    refine le_rooftopEnvelope (hV.add_const C) (quasiEverywhere_of_forall fun z => ?_)
    calc thetaPshSupremum D.form.val z + (C : EReal) ≤ 0 + (C : EReal) :=
          add_le_add (thetaPshSupremum_le_zero _ z) le_rfl
      _ = (C : EReal) := zero_add _
      _ ≤ (D.obstacle k z : EReal) := EReal.coe_le_coe_iff.mpr (hC z)
  exact fun z => hle z

theorem moreSingular_envelope (k : ℕ) :
    MoreSingularOn (thetaPshSupremum D.form.val) (D.envelope k) univ := by
  obtain ⟨C, hC⟩ := D.thetaPshSupremum_add_le_envelope k
  refine ⟨-C, fun z _ => ?_⟩
  have h := hC z
  exact ereal_le_add_neg_of_add_le h

/-- **The total mass of `u_k` is `vol(β)`** (`u_k` has minimal singularities). -/
theorem diagonalPotentialMass_envelope [MeasurableSpace 𝒳] [BorelSpace 𝒳] (k : ℕ) :
      diagonalPotentialMass D.form (D.envelope k) (D.isThetaPshPotential_envelope k) =
      SGPT.PSH.VariableComplexAtlas.sourceClassVolume (RealBottChern.ofRepresentative D.form) := by
  set w := Classical.choice D.nonempty_kahler
  obtain ⟨hV, hvol⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative w D.form
    (D.isThetaPshPotential_envelope k)
  rw [hvol]
  refine le_antisymm ?_ ?_
  · rw [← hvol]
    exact TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume w D.form _
  · exact diagonalPotentialMass_mono_of_kahler w hV (D.isThetaPshPotential_envelope k)
      (D.moreSingular_envelope k)

end Compact

/-! ### Fibre sections -/

/-- The section of `μ` over `x ↦ (x, [τ : 1])`, `τ ≠ 0`. -/
def sec {τ : ℂ} (hτ : τ ≠ 0) : F.carrier → 𝒳 :=
  Classical.choose (exists_fibreSection F D.hμ (affineLinePoint_ne_projectiveZero hτ))

theorem contMDiff_sec {τ : ℂ} (hτ : τ ≠ 0) :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ (D.sec hτ) :=
  (Classical.choose_spec (exists_fibreSection F D.hμ (affineLinePoint_ne_projectiveZero hτ))).1

theorem μ_sec {τ : ℂ} (hτ : τ ≠ 0) (x : F.carrier) :
    D.μ (D.sec hτ x) = (x, affineLinePoint τ) :=
  (Classical.choose_spec (exists_fibreSection F D.hμ (affineLinePoint_ne_projectiveZero hτ))).2.1 x

/-- **Sections of `μ` over `x ↦ (x, p)`, `p ≠ 0`, are unique.** -/
theorem section_unique {p : ProjectiveLine} (hp : p ≠ projectiveZero) {s s' : F.carrier → 𝒳}
    (hs : ∀ x, D.μ (s x) = (x, p)) (hs' : ∀ x, D.μ (s' x) = (x, p)) : s = s' := by
  funext x
  have hnot : D.μ (s x) ∉ deformationCentre F := by
    rw [hs x]; intro h; exact hp ((mem_deformationCentre_iff F).mp h).2
  exact eq_of_map_eq_of_notMem F D.hμ hnot ((hs x).trans (hs' x).symm)

/-- `I_k(τ)` (and `0` at `τ = 0`). -/
def fibreMass (k : ℕ) (τ : ℂ) : ℝ≥0∞ :=
  if hτ : τ = 0 then 0 else fibreContactMass F D.form D.μ D.χ k (D.sec hτ) (D.contMDiff_sec hτ)

theorem fibreContactMass_eq_fibreMass {k : ℕ} {τ : ℂ} (hτ : τ ≠ 0) {s : F.carrier → 𝒳}
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (hμs : ∀ x, D.μ (s x) = (x, affineLinePoint τ)) :
    fibreContactMass F D.form D.μ D.χ k s hs = D.fibreMass k τ := by
  have h := D.section_unique (affineLinePoint_ne_projectiveZero hτ) hμs (D.μ_sec hτ)
  subst h
  rw [fibreMass, dif_neg hτ]

/-- On the fibre over `p`, the obstacle is the constant `g_k(p)`. -/
theorem obstacle_sec {p : ProjectiveLine} {s : F.carrier → 𝒳} (hs : ∀ x, D.μ (s x) = (x, p))
    (k : ℕ) (x : F.carrier) : D.obstacle k (s x) = cutoffObstacleLine D.χ k p := by
  rw [obstacle, cutoffObstacle, hs x]

section FibreBound

variable [CompactSpace 𝒳] [ConnectedSpace 𝒳]

/-- **`tok-wn-conv6:fibre-bound`** (WN21 Cor. 6.5): `I_k(τ) ≤ vol(ξ)` for every section `s` over
`x ↦ (x, p)`, `p ≠ 0`. -/
theorem fibreContactMass_le {p : ProjectiveLine} (hp : p ≠ projectiveZero) (k : ℕ)
    {s : F.carrier → 𝒳}
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (hμs : ∀ x, D.μ (s x) = (x, p)) :
    fibreContactMass F D.form D.μ D.χ k s hs ≤ ENNReal.ofReal D.vol := by
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  -- the restriction of `u_k` is a `s^*θ̃`-psh potential
  have hfib := (restrictedVolume_fibre F (betaBig F)) D.E D.hE D.hE0 𝒳 D.μ D.hμ D.Eℰ D.hEℰ D.θ
    D.b D.c D.hc (by linarith [D.hcb]) D.hξ D.hξc p hp s hs hμs
  obtain ⟨hres, -⟩ := hfib.2 (D.envelope k) (D.isThetaPshPotential_envelope k)
    (D.moreSingular_envelope k)
  set θs := ClosedRealOneOneForm.pullback hs D.form with hθs
  set c₀ : ℝ := cutoffObstacleLine D.χ k p with hc₀
  have hle : ∀ x, D.envelope k (s x) ≤ (c₀ : EReal) := fun x => by
    have := D.envelope_le_obstacle k (s x)
    rwa [D.obstacle_sec hμs k x] at this
  have hdnt := SGPT.Okounkov.TranscendentalWNReg.dntConstantObstacleStatement (m + 1) F.carrier
    F.omega θs (fun x => D.envelope k (s x)) hres c₀ hle
  have hset : s ⁻¹' D.contact k = {x | D.envelope k (s x) = (c₀ : EReal)} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, contact, cutoffContactSet]
    change D.envelope k (s x) = (D.obstacle k (s x) : EReal) ↔ _
    rw [D.obstacle_sec hμs k x]
  have hmass := TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume F.omega θs
    hres
  have hcls : RealBottChern.ofRepresentative θs = RealBottChern.ofRepresentative D.θ :=
    ofRepresentative_pullback_deformationForm_fibreSection F D.hμ D.hE D.hEℰ.weight_eq
      D.hEℰ.support_eq D.θ D.b D.c hp hs hμs
  have hfin : SGPT.PSH.VariableComplexAtlas.sourceClassVolume
      (RealBottChern.ofRepresentative D.θ) ≠ ⊤ :=
    (TranscendentalVolumeConcavity.sourceClassVolume_lt_top F.omega _).ne
  calc fibreContactMass F D.form D.μ D.χ k s hs
      = (SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure F.omega θs).restrict
          {x | D.envelope k (s x) = (c₀ : EReal)} univ := by
        rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, ← hset]
        rfl
    _ ≤ diagonalPotentialMeasure θs (fun x => D.envelope k (s x)) hres univ := hdnt univ
    _ = diagonalPotentialMass θs (fun x => D.envelope k (s x)) hres := rfl
    _ ≤ SGPT.PSH.VariableComplexAtlas.sourceClassVolume (RealBottChern.ofRepresentative θs) :=
        hmass
    _ = ENNReal.ofReal D.vol := by
        rw [hcls, vol, classVolumeReal, ENNReal.ofReal_toReal hfin]

theorem fibreMass_le (k : ℕ) (τ : ℂ) : D.fibreMass k τ ≤ ENNReal.ofReal D.vol := by
  by_cases hτ : τ = 0
  · rw [fibreMass, dif_pos hτ]; exact zero_le
  · rw [fibreMass, dif_neg hτ]
    exact D.fibreContactMass_le (affineLinePoint_ne_projectiveZero hτ) k (D.contMDiff_sec hτ)
      (D.μ_sec hτ)

end FibreBound

end MCData

end SGPT.Okounkov.TranscendentalWN
