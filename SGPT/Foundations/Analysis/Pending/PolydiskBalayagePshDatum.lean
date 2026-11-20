import SGPT.Foundations.Analysis.Pending.PolydiskBalayage

set_option autoImplicit false

/-!
# Balayage on the polydisk for a plurisubharmonic datum, across the boundary

`Pending.PolydiskBalayage` proves Xia's Proposition 1.2.9 on the unit polydisk
for a datum that is plurisubharmonic **and continuous** near `P̄`.  The datum
the proposition is stated for is merely plurisubharmonic and locally bounded,
and this module removes the continuity hypothesis.

## The route

`PolydiskPshMollifierData` already produces, from a locally bounded
plurisubharmonic `u` on an open `Ω ⊇ P̄`, a decreasing sequence of `C²` Perron
data converging to `u` on `P̄`.  The same construction gives all of that on a
whole **open** neighbourhood `W` of `P̄`: the approximants are mollifications of
`u` cut off outside a set relatively compact in `Ω`, and the cutoff is
identically `1` near `P̄`.  That is
`exists_open_isPerronData_contDiff_antitone_tendsto`.

Each approximant is globally smooth, hence continuous, and plurisubharmonic on
`W`, so `plurisubharmonicOn_polydiskBalayage` applies to it with `Ω := W`.  The
balayages then decrease, and their pointwise infimum is the balayage of `u`:
inside `P` this is `perronEnvelope_iInf_eq_of_antitone`, and on `W ∖ P` both
sides are the limit of the same antitone sequence.  A decreasing limit of
plurisubharmonic functions is plurisubharmonic, so the balayage of `u` is
plurisubharmonic on `W`.

Away from `P̄` no approximation is needed: the balayage *is* `u` on the open
complement of `P̄`, so the two regions cover `Ω`.

Source: M. Xia, *Sheaves and geometry of pluripotential theory*, Prop. 1.2.9
and Lemma 2.4.3; E. Bedford and B. A. Taylor, *A new capacity for
plurisubharmonic functions*, Prop. 9.1.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- **A locally bounded plurisubharmonic function near `P̄` is a decreasing
limit of `C²` Perron data on a whole open neighbourhood of `P̄`.**  This is
`exists_isPerronData_contDiff_antitone_tendsto` with the neighbourhood exposed:
the approximants are plurisubharmonic there, not merely on `P`, and the
monotone convergence holds there, not merely on `P̄`. -/
theorem exists_open_isPerronData_contDiff_antitone_tendsto
    (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    ∃ (W : Set (ComplexModel n)) (v : ℕ → ComplexModel n → ℝ),
      IsOpen W ∧ closedUnitPolydisk n ⊆ W ∧ W ⊆ (Ω : Set (ComplexModel n)) ∧
      (∀ j, IsPerronData (v j)) ∧ (∀ j, Continuous (v j)) ∧
      (∀ j, PlurisubharmonicOn (fun z ↦ (v j z : EReal)) W) ∧
      (∀ z ∈ W, Antitone fun j ↦ v j z) ∧
      (∀ z ∈ W, Tendsto (fun j ↦ v j z) atTop (𝓝 (u z))) := by
  classical
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure
      (isCompact_closedUnitPolydisk (n := n)) Ω.isOpen hPΩ
  set A : Opens (ComplexModel n) := ⟨V, hVo⟩ with hAdef
  have hrc : RelativelyCompactIn A Ω := ⟨hVc, hVΩ⟩
  obtain ⟨f, hfsmooth, hfanti, hftend⟩ :=
    HolomorphicPullback.exists_decreasingMollifierApproximation hu hrc
  obtain ⟨χ, hχ1, -⟩ :=
    exists_testFunction_eq_one_nhds_compact (Ω := A) (K := closedUnitPolydisk n)
      isCompact_closedUnitPolydisk hKV
  obtain ⟨N, hNo, hKN, hχN⟩ := eventually_nhdsSet_iff_exists.mp hχ1
  set W : Set (ComplexModel n) := N ∩ V with hWdef
  have hWo : IsOpen W := hNo.inter hVo
  have hKW : closedUnitPolydisk n ⊆ W := fun z hz ↦ ⟨hKN hz, hKV hz⟩
  have hWV : W ⊆ V := fun _ hz ↦ hz.2
  have hWΩ : W ⊆ (Ω : Set (ComplexModel n)) := fun z hz ↦ hVΩ (subset_closure (hWV hz))
  set v : ℕ → ComplexModel n → ℝ :=
    fun j ↦ V.indicator (fun z ↦ (χ : ComplexModel n → ℝ) z * f j z) with hvdef
  have heq : ∀ j, ∀ z ∈ W, v j z = f j z := by
    intro j z hz
    rw [hvdef]
    simp only
    rw [Set.indicator_of_mem hz.2, hχN z hz.1, one_mul]
  have hsmooth : ∀ j, ContDiff ℝ ∞ (v j) := fun j ↦
    UniformBoundedGlobalMass.contDiff_cutoff_extend (Ω := A) χ.contDiff
      χ.tsupport_subset (hfsmooth j).1
  have hvpsh : ∀ j, PlurisubharmonicOn (fun z ↦ (v j z : EReal)) W := by
    intro j z hz
    refine ((hfsmooth j).2.1 z (hWV hz)).congr ?_
    filter_upwards [hWo.mem_nhds hz] with y hy
    rw [heq j y hy]
  have hperron : ∀ j, IsPerronData (v j) := fun j ↦
    ⟨hn, (hsmooth j).continuous.continuousOn,
      (hvpsh j).mono fun z hz ↦ hKW (unitPolydisk_subset_closedUnitPolydisk hz)⟩
  refine ⟨W, v, hWo, hKW, hWΩ, hperron, fun j ↦ (hsmooth j).continuous, hvpsh, ?_, ?_⟩
  · intro z hz
    simpa only [heq _ z hz] using hfanti z (hWV hz)
  · intro z hz
    simpa only [heq _ z hz] using hftend z (hWV hz)

/-- **Xia's Proposition 1.2.9 on the unit polydisk, for the data it is stated
for.**  If `u` is plurisubharmonic and locally bounded on an open `Ω`
containing the closed polydisk, then its balayage — `perronEnvelope u` inside
`P`, `u` outside — is plurisubharmonic on all of `Ω`.  No continuity of `u` is
assumed. -/
theorem plurisubharmonicOn_polydiskBalayage_of_isLocallyBoundedPshOn
    (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    PlurisubharmonicOn (fun z ↦ ((polydiskBalayage u z : ℝ) : EReal))
      (Ω : Set (ComplexModel n)) := by
  classical
  obtain ⟨W, v, hWo, hKW, hWΩ, hv, hvc, hvpsh, hanti, htend⟩ :=
    exists_open_isPerronData_contDiff_antitone_tendsto hn hu hPΩ
  obtain ⟨C, -, hC⟩ :=
    hu.exists_compact_abs_bound (isCompact_closedUnitPolydisk (n := n)) hPΩ
  have hule : ∀ j, ∀ z ∈ closedUnitPolydisk n, u z ≤ v j z := fun j z hz ↦
    (hanti z (hKW hz)).le_of_tendsto (htend z (hKW hz)) j
  have hcv : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, -C ≤ v j ζ := fun j ζ hζ ↦
    (neg_le_of_abs_le (hC ζ hζ.1)).trans (hule j ζ hζ.1)
  have hantib : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Antitone fun j ↦ v j ζ :=
    fun ζ hζ ↦ hanti ζ (hKW hζ.1)
  have htendb : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      Tendsto (fun j ↦ v j ζ) atTop (𝓝 (u ζ)) := fun ζ hζ ↦ htend ζ (hKW hζ.1)
  have hantiB : ∀ z ∈ W, Antitone fun j ↦ polydiskBalayage (v j) z := by
    intro z hz j j' hjj'
    by_cases hzP : z ∈ unitPolydisk n
    · simp only [polydiskBalayage_of_mem hzP]
      exact antitone_perronEnvelope hv hantib hzP hjj'
    · simp only [polydiskBalayage_of_notMem hzP]
      exact hanti z hz hjj'
  have hlow : ∀ z ∈ W, ∀ j, min (-C) (u z) ≤ polydiskBalayage (v j) z := by
    intro z hz j
    by_cases hzP : z ∈ unitPolydisk n
    · rw [polydiskBalayage_of_mem hzP]
      exact (min_le_left _ _).trans (le_perronEnvelope_of_forall_le (hv j) (hcv j) hzP)
    · rw [polydiskBalayage_of_notMem hzP]
      exact (min_le_right _ _).trans ((hanti z hz).le_of_tendsto (htend z hz) j)
  have hbdd : ∀ z ∈ W, BddBelow (Set.range fun j ↦ polydiskBalayage (v j) z) := fun z hz ↦
    ⟨min (-C) (u z), by rintro _ ⟨j, rfl⟩; exact hlow z hz j⟩
  have hMle : ∀ x ∈ closedUnitPolydisk n, u x ≤ C := fun x hx ↦
    (le_abs_self _).trans (hC x hx)
  have hcu : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, -C ≤ u ζ := fun ζ hζ ↦
    neg_le_of_abs_le (hC ζ hζ.1)
  have hiInf : ∀ z ∈ W, (⨅ j, polydiskBalayage (v j) z) = polydiskBalayage u z := by
    intro z hz
    by_cases hzP : z ∈ unitPolydisk n
    · rw [polydiskBalayage_of_mem (u := u) hzP,
        perronEnvelope_iInf_eq_of_antitone hv hantib htendb hMle hcu hzP]
      exact iInf_congr fun j ↦ polydiskBalayage_of_mem hzP
    · rw [polydiskBalayage_of_notMem (u := u) hzP]
      have hlim : Tendsto (fun j ↦ polydiskBalayage (v j) z) atTop (𝓝 (u z)) :=
        (htend z hz).congr fun j ↦ (polydiskBalayage_of_notMem hzP).symm
      exact tendsto_nhds_unique (tendsto_atTop_ciInf (hantiB z hz) (hbdd z hz)) hlim
  have hpshj : ∀ j,
      PlurisubharmonicOn (fun z ↦ ((polydiskBalayage (v j) z : ℝ) : EReal)) W := fun j ↦
    plurisubharmonicOn_polydiskBalayage (hv j) hWo (hvc j).continuousOn (hvpsh j)
  have hiInfPsh : PlurisubharmonicOn
      (fun z ↦ ⨅ j, ((polydiskBalayage (v j) z : ℝ) : EReal)) W :=
    DiscPshOn.plurisubharmonicOn_iInf_of_antitone hWo (fun j ↦ (hpshj j).discPshOn)
      fun z hz j j' hjj' ↦ EReal.coe_le_coe_iff.2 (hantiB z hz hjj')
  have hW : PlurisubharmonicOn (fun z ↦ ((polydiskBalayage u z : ℝ) : EReal)) W := by
    intro x hx
    refine (hiInfPsh x hx).congr ?_
    filter_upwards [hWo.mem_nhds hx] with y hy
    rw [← coe_ciInf_of_antitone (hantiB y hy) (hbdd y hy), hiInf y hy]
  intro x hx
  by_cases hxK : x ∈ closedUnitPolydisk n
  · exact hW x (hKW hxK)
  · refine (hu.1 x hx).congr ?_
    filter_upwards [isClosed_closedUnitPolydisk.isOpen_compl.mem_nhds hxK] with y hy
    rw [polydiskBalayage_of_notMem fun h ↦ hy (unitPolydisk_subset_closedUnitPolydisk h)]

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
