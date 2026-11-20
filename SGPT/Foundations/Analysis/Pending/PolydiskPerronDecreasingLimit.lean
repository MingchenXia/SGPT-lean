import SGPT.Foundations.Analysis.Pending.PolydiskBalayageDecreasingData

set_option autoImplicit false

/-!
# The envelope of a decreasing limit of boundary data

`Pending.PolydiskBalayageDecreasingData` proves that the *pointwise infimum* of
the Perron--Bremermann envelopes of a decreasing sequence of `C²` boundary data
carries no Bedford--Taylor mass.  Błocki's passage from `C²` data to merely
bounded data needs one more step, which this module supplies: that infimum
**is** the envelope of the limiting boundary data,

  `perronEnvelope f z = ⨅ j, perronEnvelope (v j) z`   (`z` in the open polydisk),

whenever `v j ↓ f` on the topological boundary `∂P = P̄ \ P`.  Both inclusions are order
theory over the competitor class of `Pending.PolydiskPerronEnvelope`:

* `≤` — the data only enter the competitor class through their boundary values
  and `f ≤ v j` there, so every competitor for `f` is a competitor for each
  `v j` (`IsPerronCompetitor.mono_boundary`) and therefore lies below every
  `perronEnvelope (v j)`;
* `≥` — the infimum is itself a competitor for `f`.  It is plurisubharmonic and
  locally bounded by `isLocallyBoundedPshOn_iInf_perronEnvelope`, and its
  boundary estimate at `ζ` comes from choosing `j` with `v j ζ < f ζ + ε/2` and
  quoting `IsPerronData.eventually_perronEnvelope_le` for that single `j`.

No continuity of `f` is used, and none is available: the pointwise limit of a
decreasing sequence of continuous functions is in general only upper
semicontinuous, which is exactly why `IsPerronData f` cannot be assumed.  Only
two crude bounds on `f` are needed — an upper bound on the closed polydisk (so
that the competitor family for `f` is bounded above, which is what makes
`perronEnvelope f` a supremum of a bounded set) and a lower bound on the
topological boundary (so that the envelopes are bounded below).

Combining with `eq_zero_of_isBTLimit_of_antitone_perronEnvelope` gives
`eq_zero_of_isBTLimit_perronEnvelope_of_antitone`: the **local form of Xia's
Lemma 2.4.3** for boundary data that are decreasing limits of `C²` Perron data,
i.e. the Perron envelope of such data solves the homogeneous Monge--Ampère
equation on the polydisk.

Source: Z. Błocki, *The complex Monge--Ampère operator in pluripotential
theory*, lecture notes, §2.3 (proof of Theorem 2.3.1); M. Xia, *Non-pluripolar
products on vector bundles and Chern--Weil formulae*, Lemma 2.4.3.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- **The infimum of the envelopes is a competitor for the limiting data.**
Plurisubharmonicity and local boundedness are
`isLocallyBoundedPshOn_iInf_perronEnvelope`; the boundary estimate at `ζ` is
that of a single member `v j` with `v j ζ` already within `ε/2` of `f ζ`. -/
theorem isPerronCompetitor_iInf_perronEnvelope
    {v : ℕ → ComplexModel n → ℝ} {f : ComplexModel n → ℝ}
    (hv : ∀ j, IsPerronData (v j))
    (hanti : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Antitone fun j ↦ v j ζ)
    (hf : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      Tendsto (fun j ↦ v j ζ) atTop (𝓝 (f ζ)))
    {c : ℝ} (hc : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ f ζ) :
    IsPerronCompetitor f (fun z ↦ ⨅ j, perronEnvelope (v j) z) := by
  have hcv : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v j ζ :=
    fun j ζ hζ ↦ (hc ζ hζ).trans ((hanti ζ hζ).le_of_tendsto (hf ζ hζ) j)
  refine ⟨(isLocallyBoundedPshOn_iInf_perronEnvelope hv hanti hcv).1, ?_⟩
  intro ζ hζ ε hε
  obtain ⟨j, hj⟩ :=
    (((hf ζ hζ).eventually
      (eventually_lt_nhds (show f ζ < f ζ + ε / 2 by linarith))).exists)
  filter_upwards [self_mem_nhdsWithin,
    (hv j).eventually_perronEnvelope_le hζ (half_pos hε)] with y hyP hy
  have hle : (⨅ k, perronEnvelope (v k) y) ≤ perronEnvelope (v j) y :=
    ciInf_le (bddBelow_range_perronEnvelope hv hcv hyP) j
  linarith

/-- **The envelope of a decreasing limit of boundary data is the limit of the
envelopes.**  This is the identification Błocki's passage from `C²` to bounded
data needs, and the only place where the competitor class for data that are not
continuous is used. -/
theorem perronEnvelope_iInf_eq_of_antitone
    {v : ℕ → ComplexModel n → ℝ} {f : ComplexModel n → ℝ}
    (hv : ∀ j, IsPerronData (v j))
    (hanti : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Antitone fun j ↦ v j ζ)
    (hf : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      Tendsto (fun j ↦ v j ζ) atTop (𝓝 (f ζ)))
    {M : ℝ} (hM : ∀ x ∈ closedUnitPolydisk n, f x ≤ M)
    {c : ℝ} (hc : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ f ζ)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    perronEnvelope f z = ⨅ j, perronEnvelope (v j) z := by
  have hfle : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, f ζ ≤ v j ζ :=
    fun j ζ hζ ↦ (hanti ζ hζ).le_of_tendsto (hf ζ hζ) j
  have hcv : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v j ζ :=
    fun j ζ hζ ↦ (hc ζ hζ).trans (hfle j ζ hζ)
  have hQ : IsPerronCompetitor f (fun y ↦ ⨅ j, perronEnvelope (v j) y) :=
    isPerronCompetitor_iInf_perronEnvelope hv hanti hf hc
  have hne : Nonempty {w : ComplexModel n → ℝ // IsPerronCompetitor f w} :=
    ⟨⟨_, hQ⟩⟩
  have hbddA : BddAbove
      (range fun w : {w : ComplexModel n → ℝ // IsPerronCompetitor f w} ↦ w.1 z) := by
    refine ⟨M, ?_⟩
    rintro y ⟨w, rfl⟩
    exact w.2.le_of_forall_le hM hz ⟨0, (hv 0).pos⟩
  refine le_antisymm (ciSup_le fun w ↦ ?_) ?_
  · refine le_ciInf fun j ↦ ?_
    exact (hv j).le_perronEnvelope (w.2.mono_boundary (hfle j)) hz
  · exact le_ciSup (f := fun w : {w : ComplexModel n → ℝ // IsPerronCompetitor f w} ↦ w.1 z)
      hbddA ⟨_, hQ⟩

/-- **Balayage on the polydisk for data that are decreasing limits of `C²`
data.**  The Perron--Bremermann envelope of such boundary data carries no
Bedford--Taylor mass: it solves the homogeneous Monge--Ampère equation.

This is the local form of Xia's Lemma 2.4.3 on the polydisk.  The passage from
`C²` to the limit is `eq_zero_of_isBTLimit_of_antitone_perronEnvelope` on the
measure side and `perronEnvelope_iInf_eq_of_antitone` on the envelope side. -/
theorem eq_zero_of_isBTLimit_perronEnvelope_of_antitone
    {v : ℕ → ComplexModel n → ℝ} {f : ComplexModel n → ℝ}
    (hv : ∀ j, IsPerronData (v j)) (hv2 : ∀ j, ContDiff ℝ 2 (v j))
    (hanti : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Antitone fun j ↦ v j ζ)
    (hf : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      Tendsto (fun j ↦ v j ζ) atTop (𝓝 (f ζ)))
    {M : ℝ} (hM : ∀ x ∈ closedUnitPolydisk n, f x ≤ M)
    {c : ℝ} (hc : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ f ζ)
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (unitPolydiskOpens n) (fun _ ↦ perronEnvelope f) μ) :
    μ = 0 := by
  have hcv : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v j ζ :=
    fun j ζ hζ ↦ (hc ζ hζ).trans ((hanti ζ hζ).le_of_tendsto (hf ζ hζ) j)
  refine eq_zero_of_isBTLimit_of_antitone_perronEnvelope hv hv2 hanti hcv
    (hμ.congr fun _ y hy ↦ ?_)
  exact perronEnvelope_iInf_eq_of_antitone hv hanti hf hM hc hy

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
