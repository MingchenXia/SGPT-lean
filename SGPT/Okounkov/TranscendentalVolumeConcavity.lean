import SGPT.Okounkov.TranscendentalVolumeConcavityContinuity
import SGPT.Okounkov.TranscendentalVolumeConcavityMatsumura

/-!
# Concavity and continuity of the volume; restricted volumes (package VOLCONC)

Blueprint nodes `tok:ext-volume-concave` and `tok:restricted-volume` of
`claude-okounkov-transcendental`, with the sub-lemmas of `claude-tok-volconc`.

* `TranscendentalVolumeConcavityStatement`: the statements `VolumeConcavityStatement` (with
  `VolumeRootConcaveStatement`, `VolumeContinuityStatement`, `VolumePositiveIffBigStatement`) and
  the definition `restrictedVolume` (DRWNXZ §2);
* `TranscendentalVolumeConcavityACVolume`: `vol = ` Boucksom's absolutely continuous volume,
  `vol α > 0 ⟺ α` big, monotonicity and the right limit;
* `TranscendentalVolumeConcavityMinkowski`: Minkowski's inequality
  `vol(α)^{1/n} + vol(β)^{1/n} ≤ vol(α + β)^{1/n}`, homogeneity, concavity of `vol^{1/n}`;
* `TranscendentalVolumeConcavityContinuity`: closedness of the pseudo-effective cone, continuity of
  `vol` on `H^{1,1}(X, ℝ)` (`C⁰` quotient topology), openness of the big cone, and
  `volumeConcavity : VolumeConcavityStatement X` (**`tok:ext-volume-concave`**);
* `TranscendentalVolumeConcavityRestricted`: well-definedness and bounds of the restricted
  volume, and `vol_{X|Z}(ξ) = ∫_Z ⟨(θ|_Z + dd^c V_θ|_Z)^d⟩` for `Z ⊄ nK(ξ)`;
* `TranscendentalVolumeConcavityMatsumura`: the book's `eq:rest_vol_Mat_def`,
  `eq:rest_vol_CT_def`, `prop:restvol_voltrace` (both equalities) and
  `thm:rest_volume_tr_volume`.
-/
