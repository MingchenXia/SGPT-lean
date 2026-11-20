/-
Copyright (c) 2026. All rights reserved.
-/
import SGPT.Foundations.PublishedEnvelope.NormedIdealQuotient
import SGPT.Foundations.PublishedEnvelope.NormedAdditiveQuotientUltrametric

/-! # The true infimum ideal quotient norm remains ultrametric -/
noncomputable section
namespace SGPT.Foundations.PublishedEnvelope.NormedIdealQuotient

/-- Genuine infimum-norm representatives derive the quotient ultrametric inequality. -/
instance quotientIsUltrametricDist {A : Type*} [SeminormedCommRing A]
    [IsUltrametricDist A] (I : Ideal A) : IsUltrametricDist (A ⧸ I) :=
  NormedAdditiveQuotient.quotientIsUltrametricDist I.toAddSubgroup

end SGPT.Foundations.PublishedEnvelope.NormedIdealQuotient
