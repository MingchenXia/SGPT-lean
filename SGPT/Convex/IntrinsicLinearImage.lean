import SGPT.Convex.Subgradient
import SGPT.Convex.HalfLine

/-!
# Actual intrinsic-interior transport through linear images

The actual affine-span directions give a genuine surjective restriction of
the linear map. The finite-dimensional open-map theorem then transports the
actual relative neighborhood, without an image-interior certificate.
-/

namespace SGPT.Convex

open Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- An actual finite-dimensional linear image sends intrinsic-interior points
into the intrinsic interior of the actual image, even without convexity. -/
theorem linearImage_mem_intrinsicInterior (T : E →ₗ[ℝ] F)
    {C : Set E} {x : E} (hx : x ∈ intrinsicInterior ℝ C) :
    T x ∈ intrinsicInterior ℝ (T '' C) := by
  let A := affineSpan ℝ C
  let B := affineSpan ℝ (T '' C)
  let xA : A := ⟨x, subset_affineSpan ℝ _ (intrinsicInterior_subset hx)⟩
  let yB : B := ⟨T x, subset_affineSpan ℝ _ ⟨x, intrinsicInterior_subset hx, rfl⟩⟩
  let : Nonempty A := ⟨xA⟩
  let : Nonempty B := ⟨yB⟩
  have hdir : B.direction = A.direction.map T := by
    change (affineSpan ℝ (T.toAffineMap '' C)).direction =
      (affineSpan ℝ C).direction.map T
    rw [← AffineSubspace.map_span T.toAffineMap C, AffineSubspace.map_direction]
    rfl
  let L : A.direction →ₗ[ℝ] B.direction :=
    (T.comp A.direction.subtype).codRestrict B.direction (by
      intro v
      rw [hdir]
      exact ⟨v, v.property, rfl⟩)
  have hsurj : Function.Surjective L := by
    intro w
    have hw : (w : F) ∈ A.direction.map T := hdir ▸ w.property
    obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.mp hw
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  have hopen : IsOpenMap L := L.isOpenMap_of_finiteDimensional hsurj
  let eA := AffineIsometryEquiv.vaddConst ℝ xA
  let eB := AffineIsometryEquiv.vaddConst ℝ yB
  let FA := A.subtype.comp eA.toAffineEquiv.toAffineMap
  let FB := B.subtype.comp eB.toAffineEquiv.toAffineMap
  let CA : Set A.direction := FA ⁻¹' C
  let CB : Set B.direction := FB ⁻¹' (T '' C)
  have hxA : xA ∈ interior ((↑) ⁻¹' C : Set A) := by
    obtain ⟨y, hy, heq⟩ := mem_intrinsicInterior.mp hx
    have hyx : y = xA := Subtype.ext heq
    simpa only [hyx] using hy
  have hzero : (0 : A.direction) ∈ interior CA := by
    change (0 : A.direction) ∈ interior (eA.toHomeomorph ⁻¹' ((↑) ⁻¹' C : Set A))
    rw [← eA.toHomeomorph.preimage_interior]
    change eA 0 ∈ interior ((↑) ⁻¹' C : Set A)
    simpa [eA] using hxA
  have hvalue (v : A.direction) : FB (L v) = T (FA v) := by
    change T (v : E) + T x = T ((v : E) + x)
    exact (T.map_add _ _).symm
  have hmaps : MapsTo L CA CB := by
    intro v hv
    change FB (L v) ∈ T '' C
    rw [hvalue]
    exact ⟨FA v, hv, rfl⟩
  have hzeroB : (0 : B.direction) ∈ interior CB := by
    simpa only [map_zero] using hopen.mapsTo_interior hmaps hzero
  apply mem_intrinsicInterior.mpr
  refine ⟨yB, ?_, rfl⟩
  have h : eB 0 ∈ interior ((↑) ⁻¹' (T '' C) : Set B) := by
    change (0 : B.direction) ∈ eB.toHomeomorph ⁻¹' interior ((↑) ⁻¹' (T '' C) : Set B)
    rw [eB.toHomeomorph.preimage_interior]
    exact hzeroB
  simpa [eB] using h

/-- Product relative interiors give actual difference-image qualification. -/
theorem sub_mem_intrinsicInterior_image_prod {C D : Set E} {x y : E}
    (hx : x ∈ intrinsicInterior ℝ C) (hy : y ∈ intrinsicInterior ℝ D) :
    x - y ∈ intrinsicInterior ℝ ((fun p : E × E ↦ p.1 - p.2) '' (C ×ˢ D)) := by
  have hp : (x, y) ∈ intrinsicInterior ℝ (C ×ˢ D) := by
    rw [intrinsicInterior_prod_eq]
    exact ⟨hx, hy⟩
  exact linearImage_mem_intrinsicInterior
    ((LinearMap.fst ℝ E E) - LinearMap.snd ℝ E E) hp

/-- An actual common relative-interior point qualifies the actual difference domain. -/
theorem zero_mem_intrinsicInterior_difference {C D : Set E} {x : E}
    (hC : x ∈ intrinsicInterior ℝ C) (hD : x ∈ intrinsicInterior ℝ D) :
    (0 : E) ∈ intrinsicInterior ℝ {z | ∃ u ∈ C, ∃ v ∈ D, u - v = z} := by
  have heq : ((fun p : E × E ↦ p.1 - p.2) '' (C ×ˢ D)) =
      {z | ∃ u ∈ C, ∃ v ∈ D, u - v = z} := by
    ext z
    constructor
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, h⟩
      exact ⟨u, hu, v, hv, h⟩
    · rintro ⟨u, hu, v, hv, h⟩
      exact ⟨(u, v), ⟨hu, hv⟩, h⟩
  simpa only [heq, sub_self] using sub_mem_intrinsicInterior_image_prod hC hD

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- An actual intrinsic-interior point can be extended beyond any actual set point. -/
theorem exists_mem_openSegment_of_mem_intrinsicInterior {C : Set E} {x y : E}
    (hx : x ∈ intrinsicInterior ℝ C) (hy : y ∈ C) :
    ∃ z ∈ C, x ∈ openSegment ℝ y z := by
  let A := affineSpan ℝ C
  have hxspan : x ∈ A := subset_affineSpan ℝ _ (intrinsicInterior_subset hx)
  have hyspan : y ∈ A := subset_affineSpan ℝ _ hy
  let xA : A := ⟨x, hxspan⟩
  let : Nonempty A := ⟨xA⟩
  let d : A.direction := ⟨x - y, A.vsub_mem_direction hxspan hyspan⟩
  let e := AffineIsometryEquiv.vaddConst ℝ xA
  have hxA : xA ∈ interior ((↑) ⁻¹' C : Set A) := by
    obtain ⟨w, hw, hweq⟩ := mem_intrinsicInterior.mp hx
    have heq : w = xA := Subtype.ext hweq
    simpa only [heq] using hw
  have hcont : Continuous (fun t : ℝ ↦ e (t • d)) :=
    e.continuous.comp (continuous_id.smul continuous_const)
  have htend : Filter.Tendsto (fun t : ℝ ↦ e (t • d)) (𝓝 0) (𝓝 xA) := by
    simpa [e] using hcont.continuousAt.tendsto (x := 0)
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, e (t • d) ∈ ((↑) ⁻¹' C : Set A) :=
    htend (mem_interior_iff_mem_nhds.mp hxA)
  obtain ⟨t, ht, htC⟩ :=
    ((show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).and
      (hevent.filter_mono nhdsWithin_le_nhds)).exists
  let z : E := t • (x - y) + x
  have hz : z ∈ C := by
    change (e (t • d) : E) ∈ C at htC
    exact htC
  refine ⟨z, hz, ?_⟩
  let a : ℝ := t / (1 + t)
  let b : ℝ := 1 / (1 + t)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hat : a = b * t := by dsimp [a, b]; ring
  refine ⟨a, b, ha, hb, hab, ?_⟩
  calc
    a • y + b • z = (a • y + a • (x - y)) + b • x := by
      simp only [z, smul_add, smul_smul, ← hat, ← add_assoc]
    _ = a • x + b • x := by rw [← smul_add]; simp
    _ = x := by rw [← add_smul, hab, one_smul]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Any actual bottom value propagates to all intrinsic-interior domain points. -/
theorem eq_bot_of_exists_bot_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsConvex f) (hbot : ∃ y, f y = ⊥) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) : f x = ⊥ := by
  obtain ⟨y, hy⟩ := hbot
  have hyD : y ∈ effectiveDomain f := by simp [effectiveDomain, hy]
  obtain ⟨z, hz, hxz⟩ := exists_mem_openSegment_of_mem_intrinsicInterior hx hyD
  exact eq_bot_of_eq_bot_of_mem_openSegment hf hy hz hxz

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- One genuine nonbottom relative-interior domain value excludes bottom globally. -/
theorem isProper_of_ne_bot_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsConvex f) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) (hfinite : f x ≠ ⊥) :
    IsProper f := by
  refine ⟨hf, ⟨x, intrinsicInterior_subset hx⟩, ?_⟩
  intro y hy
  exact hfinite (eq_bot_of_exists_bot_of_mem_intrinsicInterior hf ⟨y, hy⟩ hx)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Actual common intrinsic-interior membership survives actual intersections. -/
theorem mem_intrinsicInterior_inter {C D : Set E} {x : E}
    (hC : x ∈ intrinsicInterior ℝ C) (hD : x ∈ intrinsicInterior ℝ D) :
    x ∈ intrinsicInterior ℝ (C ∩ D) := by
  let A := affineSpan ℝ (C ∩ D)
  let B := affineSpan ℝ C
  let H := affineSpan ℝ D
  have hxCD : x ∈ C ∩ D := ⟨intrinsicInterior_subset hC, intrinsicInterior_subset hD⟩
  let xA : A := ⟨x, subset_affineSpan ℝ _ hxCD⟩
  let iB : A → B := fun p ↦ ⟨p, (affineSpan_mono ℝ inter_subset_left) p.property⟩
  let iH : A → H := fun p ↦ ⟨p, (affineSpan_mono ℝ inter_subset_right) p.property⟩
  have hiB : Continuous iB := continuous_subtype_val.subtype_mk _
  have hiH : Continuous iH := continuous_subtype_val.subtype_mk _
  have hBC : ((↑) ⁻¹' C : Set B) ∈ 𝓝 (iB xA) := by
    obtain ⟨w, hw, hweq⟩ := mem_intrinsicInterior.mp hC
    have heq : w = iB xA := Subtype.ext hweq
    simpa only [heq] using mem_interior_iff_mem_nhds.mp hw
  have hHD : ((↑) ⁻¹' D : Set H) ∈ 𝓝 (iH xA) := by
    obtain ⟨w, hw, hweq⟩ := mem_intrinsicInterior.mp hD
    have heq : w = iH xA := Subtype.ext hweq
    simpa only [heq] using mem_interior_iff_mem_nhds.mp hw
  have hpreB := hiB.continuousAt.preimage_mem_nhds hBC
  have hpreH := hiH.continuousAt.preimage_mem_nhds hHD
  apply mem_intrinsicInterior.mpr
  refine ⟨xA, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  exact inter_mem hpreB hpreH

end SGPT.Convex
