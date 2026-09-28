import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.IntersectionFaces










set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K K₀ K₁ : SimplicialComplex ℝ V} {j jfinal : V → t.Carrier}
  {Q : OpenPartialHomeomorph t.Carrier E} {B : OpenPartialHomeomorph s.Carrier E}
  {J : SimplicialComplex ℝ E} {N : K.faces → Set t.Carrier} {R : Set M}

theorem RelativeFaceMotionData.exists_final_intersection_faces
    (motion : RelativeFaceMotionData step K K₀ K₁ j Q B J N R)
    (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {face : Finset V} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    (hj : PolyhedralPLInCharts t.charts j K.space) (hji : InjOn j K.space)
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (hval : ∀ z, Q z = B (step.projection (step.inclusion z)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hold : EqOn jfinal j K₀.space)
    (hnext : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    {x y : V} (hx : x ∈ convexHull ℝ (face : Set V)) (hxold : x ∉ K₀.space)
    (hxQ : j x ∈ Q.source) (hxJ : Q (j x) ∈ J.space)
    (old : K₀.faces) (hy : y ∈ convexHull ℝ (old.val : Set V))
    (hxy : step.projection (step.inclusion (jfinal x)) =
      step.projection (step.inclusion (jfinal y))) :
    ∃ a b : Finset E,
      a ∈ motion.freeComplex.faces ∧ a ∉ motion.fixedComplex.faces ∧
      b ∈ (motion.targets old).faces ∧
      Q (jfinal x) ∈ intrinsicInterior ℝ
        (convexHull ℝ (motion.coordinates.map 1 '' (a : Set E))) ∧
      B (step.projection (step.inclusion (jfinal y))) ∈
        intrinsicInterior ℝ (convexHull ℝ (b : Set E)) ∧
      a.card ≤ face.card ∧ b.card ≤ old.val.card ∧
      affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E) ∪ (b : Set E)) = ⊤ ∧
      Module.finrank ℝ ((affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E)) ⊓
        affineSpan ℝ (b : Set E)).direction) + Module.finrank ℝ E =
        (a.card - 1) + (b.card - 1) := by
  have hxnext : x ∈ K₁.space := hsucc.symm.subset (Or.inr hx)
  have hxK : x ∈ K.space := K.convexHull_subset_space hface hx
  let w := Q (jfinal x)
  have hwcoord : w = motion.coordinates.map 1 (Q (j x)) :=
    motion.coordinate_of_successor_agreement hJQ hnext hxnext hxQ hxJ
  have hwJ : w ∈ J.space := by
    rw [hwcoord]
    exact (motion.coordinates.carrier 1).subset
      (mem_image_of_mem (motion.coordinates.map 1) hxJ)
  have hfinalpoint : jfinal x = Q.symm (motion.coordinates.map 1 (Q (j x))) :=
    (hnext hxnext).trans (motion.chart_formula 1 hxQ)
  have hfinalQ : jfinal x ∈ Q.source := by
    rw [hfinalpoint]
    apply Q.map_target
    rw [← hwcoord]
    exact hJQ hwJ
  have hsource : w ∈ motion.coordinates.map 1 '' motion.source.space := by
    refine ⟨Q (j x), ?_, hwcoord.symm⟩
    rw [motion.source_space]
    exact ⟨⟨j x, ⟨mem_image_of_mem j hxnext, hxQ⟩, rfl⟩, hxJ⟩
  have hfree : w ∉ motion.protectedSource.space := by
    intro hwfixed
    have hfixed : motion.coordinates.map 1 w = w :=
      motion.coordinates.fixed_protected 1 w hwfixed
    have hsame : Q (j x) = w := (motion.coordinates.map 1).injective
      (hwcoord.symm.trans hfixed.symm)
    rw [motion.protected_space] at hwfixed
    obtain ⟨⟨z, ⟨⟨xold, hxoldK, rfl⟩, hjoldQ⟩, hvalue⟩, _⟩ := hwfixed
    have hjx : j x = j xold := Q.injOn hxQ hjoldQ (hsame.trans hvalue.symm)
    have hxx : x = xold := hji hxK (SimplicialComplex.space_subset_of_le hK₀ hxoldK) hjx
    exact hxold (hxx.symm ▸ hxoldK)
  have hcommon : w = B (step.projection (step.inclusion (jfinal y))) := by
    change Q (jfinal x) = B (step.projection (step.inclusion (jfinal y)))
    rw [hval, hxy]
  have htarget : w ∈ (motion.targets old).space := by
    rw [motion.targets_space_of_prefix_agreement hold old]
    refine ⟨⟨step.projection (step.inclusion (jfinal y)), ?_, hcommon.symm⟩, hwJ⟩
    refine ⟨mem_image_of_mem ((step.projection ∘ step.inclusion) ∘ jfinal) hy, ?_⟩
    have hyB := hmaps hfinalQ
    change step.projection (step.inclusion (jfinal x)) ∈ B.source at hyB
    rwa [hxy] at hyB
  obtain ⟨a, b, ha, ha0, hb, hwa, hwb, hspan, hbcard, hrank⟩ :=
    motion.exists_position_faces_at_intersection old hsource hfree htarget
  obtain ⟨_, _, _, _, hbound⟩ := motion.exists_active_face_bound hK hface hsucc hj hQ hJ hJQ
  refine ⟨a, b, ha, ha0, hb, hwa, ?_, (hbound a ha ha0).2, hbcard, hspan, hrank⟩
  rw [← hcommon]
  exact hwb

end Geometry.OriginalPLTower
