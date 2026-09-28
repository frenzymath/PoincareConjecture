import PoincareConjecture.Proofs.M76.Mathlib.PlanarRadialArc
import PoincareConjecture.Proofs.M76.Smoothing.CircleSubdivision

set_option autoImplicit false

open Set NormedSpace

namespace PoincareConjecture.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

noncomputable def planarGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) : ℂ :=
  Circle.exp (gapAngle w i)

theorem planarGapVertices_eq_circle (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    planarGapVertices w i = (AddCircle.homeomorphCircle' (circleGapVertices w i) : ℂ) := rfl

theorem norm_planarGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    ‖planarGapVertices w i‖ = 1 := Circle.norm_coe _

theorem injective_planarGapVertices (w : shortArcGapSpace n theta) :
    Function.Injective (planarGapVertices w) := by
  intro i j hij
  apply injective_circleGapVertices w
  apply AddCircle.homeomorphCircle'.injective
  exact Subtype.ext hij

theorem continuous_planarGapVertices :
    Continuous (planarGapVertices : shortArcGapSpace n theta → Fin (n + 3) → ℂ) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (Circle.exp.continuous.comp
    ((continuous_gapAngle i).comp continuous_subtype_val))

theorem planarGapVertices_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    (Circle.exp (gapAngle w i + w.val i) : ℂ) = planarGapVertices w (i + 1) :=
  congrArg (fun z : AddCircle (2 * Real.pi) => (AddCircle.homeomorphCircle' z : ℂ))
    (circleGapArc_endpoint w i)

theorem linearIndependent_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    LinearIndependent ℝ
      ((↑) : ↥({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) → ℂ) := by
  have h := Complex.linearIndependent_circleExp_pair
    (a := gapAngle w i) (b := gapAngle w i + w.val i)
    (by linarith [(w.property.1 i).1]) (by simpa using (w.property.1 i).2)
  rw [planarGapVertices_endpoint] at h
  exact h

def planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) : Set ℂ :=
  segment ℝ (planarGapVertices w i) (planarGapVertices w (i + 1))

theorem injOn_normalize_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (planarGapEdge w i) := by
  simpa only [convexHull_pair, planarGapEdge] using
    (linearIndependent_planarGapEdge w i).injOn_normalize_convexHull

theorem normalize_image_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    NormedSpace.normalize '' planarGapEdge w i =
      (fun z : AddCircle (2 * Real.pi) => (AddCircle.homeomorphCircle' z : ℂ)) ''
        circleGapArc w i := by
  calc
    NormedSpace.normalize '' planarGapEdge w i =
        (fun phi => (Circle.exp phi : ℂ)) '' Icc (gapAngle w i) (gapAngle w i + w.val i) := by
      unfold planarGapEdge
      rw [← planarGapVertices_endpoint]
      exact Complex.normalize_image_segment_circleExp
        (by linarith [(w.property.1 i).1]) (by simpa using (w.property.1 i).2)
    _ = _ := by rw [circleGapArc, image_image]; rfl

private theorem planar_circle_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3))
    {z : AddCircle (2 * Real.pi)}
    (hz : z ∈ ({circleGapVertices w i, circleGapVertices w (i + 1)} :
      Set (AddCircle (2 * Real.pi)))) :
    (AddCircle.homeomorphCircle' z : ℂ) ∈
      ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) := by
  rcases hz with rfl | hz
  · exact mem_insert _ _
  · rw [mem_singleton_iff] at hz
    subst z
    exact mem_insert_of_mem _ (mem_singleton _)

private theorem planar_endpoint_mem_edge (w : shortArcGapSpace n theta) (i : Fin (n + 3))
    {z : ℂ} (hz : z ∈ ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ)) :
    z ∈ planarGapEdge w i := by
  rw [planarGapEdge, ← convexHull_pair]
  exact subset_convexHull ℝ _ hz

theorem planarGapEdges_common_direction (w : shortArcGapSpace n theta)
    {i j : Fin (n + 3)} (hij : i ≠ j) {x y : ℂ}
    (hx : x ∈ planarGapEdge w i) (hy : y ∈ planarGapEdge w j)
    (hxy : NormedSpace.normalize x = NormedSpace.normalize y) :
    x = y ∧ x ∈ ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) ∩
      {planarGapVertices w j, planarGapVertices w (j + 1)} := by
  obtain ⟨z, hz, hzx⟩ := (normalize_image_planarGapEdge w i).subset ⟨x, hx, rfl⟩
  obtain ⟨z', hz', hzy⟩ := (normalize_image_planarGapEdge w j).subset ⟨y, hy, rfl⟩
  have hzz : z = z' := AddCircle.homeomorphCircle'.injective
    (Subtype.ext (hzx.trans (hxy.trans hzy.symm)))
  subst z'
  have hends := (circleGapArc_inter w hij).subset ⟨hz, hz'⟩
  have he_i := planar_circle_endpoint w i hends.1
  have he_j := planar_circle_endpoint w j hends.2
  have hunit : NormedSpace.normalize (AddCircle.homeomorphCircle' z : ℂ) =
      (AddCircle.homeomorphCircle' z : ℂ) :=
    normalize_eq_self_of_norm_eq_one (Circle.norm_coe _)
  have hxe : x = (AddCircle.homeomorphCircle' z : ℂ) :=
    injOn_normalize_planarGapEdge w i hx (planar_endpoint_mem_edge w i he_i)
      (hzx.symm.trans hunit.symm)
  have hye : y = (AddCircle.homeomorphCircle' z : ℂ) :=
    injOn_normalize_planarGapEdge w j hy (planar_endpoint_mem_edge w j he_j)
      (hzy.symm.trans hunit.symm)
  exact ⟨hxe.trans hye.symm, hxe ▸ ⟨he_i, he_j⟩⟩

theorem injOn_normalize_iUnion_planarGapEdge (w : shortArcGapSpace n theta) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (⋃ i, planarGapEdge w i) := by
  intro x hx y hy hxy
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
  by_cases hij : i = j
  · subst j
    exact injOn_normalize_planarGapEdge w i hxi hyj hxy
  · exact (planarGapEdges_common_direction w hij hxi hyj hxy).1

theorem planarGapEdge_inter_subset (w : shortArcGapSpace n theta) (i j : Fin (n + 3)) :
    planarGapEdge w i ∩ planarGapEdge w j ⊆
      convexHull ℝ ({planarGapVertices w i, planarGapVertices w (i + 1)} ∩
        {planarGapVertices w j, planarGapVertices w (j + 1)}) := by
  by_cases hij : i = j
  · subst j
    rw [inter_self, inter_self, convexHull_pair]
    exact Subset.rfl
  · intro x hx
    exact subset_convexHull ℝ _ (planarGapEdges_common_direction w hij hx.1 hx.2 rfl).2

theorem normalize_image_iUnion_planarGapEdge (w : shortArcGapSpace n theta) :
    NormedSpace.normalize '' (⋃ i, planarGapEdge w i) = Metric.sphere (0 : ℂ) 1 := by
  rw [image_iUnion]
  simp_rw [normalize_image_planarGapEdge]
  rw [← image_iUnion, iUnion_circleGapArc]
  apply Subset.antisymm
  · rintro _ ⟨z, _, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using Circle.norm_coe
      (AddCircle.homeomorphCircle' z)
  · intro z hz
    let u : Circle := ⟨z, hz⟩
    exact ⟨AddCircle.homeomorphCircle'.symm u, mem_univ _,
      congrArg Subtype.val (AddCircle.homeomorphCircle'.apply_symm_apply u)⟩

end PoincareConjecture.M76.Smoothing
