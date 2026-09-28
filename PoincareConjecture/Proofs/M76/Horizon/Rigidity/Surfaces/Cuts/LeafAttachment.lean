import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTriangleCopies
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


noncomputable def leafTriangleMap (a b c : E) : (ℝ × ℝ) →ᴬ[ℝ] E × ℝ :=
  (((ContinuousAffineMap.lineMap a b).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap) +
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (c - a)).toContinuousAffineMap).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

@[simp] theorem leafTriangleMap_apply (a b c : E) (x : ℝ × ℝ) :
    leafTriangleMap a b c x = (AffineMap.lineMap a b x.2 + x.1 • (c - a), x.1) := rfl

theorem leafTriangleMap_injective {a b : E} (hab : a ≠ b) (c : E) :
    Function.Injective (leafTriangleMap a b c) := by
  intro x y hxy
  have hfirst := congrArg Prod.fst hxy
  have hheight : x.1 = y.1 := congrArg Prod.snd hxy
  simp only [leafTriangleMap_apply, hheight, add_left_inj] at hfirst
  exact Prod.ext hheight (AffineMap.lineMap_injective ℝ hab hfirst)

theorem leafTriangleMap_common_edge (a b c : E) :
    leafTriangleMap a b c '' segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) =
      inclusion (E := E) 0 '' segment ℝ b a := by
  calc
    _ = segment ℝ (leafTriangleMap a b c (0, 1)) (leafTriangleMap a b c (0, 0)) :=
      image_segment ℝ (leafTriangleMap a b c).toAffineMap _ _
    _ = segment ℝ (inclusion (E := E) 0 b) (inclusion (E := E) 0 a) := by simp [inclusion]
    _ = _ := (image_segment ℝ (inclusion (E := E) 0).toAffineMap _ _).symm


theorem leafTriangleMap_inter_zero_carrier (a b c : E) {s : Set E}
    (hbase : segment ℝ b a ⊆ s) :
    (inclusion (E := E) 0 '' s) ∩
        (leafTriangleMap a b c '' convexHull ℝ (range rightTriangle)) =
      inclusion (E := E) 0 '' segment ℝ b a := by
  ext z
  constructor
  · rintro ⟨⟨w, hw, hwz⟩, ⟨x, hx, hxz⟩⟩
    have hx0 : x.1 = 0 := congrArg Prod.snd (hxz.trans hwz.symm)
    have hxedge : x ∈ segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) := by
      obtain ⟨_, hy, hsum⟩ := (mem_right_region_iff x).mp hx
      apply (mem_common_edge_iff x).mpr
      exact ⟨hx0, hy, by simpa [hx0] using hsum⟩
    rw [← leafTriangleMap_common_edge a b c]
    exact ⟨x, hxedge, hxz⟩
  · intro hz
    refine ⟨image_mono hbase hz, ?_⟩
    rw [← leafTriangleMap_common_edge a b c] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨x, ?_, rfl⟩
    obtain ⟨hx0, hy, hy1⟩ := (mem_common_edge_iff x).mp hx
    exact (mem_right_region_iff x).mpr ⟨by simp [hx0], hy, by simpa [hx0]⟩


theorem projection_leafTriangleMap_image (a b c : E) :
    Prod.fst '' (leafTriangleMap a b c '' convexHull ℝ (range rightTriangle)) =
      convexHull ℝ ({a, c, b} : Set E) := by
  let F := (LinearMap.fst ℝ E ℝ).toAffineMap.comp (leafTriangleMap a b c).toAffineMap
  have hvertices : F '' range rightTriangle = ({a, c, b} : Set E) := by
    ext x
    simp [F, rightTriangle, leafTriangleMap_apply, eq_comm, or_comm, or_left_comm]
  calc
    _ = F '' convexHull ℝ (range rightTriangle) := by rw [image_image]; rfl
    _ = convexHull ℝ (F '' range rightTriangle) := F.image_convexHull _
    _ = _ := by rw [hvertices]


def leafOuterSides (a b c : E) : Set (E × ℝ) :=
  segment ℝ (a, 0) (c, 1) ∪ segment ℝ (c, 1) (b, 0)

theorem leafTriangleMap_frontier (a b c : E) :
    leafTriangleMap a b c '' frontier (convexHull ℝ (range rightTriangle)) =
      leafOuterSides a b c ∪ inclusion (E := E) 0 '' segment ℝ b a := by
  have hfrontier : frontier (convexHull ℝ (range rightTriangle)) =
      segment ℝ (0, 0) (1, 0) ∪ segment ℝ (1, 0) (0, 1) ∪
        segment ℝ (0, 1) (0, 0) := by
    rw [rightTriangle.frontier_convexHull_triangle independent_rightTriangle]
    ext x
    simp [Polygon.boundary, Polygon.edgeSet, rightTriangle, Fin.exists_fin_succ,
      affineSegment_eq_segment, or_assoc]
  rw [hfrontier, image_union, image_union, leafTriangleMap_common_edge]
  have himage (x y : ℝ × ℝ) :
      leafTriangleMap a b c '' segment ℝ x y =
        segment ℝ (leafTriangleMap a b c x) (leafTriangleMap a b c y) :=
    image_segment ℝ (leafTriangleMap a b c).toAffineMap x y
  rw [himage, himage]
  simp [leafOuterSides]

theorem leafOuterSides_zero_height {a b c : E} {x : E × ℝ}
    (hx : x ∈ leafOuterSides a b c) (hzero : x.2 = 0) :
    x ∈ ({(b, 0), (a, 0)} : Set (E × ℝ)) := by
  rcases hx with ⟨u, v, hu, hv, huv, hx⟩ | ⟨u, v, hu, hv, huv, hx⟩
  · have hv0 : v = 0 := by
      have h := congrArg Prod.snd hx
      simpa [hzero] using h
    have hu1 : u = 1 := by linarith
    right
    simpa [hu1, hv0] using hx.symm
  · have hu0 : u = 0 := by
      have h := congrArg Prod.snd hx
      simpa [hzero] using h
    have hv1 : v = 1 := by linarith
    left
    simpa [hu0, hv1] using hx.symm


def freshLeafRim (r : Set E) (a b c : E) : Set (E × ℝ) :=
  ((inclusion (E := E) 0 '' r) ∪
    (leafOuterSides a b c ∪ inclusion (E := E) 0 '' segment ℝ b a)) \
      ((inclusion (E := E) 0 '' segment ℝ b a) \ {(b, 0), (a, 0)})

theorem leafOuterSides_subset_freshLeafRim (r : Set E) (a b c : E) :
    leafOuterSides a b c ⊆ freshLeafRim r a b c := by
  intro x hx
  refine ⟨Or.inr (Or.inl hx), ?_⟩
  rintro ⟨⟨w, hw, hwx⟩, hne⟩
  apply hne
  apply leafOuterSides_zero_height hx
  exact (congrArg Prod.snd hwx).symm


theorem retained_subset_freshLeafRim {r t : Set E} (a b c : E)
    (htr : t ⊆ r) (htbase : Disjoint t (segment ℝ b a \ {b, a})) :
    inclusion (E := E) 0 '' t ⊆ freshLeafRim r a b c := by
  rintro x ⟨w, hw, rfl⟩
  refine ⟨Or.inl ⟨w, htr hw, rfl⟩, ?_⟩
  rintro ⟨⟨v, hv, hvw⟩, hne⟩
  have hvw' : v = w := congrArg Prod.fst hvw
  subst v
  apply Set.disjoint_left.mp htbase hw
  refine ⟨hv, ?_⟩
  rintro (rfl | rfl)
  · exact hne (Or.inl rfl)
  · exact hne (Or.inr rfl)

variable [FiniteDimensional ℝ E]


theorem fresh_leaf_disk_attachment {s r : Set E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s r)
    {a b : E} (hab : a ≠ b) (c : E) (hbase : segment ℝ b a ⊆ r) :
    IsFinitePLBallPair (ℝ × ℝ)
      ((inclusion (E := E) 0 '' s) ∪
        (leafTriangleMap a b c '' convexHull ℝ (range rightTriangle)))
      (freshLeafRim r a b c) := by
  let A := leafTriangleMap a b c
  let I := inclusion (E := E) 0
  have hA : Function.Injective A := leafTriangleMap_injective hab c
  have hI : Function.Injective I := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  have hnew := (rightTriangle.isFinitePLBallPair_convexHull_triangle
    independent_rightTriangle).affine_image A hA.injOn
  rw [leafTriangleMap_frontier] at hnew
  have hnewbase : I '' segment ℝ b a ⊆ leafOuterSides a b c ∪ I '' segment ℝ b a :=
    subset_union_right
  have hd : IsFinitePLBallPair ℝ (I '' segment ℝ b a) {(b, 0), (a, 0)} := by
    have hd' := isFinitePLBallPair_common_edge.affine_image A hA.injOn
    simpa only [A, leafTriangleMap_common_edge, image_insert_eq, image_singleton,
      leafTriangleMap_apply, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
      zero_smul, add_zero] using hd'
  exact (hs.affine_image I hI.injOn).union_of_boundary_interval hnew hd
    (image_mono hbase) hnewbase
    (by intro h; exact hab (congrArg Prod.fst h).symm)
    (leafTriangleMap_inter_zero_carrier a b c (hbase.trans hs.1))

end PoincareConjecture.M76.OriginalTriangleCopies
