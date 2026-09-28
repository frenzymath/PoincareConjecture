import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionCylinderRectangles
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.FourConvexPiecesEulerCount









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.CompressionCylinder

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

private def rimSide (i : Fin 4) : Set V2 := Prod.fst '' side i

private theorem mem_rimSide (i : Fin 4) (z : V2) :
    z ∈ rimSide i ↔ (z, (0 : ℝ)) ∈ side i := by
  constructor
  · rintro ⟨⟨w, t⟩, hw, rfl⟩
    exact (mem_side i (w, 0)).mpr ⟨by norm_num, ((mem_side i (w, t)).mp hw).2⟩
  · intro hz
    exact ⟨(z, 0), hz, rfl⟩

private theorem iUnion_rimSide : (⋃ i, rimSide i) = Q := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (iUnion_side.subset (mem_iUnion.mpr ⟨i, (mem_rimSide i z).mp hi⟩)).1
  · intro hz
    have h : (z, (0 : ℝ)) ∈ carrier := ⟨hz, by norm_num⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (iUnion_side.symm.subset h)
    exact mem_iUnion.mpr ⟨i, (mem_rimSide i z).mpr hi⟩



theorem square_rim_surfaceEulerCount (K : SimplicialComplex ℝ V2)
    (hK : K.faces.Finite) (hspace : K.space = Q) : K.surfaceEulerCount = 0 := by
  let fstMap : (V2 × ℝ) →ᴬ[ℝ] V2 := (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap
  have hmodels (i : Fin 4) : ∃ C : SimplicialComplex ℝ V2,
      C.faces.Finite ∧ C.space = rimSide i := by
    obtain ⟨J, hJ, hJs⟩ := exists_side_complex i
    obtain ⟨C, hC, hCs⟩ :=
      ((J.affineOnFaces_affine fstMap).finitePiecewiseAffineOn hJ).exists_finite_triangulation_image
    exact ⟨C, hC, hCs.trans (congrArg (fun S => Prod.fst '' S) hJs)⟩
  choose C hC hCs using hmodels
  have hcover : K.space = ⋃ i, (C i).space := by
    simp only [hCs]
    exact hspace.trans iUnion_rimSide.symm
  have hconvex (i : Fin 4) : Convex ℝ (C i).space := by
    rw [hCs]
    exact (side_convex i).affine_image fstMap.toAffineMap
  have hne (i : Fin 4) : (C i).space.Nonempty := by
    rw [hCs]
    exact (side_nonempty i).image Prod.fst
  have hadj : ((C 0).space ∩ (C 1).space).Nonempty ∧
      ((C 2).space ∩ (C 3).space).Nonempty ∧
      ((C 0).space ∩ (C 3).space).Nonempty ∧
      ((C 1).space ∩ (C 2).space).Nonempty := by
    have hpair (i j : Fin 4) (h : (side i ∩ side j).Nonempty) :
        ((C i).space ∩ (C j).space).Nonempty := by
      obtain ⟨z, hi, hj⟩ := h
      rw [hCs, hCs]
      exact ⟨z.1, mem_image_of_mem Prod.fst hi, mem_image_of_mem Prod.fst hj⟩
    exact ⟨hpair 0 1 adjacent_intersections_nonempty.1,
      hpair 2 3 adjacent_intersections_nonempty.2.1,
      hpair 0 3 adjacent_intersections_nonempty.2.2.1,
      hpair 1 2 adjacent_intersections_nonempty.2.2.2⟩
  have hdisj : Disjoint (C 0).space (C 2).space ∧
      Disjoint (C 1).space (C 3).space := by
    have hpair (i j : Fin 4) (h : Disjoint (side i) (side j)) :
        Disjoint (C i).space (C j).space := by
      rw [hCs, hCs]
      exact disjoint_left.mpr (fun z hi hj =>
        disjoint_left.mp h ((mem_rimSide i z).mp hi) ((mem_rimSide j z).mp hj))
    exact ⟨hpair 0 2 opposite_disjoint.1, hpair 1 3 opposite_disjoint.2⟩
  exact K.surfaceEulerCount_eq_zero_of_four_convex_cover hK C hC hcover hconvex hne
    (fun _ => ⊤) (fun _ _ _ => by trivial) (fun _ => by
      rw [AffineSubspace.direction_top, finrank_top]
      simp) hadj hdisj

end PoincareConjecture.M76.CompressionCylinder
