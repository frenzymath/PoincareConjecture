import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterBoundary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.AmbientSectorAngles
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.CapTransversals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in
private theorem mfderiv_chart_affine_ray
    (C : OpenPartialHomeomorph Plane S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (a d : Plane) (ha : a ∈ C.source) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun t : ℝ => C (a + t • d)) 0 1 =
      mfderiv (𝓡 2) (𝓡 2) C a d := by
  have hCa := (hC.contMDiffAt (C.open_source.mem_nhds ha)).mdifferentiableAt (by simp)
  have hd : HasDerivAt (fun t : ℝ => a + t • d) d 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add a using 1
    simp
  have h := congrArg (fun L => L 1) (mfderiv_comp (0 : ℝ)
    (by simpa using hCa) hd.differentiableAt.mdifferentiableAt)
  dsimp only [TangentSpace] at h ⊢
  simp only [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  rw [show a + (0 : ℝ) • d = a by simp] at h
  exact h

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem firstOuterTip_mem_chart_source (i j : Bool) :
    B.firstOuterTip i ∈ (chartAt Plane (x (i, j))).source := by
  rw [← B.coordinate_first_outer_tip i j]
  exact B.coordinates_target _ ((B.coordinates _).map_source
    (B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 1))))

theorem secondOuterTip_mem_chart_source (i j : Bool) :
    B.secondOuterTip i ∈ (chartAt Plane (x (j, i))).source := by
  rw [← B.coordinate_second_outer_tip i j]
  exact B.coordinates_target _ ((B.coordinates _).map_source
    (B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 2))))

theorem firstOuterChord_eq_chart_differential (i j : Bool) :
    B.firstOuterChord i j =
      mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (x (i, j))).symm
        (chartAt Plane (x (i, j)) (B.firstOuterTip i))
        (chartAt Plane (x (i, j)) (B.secondOuterTip j) -
          chartAt Plane (x (i, j)) (B.firstOuterTip i)) := by
  let C := (chartAt Plane (x (i, j))).symm
  have he : (fun t : ℝ => B.coordinates (i, j)
      (AffineMap.lineMap (rightTriangleBasis B.scale_pos 1) (rightTriangleBasis B.scale_pos 2) t)) =
      fun t : ℝ => C (B.chordEndpoint (i, j) false + t • B.chordDirection (i, j) false) := by
    funext t
    rw [B.chord_ray_eq_boundary, B.boundary_map]
    congr 1
    simp [affineChartSegment, Fin.succAbove, AffineMap.lineMap_apply, add_comm]
  have ha : B.chordEndpoint (i, j) false ∈ C.source := by
    have h := B.chord_ray_mem_target (i, j) false (by simp : (0 : ℝ) ∈ Icc 0 1)
    rw [zero_smul, add_zero] at h
    exact h
  have h := mfderiv_chart_affine_ray C (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (B.chordEndpoint (i, j) false) (B.chordDirection (i, j) false) ha
  dsimp only [TangentSpace] at h ⊢
  have ha0 : B.chordEndpoint (i, j) false = chartAt Plane (x (i, j)) (B.firstOuterTip i) := by
    simp only [chordEndpoint, Bool.false_eq_true, if_false,
      B.planar_first _ _ ⟨B.scale_pos.le, le_rfl⟩, B.sector_first_tip_eq]
  have hd0 : B.chordDirection (i, j) false =
      chartAt Plane (x (i, j)) (B.secondOuterTip j) - chartAt Plane (x (i, j)) (B.firstOuterTip i) := by
    simp only [chordDirection, Bool.false_eq_true, if_false,
      B.planar_first _ _ ⟨B.scale_pos.le, le_rfl⟩,
      B.planar_second _ _ ⟨B.scale_pos.le, le_rfl⟩, B.sector_first_tip_eq, B.sector_second_tip_eq]
  have hcurve := congrArg (fun f : ℝ → S => (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) f 0 : ℝ →L[ℝ] Plane) 1) he
  have heq := hcurve.trans h
  let A : Plane → (Plane →L[ℝ] Plane) := fun z => mfderiv (𝓡 2) (𝓡 2) C z
  have hpoint := congrArg (fun L : Plane →L[ℝ] Plane => L (B.chordDirection (i, j) false))
    (congrArg A ha0)
  have hout := heq.trans hpoint
  rw [hd0] at hout
  exact hout

theorem secondOuterChord_eq_chart_differential (i j : Bool) :
    B.secondOuterChord i j =
      mfderiv (𝓡 2) (𝓡 2) (chartAt Plane (x (j, i))).symm
        (chartAt Plane (x (j, i)) (B.secondOuterTip i))
        (chartAt Plane (x (j, i)) (B.firstOuterTip j) -
          chartAt Plane (x (j, i)) (B.secondOuterTip i)) := by
  let C := (chartAt Plane (x (j, i))).symm
  have he : (fun t : ℝ => B.coordinates (j, i)
      (AffineMap.lineMap (rightTriangleBasis B.scale_pos 2) (rightTriangleBasis B.scale_pos 1) t)) =
      fun t : ℝ => C (B.chordEndpoint (j, i) true + t • B.chordDirection (j, i) true) := by
    funext t
    rw [B.chord_ray_eq_boundary, B.boundary_map]
    change B.coordinates (j, i) (AffineMap.lineMap _ _ t) =
      B.coordinates (j, i) (affineChartSegment _ _ (1 - t))
    congr 1
    simp [affineChartSegment, Fin.succAbove, AffineMap.lineMap_apply, sub_smul]
    module
  have ha : B.chordEndpoint (j, i) true ∈ C.source := by
    have h := B.chord_ray_mem_target (j, i) true (by simp : (0 : ℝ) ∈ Icc 0 1)
    rw [zero_smul, add_zero] at h
    exact h
  have h := mfderiv_chart_affine_ray C (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (B.chordEndpoint (j, i) true) (B.chordDirection (j, i) true) ha
  dsimp only [TangentSpace] at h ⊢
  have ha0 : B.chordEndpoint (j, i) true = chartAt Plane (x (j, i)) (B.secondOuterTip i) := by
    simp only [chordEndpoint, if_true,
      B.planar_second _ _ ⟨B.scale_pos.le, le_rfl⟩, B.sector_second_tip_eq]
  have hd0 : B.chordDirection (j, i) true =
      chartAt Plane (x (j, i)) (B.firstOuterTip j) - chartAt Plane (x (j, i)) (B.secondOuterTip i) := by
    simp only [chordDirection, if_true,
      B.planar_first _ _ ⟨B.scale_pos.le, le_rfl⟩,
      B.planar_second _ _ ⟨B.scale_pos.le, le_rfl⟩, B.sector_first_tip_eq, B.sector_second_tip_eq]
  have hcurve := congrArg (fun f : ℝ → S => (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) f 0 : ℝ →L[ℝ] Plane) 1) he
  have heq := hcurve.trans h
  let A : Plane → (Plane →L[ℝ] Plane) := fun z => mfderiv (𝓡 2) (𝓡 2) C z
  have hpoint := congrArg (fun L : Plane →L[ℝ] Plane => L (B.chordDirection (j, i) true))
    (congrArg A ha0)
  have hout := heq.trans hpoint
  rw [hd0] at hout
  exact hout

noncomputable def firstOuterChartSpoke (i : Bool) (v : S) : Plane :=
  mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v) (B.firstOuterTip i) (B.firstOuterSpoke i)

noncomputable def secondOuterChartSpoke (i : Bool) (v : S) : Plane :=
  mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v) (B.secondOuterTip i) (B.secondOuterSpoke i)

theorem firstOuterSpoke_eq_chart_differential (i : Bool) (v : S)
    (hv : B.firstOuterTip i ∈ (chartAt Plane v).source) :
    B.firstOuterSpoke i =
      mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm
        (chartAt Plane v (B.firstOuterTip i)) (B.firstOuterChartSpoke i v) := by
  have h := congrArg (fun L : Plane →L[ℝ] Plane => L (B.firstOuterSpoke i))
    ((mdifferentiable_chart (I := 𝓡 2) v).symm_comp_deriv hv)
  exact h.symm

theorem secondOuterSpoke_eq_chart_differential (i : Bool) (v : S)
    (hv : B.secondOuterTip i ∈ (chartAt Plane v).source) :
    B.secondOuterSpoke i =
      mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm
        (chartAt Plane v (B.secondOuterTip i)) (B.secondOuterChartSpoke i v) := by
  have h := congrArg (fun L : Plane →L[ℝ] Plane => L (B.secondOuterSpoke i))
    ((mdifferentiable_chart (I := 𝓡 2) v).symm_comp_deriv hv)
  exact h.symm

theorem firstOuterSpoke_ne_zero (i : Bool) : B.firstOuterSpoke i ≠ 0 := by
  apply neg_ne_zero.mpr
  exact coordinateTriangleVelocity_ne_zero (B.coordinates (i, true))
    (rightTriangleBasis B.scale_pos) (B.coordinates_smooth _) (B.coordinates_smooth_symm _)
    (B.triangle_subset_source _) (by decide : (1 : Fin 3) ≠ 0)

theorem secondOuterSpoke_ne_zero (i : Bool) : B.secondOuterSpoke i ≠ 0 := by
  apply neg_ne_zero.mpr
  exact coordinateTriangleVelocity_ne_zero (B.coordinates (true, i))
    (rightTriangleBasis B.scale_pos) (B.coordinates_smooth _) (B.coordinates_smooth_symm _)
    (B.triangle_subset_source _) (by decide : (2 : Fin 3) ≠ 0)

theorem firstOuterChord_eq_common_chart_differential (i : Bool) (v : S)
    (hchart : ∀ j, x (i, j) = v) (j : Bool) :
    B.firstOuterChord i j =
      mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm
        (chartAt Plane v (B.firstOuterTip i))
        (chartAt Plane v (B.secondOuterTip j) - chartAt Plane v (B.firstOuterTip i)) := by
  let D : S → Plane := fun w =>
    mfderiv (𝓡 2) (𝓡 2) (chartAt Plane w).symm (chartAt Plane w (B.firstOuterTip i))
      (chartAt Plane w (B.secondOuterTip j) - chartAt Plane w (B.firstOuterTip i))
  exact (B.firstOuterChord_eq_chart_differential i j).trans (congrArg D (hchart j))

theorem secondOuterChord_eq_common_chart_differential (i : Bool) (v : S)
    (hchart : ∀ j, x (j, i) = v) (j : Bool) :
    B.secondOuterChord i j =
      mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm
        (chartAt Plane v (B.secondOuterTip i))
        (chartAt Plane v (B.firstOuterTip j) - chartAt Plane v (B.secondOuterTip i)) := by
  let D : S → Plane := fun w =>
    mfderiv (𝓡 2) (𝓡 2) (chartAt Plane w).symm (chartAt Plane w (B.secondOuterTip i))
      (chartAt Plane w (B.firstOuterTip j) - chartAt Plane w (B.secondOuterTip i))
  exact (B.secondOuterChord_eq_chart_differential i j).trans (congrArg D (hchart j))

theorem first_outer_angles_eq_chart_differentials
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v) :
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i) (B.firstOuterSpoke i) (B.firstOuterChord i j)) =
      ∑ j : Bool, g.cornerAngle (B.firstOuterTip i)
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (chartAt Plane v (B.firstOuterTip i)))
          (B.firstOuterChartSpoke i v))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (chartAt Plane v (B.firstOuterTip i)))
          (chartAt Plane v (B.secondOuterTip j) - chartAt Plane v (B.firstOuterTip i))) := by
  have hv : B.firstOuterTip i ∈ (chartAt Plane v).source := by
    simpa only [hchart] using B.firstOuterTip_mem_chart_source i true
  apply Finset.sum_congr rfl
  intro j _
  rw [← B.firstOuterSpoke_eq_chart_differential i v hv,
    ← B.firstOuterChord_eq_common_chart_differential i v hchart j]

theorem second_outer_angles_eq_chart_differentials
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v) :
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i) (B.secondOuterSpoke i) (B.secondOuterChord i j)) =
      ∑ j : Bool, g.cornerAngle (B.secondOuterTip i)
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (chartAt Plane v (B.secondOuterTip i)))
          (B.secondOuterChartSpoke i v))
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (chartAt Plane v (B.secondOuterTip i)))
          (chartAt Plane v (B.firstOuterTip j) - chartAt Plane v (B.secondOuterTip i))) := by
  have hv : B.secondOuterTip i ∈ (chartAt Plane v).source := by
    simpa only [hchart] using B.secondOuterTip_mem_chart_source i true
  apply Finset.sum_congr rfl
  intro j _
  rw [← B.secondOuterSpoke_eq_chart_differential i v hv,
    ← B.secondOuterChord_eq_common_chart_differential i v hchart j]

end ChartCircleArrangementVertexPatch.VertexCapFaces

end PoincareConjecture.Topology.Surface
