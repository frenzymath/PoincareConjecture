import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.FanAngles
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.VertexCaps








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in
private theorem mfderivWithin_scaled_curve_zero
    {eta gamma : ℝ → S} (c : ℝ)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) gamma 0)
    (heq : EqOn eta (fun t => gamma (c * t)) (Icc (0 : ℝ) 1)) :
    mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) eta (Icc (0 : ℝ) 1) 0 1 =
      c • mfderiv 𝓘(ℝ, ℝ) (𝓡 2) gamma 0 1 := by
  have hphi : HasDerivAt (fun t : ℝ => c * t) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hgamma' : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) gamma (c * 0) := by
    simpa using hgamma
  calc
    _ = mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) (fun t => gamma (c * t))
        (Icc (0 : ℝ) 1) 0 1 :=
      congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) => L 1)
        (mfderivWithin_congr_of_mem heq (by simp))
    _ = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (gamma ∘ (fun t => c * t)) 0 1 :=
      congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) => L 1)
        (mfderivWithin_eq_mfderiv
          ((uniqueDiffOn_Icc zero_lt_one 0 (by simp)).uniqueMDiffWithinAt)
          (hgamma'.comp 0 hphi.differentiableAt.mdifferentiableAt))
    _ = _ := by
      have h := LeviCivitaData.mfderiv_curve_reparam hgamma' hphi
      dsimp only [TangentSpace] at h ⊢
      convert h using 1
      exact congrArg (fun t : ℝ => c •
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) gamma t 1 : EuclideanSpace ℝ (Fin 2)))
        (mul_zero c).symm

namespace Topology.Surface.ChartCircleArrangementVertexPatch

variable {r : S → ℝ} {p : S}
  {P : ChartCircleArrangementVertexPatch r p} {x : Bool × Bool → S}

namespace VertexCapFaces

variable (B : VertexCapFaces P x)


theorem first_velocity_zero (i : Bool × Bool) :
    mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary 2).map
        (Icc (0 : ℝ) 1) 0 1 =
      (if i.1 then B.scale else -B.scale) •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
          (fun t : ℝ => P.sectorCoordinates (true, true) (t, 0)) 0 1 := by
  apply mfderivWithin_scaled_curve_zero
  · have hsource : (0 : ℝ × ℝ) ∈ (P.sectorCoordinates (true, true)).source :=
      P.sectorCoordinates_square_source _ ⟨⟨le_rfl, P.width_pos.le⟩, ⟨le_rfl, P.width_pos.le⟩⟩
    have hcoord := (P.sectorCoordinates_smooth (true, true)).contMDiffAt
      ((P.sectorCoordinates (true, true)).open_source.mem_nhds hsource)
    have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
      (contDiff_id.prodMk contDiff_const).contMDiff
    exact (hcoord.comp 0 (f := fun t : ℝ => (t, (0 : ℝ)))
      hline.contMDiffAt).mdifferentiableAt (by simp)
  · intro t ht
    rw [B.first_map i t ht]
    change P.productCoordinates (sectorParameterEquiv P.center i (t * B.scale, 0)) =
      P.productCoordinates (sectorParameterEquiv P.center (true, true)
        ((if i.1 then B.scale else -B.scale) * t, 0))
    congr 1
    rcases i with ⟨i, j⟩
    cases i <;> cases j <;> simp [sectorParameterEquiv_apply, mul_comm]


theorem second_velocity_zero (i : Bool × Bool) :
    mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary 1).map
        (Icc (0 : ℝ) 1) 0 1 =
      (if i.2 then B.scale else -B.scale) •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
          (fun t : ℝ => P.sectorCoordinates (true, true) (0, t)) 0 1 := by
  apply mfderivWithin_scaled_curve_zero
  · have hsource : (0 : ℝ × ℝ) ∈ (P.sectorCoordinates (true, true)).source :=
      P.sectorCoordinates_square_source _ ⟨⟨le_rfl, P.width_pos.le⟩, ⟨le_rfl, P.width_pos.le⟩⟩
    have hcoord := (P.sectorCoordinates_smooth (true, true)).contMDiffAt
      ((P.sectorCoordinates (true, true)).open_source.mem_nhds hsource)
    have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun t : ℝ => ((0 : ℝ), t)) :=
      (contDiff_const.prodMk contDiff_id).contMDiff
    exact (hcoord.comp 0 (f := fun t : ℝ => ((0 : ℝ), t))
      hline.contMDiffAt).mdifferentiableAt (by simp)
  · intro t ht
    rw [B.second_map i t ht]
    change P.productCoordinates (sectorParameterEquiv P.center i (0, t * B.scale)) =
      P.productCoordinates (sectorParameterEquiv P.center (true, true)
        (0, (if i.2 then B.scale else -B.scale) * t))
    congr 1
    rcases i with ⟨i, j⟩
    cases i <;> cases j <;> simp [sectorParameterEquiv_apply, mul_comm]


theorem sum_corner_angles (g : RiemannianMetric 2 S) :
    (∑ i : Bool, ∑ j : Bool,
      g.cornerAngle p
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) ((B.face (i, j)).boundary 2).map
          (Icc (0 : ℝ) 1) 0 1)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) ((B.face (i, j)).boundary 1).map
          (Icc (0 : ℝ) 1) 0 1)) = 2 * Real.pi := by
  simp_rw [B.first_velocity_zero, B.second_velocity_zero]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, neg_smul,
    g.cornerAngle_neg_left, g.cornerAngle_neg_right,
    g.cornerAngle_smul_pos_left p _ _ B.scale_pos,
    g.cornerAngle_smul_pos_right p _ _ B.scale_pos]
  ring

end VertexCapFaces
end Topology.Surface.ChartCircleArrangementVertexPatch
end PoincareConjecture
