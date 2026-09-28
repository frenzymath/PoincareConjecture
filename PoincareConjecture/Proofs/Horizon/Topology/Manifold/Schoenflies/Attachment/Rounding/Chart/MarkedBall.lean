import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Sweep.UnitBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.Transport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_marked_ball_sweep
    (b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → S2) (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x) :
    ∃ C : Opens E3,
      ∃ e : Diffeomorph (𝓡 3) 𝓘(Real, Hemisphere.Plane (g 0 : E3) × Real)
          C (Hemisphere.Plane (g 0 : E3) × Real) ∞,
        (b '' closedBall 0 1) ∩ C =
          (fun p => (e.symm p : E3)) '' {p | 0 ≤ p.2 ∧ p.2 ≤ 1} ∧
        (b '' ball 0 1) ∩ C =
          (fun p => (e.symm p : E3)) '' {p | 0 < p.2 ∧ p.2 < 1} ∧
        (fun x => b (g x)) '' ball (0 : E2) 1 =
          (fun p => (e.symm p : E3)) '' {p | p.2 = 0} ∧
        ((fun x => b (g x)) '' closedBall (0 : E2) 1) ∩ C =
          (fun p => (e.symm p : E3)) '' {p | p.2 = 0} ∧
        (b '' closedBall 0 1) \ C ⊆
          (fun x => b (g x)) '' sphere (0 : E2) 1 := by
  obtain ⟨J, H, hHB, hHBopen, _, _, hHD, hHDopen, hHE⟩ :=
    Normalization.exists_ambient_ball_normalization b g hgi hgl
  let hv := norm_eq_of_mem_sphere (g 0)
  let C₀ := unitBallSweepRange hv
  let e₀ := unitBallSweepChart hv
  let C := pullbackOpen H C₀
  let e := (pullbackDiffeomorph H C₀).trans e₀
  have hcoord (p : Hemisphere.Plane (g 0 : E3) × Real) :
      (e.symm p : E3) = H.symm (e₀.symm p : E3) := rfl
  have hclosed := pullback_image_inter H C₀ e₀.symm hHB
    (unitBallSweepChart_closedBall hv)
  have hopen := pullback_image_inter H C₀ e₀.symm hHBopen
    (unitBallSweepChart_ball hv)
  have hdisk := pullback_image_inter H C₀ e₀.symm hHD
    (unitBallSweepChart_closedDisk hv)
  refine ⟨C, e, hclosed, hopen, ?_, hdisk, ?_⟩
  · apply (H.toEquiv.injective.image_injective)
    change H '' ((fun x => b (g x)) '' ball (0 : E2) 1) =
      H '' ((fun p => (e.symm p : E3)) '' {p | p.2 = 0})
    rw [hHDopen, unitBallSweepChart_openDisk hv, image_image]
    apply image_congr
    intro p _
    change (unitBallSweepParametrization hv p : E3) = H (H.symm (e₀.symm p : E3))
    rw [H.apply_symm_apply]
    rfl
  · intro y hy
    have hHy : H y ∈ closedBall (0 : E3) 1 := hHB ▸ mem_image_of_mem H hy.1
    have hnot : H y ∉ C₀ := hy.2
    have hedge := unitBallSweepChart_edge hv ⟨hHy, hnot⟩
    rw [← hHE] at hedge
    obtain ⟨z, hz, he⟩ := hedge
    exact H.injective he ▸ hz

end Poincare.Manifold.Schoenflies.Rounding
