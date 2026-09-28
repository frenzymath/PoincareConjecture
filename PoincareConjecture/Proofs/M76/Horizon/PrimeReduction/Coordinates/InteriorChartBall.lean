import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ChartwiseBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology







set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_interior_chart_ball
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hne : (interior R).Nonempty) :
    ∃ B : Set X, B ⊆ interior R ∧ Nonempty (ChartwisePLBall e B (frontier B)) := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨i,hi⟩ := he.cover x
  let Q := e i
  let U := Q.target ∩ Q.symm ⁻¹' interior R
  have hU : IsOpen U := Q.continuousOn_symm.isOpen_inter_preimage Q.open_target isOpen_interior
  have hxU : Q x ∈ U := ⟨Q.map_source hi,by simpa only [mem_preimage,Q.left_inv hi] using hx⟩
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  let a : V3 →ᴬ[ℝ] V3 := (r/2) • ContinuousAffineMap.id ℝ V3 +
    ContinuousAffineMap.const ℝ V3 (Q x)
  have hai : Function.Injective a := by
    intro z w h
    have h' : (r/2) • z = (r/2) • w := add_right_cancel h
    exact (smul_right_injective _ (by positivity : (r/2:ℝ) ≠ 0)) h'
  have haU : a '' closedBall (0 : V3) 1 ⊆ U := by
    rintro _ ⟨z,hz,rfl⟩
    apply hrU
    rw [mem_ball,dist_eq_norm]
    change ‖(r/2) • z + Q x - Q x‖ < r
    rw [add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    have hn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    nlinarith
  have hpair := (isFinitePLBallPair_unit_cube (ι := Fin 3)).affine_image a hai.injOn
  obtain ⟨b⟩ := chartwisePLBall_of_finitePLBallPair_in_chart e Q
    (fun y _ => he.cover y) (fun j => he.compatible j i)
    (ContinuousLinearEquiv.refl ℝ V3) hpair (haU.trans inter_subset_left)
  refine ⟨Q.symm '' (a '' closedBall (0 : V3) 1),?_,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact (haU hz).2
  · exact ⟨b.frontier_eq ▸ b⟩

end PoincareConjecture.M76
