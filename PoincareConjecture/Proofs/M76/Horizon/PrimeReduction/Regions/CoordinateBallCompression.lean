import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.CubicalBallCompression
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.PrimeReduction.BallSupportedAmbientExtension



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

private noncomputable def cubeCoordinates : CubeShell.Ambient ≃ᴬ[ℝ] V3 :=
  let A : CubeShell.Ambient ≃ₗ[ℝ] V3 := {
    toFun := fun x i => CubeShell.coordinate i x
    invFun := CubeShell.vector
    left_inv := CubeShell.vector_coordinate
    right_inv := fun x => funext (CubeShell.coordinate_vector x)
    map_add' := by intro x y; funext i; exact map_add (CubeShell.coordinate i) x y
    map_smul' := by intro r x; funext i; exact map_smul (CubeShell.coordinate i) r x }
  A.toContinuousLinearEquiv.toContinuousAffineEquiv

private theorem norm_cubeCoordinates (x : CubeShell.Ambient) : ‖cubeCoordinates x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    exact (Real.norm_eq_abs _).trans_le (CubeShell.abs_coordinate_le_norm x i)
  · apply (CubeShell.norm_le_iff _ _).mpr
    intro i
    exact (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm (cubeCoordinates x) i)

theorem exists_coordinate_ball_compression {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcb : c < b) :
    ∃ H : closedBall (0 : V3) b ≃ₜ closedBall (0 : V3) b, H.IsFinitePL ∧
      (∀ x : closedBall (0 : V3) b, ‖(x : V3)‖ ≤ a →
        (H x : V3) = (c/a) • (x : V3)) ∧
      (∀ x : closedBall (0 : V3) b, ‖(x : V3)‖ = b → H x = x) ∧
      ∀ x : closedBall (0 : V3) b, ‖(x : V3)‖ ≤ a ↔ ‖(H x : V3)‖ ≤ c := by
  obtain ⟨G,hG,hsmall,hfix,hmem⟩ := CubeShell.exists_boundary_fixed_ball_compression ha hab hc hcb
  have him : cubeCoordinates '' CubeShell.shell 0 b = closedBall (0 : V3) b := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_closedBall,dist_zero_right,norm_cubeCoordinates] using hy.2
    · intro hx
      refine ⟨cubeCoordinates.symm x,⟨norm_nonneg _,?_⟩,cubeCoordinates.apply_symm_apply x⟩
      have hn := norm_cubeCoordinates (cubeCoordinates.symm x)
      rw [cubeCoordinates.apply_symm_apply] at hn
      simpa only [mem_closedBall,dist_zero_right,hn] using hx
  let C := (cubeCoordinates.toHomeomorph.image (CubeShell.shell 0 b)).trans
    (Homeomorph.setCongr him)
  let H := C.symm.trans (G.trans C)
  have hH : H.IsFinitePL := (hG.affine_conjugate cubeCoordinates cubeCoordinates).setCongr him him
  have hnorm (x : CubeShell.shell 0 b) : ‖(C x : V3)‖ = ‖(x : CubeShell.Ambient)‖ :=
    norm_cubeCoordinates x
  refine ⟨H,hH,?_,?_,?_⟩
  · intro x hx
    have hx' : ‖(C.symm x : CubeShell.Ambient)‖ ≤ a := by
      simpa only [C.apply_symm_apply] using (hnorm (C.symm x)) ▸ hx
    change cubeCoordinates (G (C.symm x)) = _
    rw [hsmall _ hx']
    change (fun i => CubeShell.coordinate i ((c/a) • (C.symm x : CubeShell.Ambient))) = _
    have heq : cubeCoordinates (C.symm x) = (x : V3) := congrArg Subtype.val (C.apply_symm_apply x)
    funext i
    rw [map_smul]
    exact congrArg (fun v : V3 => (c/a) * v i) heq
  · intro x hx
    have hx' : ‖(C.symm x : CubeShell.Ambient)‖ = b := by
      rw [←hnorm,C.apply_symm_apply,hx]
    change C (G (C.symm x)) = x
    rw [hfix _ hx',C.apply_symm_apply]
  · intro x
    have hh := hmem (C.symm x)
    rw [←hnorm (C.symm x),C.apply_symm_apply,←hnorm (G (C.symm x))] at hh
    exact hh

theorem exists_supported_coordinate_ball_compression {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcb : c < b) :
    ∃ G : V3 ≃ₜ V3,
      G.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 ∧
      (∀ x, b ≤ ‖x‖ → G x = x) ∧
      (∀ x, ‖x‖ ≤ a → G x = (c/a) • x) ∧
      ∀ x, ‖x‖ ≤ a ↔ ‖G x‖ ≤ c := by
  obtain ⟨H,hH,hsmall,hfix,hmem⟩ := exists_coordinate_ball_compression ha hab hc hcb
  have hclosed : IsClosed (closedBall (0 : V3) b) := isClosed_closedBall
  have hfront : ∀ x : closedBall (0 : V3) b,
      (x : V3) ∈ frontier (closedBall (0 : V3) b) → H x = x := by
    intro x hx
    apply hfix
    simpa only [frontier_closedBall _ (ha.trans hab).ne',mem_sphere,dist_zero_right] using hx
  let G := H.closedExtension hclosed hfront
  have hout (x : V3) (hx : b ≤ ‖x‖) : G x = x := by
    apply H.closedExtension_apply_notMem_interior hclosed hfront
    simpa only [interior_closedBall _ (ha.trans hab).ne',mem_ball,dist_zero_right,not_lt] using hx
  have hin (x : V3) (hx : ‖x‖ ≤ b) : G x = H ⟨x,by simpa using hx⟩ :=
    H.closedExtension_apply_mem hclosed hfront (by simpa using hx)
  refine ⟨G,?_,hout,?_,?_⟩
  · apply G.toOpenPartialHomeomorph.mem_piecewiseAffineGroupoid_of_local_finitePL
    intro x _
    obtain ⟨K,hK,hxK,_⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
    exact ⟨K.space,hxK (mem_singleton x),hH.closedExtension_finite_on_polyhedron hclosed hfront K hK⟩
  · intro x hx
    rw [hin x (hx.trans hab.le)]
    exact hsmall _ hx
  · intro x
    by_cases hx : ‖x‖ ≤ b
    · rw [hin x hx]
      exact hmem ⟨x,by simpa using hx⟩
    · rw [hout x (le_of_not_ge hx)]
      constructor <;> intro h <;> linarith

end PoincareConjecture.M76
