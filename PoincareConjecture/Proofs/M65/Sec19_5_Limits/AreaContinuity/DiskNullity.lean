import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import PoincareConjecture.Proofs.M02.BallHomotopyExtension

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65NullHomotopic_of_spanningDisk {g : RiemannianMetric 3 M}
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g gamma) :
    IsNullHomotopicLoop gamma := by
  let disk : C(LoopDisk, M) :=
    ⟨fun z => D.map z.val, continuousOn_iff_continuous_domRestrict.mp D.continuous_on_disk⟩
  let circle : C(sphere (0 : LoopPlane) 1, LoopCircle) :=
    ⟨fun z => ⟨z.val, mem_sphere_zero_iff_norm.mp z.property⟩,
      by fun_prop⟩
  have hinv_mem (z : sphere (0 : LoopPlane) 1) :
      (D.reparameterization.inverse (circle z)).val ∈ loopDiskSet := by
    change ‖(D.reparameterization.inverse (circle z)).val - 0‖ ≤ 1
    rw [sub_zero, (D.reparameterization.inverse (circle z)).property]
  let inverse : C(sphere (0 : LoopPlane) 1, LoopDisk) :=
    ⟨fun z => ⟨(D.reparameterization.inverse (circle z)).val, hinv_mem z⟩,
      (continuous_subtype_val.comp
        (D.reparameterization.continuous_inverse.comp circle.continuous)).subtype_mk hinv_mem⟩
  let boundary : C(sphere (0 : LoopPlane) 1, M) :=
    ⟨fun z => gamma (circle z), gamma.continuous.comp circle.continuous⟩
  let : ContractibleSpace LoopDisk :=
    contractibleSpace_closedBall (x := (0 : LoopPlane)) (r := 1) zero_le_one
  have hn := ((id_nullhomotopic LoopDisk).comp_right disk).comp_left inverse
  have heq : (disk.comp (ContinuousMap.id LoopDisk)).comp inverse = boundary := by
    ext z
    change D.map (D.reparameterization.inverse (circle z)).val = gamma (circle z)
    rw [D.boundary_eq, D.reparameterization.right_inverse]
  rw [heq] at hn
  obtain ⟨f, hf⟩ :=
    (Proofs.M02.sphere_nullhomotopic_iff_extends_closedBall boundary).mp hn
  let den : LoopPlane → ℝ := fun z => max 1 ‖z‖
  have hden (z : LoopPlane) : 0 < den z := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hden_cont : Continuous den := continuous_const.max continuous_norm
  have hclamp (z : LoopPlane) : (den z)⁻¹ • z ∈ closedBall (0 : LoopPlane) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hden z))]
    calc
      _ ≤ (den z)⁻¹ * den z := mul_le_mul_of_nonneg_left
        (le_max_right 1 ‖z‖) (inv_nonneg.mpr (hden z).le)
      _ = 1 := inv_mul_cancel₀ (hden z).ne'
  let clamp : C(LoopPlane, closedBall (0 : LoopPlane) 1) :=
    ⟨fun z => ⟨(den z)⁻¹ • z, hclamp z⟩,
      ((hden_cont.inv₀ (fun z => (hden z).ne')).smul continuous_id).subtype_mk _⟩
  refine ⟨fun z => f (clamp z), f.continuous.comp clamp.continuous, ?_⟩
  intro z
  let zs : sphere (0 : LoopPlane) 1 := ⟨z.val, mem_sphere_zero_iff_norm.mpr z.property⟩
  have hboundary : clamp z.val = ⟨zs.val, sphere_subset_closedBall zs.property⟩ := by
    apply Subtype.ext
    change (max 1 ‖z.val‖)⁻¹ • z.val = z.val
    rw [z.property, max_self, inv_one, one_smul]
  change f (clamp z.val) = gamma z
  rw [hboundary, hf zs]
  rfl

end PoincareConjecture
