import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompatibleInverseChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_boundary_exit_path
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L W : Set X}
    (hL : PLDomain e L) (hW : IsOpen W)
    {x : X} (hx : x ∈ frontier L) (hxW : x ∈ W) :
    ∃ q : ℝ → X, PolyhedralPLInCharts e q (Icc (0 : ℝ) 1) ∧
      q 0 = x ∧ MapsTo q (Icc (0 : ℝ) 1) W ∧
      ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ L ↔ t = 0 := by
  classical
  obtain ⟨ell, v, B, hv, hxB, hzero, hcompat, hhalf⟩ := hL.halfspace x hx
  have hadd (z : V3) (t : ℝ) : ell (z + t • v) = ell z + t := by
    simpa only [vadd_eq_add, map_smul, hv, smul_eq_mul, mul_one, add_comm]
      using ell.map_vadd z (t • v)
  let V : Set V3 := B.target ∩ B.symm ⁻¹' W
  have hV : IsOpen V := B.isOpen_inter_preimage_symm hW
  have hxV : B x ∈ V := ⟨B.mapsTo hxB, by
    change B.symm (B x) ∈ W
    rw [B.left_inv hxB]
    exact hxW⟩
  let r : ℝ → V3 := fun t => B x - t • v
  have hrc : Continuous r := continuous_const.sub (continuous_id.smul continuous_const)
  have hV0 : r ⁻¹' V ∈ nhds (0 : ℝ) :=
    (hV.preimage hrc).mem_nhds (by
      change B x - (0 : ℝ) • v ∈ V
      simpa only [zero_smul, sub_zero] using hxV)
  obtain ⟨d, hd, hdV⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
    (nhdsWithin_le_nhds hV0)
  let A : ℝ →ᴬ[ℝ] V3 := ContinuousAffineMap.const ℝ ℝ (B x) -
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (d • v)).toContinuousAffineMap
  have hA (t : ℝ) : A t = B x - (d * t) • v := by
    change B x - t • (d • v) = B x - (d * t) • v
    rw [smul_smul, mul_comm]
  have hAV : MapsTo A (Icc (0 : ℝ) 1) V := by
    intro t ht
    rw [hA]
    exact hdV ⟨mul_nonneg hd.le ht.1, mul_le_of_le_one_right hd.le ht.2⟩
  have hheight (t : ℝ) : ell (A t) = -(d * t) := by
    rw [hA]
    simpa only [neg_smul, ← sub_eq_add_neg, hzero, zero_sub]
      using hadd (B x) (-(d * t))
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  have hreverse (i : ι) : B.symm.trans (e i) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hcompat i)
  have hPL := polyhedralPLInCharts_of_compatible_chart_inverse e hL.cover B hreverse
    K hK ((K.affineOnFaces_affine A).finitePiecewiseAffineOn hK)
  have hPL' : PolyhedralPLInCharts e (B.symm ∘ A) (Icc (0 : ℝ) 1) := by
    rw [← hKs]
    exact hPL (fun _ ht => (hAV (hKs.subset ht)).1)
  refine ⟨B.symm ∘ A, hPL', ?_, fun _ ht => (hAV ht).2, ?_⟩
  · change B.symm (A 0) = x
    rw [hA, mul_zero, zero_smul, sub_zero, B.left_inv hxB]
  · intro t ht
    change B.symm (A t) ∈ L ↔ t = 0
    rw [hhalf _ (B.map_target (hAV ht).1), B.right_inv (hAV ht).1, hheight]
    constructor
    · intro h
      have hdt : d * t ≤ 0 := neg_nonneg.mp h
      exact le_antisymm (by nlinarith) ht.1
    · intro h
      rw [h, mul_zero, neg_zero]

end PoincareConjecture.M76
