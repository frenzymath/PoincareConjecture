import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedPolygon

set_option autoImplicit false

open Set Function

namespace Poincare.Manifold.Schoenflies.Plane

variable {n : ℕ} [NeZero n]

theorem polygonIntegerIndex_add (j k : ℤ) :
    polygonIntegerIndex n (j + k) = polygonIntegerIndex n j + polygonIntegerIndex n k := by
  apply Fin.ext
  change ((j + k) % (n : ℤ)).toNat =
    (((j % (n : ℤ)).toNat + (k % (n : ℤ)).toNat) % n)
  apply Int.ofNat_inj.mp
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp only [Int.natCast_emod, Int.natCast_add,
    Int.toNat_of_nonneg (Int.emod_nonneg (j + k) hn),
    Int.toNat_of_nonneg (Int.emod_nonneg j hn),
    Int.toNat_of_nonneg (Int.emod_nonneg k hn)]
  exact Int.add_emod j k n

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def polygonCyclicShift (p : Polygon E n) (a : Fin n) : Polygon E n := ⟨fun i => p (i + a)⟩

theorem IsSimplePolygon.cyclicShift {p : Polygon E n} (hp : IsSimplePolygon p) (a : Fin n) :
    IsSimplePolygon (polygonCyclicShift p a) := by
  have hedge (i : Fin n) : (polygonCyclicShift p a).edgeSet ℝ i = p.edgeSet ℝ (i + a) := by
    simp only [polygon_edgeSet_eq_segment, polygonCyclicShift, finRotate_apply]
    congr 2
    abel
  refine ⟨hp.three_le, hp.vertices_injective.comp (add_left_injective a), ?_⟩
  intro i j hij x hx
  rw [hedge, hedge] at hx
  have hends := hp.edges_inter (i + a) (j + a) (fun h => hij (add_right_cancel h)) hx
  simpa only [polygonCyclicShift, finRotate_apply, add_assoc, add_comm, add_left_comm] using hends

theorem roundedPolygonParameter_cyclicShift (ρ : ℝ → ℝ) (p : Polygon E n) (a : Fin n)
    (t : ℝ) :
    roundedPolygonParameter ρ (polygonCyclicShift p a) t =
      roundedPolygonParameter ρ p (t + (a.val : ℝ)) := by
  have hfloor : ⌊t + (a.val : ℝ) + 1 / 2⌋ = ⌊t + 1 / 2⌋ + (a.val : ℤ) := by
    rw [show t + (a.val : ℝ) + 1 / 2 = (t + 1 / 2) + (a.val : ℤ) by push_cast; ring,
      Int.floor_add_intCast]
  simp only [roundedPolygonParameter, roundedVertexPath, polygonCyclicShift, hfloor]
  rw [show ⌊t + 1 / 2⌋ + (a.val : ℤ) - 1 = (⌊t + 1 / 2⌋ - 1) + (a.val : ℤ) by omega,
    show ⌊t + 1 / 2⌋ + (a.val : ℤ) + 1 = (⌊t + 1 / 2⌋ + 1) + (a.val : ℤ) by omega]
  simp only [polygonIntegerIndex_add, polygonIntegerIndex_nat, Int.cast_add, Int.cast_natCast]
  congr 1
  ring

theorem range_roundedPolygonParameter_cyclicShift (ρ : ℝ → ℝ) (p : Polygon E n) (a : Fin n) :
    range (roundedPolygonParameter ρ (polygonCyclicShift p a)) =
      range (roundedPolygonParameter ρ p) := by
  have hfun : roundedPolygonParameter ρ (polygonCyclicShift p a) =
      roundedPolygonParameter ρ p ∘ (fun t => t + (a.val : ℝ)) :=
    funext (roundedPolygonParameter_cyclicShift ρ p a)
  rw [hfun]
  exact (add_right_surjective (a.val : ℝ)).range_comp _

theorem polygonCyclicShift_last_midpoint {m : ℕ} (p : Polygon E (m + 4)) (k : Fin (m + 4))
    (hmid : p k = midpoint ℝ (p ((finRotate (m + 4)).symm k)) (p (finRotate (m + 4) k))) :
    polygonCyclicShift p (finRotate (m + 4) k) (Fin.last (m + 3)) =
      midpoint ℝ
        (polygonCyclicShift p (finRotate (m + 4) k) (Fin.last (m + 2)).castSucc)
        (polygonCyclicShift p (finRotate (m + 4) k) 0) := by
  have hlastone : (Fin.last (m + 3) : Fin (m + 4)) + 1 = 0 := by
    simpa only [finRotate_apply] using (finRotate_last (n := m + 3))
  have hlast : (Fin.last (m + 3) : Fin (m + 4)) + finRotate (m + 4) k = k := by
    rw [finRotate_apply]
    calc
      Fin.last (m + 3) + (k + 1) = (Fin.last (m + 3) + 1) + k := by abel
      _ = k := by rw [hlastone, zero_add]
  have hprev : (Fin.last (m + 2)).castSucc + finRotate (m + 4) k =
      (finRotate (m + 4)).symm k := by
    apply (finRotate (m + 4)).injective
    rw [Equiv.apply_symm_apply]
    have hr : finRotate (m + 4) (Fin.last (m + 2)).castSucc = Fin.last (m + 3) :=
      finRotate_of_lt (Fin.last (m + 2)).isLt
    calc
      finRotate (m + 4) ((Fin.last (m + 2)).castSucc + finRotate (m + 4) k) =
          finRotate (m + 4) (Fin.last (m + 2)).castSucc + finRotate (m + 4) k := by
        simp only [finRotate_apply]
        abel
      _ = k := by rw [hr, hlast]
  simpa only [polygonCyclicShift, hlast, hprev, zero_add] using hmid

end Poincare.Manifold.Schoenflies.Plane
