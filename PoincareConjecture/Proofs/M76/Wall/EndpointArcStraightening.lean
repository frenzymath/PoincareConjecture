import PoincareConjecture.Proofs.M76.Wall.InitialArcCoordinates
import PoincareConjecture.Proofs.M76.Wall.Mathlib.NegativeRayStraightening
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)






theorem PLDomain.exists_straightened_endpoint_segment
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X}
    (hL : PLDomain e L) {f : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hi : InjOn f (Icc (0 : ℝ) 1)) (hfront : f 0 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ L) :
    ∃ (G : OpenPartialHomeomorph X V3) (A : V3 →L[ℝ] ℝ) (v : V3),
      f 0 ∈ G.source ∧ G (f 0) = 0 ∧ A v = 1 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ A (G y)) ∧
      (∀ y ∈ G.source, y ∈ frontier L ↔ A (G y) = 0) ∧
      ∃ m : ℝ, m < 0 ∧ ∃ δ ∈ Ioo (0 : ℝ) 1,
        MapsTo f (Icc 0 δ) G.source ∧
        ∀ t ∈ Icc 0 δ, G (f t) = (t * m) • v := by
  obtain ⟨ell, v, B, hv, hxB, hzero, hcompat, hhalf⟩ := hL.halfspace _ hfront
  obtain ⟨C, hCs, hCzero, hCcompat, hCvalue⟩ :=
    exists_centered_compatible_halfspace_chart e B hcompat (f 0) ell hzero
  have hxC : f 0 ∈ C.source := hCs.symm.subset hxB
  obtain ⟨d, _, δ, hδ, hfC, hformula⟩ :=
    hf.exists_initial_chart_vector hi C hCcompat hxC hCzero
  let A : V3 →L[ℝ] ℝ := ell.contLinear
  have hAvalue (y : X) : A (C y) = ell (B y) := hCvalue y
  have hhalfC (y : X) (hy : y ∈ C.source) : y ∈ L ↔ 0 ≤ A (C y) := by
    rw [hAvalue]
    exact hhalf y (hCs.subset hy)
  have hd : A d < 0 := by
    have hneg : A (C (f δ)) < 0 :=
      lt_of_not_ge (fun h => hproper δ hδ ((hhalfC _ (hfC ⟨hδ.1.le, le_rfl⟩)).mpr h))
    rw [hformula δ ⟨hδ.1.le, le_rfl⟩, map_smul, smul_eq_mul] at hneg
    nlinarith [hδ.1]
  obtain ⟨Q, hQPL, hQheight, hQzero, hQray⟩ :=
    A.exists_negative_ray_straightening v d hv hd
  let G := C.trans Q.toOpenPartialHomeomorph
  have hGs : G.source = C.source := by
    change C.source ∩ C ⁻¹' (univ : Set V3) = C.source
    rw [preimage_univ, inter_univ]
  have hGheight (y : X) : A (G y) = A (C y) := hQheight (C y)
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    norm_num at hval
  refine ⟨G, A, v, hGs.symm.subset hxC, ?_, hv, ?_, ?_, ?_,
    A d, hd, δ, hδ, fun _ ht => hGs.symm.subset (hfC ht), ?_⟩
  · change Q (C (f 0)) = 0
    rw [hCzero, hQzero 0 (map_zero A)]
  · intro i
    simpa only [G, ← OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans (hCcompat i) hQPL
  · intro y hy
    rw [hGheight]
    exact hhalfC y (hGs.subset hy)
  · intro y hy
    rw [hGheight, hAvalue]
    exact ((B.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff
      (hCs.subset (hGs.subset hy))).symm
  · intro t ht
    change Q (C (f t)) = (t * A d) • v
    rw [hformula t ht]
    exact hQray t ht.1

end PoincareConjecture.M76
