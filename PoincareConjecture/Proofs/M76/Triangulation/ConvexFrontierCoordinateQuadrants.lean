import PoincareConjecture.Proofs.M76.Mathlib.ConvexTwoPlaneFrontierData
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut
import PoincareConjecture.Proofs.M76.Triangulation.AffineConvexSphereCapDisks

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

theorem isFinitePLBallPair_coordinate_frontier_quadrants
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hKC : K.space = C) (hzero : (0 : (ℝ × ℝ) × ℝ) ∈ interior C)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (haC : ((0, a), 0) ∈ frontier C) (hbC : ((0, b), 0) ∈ frontier C) :
    (∀ i : Bool, IsFinitePLBallPair ℝ
      (frontier C ∩ {x | x.1.1 = 0 ∧ (if i then x.2 ≤ 0 else 0 ≤ x.2)})
      {((0, a), 0), ((0, b), 0)}) ∧
    (∀ i : Bool, IsFinitePLBallPair ℝ
      (frontier C ∩ {x | x.2 = 0 ∧ (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1)})
      {((0, a), 0), ((0, b), 0)}) ∧
    ∀ i j : Bool, IsFinitePLBallPair (ℝ × ℝ)
      (frontier C ∩ {x | (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1) ∧
        (if j then x.2 ≤ 0 else 0 ≤ x.2)})
      ((frontier C ∩ {x | x.1.1 = 0 ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)}) ∪
        (frontier C ∩ {x | x.2 = 0 ∧ (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1)})) := by
  let A : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let B : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  let R := frontier C ∩ {x | A x = 0}
  let T := frontier C ∩ {x | B x = 0}
  let marks : Set ((ℝ × ℝ) × ℝ) := {((0, a), 0), ((0, b), 0)}
  have hab : (((0, a), 0) : (ℝ × ℝ) × ℝ) ≠ ((0, b), 0) := by
    intro heq
    have hab' : a = b := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) heq
    exact (ha.trans hb).ne hab'
  obtain ⟨p₀, q₀, hp₀, hq₀, hBp₀, hAp₀, hBq₀, hAq₀⟩ :=
    hC.exists_frontier_and_interior_linear_sign hcv hzero B (-A)
      (v := ((-1, 0), 0)) rfl (by norm_num [A])
  obtain ⟨p₁, q₁, hp₁, hq₁, hBp₁, hAp₁, hBq₁, hAq₁⟩ :=
    hC.exists_frontier_and_interior_linear_sign hcv hzero B A
      (v := ((1, 0), 0)) rfl (by norm_num [A])
  obtain ⟨p₂, q₂, hp₂, hq₂, hAp₂, hBp₂, hAq₂, hBq₂⟩ :=
    hC.exists_frontier_and_interior_linear_sign hcv hzero A (-B)
      (v := ((0, 0), -1)) rfl (by norm_num [B])
  obtain ⟨p₃, q₃, hp₃, hq₃, hAp₃, hBp₃, hAq₃, hBq₃⟩ :=
    hC.exists_frontier_and_interior_linear_sign hcv hzero A B
      (v := ((0, 0), 1)) rfl (by norm_num [B])
  have hRneg : ∃ x ∈ R, B x < 0 :=
    ⟨p₂, ⟨hp₂, hAp₂⟩, neg_pos.mp hBp₂⟩
  have hRpos : ∃ x ∈ R, 0 < B x := ⟨p₃, ⟨hp₃, hAp₃⟩, hBp₃⟩
  have hTneg : ∃ x ∈ T, A x < 0 :=
    ⟨p₀, ⟨hp₀, hBp₀⟩, neg_pos.mp hAp₀⟩
  have hTpos : ∃ x ∈ T, 0 < A x := ⟨p₁, ⟨hp₁, hBp₁⟩, hAp₁⟩
  have haxis := hcv.frontier_inter_coordinate_planes_eq_poles hzero ha hb haC hbC
  have hRzero : R ∩ {x | B x = 0} = marks := by
    change R ∩ {x | B x = 0} = {((0, a), 0), ((0, b), 0)}
    rw [← haxis]
    ext x
    change ((x ∈ frontier C ∧ x.1.1 = 0) ∧ x.2 = 0) ↔
      (x ∈ frontier C ∧ x.1.1 = 0 ∧ x.2 = 0)
    exact and_assoc
  have hTzero : T ∩ {x | A x = 0} = marks := by
    change T ∩ {x | A x = 0} = {((0, a), 0), ((0, b), 0)}
    rw [← haxis]
    ext x
    change ((x ∈ frontier C ∧ x.2 = 0) ∧ x.1.1 = 0) ↔
      (x ∈ frontier C ∧ x.1.1 = 0 ∧ x.2 = 0)
    exact ⟨fun hx => ⟨hx.1.1, hx.2, hx.1.2⟩,
      fun hx => ⟨⟨hx.1, hx.2.2⟩, hx.2.1⟩⟩
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) =
      Module.finrank ℝ (ℝ × ℝ) + 1 := by simp [Module.finrank_prod]
  have hHpos : IsFinitePLBallPair (ℝ × ℝ) (frontier C ∩ {x | 0 ≤ A x}) R :=
    K.isFinitePLBallPair_convex_frontier_affine_cap hK hC hcv hKC A.toAffineMap
      ⟨q₀, hq₀, neg_pos.mp hAq₀⟩ ⟨0, hzero, A.map_zero⟩ hdim
  have hHneg : IsFinitePLBallPair (ℝ × ℝ) (frontier C ∩ {x | A x ≤ 0}) R := by
    have hcap := K.isFinitePLBallPair_convex_frontier_affine_cap hK hC hcv hKC
      (-A).toAffineMap (F := ℝ × ℝ)
      ⟨q₁, hq₁, neg_neg_of_pos hAq₁⟩ ⟨0, hzero, (-A).map_zero⟩ hdim
    simpa only [R, LinearMap.coe_toAffineMap, LinearMap.neg_apply,
      neg_nonneg, neg_eq_zero] using hcap
  have hZpos : IsFinitePLBallPair (ℝ × ℝ) (frontier C ∩ {x | 0 ≤ B x}) T :=
    K.isFinitePLBallPair_convex_frontier_affine_cap hK hC hcv hKC B.toAffineMap
      ⟨q₂, hq₂, neg_pos.mp hBq₂⟩ ⟨0, hzero, B.map_zero⟩ hdim
  have hRa : ((0, a), 0) ∈ R := (hRzero.symm.subset (by simp [marks])).1
  have hRb : ((0, b), 0) ∈ R := (hRzero.symm.subset (by simp [marks])).1
  obtain ⟨U, V, hU, hV, hUV, _⟩ := hHpos.exists_boundary_arcs hRa hRb hab
  have hRarcs := isFinitePLBallPair_signed_halves_of_arcs hU hV hUV B
    B.continuous_of_finiteDimensional.continuousOn hRzero hRneg hRpos
  have hTa : ((0, a), 0) ∈ T := (hTzero.symm.subset (by simp [marks])).1
  have hTb : ((0, b), 0) ∈ T := (hTzero.symm.subset (by simp [marks])).1
  obtain ⟨U', V', hU', hV', hUV', _⟩ := hZpos.exists_boundary_arcs hTa hTb hab
  have hTarcs := isFinitePLBallPair_signed_halves_of_arcs hU' hV' hUV' A
    A.continuous_of_finiteDimensional.continuousOn hTzero hTneg hTpos
  let H (i : Bool) := frontier C ∩ {x | if i then A x ≤ 0 else 0 ≤ A x}
  let W (i : Bool) := T ∩ {x | if i then A x ≤ 0 else 0 ≤ A x}
  have hH (i : Bool) : IsFinitePLBallPair (ℝ × ℝ) (H i) R := by
    cases i
    · exact hHpos
    · exact hHneg
  have hW (i : Bool) : IsFinitePLBallPair ℝ (W i) marks := by
    cases i
    · exact hTarcs.2
    · exact hTarcs.1
  have hHW (i : Bool) : H i ∩ {x | B x = 0} = W i := by
    ext x
    change ((x ∈ frontier C ∧ (if i then A x ≤ 0 else 0 ≤ A x)) ∧ B x = 0) ↔
      ((x ∈ frontier C ∧ B x = 0) ∧ (if i then A x ≤ 0 else 0 ≤ A x))
    exact ⟨fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩,
      fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩⟩
  have hcuts (i : Bool) := (hH i).isFinitePLBallPair_signed_halves_of_zero_arc B
    B.continuous_of_finiteDimensional.continuousOn (hW i) hab (hHW i)
    hRzero hRarcs.1 hRarcs.2 hRneg hRpos
  refine ⟨?_, ?_, ?_⟩
  · intro i
    cases i
    · simpa [R, A, B, inter_assoc, ← ofPred_and] using hRarcs.2
    · simpa [R, A, B, inter_assoc, ← ofPred_and] using hRarcs.1
  · intro i
    cases i
    · simpa [T, A, B, inter_assoc, ← ofPred_and] using hTarcs.2
    · simpa [T, A, B, inter_assoc, ← ofPred_and] using hTarcs.1
  · intro i j
    cases j
    · simpa [H, W, R, T, A, B, inter_assoc, ← ofPred_and, union_comm] using (hcuts i).2
    · simpa [H, W, R, T, A, B, inter_assoc, ← ofPred_and] using (hcuts i).1

end Geometry.SimplicialComplex
