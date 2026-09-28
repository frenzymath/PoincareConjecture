import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneBoundaryPairChart
import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierCoordinateQuadrants
import PoincareConjecture.Proofs.M76.Mathlib.ConvexConeIncidence
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes










set_option autoImplicit false

open Set Metric Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V" => ((ℝ × ℝ) × ℝ)

private theorem cone_frontier_sector {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {C S : Set E}
    (hC : IsCompact C) (hcv : Convex ℝ C) (h0 : (0 : E) ∈ interior C)
    (hS0 : (0 : E) ∈ S)
    (hscale : ∀ (t : ℝ), 0 < t → ∀ x : E, t • x ∈ S ↔ x ∈ S)
    (hne : (frontier C ∩ S).Nonempty) :
    convexJoin ℝ {0} (frontier C ∩ S) = C ∩ S := by
  have hsub : convexJoin ℝ {(0 : E)} (frontier C ∩ S) ⊆ C :=
    convexJoin_subset (singleton_subset_iff.mpr (interior_subset h0))
      (inter_subset_left.trans hC.isClosed.frontier_subset) hcv
  ext x
  constructor
  · intro hx
    refine ⟨hsub hx, ?_⟩
    obtain ⟨y, hy, t, ht, rfl⟩ := (mem_convexJoin_zero_iff _ x).mp hx
    by_cases ht0 : t = 0
    · simpa only [ht0, zero_smul] using hS0
    · exact (hscale t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) y).mpr hy.2
  · intro hx
    by_cases hx0 : x = 0
    · obtain ⟨y, hy⟩ := hne
      exact (mem_convexJoin_zero_iff _ x).mpr
        ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
    · obtain ⟨y, hy, t, ht, hxy⟩ := hC.exists_frontier_pos_smul hcv h0 hx.1 hx0
      exact (mem_convexJoin_zero_iff _ x).mpr
        ⟨y, ⟨hy, (hscale t ht.1 y).mp (hxy ▸ hx.2)⟩, t, ⟨ht.1.le, ht.2⟩, hxy⟩





theorem exists_standard_boundary_pair_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C S w : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hKC : K.space = C) (h0 : (0 : E) ∈ interior C)
    (A : E →ₗ[ℝ] ℝ)
    (hneg : ∃ x ∈ interior C, A x < 0)
    (hpos : ∃ x ∈ interior C, 0 < A x)
    {a b : E} (hab : a ≠ b)
    (ha : a ∈ frontier C) (hb : b ∈ frontier C)
    (ha0 : A a = 0) (hb0 : A b = 0)
    (hw : IsFinitePLBallPair ℝ w {a, b})
    (hproper : w \ {a, b} ⊆
      (frontier C ∩ {x | 0 ≤ A x}) \ (frontier C ∩ {x | A x = 0}))
    (hsection : S ∩ C = convexJoin ℝ {0} w) :
    ∃ H : OpenPartialHomeomorph E V,
      H.source = interior C ∧ H.target = interior (box 1) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧ H 0 = 0 ∧
      (∀ x ∈ H.source, 0 ≤ A x ↔ 0 ≤ (H x).1.1) ∧
      ∀ x ∈ H.source, x ∈ S ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0 := by
  let p := frontier C ∩ {x | 0 ≤ A x}
  let n := frontier C ∩ {x | A x ≤ 0}
  let q := frontier C ∩ {x | A x = 0}
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ (ℝ × ℝ) + 1 := by
    simpa [Module.finrank_prod] using hdim
  have hp : IsFinitePLBallPair (ℝ × ℝ) p q :=
    K.isFinitePLBallPair_convex_frontier_affine_cap hK hC hcv hKC A.toAffineMap
      hneg ⟨0, h0, A.map_zero⟩ hdim'
  have hn : IsFinitePLBallPair (ℝ × ℝ) n q := by
    have hn' : ∃ x ∈ interior C, (-A) x < 0 := by
      obtain ⟨x, hx, hxA⟩ := hpos
      exact ⟨x, hx, neg_neg_of_pos hxA⟩
    simpa only [LinearMap.coe_toAffineMap, LinearMap.neg_apply, neg_nonneg,
      neg_eq_zero] using K.isFinitePLBallPair_convex_frontier_affine_cap
        hK hC hcv hKC (-A).toAffineMap hn' ⟨0, h0, (-A).map_zero⟩ hdim'
  have hpn : p ∪ n = frontier C := by
    ext x
    change ((x ∈ frontier C ∧ 0 ≤ A x) ∨ (x ∈ frontier C ∧ A x ≤ 0)) ↔ _
    exact ⟨fun hx => hx.elim And.left And.left,
      fun hx => (le_total 0 (A x)).elim (fun h => Or.inl ⟨hx, h⟩)
        (fun h => Or.inr ⟨hx, h⟩)⟩
  have hpi : p ∩ n = q := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, le_antisymm hx.2.2 hx.1.2⟩,
      fun hx => ⟨⟨hx.1, hx.2.ge⟩, hx.1, hx.2.le⟩⟩
  have hbox := box_ballPair (by norm_num : (0 : ℝ) < 1)
  have hbcv : Convex ℝ (box 1) := by
    rw [box_eq_closedBall]
    exact convex_closedBall (0 : V) 1
  have hb0' := zero_mem_interior_box (by norm_num : (0 : ℝ) < 1)
  have hboxcopy := hbox
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hboxcopy
  let L : V →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let P := frontier (box 1) ∩ {x : V | 0 ≤ x.1.1}
  let N := frontier (box 1) ∩ {x : V | x.1.1 ≤ 0}
  let Q := frontier (box 1) ∩ {x : V | x.1.1 = 0}
  let W := frontier (box 1) ∩ {x : V | 0 ≤ x.1.1 ∧ x.2 = 0}
  let c : V := ((0, -1), 0)
  let d : V := ((0, 1), 0)
  have hcd : c ≠ d := by
    intro h
    have hh := congrArg (fun x : V => x.1.2) h
    norm_num [c, d] at hh
  have hc : c ∈ frontier (box 1) := by
    rw [box_eq_closedBall, frontier_closedBall _ one_ne_zero]
    norm_num [c, mem_sphere_zero_iff_norm, Prod.norm_def]
  have hd : d ∈ frontier (box 1) := by
    rw [box_eq_closedBall, frontier_closedBall _ one_ne_zero]
    norm_num [d, mem_sphere_zero_iff_norm, Prod.norm_def]
  have hbn : ∃ x ∈ interior (box 1), L x < 0 := by
    refine ⟨((-1 / 2, 0), 0), ?_, by norm_num [L]⟩
    rw [box_eq_closedBall, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    norm_num [mem_ball_zero_iff, Prod.norm_def]
  have hbp : ∃ x ∈ interior (box 1), (-L) x < 0 := by
    refine ⟨((1 / 2, 0), 0), ?_, by norm_num [L]⟩
    rw [box_eq_closedBall, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    norm_num [mem_ball_zero_iff, Prod.norm_def]
  have hP : IsFinitePLBallPair (ℝ × ℝ) P Q :=
    J.isFinitePLBallPair_convex_frontier_affine_cap hJ hbox.isCompact hbcv hJs
      L.toAffineMap hbn ⟨0, hb0', L.map_zero⟩ (by simp [Module.finrank_prod])
  have hN : IsFinitePLBallPair (ℝ × ℝ) N Q := by
    simpa [N, Q, L] using J.isFinitePLBallPair_convex_frontier_affine_cap
        hJ hbox.isCompact hbcv hJs (-L).toAffineMap hbp
        ⟨0, hb0', (-L).map_zero⟩ (by simp [Module.finrank_prod])
  have hPN : P ∪ N = frontier (box 1) := by
    ext x
    change ((x ∈ frontier (box 1) ∧ 0 ≤ x.1.1) ∨
      (x ∈ frontier (box 1) ∧ x.1.1 ≤ 0)) ↔ _
    exact ⟨fun hx => hx.elim And.left And.left,
      fun hx => (le_total 0 x.1.1).elim (fun h => Or.inl ⟨hx, h⟩)
        (fun h => Or.inr ⟨hx, h⟩)⟩
  have hPI : P ∩ N = Q := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, le_antisymm hx.2.2 hx.1.2⟩,
      fun hx => ⟨⟨hx.1, hx.2.ge⟩, hx.1, hx.2.le⟩⟩
  have hW : IsFinitePLBallPair ℝ W {c, d} := by
    have hh := (J.isFinitePLBallPair_coordinate_frontier_quadrants hJ hbox.isCompact
      hbcv hJs hb0' (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1) hc hd).2.1 false
    simpa [W, c, d, and_comm] using hh
  have haxis := hbcv.frontier_inter_coordinate_planes_eq_poles hb0'
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1) hc hd
  have hProper : W \ {c, d} ⊆ P \ Q := by
    intro x hx
    refine ⟨⟨hx.1.1, hx.1.2.1⟩, ?_⟩
    intro hxQ
    exact hx.2 (haxis ▸ ⟨hx.1.1, hxQ.2, hx.1.2.2⟩)
  obtain ⟨H, hHs, hHt, hHPL, hiHPL, hH0, hcap, harc⟩ :=
    exists_conical_boundary_pair_chart (by simpa [Module.finrank_prod] using hdim)
      hC hbox.isCompact hcv hbcv h0 hb0' hp hn hP hN hpn hpi hPN hPI hw hW
      hab hcd ⟨ha, ha0⟩ ⟨hb, hb0⟩ ⟨hc, rfl⟩ ⟨hd, rfl⟩ hproper hProper
  have hconeSource : convexJoin ℝ {(0 : E)} p = C ∩ {x | 0 ≤ A x} := by
    apply cone_frontier_sector hC hcv h0 (by simp)
    · intro t ht x
      change 0 ≤ A (t • x) ↔ 0 ≤ A x
      rw [map_smul, smul_eq_mul, mul_nonneg_iff_of_pos_left ht]
    · exact ⟨a, ha, by change 0 ≤ A a; rw [ha0]⟩
  have hconeCap : convexJoin ℝ {(0 : V)} P = box 1 ∩ {x : V | 0 ≤ x.1.1} := by
    apply cone_frontier_sector hbox.isCompact hbcv hb0' (by norm_num)
    · intro t ht x
      change 0 ≤ t * x.1.1 ↔ 0 ≤ x.1.1
      exact mul_nonneg_iff_of_pos_left ht
    · exact ⟨c, hc, by change (0 : ℝ) ≤ 0; exact le_rfl⟩
  have hconeArc : convexJoin ℝ {(0 : V)} W =
      box 1 ∩ {x : V | 0 ≤ x.1.1 ∧ x.2 = 0} := by
    apply cone_frontier_sector hbox.isCompact hbcv hb0' (by norm_num)
    · intro t ht x
      change (0 ≤ t * x.1.1 ∧ t * x.2 = 0) ↔ (0 ≤ x.1.1 ∧ x.2 = 0)
      simp only [mul_nonneg_iff_of_pos_left ht, mul_eq_zero, ht.ne', false_or]
    · exact ⟨c, hc, by change (0 : ℝ) ≤ 0 ∧ (0 : ℝ) = 0; exact ⟨le_rfl, rfl⟩⟩
  refine ⟨H, hHs, hHt, hHPL, hiHPL, hH0, ?_, ?_⟩
  · intro x hx
    have hxC : x ∈ C := interior_subset (hHs ▸ hx)
    have hyD : H x ∈ box 1 := interior_subset (hHt ▸ H.map_source hx)
    simpa only [hconeSource, hconeCap, mem_inter_iff, mem_ofPred_eq,
      hxC, hyD, true_and] using hcap x hx
  · intro x hx
    have hxC : x ∈ C := interior_subset (hHs ▸ hx)
    have hyD : H x ∈ box 1 := interior_subset (hHt ▸ H.map_source hx)
    simpa only [← hsection, hconeArc, mem_inter_iff, mem_ofPred_eq,
      hxC, hyD, and_true, true_and] using harc x hx

end PoincareConjecture.M76.HamiltonIndexOne
