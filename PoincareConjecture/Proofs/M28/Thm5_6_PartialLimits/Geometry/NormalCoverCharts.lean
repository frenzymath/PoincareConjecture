import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.SourceCharts.Coefficients












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, ℝ → RiemannianMetric n (M k)} {p : ∀ k, M k}
    {T' T : ℝ} {r R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover (g k) (p k)
      T' T (r j) (R j) (ρ j) (a j) (b j) (N j))

private noncomputable def partialStageUnitBallMap (k j : ℕ) (hjk : j ≤ k) (l : ℕ)
    (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) : M k :=
  (cover k j hjk).unitBallMap ⟨l % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ x




noncomputable def partialUnitBallMap (k i : ℕ)
    (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) : M k :=
  partialStageUnitBallMap cover k (min (Nat.unpair i).1 k) (min_le_right _ _)
    (Nat.unpair i).2 x



theorem partialUnitBallMap_of_le (k i : ℕ) (hik : (Nat.unpair i).1 ≤ k) :
    partialUnitBallMap cover k i =
      (cover k (Nat.unpair i).1 hik).unitBallMap
        ⟨(Nat.unpair i).2 % (N (Nat.unpair i).1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ := by
  funext x
  simp only [partialUnitBallMap, min_eq_left hik]
  rfl



theorem partialUnitBallMap_pair (k j : ℕ) (hjk : j ≤ k) (l : Fin (N j + 1)) :
    partialUnitBallMap cover k (Nat.pair j l) = (cover k j hjk).unitBallMap l := by
  funext x
  simp only [partialUnitBallMap, Nat.unpair_pair, min_eq_left hjk]
  simp only [partialStageUnitBallMap, Nat.mod_eq_of_lt l.isLt]



theorem partialUnitBallMap_zero (k : ℕ) :
    partialUnitBallMap cover k 0 ⟨0, by simp⟩ = p k := by
  change partialUnitBallMap cover k (Nat.pair 0 (0 : Fin (N 0 + 1))) ⟨0, by simp⟩ = _
  rw [partialUnitBallMap_pair cover k 0 (Nat.zero_le k) (0 : Fin (N 0 + 1))]
  simp only [NormalChartCover.unitBallMap, smul_zero]
  exact ((cover k 0 (Nat.zero_le k)).map_zero 0).trans
    (cover k 0 (Nat.zero_le k)).centre_zero



theorem partialUnitBallMap_isLocalDiffeomorph
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (k i : ℕ) :
    letI : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n))
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (partialUnitBallMap cover k i) :=
  (cover k _ (min_le_right _ _)).unitBallMap_isLocalDiffeomorph (hρ _) (hρR _) _



theorem partialUnitBallMap_isOpenEmbedding
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (k i : ℕ) :
    Topology.IsOpenEmbedding (partialUnitBallMap cover k i) :=
  (cover k _ (min_le_right _ _)).unitBallMap_isOpenEmbedding (hρ _) (hρR _) _



theorem metric_ball_eq_of_riemannian_edist
    (hdist : ∀ k (x y : M k), edist x y = (g k 0).edist x y)
    (k : ℕ) (x : M k) (s : ℝ) : ball x s = (g k 0).ball x s := by
  ext y
  change dist y x < s ↔ (g k 0).edist x y < ENNReal.ofReal s
  rw [← hdist, edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg, dist_comm]



theorem partialUnitBallMap_distance_bounds
    (hdist : ∀ k (x y : M k), edist x y = (g k 0).edist x y)
    (hρ : ∀ j, 0 < ρ j) (ha : ∀ j, 0 < a j) (i : ℕ) :
    ∃ L : ℝ≥0, ∃ c : ℝ, 0 < c ∧
      (∀ k, LipschitzWith L (partialUnitBallMap cover k i)) ∧
      ∀ k x y, c * dist x y ≤
        dist (partialUnitBallMap cover k i x) (partialUnitBallMap cover k i y) := by
  classical
  let S := Finset.range ((Nat.unpair i).1 + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  let upper := fun j => Real.sqrt (b j) * (ρ j / 2)
  let lower := fun j => Real.sqrt (a j) * (ρ j / 2)
  have hupper (j : ℕ) : 0 ≤ upper j := mul_nonneg (Real.sqrt_nonneg _) (half_pos (hρ j)).le
  have hlower (j : ℕ) : 0 < lower j := mul_pos (Real.sqrt_pos.2 (ha j)) (half_pos (hρ j))
  let B := S.sup' hS upper
  have hB : 0 ≤ B := (hupper 0).trans (Finset.le_sup' upper (by simp [S]))
  let c := S.inf' hS lower
  have hc : 0 < c := (Finset.lt_inf'_iff hS).2 (fun j _ => hlower j)
  have hreal (k : ℕ) (x y : M k) : ((g k 0).edist x y).toReal = dist x y := by
    rw [← hdist, ← dist_edist]
  refine ⟨⟨B, hB⟩, c, hc, ?_, ?_⟩
  · intro k
    have hj : min (Nat.unpair i).1 k ∈ S :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_left _ _))
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := ((cover k _ (min_le_right _ _)).unitBallMap_distances
      (hρ _) ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ x y).2
    rw [hreal] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Finset.le_sup' upper hj) dist_nonneg)
  · intro k x y
    have hj : min (Nat.unpair i).1 k ∈ S :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_left _ _))
    have h := ((cover k _ (min_le_right _ _)).unitBallMap_distances
      (hρ _) ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩ x y).1
    rw [hreal] at h
    exact (mul_le_mul_of_nonneg_right (Finset.inf'_le lower hj) dist_nonneg).trans h




theorem partialUnitBallMap_eventual_radius
    (hdist : ∀ k (x y : M k), edist x y = (g k 0).edist x y)
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j)
    {A : ℝ} (hmargin : ∀ j, r j + ρ j / 2 < A)
    (i : ℕ) (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ B : ℝ, B < A ∧ ∀ᶠ k in atTop,
      dist (p k) (partialUnitBallMap cover k i x) ≤ B := by
  let j := (Nat.unpair i).1
  refine ⟨r j + ρ j / 2, hmargin j, ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk
  rw [partialUnitBallMap_of_le cover k i hk]
  let l : Fin (N j + 1) :=
    ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  let C := cover k j hk
  have hcentre : dist (p k) (C.centre l) < r j := by
    have hmem := C.centre_mem l
    rw [← metric_ball_eq_of_riemannian_edist hdist] at hmem
    simpa only [Metric.mem_ball, dist_comm] using hmem
  have hxR : (ρ j / 2) • (x : EuclideanSpace ℝ (Fin n)) ∈ ball 0 (R j) :=
    (ball_subset_ball (hρR j)) (NormalChartCover.rescale_mem_half_ball (hρ j) x)
  have hradial : dist (C.centre l) (C.unitBallMap l x) =
      ‖(ρ j / 2) • (x : EuclideanSpace ℝ (Fin n))‖ := by
    rw [dist_edist, hdist]
    rw [NormalChartCover.unitBallMap, C.radial_distance l _ hxR,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  exact (dist_triangle _ (C.centre l) _).trans
    (add_le_add hcentre.le (hradial.le.trans
      (mem_ball_zero_iff.mp (NormalChartCover.rescale_mem_half_ball (hρ j) x)).le))



theorem partialUnitBallMap_compact_cover
    (hdist : ∀ k (x y : M k), edist x y = (g k 0).edist x y)
    (hρ : ∀ j, 0 < ρ j) {A : ℝ}
    (hcofinal : ∀ B : ℝ, B < A → ∃ j, B < r j) :
    ∀ B : ℝ, 0 < B → B < A → ∃ S : Finset ℕ,
      ∃ K : ℕ → Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
        (∀ i ∈ S, IsCompact (K i)) ∧
          ∀ᶠ k in atTop, ball (p k) B ⊆ ⋃ i ∈ S, partialUnitBallMap cover k i '' K i := by
  classical
  intro B _hB hBA
  obtain ⟨j, hj⟩ := hcofinal B hBA
  let K : Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {x | ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have himage : Subtype.val '' K = closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact mem_closedBall_zero_iff.mpr hy
      · intro hx
        refine ⟨⟨x, mem_ball_zero_iff.mpr
          ((mem_closedBall_zero_iff.mp hx).trans_lt (by norm_num))⟩,
          mem_closedBall_zero_iff.mp hx, rfl⟩
    rw [himage]
    exact isCompact_closedBall _ _
  let S := Finset.univ.image (fun l : Fin (N j + 1) => Nat.pair j l)
  refine ⟨S, fun _ => K, fun _ _ => hK, ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk
  intro y hy
  have hy' : y ∈ (g k 0).ball (p k) (r j) := by
    rw [← metric_ball_eq_of_riemannian_edist hdist]
    exact ball_subset_ball hj.le hy
  obtain ⟨l, x, hx, hxy⟩ := mem_iUnion.mp ((cover k j hk).unitBallMap_cover (hρ j) hy')
  refine mem_iUnion₂.mpr ⟨Nat.pair j l, Finset.mem_image.mpr
    ⟨l, Finset.mem_univ _, rfl⟩, x, hx, ?_⟩
  rw [partialUnitBallMap_pair cover k j hk l]
  exact hxy

end PoincareConjecture.M28
