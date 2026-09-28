import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.BufferedAtlas
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Frames.Segmented












set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff Bundle NNReal

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
private theorem shiChart_matrix_norm_le_of_pairing
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {K : Set M} (hKs : K ⊆ c.source) {L : ℝ} (hL : 1 ≤ L)
    (hmetric : ∀ z ∈ c '' K, ∀ v : E,
      ‖v‖ ≤ L * Real.sqrt (shiChartMetric g c z v v))
    {y : M} (hy : y ∈ K) (P : E →L[ℝ] E)
    (hP : ∀ v w, g.inner y (shiChartField c (P v) y)
      (shiChartField c (P w) y) = inner ℝ v w) :
    ‖P‖ ≤ L := by
  apply P.opNorm_le_bound (zero_le_one.trans hL)
  intro v
  have hdiag : shiChartMetric g c (c y) (P v) (P v) = ‖v‖ ^ 2 := by
    rw [shiChartMetric_at_source hc hi (hKs hy), hP, real_inner_self_eq_norm_sq]
  calc
    ‖P v‖ ≤ L * Real.sqrt (shiChartMetric g c (c y) (P v) (P v)) :=
      hmetric (c y) (mem_image_of_mem _ hy) (P v)
    _ = L * ‖v‖ := by rw [hdiag, Real.sqrt_sq (norm_nonneg v)]

set_option backward.isDefEq.respectTransparency false in
theorem shiChart_isometric_frame_norm_le
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {K : Set M} (hKs : K ⊆ c.source) {L : ℝ} (hL : 1 ≤ L)
    (hmetric : ∀ z ∈ c '' K, ∀ v : E,
      ‖v‖ ≤ L * Real.sqrt (shiChartMetric g c z v v))
    {y : M} (hy : y ∈ K) (J : E →L[ℝ] TangentSpace (𝓡 n) y)
    (hJ : ∀ v w, g.inner y (J v) (J w) = inner ℝ v w) :
    ‖(mvfderiv (𝓡 n) c y).comp J‖ ≤ L := by
  apply shiChart_matrix_norm_le_of_pairing hc hi hKs hL hmetric hy
  intro v w
  have hfield (a : E) :
      shiChartField c (((mvfderiv (𝓡 n) c y).comp J) a) y = J a :=
    (shiChart_mfderiv_isInvertible hc hi (hKs hy)).inverse_apply_self (J a)
  rw [hfield, hfield]
  exact hJ v w

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_shi_bounded_segmented_parallel_frames [T2Space M]
    (D : LeviCivitaData g) {N : ℕ} (hN : 0 < N)
    (s : ℕ → ℝ) (hs : ∀ j < N, s j < s (j + 1))
    (c : Fin N → OpenPartialHomeomorph M E) (K : Fin N → Set M)
    (hc : ∀ j, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c j) (c j).source)
    (hi : ∀ j, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c j).symm (c j).target)
    (hKs : ∀ j, K j ⊆ (c j).source)
    {L B R : ℝ} (hL : 1 ≤ L) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hmetric : ∀ j z, z ∈ (c j) '' K j → ∀ v : E,
      ‖v‖ ≤ L * Real.sqrt (shiChartMetric g (c j) z v v))
    (hGamma : ∀ j z, z ∈ (c j) '' K j → ‖shiChartChristoffel D (c j) z‖ ≤ B)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : ∀ j : Fin N, MapsTo γ (Icc (s j.val) (s (j.val + 1))) (K j))
    (hspeed : ∀ j : Fin N, ∀ t ∈ Icc (s j.val) (s (j.val + 1)), pathSpeed g γ t ≤ R)
    (hshort : ∀ j : Fin N,
      s (j.val + 1) - s j.val ≤ 1 / (2 * (B * L * R) + 1))
    (Jend : E →L[ℝ] TangentSpace (𝓡 n) (γ (s N)))
    (hJend : ∀ v w, g.inner (γ (s N)) (Jend v) (Jend w) = inner ℝ v w) :
    ∃ P : Fin N → ℝ → E →L[ℝ] E,
      (∀ j, ContDiffOn ℝ 1 (P j) (Icc (s j.val) (s (j.val + 1)))) ∧
      (∀ j t, t ∈ Icc (s j.val) (s (j.val + 1)) →
        HasDerivWithinAt (P j)
          (-((shiChartChristoffel D (c j) (c j (γ t))
            (deriv ((c j) ∘ γ) t)).comp (P j t)))
          (Icc (s j.val) (s (j.val + 1))) t) ∧
      (∀ (j : ℕ) (hj : j + 1 < N) (v : E),
        shiChartField (c ⟨j, (Nat.lt_succ_self j).trans hj⟩)
            (P ⟨j, (Nat.lt_succ_self j).trans hj⟩ (s (j + 1)) v) (γ (s (j + 1))) =
          shiChartField (c ⟨j + 1, hj⟩)
            (P ⟨j + 1, hj⟩ (s (j + 1)) v) (γ (s (j + 1)))) ∧
      (∀ j : Fin N, j.val + 1 = N → ∀ v,
        shiChartField (c j) (P j (s N) v) (γ (s N)) = Jend v) ∧
      (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) → ∀ v w,
        g.inner (γ t) (shiChartField (c j) (P j t v) (γ t))
          (shiChartField (c j) (P j t w) (γ t)) = inner ℝ v w) ∧
      (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) → ‖P j t‖ ≤ L) ∧
      (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) →
        ‖deriv ((c j) ∘ γ) t‖ ≤ L * R) ∧
      (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) →
        ‖shiChartChristoffel D (c j) (c j (γ t)) (deriv ((c j) ∘ γ) t)‖ ≤
          B * L * R) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hT (j : Fin N) (t : ℝ) (ht : t ∈ Icc (s j.val) (s (j.val + 1))) :
      ‖deriv ((c j) ∘ γ) t‖ ≤ L * R := by
    have hy : γ t ∈ K j := hinside j ht
    calc
      _ ≤ L * Real.sqrt (shiChartMetric g (c j) (c j (γ t))
          (deriv ((c j) ∘ γ) t) (deriv ((c j) ∘ γ) t)) :=
        hmetric j _ (mem_image_of_mem _ hy) _
      _ = L * pathSpeed g γ t := by
        rw [(shiChart_coordinate_velocity_metric (hc j) (hi j) hγ (hKs j hy)).2]
      _ ≤ L * R := mul_le_mul_of_nonneg_left (hspeed j t ht) hL0
  have hA (j : Fin N) (t : ℝ) (ht : t ∈ Icc (s j.val) (s (j.val + 1))) :
      ‖shiChartChristoffel D (c j) (c j (γ t)) (deriv ((c j) ∘ γ) t)‖ ≤
        B * L * R := by
    calc
      _ ≤ ‖shiChartChristoffel D (c j) (c j (γ t))‖ * ‖deriv ((c j) ∘ γ) t‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * ‖deriv ((c j) ∘ γ) t‖ :=
        mul_le_mul_of_nonneg_right
          (hGamma j _ (mem_image_of_mem _ (hinside j ht))) (norm_nonneg _)
      _ ≤ B * (L * R) := mul_le_mul_of_nonneg_left (hT j t ht) hB
      _ = B * L * R := by ring
  let κ : ℝ≥0 := ⟨B * L * R, mul_nonneg (mul_nonneg hB hL0) hR⟩
  obtain ⟨P, hP, hPd, hjoin, hend, hpair⟩ :=
    exists_shi_segmented_parallel_frames D hN s hs c hc hi hγ
      (fun j t ht => hKs j (hinside j ht)) (fun _ => κ) hA hshort Jend
  have hpair' (j : Fin N) (t : ℝ) (ht : t ∈ Icc (s j.val) (s (j.val + 1)))
      (v w : E) :
      g.inner (γ t) (shiChartField (c j) (P j t v) (γ t))
        (shiChartField (c j) (P j t w) (γ t)) = inner ℝ v w :=
    (hpair j t ht v w).trans (hJend v w)
  refine ⟨P, hP, hPd, hjoin, hend, hpair', ?_, hT, hA⟩
  intro j t ht
  exact shiChart_matrix_norm_le_of_pairing (hc j) (hi j) (hKs j) hL (hmetric j)
    (hinside j ht) (P j t) (hpair' j t ht)

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_shi_uniform_bounded_parallel_frames [T2Space M]
    (D : LeviCivitaData g) {C : Set M} {m : ℕ}
    (c : Fin m → OpenPartialHomeomorph M E) (K : Fin m → Set M)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hKs : ∀ i, K i ⊆ (c i).source)
    {r L B R : ℝ} (hr : 0 < r) (hL : 1 ≤ L) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hbuffer : ∀ y ∈ C, ∃ i, g.ball y r ⊆ interior (K i))
    (hmetric : ∀ i z, z ∈ (c i) '' K i → ∀ v : E,
      ‖v‖ ≤ L * Real.sqrt (shiChartMetric g (c i) z v v))
    (hGamma : ∀ i z, z ∈ (c i) '' K i → ‖shiChartChristoffel D (c i) z‖ ≤ B) :
    ∃ N : ℕ, 0 < N ∧ R / (N : ℝ) < r ∧
      1 / (N : ℝ) ≤ 1 / (2 * (B * L * R) + 1) ∧
      let s : ℕ → ℝ := fun k => (k : ℝ) / N
      ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ →
        MapsTo γ (Icc 0 1) C → (∀ t ∈ Icc 0 1, pathSpeed g γ t ≤ R) →
        ∀ Jend : E →L[ℝ] TangentSpace (𝓡 n) (γ 1),
        (∀ v w, g.inner (γ 1) (Jend v) (Jend w) = inner ℝ v w) →
        ∃ (label : Fin N → Fin m) (P : Fin N → ℝ → E →L[ℝ] E),
          (∀ j, MapsTo γ (Icc (s j.val) (s (j.val + 1))) (interior (K (label j)))) ∧
          (∀ j, ContDiffOn ℝ 1 (P j) (Icc (s j.val) (s (j.val + 1)))) ∧
          (∀ j t, t ∈ Icc (s j.val) (s (j.val + 1)) →
            HasDerivWithinAt (P j)
              (-((shiChartChristoffel D (c (label j)) (c (label j) (γ t))
                (deriv ((c (label j)) ∘ γ) t)).comp (P j t)))
              (Icc (s j.val) (s (j.val + 1))) t) ∧
          (∀ (j : ℕ) (hj : j + 1 < N) (v : E),
            shiChartField (c (label ⟨j, (Nat.lt_succ_self j).trans hj⟩))
                (P ⟨j, (Nat.lt_succ_self j).trans hj⟩ (s (j + 1)) v) (γ (s (j + 1))) =
              shiChartField (c (label ⟨j + 1, hj⟩))
                (P ⟨j + 1, hj⟩ (s (j + 1)) v) (γ (s (j + 1)))) ∧
          (∀ j : Fin N, j.val + 1 = N → ∀ v,
            shiChartField (c (label j)) (P j 1 v) (γ 1) = Jend v) ∧
          (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) → ∀ v w,
            g.inner (γ t) (shiChartField (c (label j)) (P j t v) (γ t))
              (shiChartField (c (label j)) (P j t w) (γ t)) = inner ℝ v w) ∧
          (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) → ‖P j t‖ ≤ L) ∧
          (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) →
            ‖deriv ((c (label j)) ∘ γ) t‖ ≤ L * R) ∧
          (∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) →
            ‖shiChartChristoffel D (c (label j)) (c (label j) (γ t))
              (deriv ((c (label j)) ∘ γ) t)‖ ≤ B * L * R) := by
  obtain ⟨N, hN, hmesh, hshort, hpaths⟩ :=
    exists_shi_common_mesh D c K hc hi hKs hr hL hB hR hbuffer hmetric hGamma
  let s : ℕ → ℝ := fun k => (k : ℝ) / N
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs (j : ℕ) (_hj : j < N) : s j < s (j + 1) := by
    simp only [s, Nat.cast_add, Nat.cast_one]
    exact div_lt_div_of_pos_right (by linarith) hNreal
  have hsN : s N = 1 := by
    dsimp only [s]
    exact div_self (ne_of_gt hNreal)
  have hlen (j : Fin N) : s (j.val + 1) - s j.val = 1 / (N : ℝ) := by
    simp only [s, Nat.cast_add, Nat.cast_one]
    ring
  refine ⟨N, hN, hmesh, hshort, ?_⟩
  dsimp only
  intro γ hγ hγC hspeed Jend hJend
  obtain ⟨label, hlabel⟩ := hpaths γ hγ hγC hspeed
  have hmap (j : Fin N) :
      MapsTo γ (Icc (s j.val) (s (j.val + 1))) (interior (K (label j))) := by
    simpa only [s, Nat.cast_add, Nat.cast_one] using (hlabel j).1
  have hT (j : Fin N) (t : ℝ) (ht : t ∈ Icc (s j.val) (s (j.val + 1))) :
      ‖deriv ((c (label j)) ∘ γ) t‖ ≤ L * R := by
    apply (hlabel j).2.1 t
    simpa only [s, Nat.cast_add, Nat.cast_one] using ht
  have hA (j : Fin N) (t : ℝ) (ht : t ∈ Icc (s j.val) (s (j.val + 1))) :
      ‖shiChartChristoffel D (c (label j)) (c (label j) (γ t))
        (deriv ((c (label j)) ∘ γ) t)‖ ≤ B * L * R := by
    apply (hlabel j).2.2 t
    simpa only [s, Nat.cast_add, Nat.cast_one] using ht
  let κ : ℝ≥0 := ⟨B * L * R, mul_nonneg (mul_nonneg hB (zero_le_one.trans hL)) hR⟩
  have hstep (j : Fin N) : s (j.val + 1) - s j.val ≤ 1 / (2 * (κ : ℝ) + 1) := by
    rw [hlen]
    exact hshort
  have hinside (j : Fin N) :
      MapsTo γ (Icc (s j.val) (s (j.val + 1))) (c (label j)).source :=
    fun t ht => hKs (label j) (interior_subset (hmap j ht))
  obtain ⟨P, hP, hPd, hjoin, hend, hpair⟩ :=
    exists_shi_segmented_parallel_frames D hN s hs (fun j => c (label j))
      (fun j => hc (label j)) (fun j => hi (label j)) hγ hinside
      (fun _ => κ) hA hstep Jend
  have hJend' (v w : E) :
      g.inner (γ (s N)) (Jend v) (Jend w) = inner ℝ v w :=
    (congrArg (fun t : ℝ => g.inner (γ t) (Jend v) (Jend w)) hsN).trans (hJend v w)
  have hpair' (j : Fin N) (t : ℝ) (ht : t ∈ Icc (s j.val) (s (j.val + 1)))
      (v w : E) :
      g.inner (γ t) (shiChartField (c (label j)) (P j t v) (γ t))
        (shiChartField (c (label j)) (P j t w) (γ t)) = inner ℝ v w :=
    (hpair j t ht v w).trans (hJend' v w)
  refine ⟨label, P, hmap, hP, hPd, hjoin, ?_, hpair', ?_, hT, hA⟩
  · intro j hj v
    have htime := congrArg (fun t : ℝ =>
      (shiChartField (c (label j)) (P j t v) (γ t) : E)) hsN.symm
    simpa only using! htime.trans (hend j hj v)
  · intro j t ht
    exact shiChart_matrix_norm_le_of_pairing (hc (label j)) (hi (label j))
      (hKs (label j)) hL (hmetric (label j)) (interior_subset (hmap j ht))
      (P j t) (hpair' j t ht)

end PoincareConjecture.RicciFlowAnalysis
