





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Distance












open Set Filter Topology
open scoped Topology

noncomputable section

namespace Poincare.GromovHausdorff

universe u

private structure PointedApproximationMaps
    (X Y : FiniteDiameterBasedMetricSpace.{u})
    (R : PointedGHRealization X Y) (epsilon : ℝ) where
  forward : X.carrier → Y.carrier
  backward : Y.carrier → X.carrier
  forward_base : forward X.base = Y.base
  backward_base : backward Y.base = X.base
  forward_close : ∀ x, dist (R.left x) (R.right (forward x)) < epsilon
  backward_close : ∀ y, dist (R.left (backward y)) (R.right y) < epsilon

private noncomputable def pointedApproximationMapsOfRealization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hR : pointedHausdorffDist R < epsilon) :
    PointedApproximationMaps X Y R epsilon := by
  classical
  have hforward : ∀ x : X.carrier,
      ∃ y : Y.carrier, dist (R.left x) (R.right y) < epsilon :=
    fun x => exists_right_point_lt_of_pointedHausdorffDist_lt R hR x
  have hbackward : ∀ y : Y.carrier,
      ∃ x : X.carrier, dist (R.left x) (R.right y) < epsilon :=
    fun y => exists_left_point_lt_of_pointedHausdorffDist_lt R hR y
  choose f hf using hforward
  choose g hg using hbackward
  let f' : X.carrier → Y.carrier :=
    fun x => if x = X.base then Y.base else f x
  let g' : Y.carrier → X.carrier :=
    fun y => if y = Y.base then X.base else g y
  refine
    { forward := f'
      backward := g'
      forward_base := by simp [f']
      backward_base := by simp [g']
      forward_close := ?_
      backward_close := ?_ }
  · intro x
    by_cases hx : x = X.base
    · subst x
      rw [show f' X.base = Y.base by simp [f']]
      rw [R.left_base, R.right_base, dist_self]
      exact hepsilon
    · simpa [f', hx] using hf x
  · intro y
    by_cases hy : y = Y.base
    · subst y
      rw [show g' Y.base = X.base by simp [g']]
      rw [R.left_base, R.right_base, dist_self]
      exact hepsilon
    · simpa [g', hy] using hg y






theorem exists_basedIsometry_of_pointedGHDistance_eq_zero
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (hzero : pointedGHDistance X Y = 0) :
    ∃ e : X.carrier ≃ᵢ Y.carrier, e X.base = Y.base := by
  let epsilon : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepsilon (n : ℕ) : 0 < epsilon n := by
    dsimp [epsilon]
    positivity
  have hexists (n : ℕ) :
      ∃ R : PointedGHRealization X Y,
        pointedHausdorffDist R < epsilon n :=
    (pointedGHDistance_eq_zero_iff_forall_pos_exists_realization_lt X Y).mp
      hzero (epsilon n) (hepsilon n)
  let R : ∀ n, PointedGHRealization X Y :=
    fun n => Classical.choose (hexists n)
  have hR (n : ℕ) : pointedHausdorffDist (R n) < epsilon n :=
    Classical.choose_spec (hexists n)
  let A : ∀ n, PointedApproximationMaps X Y (R n) (epsilon n) :=
    fun n => pointedApproximationMapsOfRealization (R n) (hepsilon n) (hR n)
  let q : ℕ → (X.carrier → Y.carrier) × (Y.carrier → X.carrier) :=
    fun n => ((A n).forward, (A n).backward)
  obtain ⟨p, -, hp⟩ :=
    (isCompact_univ :
      IsCompact (Set.univ :
        Set ((X.carrier → Y.carrier) × (Y.carrier → X.carrier)))).exists_mapClusterPt
      (f := atTop) (u := q) (by simp)
  obtain ⟨U, hUtop, hU⟩ := mapClusterPt_iff_ultrafilter.mp hp
  have hforward_tendsto (x : X.carrier) :
      Tendsto (fun n => (A n).forward x) (U : Filter ℕ) (𝓝 (p.1 x)) := by
    have hcontinuous :
        Continuous (fun z : (X.carrier → Y.carrier) × (Y.carrier → X.carrier) =>
          z.1 x) :=
      (continuous_apply x).comp continuous_fst
    simpa [q, Function.comp_def] using (hcontinuous.tendsto p).comp hU
  have hbackward_tendsto (y : Y.carrier) :
      Tendsto (fun n => (A n).backward y) (U : Filter ℕ) (𝓝 (p.2 y)) := by
    have hcontinuous :
        Continuous (fun z : (X.carrier → Y.carrier) × (Y.carrier → X.carrier) =>
          z.2 y) :=
      (continuous_apply y).comp continuous_snd
    simpa [q, Function.comp_def] using (hcontinuous.tendsto p).comp hU
  have hepsilon_tendsto :
      Tendsto epsilon (U : Filter ℕ) (𝓝 0) := by
    apply Filter.Tendsto.mono_left
      (show Tendsto epsilon atTop (𝓝 0) by
        simpa [epsilon] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    exact hUtop
  have htwo_epsilon_tendsto :
      Tendsto (fun n => 2 * epsilon n) (U : Filter ℕ) (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds.mul hepsilon_tendsto) :
        Tendsto (fun n => (2 : ℝ) * epsilon n) (U : Filter ℕ)
          (𝓝 ((2 : ℝ) * 0)))
  have hforward_distortion (n : ℕ) (x x' : X.carrier) :
      dist (dist ((A n).forward x) ((A n).forward x')) (dist x x') <
        2 * epsilon n := by
    calc
      dist (dist ((A n).forward x) ((A n).forward x')) (dist x x') =
          dist
            (dist ((R n).right ((A n).forward x))
              ((R n).right ((A n).forward x')))
            (dist ((R n).left x) ((R n).left x')) := by
              rw [(R n).right_isometry.dist_eq, (R n).left_isometry.dist_eq]
      _ ≤
          dist ((R n).right ((A n).forward x)) ((R n).left x) +
            dist ((R n).right ((A n).forward x')) ((R n).left x') :=
        dist_dist_dist_le _ _ _ _
      _ < epsilon n + epsilon n := by
        exact add_lt_add
          (by simpa [dist_comm] using (A n).forward_close x)
          (by simpa [dist_comm] using (A n).forward_close x')
      _ = 2 * epsilon n := by ring
  have hforward_dist_tendsto (x x' : X.carrier) :
      Tendsto (fun n => dist ((A n).forward x) ((A n).forward x'))
        (U : Filter ℕ) (𝓝 (dist x x')) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · intro n
      exact le_of_lt (hforward_distortion n x x')
    · exact htwo_epsilon_tendsto
  have hforward_dist (x x' : X.carrier) :
      dist (p.1 x) (p.1 x') = dist x x' := by
    exact tendsto_nhds_unique
      ((hforward_tendsto x).dist (hforward_tendsto x'))
      (hforward_dist_tendsto x x')
  have hforward_isometry : Isometry p.1 :=
    Isometry.of_dist_eq hforward_dist
  have hforward_lipschitz (n : ℕ) (x x' : X.carrier) :
      dist ((A n).forward x) ((A n).forward x') <
        dist x x' + 2 * epsilon n := by
    have hdist := hforward_distortion n x x'
    rw [Real.dist_eq] at hdist
    have hupper := (abs_lt.mp hdist).2
    linarith
  have hcomposition_close (n : ℕ) (y : Y.carrier) :
      dist ((A n).forward ((A n).backward y)) y < 2 * epsilon n := by
    calc
      dist ((A n).forward ((A n).backward y)) y =
          dist ((R n).right ((A n).forward ((A n).backward y)))
            ((R n).right y) := by
              rw [(R n).right_isometry.dist_eq]
      _ ≤
          dist ((R n).right ((A n).forward ((A n).backward y)))
              ((R n).left ((A n).backward y)) +
            dist ((R n).left ((A n).backward y)) ((R n).right y) :=
        dist_triangle _ _ _
      _ < epsilon n + epsilon n := by
        exact add_lt_add
          (by simpa [dist_comm] using
            (A n).forward_close ((A n).backward y))
          ((A n).backward_close y)
      _ = 2 * epsilon n := by ring
  have hcomposition_tendsto (y : Y.carrier) :
      Tendsto (fun n => (A n).forward ((A n).backward y))
        (U : Filter ℕ) (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · intro n
      exact le_of_lt (hcomposition_close n y)
    · exact htwo_epsilon_tendsto
  have hmoving_close (y : Y.carrier) :
      Tendsto
        (fun n =>
          dist ((A n).forward ((A n).backward y))
            ((A n).forward (p.2 y)))
        (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · intro n
      exact le_of_lt (hforward_lipschitz n ((A n).backward y) (p.2 y))
    · have hbackward_dist :
          Tendsto (fun n => dist ((A n).backward y) (p.2 y))
            (U : Filter ℕ) (𝓝 0) :=
        tendsto_iff_dist_tendsto_zero.mp (hbackward_tendsto y)
      simpa using hbackward_dist.add htwo_epsilon_tendsto
  have hsurjective (y : Y.carrier) : p.1 (p.2 y) = y := by
    have hvariable :
        Tendsto (fun n => (A n).forward ((A n).backward y))
          (U : Filter ℕ) (𝓝 (p.1 (p.2 y))) := by
      apply tendsto_of_tendsto_of_dist (hforward_tendsto (p.2 y))
      simpa [dist_comm] using hmoving_close y
    exact tendsto_nhds_unique hvariable (hcomposition_tendsto y)
  have hbase : p.1 X.base = Y.base := by
    have hconstant :
        Tendsto (fun _ : ℕ => Y.base) (U : Filter ℕ) (𝓝 Y.base) :=
      tendsto_const_nhds
    have hseq :
        Tendsto (fun n => (A n).forward X.base)
          (U : Filter ℕ) (𝓝 Y.base) := by
      simpa only [(A _).forward_base] using hconstant
    exact tendsto_nhds_unique (hforward_tendsto X.base) hseq
  let e : X.carrier ≃ Y.carrier :=
    Equiv.ofBijective p.1
      ⟨hforward_isometry.injective, fun y => ⟨p.2 y, hsurjective y⟩⟩
  let ei : X.carrier ≃ᵢ Y.carrier :=
    { toEquiv := e
      isometry_toFun := by
        change Isometry p.1
        exact hforward_isometry }
  refine ⟨ei, ?_⟩
  change p.1 X.base = Y.base
  exact hbase




theorem pointedGHDistance_eq_zero_iff_basedIsometry
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier] :
    pointedGHDistance X Y = 0 ↔
      ∃ e : X.carrier ≃ᵢ Y.carrier, e X.base = Y.base := by
  constructor
  · exact exists_basedIsometry_of_pointedGHDistance_eq_zero
  · rintro ⟨e, hbase⟩
    exact pointedGHDistance_eq_zero_of_basedIsometry X Y e hbase




theorem exists_basedIsometry_of_common_pointedGH_limit
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y Z : FiniteDiameterBasedMetricSpace.{u})
    [CompactSpace Y.carrier] [CompactSpace Z.carrier]
    (hY : PointedGHConverges X Y)
    (hZ : PointedGHConverges X Z) :
    ∃ e : Y.carrier ≃ᵢ Z.carrier, e Y.base = Z.base := by
  apply exists_basedIsometry_of_pointedGHDistance_eq_zero
  exact pointedGHDistance_eq_zero_of_common_pointedGH_limit X Y Z hY hZ

end Poincare.GromovHausdorff

end

