





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.Compatible
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.ClosedBall
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Extraction.Packing











open Set Filter Topology Metric
open scoped Topology

noncomputable section

namespace Poincare.GromovHausdorff

universe u

private theorem exists_basedApproximation_toRight
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {epsilon : Real}
    (hepsilon : 0 < epsilon) (hR : pointedHausdorffDist R < epsilon) :
    exists f : X.carrier -> Y.carrier,
      f X.base = Y.base /\
        forall x, dist (R.left x) (R.right (f x)) < epsilon := by
  classical
  have hnear : forall x : X.carrier, exists y : Y.carrier,
      dist (R.left x) (R.right y) < epsilon :=
    fun x => exists_right_point_lt_of_pointedHausdorffDist_lt R hR x
  choose f hf using hnear
  let f' : X.carrier -> Y.carrier :=
    fun x => if x = X.base then Y.base else f x
  refine ⟨f', by simp [f'], ?_⟩
  intro x
  by_cases hx : x = X.base
  · subst x
    rw [show f' X.base = Y.base by simp [f']]
    rw [R.left_base, R.right_base, dist_self]
    exact hepsilon
  · simpa [f', hx] using hf x

private theorem exists_basedApproximation_toLeft
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {epsilon : Real}
    (hepsilon : 0 < epsilon) (hR : pointedHausdorffDist R < epsilon) :
    exists f : Y.carrier -> X.carrier,
      f Y.base = X.base /\
        forall y, dist (R.left (f y)) (R.right y) < epsilon := by
  classical
  have hnear : forall y : Y.carrier, exists x : X.carrier,
      dist (R.left x) (R.right y) < epsilon :=
    fun y => exists_left_point_lt_of_pointedHausdorffDist_lt R hR y
  choose f hf using hnear
  let f' : Y.carrier -> X.carrier :=
    fun y => if y = Y.base then X.base else f y
  refine ⟨f', by simp [f'], ?_⟩
  intro y
  by_cases hy : y = Y.base
  · subst y
    rw [show f' Y.base = X.base by simp [f']]
    rw [R.left_base, R.right_base, dist_self]
    exact hepsilon
  · simpa [f', hy] using hf y





theorem exists_basedIsometricEmbedding_of_pointedGHConverges
    (source target : Nat -> FiniteDiameterBasedMetricSpace.{u})
    (sourceLimit targetLimit : FiniteDiameterBasedMetricSpace.{u})
    [CompactSpace targetLimit.carrier]
    (hsource : PointedGHConverges source sourceLimit)
    (htarget : PointedGHConverges target targetLimit)
    (embedding : forall n, (source n).carrier -> (target n).carrier)
    (embedding_isometry : forall n, Isometry (embedding n))
    (embedding_base : forall n,
      embedding n (source n).base = (target n).base) :
    exists limitEmbedding : sourceLimit.carrier -> targetLimit.carrier,
      Isometry limitEmbedding /\
        limitEmbedding sourceLimit.base = targetLimit.base := by
  let epsilon : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp [epsilon]
    positivity
  have hepsilon_tendsto : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  let sourceError : Nat -> Real := fun n =>
    pointedGHDistance (source n) sourceLimit + epsilon n
  let targetError : Nat -> Real := fun n =>
    pointedGHDistance (target n) targetLimit + epsilon n
  have hsourceError_pos (n : Nat) : 0 < sourceError n := by
    dsimp [sourceError]
    exact add_pos_of_nonneg_of_pos
      (pointedGHDistance_nonneg (source n) sourceLimit) (hepsilon n)
  have htargetError_pos (n : Nat) : 0 < targetError n := by
    dsimp [targetError]
    exact add_pos_of_nonneg_of_pos
      (pointedGHDistance_nonneg (target n) targetLimit) (hepsilon n)
  have hsourceRealization (n : Nat) :
      exists R : PointedGHRealization (source n) sourceLimit,
        pointedHausdorffDist R < sourceError n := by
    simpa [sourceError] using
      exists_pointedGHRealization_lt_add (source n) sourceLimit (hepsilon n)
  have htargetRealization (n : Nat) :
      exists R : PointedGHRealization (target n) targetLimit,
        pointedHausdorffDist R < targetError n := by
    simpa [targetError] using
      exists_pointedGHRealization_lt_add (target n) targetLimit (hepsilon n)
  let sourceRealization : forall n,
      PointedGHRealization (source n) sourceLimit :=
    fun n => Classical.choose (hsourceRealization n)
  let targetRealization : forall n,
      PointedGHRealization (target n) targetLimit :=
    fun n => Classical.choose (htargetRealization n)
  have hsourceRealization_lt (n : Nat) :
      pointedHausdorffDist (sourceRealization n) < sourceError n :=
    Classical.choose_spec (hsourceRealization n)
  have htargetRealization_lt (n : Nat) :
      pointedHausdorffDist (targetRealization n) < targetError n :=
    Classical.choose_spec (htargetRealization n)
  have hsourceApproximation (n : Nat) :
      exists f : sourceLimit.carrier -> (source n).carrier,
        f sourceLimit.base = (source n).base /\
          forall x,
            dist ((sourceRealization n).left (f x))
                ((sourceRealization n).right x) < sourceError n :=
    exists_basedApproximation_toLeft (sourceRealization n)
      (hsourceError_pos n) (hsourceRealization_lt n)
  have htargetApproximation (n : Nat) :
      exists f : (target n).carrier -> targetLimit.carrier,
        f (target n).base = targetLimit.base /\
          forall y,
            dist ((targetRealization n).left y)
                ((targetRealization n).right (f y)) < targetError n :=
    exists_basedApproximation_toRight (targetRealization n)
      (htargetError_pos n) (htargetRealization_lt n)
  choose sourceApproximation hsourceApproximation_base
    hsourceApproximation_close using hsourceApproximation
  choose targetApproximation htargetApproximation_base
    htargetApproximation_close using htargetApproximation
  let approximateEmbedding : Nat -> sourceLimit.carrier -> targetLimit.carrier :=
    fun n x => targetApproximation n
      (embedding n (sourceApproximation n x))
  obtain ⟨limitEmbedding, -, hlimitEmbedding⟩ :=
    (isCompact_univ : IsCompact
      (Set.univ : Set (sourceLimit.carrier -> targetLimit.carrier))).exists_mapClusterPt
      (f := atTop) (u := approximateEmbedding) (by simp)
  obtain ⟨U, hUtop, hU⟩ := mapClusterPt_iff_ultrafilter.mp hlimitEmbedding
  have happroximation_tendsto (x : sourceLimit.carrier) :
      Tendsto (fun n => approximateEmbedding n x) (U : Filter Nat)
        (nhds (limitEmbedding x)) := by
    have hcontinuous : Continuous
        (fun f : sourceLimit.carrier -> targetLimit.carrier => f x) :=
      continuous_apply x
    simpa [Function.comp_def] using
      (hcontinuous.tendsto limitEmbedding).comp hU
  have hsourceError_tendsto : Tendsto sourceError atTop (nhds 0) := by
    simpa [sourceError] using hsource.2.add hepsilon_tendsto
  have htargetError_tendsto : Tendsto targetError atTop (nhds 0) := by
    simpa [targetError] using htarget.2.add hepsilon_tendsto
  have hbound_tendsto : Tendsto
      (fun n => 2 * targetError n + 2 * sourceError n)
      (U : Filter Nat) (nhds 0) := by
    have hsourceU : Tendsto sourceError (U : Filter Nat) (nhds 0) :=
      hsourceError_tendsto.mono_left hUtop
    have htargetU : Tendsto targetError (U : Filter Nat) (nhds 0) :=
      htargetError_tendsto.mono_left hUtop
    simpa using
      ((tendsto_const_nhds.mul htargetU).add
        (tendsto_const_nhds.mul hsourceU) :
          Tendsto (fun n => 2 * targetError n + 2 * sourceError n)
            (U : Filter Nat) (nhds (2 * 0 + 2 * 0)))
  have hsource_distortion (n : Nat) (x x' : sourceLimit.carrier) :
      dist
          (dist (sourceApproximation n x) (sourceApproximation n x'))
          (dist x x') < 2 * sourceError n := by
    calc
      _ = dist
          (dist
            ((sourceRealization n).left (sourceApproximation n x))
            ((sourceRealization n).left (sourceApproximation n x')))
          (dist
            ((sourceRealization n).right x)
            ((sourceRealization n).right x')) := by
              rw [(sourceRealization n).left_isometry.dist_eq,
                (sourceRealization n).right_isometry.dist_eq]
      _ <=
          dist ((sourceRealization n).left (sourceApproximation n x))
              ((sourceRealization n).right x) +
            dist ((sourceRealization n).left (sourceApproximation n x'))
              ((sourceRealization n).right x') :=
        dist_dist_dist_le _ _ _ _
      _ < sourceError n + sourceError n :=
        add_lt_add (hsourceApproximation_close n x)
          (hsourceApproximation_close n x')
      _ = 2 * sourceError n := by ring
  have htarget_distortion (n : Nat) (x x' : sourceLimit.carrier) :
      dist
          (dist (approximateEmbedding n x) (approximateEmbedding n x'))
          (dist
            (embedding n (sourceApproximation n x))
            (embedding n (sourceApproximation n x'))) <
        2 * targetError n := by
    calc
      _ = dist
          (dist
            ((targetRealization n).right
              (targetApproximation n
                (embedding n (sourceApproximation n x))))
            ((targetRealization n).right
              (targetApproximation n
                (embedding n (sourceApproximation n x')))))
          (dist
            ((targetRealization n).left
              (embedding n (sourceApproximation n x)))
            ((targetRealization n).left
              (embedding n (sourceApproximation n x')))) := by
              rw [(targetRealization n).right_isometry.dist_eq,
                (targetRealization n).left_isometry.dist_eq]
      _ <=
          dist
              ((targetRealization n).right
                (targetApproximation n
                  (embedding n (sourceApproximation n x))))
              ((targetRealization n).left
                (embedding n (sourceApproximation n x))) +
            dist
              ((targetRealization n).right
                (targetApproximation n
                  (embedding n (sourceApproximation n x'))))
              ((targetRealization n).left
                (embedding n (sourceApproximation n x'))) :=
        dist_dist_dist_le _ _ _ _
      _ < targetError n + targetError n := by
        have hx := htargetApproximation_close n
          (embedding n (sourceApproximation n x))
        have hx' := htargetApproximation_close n
          (embedding n (sourceApproximation n x'))
        have hx_rev :
            dist
                ((targetRealization n).right
                  (targetApproximation n
                    (embedding n (sourceApproximation n x))))
                ((targetRealization n).left
                  (embedding n (sourceApproximation n x))) < targetError n := by
          simpa only [dist_comm] using hx
        have hx'_rev :
            dist
                ((targetRealization n).right
                  (targetApproximation n
                    (embedding n (sourceApproximation n x'))))
                ((targetRealization n).left
                  (embedding n (sourceApproximation n x'))) < targetError n := by
          simpa only [dist_comm] using hx'
        exact add_lt_add hx_rev hx'_rev
      _ = 2 * targetError n := by ring
  have htotal_distortion (n : Nat) (x x' : sourceLimit.carrier) :
      dist (dist (approximateEmbedding n x) (approximateEmbedding n x'))
          (dist x x') < 2 * targetError n + 2 * sourceError n := by
    have hsource' :
        dist
            (dist
              (embedding n (sourceApproximation n x))
              (embedding n (sourceApproximation n x')))
            (dist x x') < 2 * sourceError n := by
      simpa only [(embedding_isometry n).dist_eq] using
        hsource_distortion n x x'
    exact lt_of_le_of_lt
      (dist_triangle
        (dist (approximateEmbedding n x) (approximateEmbedding n x'))
        (dist
          (embedding n (sourceApproximation n x))
          (embedding n (sourceApproximation n x')))
        (dist x x'))
      (add_lt_add (htarget_distortion n x x') hsource')
  have happroximation_dist_tendsto (x x' : sourceLimit.carrier) :
      Tendsto
        (fun n => dist (approximateEmbedding n x)
          (approximateEmbedding n x'))
        (U : Filter Nat) (nhds (dist x x')) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · intro n
      exact le_of_lt (htotal_distortion n x x')
    · exact hbound_tendsto
  have hlimit_dist (x x' : sourceLimit.carrier) :
      dist (limitEmbedding x) (limitEmbedding x') = dist x x' := by
    exact tendsto_nhds_unique
      ((happroximation_tendsto x).dist (happroximation_tendsto x'))
      (happroximation_dist_tendsto x x')
  have happroximation_base (n : Nat) :
      approximateEmbedding n sourceLimit.base = targetLimit.base := by
    dsimp [approximateEmbedding]
    rw [hsourceApproximation_base n, embedding_base n,
      htargetApproximation_base n]
  have hlimit_base : limitEmbedding sourceLimit.base = targetLimit.base := by
    have hconstant : Tendsto (fun _ : Nat => targetLimit.base)
        (U : Filter Nat) (nhds targetLimit.base) := tendsto_const_nhds
    have hbase_tendsto : Tendsto
        (fun n => approximateEmbedding n sourceLimit.base)
        (U : Filter Nat) (nhds targetLimit.base) := by
      simpa only [happroximation_base] using hconstant
    exact tendsto_nhds_unique
      (happroximation_tendsto sourceLimit.base) hbase_tendsto
  exact ⟨limitEmbedding, Isometry.of_dist_eq hlimit_dist, hlimit_base⟩






theorem exists_basedIsometricEmbedding_with_inner_ball_range
    (source target : Nat -> FiniteDiameterBasedMetricSpace.{u})
    (sourceLimit targetLimit : FiniteDiameterBasedMetricSpace.{u})
    [CompactSpace sourceLimit.carrier] [CompactSpace targetLimit.carrier]
    (hsource : PointedGHConverges source sourceLimit)
    (htarget : PointedGHConverges target targetLimit)
    (embedding : forall n, (source n).carrier -> (target n).carrier)
    (embedding_isometry : forall n, Isometry (embedding n))
    (embedding_base : forall n,
      embedding n (source n).base = (target n).base)
    (radius : Real)
    (embedding_preimage : forall n (y : (target n).carrier),
      dist ((target n).base) y < radius ->
        exists x : (source n).carrier, embedding n x = y) :
    exists limitEmbedding : sourceLimit.carrier -> targetLimit.carrier,
      Isometry limitEmbedding /\
        limitEmbedding sourceLimit.base = targetLimit.base /\
        Metric.ball targetLimit.base radius ⊆ Set.range limitEmbedding := by
  classical
  let epsilon : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp [epsilon]
    positivity
  have hepsilon_tendsto : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  let sourceError : Nat -> Real := fun n =>
    pointedGHDistance (source n) sourceLimit + epsilon n
  let targetError : Nat -> Real := fun n =>
    pointedGHDistance (target n) targetLimit + epsilon n
  have hsourceError_pos (n : Nat) : 0 < sourceError n := by
    dsimp [sourceError]
    exact add_pos_of_nonneg_of_pos
      (pointedGHDistance_nonneg (source n) sourceLimit) (hepsilon n)
  have htargetError_pos (n : Nat) : 0 < targetError n := by
    dsimp [targetError]
    exact add_pos_of_nonneg_of_pos
      (pointedGHDistance_nonneg (target n) targetLimit) (hepsilon n)
  have hsourceRealization (n : Nat) :
      exists R : PointedGHRealization (source n) sourceLimit,
        pointedHausdorffDist R < sourceError n := by
    simpa [sourceError] using
      exists_pointedGHRealization_lt_add (source n) sourceLimit (hepsilon n)
  have htargetRealization (n : Nat) :
      exists R : PointedGHRealization (target n) targetLimit,
        pointedHausdorffDist R < targetError n := by
    simpa [targetError] using
      exists_pointedGHRealization_lt_add (target n) targetLimit (hepsilon n)
  let sourceRealization : forall n,
      PointedGHRealization (source n) sourceLimit :=
    fun n => Classical.choose (hsourceRealization n)
  let targetRealization : forall n,
      PointedGHRealization (target n) targetLimit :=
    fun n => Classical.choose (htargetRealization n)
  have hsourceRealization_lt (n : Nat) :
      pointedHausdorffDist (sourceRealization n) < sourceError n :=
    Classical.choose_spec (hsourceRealization n)
  have htargetRealization_lt (n : Nat) :
      pointedHausdorffDist (targetRealization n) < targetError n :=
    Classical.choose_spec (htargetRealization n)
  have hsourceToStage (n : Nat) :
      exists f : sourceLimit.carrier -> (source n).carrier,
        f sourceLimit.base = (source n).base /\
          forall x,
            dist ((sourceRealization n).left (f x))
                ((sourceRealization n).right x) < sourceError n :=
    exists_basedApproximation_toLeft (sourceRealization n)
      (hsourceError_pos n) (hsourceRealization_lt n)
  have hsourceToLimit (n : Nat) :
      exists f : (source n).carrier -> sourceLimit.carrier,
        f (source n).base = sourceLimit.base /\
          forall x,
            dist ((sourceRealization n).left x)
                ((sourceRealization n).right (f x)) < sourceError n :=
    exists_basedApproximation_toRight (sourceRealization n)
      (hsourceError_pos n) (hsourceRealization_lt n)
  have htargetToLimit (n : Nat) :
      exists f : (target n).carrier -> targetLimit.carrier,
        f (target n).base = targetLimit.base /\
          forall y,
            dist ((targetRealization n).left y)
                ((targetRealization n).right (f y)) < targetError n :=
    exists_basedApproximation_toRight (targetRealization n)
      (htargetError_pos n) (htargetRealization_lt n)
  have htargetToStage (n : Nat) :
      exists f : targetLimit.carrier -> (target n).carrier,
        f targetLimit.base = (target n).base /\
          forall y,
            dist ((targetRealization n).left (f y))
                ((targetRealization n).right y) < targetError n :=
    exists_basedApproximation_toLeft (targetRealization n)
      (htargetError_pos n) (htargetRealization_lt n)
  choose sourceToStage hsourceToStage_base hsourceToStage_close using hsourceToStage
  choose sourceToLimit hsourceToLimit_base hsourceToLimit_close using hsourceToLimit
  choose targetToLimit htargetToLimit_base htargetToLimit_close using htargetToLimit
  choose targetToStage htargetToStage_base htargetToStage_close using htargetToStage
  let approximateEmbedding : Nat -> sourceLimit.carrier -> targetLimit.carrier :=
    fun n x => targetToLimit n (embedding n (sourceToStage n x))
  let stagePreimage : forall n, targetLimit.carrier -> (source n).carrier :=
    fun n y =>
      if h : dist ((target n).base) (targetToStage n y) < radius then
        Classical.choose (embedding_preimage n (targetToStage n y) h)
      else (source n).base
  let approximatePreimage : Nat -> targetLimit.carrier -> sourceLimit.carrier :=
    fun n y => sourceToLimit n (stagePreimage n y)
  let approximatePair : Nat ->
      (sourceLimit.carrier -> targetLimit.carrier) ×
        (targetLimit.carrier -> sourceLimit.carrier) :=
    fun n => (approximateEmbedding n, approximatePreimage n)
  obtain ⟨limitPair, -, hlimitPair⟩ :=
    (isCompact_univ : IsCompact
      (Set.univ : Set
        ((sourceLimit.carrier -> targetLimit.carrier) ×
          (targetLimit.carrier -> sourceLimit.carrier)))).exists_mapClusterPt
      (f := atTop) (u := approximatePair) (by simp)
  obtain ⟨U, hUtop, hU⟩ := mapClusterPt_iff_ultrafilter.mp hlimitPair
  let limitEmbedding : sourceLimit.carrier -> targetLimit.carrier := limitPair.1
  let limitPreimage : targetLimit.carrier -> sourceLimit.carrier := limitPair.2
  have happroximation_tendsto (x : sourceLimit.carrier) :
      Tendsto (fun n => approximateEmbedding n x) (U : Filter Nat)
        (nhds (limitEmbedding x)) := by
    have hcontinuous : Continuous
        (fun p : (sourceLimit.carrier -> targetLimit.carrier) ×
            (targetLimit.carrier -> sourceLimit.carrier) => p.1 x) :=
      (continuous_apply x).comp continuous_fst
    simpa [approximatePair, limitEmbedding, Function.comp_def] using
      (hcontinuous.tendsto limitPair).comp hU
  have hpreimage_tendsto (y : targetLimit.carrier) :
      Tendsto (fun n => approximatePreimage n y) (U : Filter Nat)
        (nhds (limitPreimage y)) := by
    have hcontinuous : Continuous
        (fun p : (sourceLimit.carrier -> targetLimit.carrier) ×
            (targetLimit.carrier -> sourceLimit.carrier) => p.2 y) :=
      (continuous_apply y).comp continuous_snd
    simpa [approximatePair, limitPreimage, Function.comp_def] using
      (hcontinuous.tendsto limitPair).comp hU
  have hsourceError_tendsto : Tendsto sourceError atTop (nhds 0) := by
    simpa [sourceError] using hsource.2.add hepsilon_tendsto
  have htargetError_tendsto : Tendsto targetError atTop (nhds 0) := by
    simpa [targetError] using htarget.2.add hepsilon_tendsto
  have hsourceError_U : Tendsto sourceError (U : Filter Nat) (nhds 0) :=
    hsourceError_tendsto.mono_left hUtop
  have htargetError_U : Tendsto targetError (U : Filter Nat) (nhds 0) :=
    htargetError_tendsto.mono_left hUtop
  have hbound_tendsto : Tendsto
      (fun n => 2 * targetError n + 2 * sourceError n)
      (U : Filter Nat) (nhds 0) := by
    simpa using
      ((tendsto_const_nhds.mul htargetError_U).add
        (tendsto_const_nhds.mul hsourceError_U) :
          Tendsto (fun n => 2 * targetError n + 2 * sourceError n)
            (U : Filter Nat) (nhds (2 * 0 + 2 * 0)))

  have hsource_distortion (n : Nat) (x x' : sourceLimit.carrier) :
      dist
          (dist (sourceToStage n x) (sourceToStage n x'))
          (dist x x') < 2 * sourceError n := by
    calc
      _ = dist
          (dist
            ((sourceRealization n).left (sourceToStage n x))
            ((sourceRealization n).left (sourceToStage n x')))
          (dist
            ((sourceRealization n).right x)
            ((sourceRealization n).right x')) := by
              rw [(sourceRealization n).left_isometry.dist_eq,
                (sourceRealization n).right_isometry.dist_eq]
      _ <=
          dist ((sourceRealization n).left (sourceToStage n x))
              ((sourceRealization n).right x) +
            dist ((sourceRealization n).left (sourceToStage n x'))
              ((sourceRealization n).right x') :=
        dist_dist_dist_le _ _ _ _
      _ < sourceError n + sourceError n :=
        add_lt_add (hsourceToStage_close n x)
          (hsourceToStage_close n x')
      _ = 2 * sourceError n := by ring
  have htarget_distortion (n : Nat) (x x' : sourceLimit.carrier) :
      dist
          (dist (approximateEmbedding n x) (approximateEmbedding n x'))
          (dist
            (embedding n (sourceToStage n x))
            (embedding n (sourceToStage n x'))) <
        2 * targetError n := by
    calc
      _ = dist
          (dist
            ((targetRealization n).right
              (targetToLimit n
                (embedding n (sourceToStage n x))))
            ((targetRealization n).right
              (targetToLimit n
                (embedding n (sourceToStage n x')))))
          (dist
            ((targetRealization n).left
              (embedding n (sourceToStage n x)))
            ((targetRealization n).left
              (embedding n (sourceToStage n x')))) := by
              rw [(targetRealization n).right_isometry.dist_eq,
                (targetRealization n).left_isometry.dist_eq]
      _ <=
          dist
              ((targetRealization n).right
                (targetToLimit n
                  (embedding n (sourceToStage n x))))
              ((targetRealization n).left
                (embedding n (sourceToStage n x))) +
            dist
              ((targetRealization n).right
                (targetToLimit n
                  (embedding n (sourceToStage n x'))))
              ((targetRealization n).left
                (embedding n (sourceToStage n x'))) :=
        dist_dist_dist_le _ _ _ _
      _ < targetError n + targetError n := by
        have hx := htargetToLimit_close n
          (embedding n (sourceToStage n x))
        have hx' := htargetToLimit_close n
          (embedding n (sourceToStage n x'))
        have hx_rev :
            dist
                ((targetRealization n).right
                  (targetToLimit n
                    (embedding n (sourceToStage n x))))
                ((targetRealization n).left
                  (embedding n (sourceToStage n x))) < targetError n := by
          simpa only [dist_comm] using hx
        have hx'_rev :
            dist
                ((targetRealization n).right
                  (targetToLimit n
                    (embedding n (sourceToStage n x'))))
                ((targetRealization n).left
                  (embedding n (sourceToStage n x'))) < targetError n := by
          simpa only [dist_comm] using hx'
        exact add_lt_add hx_rev hx'_rev
      _ = 2 * targetError n := by ring
  have htotal_distortion (n : Nat) (x x' : sourceLimit.carrier) :
      dist (dist (approximateEmbedding n x) (approximateEmbedding n x'))
          (dist x x') < 2 * targetError n + 2 * sourceError n := by
    have hsource' :
        dist
            (dist
              (embedding n (sourceToStage n x))
              (embedding n (sourceToStage n x')))
            (dist x x') < 2 * sourceError n := by
      simpa only [(embedding_isometry n).dist_eq] using
        hsource_distortion n x x'
    exact lt_of_le_of_lt
      (dist_triangle
        (dist (approximateEmbedding n x) (approximateEmbedding n x'))
        (dist
          (embedding n (sourceToStage n x))
          (embedding n (sourceToStage n x')))
        (dist x x'))
      (add_lt_add (htarget_distortion n x x') hsource')
  have htotal_lipschitz (n : Nat) (x x' : sourceLimit.carrier) :
      dist (approximateEmbedding n x) (approximateEmbedding n x') <=
        dist x x' + (2 * targetError n + 2 * sourceError n) := by
    have h := htotal_distortion n x x'
    rw [Real.dist_eq] at h
    have hupper := (abs_lt.mp h).2
    linarith
  have happroximation_dist_tendsto (x x' : sourceLimit.carrier) :
      Tendsto
        (fun n => dist (approximateEmbedding n x)
          (approximateEmbedding n x'))
        (U : Filter Nat) (nhds (dist x x')) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · intro n
      exact le_of_lt (htotal_distortion n x x')
    · exact hbound_tendsto
  have hlimit_dist (x x' : sourceLimit.carrier) :
      dist (limitEmbedding x) (limitEmbedding x') = dist x x' := by
    exact tendsto_nhds_unique
      ((happroximation_tendsto x).dist (happroximation_tendsto x'))
      (happroximation_dist_tendsto x x')
  have happroximation_base (n : Nat) :
      approximateEmbedding n sourceLimit.base = targetLimit.base := by
    dsimp [approximateEmbedding]
    rw [hsourceToStage_base n, embedding_base n, htargetToLimit_base n]
  have hlimit_base : limitEmbedding sourceLimit.base = targetLimit.base := by
    have hconstant : Tendsto (fun _ : Nat => targetLimit.base)
        (U : Filter Nat) (nhds targetLimit.base) := tendsto_const_nhds
    have hbase_tendsto : Tendsto
        (fun n => approximateEmbedding n sourceLimit.base)
        (U : Filter Nat) (nhds targetLimit.base) := by
      simpa only [happroximation_base] using hconstant
    exact tendsto_nhds_unique
      (happroximation_tendsto sourceLimit.base) hbase_tendsto
  have hlimit_isometry : Isometry limitEmbedding :=
    Isometry.of_dist_eq hlimit_dist
  refine ⟨limitEmbedding, hlimit_isometry, hlimit_base, ?_⟩
  intro y hy
  have hy_radius : dist targetLimit.base y < radius := by
    simpa [dist_comm] using (Metric.mem_ball.mp hy)
  have htargetToStage_radial :
      Tendsto (fun n => dist ((target n).base) (targetToStage n y)) atTop
        (nhds (dist targetLimit.base y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero
      (f := fun n => dist (dist ((target n).base) (targetToStage n y))
        (dist targetLimit.base y))
      (g := fun n => dist ((targetRealization n).left (targetToStage n y))
        ((targetRealization n).right y))
      (t₀ := atTop) (fun _ => dist_nonneg) ?_ ?_
    · intro n
      have hleft :
          dist ((target n).base) (targetToStage n y) =
            dist ((targetRealization n).right targetLimit.base)
              ((targetRealization n).left (targetToStage n y)) := by
        calc
          dist ((target n).base) (targetToStage n y) =
              dist ((targetRealization n).left ((target n).base))
                ((targetRealization n).left (targetToStage n y)) :=
            ((targetRealization n).left_isometry.dist_eq _ _).symm
          _ = _ := by
            rw [(targetRealization n).left_base,
              (targetRealization n).right_base]
      have hright :
          dist targetLimit.base y =
            dist ((targetRealization n).right targetLimit.base)
              ((targetRealization n).right y) :=
        ((targetRealization n).right_isometry.dist_eq _ _).symm
      calc
        dist (dist ((target n).base) (targetToStage n y))
            (dist targetLimit.base y) =
            dist (dist ((targetRealization n).right targetLimit.base)
              ((targetRealization n).left (targetToStage n y)))
              (dist ((targetRealization n).right targetLimit.base)
                ((targetRealization n).right y)) := by
          rw [hleft, hright]
        _ ≤ dist ((targetRealization n).left (targetToStage n y))
              ((targetRealization n).right y) :=
          dist_dist_dist_le_right _ _ _
    · have hdist : Tendsto
          (fun n => dist ((targetRealization n).left (targetToStage n y))
            ((targetRealization n).right y)) atTop (nhds 0) := by
        refine squeeze_zero
          (f := fun n => dist ((targetRealization n).left (targetToStage n y))
            ((targetRealization n).right y))
          (g := targetError) (t₀ := atTop) (fun _ => dist_nonneg) ?_
          htargetError_tendsto
        intro n
        exact le_of_lt (htargetToStage_close n y)
      exact hdist
  have hy_event : ∀ᶠ n in atTop,
      dist ((target n).base) (targetToStage n y) < radius :=
    htargetToStage_radial.eventually_lt_const hy_radius
  have hpreimage_event : ∀ᶠ n in atTop,
      embedding n (stagePreimage n y) = targetToStage n y := by
    filter_upwards [hy_event] with n hn
    dsimp [stagePreimage]
    rw [dif_pos hn]
    exact Classical.choose_spec (embedding_preimage n (targetToStage n y) hn)
  have hpreimage_U : ∀ᶠ n in (U : Filter Nat),
      embedding n (stagePreimage n y) = targetToStage n y :=
    hUtop hpreimage_event
  have hpreimage_pair :
      Tendsto (fun n => approximateEmbedding n (approximatePreimage n y))
        (U : Filter Nat) (nhds (limitEmbedding (limitPreimage y))) := by
    have hdist : Tendsto
        (fun n => dist (approximateEmbedding n (approximatePreimage n y))
          (approximateEmbedding n (limitPreimage y)))
        (U : Filter Nat) (nhds 0) := by
      have hpre : Tendsto (fun n => approximatePreimage n y)
          (U : Filter Nat) (nhds (limitPreimage y)) := hpreimage_tendsto y
      have hdist_z : Tendsto (fun n => dist (approximatePreimage n y)
          (limitPreimage y)) (U : Filter Nat) (nhds 0) := by
        simpa using
          (hpre.dist (tendsto_const_nhds :
            Tendsto (fun _ : Nat => limitPreimage y)
              (U : Filter Nat) (nhds (limitPreimage y))))
      apply squeeze_zero
      · intro n
        exact dist_nonneg
      · intro n
        have h := htotal_lipschitz n (approximatePreimage n y) (limitPreimage y)
        exact h.trans (add_le_add_right (le_refl _) _)
      · have hbound' : Tendsto
            (fun n => dist (approximatePreimage n y) (limitPreimage y) +
              (2 * targetError n + 2 * sourceError n))
            (U : Filter Nat) (nhds 0) := by
          simpa using (hdist_z.add hbound_tendsto)
        exact hbound'
    exact tendsto_of_tendsto_of_dist
      (happroximation_tendsto (limitPreimage y))
      (by simpa [dist_comm] using hdist)
  have hpreimage_pair_y :
      Tendsto (fun n => approximateEmbedding n (approximatePreimage n y))
        (U : Filter Nat) (nhds y) := by
    have hclose : ∀ᶠ n in (U : Filter Nat),
        dist (approximateEmbedding n (approximatePreimage n y)) y <
          2 * targetError n + 2 * sourceError n := by
      filter_upwards [hpreimage_U] with n hn
      have hsource_preimage :
          dist (embedding n (sourceToStage n (approximatePreimage n y)))
              (embedding n (stagePreimage n y)) < 2 * sourceError n := by
        rw [(embedding_isometry n).dist_eq]
        calc
          dist (sourceToStage n (approximatePreimage n y)) (stagePreimage n y) =
              dist ((sourceRealization n).left
                  (sourceToStage n (approximatePreimage n y)))
                ((sourceRealization n).left (stagePreimage n y)) :=
            ((sourceRealization n).left_isometry.dist_eq _ _).symm
          _ ≤ dist ((sourceRealization n).left
                (sourceToStage n (approximatePreimage n y)))
                ((sourceRealization n).right (approximatePreimage n y)) +
              dist ((sourceRealization n).right (approximatePreimage n y))
                ((sourceRealization n).left (stagePreimage n y)) :=
            dist_triangle _ _ _
          _ < sourceError n + sourceError n := by
            exact add_lt_add (hsourceToStage_close n (approximatePreimage n y))
              (by simpa [dist_comm] using
                hsourceToLimit_close n (stagePreimage n y))
          _ = 2 * sourceError n := by ring
      let a : (targetRealization n).ambient.carrier :=
        (targetRealization n).right
          (approximateEmbedding n (approximatePreimage n y))
      let b : (targetRealization n).ambient.carrier :=
        (targetRealization n).left
          (embedding n (sourceToStage n (approximatePreimage n y)))
      let c : (targetRealization n).ambient.carrier :=
        (targetRealization n).left (targetToStage n y)
      let d : (targetRealization n).ambient.carrier :=
        (targetRealization n).right y
      have htarget_left : dist a b < targetError n := by
        dsimp [a, b]
        simpa [approximateEmbedding, dist_comm] using
          htargetToLimit_close n
            (embedding n (sourceToStage n (approximatePreimage n y)))
      have hmiddle : dist b c < 2 * sourceError n := by
        dsimp [b, c]
        rw [← hn, (targetRealization n).left_isometry.dist_eq]
        exact hsource_preimage
      have htarget_right : dist c d < targetError n := by
        dsimp [c, d]
        exact htargetToStage_close n y
      have htriangle : dist a d ≤ (dist a b + dist b c) + dist c d := by
        calc
          dist a d ≤ dist a b + dist b d := dist_triangle _ _ _
          _ ≤ dist a b + (dist b c + dist c d) :=
            add_le_add_right (dist_triangle b c d) (dist a b)
          _ = (dist a b + dist b c) + dist c d := by ring
      calc
        dist (approximateEmbedding n (approximatePreimage n y)) y =
            dist a d := by
          dsimp [a, d]
          exact ((targetRealization n).right_isometry.dist_eq _ _).symm
        _ ≤ (dist a b + dist b c) + dist c d := htriangle
        _ < (targetError n + 2 * sourceError n) + targetError n := by
          exact add_lt_add (add_lt_add htarget_left hmiddle) htarget_right
        _ = targetError n + (2 * sourceError n) + targetError n := by ring
        _ = 2 * targetError n + 2 * sourceError n := by ring
    have hdist_y : Tendsto
        (fun n => dist (approximateEmbedding n (approximatePreimage n y)) y)
        (U : Filter Nat) (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall (fun _ => dist_nonneg)
      · filter_upwards [hclose] with n hn
        simpa [dist_comm] using (le_of_lt hn)
      · exact hbound_tendsto
    exact tendsto_of_tendsto_of_dist tendsto_const_nhds
      (by simpa [dist_comm] using hdist_y)
  exact ⟨limitPreimage y, (tendsto_nhds_unique hpreimage_pair_y hpreimage_pair).symm⟩





theorem exists_basedIsometricEmbedding_between_marked_closedBall_limits_with_inner_ball_range
    (X : Nat -> BasedMetricSpaceBundle.{0})
    [forall k, CompleteSpace (X k).carrier]
    (hpack : forall delta radius, 0 < delta -> exists N : Nat, forall k n,
      n ∈ packingAdmissible (X k).base delta radius -> n <= N)
    (phi : Nat -> Nat) (Y : Nat -> PointedCompactMetricSpace.{0})
    (hconv : forall i, PointedGHConverges
      (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
        |>.toFiniteDiameterBasedMetricSpace)
      (Y i).toFiniteDiameterBasedMetricSpace)
    (i : Nat) :
    exists e : (Y i).carrier -> (Y (i + 1)).carrier,
      Isometry e /\ e (Y i).base = (Y (i + 1)).base /\
        Metric.ball (Y (i + 1)).base (i : Real) ⊆ Set.range e := by
  letI : CompactSpace
      (Y i).toFiniteDiameterBasedMetricSpace.carrier := (Y i).compact
  letI : CompactSpace
      (Y (i + 1)).toFiniteDiameterBasedMetricSpace.carrier := (Y (i + 1)).compact
  have hi : 0 <= (i : Real) := Nat.cast_nonneg i
  have hi_succ : 0 <= ((i + 1 : Nat) : Real) := Nat.cast_nonneg (i + 1)
  have hi_le_succ : (i : Real) <= ((i + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ i
  let inclusion : forall n,
      (uniformPackingBoundedClosedBall X hpack (phi n) i).carrier ->
        (uniformPackingBoundedClosedBall X hpack (phi n) (i + 1)).carrier :=
    fun n => closedBallModelInclusion (X (phi n))
      (i : Real) ((i + 1 : Nat) : Real) hi hi_succ hi_le_succ
  have hinclusion_isometry : forall n, Isometry (inclusion n) := by
    intro n
    exact closedBallModelInclusion_isometry (X (phi n))
      (i : Real) ((i + 1 : Nat) : Real) hi hi_succ hi_le_succ
  have hinclusion_base : forall n,
      inclusion n (uniformPackingBoundedClosedBall X hpack (phi n) i).base =
        (uniformPackingBoundedClosedBall X hpack (phi n) (i + 1)).base := by
    intro n
    exact closedBallModelInclusion_base (X (phi n))
      (i : Real) ((i + 1 : Nat) : Real) hi hi_succ hi_le_succ
  have hinclusion_preimage : forall n
      (y : (uniformPackingBoundedClosedBall X hpack (phi n) (i + 1)).carrier),
      dist ((uniformPackingBoundedClosedBall X hpack (phi n) (i + 1)).base) y <
          (i : Real) ->
        exists x : (uniformPackingBoundedClosedBall X hpack (phi n) i).carrier,
          inclusion n x = y := by
    intro n y hy
    have hy' : dist (X (phi n)).base y.1 < (i : Real) := by
      change dist (X (phi n)).base y.1 < (i : Real) at hy
      exact hy
    let x : (uniformPackingBoundedClosedBall X hpack (phi n) i).carrier :=
      ⟨y.1, by
        simpa [mem_closedBall, dist_comm] using hy'.le⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rfl
  exact exists_basedIsometricEmbedding_with_inner_ball_range
    (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
      |>.toFiniteDiameterBasedMetricSpace)
    (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) (i + 1))
      |>.toFiniteDiameterBasedMetricSpace)
    (Y i).toFiniteDiameterBasedMetricSpace
    (Y (i + 1)).toFiniteDiameterBasedMetricSpace
    (hconv i) (hconv (i + 1)) inclusion hinclusion_isometry hinclusion_base
    (i : Real) hinclusion_preimage





theorem exists_basedIsometricEmbedding_between_marked_closedBall_limits
    (X : Nat -> BasedMetricSpaceBundle.{0})
    [forall k, CompleteSpace (X k).carrier]
    (hpack : forall delta radius, 0 < delta -> exists N : Nat, forall k n,
      n ∈ packingAdmissible (X k).base delta radius -> n <= N)
    (phi : Nat -> Nat) (Y : Nat -> PointedCompactMetricSpace.{0})
    (hconv : forall i, PointedGHConverges
      (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
        |>.toFiniteDiameterBasedMetricSpace)
      (Y i).toFiniteDiameterBasedMetricSpace)
    (i : Nat) :
    exists e : (Y i).carrier -> (Y (i + 1)).carrier,
      Isometry e /\ e (Y i).base = (Y (i + 1)).base := by
  letI : CompactSpace
      (Y (i + 1)).toFiniteDiameterBasedMetricSpace.carrier :=
    (Y (i + 1)).compact
  have hi : 0 <= (i : Real) := Nat.cast_nonneg i
  have hi_succ : 0 <= ((i + 1 : Nat) : Real) := Nat.cast_nonneg (i + 1)
  have hi_le_succ : (i : Real) <= ((i + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ i
  let inclusion : forall n,
      (uniformPackingBoundedClosedBall X hpack (phi n) i).carrier ->
        (uniformPackingBoundedClosedBall X hpack (phi n) (i + 1)).carrier :=
    fun n => closedBallModelInclusion (X (phi n))
      (i : Real) ((i + 1 : Nat) : Real) hi hi_succ hi_le_succ
  have hinclusion_isometry : forall n, Isometry (inclusion n) := by
    intro n
    exact closedBallModelInclusion_isometry (X (phi n))
      (i : Real) ((i + 1 : Nat) : Real) hi hi_succ hi_le_succ
  have hinclusion_base : forall n,
      inclusion n (uniformPackingBoundedClosedBall X hpack (phi n) i).base =
        (uniformPackingBoundedClosedBall X hpack (phi n) (i + 1)).base := by
    intro n
    exact closedBallModelInclusion_base (X (phi n))
      (i : Real) ((i + 1 : Nat) : Real) hi hi_succ hi_le_succ
  exact exists_basedIsometricEmbedding_of_pointedGHConverges
    (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
      |>.toFiniteDiameterBasedMetricSpace)
    (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) (i + 1))
      |>.toFiniteDiameterBasedMetricSpace)
    (Y i).toFiniteDiameterBasedMetricSpace
    (Y (i + 1)).toFiniteDiameterBasedMetricSpace
    (hconv i) (hconv (i + 1)) inclusion hinclusion_isometry hinclusion_base




noncomputable def compatibleSystemOfMarkedClosedBallLimits
    (X : Nat -> BasedMetricSpaceBundle.{0})
    [forall k, CompleteSpace (X k).carrier]
    (hpack : forall delta radius, 0 < delta -> exists N : Nat, forall k n,
      n ∈ packingAdmissible (X k).base delta radius -> n <= N)
    (phi : Nat -> Nat) (Y : Nat -> PointedCompactMetricSpace.{0})
    (hconv : forall i, PointedGHConverges
      (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
        |>.toFiniteDiameterBasedMetricSpace)
      (Y i).toFiniteDiameterBasedMetricSpace) :
    CompatiblePointedCompactSystem.{0} := by
  have hexists (i : Nat) :
      exists e : (Y i).carrier -> (Y (i + 1)).carrier,
        Isometry e /\ e (Y i).base = (Y (i + 1)).base :=
    exists_basedIsometricEmbedding_between_marked_closedBall_limits
      X hpack phi Y hconv i
  choose transition transition_isometry transition_base using hexists
  exact
    { stage := Y
      transition := transition
      transition_isometry := transition_isometry
      transition_base := transition_base }






theorem exists_subseq_compatible_marked_closedBall_limits_of_uniform_packing_bounds
    (X : Nat -> BasedMetricSpaceBundle.{0})
    [forall k, CompleteSpace (X k).carrier]
    (hpack : forall delta radius, 0 < delta -> exists N : Nat, forall k n,
      n ∈ packingAdmissible (X k).base delta radius -> n <= N) :
    exists phi : Nat -> Nat,
      exists S : CompatiblePointedCompactSystem.{0},
        StrictMono phi /\
          forall i, exists R : VaryingRealizationSequence
              (fun n => ((uniformPackingBoundedClosedBall X hpack (phi n) i)
                |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
              ((S.stage i).toFiniteDiameterBasedMetricSpace
                |>.toBasedMetricSpaceBundle),
            Tendsto
                (fun n => @Metric.hausdorffDist (R.ambient n).carrier
                  inferInstance (Set.range (R.left n)) (Set.range (R.right n)))
                atTop (nhds 0) /\
              PointedGHConverges
                (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
                  |>.toFiniteDiameterBasedMetricSpace)
                (S.stage i).toFiniteDiameterBasedMetricSpace := by
  obtain ⟨phi, Y, hphi, hmarked⟩ :=
    exists_subseq_marked_closedBall_realizations_of_uniform_packing_bounds
      X hpack
  have hconv : forall i, PointedGHConverges
      (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
        |>.toFiniteDiameterBasedMetricSpace)
      (Y i).toFiniteDiameterBasedMetricSpace := by
    intro i
    exact (Classical.choose_spec (hmarked i)).2
  let S := compatibleSystemOfMarkedClosedBallLimits X hpack phi Y hconv
  refine ⟨phi, S, hphi, ?_⟩
  intro i
  change exists R : VaryingRealizationSequence
      (fun n => ((uniformPackingBoundedClosedBall X hpack (phi n) i)
        |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
      ((Y i).toFiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle),
    Tendsto
        (fun n => @Metric.hausdorffDist (R.ambient n).carrier inferInstance
          (Set.range (R.left n)) (Set.range (R.right n)))
        atTop (nhds 0) /\
      PointedGHConverges
        (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
          |>.toFiniteDiameterBasedMetricSpace)
        (Y i).toFiniteDiameterBasedMetricSpace
  exact hmarked i

end Poincare.GromovHausdorff

end

