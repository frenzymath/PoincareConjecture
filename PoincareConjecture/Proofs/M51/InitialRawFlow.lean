import PoincareConjecture.Proofs.M51.OrdinaryRestriction
import PoincareConjecture.Definitions.M33BranchContinuation
import PoincareConjecture.Definitions.Ch17.GlobalSurgery
import PoincareConjecture.Proofs.Ch01.CurvatureConnection









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51Initial

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]


abbrev carrier (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] : GeneralizedSliceCarrier.{u} where
  carrier := M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

omit [T2Space M] [SecondCountableTopology M] in

theorem initial_norm_bound (I : NormalizedInitialMetric (M := M))
    {J : Set ℝ} (F : RicciFlow 3 M J) (h0 : F.metric 0 = I.metric) (x : M) :
    (F.connection 0).curvatureTensorNorm x ≤ 1 := by
  have hmetric : ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g),
      g = I.metric → D.curvatureTensorNorm x ≤ 1 := by
    intro g D hg
    subst g
    rw [D.curvatureTensorNorm_eq I.connection]
    exact I.full_curvature_bound x
  exact hmetric _ _ h0

omit [T2Space M] [SecondCountableTopology M] in
theorem initial_volume_bound (I : NormalizedInitialMetric (M := M))
    {J : Set ℝ} (F : RicciFlow 3 M J) (h0 : F.metric 0 = I.metric)
    (x : M) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
      calibratedMetricVolume (F.metric 0) ((F.metric 0).ball x r) := by
  rw [h0]
  have hfinite : euclideanUnitBallLebesgueVolume ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have hcoeff : ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) =
      (euclideanUnitBallLebesgueVolume / 2) * ENNReal.ofReal r ^ 3 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfinite,
      ENNReal.ofReal_pow hr.le]
    norm_num only [ENNReal.ofReal_ofNat]
    simp only [div_eq_mul_inv, mul_right_comm]
  rw [hcoeff]
  rw [show calibratedMetricVolume I.metric = normalizedMetricVolume I.metric from rfl]
  rw [← I.volume_is_normalized_metric]
  exact I.small_ball_lower_bound x r hr hr1

noncomputable def regularSlab {J : Set ℝ} (F : RicciFlow 3 M J)
    (a b : ℝ) (hab : a < b) (hJ : Icc a b ⊆ J) :
    SurgeryRegularSlab (fun _ => carrier M) F.metric a b where
  ordered := hab
  flow := M51Ordinary.restrict F hJ ordConnected_Icc
    ⟨a, ⟨le_rfl, hab.le⟩, b, ⟨hab.le, le_rfl⟩, hab.ne⟩
  identify := fun _ => Diffeomorph.refl (𝓡 3) M ∞
  initial_identify := fun _ => rfl
  metric_pullback := by
    intro t x v w
    change (F.metric t.1).inner (id x)
      (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x v)
      (mfderiv (𝓡 3) (𝓡 3) (id : M → M) x w) = _
    simp only [mfderiv_id, ContinuousLinearMap.id_apply]
    rfl

@[simp] theorem regularSlab_transport {J : Set ℝ} (F : RicciFlow 3 M J)
    (a b : ℝ) (hab : a < b) (hJ : Icc a b ⊆ J) (s t : Icc a b) (x : M) :
    (regularSlab F a b hab hJ).transport s t x = x := rfl

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] in

theorem maximality {J : Set ℝ} (F : RicciFlow 3 M J)
    (hshape : J = Ici 0 ∨ ∃ T : ℝ, 0 < T ∧ J = Ico 0 T ∧
      ∀ L s : ℝ, s < T → ∃ t ∈ Ioo (max 0 s) T, ∃ x : M,
        L < (F.connection t).curvatureTensorNorm x)
    (b : ℝ) (hb : 0 < b) (hsub : Ico 0 b ⊆ J) (hout : b ∉ J) :
    ∀ L s : ℝ, s < b → ∃ t ∈ Ioo (max 0 s) b, ∃ x : M,
      L < (F.connection t).curvatureTensorNorm x := by
  rcases hshape with hJ | ⟨T, hT, hJ, hcurv⟩
  · exact False.elim (hout (hJ ▸ hb.le))
  · have hTb : T ≤ b := by
      by_contra h
      exact hout (hJ ▸ ⟨hb.le, lt_of_not_ge h⟩)
    have hbT : b ≤ T := by
      by_contra h
      have hmem := hsub (show T ∈ Ico 0 b from ⟨hT.le, lt_of_not_ge h⟩)
      rw [hJ] at hmem
      exact lt_irrefl T hmem.2
    have hEq := le_antisymm hbT hTb
    simpa only [hEq] using hcurv

variable [CompactSpace M] [Nonempty M]


noncomputable def rawFlow (g0 : StandardInitialMetric) (K : MetricSurgeryConstants)
    (P : SurgeryParameters) (I : NormalizedInitialMetric (M := M))
    (hRP : NoTrivialNormalProjectivePlane (M := M))
    {J : Set ℝ} (F : RicciFlow 3 M J) (h0 : F.metric 0 = I.metric)
    (hleast : IsLeast J 0)
    (hmax : ∀ b : ℝ, 0 < b → Ico 0 b ⊆ J → b ∉ J →
      ∀ L s : ℝ, s < b → ∃ t ∈ Ioo (max 0 s) b, ∃ x : M,
        L < (F.connection t).curvatureTensorNorm x) : SurgeryFlowData.{u} where
  standard_initial := g0
  local_constants := K
  parameters := P
  time_domain := J
  time_domain_interval := F.interval
  time_domain_nonnegative := hleast.2
  zero_mem := hleast.1
  slice := fun _ => carrier M
  metric := F.metric
  connection := F.connection
  slices_compact := fun _ _ => (show IsCompact (univ : Set M) from isCompact_univ)
  no_two_sided_projective_plane := fun _ _ => hRP
  initial_nonempty := (show Nonempty M from inferInstance)
  initial_normalized := fun x =>
    ⟨initial_norm_bound I F h0 x, initial_volume_bound I F h0 x⟩
  surgery_times := ∅
  surgery_times_subset := empty_subset J
  zero_not_surgery := by simp
  surgery_times_locally_finite := fun _ _ =>
    ⟨1, by norm_num, finite_empty.subset inter_subset_left⟩
  regular_slabs := fun a b hab hJ _ => regularSlab F a b hab hJ
  slab_transport_coherent := by intros; rfl
  event := fun _ hT => False.elim hT
  vanishing_event := fun _ hT => False.elim hT
  event_slab_compatibility := fun _ hT => False.elim hT
  vanishing_slab_compatibility := fun _ hT => False.elim hT
  maximal_intervals := by
    intro a b _ hstart hab hsub _ _ hend
    have ha : a = 0 := hstart.elim id False.elim
    subst a
    exact hmax b hab hsub (hend.elim False.elim id)
  extinction_permanent := fun _ _ _ _ _ he => he

end PoincareConjecture.M51Initial
