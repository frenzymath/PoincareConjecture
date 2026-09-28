import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LimitData
import PoincareConjecture.Proofs.M13.OrdinaryFlow

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
  {epsilon K : ℝ} {U : Set M} {x : M}

def quantitativeBackwardInterval (d : ℝ) (hd : 0 < d) : SpacetimeInterval where
  domain := Icc (-d) 0
  ordConnected := ordConnected_Icc
  nontrivial := ⟨-d, ⟨le_rfl, neg_nonpos.mpr hd.le⟩,
    0, ⟨neg_nonpos.mpr hd.le, le_rfl⟩, ne_of_lt (neg_lt_zero.mpr hd)⟩

theorem quantitative_scale_pos
    (N : QuantitativeBackwardNeck g D epsilon K U x) :
    0 < N.neck.scale⁻¹ ^ 2 := by
  exact sq_pos_of_pos (inv_pos.mpr N.neck.scale_pos)

theorem quantitative_scale_duration_eq_half
    (N : QuantitativeBackwardNeck g D epsilon K U x) :
    N.neck.scale⁻¹ ^ 2 * N.model.duration = (1 / 2 : ℝ) := by
  rw [N.duration_eq]
  field_simp [N.neck.scale_pos.ne']

structure NormalizedBackwardWindow
    (N : QuantitativeBackwardNeck g D epsilon K U x) where
  Q : ℝ
  Q_eq : Q = N.neck.scale⁻¹ ^ 2
  Q_pos : 0 < Q
  duration_identity : Q * N.model.duration = (1 / 2 : ℝ)
  flow : letI := N.model.carrier.topologicalSpace
    letI := N.model.carrier.measurableSpace
    letI := N.model.carrier.borelSpace
    letI := N.model.carrier.chartedSpace
    letI := N.model.carrier.isManifold
    letI := N.model.carrier.t2Space
    letI := N.model.carrier.t3Space
    letI := N.model.carrier.secondCountable
    OrdinaryParabolicRescaling (I := quantitativeBackwardInterval
      N.model.duration N.model.duration_pos) N.model.flow Q Q_pos 0

theorem exists_normalized_backward_window
    (N : QuantitativeBackwardNeck g D epsilon K U x) :
    Nonempty (NormalizedBackwardWindow N) := by
  letI := N.model.carrier.topologicalSpace
  letI := N.model.carrier.measurableSpace
  letI := N.model.carrier.borelSpace
  letI := N.model.carrier.chartedSpace
  letI := N.model.carrier.isManifold
  letI := N.model.carrier.t2Space
  letI := N.model.carrier.t3Space
  letI := N.model.carrier.secondCountable
  let Q : ℝ := N.neck.scale⁻¹ ^ 2
  have hQ : 0 < Q := by
    dsimp [Q]
    exact quantitative_scale_pos N
  obtain ⟨R⟩ := M13.ordinaryParabolicRescaling
    (quantitativeBackwardInterval N.model.duration N.model.duration_pos)
    N.model.flow Q hQ 0
  exact ⟨{
    Q := Q
    Q_eq := rfl
    Q_pos := hQ
    duration_identity := by
      dsimp [Q]
      exact quantitative_scale_duration_eq_half N
    flow := R
  }⟩

theorem exists_normalized_terminal_window
    (T : SingularNeckTube g D epsilon)
    {x : M} (hx : x ∈ T.cylinder.tail true (1 / 2 : ℝ)) :
    ∃ N : QuantitativeBackwardNeck g D epsilon T.backward_curvature_bound
        T.carrier x,
      Nonempty (NormalizedBackwardWindow N) := by
  obtain ⟨N⟩ := T.terminal_necks x hx
  exact ⟨N, exists_normalized_backward_window N⟩

theorem normalized_backward_window_domain
    (N : QuantitativeBackwardNeck g D epsilon K U x)
    (W : NormalizedBackwardWindow N) :
    (parabolicInterval W.Q W.Q_pos 0
      (quantitativeBackwardInterval N.model.duration N.model.duration_pos)).domain =
      Icc (-(1 / 2 : ℝ)) 0 := by
  rw [parabolicInterval_domain]
  change (parabolicTimeOrderIso W.Q W.Q_pos 0) ''
    Icc (-N.model.duration) 0 = _
  rw [OrderIso.image_Icc]
  simp only [parabolicTimeOrderIso_apply, parabolicTime, sub_zero]
  congr 1
  · rw [← W.duration_identity]
    ring
  · ring

theorem normalized_backward_window_curvature_bound
    (N : QuantitativeBackwardNeck g D epsilon K U x)
    (W : NormalizedBackwardWindow N)
    {s : ℝ} (hs : s ∈ Icc (-(1 / 2 : ℝ)) 0)
    (p : N.model.carrier.carrier)
    (hp : N.model.embedding p ∈ N.neck.carrier) :
    letI := N.model.carrier.topologicalSpace
    letI := N.model.carrier.measurableSpace
    letI := N.model.carrier.borelSpace
    letI := N.model.carrier.chartedSpace
    letI := N.model.carrier.isManifold
    letI := N.model.carrier.t2Space
    letI := N.model.carrier.t3Space
    letI := N.model.carrier.secondCountable
    (W.flow.flow.connection s).curvatureTensorNorm p ≤ K := by
  letI := N.model.carrier.topologicalSpace
  letI := N.model.carrier.measurableSpace
  letI := N.model.carrier.borelSpace
  letI := N.model.carrier.chartedSpace
  letI := N.model.carrier.isManifold
  letI := N.model.carrier.t2Space
  letI := N.model.carrier.t3Space
  letI := N.model.carrier.secondCountable
  have hsR : s ∈ (parabolicInterval W.Q W.Q_pos 0
      (quantitativeBackwardInterval N.model.duration N.model.duration_pos)).domain := by
    rw [normalized_backward_window_domain N W]
    exact hs
  have ht := (mem_parabolicInterval_iff W.Q W.Q_pos 0
      (quantitativeBackwardInterval N.model.duration N.model.duration_pos) s).mp hsR
  have hscale := (W.flow.metric_calculus s).curvature_norm_eq
    (N.model.flow.connection (parabolicTimeInv W.Q 0 s))
    (W.flow.flow.connection s) p
  change (W.flow.flow.connection s).curvatureTensorNorm p =
    (N.model.flow.connection (parabolicTimeInv W.Q 0 s)).curvatureTensorNorm p / W.Q at hscale
  rw [hscale, div_le_iff₀ W.Q_pos]
  simpa only [W.Q_eq] using
    N.curvature_bound (parabolicTimeInv W.Q 0 s) ht p hp

theorem normalized_backward_window_nonnegative
    (N : QuantitativeBackwardNeck g D epsilon K U x)
    (W : NormalizedBackwardWindow N)
    {s : ℝ} (hs : s ∈ Icc (-(1 / 2 : ℝ)) 0)
    (p : N.model.carrier.carrier) :
    letI := N.model.carrier.topologicalSpace
    letI := N.model.carrier.measurableSpace
    letI := N.model.carrier.borelSpace
    letI := N.model.carrier.chartedSpace
    letI := N.model.carrier.isManifold
    letI := N.model.carrier.t2Space
    letI := N.model.carrier.t3Space
    letI := N.model.carrier.secondCountable
    (W.flow.flow.connection s).NonnegativeCurvatureOperator p := by
  letI := N.model.carrier.topologicalSpace
  letI := N.model.carrier.measurableSpace
  letI := N.model.carrier.borelSpace
  letI := N.model.carrier.chartedSpace
  letI := N.model.carrier.isManifold
  letI := N.model.carrier.t2Space
  letI := N.model.carrier.t3Space
  letI := N.model.carrier.secondCountable
  have hsR : s ∈ (parabolicInterval W.Q W.Q_pos 0
      (quantitativeBackwardInterval N.model.duration N.model.duration_pos)).domain := by
    rw [normalized_backward_window_domain N W]
    exact hs
  have ht := (mem_parabolicInterval_iff W.Q W.Q_pos 0
      (quantitativeBackwardInterval N.model.duration N.model.duration_pos) s).mp hsR
  have hsource := N.model.nonnegative
    (parabolicTimeInv W.Q 0 s) ht p
  have htransport := (M13.homothety_nonnegative_operator_iff
    (N.model.flow.metric (parabolicTimeInv W.Q 0 s))
    (W.flow.flow.metric s)
    (Diffeomorph.refl (𝓡 3) N.model.carrier.carrier ∞)
    W.Q W.Q_pos (W.flow.metric_homothety s)
    (N.model.flow.connection (parabolicTimeInv W.Q 0 s))
    (W.flow.flow.connection s) p).2 hsource
  simpa only [Diffeomorph.coe_refl, id_eq] using htransport

end PoincareConjecture.M28
