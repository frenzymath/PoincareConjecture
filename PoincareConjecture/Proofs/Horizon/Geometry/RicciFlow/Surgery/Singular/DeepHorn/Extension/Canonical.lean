import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticCap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticComponents
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.BoundedDistance.Dense

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.GeneralizedFlowExtension

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ} (E : GeneralizedFlowExtension F T)

theorem oldSlice_metric_homothety (t : ℝ) (ht : t ∈ F.interval) :
    MetricHomothety (F.metric t) (E.extended.metric t) (E.oldSliceDiffeomorph t ht) 1 := by
  intro x v w
  change (E.extended.metric t).inner (E.forward t ht x)
    (mfderiv (𝓡 3) (𝓡 3) (E.forward t ht) x v)
    (mfderiv (𝓡 3) (𝓡 3) (E.forward t ht) x w) = 1 * (F.metric t).inner x v w
  simpa only [one_mul] using E.metric_pullback t ht x v w

theorem oldSlice_metric_homothety_symm (t : ℝ) (ht : t ∈ F.interval) :
    MetricHomothety (E.extended.metric t) (F.metric t)
      (E.oldSliceDiffeomorph t ht).symm 1 := by
  let e := E.oldSliceDiffeomorph t ht
  intro y v w
  have hcomp : e ∘ e.symm = id := by
    funext z
    exact e.apply_symm_apply z
  have hd := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (e.symm y))
    (e.symm.contMDiff.mdifferentiable (by simp) y)
  rw [hcomp, mfderiv_id] at hd
  have hv (z : TangentSpace (𝓡 3) y) :
      mfderiv (𝓡 3) (𝓡 3) e (e.symm y)
        (mfderiv (𝓡 3) (𝓡 3) e.symm y z) = z :=
    (congrArg (fun A => A z) hd).symm
  have hm := E.oldSlice_metric_homothety t ht (e.symm y)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y v) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)
  change (E.extended.metric t).inner (e (e.symm y))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)) = _ at hm
  rw [hv v, hv w, e.apply_symm_apply] at hm
  simpa only [one_mul] using hm.symm

theorem oldSlice_metric_calculus_symm (t : ℝ) (ht : t ∈ F.interval) :
    MetricHomothetyCalculus (E.extended.metric t) (F.metric t)
      (E.oldSliceDiffeomorph t ht).symm 1 :=
  Homothety.metricHomothetyCalculus _ _ _ 1 (by norm_num)
    (E.oldSlice_metric_homothety_symm t ht)

theorem canonical_control (t : ℝ) (ht : t ∈ F.interval)
    (x : (F.slice t).carrier) (epsilon C : ℝ)
    (h : GeneralizedCanonicalControl t x epsilon C) :
    GeneralizedCanonicalControl t (E.forward t ht x) epsilon C := by
  let e := (E.oldSliceDiffeomorph t ht).symm
  have he : MetricHomothety (E.extended.metric t) (F.metric t) e 1 :=
    E.oldSlice_metric_homothety_symm t ht
  have H : MetricHomothetyCalculus (E.extended.metric t) (F.metric t) e 1 :=
    E.oldSlice_metric_calculus_symm t ht
  cases h with
  | neck N hcenter =>
    exact .neck (E.strongNeck t ht N)
      ((E.strongNeck_center t ht N).trans (congrArg (E.forward t ht) hcenter))
  | cap N hepsilon hconstant _ hcore =>
    refine .cap (N.m48_pullback he H (E.extended.connection t)) hepsilon hconstant rfl ?_
    change E.inverse t ht (E.forward t ht x) ∈ N.core
    simpa only [E.left_inverse t ht x] using hcore
  | component N hmem =>
    refine .component (N.m48_pullback he H (E.extended.connection t)) ?_
    change E.inverse t ht (E.forward t ht x) ∈ N.carrier
    simpa only [E.left_inverse t ht x] using hmem
  | round N hmem =>
    refine .round (N.m48_pullback he) ?_
    change E.inverse t ht (E.forward t ht x) ∈ N.carrier
    simpa only [E.left_inverse t ht x] using hmem

theorem slice_canonical (s : ℝ) (hs : s ∈ F.interval) (epsilon C Q : ℝ)
    (h : generalizedSliceStrongCanonicalNeighborhoods F epsilon C Q s) :
    generalizedSliceStrongCanonicalNeighborhoods E.extended epsilon C Q s := by
  intro y hy
  have hscalar : F.scalar ⟨s, E.inverse s hs y⟩ = E.extended.scalar ⟨s, y⟩ := by
    change (F.connection s).scalarCurvature _ = (E.extended.connection s).scalarCurvature y
    rw [← E.scalar_pullback s hs (E.inverse s hs y), E.right_inverse s hs y]
  obtain ⟨hcontrol⟩ := h (E.inverse s hs y) (hscalar.symm ▸ hy)
  have hc := E.canonical_control s hs (E.inverse s hs y) epsilon C hcontrol
  rw [E.right_inverse s hs y] at hc
  exact ⟨hc⟩

theorem earlier_dense_canonical (t : ℝ) (ht : t ∈ F.interval) (htT : t < T)
    (x : (F.slice t).carrier) (epsilon C : ℝ)
    (h : generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods E.extended epsilon C t
      (E.forward t ht x) := by
  intro s hs hst a has
  have hsold : s ∈ F.interval := by
    rcases E.times_subset hs with hsold | hsT
    · exact hsold
    · have hsT' : s = T := hsT
      exact False.elim ((not_le_of_gt htT) (hsT' ▸ hst))
  obtain ⟨r, hr, har, hrs, hslice⟩ := h s hsold hst a has
  refine ⟨r, E.old_times hr, har, hrs, ?_⟩
  have hc := E.slice_canonical r hr epsilon C (4 * F.scalar ⟨t, x⟩) hslice
  simpa only [GeneralizedRicciFlowData.scalar, E.scalar_pullback] using hc

end PoincareConjecture.GeneralizedFlowExtension

namespace PoincareConjecture.SingularTimeAssumptions

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

theorem terminal_time_pos (H : SingularTimeAssumptions F T M) : 0 < T := by
  obtain ⟨s, hs⟩ := F.interval_nontrivial.nonempty
  exact (H.interval_preterminal hs).1.trans_lt (H.interval_preterminal hs).2

theorem exists_regular_time_above (H : SingularTimeAssumptions F T M)
    {s a : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) (has : a < s) :
    ∃ r, r ∈ F.interval ∧ a < r ∧ r ≤ s ∧ (r = 0 ∨ r ∉ H.singularTimes) := by
  by_cases hs0' : s = 0
  · exact ⟨0, H.interval_exhausts_preterminal ⟨le_rfl, H.terminal_time_pos⟩,
      by simpa only [hs0'] using has, hs0, Or.inl rfl⟩
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs0')
  by_cases hsing : s ∈ H.singularTimes
  · obtain ⟨d, hd, hsep⟩ := H.singularTimes_discrete s hsing
    obtain ⟨r, hlow, hrs⟩ := exists_between
      (max_lt has (max_lt hspos (sub_lt_self s hd)))
    have hr0 : 0 < r :=
      ((le_max_left 0 (s - d)).trans (le_max_right a (max 0 (s - d)))).trans_lt hlow
    have hrnear : s - d < r :=
      ((le_max_right 0 (s - d)).trans (le_max_right a (max 0 (s - d)))).trans_lt hlow
    refine ⟨r, H.interval_exhausts_preterminal ⟨hr0.le, hrs.trans_le hsT⟩,
      (le_max_left a _).trans_lt hlow, hrs.le, Or.inr ?_⟩
    intro hrS
    have hdist := hsep r hrS (ne_of_lt hrs)
    rw [abs_of_neg (sub_neg.mpr hrs)] at hdist
    linarith
  · have hsltT : s < T := lt_of_le_of_ne hsT (by
      intro heq
      exact hsing (heq.symm ▸ H.terminal_is_singular))
    exact ⟨s, H.interval_exhausts_preterminal ⟨hs0, hsltT⟩, has, le_rfl, Or.inr hsing⟩

end PoincareConjecture.SingularTimeAssumptions

namespace PoincareConjecture.GeneralizedFlowExtension

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

theorem earlier_dense_canonical_of_singularTimeAssumptions
    (E : GeneralizedFlowExtension F T) (H : SingularTimeAssumptions F T M)
    {t : ℝ} (htT : t ≤ T) (x : (E.extended.slice t).carrier)
    (hcutoff : H.r₀⁻¹ ^ 2 ≤ 4 * E.extended.scalar ⟨t, x⟩) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods E.extended
      H.epsilon H.constant t x := by
  intro s hs hst a has
  have hs0 : 0 ≤ s := by
    rcases E.times_subset hs with hsold | hsnew
    · exact H.interval_nonnegative hsold
    · have hsT : s = T := hsnew
      rw [hsT]
      exact H.terminal_time_pos.le
  obtain ⟨r, hr, har, hrs, hregular⟩ :=
    H.exists_regular_time_above hs0 (hst.trans htT) has
  refine ⟨r, E.old_times hr, har, hrs, ?_⟩
  apply E.slice_canonical r hr
  intro y hy
  exact ⟨H.canonical_control r hr hregular y (hcutoff.trans hy)⟩

end PoincareConjecture.GeneralizedFlowExtension
