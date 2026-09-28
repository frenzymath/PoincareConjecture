import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StrongNeck
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StaticCap
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StaticComponents
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.TerminalPinching
import PoincareConjecture.Proofs.M32.Claim11_32.Sequence


















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

section Extension

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ} (E : GeneralizedFlowExtension F T)



theorem extension_oldSlice_metric_homothety (t : ℝ) (ht : t ∈ F.interval) :
    MetricHomothety (F.metric t) (E.extended.metric t)
      (extension_oldSliceDiffeomorph E t ht) 1 := by
  intro x v w
  change (E.extended.metric t).inner (E.forward t ht x)
    (mfderiv (𝓡 3) (𝓡 3) (E.forward t ht) x v)
    (mfderiv (𝓡 3) (𝓡 3) (E.forward t ht) x w) = 1 * (F.metric t).inner x v w
  simpa only [one_mul] using E.metric_pullback t ht x v w



theorem extension_oldSlice_metric_homothety_symm (t : ℝ) (ht : t ∈ F.interval) :
    MetricHomothety (E.extended.metric t) (F.metric t)
      (extension_oldSliceDiffeomorph E t ht).symm 1 := by
  let e := extension_oldSliceDiffeomorph E t ht
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
  have hm := extension_oldSlice_metric_homothety E t ht (e.symm y)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y v) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)
  change (E.extended.metric t).inner (e (e.symm y))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)) = _ at hm
  rw [hv v, hv w, e.apply_symm_apply] at hm
  simpa only [one_mul] using hm.symm



theorem extension_oldSlice_metric_calculus_symm (t : ℝ) (ht : t ∈ F.interval) :
    MetricHomothetyCalculus (E.extended.metric t) (F.metric t)
      (extension_oldSliceDiffeomorph E t ht).symm 1 :=
  Homothety.metricHomothetyCalculus _ _ _ 1 (by norm_num)
    (extension_oldSlice_metric_homothety_symm E t ht)



theorem extension_canonical_control (t : ℝ) (ht : t ∈ F.interval)
    (x : (F.slice t).carrier) (epsilon C : ℝ)
    (h : GeneralizedCanonicalControl t x epsilon C) :
    GeneralizedCanonicalControl t (E.forward t ht x) epsilon C := by
  let e := (extension_oldSliceDiffeomorph E t ht).symm
  have he : MetricHomothety (E.extended.metric t) (F.metric t) e 1 :=
    extension_oldSlice_metric_homothety_symm E t ht
  have Hcal : MetricHomothetyCalculus (E.extended.metric t) (F.metric t) e 1 :=
    extension_oldSlice_metric_calculus_symm E t ht
  cases h with
  | neck N hcenter =>
    exact .neck (extension_strongNeck E t ht N)
      ((extension_strongNeck_center E t ht N).trans (congrArg (E.forward t ht) hcenter))
  | cap N hepsilon hconstant _ hcore =>
    refine .cap (pullbackCapCertificate N he Hcal (E.extended.connection t))
      hepsilon hconstant rfl ?_
    change E.inverse t ht (E.forward t ht x) ∈ N.core
    simpa only [E.left_inverse t ht x] using hcore
  | component N hmem =>
    refine .component (pullbackSingularCComponent N he Hcal (E.extended.connection t)) ?_
    change E.inverse t ht (E.forward t ht x) ∈ N.carrier
    simpa only [E.left_inverse t ht x] using hmem
  | round N hmem =>
    refine .round (pullbackSingularRoundComponent N he) ?_
    change E.inverse t ht (E.forward t ht x) ∈ N.carrier
    simpa only [E.left_inverse t ht x] using hmem



theorem extension_slice_canonical (s : ℝ) (hs : s ∈ F.interval) (epsilon C cutoff : ℝ)
    (h : generalizedSliceStrongCanonicalNeighborhoods F epsilon C cutoff s) :
    generalizedSliceStrongCanonicalNeighborhoods E.extended epsilon C cutoff s := by
  intro y hy
  have hscalar : F.scalar ⟨s, E.inverse s hs y⟩ = E.extended.scalar ⟨s, y⟩ := by
    change (F.connection s).scalarCurvature _ = (E.extended.connection s).scalarCurvature y
    rw [← E.scalar_pullback s hs (E.inverse s hs y), E.right_inverse s hs y]
  obtain ⟨hcontrol⟩ := h (E.inverse s hs y) (hscalar.symm ▸ hy)
  have hc := extension_canonical_control E s hs (E.inverse s hs y) epsilon C hcontrol
  rw [E.right_inverse s hs y] at hc
  exact ⟨hc⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]



theorem extension_earlier_dense_canonical (H : SingularTimeAssumptions F T M)
    {t : ℝ} (htT : t ≤ T) (x : (E.extended.slice t).carrier)
    (hcutoff : H.r₀⁻¹ ^ 2 ≤ 4 * E.extended.scalar ⟨t, x⟩) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods E.extended
      H.epsilon H.constant t x := by
  intro s hs hst a has
  have hs0 : 0 ≤ s := by
    rcases E.times_subset hs with hsold | hsnew
    · exact H.interval_nonnegative hsold
    · have hsT : s = T := mem_singleton_iff.mp hsnew
      rw [hsT]
      exact (terminalTime_pos H).le
  obtain ⟨r, hr, har, hrs, hregular⟩ :=
    existsRegularTimeAbove H hs0 (hst.trans htT) has
  refine ⟨r, E.old_times hr, har, hrs, ?_⟩
  apply extension_slice_canonical E r hr
  intro y hy
  exact ⟨H.canonical_control r hr hregular y (hcutoff.trans hy)⟩

end Extension

section Sequence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}



theorem terminalBlowupSequence_boundedDistance_hypotheses
    (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
    (Q : ∀ k, SingularLimitConclusion (H k))
    (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
    (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
    (hdiv : Tendsto (fun k =>
      ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)
    (hM04 : RicciFlowCurvatureTheory.{u}) {epsilon C : ℝ}
    (hepsilon : ∀ k, (H k).epsilon = epsilon) (hC : ∀ k, (H k).constant = C)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 ≤
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k) :
    GeneralizedBoundedDistanceHypotheses
      (terminalBlowupSequence H Q x hpos hdiv) epsilon C := by
  constructor
  · intro k
    exact extension_pinchedOrNonnegative hM04 (H k) (Q k).extension
  · intro k
    simpa only [terminalBlowupSequence, hepsilon k, hC k] using
      extension_earlier_dense_canonical (Q k).extension (H k) le_rfl (x k) (hcutoff k)

end Sequence

end PoincareConjecture.M32
