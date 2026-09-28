import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M03.FiniteBundleFamilyEnergy
import PoincareConjecture.Proofs.M03.FiniteCoordinateCutoffs
import PoincareConjecture.Proofs.M03.ModelFiberEnergyCoordinates










set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle MeasureTheory Set

universe u

namespace PoincareConjecture.Proofs.M03

theorem exists_metric_difference_energy
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] :
    let FM := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ
    let EM := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ
    let d := Module.finrank ℝ FM
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ∃ (q : FM ≃L[ℝ] EuclideanSpace ℝ (Fin d))
      (s : Finset M) (φ : M → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ),
      0 ≤ C ∧
      (∀ a ∈ s, ContDiff ℝ ∞ (φ a) ∧ HasCompactSupport (φ a) ∧
        tsupport (φ a) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target) ∧
      (∀ x : M, ∃ a ∈ s,
        x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) a).source ∧
        φ a (chartAt (EuclideanSpace ℝ (Fin n)) a x) = 1) ∧
      ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J')
        (K : Set ℝ), IsCompact K → K ⊆ J ∩ J' →
        let c := chartAt (EuclideanSpace ℝ (Fin n))
        let e := trivializationAt FM EM
        let h : (t : ℝ) → (x : M) → EM x :=
          fun t x => (F.metric t).inner x - (F'.metric t).inner x
        let f : M → Fin d → ℝ × EuclideanSpace ℝ (Fin n) → ℝ :=
          fun a i p => q ((e a) (TotalSpace.mk' FM
            ((c a).symm p.2) (h p.1 ((c a).symm p.2)))).2 i
        let energy : ℝ → ℝ :=
          fun t => ∑ a ∈ s, ∑ i, ∫ z, (φ a z * f a i (t, z)) ^ 2
        ContinuousOn energy K ∧
        (∀ t ∈ K, 0 ≤ energy t) ∧
        (∀ t ∈ K, energy t = 0 ↔ F.metric t = F'.metric t) ∧
        (∀ t ∈ interior K, HasDerivAt energy
          (∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * f a i (t, z) *
            fderiv ℝ (f a i) (t, z) (1, 0)) t) ∧
        (∀ t ∈ K, ∀ a ∈ s,
          (∫ z in tsupport (φ a), ∑ i, (f a i (t, z)) ^ 2) ≤ C * energy t) := by
  let FM := EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ
  let EM := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] ℝ
  let : NormedAddCommGroup FM := inferInstance
  let : NormedSpace ℝ FM := inferInstance
  let : ∀ x, AddCommGroup (EM x) := inferInstance
  let : ∀ x, Module ℝ (EM x) := inferInstance
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  obtain ⟨q, _, _, _⟩ := exists_model_fiber_energy_coordinates (F := FM)
  obtain ⟨s, r, R, φ, hcut, hcover⟩ := exists_finite_coordinate_cutoffs (n := n) (M := M)
  have hφ : ∀ a ∈ s, ContDiff ℝ ∞ (φ a) ∧ HasCompactSupport (φ a) ∧
      tsupport (φ a) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target := by
    intro a ha
    obtain ⟨_, _, htarget, hsmooth, hcompact, _, _, hsupp, _, _⟩ := hcut a ha
    exact ⟨hsmooth, hcompact, hsupp.trans htarget⟩
  have hcover' : ∀ x : M, ∃ a ∈ s,
      x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) a).source ∧
      φ a (chartAt (EuclideanSpace ℝ (Fin n)) a x) = 1 := by
    intro x
    obtain ⟨a, ha, hx, hz⟩ := hcover x
    obtain ⟨_, _, _, _, _, _, hone, _, _, _⟩ := hcut a ha
    exact ⟨a, ha, hx, hone (Metric.ball_subset_closedBall hz)⟩
  have hbase : ∀ a ∈ s, (chartAt (EuclideanSpace ℝ (Fin n)) a).source ⊆
      (trivializationAt FM EM a).baseSet := by
    intro a _
    simp only [FM, EM, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, mem_univ x⟩
  obtain ⟨C, hC0, hC⟩ := exists_finite_bundle_family_energy_bound (E := EM) q s φ
    (fun a ha => (hφ a ha).1.continuous) (fun a ha => (hφ a ha).2.1)
    (fun a ha => (hφ a ha).2.2) hbase hcover'
  refine ⟨q, s, φ, C, hC0, hφ, hcover', ?_⟩
  intro J J' F F' K hK hKsub
  let h : (t : ℝ) → (x : M) → EM x :=
    fun t x => (F.metric t).inner x - (F'.metric t).inner x
  have hF : RiemannianMetric.IsSmoothFamilyOn F.metric K :=
    F.smooth.mono (Set.prod_mono (fun _ ht => (hKsub ht).1) subset_rfl)
  have hF' : RiemannianMetric.IsSmoothFamilyOn F'.metric K :=
    F'.smooth.mono (Set.prod_mono (fun _ ht => (hKsub ht).2) subset_rfl)
  have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, FM)) ∞
      (fun p : ℝ × M => TotalSpace.mk' FM p.2 (h p.1 p.2)) (K ×ˢ Set.univ) := by
    intro p hp
    apply Bundle.contMDiffWithinAt_totalSpace.mpr
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    have hc := (Bundle.contMDiffWithinAt_totalSpace.mp (hF p hp)).2
    have hc' := (Bundle.contMDiffWithinAt_totalSpace.mp (hF' p hp)).2
    let e := trivializationAt FM EM p.2
    have he : p.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.2
    have hnear : ∀ᶠ z in 𝓝[K ×ˢ (Set.univ : Set M)] p, z.2 ∈ e.baseSet :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he))
    apply (hc.sub hc').congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [hnear] with z hz
    exact (e.linearEquivAt ℝ z.2 hz).map_sub
      ((F.metric z.1).inner z.2) ((F'.metric z.1).inner z.2)
  obtain ⟨hcont, hnonneg, hzero, hderiv, hbound⟩ := hC K hK h hh
  refine ⟨hcont, hnonneg, ?_, hderiv, hbound⟩
  intro t ht
  refine (hzero t ht).trans ?_
  constructor
  · intro hzero'
    have hinner : (F.metric t).inner = (F'.metric t).inner := by
      funext x
      exact sub_eq_zero.mp (hzero' x)
    have hext (g g' : RiemannianMetric n M) (heq : g.inner = g'.inner) : g = g' := by
      cases g
      cases g'
      cases heq
      rfl
    exact hext _ _ hinner
  · intro heq x
    exact sub_eq_zero.mpr (congrArg (fun g : RiemannianMetric n M => g.inner x) heq)

end PoincareConjecture.Proofs.M03
