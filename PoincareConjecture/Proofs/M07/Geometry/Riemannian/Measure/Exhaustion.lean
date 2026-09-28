import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.LocalFinite
import PoincareConjecture.Proofs.M07.Topology.Exhaustion
import Mathlib.Topology.EMetricSpace.Paracompact












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

private theorem compactExhaustion_of_connected_paracompact
    {X : Type u} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    [WeaklyLocallyCompactSpace X] [ParacompactSpace X] (p : X) :
    Nonempty (CompactExhaustion X) := by
  classical
  choose C hC hCn using fun x : X ↦ exists_compact_mem_nhds x
  obtain ⟨V, hVo, hVcover, hVloc, hVC⟩ := precise_refinement
    (fun x ↦ interior (C x)) (fun _ ↦ isOpen_interior)
    (iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, mem_interior_iff_mem_nhds.mpr (hCn x)⟩)
  have hVcompact (x : X) : IsCompact (closure (V x)) :=
    (hC x).of_isClosed_subset isClosed_closure
      (closure_minimal ((hVC x).trans interior_subset) (hC x).isClosed)
  let step (s : Set X) := ⋃ i ∈ {i | (V i ∩ s).Nonempty}, closure (V i)
  have hstep_compact {s : Set X} (hs : IsCompact s) : IsCompact (step s) :=
    (hVloc.finite_nonempty_inter_compact hs).isCompact_biUnion
      (fun i _ ↦ hVcompact i)
  have hVstep {s : Set X} {i : X} (hi : (V i ∩ s).Nonempty) :
      V i ⊆ step s := by
    intro x hx
    exact mem_iUnion₂.mpr ⟨i, hi, subset_closure hx⟩
  have hstep_interior (s : Set X) : s ⊆ interior (step s) := by
    intro x hx
    obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.mp hVcover x
    exact interior_mono (hVstep ⟨x, hi, hx⟩) ((hVo i).interior_eq.symm ▸ hi)
  let K : ℕ → Set X := fun j ↦ Nat.rec {p} (fun _ s ↦ step s) j
  have hKcompact : ∀ j, IsCompact (K j) := by
    intro j
    induction j with
    | zero => exact isCompact_singleton
    | succ j ih => exact hstep_compact ih
  have hKstep (j : ℕ) : K j ⊆ interior (K (j + 1)) := hstep_interior _
  have hSopen : IsOpen (⋃ j, K j) := by
    have heq : (⋃ j, K j) = ⋃ j, interior (K j) := by
      apply Subset.antisymm
      · exact iUnion_subset fun j ↦ (hKstep j).trans
          (subset_iUnion (fun k ↦ interior (K k)) (j + 1))
      · exact iUnion_mono fun _ ↦ interior_subset
    rw [heq]
    exact isOpen_iUnion fun _ ↦ isOpen_interior
  have hSclosed : IsClosed (⋃ j, K j) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.mp hVcover x
    apply Filter.mem_of_superset ((hVo i).mem_nhds hi)
    intro y hy hyS
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyS
    exact hx (mem_iUnion.mpr ⟨j + 1, hVstep ⟨y, hy, hj⟩ hi⟩)
  have hcover : (⋃ j, K j) = univ :=
    (show IsClopen (⋃ j, K j) from ⟨hSclosed, hSopen⟩).eq_univ
      ⟨p, mem_iUnion.mpr ⟨0, mem_singleton p⟩⟩
  exact ⟨⟨K, hKcompact, hKstep, hcover⟩⟩

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]



theorem nonempty_compactExhaustion (g : RiemannianMetric n M) :
    Nonempty (CompactExhaustion M) := by
  classical
  rcases isEmpty_or_nonempty M with h | h
  · exact ⟨⟨fun _ ↦ ∅, fun _ ↦ isCompact_empty,
      fun _ ↦ empty_subset _, by ext x; exact isEmptyElim x⟩⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  exact compactExhaustion_of_connected_paracompact (Classical.arbitrary M)



theorem secondCountableTopology (g : RiemannianMetric n M) :
    SecondCountableTopology M := by
  obtain ⟨K⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M

variable [MeasurableSpace M] [BorelSpace M]



instance volumeMeasure_sigmaFinite_of_preconnected (g : RiemannianMetric n M) :
    SigmaFinite (volumeMeasure g) := by
  let : SecondCountableTopology M := g.secondCountableTopology
  exact volumeMeasure_sigmaFinite g



theorem exists_finiteVolume_open_exhaustion (g : RiemannianMetric n M) (base : M) :
    ∃ U : ℕ → Set M,
      (∀ j, IsOpen (U j)) ∧
      (∀ j, IsConnected (U j)) ∧
      (∀ j, IsCompact (closure (U j))) ∧
      (∀ j, volumeMeasure g (closure (U j)) < ⊤) ∧
      (∀ j, U j ⊆ U (j + 1)) ∧
      (⋃ j, U j = univ) ∧
      (∀ j, base ∈ U j) := by
  let : SecondCountableTopology M := g.secondCountableTopology
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨U, hUo, hUc, hUk, hUm, hcover, hbase⟩ :=
    Poincare.exists_connected_open_exhaustion base
  exact ⟨U, hUo, hUc, hUk, fun j ↦ g.volumeMeasure_lt_top_of_isCompact (hUk j),
    hUm, hcover, hbase⟩

end PoincareConjecture.RiemannianMetric
