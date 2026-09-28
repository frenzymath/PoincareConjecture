import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveBoxLines
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

def HistoryPositive {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    (H : M33RegularHistoryRealization G F) (p : G.point) : Prop :=
  ∀ ht : p.1 ∈ G.interval, SurgeryPositiveComponentAt F p.1 (H.forward p.1 ht p.2)

def componentBoxImage (G : GeneralizedRicciFlowData.{u})
    (i : Σ q : G.box_index, (G.box q).carrier.carrier) : Set G.point :=
  (fun p : (G.box i.1).interval × (G.box i.1).carrier.carrier =>
    (⟨p.1.1, (G.box i.1).forward p.1.1 p.1.2 p.2⟩ : G.point)) ''
      (univ ×ˢ connectedComponent i.2)

theorem componentBoxImage_isOpen (G : GeneralizedRicciFlowData.{u})
    (i : Σ q : G.box_index, (G.box q).carrier.carrier) :
    IsOpen (componentBoxImage G i) := by
  let : LocallyConnectedSpace (G.box i.1).carrier.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  exact (G.box_openEmbedding i.1).isOpenMap _
    (isOpen_univ.prod isOpen_connectedComponent)

theorem componentBoxImage_cover (G : GeneralizedRicciFlowData.{u}) :
    (univ : Set G.point) ⊆ ⋃ i, componentBoxImage G i := by
  intro p _
  obtain ⟨q, ht, x, hx⟩ := G.box_covers p.1 p.2
  apply mem_iUnion.mpr
  refine ⟨⟨q, x⟩, ⟨(⟨p.1, ht⟩, x), ⟨mem_univ _, mem_connectedComponent⟩, ?_⟩⟩
  exact congrArg (fun z => (⟨p.1, z⟩ : G.point)) hx

theorem historyPositive_of_mem_componentBox
    {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    (H : M33RegularHistoryRealization G F)
    (i : Σ q : G.box_index, (G.box q).carrier.carrier)
    {p r : G.point} (hp : p ∈ componentBoxImage G i)
    (hr : r ∈ componentBoxImage G i) (hpr : p.1 ≤ r.1)
    (hpos : HistoryPositive H p) : HistoryPositive H r := by
  obtain ⟨⟨s, x⟩, ⟨_, hx⟩, rfl⟩ := hp
  obtain ⟨⟨t, y⟩, ⟨_, hy⟩, rfl⟩ := hr
  have hxy : y ∈ connectedComponent x := by
    simpa only [connectedComponent_eq hx] using hy
  intro ht
  exact positive_component_history_box_connected H i.1 hxy s.2 t.2 hpr
    (hpos (m33BoxIntervalSubset G i.1 s.2))

theorem historyPositive_along_path
    {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    (H : M33RegularHistoryRealization G F) {a b : ℝ} (hab : a ≤ b)
    (γ : ℝ → G.point) (hγ : ContinuousOn γ (Icc a b))
    (hclock : MonotoneOn (fun s => (γ s).1) (Icc a b))
    (hstart : HistoryPositive H (γ a)) : HistoryPositive H (γ b) := by
  let c : (Σ q : G.box_index, (G.box q).carrier.carrier) → Set (Icc a b) :=
    fun i => (fun s : Icc a b => γ s.1) ⁻¹' componentBoxImage G i
  have hc : ∀ i, IsOpen (c i) := fun i =>
    (componentBoxImage_isOpen G i).preimage (continuousOn_iff_continuous_domRestrict.mp hγ)
  have hcover : univ ⊆ ⋃ i, c i := by
    intro s _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (componentBoxImage_cover G (mem_univ (γ s.1)))
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hc hcover
  have hind : ∀ n : ℕ, HistoryPositive H (γ (t n).1) := by
    intro n
    induction n with
    | zero => simpa only [ht0] using hstart
    | succ n ih =>
      obtain ⟨i, hi⟩ := hsub n
      have hle : t n ≤ t (n + 1) := hmono (Nat.le_succ n)
      exact historyPositive_of_mem_componentBox H i
        (hi ⟨le_rfl, hle⟩) (hi ⟨hle, le_rfl⟩)
        (hclock (t n).2 (t (n + 1)).2 hle) ih
  simpa only [hm m le_rfl] using hind m

end PoincareConjecture.Proofs.M46
