import PoincareConjecture.Proofs.M38.ZeroCapRetention
import PoincareConjecture.Proofs.M38.ComponentDecomposition
import PoincareConjecture.Proofs.M38.EventSlices

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

theorem zero_cap_reconstruction (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (hcount : (F.event T hT).cap_count = 0)
    (hstandard : ∀ x : (F.slice (F.event T hT).tMinus).carrier,
      x ∉ (F.event T hT).retained_pre →
        Nonempty (SurgerySphereBundle
          (componentCarrier (F.slice (F.event T hT).tMinus) x)) ∨
        Nonempty (SurgeryPositiveSpaceform
          (componentCarrier (F.slice (F.event T hT).tMinus) x))) :
    Nonempty (RawNonemptyTopologyWitness F T hT) := by
  classical
  let : IsEmpty (Fin (F.event T hT).cap_count) := by
    rw [hcount]
    infer_instance
  have hcompact := F.slices_compact (F.event T hT).tMinus
    (mem_time_domain_before_surgery F hT (F.event T hT).tMinus_nonnegative
      (F.event T hT).tMinus_lt.le)
  obtain ⟨n, r, D, hregion⟩ :=
    exists_component_decomposition (F.slice (F.event T hT).tMinus) hcompact
  let kind : Fin n → SurgerySummandKind := fun i =>
    if r i ∈ (F.event T hT).retained_pre then .survivor else
      if Nonempty (SurgerySphereBundle
        (componentCarrier (F.slice (F.event T hT).tMinus) (r i))) then
        .sphereBundle else .spaceform
  have hsurvivor (i : Fin n) : kind i = .survivor ↔
      r i ∈ (F.event T hT).retained_pre := by
    by_cases hi : r i ∈ (F.event T hT).retained_pre
    · simp [kind, hi]
    · simp only [kind, if_neg hi]
      split <;> simp_all
  have hpost (y : (F.slice T).carrier) : y ∈ (F.event T hT).retained_post := by
    rw [zero_cap_retained_post F T hT hcount]
    exact Set.mem_univ y
  let C : SurgeryTopologyConclusion (F.slice (F.event T hT).tMinus) (F.slice T) := {
    piece_count := n
    piece := fun i => componentCarrier (F.slice (F.event T hT).tMinus) (r i)
    piece_compact := fun i =>
      componentCarrier_compact (F.slice (F.event T hT).tMinus) hcompact (r i)
    piece_connected := fun i =>
      componentCarrier_connected (F.slice (F.event T hT).tMinus) (r i)
    kind := kind
    survivor_region := fun i => (F.event T hT).retention.map '' D.region i
    survivor := fun i hi => by
      have hr := (hsurvivor i).mp hi
      rw [hregion i, zero_cap_component_image F T hT hcount hr]
      exact zeroCapSurvivorEquivalence F T hT hcount (r i) hr
    survivor_component := fun i hi => by
      refine ⟨(F.event T hT).retention.map (r i), ?_⟩
      rw [hregion i, zero_cap_component_image F T hT hcount ((hsurvivor i).mp hi)]
    survivor_cover := by
      apply Set.eq_univ_of_forall
      intro y
      let x := (F.event T hT).retention.inverse y
      have hxret : x ∈ (F.event T hT).retained_pre :=
        (F.event T hT).retention.inverse_image.subset (Set.mem_image_of_mem _ (hpost y))
      have hxcover : x ∈ ⋃ i, D.region i := by
        rw [D.cover]
        exact Set.mem_univ x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
      have hxcomp : x ∈ connectedComponent (r i) := (hregion i).subset hi
      have hrcomp : r i ∈ connectedComponent x := by
        rw [← connectedComponent_eq hxcomp]
        exact mem_connectedComponent
      have hrret := (zero_cap_retained_clopen F T hT hcount).connectedComponent_subset
        hxret hrcomp
      exact Set.mem_iUnion.mpr ⟨⟨i, (hsurvivor i).mpr hrret⟩,
        ⟨x, hi, (F.event T hT).retention.right_inverse (hpost y)⟩⟩
    survivor_disjoint := fun i j hij hi hj => by
      apply Set.disjoint_left.mpr
      rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
      have hxret := zero_cap_component_retained F T hT hcount ((hsurvivor i).mp hi)
        ((hregion i).subset hx)
      have hyret := zero_cap_component_retained F T hT hcount ((hsurvivor j).mp hj)
        ((hregion j).subset hy)
      have hxy := (F.event T hT).retention.left_inverse.injOn hxret hyret
        (hxz.trans hyz.symm)
      exact Set.disjoint_left.mp (D.pairwise_disjoint i j hij) hx (hxy.symm ▸ hy)
    bundles := fun i hi => by
      have hr : r i ∉ (F.event T hT).retained_pre := by
        intro hr
        simp [kind, hr] at hi
      by_cases hb : Nonempty (SurgerySphereBundle
        (componentCarrier (F.slice (F.event T hT).tMinus) (r i)))
      · exact hb
      · simp [kind, hr, hb] at hi
    spaceforms := fun i hi => by
      have hr : r i ∉ (F.event T hT).retained_pre := by
        intro hr
        simp [kind, hr] at hi
      have hb : ¬ Nonempty (SurgerySphereBundle
          (componentCarrier (F.slice (F.event T hT).tMinus) (r i))) := by
        intro hb
        simp [kind, hr, hb] at hi
      exact (hstandard (r i) hr).resolve_left hb
    reconstruction := {
      initial := F.slice (F.event T hT).tMinus
      disjoint_union := D
      operations := .refl } }
  exact ⟨{
    conclusion := C
    cap_correspondence := { cap_piece := fun i => isEmptyElim i } }⟩

end PoincareConjecture.M38
