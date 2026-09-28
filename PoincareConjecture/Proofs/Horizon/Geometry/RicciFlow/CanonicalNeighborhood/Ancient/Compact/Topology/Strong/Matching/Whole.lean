import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.TruncatedDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CompactKappa

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] {g : RiemannianMetric 3 M}

omit [T2Space M] [ConnectedSpace M] in
private theorem mem_closure_cap_end_region_iff (C : CapCertificate g) {a b : ℝ}
    (hab : a < b) {x : M} (hx : x ∈ C.end_neck.carrier) :
    x ∈ closure (C.end_neck.region a b) ↔
      a ≤ (C.end_neck.coordinate_inverse x).2 ∧
        (C.end_neck.coordinate_inverse x).2 ≤ b := by
  have himage : C.end_neck.coordinatePartialHomeomorph.symm.IsImage
      (C.end_neck.region a b) ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) := by
    intro y hy
    change (C.end_neck.coordinate_inverse y).1 ∈ univ ∧
      (C.end_neck.coordinate_inverse y).2 ∈ Ioo a b ↔
        y ∈ C.end_neck.carrier ∧ a < (C.end_neck.coordinate_inverse y).2 ∧
          (C.end_neck.coordinate_inverse y).2 < b
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ C.end_neck.carrier from hy]
  have h := himage.closure.apply_mem_iff hx
  change C.end_neck.coordinate_inverse x ∈ closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) ↔
    x ∈ closure (C.end_neck.region a b) at h
  simpa only [closure_prod_eq, closure_univ, closure_Ioo hab.ne,
    mem_prod, mem_univ, true_and, mem_Icc] using h.symm

private theorem isConnected_truncated_core_compl (C : CapCertificate g)
    {a : ℝ} (ha : a ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹)
    (hK : IsCompact (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)))
    (hfront : frontier (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)) =
      range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, a))) :
    IsConnected (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a))ᶜ := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)
  have heq : Kᶜ ∩ C.end_neck.carrier = C.end_neck.region a C.epsilon⁻¹ := by
    ext x
    constructor
    · rintro ⟨hxK, hxN⟩
      have hdom := (C.end_neck.coordinate_inverse_mem x hxN).2
      rw [C.end_neck_epsilon] at hdom
      refine ⟨hxN, ?_, hdom.2⟩
      by_contra h
      exact hxK (Or.inr ((mem_closure_cap_end_region_iff C ha.1 hxN).mpr
        ⟨hdom.1.le, le_of_not_gt h⟩))
    · intro hx
      refine ⟨?_, hx.1⟩
      rintro (hcore | hclosure)
      · exact disjoint_left.mp C.disjoint_closed_core_end hcore hx.1
      · exact (not_lt_of_ge ((mem_closure_cap_end_region_iff C ha.1 hx.1).mp
          hclosure).2) hx.2.1
  have hinter : IsConnected (Kᶜ ∩ C.end_neck.carrier) := by
    rw [heq]
    apply C.end_neck.isConnected_region
    · simpa only [C.end_neck_epsilon] using ha.1.le
    · rw [C.end_neck_epsilon]
    · exact ha.2
  have hfrontN : frontier Kᶜ ⊆ C.end_neck.carrier := by
    rw [frontier_compl, hfront]
    rintro _ ⟨q, rfl⟩
    exact C.end_neck.coordinate_map_mem
      ⟨mem_univ _, by simpa only [C.end_neck_epsilon] using ha⟩
  have hne : Kᶜ ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := C.core_nonempty
    have hxK : x ∈ Kᶜ := h ▸ mem_univ x
    exact hxK (Or.inl (C.core_subset_closed_core hx))
  exact Poincare.Topology.isConnected_of_inter_of_frontier_subset
    hK.isClosed.isOpen_compl C.end_neck.carrier_open hinter hfrontN hne

theorem exists_whole_cover_of_frontier_in_cap_threshold :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [ConnectedSpace M] {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ epsilonStar →
        ∀ U : Set M, IsOpen U → IsCompact (frontier U) →
          frontier U ⊆ C.carrier → (U \ C.carrier).Nonempty →
          U ∪ C.carrier = univ := by
  obtain ⟨epsilonStar, hpos, hsmall, hdomain⟩ :=
    CapCertificate.exists_truncated_core_domain_threshold.{u}
  refine ⟨epsilonStar, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ g C he U hU hcompact hfront hmeet
  let I := Ioo (-C.epsilon⁻¹) C.epsilon⁻¹
  have hr : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hzero : (0 : ℝ) ∈ I := ⟨neg_lt_zero.mpr hr, hr⟩
  let : Nonempty I := ⟨⟨0, hzero⟩⟩
  let K (a : I) := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a.1)
  have hmono (a b : I) (hab : a.1 ≤ b.1) : K a ⊆ K b := by
    apply union_subset_union_right
    apply closure_mono
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans_le hab⟩
  have hcover : frontier U ⊆ ⋃ a : I, interior (K a) := by
    intro x hx
    rcases C.carrier_eq_closed_core_union_end ▸ hfront hx with hcore | hend
    · apply mem_iUnion.mpr
      exact ⟨⟨0, hzero⟩, (hdomain C he 0 hzero).2.2.2.2.2 hcore⟩
    · have hdom := (C.end_neck.coordinate_inverse_mem x hend).2
      rw [C.end_neck_epsilon] at hdom
      let a := ((C.end_neck.coordinate_inverse x).2 + C.epsilon⁻¹) / 2
      have ha : a ∈ I := by
        change -C.epsilon⁻¹ < a ∧ a < C.epsilon⁻¹
        dsimp [a]
        constructor <;> linarith [hdom.1, hdom.2]
      refine mem_iUnion.mpr ⟨⟨a, ha⟩, ?_⟩
      rw [(hdomain C he a ha).2.2.1]
      exact Or.inr ⟨hend, hdom.1, by dsimp [a]; linarith [hdom.2]⟩
  have hdir : Directed (· ⊆ ·) (fun a : I => interior (K a)) := by
    intro a b
    rcases le_total a.1 b.1 with hab | hba
    · exact ⟨b, interior_mono (hmono a b hab), Subset.rfl⟩
    · exact ⟨a, Subset.rfl, interior_mono (hmono b a hba)⟩
  obtain ⟨a, ha⟩ := hcompact.elim_directed_cover (fun a : I => interior (K a))
    (fun _ => isOpen_interior) hcover hdir
  obtain ⟨hK, hKC, -, hfrontK, -, -⟩ := hdomain C he a.1 a.2
  have hconn := isConnected_truncated_core_compl C a.2 hK hfrontK
  have hdis : Disjoint (K a)ᶜ (frontier U) :=
    disjoint_left.mpr fun x hx hy => hx (interior_subset (ha hy))
  obtain ⟨x, hxU, hxC⟩ := hmeet
  have hsub : (K a)ᶜ ⊆ U := by
    have h := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      hconn.isPreconnected hdis
      ⟨x, fun hxK => hxC (hKC hxK), hU.interior_eq.symm ▸ hxU⟩
    rwa [hU.interior_eq] at h
  apply eq_univ_of_forall
  intro y
  by_cases hy : y ∈ C.carrier
  · exact Or.inr hy
  · exact Or.inl (hsub (fun hyK => hy (hKC hyK)))

end PoincareConjecture.CompactKappa
