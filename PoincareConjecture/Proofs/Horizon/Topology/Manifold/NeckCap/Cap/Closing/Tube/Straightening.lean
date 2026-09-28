import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.Straightening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.CompactCut

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapTubeAttachment

theorem exists_tube_collar_straightening_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {X : Set M},
        ∀ {C : CapCertificate g} {T : EpsilonTubeCertificate g X} {side : Bool},
          CapTubeAttachment C T side → C.epsilon ≤ ε₀ →
          let U : Opens M := ⟨C.carrier, C.carrier_open⟩
          let V : Opens M := ⟨T.carrier, T.carrier_open⟩
          ∃ s ∈ Ioo 0 C.epsilon⁻¹, ∃ δ : ℝ,
            0 < δ ∧ 0 < s - δ ∧ s + δ < C.epsilon⁻¹ ∧
            C.end_neck.region (s - δ) C.epsilon⁻¹ ⊆ (U ⊓ V : Opens M) ∧
            ∃ r : ℝ, 0 < r ∧ r < δ ∧
            ∃ (F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
                RoundCylinderSpace (U ⊓ V : Opens M) ∞)
              (G : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace V ∞),
              (∀ p : RoundCylinderSpace, |p.2| < r →
                (F p : M) = C.end_neck.coordinate_map (p.1, s + p.2)) ∧
              (∀ p : RoundCylinderSpace, |p.2| < r →
                (G p : M) = C.end_neck.coordinate_map (p.1, s + p.2)) ∧
              let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
              IsCompact K ∧ K ⊆ C.carrier ∧ C.closed_core ⊆ interior K ∧
                frontier K = range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, s)) ∧
                C.carrier \ K ⊆ (U ⊓ V : Opens M) ∧
                ((U ⊓ V : Opens M) : Set M) \ K = C.end_neck.region s C.epsilon⁻¹ ∧
                (∀ p : RoundCylinderSpace, (F p : M) ∈ interior K ↔ p.2 < 0) ∧
                (∀ p : RoundCylinderSpace, (F p : M) ∈ K ↔ p.2 ≤ 0) ∧
                (∀ p : RoundCylinderSpace, (G p : M) ∈ interior K ↔ p.2 < 0) ∧
                ∀ p : RoundCylinderSpace, (G p : M) ∈ K ↔ p.2 ≤ 0 := by
  obtain ⟨ε₁, hε₁, hsmall, hstraight⟩ := exists_collar_straightening_threshold.{u}
  obtain ⟨ε₂, hε₂, _, htrunc⟩ := CapCertificate.exists_truncated_core_domain_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g X C T side A hC
  let U : Opens M := ⟨C.carrier, C.carrier_open⟩
  let V : Opens M := ⟨T.carrier, T.carrier_open⟩
  obtain ⟨s, hs, δ, hδ, hlo, hhi, htail, η, hη, hηδ, F, hFval,
      hK, hKC, hcore, hfront, hUdiff, hFnegative, hFclosed, _⟩ :=
    hstraight A (hC.trans (min_le_left _ _))
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  obtain ⟨_, _, hint, _, _, _⟩ := htrunc C (hC.trans (min_le_right _ _)) s
    ⟨(neg_lt_zero.mpr hR).trans hs.1, hs.2⟩
  have hcollar : C.end_neck.region (s - δ) (s + δ) ⊆ T.carrier := by
    intro x hx
    exact (htail ⟨hx.1, hx.2.1, hx.2.2.trans hhi⟩).2
  obtain ⟨hcL, hcR, hcover, _, _⟩ := C.truncated_sides_components
    T.carrier_open T.cylinder.isConnected_carrier hK.isClosed hδ
    ((neg_lt_zero.mpr hR).trans hlo) hhi hcollar hint hfront
  have hescape := T.cylinder.compact_cut_sides_escape U V hK hKC
    F.toHomeomorph hFclosed hFnegative
  have hlo' : -C.end_neck.epsilon⁻¹ < s - δ := by
    rw [C.end_neck_epsilon]
    exact (neg_lt_zero.mpr hR).trans hlo
  have hhi' : s + δ < C.end_neck.epsilon⁻¹ := by rwa [C.end_neck_epsilon]
  obtain ⟨c, hcs, hct, hc, hci, hcval⟩ := C.end_neck.exists_slice_collar hlo' hhi'
  obtain ⟨E, _⟩ := C.end_neck.exists_unit_to_real_cylinder
  let J := E.symm.trans (T.cylinder.toDiffeomorph V)
  have hS : range (fun q : UnitTwoSphere => c (q, 0)) =
      range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, s)) := by
    congr 1
    funext q
    simpa only [add_zero] using hcval (q, 0)
  obtain ⟨σ, hσ, hσδ, G, hG⟩ := Poincare.exists_essential_sphere_collar_extension_in_open
    V J hδ c hcs (hct ▸ hcollar) hc hci (T.carrier ∩ interior K) (T.carrier \ K)
    (T.carrier_open.inter isOpen_interior) (T.carrier_open.inter hK.isClosed.isOpen_compl)
    hcL hcR (disjoint_left.mpr fun _ hx hy => hy.2 (interior_subset hx.2))
    (by rw [hS, ← hfront]; exact hcover) hescape
  have hGval (p : RoundCylinderSpace) (hp : |p.2| < σ) :
      (G p : M) = C.end_neck.coordinate_map (p.1, s + p.2) :=
    (hG p hp).trans (hcval p)
  have hGzero : range (fun q : UnitTwoSphere => (G (q, 0) : M)) = frontier K := by
    rw [hfront]
    congr 1
    funext q
    simpa only [add_zero] using hGval (q, 0) (by simpa using hσ)
  let q := (C.end_neck.coordinate_inverse C.end_neck.center).1
  let p₀ : RoundCylinderSpace := (q, -σ / 2)
  have hp₀ : p₀.2 < 0 := by dsimp [p₀]; linarith
  have hpσ : |p₀.2| < σ := by rw [abs_of_neg hp₀]; dsimp [p₀]; linarith
  have hseed : (G p₀ : M) ∈ T.carrier ∩ interior K := by
    refine ⟨(G p₀).property, ?_⟩
    rw [hint]
    apply Or.inr
    rw [hGval p₀ hpσ]
    have hdom : (q, s + p₀.2) ∈ C.end_neck.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, C.end_neck_epsilon]
      refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp [p₀] <;> linarith
    refine ⟨C.end_neck.coordinate_map_mem hdom, ?_⟩
    rw [C.end_neck.coordinate_inverse_coordinate_map hdom]
    constructor <;> dsimp [p₀] <;> linarith
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  obtain ⟨hleft, hright⟩ := Poincare.Topology.cylinder_sides_of_negative_witness
    V G.toHomeomorph (T.carrier_open.inter isOpen_interior)
    (T.carrier_open.inter hK.isClosed.isOpen_compl) hcL.isPreconnected
    (disjoint_left.mpr fun _ hx hy => hy.2 (interior_subset hx.2))
    (hGzero.symm ▸ hcover) hp₀ hseed
  have houtside : C.carrier \ K ⊆ (U ⊓ V : Opens M) := by
    intro x hx
    have hxend := (C.carrier_eq_closed_core_union_end ▸ hx.1).resolve_left
      (fun h => hx.2 (Or.inl h))
    have hz := (C.end_neck.coordinate_inverse_mem x hxend).2
    rw [C.end_neck_epsilon] at hz
    have hxs : s ≤ (C.end_neck.coordinate_inverse x).2 := by
      by_contra h
      exact hx.2 (Or.inr (subset_closure ⟨hxend, hz.1, lt_of_not_ge h⟩))
    exact htail ⟨hxend, by linarith, hz.2⟩
  let r := min η σ
  have hr : 0 < r := lt_min hη hσ
  refine ⟨s, hs, δ, hδ, hlo, hhi, htail, r, hr,
    (min_le_left _ _).trans_lt hηδ, F, G,
    (fun p hp => hFval p (hp.trans_le (min_le_left _ _))),
    (fun p hp => hGval p (hp.trans_le (min_le_right _ _))),
    hK, hKC, hcore, hfront, houtside, hUdiff, hFnegative, hFclosed, ?_, ?_⟩
  · intro p
    exact (and_iff_right (G p).property).symm.trans (hleft p)
  · intro p
    have h : (G p : M) ∉ K ↔ 0 < p.2 :=
      (and_iff_right (G p).property).symm.trans (hright p)
    simpa only [not_not, not_lt] using not_congr h

end PoincareConjecture.CapTubeAttachment
