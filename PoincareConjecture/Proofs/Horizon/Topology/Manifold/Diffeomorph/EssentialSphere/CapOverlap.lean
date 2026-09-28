import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.CapStraightening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CylinderPasting
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_second_cap_overlap_model_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), D.epsilon ≤ ε₀ →
          ∀ (U : Opens M), OpenCylinderModel (U : Set M) →
            C.end_neck.carrier ⊆ U →
            Disjoint C.closed_core (U : Set M) → Disjoint D.closed_core C.carrier →
            Disjoint C.closed_core D.carrier →
            IsCompact (C.carrier ∪ (U : Set M) ∪ D.carrier) →
            (frontier (C.carrier ∪ (U : Set M)) ∩ D.core).Nonempty →
            Nonempty (OpenCylinderModel (D.carrier ∩ (U : Set M))) := by
  obtain ⟨ε₀, hε₀, hsmall, hstraight⟩ := exists_second_cap_collar_straightening_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε U T hend hfirst hDC hCD hcompact hencounter
  obtain ⟨s, hs, δ, hδ, hlo, hhi, -, htail, η, hη, -, F, hF,
      hK, hKD, hfront, hunion, hinter, -, -, -, hFside⟩ :=
    hstraight C D hε U T hend hfirst hDC hCD hcompact hencounter
  let K := D.closed_core ∪ closure (D.end_neck.region (-D.epsilon⁻¹) s)
  have hs' : s ∈ Ioo (-D.end_neck.epsilon⁻¹) D.end_neck.epsilon⁻¹ := by
    rw [D.end_neck_epsilon]
    exact ⟨(neg_lt_zero.mpr (inv_pos.mpr D.epsilon_pos)).trans hs.1, hs.2⟩
  obtain ⟨r, G, hr, -, hGaff, hGside⟩ :=
    D.end_neck.exists_affine_neck_coordinates (fun _ => s) contMDiff_const (fun _ => hs')
  have hG (p : RoundCylinderSpace) (hp : |p.2| < r) :
      (G p : M) = D.end_neck.coordinate_map (p.1, s + p.2) := by
    have h := D.end_neck.coordinate_map_coordinate_inverse (G p).property
    rw [hGaff p hp] at h
    exact h.symm
  have hpos (p : RoundCylinderSpace) (hp : 0 < p.2) :
      (G p : M) ∈ D.end_neck.region s D.epsilon⁻¹ := by
    refine ⟨(G p).property, ?_, ?_⟩
    · exact lt_of_not_ge fun h => (not_le_of_gt hp) ((hGside p).mp h)
    · simpa only [D.end_neck_epsilon] using
        (D.end_neck.coordinate_inverse_mem _ (G p).property).2.2
  have havoid : Disjoint K (D.end_neck.region s D.epsilon⁻¹) := by
    have hcl : closure (D.end_neck.region (-D.epsilon⁻¹) s) ⊆
        (D.end_neck.region s D.epsilon⁻¹)ᶜ := by
      apply closure_minimal _ (D.end_neck.isOpen_region s D.epsilon⁻¹).isClosed_compl
      exact fun _ hx hy => lt_asymm hx.2.2 hy.2.1
    apply disjoint_left.mpr
    intro x hx hy
    rcases hx with hc | he
    · exact disjoint_left.mp D.disjoint_closed_core_end hc hy.1
    · exact hcl he hy
  obtain ⟨W, P, -, hW⟩ := Poincare.exists_pasted_cylinder U D.end_neck.carrierOpen
    F G (min η r) (lt_min hη hr)
    (fun p hp => (hF p (hp.trans_le (min_le_left _ _))).trans
      (hG p (hp.trans_le (min_le_right _ _))).symm)
    (fun p q hp hq heq => disjoint_left.mp havoid ((hFside p).mpr hp)
      (heq.symm ▸ hpos q hq))
  have hWexact : (W : Set M) = D.carrier ∩ (U : Set M) := by
    rw [hW]
    apply Subset.antisymm
    · rintro x (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact ⟨hKD ((hFside p).mpr hp), (F p).property⟩
      · have hx := hpos p hp
        exact ⟨D.end_neck_subset hx.1, htail ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩⟩
    · intro x hx
      by_cases hxK : x ∈ K
      · left
        obtain ⟨p, hp⟩ := F.surjective ⟨x, hx.2⟩
        have hp' : (F p : M) = x := congrArg Subtype.val hp
        refine ⟨p, (hFside p).mp ?_, congrArg Subtype.val hp⟩
        change (F p : M) ∈ K
        rw [hp']
        exact hxK
      · right
        have hxtail : x ∈ D.end_neck.region (s - δ) D.epsilon⁻¹ := by
          have h := hunion.le hx
          exact h.resolve_left fun hi => hxK (interior_subset hi.2)
        have hxgt : s < (D.end_neck.coordinate_inverse x).2 := by
          by_contra hn
          rcases lt_or_eq_of_le (le_of_not_gt hn) with hl | he
          · have hreg : x ∈ D.end_neck.region (s - δ) s :=
              ⟨hxtail.1, hxtail.2.1, hl⟩
            exact hxK (interior_subset (hinter.ge hreg).1.2)
          · have hxs : x ∈ frontier K := by
              rw [hfront]
              refine ⟨(D.end_neck.coordinate_inverse x).1, ?_⟩
              rw [← he]
              exact D.end_neck.coordinate_map_coordinate_inverse hxtail.1
            have hclosed : IsClosed K := hK.isClosed
            exact hxK (hclosed.frontier_subset hxs)
        obtain ⟨p, hp⟩ := G.surjective ⟨x, hxtail.1⟩
        have hp' : (G p : M) = x := congrArg Subtype.val hp
        refine ⟨p, ?_, congrArg Subtype.val hp⟩
        have hnot : ¬ (D.end_neck.coordinate_inverse (G p)).2 ≤ s := by
          rw [hp']
          exact not_le.mpr hxgt
        exact lt_of_not_ge fun h => hnot ((hGside p).mpr h)
  obtain ⟨E, -⟩ := D.end_neck.exists_unit_to_real_cylinder
  have model : OpenCylinderModel (W : Set M) :=
    OpenCylinderModel.ofDiffeomorph W (E.trans P)
      (D.end_neck.coordinate_inverse D.end_neck.center).1
  exact ⟨hWexact ▸ model⟩

end PoincareConjecture.CapCertificate
