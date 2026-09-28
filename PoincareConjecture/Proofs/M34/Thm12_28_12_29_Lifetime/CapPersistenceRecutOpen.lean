import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCollarSides












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)


def recutCarrier (b : ℝ) : Set M :=
  N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b


theorem recutCarrier_subset_carrier (b : ℝ) : N.recutCarrier b ⊆ N.carrier := by
  intro x hx
  exact hx.elim (fun hy => N.closed_core_subset_carrier hy) (fun he => N.end_neck_subset he.1)



theorem recutCarrier_sdiff_end (b : ℝ) :
    N.recutCarrier b \ N.end_neck.region (-N.epsilon⁻¹) b = N.closed_core := by
  ext x
  constructor
  · rintro ⟨hx, hxend⟩
    exact hx.elim id (fun h => False.elim (hxend h))
  · intro hx
    refine ⟨Or.inl hx, ?_⟩
    intro he
    rw [N.closed_core_eq_complement_end] at hx
    exact hx.2 he.1




theorem recutCarrier_isOpen {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) : IsOpen (N.recutCarrier b) := by
  have hbN : -N.end_neck.epsilon⁻¹ < b := by rwa [N.end_neck_epsilon]
  have hbN' : b < N.end_neck.epsilon⁻¹ := by rwa [N.end_neck_epsilon]
  let K := N.end_neck.coordinate_map '' (univ ×ˢ Icc b b)
  have hK : IsCompact K := N.end_neck.isCompact_image_closed_axial_interval hbN hbN'
  have hKend : K ⊆ N.end_neck.carrier :=
    N.end_neck.image_closed_axial_interval_subset_carrier hbN hbN'
  have hSK : N.boundary_neck.central_sphere ⊆ Kᶜ := by
    intro x hx hxK
    have hy := N.boundary_subset_closed_core (N.boundary_eq_neck_sphere.symm ▸ hx)
    rw [N.closed_core_eq_complement_end] at hy
    exact hy.2 (hKend hxK)
  obtain ⟨r, hr, hrN, hstripK⟩ :=
    N.boundary_neck.exists_centered_region_subset_open hK.isClosed.isOpen_compl hSK
  have he : 0 < N.boundary_neck.epsilon⁻¹ := inv_pos.mpr N.boundary_neck.epsilon_pos
  have hcentral {x : M} (hx : x ∈ N.boundary_neck.carrier)
      (hz : (N.boundary_neck.coordinate_inverse x).2 = 0) : x ∈ N.closed_core := by
    apply N.boundary_subset_closed_core
    rw [N.boundary_eq_neck_sphere]
    exact (N.boundary_neck.mem_central_sphere_iff_of_mem hx).mpr hz
  have hhalves {x : M} (hx : x ∈ N.boundary_neck.region (-r) r)
      (hxe : x ∈ N.end_neck.carrier) :
      x ∈ N.boundary_neck.region (-r) 0 ∪ N.boundary_neck.region 0 r := by
    have hn : (N.boundary_neck.coordinate_inverse x).2 ≠ 0 := by
      intro hzero
      have hy := hcentral hx.1 hzero
      rw [N.closed_core_eq_complement_end] at hy
      exact hy.2 hxe
    exact (lt_or_gt_of_ne hn).elim
      (fun hs => Or.inl ⟨hx.1, hx.2.1, hs⟩)
      (fun hs => Or.inr ⟨hx.1, hs, hx.2.2⟩)
  have hcB : N.boundary_neck.center ∈ N.boundary_sphere :=
    N.boundary_eq_neck_sphere.symm ▸ N.boundary_neck.center_on_central_sphere
  have hcN := N.boundary_neck.central_sphere_subset N.boundary_neck.center_on_central_sphere
  have hc0 := (N.boundary_neck.mem_central_sphere_iff_of_mem hcN).mp
    N.boundary_neck.center_on_central_sphere
  have hc : N.boundary_neck.center ∈ N.boundary_neck.region (-r) r := by
    exact ⟨hcN, by rw [hc0]; exact neg_neg_of_pos hr, by rw [hc0]; exact hr⟩
  obtain ⟨y, hystrip, hyinner⟩ := mem_closure_iff.mp
    (N.boundary_subset_inner_end_closure hb hcB)
    _ (N.boundary_neck.region_isOpen (-r) r) hc
  have hinner {S : Set M} (hS : IsPreconnected S)
      (hSS : S ⊆ N.boundary_neck.region (-r) r) (hSE : S ⊆ N.end_neck.carrier)
      (hbelow : ∃ x ∈ S, (N.end_neck.coordinate_inverse x).2 < b) :
      S ⊆ N.end_neck.region (-N.epsilon⁻¹) b := by
    have hheight := N.end_neck.coordinate_inverse_smooth.continuousOn.snd.mono hSE
    have hne : ∀ x ∈ S, (N.end_neck.coordinate_inverse x).2 ≠ b := by
      intro x hx hxb
      apply hstripK (hSS hx)
      refine ⟨N.end_neck.coordinate_inverse x, ⟨mem_univ _, ?_, ?_⟩,
        N.end_neck.coordinate_map_coordinate_inverse (hSE hx)⟩ <;> rw [hxb]
    intro x hx
    have hlow := (N.end_neck.coordinate_inverse_mem x (hSE hx)).2.1
    rw [N.end_neck_epsilon] at hlow
    exact ⟨hSE hx, hlow, hS.gt_of_ne hheight hne hbelow hx⟩
  have hstrip : N.boundary_neck.region (-r) r ⊆ N.recutCarrier b := by
    rcases N.boundary_neck_opposite_sides hr hrN with ⟨hAc, hBe⟩ | ⟨hBc, hAe⟩
    · have hyB := (hhalves hystrip hyinner.1).resolve_left
        (fun hyA => Set.disjoint_left.mp N.core_disjoint_end_neck (hAc hyA) hyinner.1)
      have hBi := hinner (N.boundary_neck.region_isPreconnected
        (neg_nonpos.mpr he.le) hrN)
        (fun _ hx => ⟨hx.1, (neg_neg_of_pos hr).trans hx.2.1, hx.2.2⟩)
        hBe ⟨y, hyB, hyinner.2.2⟩
      intro x hx
      rcases lt_trichotomy (N.boundary_neck.coordinate_inverse x).2 0 with hneg | hz | hpos
      · exact Or.inl (interior_subset (N.core_eq_interior_closed_core ▸
          hAc ⟨hx.1, hx.2.1, hneg⟩))
      · exact Or.inl (hcentral hx.1 hz)
      · exact Or.inr (hBi ⟨hx.1, hpos, hx.2.2⟩)
    · have hyA := (hhalves hystrip hyinner.1).resolve_right
        (fun hyB => Set.disjoint_left.mp N.core_disjoint_end_neck (hBc hyB) hyinner.1)
      have hAi := hinner (N.boundary_neck.region_isPreconnected (neg_le_neg hrN) he.le)
        (fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans hr⟩) hAe ⟨y, hyA, hyinner.2.2⟩
      intro x hx
      rcases lt_trichotomy (N.boundary_neck.coordinate_inverse x).2 0 with hneg | hz | hpos
      · exact Or.inr (hAi ⟨hx.1, hx.2.1, hneg⟩)
      · exact Or.inl (hcentral hx.1 hz)
      · exact Or.inl (interior_subset (N.core_eq_interior_closed_core ▸
          hBc ⟨hx.1, hpos, hx.2.2⟩))
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  rcases hx with hxY | hxE
  · by_cases hi : x ∈ interior N.closed_core
    · exact mem_of_superset (isOpen_interior.mem_nhds hi)
        (fun _ h => Or.inl (interior_subset h))
    · have hxB : x ∈ N.boundary_sphere :=
        N.core_frontier_eq_boundary ▸
          (show x ∈ frontier N.closed_core from ⟨subset_closure hxY, hi⟩)
      have hxS : x ∈ N.boundary_neck.central_sphere := N.boundary_eq_neck_sphere ▸ hxB
      have hxN := N.boundary_neck.central_sphere_subset hxS
      have hx0 := (N.boundary_neck.mem_central_sphere_iff_of_mem hxN).mp hxS
      have hxstrip : x ∈ N.boundary_neck.region (-r) r := by
        exact ⟨hxN, by rw [hx0]; exact neg_neg_of_pos hr, by rw [hx0]; exact hr⟩
      exact mem_of_superset ((N.boundary_neck.region_isOpen (-r) r).mem_nhds hxstrip) hstrip
  · exact mem_of_superset ((N.end_neck.region_isOpen (-N.epsilon⁻¹) b).mem_nhds hxE)
      (fun _ h => Or.inr h)

end PoincareConjecture.CapCertificate
