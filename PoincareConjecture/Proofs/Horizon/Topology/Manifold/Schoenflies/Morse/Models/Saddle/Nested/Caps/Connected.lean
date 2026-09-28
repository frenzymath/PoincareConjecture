import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Regions



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem vector_mem_sphere {x y z : Real} (h : x^2+y^2+z^2=1) :
    vector x y z ∈ sphere (0 : E3) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hn := EuclideanSpace.norm_sq_eq (vector x y z)
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, vector_zero, vector_one, vector_two] at hn
  nlinarith [norm_nonneg (vector x y z)]

theorem southernCap_nonempty : southernCap.Nonempty := by
  refine ⟨⟨vector 0 0 (-1), vector_mem_sphere (by norm_num)⟩, ?_⟩
  change height _ < 1 ∧ (-1 : Real) < separatingLatitude
  rw [height_apply]
  simp only [vector_zero, vector_one, vector_two]
  constructor
  · norm_num
  · linarith [separatingLatitude_bounds.1]

theorem northernCap_nonempty : northernCap.Nonempty := by
  refine ⟨⟨vector (-3/5) 0 (4/5), vector_mem_sphere (by norm_num)⟩, ?_⟩
  change height _ < 1 ∧ separatingLatitude < (4/5 : Real)
  rw [height_apply]
  simp only [vector_zero, vector_one, vector_two]
  constructor
  · norm_num
  · have hu : upperRoot < (7/10 : Real) := by
      dsimp [upperRoot]
      linarith [sqrt_nineteen_bounds.2]
    linarith [separatingLatitude_bounds.2]

theorem upperCap_nonempty : upperCap.Nonempty := by
  refine ⟨⟨vector (4/5) 0 (3/5), vector_mem_sphere (by norm_num)⟩, ?_⟩
  change 13/10 < height _
  rw [height_apply]
  norm_num

private theorem connected_of_two_complementary_regions
    {X : Type*} [TopologicalSpace X] {C U : Set X}
    (hU : IsOpen U) (hUC : U ⊆ Cᶜ) (hfront : frontier U ⊆ C)
    (hne : U.Nonempty) (hout : (Cᶜ \ U).Nonempty)
    (hsep : ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B=Cᶜ) : IsConnected U := by
  obtain ⟨A, B, hA, hB, hdis, hcover⟩ := hsep
  have hside (V : Set X) (hV : IsConnected V) (hVC : V ⊆ Cᶜ)
      (hVU : (V ∩ U).Nonempty) : V ⊆ U := by
    rw [← hU.interior_eq]
    apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hV.2
      (disjoint_left.mpr (fun x hx hxf => hVC hx (hfront hxf)))
    rwa [hU.interior_eq]
  have hAC : A ⊆ Cᶜ := fun x hx => hcover.subset (Or.inl hx)
  have hBC : B ⊆ Cᶜ := fun x hx => hcover.subset (Or.inr hx)
  have hsolve (V W : Set X) (hV : IsConnected V) (hW : IsConnected W)
      (hVC : V ⊆ Cᶜ) (hWC : W ⊆ Cᶜ) (hcover' : V ∪ W=Cᶜ)
      (hVU : (V ∩ U).Nonempty) : U=V := by
    have hsub := hside V hV hVC hVU
    apply Subset.antisymm
    · intro x hx
      rcases hcover'.superset (hUC hx) with hVx | hWx
      · exact hVx
      · have hWsub := hside W hW hWC ⟨x, hWx, hx⟩
        obtain ⟨q, hqC, hqU⟩ := hout
        exact (hqU ((hcover'.superset hqC).elim (fun h => hsub h) (fun h => hWsub h))).elim
    · exact hsub
  obtain ⟨p, hp⟩ := hne
  rcases hcover.superset (hUC hp) with hpa | hpb
  · exact (hsolve A B hA hB hAC hBC hcover ⟨p, hpa, hp⟩) ▸ hA
  · exact (hsolve B A hB hA hBC hAC (by rw [union_comm, hcover]) ⟨p, hpb, hp⟩) ▸ hB

private theorem regular_circle_regions {c : Real} {C : Set S2}
    (hc : ∀ p, height p=c → mfderiv (𝓡 2) 𝓘(Real, Real) height p ≠ 0)
    (hne : C.Nonempty) (hC : C ⊆ height ⁻¹' {c})
    (hcomponent : ∀ p ∈ C, connectedComponentIn (height ⁻¹' {c}) p=C) :
    ∃ A B : Set S2, IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧ A ∪ B=Cᶜ := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨A, B, _, _, hA, hB, hd, hcover, _⟩ :=
    exists_regular_level_component_complementary_regions height_contMDiff finite_critical_points
      c hc p (hC hp)
  rw [hcomponent p hp] at hcover
  exact ⟨A, B, hA, hB, hd, hcover⟩

theorem isConnected_southernCap : IsConnected southernCap := by
  have hC : outerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_left
  apply connected_of_two_complementary_regions isOpen_southernCap
    (fun p hp hc => (ne_of_lt hp.1) (hC hc)) frontier_southernCap_subset southernCap_nonempty
  · obtain ⟨p, hp⟩ := upperCap_nonempty
    exact ⟨p, (fun h => by have := hC h; change height p=1 at this; dsimp [upperCap] at hp; linarith),
      fun h => by have := h.1; dsimp [upperCap] at hp; linarith⟩
  · exact regular_circle_regions height_one_regular isConnected_outerSourceCircle.nonempty hC
      (fun p hp => connectedComponentIn_lower_of_mem_outer hp)

theorem isConnected_northernCap : IsConnected northernCap := by
  have hC : innerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_right
  apply connected_of_two_complementary_regions isOpen_northernCap
    (fun p hp hc => (ne_of_lt hp.1) (hC hc)) frontier_northernCap_subset northernCap_nonempty
  · obtain ⟨p, hp⟩ := upperCap_nonempty
    exact ⟨p, (fun h => by have := hC h; change height p=1 at this; dsimp [upperCap] at hp; linarith),
      fun h => by have := h.1; dsimp [upperCap] at hp; linarith⟩
  · exact regular_circle_regions height_one_regular isConnected_innerSourceCircle.nonempty hC
      (fun p hp => connectedComponentIn_lower_of_mem_inner hp)

theorem isConnected_upperCap : IsConnected upperCap := by
  apply connected_of_two_complementary_regions isOpen_upperCap
    (fun p hp hc => (ne_of_gt hp) hc) frontier_upperCap_subset upperCap_nonempty
  · obtain ⟨p, hp⟩ := southernCap_nonempty
    exact ⟨p, (fun h => by change height p=13/10 at h; have := hp.1; linarith),
      fun h => by have := hp.1; dsimp [upperCap] at h; linarith⟩
  · apply regular_circle_regions
      (fun p hp => nested_cutting_heights_regular p (Or.inr hp))
      isConnected_upper_height_level.nonempty subset_rfl
    intro p hp
    exact Subset.antisymm (connectedComponentIn_subset _ _)
      (isConnected_upper_height_level.2.subset_connectedComponentIn hp subset_rfl)

end Poincare.Manifold.Schoenflies.Saddle.Nested
