import PoincareConjecture.Proofs.M25.Topology3D.Space3.RelativeCapCompression
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood














set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem exists_ball_transport_of_common_cap_germ (A B : BallNeighborhoodChart E F)
    (u : E) (hu : ‖u‖ = 1) (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (hcommon : ∀ᶠ x in 𝓝ˢ {x : E | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ},
      A.chart x = B.chart x)
    {Ω : Set F} (hΩ : IsOpen Ω)
    (hAΩ : A.closedRegion \ (A.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ⊆ Ω)
    (hBΩ : B.closedRegion \ (A.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ⊆ Ω) :
    ∃ G : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) F F ∞,
      (∀ x ∈ closedBall (0 : E) 1, G (A.chart x) = B.chart x) ∧
      G '' A.inside = B.inside ∧
      G '' A.closedRegion = B.closedRegion ∧
      G '' A.boundary = B.boundary ∧
      (∀ y ∈ A.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}, G y = y) ∧
      ∃ K : Set F, IsCompact K ∧
        K ⊆ Ω \ (A.chart '' {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ∧
        ∀ y ∉ K, G y = y := by
  let D : Set E := {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}
  change ∀ᶠ x in 𝓝ˢ D, A.chart x = B.chart x at hcommon
  change A.closedRegion \ (A.chart '' D) ⊆ Ω at hAΩ
  change B.closedRegion \ (A.chart '' D) ⊆ Ω at hBΩ
  have hDball : D ⊆ closedBall (0 : E) 1 :=
    fun _ hx => mem_closedBall_zero_iff.mpr hx.1.le
  have hDA : D ⊆ A.chart.source := hDball.trans A.closedBall_subset_source
  have hDB : D ⊆ B.chart.source := hDball.trans B.closedBall_subset_source
  obtain ⟨V, hV, hDV, hVeq⟩ := eventually_nhdsSet_iff_exists.mp hcommon
  have hcapEq : A.chart '' D = B.chart '' D :=
    image_congr (fun x hx => hVeq x (hDV hx))
  let U := (V ∩ A.chart.source) ∩ B.chart.source
  have hU : IsOpen U := (hV.inter A.chart.open_source).inter B.chart.open_source
  have hDU : D ⊆ U := fun _ hx => ⟨⟨hDV hx, hDA hx⟩, hDB hx⟩
  let W := (A.chart.source ∩ A.chart ⁻¹' Ω) ∩ (B.chart.source ∩ B.chart ⁻¹' Ω)
  have hW : IsOpen W :=
    (A.chart.isOpen_inter_preimage hΩ).inter (B.chart.isOpen_inter_preimage hΩ)
  have hballW : closedBall (0 : E) 1 \ D ⊆ W := by
    intro x hx
    refine ⟨⟨A.closedBall_subset_source hx.1, hAΩ ⟨⟨x, hx.1, rfl⟩, ?_⟩⟩,
      ⟨B.closedBall_subset_source hx.1, hBΩ ⟨⟨x, hx.1, rfl⟩, ?_⟩⟩⟩
    · rintro ⟨z, hz, heq⟩
      have hzx := A.chart.injOn (hDA hz) (A.closedBall_subset_source hx.1) heq
      exact hx.2 (hzx ▸ hz)
    · rw [hcapEq]
      rintro ⟨z, hz, heq⟩
      have hzx := B.chart.injOn (hDB hz) (B.closedBall_subset_source hx.1) heq
      exact hx.2 (hzx ▸ hz)

  obtain ⟨T, _, Φ, hΦ, hzero, _, hfinal, _, C, hC, hCs, hfix⟩ :=
    exists_relative_cap_compression u hu a ha hU hDU hW hballW
  have hCA : C ⊆ A.chart.source := fun _ hx => (hCs hx).1.1.1
  have hCB : C ⊆ B.chart.source := fun _ hx => (hCs hx).1.2.1
  obtain ⟨ΦA, _, _, htrackA, hfixA, hCAcompact, _⟩ :=
    exists_chart_transport_isotopy A.chart A.smooth A.smooth_symm
      Φ hΦ hzero hC hCA hfix
  obtain ⟨ΦB, _, _, htrackB, hfixB, hCBcompact, _⟩ :=
    exists_chart_transport_isotopy B.chart B.smooth B.smooth_symm
      Φ hΦ hzero hC hCB hfix
  let G := (ΦA T).trans (ΦB T).symm
  have hpoint (x : E) (hx : x ∈ closedBall (0 : E) 1) :
      G (A.chart x) = B.chart x := by
    change (ΦB T).symm (ΦA T (A.chart x)) = B.chart x
    rw [htrackA T x (A.closedBall_subset_source hx), hVeq (Φ T x) (hfinal hx).1.1,
      ← htrackB T x (B.closedBall_subset_source hx), (ΦB T).symm_apply_apply]
  have himage (S : Set E) (hS : S ⊆ closedBall (0 : E) 1) :
      G '' (A.chart '' S) = B.chart '' S := by
    rw [← image_comp]
    exact image_congr (fun x hx => hpoint x (hS hx))
  have hcapfix : ∀ y ∈ A.chart '' D, G y = y := by
    rintro y ⟨x, hx, rfl⟩
    rw [hpoint x (hDball hx)]
    exact (hVeq x (hDV hx)).symm
  have hCAΩ : A.chart '' C ⊆ Ω \ (A.chart '' D) := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨(hCs hx).1.1.2, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hzx := A.chart.injOn (hDA hz) (hCA hx) heq
    exact (hCs hx).2 (hzx ▸ hz)
  have hCBΩ : B.chart '' C ⊆ Ω \ (A.chart '' D) := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨(hCs hx).1.2.2, ?_⟩
    rw [hcapEq]
    rintro ⟨z, hz, heq⟩
    have hzx := B.chart.injOn (hDB hz) (hCB hx) heq
    exact (hCs hx).2 (hzx ▸ hz)
  refine ⟨G, hpoint, ?_, ?_, ?_, hcapfix, (A.chart '' C) ∪ (B.chart '' C),
    hCAcompact.union hCBcompact, union_subset hCAΩ hCBΩ, ?_⟩
  · exact himage (ball (0 : E) 1) ball_subset_closedBall
  · exact himage (closedBall (0 : E) 1) subset_rfl
  · exact himage (sphere (0 : E) 1) sphere_subset_closedBall
  · intro y hy
    change (ΦB T).symm (ΦA T y) = y
    rw [hfixA T y (fun h => hy (Or.inl h))]
    exact equiv_symm_fixed_of_fixed (ΦB T).toEquiv
      (hfixB T y (fun h => hy (Or.inr h)))

end PoincareConjecture.M25.Topology3D
