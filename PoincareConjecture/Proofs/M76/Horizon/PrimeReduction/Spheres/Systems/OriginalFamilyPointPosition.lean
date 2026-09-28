import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ChartCarrier
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartSurfacePosition
import PoincareConjecture.Proofs.M76.PrimeReduction.SphereAmbientTransport
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes








set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_sphere_system_point_avoiding_motion
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hU : IsOpen U) {p : X} (hp : p ∈ U) :
    ∃ (G : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ U ∧ EqOn G id Cᶜ ∧
      (∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (G '' S i)) ∧ p ∉ G '' (⋃ i, S i) := by
  classical
  obtain ⟨i, hpi⟩ := hcover p
  let B := e i
  let O := B '' (U ∩ B.source)
  have hO : IsOpen O := B.isOpen_image_of_subset_source
    (hU.inter B.open_source) inter_subset_right
  have hpO : B p ∈ O := ⟨p, ⟨hp, hpi⟩, rfl⟩
  obtain ⟨r, J, hr, hJ, hJs, hJO, _, _⟩ :=
    SimplicialComplex.exists_nested_finite_coordinate_cubes hO hpO
  have hJB : J.space ⊆ B.target := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hJO hx
    exact B.map_source hy.2
  have hpJ : B p ∈ interior J.space := by
    rw [hJs]
    exact ball_subset_interior_closedBall (mem_ball_self (by positivity : 0 < 3 * r))
  have hcv : Convex ℝ J.space := hJs.symm ▸ convex_closedBall (B p) (3 * r)
  obtain ⟨P, hP, hPs, hPc, hlocal, _⟩ := exists_finite_sphere_system_chart_carrier S sS hdis B (fun j => he j i) J hJ hJB
  have hPJ : P.space ⊆ J.space := hPs.subset.trans inter_subset_right
  obtain ⟨D, hD, hDs⟩ := J.exists_finite_convex_frontier_triangulation hJ hcv
  obtain ⟨P0, hP0, hP0s⟩ := P.exists_finite_triangulation_inter D hP hD
  have hP0eq : P0.space = P.space ∩ frontier J.space := by rw [hP0s, hDs]
  obtain ⟨T, hT, hTs⟩ :=
    SimplicialComplex.exists_finite_coordinate_closedBall (B p) (le_refl (0 : ℝ))
  have hTpoint : T.space = {B p} := by simpa only [closedBall_zero] using hTs
  have hTv : T.vertices ⊆ {B p} := T.vertices_subset_space.trans hTpoint.subset
  have hpT : B p ∈ T.vertices := by
    obtain ⟨a, ha, _⟩ := SimplicialComplex.mem_space_iff.mp
      (hTpoint.symm.subset (mem_singleton (B p)))
    obtain ⟨v, hv⟩ := T.nonempty_of_mem_faces ha
    have hvT : v ∈ T.vertices := T.down_closed ha
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact (mem_singleton_iff.mp (hTv hvT)) ▸ hvT
  have hTc (a : Finset V3) (ha : a ∈ T.faces) : a.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact (mem_singleton_iff.mp (hTpoint.subset (T.subset_space ha hx))).trans
      (mem_singleton_iff.mp (hTpoint.subset (T.subset_space ha hy))).symm
  have hprot : Disjoint P0.space T.vertices := by
    apply disjoint_left.mpr
    intro x hx hxt
    have hxp : x = B p := mem_singleton_iff.mp (hTv hxt)
    have hxfront : x ∈ frontier J.space := (hP0eq.subset hx).2
    exact disjoint_left.mp disjoint_interior_frontier hpJ (hxp ▸ hxfront)
  obtain ⟨_, A, G, _, _, _, _, hAv, _, _, _, hGout, _, hGPL, hGinv, hGA, _⟩ :=
    exists_original_chart_surface_position (by simp) e he B (fun j => he j i)
      J P P0 T hJ hP hP0 hT hcv (hP0eq.subset.trans inter_subset_left)
      hPJ hJB (fun _ hx => hP0eq.symm.subset hx) hPc hprot
      (by intro a ha hac; have h := hTc a ha; omega) (⋃ i, S i) hlocal zero_lt_one
  let C := B.symm '' J.space
  have hC : IsCompact C := (J.isCompact_space_of_finite hJ).image_of_continuousOn
    (B.symm.continuousOn.mono hJB)
  have hCU : C ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hJO hx
    rw [B.left_inv hy.2]
    exact hy.1
  refine ⟨G, C, hC, hCU, hGout, hGPL, hGinv, ⟨fun i => Classical.choice ((sS i).nonempty_image G hcover hGPL)⟩, ?_⟩
  intro hpG
  have hBpG : B.symm (B p) ∈ G '' (⋃ i, S i) := by simpa only [B.left_inv hpi] using hpG
  exact disjoint_left.mp hAv ((hGA (B p) (interior_subset hpJ)).mp hBpG) hpT

end PoincareConjecture.M76

