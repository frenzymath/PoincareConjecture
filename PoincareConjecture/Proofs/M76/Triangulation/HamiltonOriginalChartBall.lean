import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedRegionRecognition
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {X α : Type*} [TopologicalSpace X] [T2Space X]
  {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D : Set X}

local notation "V3" => (Fin 3 → ℝ)





theorem ChartwisePLSphere.ball_of_original_chart
    (s : ChartwisePLSphere e (frontier D))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hD : IsCompact D) (hne : (interior D).Nonempty)
    (i : α) (hchart : D ⊆ (e i).source) :
    Nonempty (ChartwisePLBall e D (frontier D)) := by
  let c := e i
  have hfrontchart : frontier D ⊆ c.source := hD.isClosed.frontier_subset.trans hchart
  have hcoord : IsCompact (c '' D) := hD.image_of_continuousOn (c.continuousOn.mono hchart)
  have hcoordtarget : c '' D ⊆ c.target := by
    rintro y ⟨x, hx, rfl⟩
    exact c.map_source (hchart hx)
  have himage : c.IsImage D (c '' D) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact c.injOn (hchart hy) hx hyx ▸ hy
    · exact fun hy => mem_image_of_mem c hy
  have hcoordfront : frontier (c '' D) = c '' frontier D := by
    have h := himage.frontier.image_eq
    rw [inter_eq_right.mpr hfrontchart,
      inter_eq_right.mpr (hcoord.isClosed.frontier_subset.trans hcoordtarget)] at h
    exact h.symm
  have hcoordne : (interior (c '' D)).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨c x, (himage.interior.apply_mem_iff (hchart (interior_subset hx))).mpr hx⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKB, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let L := K.frontierSubcomplex (closedBall (0 : V3) 1)
  have hL : L.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hLs : L.space = sphere (0 : V3) 1 := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKB,
      frontier_closedBall _ one_ne_zero]
  have hsPL : FinitePiecewiseAffineOn (c ∘ s.map) (sphere (0 : V3) 1) := by
    rw [← hLs]
    apply (show PolyhedralPLInCharts e s.map L.space from
      hLs.symm ▸ s.piecewiseAffine).finitePiecewiseAffineOn_fixed_chart hcompat L hL i
    intro x hx
    rw [s.map_eq ⟨x, hLs ▸ hx⟩]
    exact hfrontchart (s.parametrization ⟨x, hLs ▸ hx⟩).property
  let sc : frontier D ≃ₜ c '' frontier D :=
    c.homeomorphOfImageSubsetSource hfrontchart rfl
  let sphereMap := s.parametrization.trans sc
  have hsphereMap : sphereMap.IsFinitePL := by
    refine ⟨c ∘ s.map, hsPL, ?_⟩
    intro x
    exact congrArg c (s.map_eq x).symm
  let model := sphereMap.symm.trans (Homeomorph.setCongr
    (frontier_closedBall (0 : V3) one_ne_zero).symm)
  have hmodel : model.IsFinitePL := hsphereMap.symm.setCongr rfl
    (frontier_closedBall (0 : V3) one_ne_zero).symm
  obtain ⟨J, hJ, hJcv, hDJ⟩ := hcoord.exists_finite_convex_neighborhood
  have hJne : (interior J.space).Nonempty :=
    (hcoordne.mono interior_subset).mono hDJ
  have hregions := hmodel.hasAlexanderRegionBalls
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp) (by simp)
    (J.isCompact_space_of_finite hJ) hJcv hJne
    ((image_mono hD.isClosed.frontier_subset).trans hDJ) J hJ rfl
  have hball := hasAlexanderRegionBalls_identifies_closed_region hregions
    hcoord.isClosed hcoordne hcoordfront hDJ
  let q : D ≃ₜ c '' D := c.homeomorphOfImageSubsetSource hchart rfl
  let linear : ((ℝ × ℝ) × ℝ) ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨b, hb, hboundary⟩ := hball.exists_cube_chart linear
  obtain ⟨f, hf, hfeq⟩ := hb.symm
  have hftarget : MapsTo f (closedBall (0 : V3) 1) c.target := by
    intro x hx
    rw [← hfeq ⟨x, hx⟩]
    exact hcoordtarget (b.symm ⟨x, hx⟩).property
  have hPL : PolyhedralPLInCharts e (c.symm ∘ f) (closedBall (0 : V3) 1) := by
    have hf' := hf
    obtain ⟨T, hT, hTs, _⟩ := hf'
    rw [← hTs]
    apply polyhedralPLInCharts_of_one_chart_inverse T hT
      (by simpa only [hTs] using hf) i
    simpa only [hTs] using hftarget
  refine ⟨{
    boundary_subset := hD.isClosed.frontier_subset
    parametrization := b.symm.trans q.symm
    map := c.symm ∘ f
    map_eq := ?_
    piecewiseAffine := hPL
    boundary_eq := ?_
  }⟩
  · intro x
    change c.symm (f x) = c.symm (b.symm x)
    exact congrArg c.symm (hfeq x).symm
  · intro x
    change c.symm (b.symm x) ∈ frontier D ↔ (x : V3) ∈ sphere (0 : V3) 1
    rw [himage.frontier.symm_apply_mem_iff (hcoordtarget (b.symm x).property),
      hcoordfront, hboundary, b.apply_symm_apply, frontier_closedBall _ one_ne_zero]

end PoincareConjecture.M76
