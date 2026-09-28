import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Annulus.Coordinates
import PoincareConjecture.Proofs.M76.Mathlib.CoveringPLAtlas
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation
import Mathlib.Topology.Homotopy.Lifting











set_option autoImplicit false

open Set Metric Geometry Topology
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

private theorem interval_coordinate_bounds (x : closedBall (0 : V1) 1) :
    -1 ≤ (x : V1) 0 ∧ (x : V1) 0 ≤ 1 := by
  have hx : ‖(x : V1)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  exact abs_le.mp ((norm_le_pi_norm (x : V1) 0).trans hx)


noncomputable def cylinder : (unitInterval × Q2) ≃ₜ source where
  toFun p := ⟨((fun _ : Fin 1 ↦ 2 * (p.1 : ℝ) - 1), p.2), by
    refine ⟨?_, p.2.property⟩
    rw [mem_closedBall, dist_zero_right, pi_norm_const, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩⟩
  invFun x := (⟨((x : V1 × V2).1 0 + 1) / 2, by
    have hx := interval_coordinate_bounds ⟨(x : V1 × V2).1, x.property.1⟩
    constructor <;> linarith⟩, ⟨(x : V1 × V2).2, x.property.2⟩)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change (2 * (p.1 : ℝ) - 1 + 1) / 2 = (p.1 : ℝ)
      ring
    · rfl
  right_inv x := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change 2 * (((x : V1 × V2).1 0 + 1) / 2) - 1 = (x : V1 × V2).1 0
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem cylinder_zero (u : Q2) : cylinder (0, u) =
    ⟨(endpoint false, u), sphere_subset_closedBall (endpoint_mem_sphere false), u.property⟩ := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  funext i
  change 2 * (0 : ℝ) - 1 = -1
  norm_num

theorem cylinder_one (u : Q2) : cylinder (1, u) =
    ⟨(endpoint true, u), sphere_subset_closedBall (endpoint_mem_sphere true), u.property⟩ := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  funext i
  change 2 * (1 : ℝ) - 1 = 1
  norm_num



theorem exists_source_lift
    {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    {p : X → M} (hp : IsCoveringMap p)
    (F : C(source, M)) (negative : C(Q2, X))
    (hnegative : ∀ u : Q2, p (negative u) =
      F ⟨(endpoint false, u), sphere_subset_closedBall (endpoint_mem_sphere false), u.property⟩) :
    ∃ G : C(source, X), (∀ x, p (G x) = F x) ∧
      ∀ u : Q2,
        G ⟨(endpoint false, u), sphere_subset_closedBall (endpoint_mem_sphere false), u.property⟩ =
          negative u := by
  let H : C(unitInterval × Q2, M) := F.comp ⟨cylinder, cylinder.continuous⟩
  have hzero (u : Q2) : H (0, u) = p (negative u) := by
    change F (cylinder (0, u)) = _
    rw [cylinder_zero]
    exact (hnegative u).symm
  let lift := hp.liftHomotopy H negative hzero
  let G : C(source, X) := lift.comp ⟨cylinder.symm, cylinder.symm.continuous⟩
  refine ⟨G, ?_, ?_⟩
  · intro x
    have hv := congrFun (hp.liftHomotopy_lifts H negative hzero) (cylinder.symm x)
    change p (G x) = F (cylinder (cylinder.symm x)) at hv
    simpa only [cylinder.apply_symm_apply] using hv
  · intro u
    rw [← cylinder_zero]
    change lift (cylinder.symm (cylinder (0, u))) = negative u
    rw [cylinder.symm_apply_apply]
    exact hp.liftHomotopy_zero H negative hzero u



theorem exists_source_triangulation :
    ∃ K : SimplicialComplex ℝ (V1 × V2), K.faces.Finite ∧ K.space = source := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    Set.isFinitePLBallPair_unit_cube (ι := Fin 1)
  let J := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hJ : J.faces.Finite :=
    squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hJs : J.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  obtain ⟨A, hA, hAs, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  exact ⟨A, hA, hAs.trans (by rw [hKs, hJs]; rfl)⟩



theorem exists_polyhedralPL_source_lift
    {E M X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [TopologicalSpace X]
    {p : X → M} (hp : IsCoveringMap p)
    {c : ι → OpenPartialHomeomorph M E}
    (d : ι × X → OpenPartialHomeomorph X E)
    (hcenter : ∀ i x, p x ∈ (c i).source → x ∈ (d (i, x)).source)
    (hval : ∀ k, EqOn (d k) ((c k.1) ∘ p) (d k).source)
    {f : (V1 × V2) → M} (hf : PolyhedralPLInCharts c f source)
    (negative : C(Q2, X))
    (hnegative : ∀ u : Q2, p (negative u) = f (endpoint false, u)) :
    ∃ g : (V1 × V2) → X, PolyhedralPLInCharts d g source ∧
      EqOn (p ∘ g) f source ∧
      ∀ u : Q2, g (endpoint false, u) = negative u := by
  classical
  let F : C(source, M) := ⟨fun x ↦ f x, hf.continuousOn.domRestrict⟩
  obtain ⟨G, hG, hGnegative⟩ := exists_source_lift hp F negative hnegative
  let g : (V1 × V2) → X := fun x ↦
    if hx : x ∈ source then G ⟨x, hx⟩ else negative squareRimBase
  have hg (x : source) : g x = G x := by simp only [g, dif_pos x.property]
  have hgc : ContinuousOn g source := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact G.continuous.congr (fun x ↦ (hg x).symm)
  have hpg : EqOn (p ∘ g) f source := by
    intro x hx
    change p (g x) = f x
    rw [hg ⟨x, hx⟩]
    exact hG ⟨x, hx⟩
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  have hgPL : PolyhedralPLInCharts d g K.space :=
    (hKs.symm ▸ hf).lift d hcenter hval K hK (hKs.symm ▸ hgc) (hKs.symm ▸ hpg)
  refine ⟨g, hKs ▸ hgPL, hpg, ?_⟩
  intro u
  rw [hg ⟨(endpoint false, u),
    sphere_subset_closedBall (endpoint_mem_sphere false), u.property⟩]
  exact hGnegative u

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
