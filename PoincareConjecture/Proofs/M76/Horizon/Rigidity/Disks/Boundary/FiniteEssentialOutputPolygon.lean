import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.EssentialOutputPolygon









set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
open PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)

theorem exists_finite_essential_output_polygon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (j : V2 → E) (hj : FinitePiecewiseAffineOn j D2) (hi : InjOn j D2)
    (rim : C(Q2, T)) (hjb : ∀ x : Q2, j x = (rim x : E))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map rim.continuous)) ≠ 1)
    (hdepth : ∀ x : Q2,
      depth 1 (c.symm (rim x)) ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ)) :
    ∃ (n : ℕ) (P : Polygon P2 (n + 3)), P.HasSimplicialEdges ∧
      Function.Injective P ∧
      P.boundary ℝ = (fun x : Q2 ↦ (c.symm (rim x) : P2)) '' univ ∧
      annulusChartImage c (P.boundary ℝ) = j '' Q2 ∧
      _root_.Dehn.annulusSquare 1 (1 / 8 : ℝ) ⊆ P.inside ∧
      closure P.inside ⊆ interior (_root_.Dehn.annulusSquare 1 (-(1 / 8 : ℝ))) := by
  have hjcopy := hj
  obtain ⟨K, hK, hKs, _⟩ := hjcopy
  let QK := K.frontierSubcomplex D2
  have hQK : QK.faces.Finite := K.frontierSubcomplex_finite D2 hK
  have hQKs : QK.space = Q2 := by
    change (K.frontierSubcomplex D2).space = Q2
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs,
      frontier_closedBall _ one_ne_zero]
  have hjQ : FinitePiecewiseAffineOn j Q2 := by
    rw [← hQKs]
    apply hj.restrict QK hQK
    exact hQKs.subset.trans sphere_subset_closedBall
  have hjT : MapsTo j Q2 T := by
    intro x hx
    rw [hjb ⟨x, hx⟩]
    exact (rim ⟨x, hx⟩).property
  obtain ⟨k, hk, hkv⟩ := hc.symm
  have hki : InjOn k T := by
    intro x hx y hy hxy
    have hh : c.symm ⟨x, hx⟩ = c.symm ⟨y, hy⟩ := Subtype.ext
      ((hkv ⟨x, hx⟩).trans (hxy.trans (hkv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (c.symm.injective hh)
  have hcomp := hk.comp hjQ hjT
  have hcompinj : InjOn (k ∘ j) Q2 := hki.comp (hi.mono sphere_subset_closedBall) hjT
  have hval (x : Q2) : (k ∘ j) x = (c.symm (rim x) : P2) := by
    change k (j x) = _
    rw [hjb x]
    exact (hkv (rim x)).symm
  obtain ⟨n, P, hPi, hP, hPb⟩ := squareRimPolygon.exists_polygon_finitePL_image
    hasSimplicialEdges_squareRimPolygon injective_squareRimPolygon hcomp
    (by rw [boundary_squareRimPolygon])
    (by simpa only [boundary_squareRimPolygon] using hcompinj)
  rw [boundary_squareRimPolygon] at hPb
  have hPimage : P.boundary ℝ =
      (fun x : Q2 ↦ (c.symm (rim x) : P2)) '' univ := by
    rw [hPb]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, mem_univ _, (hval ⟨x, hx⟩).symm⟩
    · rintro ⟨x, _, rfl⟩
      exact ⟨x, x.property, hval x⟩
  have htransport : annulusChartImage c (P.boundary ℝ) = j '' Q2 := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨x, hx, hxp⟩ := hPb.subset hp
      have heq : p = c.symm (rim ⟨x, hx⟩) :=
        Subtype.ext (hxp.symm.trans (hval ⟨x, hx⟩))
      refine ⟨x, hx, ?_⟩
      change j x = (c p : E)
      rw [heq, c.apply_symm_apply]
      exact hjb ⟨x, hx⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨c.symm (rim ⟨x, hx⟩), ?_, ?_⟩
      · exact hPimage.symm ▸ mem_image_of_mem _ (mem_univ (⟨x, hx⟩ : Q2))
      · change (c (c.symm (rim ⟨x, hx⟩)) : E) = j x
        rw [c.apply_symm_apply]
        exact (hjb ⟨x, hx⟩).symm
  let gamma : C(Q2, Ann) := ⟨fun x ↦ c.symm (rim x), c.symm.continuous.comp rim.continuous⟩
  have hgamma : ∀ x : Q2, (gamma x : P2) ∈ P.boundary ℝ := by
    intro x
    rw [hPimage]
    exact ⟨x, mem_univ _, rfl⟩
  have hgammaEssential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1 := by
    intro h
    apply hessential
    apply (c.symm.loopClass_map_eq_one_iff (squareRimLoop.map rim.continuous)).mp
    exact h
  have hstrict : ∀ p ∈ P.boundary ℝ,
      -(1 / 8 : ℝ) < depth 1 p ∧ depth 1 p < (1 / 8 : ℝ) := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := hPimage.subset hp
    exact hdepth x
  obtain ⟨hinner, houter⟩ := essential_polygon_in_square_annulus
    P hP hPi hstrict gamma hgamma hgammaEssential
  exact ⟨n, P, hP, hPi, hPimage, htransport, hinner, houter⟩

end PoincareConjecture.M76

