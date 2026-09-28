import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalSphereChartCarrier
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem ChartwisePLSphere.exists_finite_clipped_parameter
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space) :
    ∃ g : V3 → V3, FinitePiecewiseAffineOn g P.space ∧
      MapsTo g P.space (sphere (0 : V3) 1) ∧ InjOn g P.space ∧
      (∀ w ∈ P.space, s.map (g w) = Q.symm w) ∧
      (∀ x ∈ sphere (0 : V3) 1, s.map x ∈ Q.source →
        Q (s.map x) ∈ J.space → g (Q (s.map x)) = x) ∧
      g '' P.space = {x | x ∈ sphere (0 : V3) 1 ∧
        s.map x ∈ Q.source ∧ Q (s.map x) ∈ J.space} := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let K := B.frontierSubcomplex (closedBall (0 : V3) 1)
  have hK : K.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hKs : K.space = sphere (0 : V3) 1 := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  have hmap : s.map '' K.space = S := by
    rw [hKs]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x, hx⟩
      refine ⟨z, z.property, ?_⟩
      rw [s.map_eq z, hz]
  have hinj : InjOn s.map K.space := by
    intro x hx y hy hxy
    have hxS := hKs.subset hx
    have hyS := hKs.subset hy
    rw [s.map_eq ⟨x, hxS⟩, s.map_eq ⟨y, hyS⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hf : PolyhedralPLInCharts e s.map K.space := hKs.symm ▸ s.piecewiseAffine
  obtain ⟨L, g, _, hLs, hg, hgK, hright, hleft⟩ :=
    hf.exists_finite_clipped_chart_inverse K hK hinj Q hQ J hJ hJQ
  have hLP : L.space = P.space := by simpa only [hmap, ← hPs] using hLs
  have hgP := hg.restrict P hP hLP.symm.subset
  have hcoord (w : V3) (hw : w ∈ P.space) :
      s.map (g w) ∈ Q.source ∧ Q (s.map (g w)) = w :=
    hright w (hLP.symm.subset hw)
  have hparam (w : V3) (hw : w ∈ P.space) : s.map (g w) = Q.symm w := by
    exact (Q.left_inv (hcoord w hw).1).symm.trans
      (congrArg Q.symm (hcoord w hw).2)
  have hginj : InjOn g P.space := by
    intro a ha b hb hab
    exact ((hcoord a ha).2.symm.trans (congrArg (fun x => Q (s.map x)) hab)).trans
      (hcoord b hb).2
  refine ⟨g, hgP, fun w hw => hKs.subset (hgK (hLP.symm.subset hw)),
    hginj, hparam, ?_, ?_⟩
  · intro x hx hsource hwindow
    exact hleft x (hKs.symm.subset hx) hsource hwindow
  · ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hKs.subset (hgK (hLP.symm.subset hw)), (hcoord w hw).1,
        (hcoord w hw).2.symm ▸ (hPs.subset hw).2⟩
    · rintro ⟨hx, hsource, hwindow⟩
      have hxS : s.map x ∈ S := by
        rw [s.map_eq ⟨x, hx⟩]
        exact (s.parametrization ⟨x, hx⟩).property
      exact ⟨Q (s.map x), hPs.symm.subset ⟨⟨s.map x, ⟨hxS, hsource⟩, rfl⟩,
        hwindow⟩, hleft x (hKs.symm.subset hx) hsource hwindow⟩

end PoincareConjecture.M76
