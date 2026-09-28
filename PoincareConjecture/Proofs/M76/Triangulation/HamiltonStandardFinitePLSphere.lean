import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardLiftPL
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
  {α : Type*}
  {d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
  {S : Set (LatticeHandleAmbient ι κ L)}





theorem ChartwisePLSphere.exists_finitePL_standard_lattice_lift
    (s : ChartwisePLSphere d S) (hd : StandardLatticeHandleAtlas ι κ L d) :
    ∃ (T : Set ((ι → ℝ) × (κ → ℝ)))
      (l : sphere (0 : Fin 3 → ℝ) 1 ≃ₜ T),
      l.IsFinitePL ∧ ∀ x,
        ((l x : (ι → ℝ) × (κ → ℝ)).1,
          QuotientAddGroup.mk (l x : (ι → ℝ) × (κ → ℝ)).2) =
            (s.parametrization x : LatticeHandleAmbient ι κ L) := by
  classical
  obtain ⟨l, hlinj, hl⟩ := s.exists_standard_lattice_lift ι κ L
  let : CompactSpace (sphere (0 : Fin 3 → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let h := (l.continuous.isClosedEmbedding hlinj).isEmbedding.toHomeomorph
  let g : (Fin 3 → ℝ) → ((ι → ℝ) × (κ → ℝ)) := fun x =>
    if hx : x ∈ sphere (0 : Fin 3 → ℝ) 1 then l ⟨x, hx⟩ else 0
  have hg (x : sphere (0 : Fin 3 → ℝ) 1) : g x = l x := by
    simp only [g, dif_pos x.property]
  have hgcont : ContinuousOn g (sphere (0 : Fin 3 → ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : sphere (0 : Fin 3 → ℝ) 1 => g x)
    rw [show (fun x : sphere (0 : Fin 3 → ℝ) 1 => g x) = l from funext hg]
    exact l.continuous
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair (Fin 3 → ℝ)
      (closedBall (0 : Fin 3 → ℝ) 1) (sphere (0 : Fin 3 → ℝ) 1))
  let K := B.frontierSubcomplex (closedBall (0 : Fin 3 → ℝ) 1)
  have hK : K.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hKs : K.space = sphere (0 : Fin 3 → ℝ) 1 := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  have hgPL : FinitePiecewiseAffineOn g (sphere (0 : Fin 3 → ℝ) 1) := by
    rw [← hKs]
    apply hd.finitePiecewiseAffineOn_lift K hK s.map
      (by simpa only [hKs] using s.piecewiseAffine) g
      (by simpa only [hKs] using hgcont)
    intro x hx
    have hxs : x ∈ sphere (0 : Fin 3 → ℝ) 1 := hKs ▸ hx
    rw [hg ⟨x, hxs⟩]
    exact (hl ⟨x, hxs⟩).trans (s.map_eq ⟨x, hxs⟩).symm
  refine ⟨range l, h, ⟨g, hgPL, fun x => (hg x).symm⟩, ?_⟩
  exact fun x => hl x

end PoincareConjecture.M76
