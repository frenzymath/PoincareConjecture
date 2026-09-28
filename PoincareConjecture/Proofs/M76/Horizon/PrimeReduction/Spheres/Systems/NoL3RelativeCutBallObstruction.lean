import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3CutBallObstruction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RelativeComponentBoundary

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem HasNoPuncturedSphereComponents.not_ball_with_retained_collar_relative_boundary
    {X V E ι κ : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite κ]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {Q D S F : Set X} {f : X → E} {A : Set V} {c : V × ℝ → X} {ε : ℝ}
    (hno : HasNoPuncturedSphereComponents e f Q)
    (ball : ChartwisePLBall e D S)
    (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (B : κ → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hfront : frontier Q = F ∪ ⋃ i, B i) (hDF : Disjoint (interior D) F)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f D) (hSQ : Disjoint S Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hopen : IsOpen (c '' (A ×ˢ Ioo (-ε) ε)))
    (hcenter : c '' (A ×ˢ ({0} : Set ℝ)) = S)
    (hne : S.Nonempty)
    (hend : ∀ b : Bool, c '' (A ×ˢ ({if b then ε else -ε} : Set ℝ)) ⊆ Q) : False := by
  obtain ⟨b,x,hxb,hxD⟩ := exists_collar_end_in_interior hε hε1 hc hci hopen
    (hcenter.trans ball.frontier_eq.symm) (ball.frontier_eq.symm ▸ hne) ball.closure_interior
  have hxQ := hend b hxb
  have hcc : connectedComponentIn Q x ⊆ interior D :=
    isPreconnected_connectedComponentIn.subset_interior_of_avoids_frontier
      (by rw [ball.frontier_eq]; exact hSQ.symm.mono (connectedComponentIn_subset _ _) Subset.rfl)
      ⟨x,mem_connectedComponentIn hxQ,hxD⟩
  obtain ⟨hC,hCPL,_,hCfront⟩ := hPL.component_frontier_away_from_old_boundary hQ B sB
    hfront hxQ (hDF.mono hcc Subset.rfl)
  exact hno.not_spherical_component_subset_ball ball hxQ hC hCPL
    (fun i : {i : κ // B i ⊆ connectedComponentIn Q x} => B i)
    (fun i => sB i) (fun i j hij => hBdis (Subtype.val_injective.ne hij)) hCfront
    hf hfi (hcc.trans interior_subset)

end PoincareConjecture.M76
