import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.Map
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.Count



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_disk_replacement_with_count_decrease
    {X ι E κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {A : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hsub : closure P.inside ⊆ interior J.space)
    {f : P2 → X} (hf : PolyhedralPLInCharts e f J.space) (hfi : InjOn f J.space)
    {c q : Set E} {g : E → X} (hc : IsFinitePLBallPair P2 c q)
    (hg : PolyhedralPLInCharts e g c) (hgi : InjOn g c)
    (hrim : f '' P.boundary ℝ = g '' q)
    (hcontact : (g '' c) ∩ (f '' (J.space \ P.inside)) = f '' P.boundary ℝ)
    (havoid : Disjoint (g '' c) A)
    (pieces : κ → Set P2) (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hcover : ⋃ i, pieces i = J.space ∩ f ⁻¹' A)
    (hconn : ∀ i, IsConnected (pieces i))
    (hremoved : (J.space ∩ f ⁻¹' A ∩ P.inside).Nonempty) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧ InjOn k J.space ∧
      EqOn k f (J.space \ P.inside) ∧ EqOn k f (frontier J.space) ∧
      k '' closure P.inside = g '' c ∧
      k '' J.space = (f '' (J.space \ P.inside)) ∪ (g '' c) ∧
      J.space ∩ k ⁻¹' A = (J.space ∩ f ⁻¹' A) \ P.inside ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' A : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' A : Set P2)) := by
  obtain ⟨k, hk, hki, hkeep, hfront, hdisk, himage⟩ :=
    exists_original_interior_disk_replacement he J hJ P hP hPi hsub hf hfi
      hc hg hgi hrim hcontact
  have hsource : J.space ∩ k ⁻¹' A = (J.space ∩ f ⁻¹' A) \ P.inside := by
    ext x
    constructor
    · intro hx
      have hxout : x ∉ P.inside := by
        intro hxin
        exact disjoint_left.mp havoid (hdisk.subset ⟨x, subset_closure hxin, rfl⟩) hx.2
      refine ⟨⟨hx.1, ?_⟩, hxout⟩
      change f x ∈ A
      rw [← hkeep ⟨hx.1, hxout⟩]
      exact hx.2
    · intro hx
      refine ⟨hx.1.1, ?_⟩
      change k x ∈ A
      rw [hkeep ⟨hx.1.1, hx.2⟩]
      exact hx.1.2
  have hboundary : Disjoint (J.space ∩ f ⁻¹' A) (frontier P.inside) := by
    rw [P.frontier_inside hP hPi]
    apply disjoint_left.mpr
    intro x hx hxP
    exact disjoint_left.mp havoid
      (image_mono hc.1 (hrim.subset (mem_image_of_mem f hxP))) hx.2
  refine ⟨k, hk, hki, hkeep, hfront, hdisk, himage, hsource, ?_⟩
  rw [hsource]
  exact connectedComponents_card_lt_of_open_deletion pieces hclosed hdis hcover hconn
    (P.isOpen_inside hP hPi) hboundary hremoved

end PoincareConjecture.M76.Dehn.Annuli
