import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SingleNewPortCollarContact
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.RealizedCollarEndpointAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.RetainedBallTransport








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.exists_ball_of_single_new_port_component
    {X E F α β κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : α → OpenPartialHomeomorph X V3} {R C T : Set X} {f : X → E}
    (c : MarkedSphereCut e R κ) (d : MarkedSphereCut e R (Option κ))
    (hports : ∀ j : κ × Bool, d.ports (some j.1,j.2) = c.ports j)
    (hdc : d.carrier ⊆ c.carrier) (hC : IsClosed C) (hCd : C ⊆ d.carrier)
    (hm : HasPuncturedSphereModel e f C)
    (hfront : frontier C = ⋃ j : {j : Option κ × Bool // d.ports j ⊆ C}, d.ports j)
    (side : Bool) (hchosen : d.ports (none,side) ⊆ C)
    (hopposite : Disjoint (d.ports (none,!side)) C)
    (raw : OriginalFiniteSphereCollar e c.carrier T (d.collar none)
      (fun b => d.ports (none,b)))
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (phi : X → F) (hphi : Continuous phi)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphii : InjOn phi c.carrier) (caps : κ × Bool → Set F)
    (hcaps : ∀ j, IsFinitePLBallPair V3 (caps j) (phi '' c.ports j))
    (hcontact : ∀ j, caps j ∩ phi '' c.carrier = phi '' c.ports j)
    (hcapsdis : Pairwise fun j k => Disjoint (caps j) (caps k))
    {W : Set F} (hDW : phi '' c.carrier ∪ ⋃ j, caps j ⊆ W)
    (atlas : β → OpenPartialHomeomorph W V3)
    (hcover : ∀ x, ∃ i, x ∈ (atlas i).source)
    (hcompat : ∀ i j, (atlas i).symm.trans (atlas j) ∈ piecewiseAffineGroupoid V3)
    (hrep : ∀ i, ∃ (Q : Set F) (g : F → V3), FinitePiecewiseAffineOn g Q ∧
      ∀ x ∈ (atlas i).source, (x : F) ∈ Q ∧ atlas i x = g x)
    (G : W ≃ₜ W) {V S : Set W}
    (hVD : V ⊆ (Subtype.val : W → F) ⁻¹' (phi '' c.carrier ∪ ⋃ j, caps j))
    (hfix : EqOn G id Vᶜ)
    (hG : ∀ i j, (atlas i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (atlas j)) ∈
      piecewiseAffineGroupoid V3)
    (himage : phi '' T = (Subtype.val : W → F) '' (G '' S)) :
    ∃ A : Set W, A ⊆ (Subtype.val : W → F) ⁻¹' (phi '' c.carrier ∪ ⋃ j, caps j) ∧
      Nonempty (ChartwisePLBall atlas A S) := by
  obtain ⟨hball,hsub⟩ := c.isFinitePLBallPair_single_new_port_filling d hports hdc hC hCd
    hm hfront side hchosen hopposite K g hg hgi hreal phi hphiPL hphii caps hcaps hcontact hcapsdis
  have hinside : closure (d.collar none) ⊆ interior c.carrier :=
    raw.closed_eq.subset.trans raw.closedInterior
  have hmeet := c.single_new_port_filling_collar_contact d hCd hinside side hchosen
    hopposite phi hphii (hCd.trans hdc) caps hcontact
  obtain ⟨A,hA,⟨ball⟩,_,_⟩ := raw.exists_realized_endpoint_attachment phi hphi hphiPL hphii
    subset_union_left hDW atlas hcover hcompat hrep side hball hsub hmeet
  have hboundary : (Subtype.val : W → F) ⁻¹' (phi '' T) = G '' S := by
    rw [himage,preimage_image_eq _ Subtype.val_injective]
  rw [hboundary] at ball
  exact ball.exists_ball_before_supported_motion G hA hVD hfix hcover hG

end PoincareConjecture.M76
