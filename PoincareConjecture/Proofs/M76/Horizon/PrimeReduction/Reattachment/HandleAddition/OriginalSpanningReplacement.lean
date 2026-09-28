import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningNarrowedInsideGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningRelativeRectangleCap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningJoinedPatchReplacement

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "Rect" => (J ×ˢ I)
local notation "Ends" => (({0,1} : Set ℝ) ×ˢ I)
local notation "Sides" => (J ×ˢ ({-1,1} : Set ℝ))
local notation "Corners" => (({0,1} : Set ℝ) ×ˢ ({-1,1} : Set ℝ))
local notation "RectRim" => Ends ∪ Sides
local notation "Wide" => (Icc (-1 : ℝ) 2 ×ˢ I)
local notation "WideRim" => ((({-1,2} : Set ℝ) ×ˢ I) ∪ (Icc (-1 : ℝ) 2 ×ˢ ({-1,1} : Set ℝ)))

theorem HamiltonMarkedProtectedBall.exists_original_spanning_replacement
    {ι κ α V : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S W : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hn : ¬∃ B,B ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall e B S))
    (hW : PLDomain e W) (hWS : frontier W = S) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (_hcross : ∀ x ∈ S ∩ frontier E,∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0)
      {j : V2 → X} (P : OriginalDiskProduct e (E ∩ W) j)
      (_hNfront : frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S))
      (_hPO : MapsTo P.map (Disk ×ˢ I) (interior R))
      {d U C : Set V} {a₀ a₁ : V}
      (_hd : IsFinitePLBallPair P2 d (U ∪ C))
      (_hU : IsFinitePLBallPair ℝ U {a₀,a₁}) (_hC : IsFinitePLBallPair ℝ C {a₀,a₁})
      (_hab : a₀ ≠ a₁) (_hUC : U ∩ C = {a₀,a₁})
      (H : Disk ≃ₜ d) (_hH : H.IsFinitePL)
      (_hHrim : ∀ z : Disk,(z : V2) ∈ Rim ↔ (H z : V) ∈ U ∪ C)
      {f : V → X} (_hj : ∀ z : Disk,j z = f (H z))
      (_hjU : ∀ z : Disk,j z ∈ frontier E ↔ (H z : V) ∈ U)
      (_hjC : ∀ z : Disk,j z ∈ S ↔ (H z : V) ∈ C)
      (_hmark : ∀ z ∈ Rim,∀ t ∈ I,
        (P.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
        (P.map (z,t) ∈ S ↔ j z ∈ S)),
    ∃ (k : V × ℝ → X) (B T : Set X) (r a : P2 → X) (cap : P2 × ℝ → X),
      PolyhedralPLInCharts e k (d ×ˢ I) ∧ InjOn k (d ×ˢ I) ∧
      (∀ x ∈ d,k (x,0) = f x) ∧
      (∀ z (hz : z ∈ d ×ˢ I),k z = P.map (H.symm ⟨z.1,hz.1⟩,z.2 / 2)) ∧
      B = k '' (d ×ˢ I) ∧ T = k '' (((U ∪ C) ×ˢ I) ∪ (d ×ˢ ({-1,1} : Set ℝ))) ∧
      Nonempty (ChartwisePLBall e B T) ∧ B ⊆ E ∩ W ∧ B ⊆ interior R ∧
      (∀ z ∈ d ×ˢ I,k z ∈ frontier E ↔ z.1 ∈ U) ∧
      (∀ z ∈ d ×ˢ I,k z ∈ S ↔ z.1 ∈ C) ∧
      PolyhedralPLInCharts e r Rect ∧ InjOn r Rect ∧ r '' Rect = k '' (U ×ˢ I) ∧
      r '' (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ)) = k '' (U ×ˢ ({-1,1} : Set ℝ)) ∧
      B ∩ frontier E = r '' Rect ∧ T ∩ frontier E = r '' Rect ∧
      (T \ r '' Rect).Nonempty ∧ MapsTo r Rect ((frontier E ∩ W) ∩ interior R) ∧
      (∀ t ∈ I,r (0,t) = k (a₀,t)) ∧ (∀ t ∈ I,r (1,t) = k (a₁,t)) ∧
      (∀ z ∈ Rect,r z ∈ S ↔ z.1 = 0 ∨ z.1 = 1) ∧
      PolyhedralPLInCharts e a Rect ∧ InjOn a Rect ∧ a '' Rect = k '' (C ×ˢ I) ∧
      B ∩ S = a '' Rect ∧ a '' Rect ⊆ T ∧ EqOn a r Ends ∧
      (∀ z ∈ Rect,a z ∈ frontier E ↔ z.1 = 0 ∨ z.1 = 1) ∧
      PolyhedralPLInCharts e cap (Rect ×ˢ J) ∧ InjOn cap (Rect ×ˢ J) ∧
      MapsTo cap (Rect ×ˢ J) (D ∩ W) ∧ MapsTo cap (Rect ×ˢ J) (interior R) ∧
      (∀ z ∈ Rect,cap (z,0) = r z) ∧
      (∀ z ∈ Rect ×ˢ J,cap z ∈ E ↔ z.2 = 0) ∧
      (∀ z ∈ Rect ×ˢ J,cap z ∈ S ↔ z.1.1 = 0 ∨ z.1.1 = 1) ∧
      cap '' (Rect ×ˢ J) ∩ E = r '' Rect ∧
      Nonempty (ChartwisePLBall e (cap '' (Rect ×ˢ J))
        (cap '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ))))) ∧
      (∃ (Hc : Disk ≃ₜ Rect) (v : V2 → P2) (c : V2 × ℝ → X) (u : P2 → V2),
        Hc.IsFinitePL ∧ FinitePiecewiseAffineOn v Disk ∧ (∀ z : Disk,(Hc z : P2) = v z) ∧
        PolyhedralPLInCharts e c (Disk ×ˢ J) ∧ InjOn c (Disk ×ˢ J) ∧
        FinitePiecewiseAffineOn u Rect ∧ (∀ z : Rect,(Hc.symm z : V2) = u z) ∧
        (∀ z,cap z = c (u z.1,z.2)) ∧ cap '' (Rect ×ˢ J) = c '' (Disk ×ˢ J) ∧
        ∃ (K : Set X) (q : Finset (D ∪ K : Set X))
          (Pc : RelativeFrontierDiskProduct e D W (interior R ∩ interior R) (r ∘ v) K q),
          Pc.map = c ∧ ∀ z ∈ Rect ×ˢ J,
            Pc.productInverse (Pc.graph (cap z)) = (Pc.graph (r z.1),Pc.delta * z.2)) ∧
      ∃ (Q T' S' : Set X) (f' : P2 → X) (g : V3 → X) (d' q' : Set V3),
        Nonempty (ChartwisePLBall e Q T') ∧ Q = B ∪ cap '' (Rect ×ˢ J) ∧ Q ⊆ interior R ∧
        IsFinitePLBallPair P2 Wide WideRim ∧ PolyhedralPLInCharts e f' Wide ∧ InjOn f' Wide ∧
        Q ∩ S = f' '' Wide ∧ f' '' Wide ⊆ T' ∧
        IsFinitePLBallPair P2 d' q' ∧ PolyhedralPLInCharts e g d' ∧ InjOn g d' ∧
        g '' d' = T' \ (f' '' Wide \ f' '' WideRim) ∧ g '' q' = f' '' WideRim ∧
        S' = (S \ (f' '' Wide \ f' '' WideRim)) ∪ g '' d' ∧
        Nonempty (ChartwisePLSphere e S') ∧ S' ⊆ interior R ∧
        (¬∃ A,A ⊆ R ∧ Nonempty (ChartwisePLBall e A S')) ∧
        Q ∩ S' = g '' d' ∧ g '' d' ∩ frontier E = r '' Sides ∧
        S' ∩ frontier E = ((S ∩ frontier E) \ (r '' Ends \ r '' Corners)) ∪ r '' Sides := by
  intro X R E hcross j P hNfront hPO d U C a₀ a₁ hd hU hC hab hUC H hH hHrim f hj hjU hjC hmark
  obtain ⟨k,B,T,r,hk,hki,hk0,hB,hT,⟨uB⟩,hBE,hBR,hkE,hkS,hBS,
    hr,hri,hrimage,hrSides,hBF,hTF,hTout,hrMap,hr0,hr1,hrS,hkP⟩ :=
    P.exists_narrowed_spanning_inside_geometry hNfront hPO hd hU hab hUC H hH hHrim hj hjU hjC hmark
  have hCd : C ⊆ d := subset_union_right.trans hd.1
  obtain ⟨a,ha,hai,haimage,_haSides,ha0,ha1,haF,_⟩ :=
    exists_original_marked_base_rectangle hC hab hCd
      (show C ∩ U = {a₀,a₁} by rw [inter_comm,hUC]) hk hki hkE
  have har : EqOn a r Ends := by
    intro z hz
    rcases hz.1 with h | h
    · rw [show z = (0,z.2) from Prod.ext h rfl,ha0 z.2 hz.2,hr0 z.2 hz.2]
    · have h' : z.1 = 1 := h
      rw [show z = (1,z.2) from Prod.ext h' rfl,ha1 z.2 hz.2,hr1 z.2 hz.2]
  have haT : a '' Rect ⊆ T := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := haimage.subset hx
    rw [hT]
    exact ⟨z,Or.inl ⟨Or.inr hz.1,hz.2⟩,rfl⟩
  have hBSa : B ∩ S = a '' Rect := hBS.trans haimage.symm
  have hrT : r '' Rect ⊆ T := fun x hx => (hTF.symm.subset hx).1
  obtain ⟨cap,hcap,hcapi,hcapDW,hcapO,hcap0,hcapE,hcapS,hcapbase,⟨vCap⟩,hret⟩ :=
    b.exists_original_relative_rectangle_cap he hdim hi hW hWS hSR hcross hr hri
      (fun z hz => (hrMap hz).1.1) (fun z hz => (hrMap hz).1.2) (fun z hz => (hrMap hz).2)
      isOpen_interior (image_subset_iff.mpr (fun z hz => (hrMap hz).2))
  have hcapR : MapsTo cap (Rect ×ˢ J) (interior R) := fun z hz => (hcapO hz).2
  have hcapends (z) (hz : z ∈ Rect ×ˢ J) : cap z ∈ S ↔ z.1.1 = 0 ∨ z.1.1 = 1 :=
    (hcapS z hz).trans (hrS z.1 hz.1)
  have hreplacement := s.exists_nonbounding_spanning_patch_replacement he
    (isCompact_latticeHandleDomain ι κ L) uB (hBE.trans inter_subset_left) hBR
    isClosed_closure.frontier_subset hSR ha hai hr hri hcap hcapi hcap0 har hcapE hcapends
    (image_subset_iff.mpr hcapR) hBSa haT haF hrT hTF hTout vCap hn
  refine ⟨k,B,T,r,a,cap,hk,hki,hk0,hkP,hB,hT,⟨uB⟩,hBE,hBR,hkE,hkS,
    hr,hri,hrimage,hrSides,hBF,hTF,hTout,hrMap,hr0,hr1,hrS,ha,hai,haimage,hBSa,haT,har,haF,
    hcap,hcapi,hcapDW,hcapR,hcap0,hcapE,hcapends,hcapbase,⟨vCap⟩,?_,hreplacement⟩
  exact hret

end PoincareConjecture.M76
