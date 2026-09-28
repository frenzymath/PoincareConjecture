import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialPlanarCompression
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskInnermostCircle
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PlanarSurfaceCarrierInterior

set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

open Classical in
theorem ChartwisePLSphere.contact_intervals_of_sphere_and_disk_minima
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S E D : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (hR : IsCompact R)
    (hSR : S ⊆ interior R)
    (hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (hE : IsClosed E) (hER : E ⊆ R)
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (hDQ : D ⊆ Q.source)
    (hQ : ∀ a, (e a).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hCQ : S ∩ frontier E ⊆ Q.source)
    (hG : G.faces.Finite) (hGs : G.space = Q '' (S ∩ frontier E))
    (hpres : HasDisjointPolygonPresentation G.space)
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hcross : ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
        (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ frontier E ↔ (C x).1.1 = 0)
    (hmin : ∀ d : Set X × OpenPartialHomeomorph X V3 × SimplicialComplex ℝ V3,
      (Nonempty (ChartwisePLSphere e d.1) ∧ d.1 ⊆ interior R ∧
        (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B d.1)) ∧
        D ⊆ d.2.1.source ∧
        (∀ a, (e a).symm.trans d.2.1 ∈ piecewiseAffineGroupoid V3) ∧
        d.1 ∩ frontier E ⊆ d.2.1.source ∧
        d.2.2.faces.Finite ∧ d.2.2.space = d.2.1 '' (d.1 ∩ frontier E) ∧
        HasDisjointPolygonPresentation d.2.2.space ∧
        (∀ a ∈ d.2.2.faces, a.card ≤ 2) ∧
        (∀ v : d.2.2.vertices,
          (d.2.2.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
        ∀ w ∈ d.2.2.space, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ C : OpenPartialHomeomorph V3 C3,
            w ∈ C.source ∧ C.source ⊆ O ∩ d.2.1.target ∧
            (∀ z ∈ C.source, d.2.1.symm z ∈ interior R) ∧ C w = 0 ∧
            LocallyPiecewiseAffineOn C C.source ∧
            LocallyPiecewiseAffineOn C.symm C.target ∧
            (∀ x ∈ C.source, d.2.1.symm x ∈ d.1 ↔ (C x).2 = 0) ∧
            ∀ x ∈ C.source, d.2.1.symm x ∈ frontier E ↔ (C x).1.1 = 0) →
      Nat.card (ConnectedComponents G.space) ≤
        Nat.card (ConnectedComponents d.2.2.space))
    (heE : PLDomain e E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2}
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E)
    (hpp : ∀ z∈K.space,p z∈frontier E ↔ z∈B)
    (J0 : SimplicialComplex ℝ P2) (hJcv : Convex ℝ J0.space)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f J0.space) (hfi : InjOn f J0.space)
    (hfE : MapsTo f J0.space E)
    (hfproper : ∀ z∈J0.space,f z∈frontier E ↔ z∈frontier J0.space)
    (C : SurfaceIntersectionComponents J0.space K.space f p B)
    (M : SurfaceIntersectionComponents K.space J0.space p f (frontier J0.space))
    (hnull : ¬ ∃ i,∃ (n : ℕ) (L : Polygon P2 (n+3)),Function.Injective L ∧
      L.HasSimplicialEdges ∧ L.boundary ℝ=C.pieces i ∧
      closure L.inside⊆interior K.space\B) :
    ∀ i,IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i∩frontier J0.space) := by
  have hKint := s.planar_exterior_interior_of_not_rim heE K hK p hp hpi hps hpp
  have hnocircle : ¬ ∃ i,Disjoint (M.pieces i) (frontier J0.space) := by
    intro hc
    obtain ⟨i,n,m,L,T,hLi,hL,hLb,hLK,hTi,hT,hd,hj,hji,hTin,hjE,hproper,hcircle⟩ :=
      exists_actual_disk_at_innermost_compression_circle J0 hJcv hf hfi hfE hfproper
        hpp hps C M hc
    have hLA : L.boundary ℝ⊆interior K.space := hLK.trans hKint
    have hinside := s.polygon_disk_of_proper_compression_at_minimum he hR hSR hn
      hE hER Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
      (K.isCompact_space_of_finite hK) p hp.continuousOn hpi hps hpp
      L hL hLi hLA hd f hj hji (fun z hz => hjE (mem_image_of_mem f hz)) hproper hcircle
    exact hnull ⟨i,n,L,hLi,hL,hLb,hinside⟩
  intro i
  rcases M.models i with hd | ⟨_,_,_,_,_,hc⟩
  · exact hd
  · exact (hnocircle ⟨i,hc⟩).elim

end PoincareConjecture.M76
