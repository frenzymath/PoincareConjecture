import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalCompressionRim
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.MarkedCollarDiskCompression
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.MarkedDiskRimHomotopy









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Rim" => sphere (0 : Fin 2 → ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem ChartwisePLSphere.no_returning_marked_disk_motion_at_minimum
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S E D : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (heE : PLDomain e E) (hR : IsCompact R)
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
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2} (p : P2 → X)
    (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space) (hps : p '' K.space = S ∩ E)
    (hproperA : ∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B)
    {C Z q : Set P2}
    (hC : IsFinitePLBallPair ℝ C (C ∩ B)) (hCK : C ⊆ K.space)
    (g : P2 → X) (hg : PolyhedralPLInCharts e g Z) (hgi : InjOn g Z)
    (hZ : IsFinitePLBallPair ℝ Z q) (hgZ : g '' Z ⊆ S ∩ frontier E)
    (hgq : g '' q = p '' (C ∩ B))
    (hinter : p '' C ∩ g '' Z = p '' (C ∩ B))
    (hno : ¬ ∃ A U : Set P2, IsFinitePLBallPair P2 A (U ∪ C) ∧
      IsFinitePLBallPair ℝ U (U ∩ C) ∧ A ⊆ K.space ∧ A ∩ B = U)
    {d r : Set P2} (hd : IsFinitePLBallPair P2 d r)
    (f k : P2 → X) (hfi : InjOn f d)
    (hfrim : f '' r = p '' C ∪ g '' Z)
    (hk : PolyhedralPLInCharts e k d) (hki : InjOn k d)
    (hkE : k '' d ⊆ interior E)
    (H : C(I × d,E))
    (hH0 : ∀ z : d,(H (0,z) : X)=f z)
    (hH1 : ∀ z : d,(H (1,z) : X)=k z)
    (hHmark : ∀ (t : I) (z : d),(H (t,z) : X) ∈ S ↔ (z : P2) ∈ r) :
    False := by
  obtain ⟨gamma,delta,hgamma,_,hgammafull,hdeltafull,hhom⟩ :=
    exists_simple_rim_loops_of_marked_disk_homotopy hd hfi hki H hH0 hH1 hHmark
  have hkproper : ∀ z ∈ d,k z ∈ S ↔ z ∈ r := by
    intro z hz
    rw [←hH1 ⟨z,hz⟩]
    exact hHmark 1 ⟨z,hz⟩
  have hnull := s.rim_nullhomotopic_of_proper_compression_at_minimum he heE hR hSR hn
    hE hER Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
    K hK p hp hpi hps hproperA hd k hk hki
    (fun z hz => hkE ⟨z,hz,rfl⟩) hkproper delta hdeltafull.subset
  have hgammanull : gamma.Nullhomotopic := by
    obtain ⟨x,hx⟩ := hnull
    exact ⟨x,hhom.trans hx⟩
  have hcrossO : ∀ x ∈ S ∩ frontier E,∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ T x = 0 ∧
      (∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ T.source,y ∈ S ↔ T y 1 = 0) ∧
      ∀ y ∈ T.source,y ∈ frontier E ↔ T y 0 = 0 := by
    intro x hx
    obtain ⟨T,hxT,_,_,hT0,hT,_,hTS,hTE⟩ :=
      hcross (Q x) (hGs.symm.subset (mem_image_of_mem Q hx)) univ isOpen_univ (mem_univ _)
    exact compatible_paired_chart_of_coordinate_crossing Q hQ T hT (hCQ hx) hxT hT0 hTS hTE
  obtain ⟨A,U,hA,hU,hAK,hAB,_⟩ :=
    s.exists_original_returning_disk_of_nullhomotopic_loop heE hE K hK p hp hpi hps
      hproperA hcrossO hC hCK g hg hgi hZ hgZ hgq hinter gamma hgamma
      (hgammafull.trans hfrim) hgammanull
  exact hno ⟨A,U,hA,hU,hAK,hAB⟩

theorem ChartwisePLSphere.no_returning_marked_collar_compression_at_minimum
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S E D : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (heE : PLDomain e E) (hR : IsCompact R)
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
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2} (p : P2 → X)
    (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space) (hps : p '' K.space = S ∩ E)
    (hproperA : ∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B)
    {C Z q : Set P2}
    (hC : IsFinitePLBallPair ℝ C (C ∩ B)) (hCK : C ⊆ K.space)
    (g : P2 → X) (hg : PolyhedralPLInCharts e g Z) (hgi : InjOn g Z)
    (hZ : IsFinitePLBallPair ℝ Z q) (hgZ : g '' Z ⊆ S ∩ frontier E)
    (hgq : g '' q = p '' (C ∩ B))
    (hinter : p '' C ∩ g '' Z = p '' (C ∩ B))
    (hno : ¬ ∃ A U : Set P2, IsFinitePLBallPair P2 A (U ∪ C) ∧
      IsFinitePLBallPair ℝ U (U ∩ C) ∧ A ⊆ K.space ∧ A ∩ B = U)
    (M : OriginalFiniteCollarModel e E)
    (hmark : ∀ z ∈ M.collarBase.space ×ˢ I,
      (M.inverse (M.collar z) : X) ∈ S ↔
        (M.inverse (M.collar (z.1,0)) : X) ∈ S)
    {d r : Set P2} (hd : IsFinitePLBallPair P2 d r)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d)
    (hfE : f '' d ⊆ E) (hfS : f '' d ∩ S = f '' r)
    (hfrim : f '' r = p '' C ∪ g '' Z) : False := by
  obtain ⟨k,hk,hki,hkE,_,H,hH0,hH1,hHmark⟩ :=
    M.compress_original_disk_preserving_product_mark hmark hd hf hfi hfE hfS
  exact s.no_returning_marked_disk_motion_at_minimum he heE hR hSR hn hE hER
    Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin K hK p hp hpi hps hproperA
    hC hCK g hg hgi hZ hgZ hgq hinter hno hd f k hfi hfrim hk hki hkE
    H hH0 hH1 hHmark

end PoincareConjecture.M76

