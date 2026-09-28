import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereSurgeryContactDecrease
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SurgeryRimNullhomotopy










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

theorem ChartwisePLSphere.polygon_disk_of_proper_compression_at_minimum
    {X α V : Type*} [MetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
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
    {A B : Set P2} (hA : IsCompact A) (p : P2 → X)
    (hp : ContinuousOn p A) (hpi : InjOn p A) (hps : p '' A = S ∩ E)
    (hproperA : ∀ z ∈ A, p z ∈ frontier E ↔ z ∈ B)
    {n : ℕ} (L : Polygon P2 (n+3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) (hLA : L.boundary ℝ ⊆ interior A)
    {d q : Set V} (hd : IsFinitePLBallPair P2 d q) (j : V → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjE : MapsTo j d (interior E))
    (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q)
    (hcircle : p '' L.boundary ℝ = j '' q) :
    closure L.inside ⊆ interior A \ B := by
  classical
  by_contra hnondisk
  have hjR : MapsTo j d (interior R) := fun z hz => interior_mono hER (hjE hz)
  obtain ⟨K,_,_,k,_,_,_,_,_,_,_,_,_,_,_,hkQ,_,_,P,hP,hPS,_,_,_,_⟩ :=
    s.exists_original_whole_disk_product hR he hSR isOpen_univ (subset_univ S)
      hd j hj hji hjR hproper isOpen_interior (fun _ hx => by
        obtain ⟨z,hz,rfl⟩ := hx
        exact hjE hz)
  have hsmall : Disk ×ˢ J ⊆ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    exact ⟨hz,by constructor <;> linarith [ht.1,ht.2]⟩
  have hUE : P.closedStrip ⊆ interior E := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hP (hsmall hz)).1.1
  have hUR : P.closedStrip ⊆ interior R := hUE.trans (interior_mono hER)
  have hUF : Disjoint P.closedStrip (frontier E) :=
    disjoint_left.mpr (fun x hx hf => hf.2 (hUE hx))
  have hband : P.map '' (Rim ×ˢ J) ⊆ S ∩ interior E := by
    rintro _ ⟨z,hz,rfl⟩
    have hzfull := hsmall ⟨sphere_subset_closedBall hz.1,hz.2⟩
    exact ⟨(hPS z hzfull).mpr hz.1,(hP hzfull).1.1⟩
  have hcenter : p '' L.boundary ℝ = P.map '' (Rim ×ˢ {(0 : ℝ)}) := by
    rw [hcircle,←hkQ]
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨(z,0),⟨hz,rfl⟩,P.central z (sphere_subset_closedBall hz)⟩
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨z,hz,(P.central z (sphere_subset_closedBall hz)).symm⟩
  obtain ⟨a,r,har,_,hcover,t,_,hdis,houtside⟩ :=
    P.exists_original_separated_end_spheres s he.compatible hPS
  have hcapU (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hretS (b : Bool) : s.map '' a b ⊆ S := by
    rintro _ ⟨z,hz,rfl⟩
    rw [s.map_eq ⟨z,(har b).2.1 hz⟩]
    exact (s.parametrization ⟨z,(har b).2.1 hz⟩).property
  have hretstrip (b : Bool) : (s.map '' a b) ∩ P.closedStrip = P.capRimSet b :=
    (har b).2.2.2.2.trans (har b).2.2.2.1
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hretout (b : Bool) : ((s.map '' a b) \ P.capDisk b).Nonempty := by
    obtain ⟨z,hza,hzr⟩ := (har b).1.sdiff_nonempty
    refine ⟨s.map z,⟨z,hza,rfl⟩,?_⟩
    intro hc
    obtain ⟨w,hwr,hwz⟩ := (har b).2.2.2.2.subset ⟨⟨z,hza,rfl⟩,hcapU b hc⟩
    exact hzr (hsi ((har b).2.1 ((har b).1.1 hwr)) ((har b).2.1 hza) hwz ▸ hwr)
  have hboth (b : Bool) : (((s.map '' a b) ∪ P.capDisk b) ∩ frontier E).Nonempty := by
    obtain ⟨x,hxa,hxf⟩ := P.retained_disk_contact_of_nondisk_planar_rim s hE
      (har b).1 (har b).2.1 b (har b).2.2.2.1 hband hA p hp hpi hps hproperA
      L hL hLi hLA hcenter hnondisk
    exact ⟨x,Or.inl hxa,hxf⟩
  apply P.not_both_contacts_of_minimal_position he hR s hSR hn hUR hUF
    (fun b => s.map '' a b) hretS hretstrip hretout _ t hdis.symm _
    Q G hCQ hG hGs hpres hGc hdegree hcross hDQ hQ hmin hboth
  · simpa only [union_comm (s.map '' a true) (s.map '' a false)] using hcover
  · simpa only [union_comm ((s.map '' a true) ∪ P.capDisk true)
      ((s.map '' a false) ∪ P.capDisk false)] using houtside

end PoincareConjecture.M76
