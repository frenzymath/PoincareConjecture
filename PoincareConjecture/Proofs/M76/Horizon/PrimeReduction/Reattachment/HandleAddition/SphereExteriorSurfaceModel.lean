import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceGerms
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorFiniteModel
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderSectionDimension








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ChartwisePLSphere.exists_planar_exterior_surface_subdivision
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {E S : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E)
    (K0 B0 : SimplicialComplex ℝ P2) (hK0 : K0.faces.Finite) (hB0K : B0 ≤ K0)
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K0.space) (hpi : InjOn p K0.space)
    (hps : p '' K0.space = S ∩ E)
    (hpb : p '' B0.space = S ∩ frontier E)
    (hproper : ∀ z ∈ K0.space, p z ∈ frontier E ↔ z ∈ B0.space)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0) :
    ∃ K B : SimplicialComplex ℝ P2,
      K.faces.Finite ∧ K.IsSubdivision K0 ∧ B ≤ K ∧ B.space = B0.space ∧
      PolyhedralPLInCharts e p K.space ∧ InjOn p K.space ∧
      p '' K.space = S ∩ E ∧ p '' B.space = S ∩ frontier E ∧
      (∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B.space) ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
      (∀ t ∈ B.faces, t.card ≤ 2) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset P2 | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
      HasDisjointPolygonPresentation B.space := by
  classical
  let : CompactSpace K0.space := isCompact_iff_compactSpace.mp (K0.isCompact_space_of_finite hK0)
  let H : K0.space ≃ₜ ↥(S ∩ E) :=
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn p K0.space hpi)
      (hp.continuousOn.domRestrict.subtype_mk _)).trans (Homeomorph.setCongr hps)
  have hH (z : K0.space) : (H z : X) = p z := rfl
  have hlocal := s.surface_rim_charts_of_frontier_crossings he hcross
  have hproper' (z : P2) (hz : z ∈ K0.space) : p z ∈ S ∩ frontier E ↔ z ∈ B0.space := by
    have hzS := (hps.subset ⟨z,hz,rfl⟩).1
    exact (and_iff_right hzS).trans (hproper z hz)
  obtain ⟨K,B,hK,hKK0,hBK,hBs,hfull,hpure,hcounts,hlinks,hpoly⟩ :=
    exists_surface_rim_incidence_subdivision e K0 B0 hK0 (hK0.subset hB0K)
      (SimplicialComplex.space_subset_of_le hB0K) H p hH hp hproper' hlocal
  refine ⟨K,B,hK,hKK0,hBK,hBs,hKK0.space_eq.symm ▸ hp,
    hKK0.space_eq.symm ▸ hpi,by rwa [hKK0.space_eq],by rwa [hBs],?_,
    hfull,hpure,?_,hcounts,hlinks,hpoly⟩
  · intro z hz
    rw [hBs]
    exact hproper z (hKK0.space_eq.subset hz)
  · intro t ht
    exact hpoly.hasAlexanderCurvePresentation.card_le_two_of_convexHull_subset
      (B.indep ht) (B.convexHull_subset_space ht)

open Classical in
theorem ChartwisePLSphere.exists_planar_exterior_surface_or_subset
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R E S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hE : IsCompact E) (heE : PLDomain e E)
    (hne : E.Nonempty)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0) :
    S ⊆ E ∨
      ∃ (K B : SimplicialComplex ℝ P2) (p : P2 → X),
        K.faces.Finite ∧ B ≤ K ∧
        PolyhedralPLInCharts e p K.space ∧ InjOn p K.space ∧
        p '' K.space = S ∩ E ∧ p '' B.space = S ∩ frontier E ∧
        (∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B.space) ∧
        (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
        (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
        (∀ t ∈ B.faces, t.card ≤ 2) ∧
        (∀ t ∈ K.faces, t.card = 2 →
          {q : Finset P2 | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
            if t ∈ B.faces then 1 else 2) ∧
        (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
        HasDisjointPolygonPresentation B.space := by
  rcases s.exists_planar_exterior_model_or_subset hR he hSR hE heE hne with hsub | hmodel
  · exact Or.inl hsub
  · obtain ⟨K0,B0,p,hK0,hB0,_,hp,hpi,hps,hpb,hproper⟩ := hmodel
    obtain ⟨K,B,hK,_,hBK,_,hp',hpi',hps',hpb',hproper',hfull,hpure,hdimB,hcount,hlink,hpoly⟩ :=
      s.exists_planar_exterior_surface_subdivision heE K0 B0 hK0 hB0 p hp hpi hps hpb hproper hcross
    exact Or.inr ⟨K,B,p,hK,hBK,hp',hpi',hps',hpb',hproper',hfull,hpure,
      hdimB,hcount,hlink,hpoly⟩

open Classical in
theorem HamiltonMarkedProtectedBall.exists_positioned_planar_exterior_surface
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∃ Phi : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι κ L,
      EqOn Phi id (interior R)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (Phi '' S)) ∧ Phi '' S ⊆ interior R ∧
      (∀ x ∈ Phi '' S ∩ frontier E,
        ∃ T : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
          x ∈ T.source ∧ T x = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ T.source, y ∈ Phi '' S ↔ T y 1 = 0) ∧
          (∀ y ∈ T.source, y ∈ frontier E ↔ T y 0 = 0) ∧
          ((∀ y ∈ T.source, y ∈ E ↔ 0 ≤ T y 0) ∨
            (∀ y ∈ T.source, y ∈ E ↔ T y 0 ≤ 0))) ∧
      (Phi '' S ⊆ E ∨
        ∃ (K B : SimplicialComplex ℝ P2) (p : P2 → LatticeHandleAmbient ι κ L),
          K.faces.Finite ∧ B ≤ K ∧
          PolyhedralPLInCharts e p K.space ∧ InjOn p K.space ∧
          p '' K.space = Phi '' S ∩ E ∧ p '' B.space = Phi '' S ∩ frontier E ∧
          (∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B.space) ∧
          (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
          (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
          (∀ t ∈ B.faces, t.card ≤ 2) ∧
          (∀ t ∈ K.faces, t.card = 2 →
            {q : Finset P2 | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
              if t ∈ B.faces then 1 else 2) ∧
          (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
          HasDisjointPolygonPresentation B.space) := by
  classical
  obtain ⟨Phi,hfix,hPhi,hPhiinv,⟨s'⟩,hSR',hcross⟩ :=
    b.exists_positioned_exterior_surface_charts he hdim hi s hSR
  refine ⟨Phi,hfix,hPhi,hPhiinv,⟨s'⟩,hSR',hcross,?_⟩
  have heE := b.plDomain_closed_complement he hdim hi
  have hE := (b.closed_complement_geometry he hdim hi).1
  have hne := (b.isConnected_closed_complement he hdim hi).nonempty
  exact s'.exists_planar_exterior_surface_or_subset
    (isCompact_latticeHandleDomain ι κ L) he hSR' hE heE hne (fun x hx => by
      obtain ⟨T,hxT,hT0,hTe,hTS,hTE,_⟩ := hcross x hx
      exact ⟨T,hxT,hT0,hTe,hTS,hTE⟩)

end PoincareConjecture.M76
