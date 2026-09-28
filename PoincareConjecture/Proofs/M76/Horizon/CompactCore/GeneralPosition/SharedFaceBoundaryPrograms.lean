import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.SharedBoundaryCharts
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaryComplex
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.SourceEdgeHomotopy










set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

theorem exists_shared_face_boundary_programs
    {E V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hdim : Module.finrank ℝ E = 2)
    (a b : {s : K.faces // s.val.card = 2} → K.vertices)
    (hab : ∀ k, (a k : E) ≠ b k)
    (hpair : ∀ k, ({(a k : E), (b k : E)} : Finset E) = k.val.val)
    (T : SimplicialComplex ℝ E) (hT : T.faces.Finite)
    (hTS : T.space = ⋃ k, segment ℝ (a k : E) (b k : E))
    (G : C(I × T.space, X)) (f g : E → X)
    (hG0 : ∀ x : T.space, G (0, x) = f x)
    (hG1 : ∀ x : T.space, G (1, x) = g x)
    (hg : PolyhedralPLInCharts e g T.space)
    (C : {s : K.faces // s.val.card = 3} → OpenPartialHomeomorph X V)
    (hcompat : ∀ s i, (e i).symm.trans (C s) ∈ piecewiseAffineGroupoid V)
    (W : {s : K.faces // s.val.card = 3} → Set V)
    (hcontrol : ∀ s k, k.val.val ⊆ s.val.val → ∀ (t r : I)
      (hx : AffineMap.lineMap (a k : E) (b k : E) (r : ℝ) ∈ T.space),
      G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩) ∈ (C s).source ∧
      C s (G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩)) ∈ W s) :
    ∃ (R : SimplicialComplex ℝ E)
      (L : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
      (Q : {s : K.faces // s.val.card = 2} → SimplicialComplex ℝ E)
      (D : ∀ s : {s : K.faces // s.val.card = 3},
        C(I × frontier (convexHull ℝ (s.val.val : Set E)), X)),
      R.faces.Finite ∧ R.IsSubdivision T ∧
      (∀ s, L s ≤ R ∧ (L s).space = frontier (convexHull ℝ (s.val.val : Set E)) ∧
        (∀ z ∈ R.faces, (∀ v ∈ z, v ∈ (L s).vertices) → z ∈ (L s).faces) ∧
        (L s).AffineOnFaces (C s ∘ g)) ∧
      (∀ k, Q k ≤ R ∧ (Q k).space = segment ℝ (a k : E) (b k : E) ∧
        ∀ z ∈ R.faces, (∀ v ∈ z, v ∈ (Q k).vertices) → z ∈ (Q k).faces) ∧
      (∀ s : {s : K.faces // s.val.card = 3},
        frontier (convexHull ℝ (s.val.val : Set E)) ⊆ T.space) ∧
      (∀ (s : {s : K.faces // s.val.card = 3}) (t : I)
        (u : frontier (convexHull ℝ (s.val.val : Set E))) (hu : (u : E) ∈ T.space),
        D s (t, u) = G (t, ⟨u, hu⟩)) ∧
      (∀ (s : {s : K.faces // s.val.card = 3})
        (u : frontier (convexHull ℝ (s.val.val : Set E))), D s (0, u) = f u) ∧
      (∀ (s : {s : K.faces // s.val.card = 3})
        (u : frontier (convexHull ℝ (s.val.val : Set E))), D s (1, u) = g u) ∧
      ∀ s z, D s z ∈ (C s).source ∧ C s (D s z) ∈ W s := by
  classical
  let : Finite K.faces := hK.to_subtype
  have hedge (k : {s : K.faces // s.val.card = 2}) : {(a k : E), (b k : E)} ∈ K.faces :=
    (hpair k).symm ▸ k.val.property
  have hseg (k : {s : K.faces // s.val.card = 2}) :
      segment ℝ (a k : E) (b k : E) = convexHull ℝ (k.val.val : Set E) := by
    rw [← hpair k]
    simp only [Finset.coe_pair, convexHull_pair]
  have hboundaryEdge (s : {s : K.faces // s.val.card = 3}) {x : E}
      (hx : x ∈ frontier (convexHull ℝ (s.val.val : Set E))) :
      ∃ k : {s : K.faces // s.val.card = 2}, k.val.val ⊆ s.val.val ∧
        x ∈ segment ℝ (a k : E) (b k : E) := by
    rw [K.triangle_frontier_eq_iUnion_erase hdim s.val.property s.property] at hx
    obtain ⟨p, hxp⟩ := mem_iUnion.mp hx
    obtain ⟨he, hc, hsub⟩ := K.triangle_erase_is_edge s.val.property s.property p.property
    let k : {s : K.faces // s.val.card = 2} := ⟨⟨s.val.val.erase p, he⟩, hc⟩
    exact ⟨k, hsub, (hseg k).symm.subset hxp⟩
  have hboundaryT (s : {s : K.faces // s.val.card = 3}) :
      frontier (convexHull ℝ (s.val.val : Set E)) ⊆ T.space := by
    intro x hx
    obtain ⟨k, _, hk⟩ := hboundaryEdge s hx
    exact hTS.symm.subset (mem_iUnion.mpr ⟨k, hk⟩)
  let D (s : {s : K.faces // s.val.card = 3}) :
      C(I × frontier (convexHull ℝ (s.val.val : Set E)), X) :=
    G.comp ⟨fun z => (z.1, ⟨z.2, hboundaryT s z.2.property⟩),
      continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  have hDcontrol (s : {s : K.faces // s.val.card = 3})
      (z : I × frontier (convexHull ℝ (s.val.val : Set E))) :
      D s z ∈ (C s).source ∧ C s (D s z) ∈ W s := by
    obtain ⟨k, hks, hxk⟩ := hboundaryEdge s z.2.property
    rw [segment_eq_image_lineMap] at hxk
    obtain ⟨r, hr, heq⟩ := hxk
    have hrT : AffineMap.lineMap (a k : E) (b k : E) r ∈ T.space :=
      heq.symm ▸ hboundaryT s z.2.property
    simpa only [D, ContinuousMap.comp_apply, ContinuousMap.coe_mk, heq] using
      hcontrol s k hks z.1 ⟨r, hr⟩ hrT
  choose J hJ hJK hJS hJfaces hJcard hJedges using
    fun s : {s : K.faces // s.val.card = 3} =>
      K.exists_planar_triangle_boundary_complex hdim s.val.property s.property
  have hJT (s : {s : K.faces // s.val.card = 3}) : (J s).space ⊆ T.space :=
    (hJS s).subset.trans (hboundaryT s)
  have hgsource (s : {s : K.faces // s.val.card = 3}) : MapsTo g (J s).space (C s).source := by
    intro x hx
    have h := (hDcontrol s (1, ⟨x, (hJS s).subset hx⟩)).1
    change G (1, ⟨x, hboundaryT s ((hJS s).subset hx)⟩) ∈ (C s).source at h
    rw [hG1] at h
    exact h
  choose P l hP hPK hPS hPa hPb hPline hPmap hPinv using
    fun k : {s : K.faces // s.val.card = 2} =>
      K.exists_edge_subcomplex_coordinate (hab k) (hedge k)
  have hPT (k : {s : K.faces // s.val.card = 2}) : (P k).space ⊆ T.space := by
    intro x hx
    exact hTS.symm.subset (mem_iUnion.mpr ⟨k, (hPS k).subset hx⟩)
  obtain ⟨R, L, Q, hR, hRT, hL, hQ⟩ :=
    hg.exists_shared_marked_chart_refinement T hT J hJ hJT C hcompat hgsource P hP hPT
  refine ⟨R, L, Q, D, hR, hRT, ?_, ?_, hboundaryT, ?_, ?_, ?_, hDcontrol⟩
  · intro s
    exact ⟨(hL s).1, (hL s).2.1.trans (hJS s), (hL s).2.2⟩
  · intro k
    exact ⟨(hQ k).1, (hQ k).2.1.trans (hPS k), (hQ k).2.2⟩
  · intro s t u hu
    rfl
  · intro s u
    exact hG0 ⟨u, hboundaryT s u.property⟩
  · intro s u
    exact hG1 ⟨u, hboundaryT s u.property⟩

end Geometry.SimplicialComplex
