import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Faces.OtherFaces
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Faces.BoundaryDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.TriangleGraphPosition

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_planar_triangle_position_step
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (Source : SimplicialComplex ℝ (ℝ × ℝ)) (hSource : Source.faces.Finite)
    {f : (ℝ × ℝ) → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hfi : InjOn f Source.space)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hSV : Disjoint (f '' Source.space) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      (f '' Source.space ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (f '' Source.space) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hinterior : ∀ x ∈ Source.space, f x ∈ Q.source → x ∈ interior Source.space)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ (Phi : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ EqOn Phi id W ∧ EqOn Phi id Q.sourceᶜ ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      InTriangleGraphPosition Q (Phi '' (f '' Source.space))
        (g '' convexHull ℝ (s : Set E)) (convexHull ℝ (A '' (s : Set E))) := by
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hJ, _, hTJ, hJQ, _, _, _, _, _, _, hMJ, _, _,
      hG, hGs, hGc, hphysical, _, hout, hPL, hPLi, hwhole, hW, _, hfacesW,
      hfix, hagree, _, hdegree, hcross⟩ :=
    exists_original_planar_other_faces_motion_with_crossings Source hSource hf hfi rfl
      he K hK g hgc hgi hSV hs hs3 hedges hcofaces Q hQ hinterior A hmap hA
      (D := ∅) isClosed_empty (disjoint_empty _) zero_lt_one
  have hGQ : G.space ⊆ Q.target := fun _ hx => hJQ (hMJ (hGs.subset hx).1)
  have hGt : G.space ⊆ convexHull ℝ (A '' (s : Set E)) :=
    fun _ hx => (hGs.subset hx).2
  have hedgeW : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      g '' convexHull ℝ (a : Set E) ⊆ W := by
    intro a ha _ ha2
    exact hfacesW a ha (by omega) (fun h => by rw [h, hs3] at ha2; omega)
  have hAtlas : ∀ y ∈ f '' Source.space, ∃ i, y ∈ (e i).source := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, P, V, _, _, _, hxV, hVP, hPe, _⟩ := hf.coordinates ⟨x, hx⟩
    exact ⟨i, hPe (hVP (mem_image_of_mem Subtype.val hxV))⟩
  have hboundary := ncard_surface_triangle_boundary_neighborSet_eq_one hAtlas K g hgi hSV
    hs hs3 hcofaces Q hQ A hmap hA
    G hG hGQ hGt Phi hW hedgeW hagree hphysical
  have hfinite := finite_original_triangle_graph_boundary K g hgi hs hs3 (f '' Source.space)
    hedges Q A hmap hA G Phi hedgeW hagree hphysical
  refine ⟨Phi, W, hW, hfix, ?_, hfacesW, hPL, hPLi,
    G, hG, subset_inter hGt hGQ, hGc, hphysical,
    fun v hv => hdegree v v.property hv, hboundary, hfinite, ?_⟩
  · intro x hx
    apply hout
    rintro ⟨y, hy, rfl⟩
    exact hx (Q.map_target (hJQ hy))
  · rintro w ⟨hwG, hwt⟩ O hO hwO
    obtain ⟨B, hwB, hBO, hBw, hB, hBi, hBS, hBT⟩ :=
      hcross w ⟨(hGs.subset hwG).1, hwt⟩ (O ∩ interior J.space)
        (hO.inter isOpen_interior) ⟨hwO, hTJ (intrinsicInterior_subset hwt)⟩
    refine ⟨B, hwB, hBO.trans inter_subset_left, hBw, hB, hBi, ?_, hBT⟩
    intro x hx
    exact (hwhole x (interior_subset (hBO hx).2)).trans (hBS x hx)

end PoincareConjecture.M76
