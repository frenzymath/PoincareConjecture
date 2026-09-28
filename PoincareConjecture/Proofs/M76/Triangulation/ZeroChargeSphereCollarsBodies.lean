import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeSphereCollarsData
import PoincareConjecture.Proofs.M76.Mathlib.TriangleMarkedPolygonSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AlternatingCutNeighborhoods










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}





theorem exists_sphere_collar_body_family
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) (c : ℝ)
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = c}) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)) (t : Fin (N + 3) → ℝ)
      (b : ∀ i, SphereCollarBody K (Q (finRotate (N + 3) i))),
      Q.HasSimplicialEdges ∧ Function.Injective Q ∧
      Q.boundary ℝ = K.space ∩ {x | A x = c} ∧
      (∀ i, t i ∈ Ioo (0 : ℝ) 1) ∧
      (∀ i, ∃ s ∈ K.faces, s.card = 3 ∧
        Q.edgeCut t i ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) ∧
      ∀ i (j : Bool),
        sphereCollarCenter (Q (finRotate (N + 3) i))
          (Q.edgeCut t (if j then finRotate (N + 3) i else i)) ∈
            interior (b i).carrier := by
  classical
  obtain ⟨m, V, hV, hVi, hVP, _, htriangles⟩ :=
    P.exists_subdivision_with_original_triangle_edges hP hPinj K hK hpure
      A hA c hsection.subset
  have hVS : V.boundary ℝ = K.space ∩ {x | A x = c} := hVP.trans hsection
  let coords : E ≃L[ℝ] (Fin 3 → ℝ) :=
    (LinearEquiv.ofFinrankEq E (Fin 3 → ℝ) (by simpa using hdim)).toContinuousLinearEquiv
  obtain ⟨M, C, L, J, hgeom⟩ := V.exists_original_vertex_event_bodies K hK hpure
    hcofaces hlinks (hVS.subset.trans inter_subset_left)
    (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _) coords
  have hvertex (i : Fin (m + 3)) : Nonempty (SphereCollarBody K (V i)) := by
    obtain ⟨hK0, hK0space, hbound, hM, hMK, hzero, hpureM, hcofacesM,
      hconn, hC, hcv, hzeroC, _, hdisj, hlocal, hface, hL, hrep, hJ, hJC, _⟩ := hgeom i
    let Z : Finset (E →ₗ[ℝ] ℝ) := Finset.univ.image (L i)
    refine ⟨{
      auxiliary := M i
      carrier := C i
      halfspaces := Z
      frontierComplex := J i
      original_finite := hK0
      original_space := hK0space
      original_bound := hbound
      auxiliary_finite := hM
      auxiliary_space := hMK
      zero_vertex := hzero
      pure := hpureM
      cofaces := hcofacesM
      connected_link := hconn
      compact := hC
      convex := hcv
      zero_interior := hzeroC
      disjoint_link := hdisj
      local_star := hlocal
      original_incidence := hface
      halfspaces_nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
      halfspaces_nonzero := ?_
      halfspaces_carrier := ?_
      frontier_finite := hJ
      frontier_space := hJC }⟩
    · intro B hB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      exact hL j
    · rw [hrep]
      ext x
      constructor
      · intro hx B hB
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
        exact hx j
      · intro hx j
        exact hx (L i j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  let v (i : Fin (m + 3)) : SphereCollarBody K (V i) := Classical.choice (hvertex i)
  let U (i : Fin (m + 3)) : Set E :=
    sphereCollarCenter (V i) ⁻¹' interior (v i).carrier
  have hU (i : Fin (m + 3)) : IsOpen (U i) :=
    isOpen_interior.preimage (sphereCollarCenter (V i)).continuous
  have hUconv (i : Fin (m + 3)) : Convex ℝ (U i) :=
    (v i).convex.interior.affine_preimage (sphereCollarCenter (V i)).toAffineEquiv.toAffineMap
  have hVU (i : Fin (m + 3)) : V i ∈ U i := by
    change -V i + V i ∈ interior (v i).carrier
    simpa only [neg_add_cancel] using (v i).zero_interior
  obtain ⟨α, β, hcuts, _⟩ := V.exists_alternating_cut_neighborhoods U hU hUconv hVU
  have hα (i) := (hcuts i).1
  have hβ (i) := (hcuts i).2.1
  choose s hs hsc htri using htriangles
  have hconnector (i : Fin (m + 3)) :
      ∃ b : SphereCollarBody K (V.edgeCut (fun _ => (1 / 2 : ℝ)) i),
        sphereCollarCenter (V.edgeCut (fun _ => (1 / 2 : ℝ)) i) ''
          segment ℝ (V.edgeCut α i) (V.edgeCut β i) ⊆ interior b.carrier := by
    let q := V.edgeCut (fun _ => (1 / 2 : ℝ)) i
    obtain ⟨M0, C0, Z0, J0, hK0, hK0space, hbound, hM0, hMK0, hzeroM,
      hpureM, hcofacesM, hconn, _, _, hC0, hcv0, hzeroC, hSC, _, hdisj,
      hlocal, hface, hZne, hZ, hrep, hJ0, hJC0, _⟩ :=
      K.exists_original_connector_body_in_centered_coordinates hK hpure hcofaces hlinks
        (hs i) (hsc i) (by
          rw [segment_eq_image_lineMap]
          exact isCompact_Icc.image AffineMap.lineMap_continuous)
        (convex_segment (V.edgeCut α i) (V.edgeCut β i))
        ((hcuts i).2.2.2.2.2.trans (htri i)) (hcuts i).2.2.2.2.1
        (sphereCollarCenter q) (by change -q + q = 0; exact neg_add_cancel q)
        isOpen_univ (subset_univ _) coords
    exact ⟨{
      auxiliary := M0
      carrier := C0
      halfspaces := Z0
      frontierComplex := J0
      original_finite := hK0
      original_space := hK0space
      original_bound := hbound
      auxiliary_finite := hM0
      auxiliary_space := hMK0
      zero_vertex := hzeroM
      pure := hpureM
      cofaces := hcofacesM
      connected_link := hconn
      compact := hC0
      convex := hcv0
      zero_interior := hzeroC
      disjoint_link := hdisj
      local_star := hlocal
      original_incidence := hface
      halfspaces_nonempty := hZne
      halfspaces_nonzero := hZ
      halfspaces_carrier := hrep
      frontier_finite := hJ0
      frontier_space := hJC0 }, hSC⟩
  choose bconn hbconn using hconnector
  let Q := V.midpointSubdivision
  let t := Polygon.midpointCutParameters α β
  have ht (i) : t i ∈ Ioo (0 : ℝ) 1 := Polygon.midpointCutParameters_mem α β hα hβ i
  have hbody (k : Fin ((m + 3) * 2)) :
      ∃ b : SphereCollarBody K (Q (finRotate ((m + 3) * 2) k)),
        ∀ j : Bool, sphereCollarCenter (Q (finRotate ((m + 3) * 2) k))
          (Q.edgeCut t (if j then finRotate ((m + 3) * 2) k else k)) ∈
            interior b.carrier := by
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · have hcenter : Q (finRotate ((m + 3) * 2) (finProdFinEquiv (i, (0 : Fin 2)))) =
          V.edgeCut (fun _ => (1 / 2 : ℝ)) i := by
        simp only [Q, Polygon.midpoint_rotate_zero, Polygon.midpointSubdivision_apply_one,
          Polygon.edgeCut]
      rw [hcenter]
      refine ⟨bconn i, ?_⟩
      intro j
      cases j
      · change sphereCollarCenter _ (Q.edgeCut t (finProdFinEquiv (i, (0 : Fin 2)))) ∈ _
        rw [V.midpointSubdivision_edgeCut_zero]
        exact hbconn i (mem_image_of_mem _ (left_mem_segment ℝ _ _))
      · change sphereCollarCenter _
          (Q.edgeCut t (finRotate ((m + 3) * 2) (finProdFinEquiv (i, (0 : Fin 2))))) ∈ _
        rw [Polygon.midpoint_rotate_zero, V.midpointSubdivision_edgeCut_one]
        exact hbconn i (mem_image_of_mem _ (right_mem_segment ℝ _ _))
    · have hcenter : Q (finRotate ((m + 3) * 2) (finProdFinEquiv (i, (1 : Fin 2)))) =
          V (finRotate (m + 3) i) := by
        simp only [Q, Polygon.midpoint_rotate_one, Polygon.midpointSubdivision_apply_zero]
      rw [hcenter]
      refine ⟨v (finRotate (m + 3) i), ?_⟩
      intro j
      cases j
      · change sphereCollarCenter _ (Q.edgeCut t (finProdFinEquiv (i, (1 : Fin 2)))) ∈ _
        rw [V.midpointSubdivision_edgeCut_one]
        exact (hcuts i).2.2.2.1
      · change sphereCollarCenter _
          (Q.edgeCut t (finRotate ((m + 3) * 2) (finProdFinEquiv (i, (1 : Fin 2))))) ∈ _
        rw [Polygon.midpoint_rotate_one, V.midpointSubdivision_edgeCut_zero]
        exact (hcuts (finRotate (m + 3) i)).2.2.1
  choose b hb using hbody
  have hmarks (k : Fin ((m + 3) * 2)) : ∃ s ∈ K.faces, s.card = 3 ∧
      Q.edgeCut t k ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    refine ⟨s i, hs i, hsc i, ?_⟩
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · rw [V.midpointSubdivision_edgeCut_zero]
      exact htri i ⟨α i, ⟨(hα i).1, (hα i).2.trans (by norm_num)⟩, rfl⟩
    · rw [V.midpointSubdivision_edgeCut_one]
      exact htri i ⟨β i, ⟨(by linarith [(hβ i).1]), (hβ i).2⟩, rfl⟩
  have hex : ∃ (L : ℕ) (Q : Polygon E L) (t : Fin L → ℝ)
      (b : ∀ i, SphereCollarBody K (Q (finRotate L i))),
      3 ≤ L ∧ Q.HasSimplicialEdges ∧ Function.Injective Q ∧
      Q.boundary ℝ = K.space ∩ {x | A x = c} ∧
      (∀ i, t i ∈ Ioo (0 : ℝ) 1) ∧
      (∀ i, ∃ s ∈ K.faces, s.card = 3 ∧
        Q.edgeCut t i ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) ∧
      ∀ i (j : Bool), sphereCollarCenter (Q (finRotate L i))
        (Q.edgeCut t (if j then finRotate L i else i)) ∈ interior (b i).carrier := by
    exact ⟨(m + 3) * 2, Q, t, b, by omega,
      (V.midpointSubdivision_simple hV hVi).1, (V.midpointSubdivision_simple hV hVi).2,
      V.midpointSubdivision_boundary.trans hVS, ht, hmarks, hb⟩
  obtain ⟨L, Q, t, b, hL, hQ, hQi, hQS, ht, hmarks, hb⟩ := hex
  obtain ⟨N, rfl⟩ : ∃ N, L = N + 3 := ⟨L - 3, by omega⟩
  exact ⟨N, Q, t, b, hQ, hQi, hQS, ht, hmarks, hb⟩

end PoincareConjecture.M76.ZeroChargeJoint
