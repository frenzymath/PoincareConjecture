import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.EssentialClosedComponent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DisjointComponentRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent










set_option autoImplicit false
open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains
open AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

open Classical in
theorem exists_common_essential_rim_component
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (gamma : Bool → C(sphere (0 : Fin 2 → ℝ) 1, K.space))
    (radial : C(K.space, sphere (0 : Fin 2 → ℝ) 1))
    (hleft : ∀ b u, radial (gamma b u) = u)
    (hrank :
      letI : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
      let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) ≤
        Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) + 2) :
    ∃ C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∀ b u, (gamma b u : E) ∈ (K.edgeComponentComplex C).space) ∧
        (K.edgeComponentComplex C).surfaceEulerCount = 0 := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let Q := sphere (0 : Fin 2 → ℝ) 1
  let : ConnectedSpace Q := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp) (0 : Fin 2 → ℝ) zero_le_one)
  have hcomp (b : Bool) :
      ∃ C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        ∀ u, (gamma b u : E) ∈ (K.edgeComponentComplex C).space := by
    have hc : IsConnected (range (fun u : Q ↦ (gamma b u : E))) :=
      isConnected_range (continuous_subtype_val.comp (gamma b).continuous)
    obtain ⟨C, hC⟩ := K.exists_edgeComponentComplex_of_isConnected hK hc
      (by rintro _ ⟨u, rfl⟩; exact (gamma b u).property)
    exact ⟨C, fun u ↦ hC (mem_range_self u)⟩
  choose C hC using hcomp
  let J (b : Bool) := K.edgeComponentComplex (C b)
  have hJ (b : Bool) : (J b).faces.Finite := hK.subset (K.edgeComponentComplex_le _)
  let (b : Bool) : Fintype (J b).vertices :=
    ((J b).finite_vertices_of_finite_faces (hJ b)).fintype
  have hp (b : Bool) : ∀ s ∈ (J b).faces,
      ∃ t ∈ (J b).faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hc⟩ := K.edgeComponentComplex_pure (C b)
      (fun s hs ↦ by obtain ⟨t, ht, hc, hst⟩ := hpure s hs; exact ⟨t, ht, hst, hc⟩) s hs
    exact ⟨t, ht, hc, hst⟩
  have hl (b : Bool) : ∀ v ∈ (J b).vertices, IsConnected ((J b).link v).space := by
    intro v hv
    rw [← (J b).faceLink_singleton_eq_link, K.edgeComponentComplex_vertex_link (C b) hv,
      K.faceLink_singleton_eq_link]
    exact hlinks v (K.edgeComponentComplex_le _ hv)
  have ht (b : Bool) : ∀ s ∈ (J b).faces, s.card = 2 →
      {t : Finset E | t ∈ (J b).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
    intro s hs hc
    rw [K.edgeComponentComplex_cofaces (C b) hs 3]
    exact hcofaces s (K.edgeComponentComplex_le _ hs) hc
  have hjconn (b : Bool) : IsConnected (J b).space :=
    (K.edgeComponentComplex_isPathConnected (C b)).isConnected
  have hbound (b : Bool) :
      (J b).surfaceEulerCount ≤ 0 ∧
      Module.finrank (ZMod 2) (LinearMap.range
        (vertexCoboundary (J b).vertexAbstractComplex.toPreAbstractSimplicialComplex)) + 2 ≤
      Module.finrank (ZMod 2) (LinearMap.ker
        (edgeCoboundary (J b).vertexAbstractComplex.toPreAbstractSimplicialComplex)) := by
    let g : C(Q, (J b).space) :=
      ⟨fun u ↦ ⟨gamma b u, hC b u⟩,
        (continuous_subtype_val.comp (gamma b).continuous).subtype_mk _⟩
    let r : C((J b).space, Q) :=
      ⟨fun x ↦ radial ⟨x, space_subset_of_le (K.edgeComponentComplex_le _) x.property⟩,
        radial.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
    apply (J b).closed_surface_rank_ge_two_of_rim_retraction (hJ b) (hp b) (hjconn b)
      (by intro v hv; convert! hl b v hv) (ht b) number
      (hnumber.mono (fun _ hv ↦ K.edgeComponentComplex_le _ hv)) sign
      (by intro t ht hc u hu huc htu s hsc hst hsu
          convert! hcancel t ht.1 hc u hu.1 huc htu s hsc hst hsu) g r
    exact hleft b
  have heq : C false = C true := by
    by_contra hne
    have hsum := K.disjoint_closed_subcomplex_rank_bound (J false) (J true)
      (K.edgeComponentComplex_le _) (K.edgeComponentComplex_le _)
      (K.pairwise_disjoint_edgeComponentComplex_space hne)
      (fun hs ht hst ↦ K.edgeComponentComplex_coface _ hs ht hst)
      (fun hs ht hst ↦ K.edgeComponentComplex_coface _ hs ht hst)
    have h0 := (hbound false).2
    have h1 := (hbound true).2
    dsimp only at hrank
    omega
  have hmono := K.closed_subcomplex_rank_bound (J false)
    (K.edgeComponentComplex_le _)
    (fun hs ht hst ↦ K.edgeComponentComplex_coface _ hs ht hst)
  have hid := (J false).closed_surface_incidence_rank_identity (hJ false) (hp false)
    (hjconn false) (by intro v hv; convert! hl false v hv) (ht false)
  have hnonpos := (hbound false).1
  refine ⟨C false, ?_, ?_⟩
  · intro b u
    cases b with
    | false => exact hC false u
    | true => simpa only [heq] using hC true u
  · dsimp only at hid hrank
    change (J false).surfaceEulerCount = 0
    omega

end Geometry.SimplicialComplex
