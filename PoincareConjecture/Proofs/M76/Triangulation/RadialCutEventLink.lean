import PoincareConjecture.Proofs.M76.Mathlib.ActualCutPoleSurfaceGerms
import PoincareConjecture.Proofs.M76.Mathlib.SurfaceLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.RadialFrontierHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarConvexCone
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone

set_option autoImplicit false

open Set Geometry NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_radial_cut_event_link
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hconn : (K.link 0).vertexAbstractComplex.edgeGraph.Connected)
    (A : E →ₗ[ℝ] ℝ)
    (hlinkzero : ((K.link 0).space ∩ {x | A x = 0}).ncard = 2)
    (hlinkneg : ∃ x ∈ (K.link 0).space, A x < 0)
    (hlinkpos : ∃ x ∈ (K.link 0).space, 0 < A x)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hdisj : Disjoint C (K.link 0).space)
    (hlocal : K.space ∩ C = (K.closedStar 0).space ∩ C)
    {ι : Type*} [Finite ι] [Nonempty ι] (Z : ι → E →ₗ[ℝ] ℝ)
    (hZ : ∀ i, Z i ≠ 0) (hrep : C = {x | ∀ i, Z i x ≤ 1})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJC : J.space = frontier C)
    (a : Bool → E) (ha : ∀ j, a j ∈ K.space)
    (haC : ∀ j, a j ∈ interior C)
    (hdir : normalize (a false) ≠ normalize (a true))
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hheight : ∀ j x, (L j x).1.1 = A x)
    (σ : Bool → ℝ) (hσ : ∀ j, σ j ≠ 0)
    (hLa : ∀ j, L j (a j) = ((0, σ j), 0)) :
    ∃ (B : SimplicialComplex ℝ E) (n : ℕ) (P : Polygon E (n + 3))
      (p : Bool → E) (ρ : Bool → ℝ),
      B.faces.Finite ∧ B.space = C ∧ P.HasSimplicialEdges ∧ Function.Injective P ∧
      P.boundary ℝ = frontier C ∩ K.space ∧
      C ∩ K.space = convexJoin ℝ {0} (P.boundary ℝ) ∧
      (∀ j, p j ∈ frontier C ∧ p j ∈ (K.closedStar 0).space ∧
        1 < ρ j ∧ p j = ρ j • a j) ∧
      p false ≠ p true ∧
      P.boundary ℝ ∩ {x | A x = 0} = {p false, p true} ∧
      (∃ x ∈ P.boundary ℝ, A x < 0) ∧ ∃ x ∈ P.boundary ℝ, 0 < A x := by
  classical
  have hastar (j : Bool) : a j ∈ (K.closedStar 0).space :=
    (hlocal.subset ⟨ha j, interior_subset (haC j)⟩).1
  have hrad (j : Bool) := hC.exists_frontier_radial_pole_of_linear_image hcv hzero
    (L j) (interior_subset (haC j)) (hσ j) (hLa j)
  choose p ρ hpC hρ hpa _ _ hstrict using hrad
  have hρpos (j : Bool) : 0 < ρ j := zero_lt_one.trans_le (hρ j)
  have hpstar (j : Bool) : p j ∈ (K.closedStar 0).space :=
    K.mem_closedStar_of_frontier_positive_smul hC.isClosed hcv hzero hdisj
      (hastar j) (hpC j) (hρpos j) (hpa j)
  have hpne : p false ≠ p true := by
    intro heq
    have h := congrArg (normalize : E → E) heq
    rw [hpa false, hpa true, normalize_smul_of_pos (hρpos false),
      normalize_smul_of_pos (hρpos true)] at h
    exact hdir h
  have hpzero (j : Bool) : A (p j) = 0 := by
    have hazero : A (a j) = 0 := by
      rw [← hheight j (a j), hLa j]
    rw [hpa j, map_smul, hazero, smul_zero]
  obtain ⟨m, Q, hQi, hQ, hQlink⟩ :=
    K.exists_surface_link_polygon hK hpure hcofaces 0 hconn
  obtain ⟨n, P, hPi, hP, hPb⟩ :=
    K.exists_polygon_closedStar_convex_frontier hK Q hQ hQi hQlink
      hC hcv hzero hdisj Z hZ hrep
  have hPS : P.boundary ℝ = frontier C ∩ K.space := by
    rw [hPb]
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, space_subset_of_le
        (show K.closedStar 0 ≤ K from fun _ ht => ht.1) hx.1⟩
    · intro hx
      exact ⟨(hlocal.subset ⟨hx.2, hC.isClosed.frontier_subset hx.1⟩).1, hx.1⟩
  have hPrad : P.boundary ℝ = frontier C ∩
      normalize ⁻¹' (normalize '' (K.link 0).space) := by
    rw [hPb]
    exact (K.radial_frontier_section_eq_closedStar_inter hC.isClosed hcv hzero hdisj).symm
  obtain ⟨hzeroCard, hnegative, hpositive⟩ :=
    hC.radial_frontier_section_height_data hcv hzero K.zero_notMem_link_space
      K.injOn_normalize_link hPrad A
  have hpPzero (j : Bool) : p j ∈ P.boundary ℝ ∩ {x | A x = 0} :=
    ⟨hPb.symm.subset ⟨hpstar j, hpC j⟩, hpzero j⟩
  have hPzero : P.boundary ℝ ∩ {x | A x = 0} = {p false, p true} := by
    apply Eq.symm
    refine Set.eq_of_subset_of_ncard_le
      (pair_subset (hpPzero false) (hpPzero true)) ?_ ?_
    · rw [hzeroCard, hlinkzero, ncard_pair hpne]
    · exact finite_of_ncard_ne_zero (by rw [hzeroCard, hlinkzero]; norm_num)
  have hPne : ((K.closedStar 0).space ∩ frontier C).Nonempty :=
    ⟨p false, hpstar false, hpC false⟩
  have hcone : convexJoin ℝ {0} (P.boundary ℝ) = K.space ∩ C := by
    rw [hPb, K.convexJoin_closedStar_frontier_eq_inter hC hcv hzero hdisj hPne]
    exact hlocal.symm
  have hlin := J.linearIndependent_faces_of_space_subset_frontier hcv hzero hJC.subset
  have hnorm : InjOn (normalize : E → E) J.space :=
    (hcv.injOn_normalize_frontier hzero).mono hJC.subset
  let B := J.coneAtZero hlin hnorm
  have hB : B.faces.Finite := finite_coneAtZero_faces hJ hlin hnorm
  have hBC : B.space = C := J.coneAtZero_space_of_frontier hlin hnorm hC hcv hzero hJC
  exact ⟨B, n, P, p, ρ, hB, hBC, hP, hPi, hPS,
    (inter_comm C K.space).trans hcone.symm,
    fun j => ⟨hpC j, hpstar j, hstrict j (haC j), hpa j⟩,
    hpne, hPzero, hnegative.mpr hlinkneg, hpositive.mpr hlinkpos⟩

end Geometry.SimplicialComplex
