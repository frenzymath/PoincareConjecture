import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.Orientation.SimultaneousChartStars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CyclicBoundaryAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedChartSubdivision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.ClosedPhaseSphere
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition










set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Metric Geometry AbstractSimplicialComplex PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

open Classical in
theorem exists_hamiltonZero_original_cyclic_marked_annulus
    {E ι β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [Fintype β] [Nonempty β]
    (e : ι → OpenPartialHomeomorph X0 V3) {N S M : Set X0}
    (he : PLDomain e N) (hSN : S ⊆ frontier N)
    (K0 B0 : SimplicialComplex ℝ E) (hK0 : K0.faces.Finite) (hB0K : B0 ≤ K0)
    (H0 : K0.space ≃ₜ S) (g : E → X0)
    (hH0 : ∀ z : K0.space, (H0 z : X0) = g z)
    (hgPL : PolyhedralPLInCharts e g K0.space)
    (hB0M : ∀ z ∈ K0.space, g z ∈ M ↔ z ∈ B0.space)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X0 V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ psi (T y) = 0))
    (L : β → SimplicialComplex ℝ E) (hLB : ∀ i, L i ≤ B0)
    (hdis : Pairwise (fun i j => Disjoint (L i).space (L j).space))
    (hcover : (⋃ i, (L i).space) = B0.space)
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hconn : IsConnected K0.space) (x : K0.space)
    [IsCyclic (FundamentalGroup K0.space x)] [Nontrivial (FundamentalGroup K0.space x)] :
    ∃ order : Bool ≃ β, ∃ A : squareAnnulus 8 1 ≃ₜ K0.space,
      A.IsFinitePL ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = -1 ↔
        (A p : E) ∈ (L (order false)).space) ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = 1 ↔
        (A p : E) ∈ (L (order true)).space) ∧
      ∃ f : (ℝ × ℝ) → X0, PolyhedralPLInCharts e f (squareAnnulus 8 1) ∧
        ∀ p : squareAnnulus 8 1, f p = g (A p) := by
  classical
  have hgS (z : K0.space) : g z ∈ S := by rw [← hH0 z]; exact (H0 z).property
  choose T hpT hcT hkT using fun z : K0.space => hlocal (g z) (hgS z)
  choose C hpC hcC hkC using fun z : K0.space =>
    he.exists_local_region_chart ⟨g z, he.closed.frontier_subset (hSN (hgS z))⟩
  let marks0 : Option β → SimplicialComplex ℝ E := fun i => i.elim B0 L
  have hm0 (i : Option β) : marks0 i ≤ K0 := by
    cases i with
    | none => exact hB0K
    | some i => exact (hLB i).trans hB0K
  obtain ⟨K, marks, hK, hKK0, hmarks, hstars⟩ :=
    hgPL.exists_full_simultaneous_compatible_chart_stars K0 hK0 T C hcT hcC hpT hpC
      marks0 (fun i => hK0.subset (hm0 i))
      (fun i => SimplicialComplex.space_subset_of_le (hm0 i))
  let B := marks none
  let rims (i : β) := marks (some i)
  have hBK : B ≤ K := (hmarks none).1
  have hBs : B.space = B0.space := (hmarks none).2.1
  have hrK (i : β) : rims i ≤ K := (hmarks (some i)).1
  have hrs (i : β) : (rims i).space = (L i).space := (hmarks (some i)).2.1
  let H : K.space ≃ₜ S := (Homeomorph.setCongr hKK0.space_eq).trans H0
  have hH (z : K.space) : (H z : X0) = g z := hH0 ⟨z, hKK0.space_eq ▸ z.property⟩
  have hgi : InjOn g K.space := by
    intro a ha b hb hab
    have hh : H ⟨a, ha⟩ = H ⟨b, hb⟩ := Subtype.ext
      ((hH ⟨a, ha⟩).trans (hab.trans (hH ⟨b, hb⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have hBM (z : E) (hz : z ∈ K.space) : g z ∈ M ↔ z ∈ B.space := by
    rw [hBs]
    exact hB0M z (hKK0.space_eq ▸ hz)
  have hsurface : ∀ p ∈ K.vertices, ∃ D : OpenPartialHomeomorph X0 V3,
      MapsTo g (K.closedStar p).space D.source ∧
      (K.closedStar p).AffineOnFaces (fun z => D (g z)) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ D.source, y ∈ S ↔ ell (D y) = 0) ∧ Disjoint D.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ D.source, y ∈ S ↔ ell (D y) = 0 ∧ 0 ≤ psi (D y)) ∧
          ∀ y ∈ D.source, y ∈ M ↔ psi (D y) = 0) := by
    intro p hp
    obtain ⟨q, hqT, hqTf, _, _⟩ := hstars p hp
    exact ⟨T q, hqT, hqTf, hkT q⟩
  obtain ⟨hpure, hcounts, hlinks⟩ :=
    K.marked_surface_incidence_of_planar_halfspace_stars B hK hBK
      (hmarks none).2.2 (marked_surface_planar_halfspace_stars K B hK H g hH hBM hsurface)
  have hfront : MapsTo g K.space (frontier N) := by
    intro z hz
    apply hSN
    rw [← hH ⟨z, hz⟩]
    exact (H ⟨z, hz⟩).property
  obtain ⟨number, sign, hnumber, hcancel⟩ :=
    exists_hamiltonZero_frontier_geometric_coface_signs e he.cover he.compatible K K
      le_rfl hK g N (by simpa only [hKK0.space_eq] using hgPL.continuousOn) hgi hfront
      (by
        intro p hp
        obtain ⟨q, _, _, hqC, hqCf⟩ := hstars p hp
        refine ⟨C q, hcC q, hqC, hqCf, ?_⟩
        rcases hkC q with hi | ⟨ell, v, hv, _, hs⟩
        · exact Or.inl hi
        · exact Or.inr ⟨ell, v, hv, hs⟩)
  have hrf (s : Finset E) (hs : s ∈ K.faces) :
      s ∈ B.faces ↔ ∃ i, s ∈ (rims i).faces := by
    constructor
    · intro hsB
      obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
        (Finset.coe_nonempty.mpr (B.nonempty_of_mem_faces hsB)).convexHull
      have hzB := B.convexHull_subset_space hsB (intrinsicInterior_subset hz)
      obtain ⟨i, hzi⟩ := mem_iUnion.mp (hcover.symm.subset (hBs.subset hzB))
      exact ⟨i, K.face_mem_subcomplex_of_intrinsicInterior (rims i) (hrK i) hs hz
        ((hrs i).symm.subset hzi)⟩
    · rintro ⟨i, hsi⟩
      apply K.le_of_common_subcomplex_space_subset (rims i) B (hrK i) hBK _ hsi
      rw [hrs i, hBs]
      exact SimplicialComplex.space_subset_of_le (hLB i)
  let gamma' (i : β) := (gamma i).trans (Homeomorph.setCongr (hrs i).symm)
  have hg' (i : β) : (gamma' i).IsFinitePL :=
    (hgamma i).trans (Homeomorph.isFinitePL_setCongr (hrs i).symm (L i)
      (hK0.subset ((hLB i).trans hB0K)) rfl)
  let xK : K.space := ⟨x, hKK0.space_eq.symm ▸ x.property⟩
  have htransfer (U : Set E) (hU : U = K0.space) :
      IsCyclic (FundamentalGroup U ⟨x, hU.symm ▸ x.property⟩) ∧
        Nontrivial (FundamentalGroup U ⟨x, hU.symm ▸ x.property⟩) := by
    subst U
    exact ⟨inferInstance, inferInstance⟩
  let : IsCyclic (FundamentalGroup K.space xK) := (htransfer K.space hKK0.space_eq).1
  let : Nontrivial (FundamentalGroup K.space xK) := (htransfer K.space hKK0.space_eq).2
  obtain ⟨order, A, hA, ha, hb⟩ :=
    exists_marked_annulus_of_nontrivial_isCyclic_and_geometric_signs K hK
      (by intro s hs; obtain ⟨t, ht, hst, htc⟩ := hpure s hs; exact ⟨t, ht, htc, hst⟩)
      (hKK0.space_eq.symm ▸ hconn)
      (by
        intro v hv
        have hl := hlinks v hv
        rw [K.faceLink_singleton_eq_link] at hl
        convert! hl)
      rims hrK (by intro i j hij; simpa only [hrs] using hdis hij) gamma' hg'
      (by
        intro s hs hsc
        have hc : (K.faceLink s).vertices.ncard =
            {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard := by
          simpa only [hsc] using K.ncard_faceLink_vertices_eq_cofaces s
        rw [← hc, hcounts s hs hsc, hrf s hs]
        by_cases h : ∃ i, s ∈ (rims i).faces <;> simp only [h, if_true, if_false])
      number hnumber sign (by convert! hcancel) xK
  let A0 := A.trans (Homeomorph.setCongr hKK0.space_eq)
  have hA0 : A0.IsFinitePL := hA.trans (Homeomorph.isFinitePL_setCongr hKK0.space_eq K hK rfl)
  refine ⟨order, A0, hA0, ?_, ?_, ?_⟩
  · intro p
    change depth 8 (p : ℝ × ℝ) = -1 ↔ (A p : E) ∈ (L (order false)).space
    simpa only [hrs] using ha p
  · intro p
    change depth 8 (p : ℝ × ℝ) = 1 ↔ (A p : E) ∈ (L (order true)).space
    simpa only [hrs] using hb p
  · obtain ⟨a, haPL, haa⟩ := hA0
    have hamap : MapsTo a (squareAnnulus 8 1) K0.space := by
      intro y hy
      rw [← haa ⟨y, hy⟩]
      exact (A0 ⟨y, hy⟩).property
    obtain ⟨P, hP, hPs, hPa⟩ := haPL
    refine ⟨g ∘ a, ?_, fun p => congrArg g (haa p).symm⟩
    rw [← hPs]
    exact hgPL.comp_finitePiecewiseAffineOn P hP ⟨P, hP, rfl, hPa⟩
      (by simpa only [hPs] using hamap)

end PoincareConjecture.M76
