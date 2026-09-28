import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalDomainCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

open Classical in

theorem exists_standard_boundary_circle_triangulation
    {R S : Set V3} (hR : IsCompact R)
    (he : PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hS : S ⊆ frontier R) (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL) :
    ∃ K A L : SimplicialComplex ℝ V3,
      K.faces.Finite ∧ A ≤ K ∧ L ≤ A ∧
      K.space = R ∧ A.space = frontier R ∧ L.space = S ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ A.vertices) → t ∈ A.faces) ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces) ∧
      ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph V3 V3,
        B ∈ piecewiseAffineGroupoid V3 ∧ (K.closedStar p).space ⊆ B.source ∧
        (K.closedStar p).AffineOnFaces B ∧
        (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) := by
  classical
  let e := fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph
  have hid : ∀ j : Unit, LocallyPiecewiseAffineOn (id ∘ (e j).symm) (e j).target := by
    intro j
    exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) isOpen_univ
  obtain ⟨K0, A0, _, hK0, hA0K, hA0, hK0s, hA0s, _, _⟩ :=
    OpenPartialHomeomorph.exists_finite_PL_domain_image_pair e he.cover continuous_id hid
      hR (fun _ _ _ _ h => h) he.halfspace
  simp only [image_id] at hK0s hA0s
  obtain ⟨g, hg, hgv⟩ := hgamma
  obtain ⟨L0, hL0, hL0s⟩ := hg.exists_finite_triangulation_image
  have hgS : g '' Q2 = S := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (hgv ⟨q, hq⟩) ▸ (gamma ⟨q, hq⟩).property
    · intro hz
      let q := gamma.symm ⟨z, hz⟩
      exact ⟨q, q.property, (hgv q).symm.trans
        (congrArg Subtype.val (gamma.apply_symm_apply ⟨z, hz⟩))⟩
  have hL0s' : L0.space = S := hL0s.trans hgS
  have hIdPL : PolyhedralPLInCharts e id K0.space := by
    refine ⟨continuousOn_id, ?_⟩
    intro q
    exact ⟨(), K0, univ, hK0, subset_rfl, isOpen_univ, mem_univ _,
      fun _ hz => by obtain ⟨x, _, rfl⟩ := hz; exact x.property,
      fun _ _ => mem_univ _,
      (K0.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK0⟩
  choose B hpoint hcompat hkind using fun q : K0.space =>
    he.exists_local_region_chart ⟨q, hK0s ▸ q.property⟩
  let marks : Bool → SimplicialComplex ℝ V3 := fun b => if b then L0 else A0
  have hmarks (b : Bool) : (marks b).faces.Finite := by cases b <;> assumption
  have hmarksK (b : Bool) : (marks b).space ⊆ K0.space := by
    cases b
    · exact space_subset_of_le hA0K
    · change L0.space ⊆ K0.space
      rw [hL0s', hK0s]
      exact hS.trans he.closed.frontier_subset
  obtain ⟨K, M, hK, hKK0, hM, hstars⟩ := hIdPL.exists_full_compatible_chart_stars
    K0 hK0 B hcompat hpoint marks hmarks hmarksK
  have hAs : (M false).space = frontier R := (hM false).2.1.trans hA0s
  have hLs : (M true).space = S := (hM true).2.1.trans hL0s'
  have hLA : M true ≤ M false := by
    intro t ht
    apply (hM false).2.2 t ((hM true).1 ht)
    intro v hv
    have hvL := (M true).face_subset_vertices ht hv
    have hvA : v ∈ (M false).space := hAs.symm ▸ hS (hLs ▸ (M true).vertices_subset_space hvL)
    obtain ⟨u, hu, hvu⟩ := mem_space_iff.mp hvA
    exact (M false).face_subset_vertices hu
      ((K.vertex_mem_convexHull_iff ((hM true).1 hvL) ((hM false).1 hu)).mp hvu)
  refine ⟨K, M false, M true, hK, (hM false).1, hLA,
    hKK0.space_eq.trans hK0s, hAs, hLs, (hM false).2.2, (hM true).2.2, ?_⟩
  intro p hp
  obtain ⟨q, hsource, hface⟩ := hstars p hp
  have hB : B q ∈ piecewiseAffineGroupoid V3 := by
    simpa only [e, Homeomorph.refl_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_trans] using hcompat q ()
  refine ⟨B q, hB, hsource, hface, ?_⟩
  rcases hkind q with hinside | ⟨ell, v, hv, _, hhalf⟩
  · exact Or.inl hinside
  · exact Or.inr ⟨ell, v, hv, hhalf⟩

end PoincareConjecture.M76.Dehn
