import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedFiniteModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.PolygonCircleModels

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_original_marked_surface_circle_incidence
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Nonempty X]
    (e : ι → OpenPartialHomeomorph X V3) (hX : IsCompact (univ : Set X))
    {R S M : Set X} (he : PLDomain e R) (hS : IsCompact S)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ psi (T y) = 0)) :
    ∃ (s : Finset (univ : Set X)) (F : X → (s → ℝ × V3))
      (K B : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X),
      Continuous F ∧ Function.Injective F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ B ≤ K ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      K.space = F '' S ∧ B.space = F '' (S ∩ M) ∧
      PolyhedralPLInCharts e g K.space ∧ InjOn g K.space ∧
      (∀ z ∈ K.space, F (g z) = z) ∧ g '' K.space = S ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, q.card = 3 ∧ t ⊆ q) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
      ∃ (m : ℕ) (J : Fin m → SimplicialComplex ℝ (s → ℝ × V3))
        (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (J i).space),
        (∀ i, J i ≤ B ∧ J i ≤ K ∧ (J i).faces.Finite ∧ (gamma i).IsFinitePL) ∧
        Pairwise (fun i j => Disjoint (J i).space (J j).space) ∧
        (⋃ i, (J i).space) = F '' (S ∩ M) ∧
        ∀ t, t ∈ B.faces ↔ ∃ i, t ∈ (J i).faces := by
  classical
  obtain ⟨s, F, K, B, g, hFc, hFi, hF, hK, hBK, hfull, hKs, hBs,
    hPL, hgi, hfg, hgs, hpure, hcounts, hlinks, hpolygons⟩ :=
    exists_original_marked_surface_finite_incidence_with_rim_polygons e hX he hS hlocal
  obtain ⟨m, J, gamma, hJ, hdis, hcover, hfaces⟩ :=
    B.exists_circle_subcomplexes_of_polygon_presentation (hK.subset hBK) hpolygons
  exact ⟨s, F, K, B, g, hFc, hFi, hF, hK, hBK, hfull, hKs, hBs,
    hPL, hgi, hfg, hgs, hpure, hcounts, hlinks, m, J, gamma,
    fun i => ⟨(hJ i).1, (hJ i).1.trans hBK, (hJ i).2⟩,
    hdis, hcover.trans hBs, hfaces⟩

end PoincareConjecture.M76
