import PoincareConjecture.Proofs.M76.Triangulation.GenericPLSphereSections
import PoincareConjecture.Proofs.M76.Mathlib.ZeroChargeHeightPerturbation
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSphereTopology
import PoincareConjecture.Proofs.M76.Mathlib.SinglePolygonPresentation

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_generic_single_polygon_height_of_zero_charge
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {C : Set F} {e : K.space ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3)
    (A : E →ᵃ[ℝ] ℝ)
    (hpres : ∀ c, HasAlexanderCurvePresentation (K.space ∩ {x | A x = c}) 0)
    (hsigns : ∀ x ∈ K.space,
      x ∈ closure ((K.space ∩ {y | A y = A x}) \ {x}) →
        x ∈ closure (K.space ∩ {y | A y < A x}) ∧
          x ∈ closure (K.space ∩ {y | A x < A y})) :
    ∃ (B : E →ᵃ[ℝ] ℝ) (p q : E),
      B.linear ≠ 0 ∧ InjOn B K.vertices ∧ p ∈ K.vertices ∧ q ∈ K.vertices ∧
      B p < B q ∧
      (∀ x ∈ K.space, B p ≤ B x ∧ B x ≤ B q) ∧
      K.space ∩ {x | B x = B p} = {p} ∧
      K.space ∩ {x | B x = B q} = {q} ∧
      (∀ c, HasAlexanderCurvePresentation (K.space ∩ {x | B x = c}) 0) ∧
      (∀ c ∈ Ioo (B p) (B q), ∃ n : ℕ, ∃ P : Polygon E (n + 3),
        Function.Injective P ∧ P.HasSimplicialEdges ∧
          P.boundary ℝ = K.space ∩ {x | B x = c}) ∧
      (∀ x ∈ K.space, B p < B x → B x < B q →
        x ∈ closure (K.space ∩ {y | B y < B x}) ∧
          x ∈ closure (K.space ∩ {y | B x < B y})) ∧
      ∀ v ∈ K.vertices,
        ((K.link v).vertexAbstractComplex.edgeGraph.induce
          {w : (K.link v).vertices | B (w : E) < B v}).Preconnected ∧
          ((K.link v).vertexAbstractComplex.edgeGraph.induce
            {w : (K.link v).vertices | B v < B (w : E)}).Preconnected := by
  have hconn := e.isConnected_of_convex_frontier hC hcv hne (by omega)
  have hnontrivial := e.nontrivial_of_convex_frontier hC hcv hne (by omega)
  obtain ⟨B, hB, _, hBlink⟩ :=
    K.exists_generic_height_with_preconnected_signed_links hK hpure hcofaces hlinks A hpres hsigns
  obtain ⟨p, q, hp, hq, hpq, hbound, hmin, hmax⟩ :=
    K.exists_unique_extreme_sections_of_generic_vertices hK hnontrivial B hB
  have hBlinear : B.linear ≠ 0 := by
    intro hz
    have h := B.linearMap_vsub q p
    change B.linear (q - p) = B q - B p at h
    rw [hz, LinearMap.zero_apply] at h
    exact hpq.ne' (sub_eq_zero.mp h.symm)
  have hlevels : ∀ c ∈ Ioo (B p) (B q), ∃ n : ℕ, ∃ P : Polygon E (n + 3),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = K.space ∩ {x | B x = c} := by
    intro c hc
    exact K.exists_intermediate_level_polygon_of_preconnected_signed_links hK
      hconn.isPreconnected hpure hcofaces hlinks he hC hcv hne hdim B hB hBlink
        hp hq hc.1 hc.2
  have hBpres : ∀ c, HasAlexanderCurvePresentation (K.space ∩ {x | B x = c}) 0 := by
    intro c
    rcases lt_trichotomy c (B p) with hc | hc | hc
    · have hempty : K.space ∩ {x | B x = c} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxc⟩
        exact (not_lt_of_ge (hbound x hx).1) (hxc.trans_lt hc)
      rw [hempty]
      exact subsingleton_empty.hasAlexanderCurvePresentation
    · rw [hc, hmin]
      exact (show ({p} : Set E).Subsingleton from
        subsingleton_singleton).hasAlexanderCurvePresentation
    · rcases lt_trichotomy c (B q) with hcq | hcq | hcq
      · obtain ⟨n, P, hPi, hPe, hPs⟩ := hlevels c ⟨hc, hcq⟩
        rw [← hPs]
        exact P.hasAlexanderCurvePresentation hPi hPe
      · rw [hcq, hmax]
        exact (show ({q} : Set E).Subsingleton from
          subsingleton_singleton).hasAlexanderCurvePresentation
      · have hempty : K.space ∩ {x | B x = c} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          rintro x ⟨hx, hxc⟩
          exact (not_lt_of_ge (hbound x hx).2) (hcq.trans_eq hxc.symm)
        rw [hempty]
        exact subsingleton_empty.hasAlexanderCurvePresentation
  have hgraphs := K.preconnected_signed_sublevel_graphs_of_preconnected_links hK
    (K.preconnected_edgeGraph_of_isPreconnected hK hconn.isPreconnected) B hB hBlink
  exact ⟨B, p, q, hBlinear, hB, hp, hq, hpq, hbound, hmin, hmax, hBpres,
    hlevels, fun x hx hpx hxq =>
      K.mem_both_height_closures_of_preconnected_sublevels hK B hB hgraphs hx hp hq hpx hxq,
    hBlink⟩

end Geometry.SimplicialComplex
