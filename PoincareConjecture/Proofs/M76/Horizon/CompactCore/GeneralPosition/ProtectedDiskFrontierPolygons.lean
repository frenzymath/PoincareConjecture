import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalDiskFrontierPolygons











set_option autoImplicit false

namespace PoincareConjecture.M76

open Set Geometry Geometry.SimplicialComplex unitInterval

theorem PLDomain.exists_protected_disk_frontier_polygons
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
    [TopologicalSpace X] [Nonempty X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hdim : Module.finrank ℝ E = 2)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (f : E → X) (hf : PolyhedralPLInCharts e f K.space) (hfY : MapsTo f K.space Y)
    (hboundary : ∀ x ∈ frontier K.space, f x ∉ F) :
    ∃ (G : C(I × K.space, X)) (g : E → X) (S : Set (Set E)),
      (∀ z, G z ∈ Y) ∧ (∀ x : K.space, G (0, x) = f x) ∧
      (∀ x : K.space, G (1, x) = g x) ∧
      (∀ (t : I) (x : K.space), (x : E) ∈ frontier K.space → G (t, x) = f x) ∧
      PolyhedralPLInCharts e g K.space ∧ S.Finite ∧
      (∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon E (n + 3),
        Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s) ∧
      S.PairwiseDisjoint id ∧ K.space ∩ g ⁻¹' F = ⋃ s ∈ S, s ∧
      ∀ s ∈ S, s ⊆ interior K.space := by
  classical
  obtain ⟨R, L, hR, hRK, _, hstars⟩ := hN.exists_protected_frontier_map_stars hY hcut
    K hK hf hfY (fun i : Empty => i.elim) (fun i => i.elim) (fun i => i.elim)
  choose B hBY hcompat hsource hcoord hkind using fun v : R.vertices => hstars v v.property
  have hkind' (v : R.vertices) : Disjoint (B v).source F ∨ ∃ ell : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ,
      (∀ y ∈ (B v).source, y ∈ N ↔ 0 ≤ ell (B v y)) ∧
      ∀ y ∈ (B v).source, y ∈ F ↔ ell (B v y) = 0 := by
    rcases hkind v with hd | ⟨ell, _, _, hN, hF⟩
    · exact Or.inl hd
    · exact Or.inr ⟨ell, hN, hF⟩
  obtain ⟨G, g, S, hGY, hG0, hG1, hGfixed, hg, hS, hpoly, hdisjoint, hcover, hinterior⟩ :=
    hN.exists_original_disk_frontier_polygons hY hcut R hR hdim
      (hRK.space_eq.symm ▸ hcv) (hRK.space_eq.symm ▸ hne) f
      (hRK.space_eq.symm ▸ hfY) B hcompat hsource hcoord hkind'
      (hRK.space_eq.symm ▸ hboundary)
  let G' : C(I × K.space, X) := G.comp
    ⟨fun z => (z.1, ⟨z.2, hRK.space_eq.symm.subset z.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  refine ⟨G', g, S, fun z => hGY _, fun x => hG0 _, fun x => hG1 _, ?_,
    hRK.space_eq ▸ hg, hS, hpoly, hdisjoint, hRK.space_eq ▸ hcover,
    hRK.space_eq ▸ hinterior⟩
  intro t x hx
  exact hGfixed t ⟨x, hRK.space_eq.symm.subset x.property⟩ (by simpa only [hRK.space_eq] using hx)

end PoincareConjecture.M76
