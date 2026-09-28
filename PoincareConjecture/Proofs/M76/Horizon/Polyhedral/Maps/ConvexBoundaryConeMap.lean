import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone
import PoincareConjecture.Proofs.M76.Mathlib.ConicalPlaneExtension
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps

set_option autoImplicit false

open Set Geometry NormedSpace

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem AffineOnFaces.exists_convex_boundary_cone
    {K : SimplicialComplex ℝ E} {b : E → F} (hb : K.AffineOnFaces b)
    (hK : K.faces.Finite) {S : Set E} (hS : IsCompact S) (hScv : Convex ℝ S)
    (hS0 : (0 : E) ∈ interior S) (hKS : K.space = frontier S)
    {W : Set F} (hW : Convex ℝ W) (hbW : MapsTo b (frontier S) W)
    (a : F) (ha : a ∈ W) :
    ∃ (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
      (hrad : InjOn (normalize : E → E) K.space) (g : E → F),
      (K.coneAtZero hlin hrad).space = S ∧
      (K.coneAtZero hlin hrad).AffineOnFaces g ∧
      FinitePiecewiseAffineOn g S ∧ g 0 = a ∧ EqOn g b (frontier S) ∧
      MapsTo g S W ∧
      ∀ u ∈ frontier S, ∀ r ∈ Icc (0 : ℝ) 1,
        g (r • u) = (1 - r) • a + r • b u := by
  classical
  let hlin := K.linearIndependent_faces_of_space_subset_frontier hScv hS0 hKS.subset
  let hrad : InjOn (normalize : E → E) K.space :=
    (hScv.injOn_normalize_frontier hS0).mono hKS.subset
  let C := K.coneAtZero hlin hrad
  have hCS : C.space = S := K.coneAtZero_space_of_frontier hlin hrad hS hScv hS0 hKS
  have h0not : (0 : E) ∉ K.space := by
    intro hx
    exact (hKS.subset hx).2 hS0
  let v : E → F := fun x => if x = 0 then a else b x
  obtain ⟨g, hg, hgv⟩ := C.exists_affineOnFaces_eqOn_vertices v
  have hg0 : g 0 = a := by
    rw [hgv (zero_mem_coneAtZero_vertices hlin hrad)]
    simp [v]
  have hgK : K.AffineOnFaces g := fun s hs => hg s (le_coneAtZero hlin hrad hs)
  have hgb : EqOn g b K.space :=
    hgK.eqOn_of_eqOn_vertices hb (fun x hx => by
      rw [hgv (le_coneAtZero hlin hrad hx)]
      exact if_neg (fun h : x = 0 => h0not (h ▸ K.vertices_subset_space hx)))
  have hgPL : FinitePiecewiseAffineOn g S :=
    hCS ▸ hg.finitePiecewiseAffineOn (finite_coneAtZero_faces hK hlin hrad)
  have hgW : MapsTo g S W := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp (hCS.symm.subset hx)
    have hvW : g '' (s : Set E) ⊆ W := by
      rintro _ ⟨y, hy, rfl⟩
      have hyv : y ∈ C.vertices := C.down_closed hs
        (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty y)
      rw [hgv hyv]
      by_cases hy0 : y = 0
      · simpa [v, hy0] using ha
      · have hyK : y ∈ K.vertices := by
          have hh := hyv
          rw [coneAtZero_vertices] at hh
          exact hh.resolve_left hy0
        simpa [v, hy0] using hbW (hKS.subset (K.vertices_subset_space hyK))
    exact (convexHull_min hvW hW) (hg.mapsTo_convexHull hs (Subset.refl _) hxs)
  refine ⟨hlin, hrad, g, hCS, hg, hgPL, hg0, hKS ▸ hgb, hgW, ?_⟩
  intro u hu r hr
  let t : F →ᴬ[ℝ] F := (ContinuousAffineEquiv.constVAdd ℝ F (-a)).toContinuousAffineMap
  have hsub : C.AffineOnFaces (t ∘ g) := hg.postcomp t
  have hsub0 : (t ∘ g) 0 = 0 := by
    change -a + g 0 = 0
    rw [hg0, neg_add_cancel]
  have h := hsub.smul_on_cone hsub0 u (hKS.symm.subset hu) r hr
  change -a + g (r • u) = r • (-a + g u) at h
  rw [hgb (hKS.symm.subset hu)] at h
  calc
    g (r • u) = a + r • (-a + b u) := by rw [← h]; abel
    _ = (1 - r) • a + r • b u := by module

end Geometry.SimplicialComplex
