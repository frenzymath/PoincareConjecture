import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Periodic.LatticeWindow
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLIntervalImageGraph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import Mathlib.Topology.Perfect



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

theorem exists_finite_periodic_window_graph
    {p : ℝ} (hp : 0 < p) {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc (0 : ℝ) 1))
    (hne : (r '' Icc (0 : ℝ) 1).Nontrivial)
    {W : Set (ℝ × ℝ)} (hW : IsCompact W) :
    ∃ L : SimplicialComplex ℝ (ℝ × ℝ), L.faces.Finite ∧
      (∀ s ∈ L.faces, s.card ≤ 2) ∧ Preperfect L.space ∧
      ∀ z ∈ W, ((z.1 : AddCircle p), (z.2 : AddCircle p)) ∈
        (fun t => (((r t).1 : AddCircle p), ((r t).2 : AddCircle p))) '' Icc (0 : ℝ) 1 ↔
        z ∈ L.space := by
  classical
  have hcompact := isCompact_Icc.image_of_continuousOn hr.continuousOn
  obtain ⟨J, hJ⟩ := exists_finite_lattice_window hp hcompact hW
  let A (n : J) : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineMap.id ℝ (ℝ × ℝ) +
      ContinuousAffineMap.const ℝ (ℝ × ℝ) ((n.val.1 : ℝ) * p, (n.val.2 : ℝ) * p)
  have hA (n : J) : Function.Injective (A n) := by
    intro x y hxy
    exact add_right_cancel hxy
  have graphs (n : J) := (hr.postcomp (A n)).exists_interval_image_graph ∅ (by simp)
  choose K hK hKs hdim _ using graphs
  obtain ⟨L, hL, hLs, hfaces⟩ := SimplicialComplex.exists_finite_triangulation_iUnion K hK
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨n, t, ht, hst⟩ := hfaces s hs
    have hspan : (s : Set (ℝ × ℝ)) ⊆ affineSpan ℝ (t : Set (ℝ × ℝ)) :=
      (subset_convexHull ℝ _).trans (hst.trans (convexHull_subset_affineSpan _))
    exact ((L.indep hs).card_le_card_of_subset_affineSpan hspan).trans (hdim n t ht)
  · intro x hx
    rw [hLs] at hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hpre : IsPreconnected (K n).space := by
      rw [hKs n]
      exact isPreconnected_Icc.image _ (hr.postcomp (A n)).continuousOn
    have hnontriv : (K n).space.Nontrivial := by
      rw [hKs n, image_comp]
      exact hne.image (hA n)
    exact (hpre.preperfect_of_nontrivial hnontriv x hn).mono
      (Filter.principal_mono.mpr (fun y hy => hLs.symm ▸ mem_iUnion.mpr ⟨n, hy⟩))
  · intro z hz
    rw [show (fun t => (((r t).1 : AddCircle p), ((r t).2 : AddCircle p))) '' Icc (0 : ℝ) 1 =
        (fun x : ℝ × ℝ => ((x.1 : AddCircle p), (x.2 : AddCircle p))) ''
          (r '' Icc (0 : ℝ) 1) from image_comp
            (fun x : ℝ × ℝ => ((x.1 : AddCircle p), (x.2 : AddCircle p))) r _,
      hJ z hz, hLs]
    simp only [hKs, image_comp]
    rfl

end PoincareConjecture.M76.PeriodicSquare
