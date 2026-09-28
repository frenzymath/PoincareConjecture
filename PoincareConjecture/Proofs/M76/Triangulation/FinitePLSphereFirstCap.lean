import PoincareConjecture.Proofs.M76.Triangulation.MarkedFinitePLSphereIncidence
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderBaseFirstSection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Mathlib.PlanarDiskConvexContainment

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePL.exists_first_height_cap_ball
    {s : Set E} {C : Set F} {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdimF : Module.finrank ℝ F = 3) (hdimE : Module.finrank ℝ E = 3)
    {p : E} (hp : p ∈ s) (A : E →ᵃ[ℝ] ℝ) (hpA : A p = 0)
    (hmin : ∀ x ∈ s, 0 ≤ A x) (hzero : s ∩ {x | A x = 0} = {p})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β ∈ Ioo (0 : ℝ) ε, ∃ d : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d (s ∩ {x | A x = β}) ∧
      (∀ x ∈ d, A x = β) ∧ d ∩ s = s ∩ {x | A x = β} ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {p} d)
        (d ∪ (s ∩ {x | A x ≤ β})) ∧
      convexJoin ℝ {p} d ∩ s = s ∩ {x | A x ≤ β} ∧
      convexJoin ℝ {p} d ⊆ {x | A x ∈ Icc 0 β} ∧
      ∀ U : Set E, Convex ℝ U → s ⊆ U → convexJoin ℝ {p} d ⊆ U := by
  have hpoint : (↑({p} : Finset E) : Set E) ⊆ s := by
    simpa only [Finset.coe_singleton] using (singleton_subset_iff.mpr hp)
  obtain ⟨K, hK, hKs, hPK, _, hpure, hcofaces, hconn⟩ :=
    he.exists_marked_height_aligned_surface_complex hC hcv hne hdimF A {p} hpoint
  have hpK : p ∈ K.vertices := hPK (Finset.mem_singleton_self p)
  have hpositive (v : E) (hv : v ∈ K.vertices) (hvp : v ≠ p) : 0 < A v := by
    have hvs : v ∈ s := hKs.subset (K.vertices_subset_space hv)
    exact lt_of_le_of_ne (hmin v hvs) (fun heq => hvp (hzero.subset ⟨hvs, heq.symm⟩))
  obtain ⟨β, hβ, hgap⟩ :=
    (K.finite_vertices_of_finite_faces hK).exists_pos_lt_positive_values A hε
  have hlink := (K.link p).connected_edgeGraph_of_isConnected
    (SimplicialComplex.finite_link_faces hK p) (hconn p hpK)
  obtain ⟨d, hd, hdplane, hdcontact, hball⟩ :=
    K.exists_extreme_vertex_cap_ball hdimE hK hpure hcofaces A hpK hpA hβ.1
      (fun v hv hvp => hgap v hv (hpositive v hv hvp)) hlink
  rw [hKs] at hd hdcontact hball
  have hheight : convexJoin ℝ {p} d ⊆ {x | A x ∈ Icc 0 β} := by
    apply convexJoin_subset ?_ ?_ ((convex_Icc (0 : ℝ) β).affine_preimage A)
    · exact singleton_subset_iff.mpr (by change A p ∈ Icc 0 β; rw [hpA]; exact ⟨le_rfl, hβ.1.le⟩)
    · intro x hx
      change A x ∈ Icc 0 β
      rw [hdplane x hx]
      exact ⟨hβ.1.le, le_rfl⟩
  have hcontact : convexJoin ℝ {p} d ∩ s = s ∩ {x | A x ≤ β} := by
    apply Subset.antisymm
    · exact fun x hx => ⟨hx.2, (hheight hx.1).2⟩
    · exact fun x hx => ⟨hball.1 (Or.inr hx), hx.1⟩
  refine ⟨β, hβ, d, hd, hdplane, hdcontact, hball, hcontact, hheight, ?_⟩
  intro U hU hsU
  obtain ⟨n, P, hPi, hPe, hPb⟩ := hd.exists_polygon_boundary
  let B := A - AffineMap.const ℝ E β
  have hBplane : d ⊆ {x | B x = 0} := by
    intro x hx
    change A x - β = 0
    rw [hdplane x hx, sub_self]
  have hAlinear : A.linear ≠ 0 := by
    intro hz
    have hPheight : A (P 0) = β := (hPb.subset (P.vertex_mem_boundary 0)).2
    have h := A.linearMap_vsub (P 0) p
    change A.linear (P 0 - p) = A (P 0) - A p at h
    rw [hz, LinearMap.zero_apply, hPheight, hpA, sub_zero] at h
    exact hβ.1.ne h
  have hBlinear : B.linear ≠ 0 := by simpa [B] using hAlinear
  have hdP : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ) := by rwa [hPb]
  have hdU : d ⊆ U := hdP.subset_convex_of_planar_polygon_boundary P hPe hPi B hBlinear
    hdimE hBplane hU (by
      rintro x ⟨i, rfl⟩
      exact hsU (hPb.subset (P.vertex_mem_boundary i)).1)
  exact convexJoin_subset (singleton_subset_iff.mpr (hsU hp)) hdU hU

end Homeomorph
