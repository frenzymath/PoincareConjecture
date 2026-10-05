/-
Copyright (c) 2026 The PoincareLib contributors.
-/
import PoincareLib.Topology.Surface.Triangulation.Edges
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.DiscreteSubset

/-!
# Finiteness of transverse edge intersections

Two compact surface arcs have finitely many intersection parameters if the
coordinate difference has injective derivative at every coincidence, including
endpoint coincidences. Compactness alone does not give this finiteness.

These are auxiliary lemmas for the boundary subdivision needed in Lee,
*Introduction to Riemannian Manifolds*, second edition, Problem 9-5, p. 281.
The transverse-arc criterion is an alternative to the geodesic intersection
control used in that problem.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- Transverse compact surface arcs have finitely many pairs of intersection
parameters. The derivative condition is imposed at endpoints as well. -/
theorem finite_transverse_coincidences (e f : SmoothEdge M)
    (htrans : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, e.map s = f.map t →
      ∃ L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2),
        HasFDerivAt (fun p : ℝ × ℝ =>
          chartAt (EuclideanSpace ℝ (Fin 2)) (e.map s) (e.map p.1) -
          chartAt (EuclideanSpace ℝ (Fin 2)) (e.map s) (f.map p.2)) L (s, t) ∧
        Function.Injective L) :
    {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
      e.map p.1 = f.map p.2}.Finite := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let S : Set (ℝ × ℝ) := {p | p ∈ K ∧ e.map p.1 = f.map p.2}
  have hcompactK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have he : ContinuousOn (fun p : ℝ × ℝ => e.map p.1) K :=
    e.smooth.continuousOn.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hf : ContinuousOn (fun p : ℝ × ℝ => f.map p.2) K :=
    f.smooth.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hclosedS : IsClosed S := hcompactK.isClosed.isClosed_eq he hf
  have hcompactS : IsCompact S := hcompactK.of_isClosed_subset hclosedS (fun _ hp => hp.1)
  have hdiscrete : IsDiscrete S := by
    apply isDiscrete_iff_nhdsNE.mpr
    intro p hp
    obtain ⟨L, hL, hinj⟩ := htrans p.1 hp.1.1 p.2 hp.1.2 hp.2
    obtain ⟨C, _, hC⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hinj
    apply inf_principal_eq_bot.mpr
    filter_upwards [hL.eventually_ne (c := 0) ⟨C, hC⟩] with q hq
    intro hqS
    apply hq
    rw [hqS.2, sub_self]
  convert hcompactS.finite hdiscrete using 1
  ext p
  simp only [S, K, mem_ofPred_eq, mem_prod, and_assoc]

/-- The actual intersection of transverse compact surface arcs is finite. -/
theorem finite_transverse_edge_intersection (e f : SmoothEdge M)
    (htrans : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, e.map s = f.map t →
      ∃ L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2),
        HasFDerivAt (fun p : ℝ × ℝ =>
          chartAt (EuclideanSpace ℝ (Fin 2)) (e.map s) (e.map p.1) -
          chartAt (EuclideanSpace ℝ (Fin 2)) (e.map s) (f.map p.2)) L (s, t) ∧
        Function.Injective L) :
    (e.map '' Icc (0 : ℝ) 1 ∩ f.map '' Icc (0 : ℝ) 1).Finite := by
  apply ((finite_transverse_coincidences e f htrans).image
    (fun p : ℝ × ℝ => e.map p.1)).subset
  rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, heq⟩⟩
  exact ⟨(s, t), ⟨hs, ht, heq.symm⟩, rfl⟩

end PoincareMT.Topology.Surface
