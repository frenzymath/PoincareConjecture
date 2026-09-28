import PoincareConjecture.Proofs.M76.Triangulation.PLCubeCompression
import PoincareConjecture.Proofs.M76.Mathlib.FullBoundedMesh
import PoincareConjecture.Proofs.M76.Mathlib.CoreInterpolationError
import PoincareConjecture.Proofs.M76.Mathlib.CompactifiedConjugation
import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinder











set_option autoImplicit false

open Set Metric
open Geometry

namespace PoincareConjecture.M76





theorem exists_plCylinderCompression (ι : Type*) [Fintype ι] (J : Finset ι) :
    ∃ p : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      p.source = univ ∧ p.target = ball 0 2 ∧
      (∀ x, ‖x‖ ≤ 1 → p x = x) ∧
      LocallyPiecewiseAffineOn p p.source ∧ LocallyPiecewiseAffineOn p.symm p.target ∧
      MapsTo p (coordinateCylinder J) (coordinateCylinder J) ∧
      ∀ (g : (ι → ℝ) ≃ₜ (ι → ℝ)) (C : ℝ), (∀ x, ‖g x - x‖ ≤ C) →
        ∃ H : (ι → ℝ) ≃ₜ (ι → ℝ),
          (∀ x, H (p x) = p (g x)) ∧ ∀ y ∉ ball (0 : ι → ℝ) 2, H y = y := by
  classical
  obtain ⟨K, B, _, hKspace, hKlocal, hKmesh⟩ :=
    SimplicialComplex.exists_full_locallyFinite_boundedMesh (ι → ℝ)
  have hN (s : Finset (ι → ℝ)) (hs : s ∈ K.faces) :
      s.card ≤ Module.finrank ℝ (ι → ℝ) + 1 := by
    have h := (K.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe] using h
  obtain ⟨L, hLlocal, hLK, _, hLH⟩ :=
    K.exists_locallyFinite_subdivision_respectsAffineHyperplanes
      hKlocal hN (coordinateCylinderForms J)
  obtain ⟨D, hDlocal, hDL, hsector⟩ := L.exists_cubeSector_subdivision hLlocal
  have hDK := hDL.trans hLK
  have hDspace : D.space = univ := hDK.space_eq.trans hKspace
  have hDH : ∀ A ∈ coordinateCylinderForms J, D.RespectsAffineHyperplane A :=
    fun A hA => hDL.respectsAffineHyperplane (hLH A hA)
  let e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ) := OpenPartialHomeomorph.coreCompression
  have hs (s : Finset (ι → ℝ)) (hs : s ∈ D.faces) :=
    NormedSpace.coreCompression_simplex s (D.indep hs) (hsector s hs)
  obtain ⟨p, hps, hpt, hp, hvertices, hfPL, hgPL⟩ :=
    D.exists_piecewiseAffine_interpolant e hDspace (fun x _ => hDlocal x)
      (fun s hs' => (hs s hs').1) (fun s hs' => (hs s hs').2)
  have hfix (x : ι → ℝ) (hx : ‖x‖ ≤ 1) : p x = x := by
    apply hp.eqOn_core_of_sectors hsector _ x (hDspace.symm ▸ mem_univ x) hx
    intro v hv hvnorm
    exact (hvertices hv).trans (NormedSpace.coreCompression_of_norm_le_one hvnorm)
  have hpcyl : MapsTo p (coordinateCylinder J) (coordinateCylinder J) := by
    intro x hx
    apply hp.mapsTo_of_aligned_halfspaces (coordinateCylinderForms J) hDH
      (convex_coordinateCylinder J) _ x (hDspace.symm ▸ mem_univ x)
      ((mem_coordinateCylinder_iff J x).mp hx)
    intro v hv hvH
    rw [hvertices hv]
    exact coreCompression_mem_coordinateCylinder J ((mem_coordinateCylinder_iff J v).mpr hvH)
  refine ⟨p, hps, hpt, hfix, hfPL, hgPL, hpcyl, ?_⟩
  let q : (ι → ℝ) ≃ₜ ball (0 : ι → ℝ) 2 :=
    (Homeomorph.Set.univ (ι → ℝ)).symm.trans
      ((Homeomorph.setCongr hps.symm).trans
        (p.toHomeomorphSourceTarget.trans (Homeomorph.setCongr hpt)))
  have hq (x : ι → ℝ) : (q x : ι → ℝ) = p x := rfl
  have herror (x : ι → ℝ) :
      ‖(q x : ι → ℝ) - NormedSpace.coreCompression x‖ ≤
        (2 * B) * (2 - ‖NormedSpace.coreCompression x‖) := by
    rw [hq]
    exact hp.norm_sub_coreCompression_le hvertices (hDK.diam_le hKmesh)
      (hDspace.symm ▸ mem_univ x)
  intro g C hC
  obtain ⟨H, hH, hHfix⟩ := q.exists_compactification_of_core_error herror g hC
  exact ⟨H, fun x => by simpa only [hq] using hH x, hHfix⟩

end PoincareConjecture.M76
