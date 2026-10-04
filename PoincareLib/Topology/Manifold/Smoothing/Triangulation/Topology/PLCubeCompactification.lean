import PoincareLib.Topology.Manifold.Smoothing.Triangulation.General.PLCubeCompression
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FullBoundedMesh
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CoreInterpolationError
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.CompactifiedConjugation

/-!
# Compactification by a core-fixing PL cube map

The uniformly bounded aligned grid gives a PL compression with
controlled behavior at infinity. Every bounded homeomorphism
conjugates through it to a homeomorphism extending by identity
across the compactifying cube boundary. This is Hamilton 1976,
pp. 65, 67--68 in the absolute (`k = 0`) case; see M76
derivations 86--87.
-/

set_option autoImplicit false

open Set Metric
open Geometry

namespace PoincareMT.M76

/-- Choose one PL cube compression, fixing the closed unit cube,
through which every bounded homeomorphism admits a boundary-fixed
ambient compactification. See Hamilton pp. 65, 67--68 and
M76 derivations 86--87. -/
theorem exists_plCubeCompactification (ι : Type*) [Fintype ι] :
    ∃ p : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      p.source = univ ∧ p.target = ball 0 2 ∧
      (∀ x, ‖x‖ ≤ 1 → p x = x) ∧
      LocallyPiecewiseAffineOn p p.source ∧ LocallyPiecewiseAffineOn p.symm p.target ∧
      ∀ (g : (ι → ℝ) ≃ₜ (ι → ℝ)) (C : ℝ), (∀ x, ‖g x - x‖ ≤ C) →
        ∃ H : (ι → ℝ) ≃ₜ (ι → ℝ),
          (∀ x, H (p x) = p (g x)) ∧ ∀ y ∉ ball (0 : ι → ℝ) 2, H y = y := by
  obtain ⟨K, B, _, hKspace, hKlocal, hKmesh⟩ :=
    SimplicialComplex.exists_full_locallyFinite_boundedMesh (ι → ℝ)
  obtain ⟨D, hDlocal, hDK, hsector⟩ := K.exists_cubeSector_subdivision hKlocal
  have hDspace : D.space = univ := hDK.space_eq.trans hKspace
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
  refine ⟨p, hps, hpt, hfix, hfPL, hgPL, ?_⟩
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

end PoincareMT.M76
