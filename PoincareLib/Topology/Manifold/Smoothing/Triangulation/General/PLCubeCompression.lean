import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FullNormedComplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.CubeSectorSubdivision
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ProjectivePLInterpolation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CoreCompressionSimplices
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CoreFixedInterpolation

/-!
# Core-fixing PL compression of Euclidean cube coordinates

An aligned locally finite grid and projective vertex compression
produce a PL homeomorphism from the full coordinate space to the
open radius-two cube, fixing the unit cube. This is the absolute
(`k = 0`) compression in Hamilton 1976, pp. 67--68. The relative
handle construction is a separate obligation. See M76 derivation 86.
-/

set_option autoImplicit false

open Set Metric
open Geometry

namespace PoincareMT.M76

/-- The full real coordinate space admits a PL compression onto
the open radius-two cube which fixes its closed unit cube.
The function space carries its usual supremum norm. See
Hamilton pp. 67--68 and M76 derivation 86. -/
theorem exists_plCubeCompression (ι : Type*) [Fintype ι] :
    ∃ p : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      p.source = univ ∧ p.target = ball 0 2 ∧
      (∀ x, ‖x‖ ≤ 1 → p x = x) ∧
      LocallyPiecewiseAffineOn p p.source ∧ LocallyPiecewiseAffineOn p.symm p.target := by
  obtain ⟨K, hKspace, hKlocal⟩ :=
    SimplicialComplex.exists_full_locallyFinite_complex (ι → ℝ)
  obtain ⟨D, hDlocal, hDK, hsector⟩ := K.exists_cubeSector_subdivision hKlocal
  have hDspace : D.space = univ := hDK.space_eq.trans hKspace
  let e : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ) := OpenPartialHomeomorph.coreCompression
  have hs (s : Finset (ι → ℝ)) (hs : s ∈ D.faces) :=
    NormedSpace.coreCompression_simplex s (D.indep hs) (hsector s hs)
  obtain ⟨p, hps, hpt, hp, hvertices, hfPL, hgPL⟩ :=
    D.exists_piecewiseAffine_interpolant e hDspace (fun x _ => hDlocal x)
      (fun s hs' => (hs s hs').1) (fun s hs' => (hs s hs').2)
  refine ⟨p, hps, hpt, ?_, hfPL, hgPL⟩
  intro x hx
  apply hp.eqOn_core_of_sectors hsector _ x (hDspace.symm ▸ mem_univ x) hx
  intro v hv hvnorm
  exact (hvertices hv).trans (NormedSpace.coreCompression_of_norm_le_one hvnorm)

end PoincareMT.M76
