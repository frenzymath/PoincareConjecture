import PoincareConjecture.Proofs.M76.Mathlib.FullNormedComplex
import PoincareConjecture.Proofs.M76.Mathlib.CubeSectorSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.ProjectivePLInterpolation
import PoincareConjecture.Proofs.M76.Mathlib.CoreCompressionSimplices
import PoincareConjecture.Proofs.M76.Mathlib.CoreFixedInterpolation

set_option autoImplicit false

open Set Metric
open Geometry

namespace PoincareConjecture.M76

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

end PoincareConjecture.M76
