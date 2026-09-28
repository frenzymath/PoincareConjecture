import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Volume




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem density_pos {z : Spacetime n} (hx : z.1 ∈ e.source) :
    0 < density F e z := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  exact ((F.metric (-z.2)).contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).2

theorem contDiffOn_density : ContDiffOn ℝ ∞ (density F e) (domain J e) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  intro z hz
  have h := F.contDiffAt_pullbackVolumeDensity_spacetime hz.2
    (he.contMDiffAt (e.open_source.mem_nhds hz.1)) (hD.mfderiv_injective hz.1)
  exact (h.comp z (contDiffAt_snd.neg.prodMk contDiffAt_fst)).contDiffWithinAt

theorem contDiffOn_pullbackCoefficients :
    ContDiffOn ℝ ∞ (fun z : Spacetime n =>
      (F.metric (-z.2)).pullbackCoefficients e z.1) (domain J e) := by
  intro z hz
  have hF : RiemannianMetric.IsSmoothFamilyOn F.metric (interior J) :=
    F.smooth.mono (Set.prod_mono interior_subset Subset.rfl)
  have h := hF.contDiffAt_spacetime_pullbackCoefficients
    isOpen_interior (he.contMDiffAt (e.open_source.mem_nhds hz.1)) hz.2
  exact (h.comp z (contDiffAt_snd.neg.prodMk contDiffAt_fst)).contDiffWithinAt

theorem contDiffOn_principal (i j : Fin n) :
    ContDiffOn ℝ ∞ (principal F e i j) (domain J e) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  intro z hz
  have hB := (contDiffOn_pullbackCoefficients F e he hei).contDiffAt
    ((isOpen_domain e).mem_nhds hz)
  have hI := ((F.metric (-z.2)).isInvertible_pullbackCoefficients
    (hD.mfderiv_injective hz.1)).contDiffAt_map_inverse.comp z hB
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp z
    (hI.clm_apply (contDiffAt_const (c := EuclideanSpace.proj (𝕜 := ℝ) j)))).contDiffWithinAt

theorem contDiffOn_weightedPrincipal (i j : Fin n) :
    ContDiffOn ℝ ∞ (weightedPrincipal F e i j) (domain J e) :=
  (contDiffOn_density F e he hei).mul (contDiffOn_principal F e he hei i j)

theorem contDiffOn_drift (i : Fin n) :
    ContDiffOn ℝ ∞ (drift F e i) (domain J e) := by
  apply ((contDiffOn_density F e he hei).inv
    (fun z hz => (density_pos F e he hei hz.1).ne')).mul
  apply ContDiffOn.sum
  intro j _
  exact ((contDiffOn_weightedPrincipal F e he hei j i).fderiv_of_isOpen
    (isOpen_domain e) (by simp)).clm_apply contDiffOn_const

theorem principal_symm {z : Spacetime n} (hx : z.1 ∈ e.source) (i j : Fin n) :
    principal F e i j z = principal F e j i z := by
  apply mul_left_cancel₀ (density_pos F e he hei hx).ne'
  exact LeviCivitaData.Dirichlet.divergenceCoefficients_symm
    (g := F.metric (-z.2)) e he hei hx i j

theorem principal_pos {z : Spacetime n} (hx : z.1 ∈ e.source)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, principal F e i j z * v i * v j := by
  have hp := LeviCivitaData.Dirichlet.divergenceCoefficients_pos
    (g := F.metric (-z.2)) e he hei hx v hv
  have heq : (∑ i, ∑ j, LeviCivitaData.Dirichlet.divergenceCoefficients
        (F.metric (-z.2)) e z.1 i j * v i * v j) =
      density F e z * ∑ i, ∑ j, principal F e i j z * v i * v j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (density F e z * principal F e i j z) * v i * v j = _
    ring
  rw [heq] at hp
  exact (mul_pos_iff_of_pos_left (density_pos F e he hei hx)).mp hp

end PoincareConjecture.RicciFlow.BackwardCoordinates
