import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.DiskNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Normalization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function IsManifold
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem exists_sphere_disk_neighborhoods_of_injective_mfderiv
    {f : S1 -> S2} (hf : ContMDiff (𝓡 1) (𝓡 2) ∞ f)
    (hfi : Injective f) (hfd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) f q)) :
    ∃ e₀ e₁ : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ e₀.source ∧ closedBall 0 1 ⊆ e₁.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀ e₀.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀.symm e₀.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₁ e₁.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₁.symm e₁.target ∧
      e₀ '' sphere (0 : E2) 1 = range f ∧
      e₁ '' sphere (0 : E2) 1 = range f ∧
      e₁ '' closedBall 0 1 = (e₀ '' ball 0 1)ᶜ ∧
      Disjoint (e₀ '' ball 0 1) (e₁ '' ball 0 1) ∧
      e₀ '' closedBall 0 1 ∪ e₁ '' closedBall 0 1 = univ ∧
      e₀ '' closedBall 0 1 ∩ e₁ '' closedBall 0 1 = range f := by
  obtain ⟨p, hp⟩ := exists_point_not_mem_range_smooth_circle_sphere hf
  obtain ⟨A, hboundary⟩ := exists_ambient_diffeomorph_of_smooth_circle
    (stereographic' 2 p ∘ f)
    (isSmoothEmbedding_stereographic_circle_of_injective_mfderiv hf hfi hfd hp)
  obtain ⟨e₀, e₁, _, hdisks⟩ :=
    exists_sphere_disk_neighborhoods_of_stereographic_boundary hp A hboundary
  exact ⟨e₀, e₁, hdisks⟩

theorem exists_sphere_disk_neighborhoods_of_smooth_circle
    {f : S1 -> S2} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ f) :
    ∃ e₀ e₁ : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ e₀.source ∧ closedBall 0 1 ⊆ e₁.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀ e₀.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀.symm e₀.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₁ e₁.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₁.symm e₁.target ∧
      e₀ '' sphere (0 : E2) 1 = range f ∧
      e₁ '' sphere (0 : E2) 1 = range f ∧
      e₁ '' closedBall 0 1 = (e₀ '' ball 0 1)ᶜ ∧
      Disjoint (e₀ '' ball 0 1) (e₁ '' ball 0 1) ∧
      e₀ '' closedBall 0 1 ∪ e₁ '' closedBall 0 1 = univ ∧
      e₀ '' closedBall 0 1 ∩ e₁ '' closedBall 0 1 = range f :=
  exists_sphere_disk_neighborhoods_of_injective_mfderiv hf.contMDiff
    hf.isEmbedding.injective (fun q =>
      (hf.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp))

end Poincare.Manifold.Schoenflies
