import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

def smoothOpenPartialHomeomorph {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (f : M → N) (g : N → M) (U : Set M) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hg : ContMDiffOn (𝓡 n) (𝓡 n) ∞ g (f '' U))
    (hleft : LeftInvOn g f U)
    (hD : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    OpenPartialHomeomorph M N where
  toFun := f
  invFun := g
  source := U
  target := f '' U
  map_source' := fun _ hx => mem_image_of_mem f hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [hleft hx]
  left_inv' := hleft
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hleft hx]
  open_source := hU
  open_target := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x, hx, rfl⟩
    rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
      (hf.contMDiffAt (hU.mem_nhds hx)) (hD x hx)]
    exact image_mem_map (hU.mem_nhds hx)
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := hg.continuousOn
