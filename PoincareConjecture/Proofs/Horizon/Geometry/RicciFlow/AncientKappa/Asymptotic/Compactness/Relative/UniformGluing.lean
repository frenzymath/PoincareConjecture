import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Extraction







set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.PointedGeometricConvergence

theorem exists_continuous_uniformLimit_of_compact_extraction
    {X Y : Type*} [TopologicalSpace X] [UniformSpace Y] [T2Space Y]
    (g : ℕ → X → Y) (Q : ℕ → Set X)
    (hcover : ∀ x, ∃ i, Q i ∈ 𝓝 x)
    (hcofinal : ∀ K : Set X, IsCompact K → ∃ i, K ⊆ Q i)
    (f : ∀ i, Q i → Y) (hf : ∀ i, Continuous (f i))
    (hconv : ∀ i, TendstoUniformly (fun k (x : Q i) ↦ g k x.val) (f i) atTop) :
    ∃ F : X → Y, Continuous F ∧
      ∀ K : Set X, IsCompact K → TendstoUniformlyOn g F atTop K := by
  classical
  choose j hj using hcover
  let F (x : X) := f (j x) ⟨x, mem_of_mem_nhds (hj x)⟩
  have heq (i : ℕ) (x : Q i) : F x.val = f i x :=
    tendsto_nhds_unique ((hconv (j x.val)).tendsto_at
      ⟨x.val, mem_of_mem_nhds (hj x.val)⟩) ((hconv i).tendsto_at x)
  refine ⟨F, ?_, ?_⟩
  · apply continuous_of_cover_nhds (fun x ↦ ⟨j x, hj x⟩)
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : (Q i).domRestrict F = f i := funext (heq i)
    rw [hres]
    exact hf i
  · intro K hK
    obtain ⟨i, hi⟩ := hcofinal K hK
    apply TendstoUniformlyOn.mono (s := Q i) _ hi
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hres : F ∘ (Subtype.val : Q i → X) = f i := funext (heq i)
    rw [hres]
    exact hconv i

end PoincareConjecture.PointedGeometricConvergence
