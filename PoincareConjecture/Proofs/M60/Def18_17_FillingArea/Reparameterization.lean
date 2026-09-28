import PoincareConjecture.Statements.Ch18.LoopSpaceWidth

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

def CircleReparameterization.symm (r : CircleReparameterization) :
    CircleReparameterization where
  map := r.inverse
  inverse := r.map
  left_inverse := r.right_inverse
  right_inverse := r.left_inverse
  continuous_map := r.continuous_inverse
  continuous_inverse := r.continuous_map

def CircleReparameterization.trans (r s : CircleReparameterization) :
    CircleReparameterization where
  map := s.map ∘ r.map
  inverse := r.inverse ∘ s.inverse
  left_inverse := fun z =>
    (congrArg r.inverse (s.left_inverse (r.map z))).trans (r.left_inverse z)
  right_inverse := fun z =>
    (congrArg s.map (r.right_inverse (s.inverse z))).trans (s.right_inverse z)
  continuous_map := s.continuous_map.comp r.continuous_map
  continuous_inverse := r.continuous_inverse.comp s.continuous_inverse

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m60ReparameterizedLoops_symm {γ₁ γ₂ : C1FreeLoopSpace (M := M)}
    (h : ReparameterizedLoops γ₁ γ₂) : ReparameterizedLoops γ₂ γ₁ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r.symm, fun z => ?_⟩
  change γ₂ z = γ₁ (r.inverse z)
  rw [hr, r.right_inverse]

def m60Disk_reparameterize {g : RiemannianMetric 3 M}
    {γ₁ γ₂ : C1FreeLoopSpace (M := M)} (r : CircleReparameterization)
    (h : ∀ z, γ₁ z = γ₂ (r.map z)) (D : LipschitzSpanningDisk g γ₁) :
    LipschitzSpanningDisk g γ₂ where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization.trans r
  boundary_eq := fun z => (D.boundary_eq z).trans (h _)
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

theorem m60Disk_reparameterize_area {g : RiemannianMetric 3 M}
    {γ₁ γ₂ : C1FreeLoopSpace (M := M)} (r : CircleReparameterization)
    (h : ∀ z, γ₁ z = γ₂ (r.map z)) (D : LipschitzSpanningDisk g γ₁) :
    (m60Disk_reparameterize r h D).area = D.area := rfl

theorem m60DiskAreas_eq_of_reparameterized (g : RiemannianMetric 3 M)
    {γ₁ γ₂ : C1FreeLoopSpace (M := M)} (h : ReparameterizedLoops γ₁ γ₂) :
    Set.range (fun D : LipschitzSpanningDisk g γ₁ => D.area) =
      Set.range (fun D : LipschitzSpanningDisk g γ₂ => D.area) := by
  have forward {γ δ : C1FreeLoopSpace (M := M)} (hγδ : ReparameterizedLoops γ δ) :
      Set.range (fun D : LipschitzSpanningDisk g γ => D.area) ⊆
        Set.range (fun D : LipschitzSpanningDisk g δ => D.area) := by
    obtain ⟨r, hr⟩ := hγδ
    rintro a ⟨D, rfl⟩
    exact ⟨m60Disk_reparameterize r hr D, rfl⟩
  exact Set.Subset.antisymm (forward h) (forward (m60ReparameterizedLoops_symm h))

theorem m60FillingArea_eq_of_reparameterized (g : RiemannianMetric 3 M)
    {γ₁ γ₂ : C1FreeLoopSpace (M := M)} (h : ReparameterizedLoops γ₁ γ₂) :
    fillingArea g γ₁ = fillingArea g γ₂ :=
  congrArg sInf (m60DiskAreas_eq_of_reparameterized g h)

end PoincareConjecture
