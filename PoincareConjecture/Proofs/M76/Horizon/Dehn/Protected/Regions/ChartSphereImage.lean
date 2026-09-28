import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Spheres.Disks









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_finitePL_chart_image
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (i : α) (hsource : S ⊆ (e i).source) :
    ∃ b : sphere (0 : V3) 1 ≃ₜ (e i) '' S,
      b.IsFinitePL ∧ ∀ x, (b x : V3) = e i (s.parametrization x) := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hPL : FinitePiecewiseAffineOn ((e i) ∘ s.map) (sphere (0 : V3) 1) := by
    rw [← hKs]
    have hmap : PolyhedralPLInCharts e s.map K.space := hKs.symm ▸ s.piecewiseAffine
    apply hmap.finitePiecewiseAffineOn_fixed_chart hcompat K hK i
    intro x hx
    rw [s.map_eq ⟨x, hKs ▸ hx⟩]
    exact hsource (s.parametrization ⟨x, hKs ▸ hx⟩).property
  let b := s.parametrization.trans ((e i).homeomorphOfImageSubsetSource hsource rfl)
  exact ⟨b, ⟨(e i) ∘ s.map, hPL, fun x => congrArg (e i) (s.map_eq x).symm⟩,
    fun _ => rfl⟩

end PoincareConjecture.M76
