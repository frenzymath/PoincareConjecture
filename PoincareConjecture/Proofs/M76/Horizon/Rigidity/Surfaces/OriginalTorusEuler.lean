import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels













set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)



structure OriginalTorusEulerCandidate
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (N F : Set X) where
  model : FrontierResidualModel e N F
  component : Fin model.count
  residual : model.residual component = 2

namespace OriginalTorusEulerCandidate

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {N F : Set X}
  (C : OriginalTorusEulerCandidate e N F)

noncomputable def complex : SimplicialComplex ℝ (C.model.vertices → ℝ × V3) :=
  C.model.complex

noncomputable def componentComplex :=
  C.complex.edgeComponentComplex (C.model.pick C.component)

noncomputable def surface : Set X := C.model.components C.component

theorem surface_eq_image :
    C.surface = C.model.map '' (C.componentComplex).space :=
  C.model.images C.component

theorem surface_compact : IsCompact C.surface := by
  change IsCompact (C.model.components C.component)
  exact (C.model.component C.component).1

theorem surface_connected : IsConnected C.surface := by
  change IsConnected (C.model.components C.component)
  exact (C.model.component C.component).2.1

theorem surface_is_frontier_component :
    C.surface ⊆ F ∧ ∀ x ∈ C.surface, connectedComponentIn F x = C.surface :=
  ⟨(C.model.component C.component).2.2.1, (C.model.component C.component).2.2.2⟩

theorem chart_map_injective : InjOn C.model.map C.complex.space :=
  C.model.injective

theorem chartwise_pl :
    PolyhedralPLInCharts e C.model.map C.complex.space :=
  C.model.pl

theorem inverse_on_carrier (z : C.complex.space) :
    C.model.coordinates (C.model.map z) = z :=
  C.model.inverse z z.property

theorem euler_zero :
    (C.componentComplex).surfaceEulerCount = 0 := by
  have h := C.model.euler C.component
  rw [C.residual] at h
  norm_num at h ⊢
  exact h

theorem nonempty : C.surface.Nonempty := by
  change (C.model.components C.component).Nonempty
  exact (C.model.component C.component).2.1.nonempty

end OriginalTorusEulerCandidate



theorem FrontierResidualModel.original_torus_euler_candidate
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N F : Set X}
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (hi : M.residual i = 2) :
    Nonempty (OriginalTorusEulerCandidate e N F) :=
  ⟨⟨M, i, hi⟩⟩

end PoincareConjecture.M76
