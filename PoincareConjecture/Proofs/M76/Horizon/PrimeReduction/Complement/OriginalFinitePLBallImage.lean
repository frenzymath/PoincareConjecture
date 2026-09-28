import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalDiskStripBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_chartwisePLBall_image
    {E M X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D bd Z : Set E} {f : E → X}
    (hD : IsFinitePLBallPair M D bd) (v : M ≃L[ℝ] V3)
    (hf : PolyhedralPLInCharts e f Z) (hDZ : D ⊆ Z) (hfi : InjOn f Z) :
    Nonempty (ChartwisePLBall e (f '' D) (f '' bd)) := by
  obtain ⟨H,hH,hboundary⟩ := hD.exists_cube_chart v
  obtain ⟨g,hg,hgeq⟩ := hH.symm
  have hgmap : MapsTo g (closedBall (0 : V3) 1) D := by
    intro x hx
    rw [← hgeq ⟨x,hx⟩]
    exact (H.symm ⟨x,hx⟩).property
  have hPL : PolyhedralPLInCharts e (f ∘ g) (closedBall (0 : V3) 1) := by
    obtain ⟨K,hK,hKs,hfaces⟩ := hg
    rw [← hKs]
    exact hf.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hfaces⟩
      (fun x hx => hDZ (hgmap (hKs.subset hx)))
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let G : D ≃ₜ (f '' D) := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f D (hfi.mono hDZ))
    ((hf.continuousOn.mono hDZ).domRestrict.subtype_mk _)
  refine ⟨{
    boundary_subset := image_mono hD.1
    parametrization := H.symm.trans G
    map := f ∘ g
    map_eq := fun x => congrArg f (hgeq x).symm
    piecewiseAffine := hPL
    boundary_eq := ?_
  }⟩
  intro x
  change f (H.symm x) ∈ f '' bd ↔ (x : V3) ∈ sphere 0 1
  have hmem : f (H.symm x) ∈ f '' bd ↔ (H.symm x : E) ∈ bd := by
    constructor
    · rintro ⟨y,hy,heq⟩
      exact hfi (hDZ (hD.1 hy)) (hDZ (H.symm x).property) heq ▸ hy
    · exact fun hx => ⟨H.symm x,hx,rfl⟩
  rw [hmem,hboundary,H.apply_symm_apply,frontier_closedBall _ one_ne_zero]

end PoincareConjecture.M76
