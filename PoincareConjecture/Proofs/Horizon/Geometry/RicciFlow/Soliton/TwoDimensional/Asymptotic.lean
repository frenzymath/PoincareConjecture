import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Norm

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 2 M} {S : AncientRescalingSequence K}

theorem potential_slice_smooth (L : AncientAsymptoticSolitonLimitData S)
    {t : ℝ} (ht : t < 0) :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => L.potential (x, t)) := by
  let C := L.convergence.limit.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
  change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => L.potential (x, t))
  intro x
  exact (L.potential_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Iio).mem_nhds
      (show (x, t) ∈ Set.univ ×ˢ Set.Iio 0 from ⟨Set.mem_univ x, ht⟩))).comp x
      (contMDiffAt_id.prodMk contMDiffAt_const)

theorem compactSpace (L : AncientAsymptoticSolitonLimitData S) :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    CompactSpace C.carrier := by
  let C := L.convergence.limit.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
  let : T3Space C.carrier := C.t3Space
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  let F := L.convergence.limit.flow
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 (fun x => L.potential (x, -1)) :=
    (L.potential_slice_smooth (by norm_num : (-1 : ℝ) < 0)).of_le (by decide)
  apply (F.connection (-1)).compactSpace_of_surface_shrinker
    (L.convergence.limit.complete (-1) (by norm_num))
    hf
    (by norm_num : (0 : ℝ) < 1 / 2)
  · intro x v w
    have h := L.soliton_equation (-1) (by norm_num) x v w
    dsimp [F] at *
    norm_num at h
    linarith
  · exact L.convergence.limit.nonnegative_curvature_operator (-1) (by norm_num)
  · exact L.nonflat_at (-1) (by norm_num)

theorem bounded_curvature (L : AncientAsymptoticSolitonLimitData S) :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧ ∀ x : C.carrier,
      |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B := by
  let C := L.convergence.limit.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
  let : CompactSpace C.carrier := L.compactSpace
  change ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧ ∀ x : C.carrier, _
  intro t _
  obtain ⟨B, hB, hb⟩ :=
    (L.convergence.limit.flow.connection t).exists_pos_curvatureTensorNorm_le_surface
  refine ⟨B, hB.le, fun x => ?_⟩
  rw [abs_of_nonneg (show 0 ≤ (L.convergence.limit.flow.connection t).curvatureTensorNorm x
    from Real.sqrt_nonneg _)]
  exact hb x

end PoincareConjecture.AncientAsymptoticSolitonLimitData
