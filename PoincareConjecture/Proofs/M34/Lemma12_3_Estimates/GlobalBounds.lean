import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.EndTransport
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M34.Lemma12_3_CoreVolume

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

def endEstimateCore (e : StandardCylindricalEnd g) : Set StandardCapSpace :=
  e.closed_core ∪ e.coordinate '' (univ ×ˢ Icc (0 : ℝ) 1)

theorem endEstimateCore_isCompact (e : StandardCylindricalEnd g) :
    IsCompact (endEstimateCore e) := by
  apply e.core_compact.union
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply e.coordinate_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, by
    change -e.collar < z.2
    have h := hz.2.1
    linarith [e.collar_pos]⟩

theorem end_height_gt_one_of_not_mem_core (e : StandardCylindricalEnd g)
    {x : StandardCapSpace} (hx : x ∉ endEstimateCore e) :
    ∃ z : StandardCylinderSpace, 1 < z.2 ∧ e.coordinate z = x := by
  have hxcore : x ∉ e.closed_core := fun h => hx (Or.inl h)
  have hcarrier : x ∈ e.carrier := by
    rw [e.carrier_eq]
    refine ⟨mem_univ _, fun hb => hxcore ?_⟩
    rw [e.closed_core_eq]
    exact (show g.edist 0 x < ENNReal.ofReal e.radius from hb).le
  refine ⟨e.inverse x, ?_, e.coordinate_right_inverse hcarrier⟩
  by_contra h
  apply hx
  exact Or.inr ⟨e.inverse x, ⟨mem_univ _, e.inverse_domain x hcarrier, le_of_not_gt h⟩,
    e.coordinate_right_inverse hcarrier⟩

theorem end_compact_curvature_representative (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) (x : StandardCapSpace) :
    ∃ y ∈ endEstimateCore e, D.scalarCurvature x = D.scalarCurvature y ∧
      ∀ k : ℕ, D.curvatureDerivativeNorm k x = D.curvatureDerivativeNorm k y := by
  by_cases hx : x ∈ endEstimateCore e
  · exact ⟨x, hx, rfl, fun _ => rfl⟩
  obtain ⟨z, hz, rfl⟩ := end_height_gt_one_of_not_mem_core e hx
  have hzpos : 0 < z.2 := zero_lt_one.trans hz
  have hsum : z.2 + (1 - z.2) = 1 := by ring
  have hpos : 0 < z.2 + (1 - z.2) := by rw [hsum]; exact zero_lt_one
  refine ⟨e.coordinate (z.1, 1), Or.inr ⟨(z.1, 1), ?_, rfl⟩, ?_, ?_⟩
  · exact ⟨mem_univ _, zero_le_one, le_rfl⟩
  · simpa only [hsum] using end_scalarCurvature_translate D e (1 - z.2) hzpos hpos
  · intro k
    simpa only [hsum] using end_curvatureDerivativeNorm_translate D e (1 - z.2) hzpos hpos k

theorem end_curvatureDerivativeNorm_bounded (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : StandardCapSpace, D.curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    curvatureDerivativeNorm_bounded_on_compact D k (endEstimateCore_isCompact e)
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨y, hy, _, hnorm⟩ := end_compact_curvature_representative D e x
  rw [hnorm k]
  exact hC y hy

theorem end_scalarCurvature_bounds (D : LeviCivitaData g)
    (e : StandardCylindricalEnd g)
    (hpos : ∀ x ∈ endEstimateCore e, 0 < D.scalarCurvature x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : StandardCapSpace,
      C⁻¹ ≤ D.scalarCurvature x ∧ D.scalarCurvature x ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    scalarCurvature_bounds_on_compact D (endEstimateCore_isCompact e) hpos
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨y, hy, hscalar, _⟩ := end_compact_curvature_representative D e x
  rw [hscalar]
  exact hC y hy

theorem standardCapEstimate_of_scalar_pos (g₀ : StandardInitialMetric)
    (hpos : ∀ x : StandardCapSpace, 0 < g₀.connection.scalarCurvature x) :
    Nonempty (StandardCapEstimate g₀) := by
  obtain ⟨C, hC0, hC⟩ := end_scalarCurvature_bounds g₀.connection g₀.cylindrical_end
    (fun x _ => hpos x)
  obtain ⟨V, hV0, hV⟩ := exists_core_volume_bound g₀
  exact ⟨{
    scalar_constant := C
    scalar_constant_pos := hC0
    scalar_bounds := hC
    core_volume_constant := V
    core_volume_constant_pos := hV0
    core_volume_upper := hV
    curvature_derivative_bounds :=
      end_curvatureDerivativeNorm_bounded g₀.connection g₀.cylindrical_end }⟩

end PoincareConjecture.M34
