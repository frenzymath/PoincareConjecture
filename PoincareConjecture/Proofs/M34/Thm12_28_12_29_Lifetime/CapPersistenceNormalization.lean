import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M09.RiemannianProper











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem edist_le_intrinsicEDist (V : Set M) (x y : M) :
    g.edist x y ≤ intrinsicEDist g V x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_sInf
  rintro L ⟨γ, hγ, hγ0, hγ1, _, rfl⟩
  exact Manifold.riemannianEDist_le_pathELength hγ hγ0 hγ1 zero_le_one



theorem intrinsicEDist_le_intrinsicDiameter {V : Set M} {x y : M}
    (hx : x ∈ V) (hy : y ∈ V) :
    intrinsicEDist g V x y ≤ intrinsicDiameter g V :=
  le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩

namespace CapCertificate

variable [MeasurableSpace M] [BorelSpace M] [T3Space M] (N : CapCertificate g)



theorem closed_core_subset_carrier : N.closed_core ⊆ N.carrier := by
  rw [N.closed_core_eq_complement_end]
  exact sdiff_subset



theorem core_subset_carrier' : N.core ⊆ N.carrier := by
  rw [N.core_eq_interior_closed_core]
  exact interior_subset.trans N.closed_core_subset_carrier



theorem scalar_bounds_of_normalized_base {o : M} (ho : o ∈ N.carrier)
    (hnormal : N.connection.scalarCurvature o = 1)
    {C : ℝ} (hC : N.cap_constant ≤ C) {x : M} (hx : x ∈ N.carrier) :
    C⁻¹ ≤ N.connection.scalarCurvature x ∧ N.connection.scalarCurvature x ≤ C := by
  have hCpos : 0 < C := N.cap_constant_pos.trans_le hC
  obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
  have hupper := hratio o ho x hx
  have hlower := hratio x hx o ho
  rw [hnormal, mul_one] at hupper
  rw [hnormal] at hlower
  refine ⟨?_, hupper.trans (hb.le.trans hC)⟩
  apply (inv_le_iff_one_le_mul₀' hCpos).mpr
  calc
    1 ≤ b * N.connection.scalarCurvature x := hlower
    _ ≤ C * N.connection.scalarCurvature x :=
      mul_le_mul_of_nonneg_right (hb.le.trans hC) (N.scalar_pos x hx).le



theorem scalarSup_bounds_of_normalized_base {o : M} (ho : o ∈ N.carrier)
    (hnormal : N.connection.scalarCurvature o = 1)
    {C : ℝ} (hC : N.cap_constant ≤ C) :
    1 ≤ scalarCurvatureSupOn g N.connection N.carrier ∧
      scalarCurvatureSupOn g N.connection N.carrier ≤ C := by
  have hb : BddAbove (Set.range
      (fun z : N.carrier => N.connection.scalarCurvature z.1)) :=
    ⟨C, by rintro _ ⟨z, rfl⟩; exact (N.scalar_bounds_of_normalized_base ho hnormal hC z.2).2⟩
  constructor
  · rw [← hnormal]
    exact le_csSup hb ⟨⟨o, ho⟩, rfl⟩
  · exact csSup_le ⟨_, ⟨⟨o, ho⟩, rfl⟩⟩ (by
      rintro _ ⟨z, rfl⟩
      exact (N.scalar_bounds_of_normalized_base ho hnormal hC z.2).2)



theorem carrier_subset_ball_of_normalized_base {o : M} (ho : o ∈ N.carrier)
    (hnormal : N.connection.scalarCurvature o = 1)
    {C : ℝ} (hC : N.cap_constant ≤ C) : N.carrier ⊆ g.ball o C := by
  have hsup := (N.scalarSup_bounds_of_normalized_base ho hnormal hC).1
  have hpow : scalarCurvatureSupOn g N.connection N.carrier ^ (-1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hsup (by norm_num)
  intro x hx
  calc
    g.edist o x ≤ intrinsicEDist g N.carrier o x := edist_le_intrinsicEDist _ _ _
    _ ≤ intrinsicDiameter g N.carrier := intrinsicEDist_le_intrinsicDiameter ho hx
    _ < ENNReal.ofReal (N.cap_constant *
        scalarCurvatureSupOn g N.connection N.carrier ^ (-1 / 2 : ℝ)) :=
      N.intrinsic_diameter_bound
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ N.cap_constant * 1 := mul_le_mul_of_nonneg_left hpow N.cap_constant_pos.le
        _ ≤ C := by simpa only [mul_one] using hC)



theorem isCompact_closure_of_normalized_base [ConnectedSpace M]
    (hcomplete : MetricComplete g) {o : M} (ho : o ∈ N.carrier)
    (hnormal : N.connection.scalarCurvature o = 1) : IsCompact (closure N.carrier) := by
  have hc := Proofs.M09.isCompact_closure_metric_ball g hcomplete o N.cap_constant
  exact hc.of_isClosed_subset isClosed_closure
    (closure_mono (N.carrier_subset_ball_of_normalized_base ho hnormal le_rfl))

end CapCertificate
end PoincareConjecture
