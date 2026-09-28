import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.StabilizedClosedC2
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_Comparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.UnitRicciControl





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

open M64 M64.RampTransport




theorem m64RampSmallAnnulusComparison_of_geometry
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Icc a b)} (G : M63AmbientGeometry F) :
    M64RampSmallAnnulusComparison G := by
  intro _hn r hr
  obtain ⟨mu, hmu, hcomparison⟩ := m64IntrinsicAnnulusComparison
    (7 / 800) (r / 4) G.K0 (by norm_num) (by norm_num) (div_pos hr (by norm_num))
  refine ⟨mu / 2, half_pos hmu, ?_⟩
  intro circumference hc
  dsimp only
  intro time ht gamma0 gamma1 hp0 hp1 hg0 hg1 hramp0 hramp1 hlength hturn A harea
  let P := G.product circumference hc
  let : Fact (0 < circumference) := ⟨hc⟩
  obtain ⟨Q⟩ := nonempty_auxiliary_unit_product P
  by_contra hfailure
  have hgap : 0 < (3 / 4 : ℝ) * m62Length P.flow (fun y _ => gamma0 y) time -
      m62Length P.flow (fun y _ => gamma1 y) time := sub_pos.mpr (lt_of_not_ge hfailure)
  let gap := (3 / 4 : ℝ) * m62Length P.flow (fun y _ => gamma0 y) time -
    m62Length P.flow (fun y _ => gamma1 y) time
  let epsilon := min (mu / 4) (gap / 4)
  have hepsilon : 0 < epsilon :=
    lt_min (div_pos hmu (by norm_num)) (div_pos hgap (by norm_num))
  obtain ⟨S⟩ := exists_stabilized_smooth_ramp_approximation P Q ht hg0 hg1 hp0 hp1
    hramp0 hramp1 A hr hlength hturn hepsilon
  have hsmall : S.separated.minimum.area < mu := by
    have hA := S.minimum_area_error
    have he : epsilon ≤ mu / 4 := min_le_left _ _
    linarith
  have hsec (p : Q.charts.Point) (u v : TangentSpace (𝓡 ((n + 1) + 1)) p) :
      (Q.flow.connection time).sectionalCurvature p u v ≤ G.K0 :=
    (le_abs_self _).trans
      (auxiliaryCircle_sectional_abs_le_of_ambient_bounds P Q G.nonnegative.1 G.bounds ht p u v)
  have h := stabilized_comparison_with_error S ht hr hepsilon
    (stabilized_minimum_closed_c2 S) hsec hcomparison hsmall
  have he : epsilon ≤ gap / 4 := min_le_right _ _
  dsimp only [gap] at he
  linarith

end PoincareConjecture
