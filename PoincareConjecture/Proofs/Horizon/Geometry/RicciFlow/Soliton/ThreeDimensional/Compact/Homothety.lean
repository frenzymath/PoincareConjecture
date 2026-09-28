import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g h : RiemannianMetric 3 M}

theorem HomotheticMetricSlice.constantPositiveSectionalCurvature_three
    {c : ℝ} (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hg : ConstantPositiveSectionalCurvature g D) :
    ConstantPositiveSectionalCurvature h D' := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨k, hk, hround⟩ := hg
  refine ⟨k / c, div_pos hk hc, fun x u v hu hv huv => ?_⟩
  let U := mfderiv (𝓡 3) (𝓡 3) E.map x u
  let V := mfderiv (𝓡 3) (𝓡 3) E.map x v
  have hu' : c * g.inner (E.map x) U U = 1 := (E.inner_eq x u u).symm.trans hu
  have hv' : c * g.inner (E.map x) V V = 1 := (E.inner_eq x v v).symm.trans hv
  have huv' : c * g.inner (E.map x) U V = 0 := (E.inner_eq x u v).symm.trans huv
  have hs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hi (a b : TangentSpace (𝓡 3) (E.map x)) :
      g.inner (E.map x) (Real.sqrt c • a) (Real.sqrt c • b) =
        c * g.inner (E.map x) a b := by
    change inner ℝ (Real.sqrt c • a) (Real.sqrt c • b) = c * inner ℝ a b
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, hs]
  have hsec := hround (E.map x) (Real.sqrt c • U) (Real.sqrt c • V)
    ((hi U U).trans hu') ((hi V V).trans hv') ((hi U V).trans huv')
  have hcurv := D'.curvatureTensor_eq_of_local_isometry
    (rescaledMetric_connection g D c hc) isOpen_univ E.map.contMDiff.contMDiffOn
    (fun y _ a b => E.inner_eq y a b) (Set.mem_univ x) u v u v
  rw [rescaledMetric_curvatureTensor] at hcurv
  have hscale : D.curvatureTensor (E.map x)
      (Real.sqrt c • U) (Real.sqrt c • V) (Real.sqrt c • U) (Real.sqrt c • V) =
      c ^ 2 * D.curvatureTensor (E.map x) U V U V := by
    simp only [LeviCivitaData.curvatureTensor_smul_first,
      LeviCivitaData.curvatureTensor_smul_second, LeviCivitaData.curvatureTensor_smul_third,
      LeviCivitaData.curvatureTensor_smul_last]
    calc
      _ = (Real.sqrt c * Real.sqrt c) ^ 2 * D.curvatureTensor (E.map x) U V U V := by ring
      _ = _ := by rw [hs]
  have hk' : c ^ 2 * D.curvatureTensor (E.map x) U V U V = k := by
    simpa only [LeviCivitaData.sectionalCurvature, hi, hu', hv', huv',
      one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one, hscale] using hsec
  rw [LeviCivitaData.sectionalCurvature, hu, hv, huv]
  simp only [one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one]
  apply (eq_div_iff hc.ne').mpr
  change D'.curvatureTensor x u v u v * c = k
  change D'.curvatureTensor x u v u v = c * D.curvatureTensor (E.map x) U V U V at hcurv
  rw [hcurv]
  nlinarith only [hk']

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem ShrinkingSolitonFlow.round_at_time_three {S : GradientShrinkingSolitonData 3 M}
    (G : ShrinkingSolitonFlow S)
    (hround : ConstantPositiveSectionalCurvature S.metric S.connection)
    (t : ℝ) (ht : t < 0) :
    ConstantPositiveSectionalCurvature (G.flow.metric t) (G.flow.connection t) := by
  obtain ⟨E⟩ := G.self_similar t ht
  exact E.constantPositiveSectionalCurvature_three (abs_pos.mpr (ne_of_lt ht))
    S.connection (G.flow.connection t) hround

end PoincareConjecture
