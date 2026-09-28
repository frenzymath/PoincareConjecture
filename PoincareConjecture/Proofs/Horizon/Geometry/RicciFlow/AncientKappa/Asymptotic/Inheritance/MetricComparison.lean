import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.HolderAssembly


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

namespace AncientCompactTimeConvergence

variable (G : AncientCompactTimeConvergence S)

def coordinateBilinear (k : ℕ) (q : G.limit.carrier.carrier) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := by
  let c := extChartAt (𝓡 n) q
  let f : G.limit.carrier.carrier → M := fun x ↦ ((G.embedding k).toFun (t, x)).2
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (f (c.symm y))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (f (c.symm y))) := by
    unfold TangentSpace
    infer_instance
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) (f (c.symm y)) :=
    (mfderiv (𝓡 n) (𝓡 n) f (c.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) c.symm y)
  exact ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 n) (f (c.symm y))) (F := TangentSpace (𝓡 n) (f (c.symm y)))
    (G := ℝ) (E' := EuclideanSpace ℝ (Fin n)) (F' := EuclideanSpace ℝ (Fin n))
    (((S.rescaling (G.subsequence k)).flow.metric t).inner (f (c.symm y))) A A

theorem coordinateBilinear_apply_basis (k : ℕ) (q : G.limit.carrier.carrier) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (a b : Fin n) :
    G.coordinateBilinear k q t y (EuclideanSpace.basisFun (Fin n) ℝ a)
      (EuclideanSpace.basisFun (Fin n) ℝ b) =
        ancientPullbackCoefficient (G.embedding k) q a b (t, y) := rfl

theorem tendstoUniformlyOn_coordinateBilinear (q : G.limit.carrier.carrier)
    {t : ℝ} (ht : t < 0) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hAt : A ⊆ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun k ↦ G.coordinateBilinear k q t)
      ((G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 n) q).symm) atTop A := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hc : IsCompact ((extChartAt (𝓡 n) q).symm '' A) :=
    hA.image_of_continuousOn ((contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hAt)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hc
  obtain ⟨l, hlt⟩ := (eventually_timeWindow_mem_nhds ht).exists
  let i := max j l
  have hdom : {t} ×ˢ A ⊆ {z | z.1 ∈ ancientM18TimeWindow i ∧
      z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion i} := by
    rintro ⟨s, y⟩ ⟨rfl, hy⟩
    exact ⟨ancientM18TimeWindow_mono (le_max_right j l) (mem_of_mem_nhds hlt),
      hAt hy, G.exhaustion_monotone (le_max_left j l) (hj (mem_image_of_mem _ hy))⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / ((n : ℝ) ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q i 0 ({t} ×ˢ A)
    (isCompact_singleton.prod hA) hdom δ hδ
  filter_upwards [eventually_ge_atTop N] with k hk y hy
  have hentry (a b : Fin n) :
      |(G.coordinateBilinear k q t y -
        (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 n) q).symm y)
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)| ≤ δ := by
    have hh := (hN k hk a b (t, y) ⟨rfl, hy⟩).le
    change |ancientPullbackCoefficient (G.embedding k) q a b (t, y) -
      G.limit.carrier.coordinateCoefficient q
        (fun t x v w ↦ (G.limit.flow.metric t).inner x v w) a b (t, y)| ≤ δ
    simpa only [MetricJet, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      ← map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs] using hh
  have hh := HarmonicCoordinates.norm_bilinear_le_dim_sq_mul_of_entries _ hδ.le hentry
  have hsmall : (n : ℝ) ^ 2 * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ (by positivity : 0 < (n : ℝ) ^ 2 + 1)).mpr (by nlinarith)
  simpa only [dist_eq_norm, norm_sub_rev] using hh.trans_lt hsmall

private theorem exists_local_pullback_inner_error
    {t ε : ℝ} (ht : t < 0) (hε : 0 < ε) (p : G.limit.carrier.carrier) :
    ∃ N ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ x ∈ N, ∀ v : TangentSpace (𝓡 n) x,
      |ancientPullbackInnerValue (G.embedding k) t x v v -
        (G.limit.flow.metric t).inner x v v| ≤ ε * (G.limit.flow.metric t).inner x v v := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 n) p
  let g := G.limit.flow.metric t
  have hp : p ∈ c.source := mem_extChartAt_source p
  have hcp : c p ∈ c.target := c.map_source hp
  obtain ⟨C, hC, hpC, hCt⟩ := exists_compact_between isCompact_singleton
    (isOpen_extChartAt_target p) (singleton_subset_iff.mpr hcp)
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  have hcont : ContinuousOn (g.pullbackCoefficients c.symm) C :=
    fun y hy ↦ (g.contDiffAt_pullbackCoefficients (hc y (hCt hy))).continuousAt.continuousWithinAt
  have hpos : ∀ y ∈ C, ∀ v, v ≠ 0 → 0 < g.pullbackCoefficients c.symm y v v := by
    intro y hy v hv
    apply g.pos (c.symm y)
    intro hz
    apply hv
    apply (hi y (hCt hy)).injective
    rw [map_zero]
    convert! hz using 1
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hC hcont hpos
  have hconv := Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_coordinateBilinear p ht hC hCt) (ε * a) (mul_pos hε ha)
  let N := c.source ∩ c ⁻¹' interior C
  have hN : N ∈ 𝓝 p := inter_mem (extChartAt_source_mem_nhds p)
    ((continuousAt_extChartAt p).preimage_mem_nhds
      (isOpen_interior.mem_nhds (hpC (mem_singleton _))))
  refine ⟨N, hN, ?_⟩
  filter_upwards [hconv] with k hk x hx v
  have hxC : c x ∈ C := interior_subset hx.2
  have hxi := hi (c x) (hCt hxC)
  let w := (mfderiv (𝓡 n) (𝓡 n) c.symm (c x)).inverse v
  have herr : |G.coordinateBilinear k p t (c x) w w - g.pullbackCoefficients c.symm (c x) w w| ≤
      ε * g.pullbackCoefficients c.symm (c x) w w := by
    have hd : ‖G.coordinateBilinear k p t (c x) - g.pullbackCoefficients c.symm (c x)‖ ≤ ε * a := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hk (c x) hxC).le
    calc
      _ ≤ ‖G.coordinateBilinear k p t (c x) - g.pullbackCoefficients c.symm (c x)‖ * ‖w‖ * ‖w‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using
          (G.coordinateBilinear k p t (c x) - g.pullbackCoefficients c.symm (c x)).le_opNorm₂ w w
      _ ≤ ε * (a * ‖w‖ ^ 2) := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hd (mul_nonneg (norm_nonneg w) (norm_nonneg w))
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower (c x) hxC w) hε.le
  have hv : mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w = v := hxi.self_apply_inverse v
  change |ancientPullbackInnerValue (G.embedding k) t (c.symm (c x))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w) (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w) -
    g.inner (c.symm (c x)) (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w)| ≤
    ε * g.inner (c.symm (c x)) (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c x) w) at herr
  have htransport := congrArg (fun z : G.limit.carrier.carrier ↦
    |ancientPullbackInnerValue (G.embedding k) t z v v - g.inner z v v| ≤
      ε * g.inner z v v) (c.left_inv hx.1)
  apply htransport.mp
  simpa only [hv] using herr

theorem eventually_pullback_inner_error {A : Set G.limit.carrier.carrier}
    (hA : IsCompact A) {t ε : ℝ} (ht : t < 0) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ A, ∀ v : TangentSpace (𝓡 n) x,
      |ancientPullbackInnerValue (G.embedding k) t x v v -
        (G.limit.flow.metric t).inner x v v| ≤ ε * (G.limit.flow.metric t).inner x v v := by
  classical
  choose N hN hbound using G.exists_local_pullback_inner_error ht hε
  obtain ⟨s, hs⟩ := hA.elim_nhds_subcover' (fun p _ ↦ N p) (fun p _ ↦ hN p)
  filter_upwards [s.eventually_all.mpr (fun p _ ↦ hbound p)] with k hk x hx v
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
  exact hk p hp x hxp v

theorem eventually_pullback_tangentNorm_bounds {A : Set G.limit.carrier.carrier}
    (hA : IsCompact A) {t C : ℝ} (ht : t < 0) (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ x ∈ A, ∀ v : TangentSpace (𝓡 n) x,
      Real.sqrt (ancientPullbackInnerValue (G.embedding k) t x v v) ≤
        C * (G.limit.flow.metric t).tangentNorm x v ∧
      (G.limit.flow.metric t).tangentNorm x v ≤
        C * Real.sqrt (ancientPullbackInnerValue (G.embedding k) t x v v) := by
  have hCp : 0 < C := zero_lt_one.trans hC
  have hu : 0 < C ^ 2 - 1 := by nlinarith
  have hl : 0 < 1 - C⁻¹ ^ 2 := by
    have h0 := inv_pos.mpr hCp
    have h1 := (inv_lt_one₀ hCp).mpr hC
    nlinarith
  let ε := min (C ^ 2 - 1) (1 - C⁻¹ ^ 2)
  filter_upwards [G.eventually_pullback_inner_error hA ht (lt_min hu hl)] with k hk x hx v
  let a := (G.limit.flow.metric t).inner x v v
  let b := ancientPullbackInnerValue (G.embedding k) t x v v
  have ha : 0 ≤ a := by
    by_cases hv : v = 0
    · simp [a, hv]
    · exact ((G.limit.flow.metric t).pos x v hv).le
  have hh := abs_le.mp (hk x hx v)
  change -(ε * a) ≤ b - a ∧ b - a ≤ ε * a at hh
  have he1 : ε ≤ C ^ 2 - 1 := min_le_left _ _
  have he2 : ε ≤ 1 - C⁻¹ ^ 2 := min_le_right _ _
  have hab : b ≤ C ^ 2 * a := by nlinarith
  have hba : a ≤ C ^ 2 * b := by
    have hh' : C⁻¹ ^ 2 * a ≤ b := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh' (sq_nonneg C)
    have hi : C ^ 2 * C⁻¹ ^ 2 = 1 := by field_simp
    simpa only [← mul_assoc, hi, one_mul] using hm
  change Real.sqrt b ≤ C * Real.sqrt a ∧ Real.sqrt a ≤ C * Real.sqrt b
  constructor
  · rw [← Real.sqrt_sq hCp.le, ← Real.sqrt_mul (sq_nonneg C)]
    exact Real.sqrt_le_sqrt hab
  · rw [← Real.sqrt_sq hCp.le, ← Real.sqrt_mul (sq_nonneg C)]
    exact Real.sqrt_le_sqrt hba

end AncientCompactTimeConvergence
end PoincareConjecture
