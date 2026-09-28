import PoincareConjecture.Proofs.M32.Claim11_32.ScalarDistance
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.AnalyticGradient
import PoincareConjecture.Proofs.M32.Claim11_32.Sequence
import PoincareConjecture.Proofs.M32.Thm11_31.Topology
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactConfinement

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

theorem horn_ball_subset_of_boundary_distance
    {F : GeneralizedRicciFlowData.{u}} {T accuracy : ℝ}
    {E : GeneralizedFlowExtension F T} (horn : StrongHorn E accuracy)
    {x : (E.extended.slice T).carrier} (hx : x ∈ horn.carrier)
    {r : ℝ} (hboundary : ∀ y ∈ horn.boundary_sphere,
      ENNReal.ofReal r ≤ (E.extended.metric T).edist x y) :
    (E.extended.metric T).ball x r ⊆ horn.carrier := by
  intro y hy
  obtain ⟨gamma, hzero, hone, hgamma, _, hball⟩ :=
    (E.extended.metric T).exists_short_path_in_ball x y hy
  have hpre := isPreconnected_Icc.image gamma hgamma.continuousOn
  have hmeet : (gamma '' Icc (0 : ℝ) 1 ∩ horn.carrier).Nonempty :=
    ⟨x, ⟨0, ⟨le_rfl, zero_le_one⟩, hzero⟩, hx⟩
  have havoid : Disjoint (gamma '' Icc (0 : ℝ) 1) horn.boundary_sphere := by
    apply disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ hz
    exact not_lt_of_ge (hboundary _ hz) (hball ht)
  exact horn_subset_carrier_of_isPreconnected horn hpre hmeet havoid
    ⟨1, ⟨zero_le_one, le_rfl⟩, hone⟩

theorem exists_terminal_horn_ball_radius {K B : ℝ} (hK : 0 < K) (hB : 0 < B) :
    ∃ d : ℝ, 0 < d ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ (_hM04 : RicciFlowCurvatureTheory.{u}) (H : SingularTimeAssumptions F T M)
          (E : GeneralizedFlowExtension F T),
          H.r₀⁻¹ ^ 2 < K → H.analytic_constant = B →
          ∀ {accuracy : ℝ} (horn : StrongHorn E accuracy),
            (∀ y ∈ horn.boundary_sphere, (E.extended.connection T).scalarCurvature y ≤ K) →
            ∀ x ∈ horn.carrier, 2 * K ≤ (E.extended.connection T).scalarCurvature x →
              (E.extended.metric T).ball x d ⊆ horn.carrier := by
  obtain ⟨d, hd, hdist⟩ := exists_scalar_level_distance.{u} hK hB
  refine ⟨d, hd, ?_⟩
  intro F T M _ _ _ _ _ _ _ _ hM04 H E hcutoff hconstant accuracy horn hboundary x hx hhigh
  apply horn_ball_subset_of_boundary_distance horn hx
  intro y hy
  apply hdist (E.extended.connection T) ?_ x y hhigh (hboundary y hy)
  intro z hz v hv
  simpa only [hconstant] using terminal_scalar_gradient_bound hM04 H E z
    (hcutoff.trans_le hz) v hv

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
  (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
  (Q : ∀ k, SingularLimitConclusion (H k))
  (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
  (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
  (hdiv : Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)

theorem terminalBlowupSequence_baseBalls_subset_horns
    (hM04 : RicciFlowCurvatureTheory.{u}) {K B : ℝ} {accuracy : ℕ → ℝ}
    (hK : 0 < K) (hB : 0 < B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (horn : ∀ k, StrongHorn (Q k).extension (accuracy k))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K) :
    ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      (terminalBlowupSequence H Q x hpos hdiv).baseBall k A ⊆ (horn k).carrier := by
  obtain ⟨d, hd, hconfine⟩ := exists_terminal_horn_ball_radius.{u} hK hB
  intro A _
  have hsmall : Tendsto (fun k => A /
      Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hdiv)).const_mul A
  filter_upwards [hdiv.eventually (eventually_ge_atTop (2 * K)),
    hsmall.eventually (gt_mem_nhds hd)] with k hhigh hradius
  have hinside := hconfine hM04 (H k) (Q k).extension (hcutoff k)
    (hconstant k) (horn k) (hboundary k) (x k) (hx k) hhigh
  intro y hy
  apply hinside
  exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hradius.le)

end PoincareConjecture.M32
