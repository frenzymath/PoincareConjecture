import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Radius.LocalUpgrade
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Radius.Scale
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Radius.Propagation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Infinity.Necks
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Escape

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem noncompact_uniform_strongNeck_radius_of_services
    (P : NoncompactKappaServices.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4)
    (hεsep : epsilon ≤ neckSeparationThreshold) :
    ∃ D : ℝ, 1 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (_hnoncompact : ¬ IsCompact (univ : Set M))
        (S : RiemannianMetric.PointSoulData (K.flow.metric 0)) (x : M),
        x ∉ (K.flow.metric 0).ball S.center
          (D * (K.flow.connection 0).scalarCurvature S.center ^ (-1 / 2 : ℝ)) →
        ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  obtain ⟨L, hL, hlocal⟩ := noncompact_uniform_strongNeck_of_nearby_neck_of_services P hε hεsmall
  obtain ⟨D₀, hD₀, hseparate⟩ := nonround_uniform_relative_curvature_scale_separation_of_services P hL.le
  refine ⟨D₀ + 2, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact S x hx
  let : NoncompactSpace M := not_compactSpace_iff.mp fun hcompact =>
    hnoncompact (isCompact_univ_iff.mpr hcompact)
  let R : M → ℝ := (K.flow.connection 0).scalarCurvature
  have hR (y : M) : 0 < R y := by
    obtain ⟨A⟩ := P.normalization M K y 0 le_rfl
    change 0 < (K.flow.connection 0).scalarCurvature y
    exact A.scale_eq ▸ A.scale_pos
  have hroot (y : M) : 0 < Real.sqrt (R y) := Real.sqrt_pos.mpr (hR y)
  let r : ℝ := D₀ / Real.sqrt (R S.center)
  have hr : 0 < r := div_pos hD₀ (hroot S.center)
  let U : Set M := {y | r < ((K.flow.metric 0).edist S.center y).toReal}
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (S.isPreconnected_exterior hr.le)
  let G : Set U := {y | ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = y.val}
  let O : U → U → Prop := fun a b =>
    Real.sqrt (R b.val) * ((K.flow.metric 0).edist a.val b.val).toReal < 1 ∧
      R b.val < 4 * R a.val
  have hRcont : Continuous (fun y : U => R y.val) :=
    (K.flow.connection 0).continuous_scalarCurvature.comp continuous_subtype_val
  have hdistcont (a : U) :
      Continuous (fun b : U => ((K.flow.metric 0).edist a.val b.val).toReal) :=
    ((K.flow.metric 0).continuous_toReal_edist a.val).comp continuous_subtype_val
  have hrow (a : U) : IsOpen {b | O a b} :=
    (isOpen_lt ((Real.continuous_sqrt.comp hRcont).mul (hdistcont a)) continuous_const).inter
      (isOpen_lt hRcont continuous_const)
  have hcolumn (b : U) : IsOpen {a | O a b} := by
    have hd : Continuous (fun a : U => ((K.flow.metric 0).edist a.val b.val).toReal) := by
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hdistcont b
    exact (isOpen_lt (continuous_const.mul hd) continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.mul hRcont))
  have hrefl (a : U) : O a a := by
    constructor
    · simp [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    · have := hR a.val
      dsimp [R] at *
      linarith
  obtain ⟨z, hz, N, hN⟩ := K.exists_strongNeck_arbitrarily_far_of_services P S.center
    (S.noEmbeddedTrivialNormalProjectivePlane K) hε hεsmall r
  have hG : G.Nonempty := ⟨⟨z, hz⟩, N, hN⟩
  have hprop : ∀ a ∈ G, ∀ b, O a b → b ∈ G := by
    rintro a ⟨N, hN⟩ b ⟨hnear, hratio⟩
    have hcenter : N.terminal_neck.center = a.val := N.terminal_center.trans hN
    have hscale : Real.sqrt (R b.val) * N.terminal_neck.scale ≤ 2 := by
      rw [N.terminal_neck.scale_eq_scalar,
        N.terminal_neck.scalar_center_eq (K.flow.connection 0), hcenter]
      change Real.sqrt (R b.val) * R a.val ^ (-1 / 2 : ℝ) ≤ 2
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
        Real.rpow_neg (hR a.val).le, ← Real.sqrt_eq_rpow,
        ← div_eq_mul_inv, div_le_iff₀ (hroot a.val)]
      have hs := Real.sqrt_le_sqrt hratio.le
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num)] at hs
      norm_num at hs
      exact hs
    have hd : D₀ < Real.sqrt (R S.center) *
        ((K.flow.metric 0).edist b.val S.center).toReal := by
      have hb : r < ((K.flow.metric 0).edist S.center b.val).toReal := b.property
      have hh := (div_lt_iff₀ (hroot S.center)).mp hb
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm, mul_comm] using hh
    have hfar := hseparate K S.center b.val (K.not_isRound_of_noncompact hnoncompact) hd
    apply hlocal K hnoncompact S N.terminal_neck b.val
      (N.terminal_epsilon.trans_le hεsep)
    · simpa only [hcenter] using hnear.le
    · exact hscale
    · simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hfar
  have hfull := CoreRadius.eq_univ_of_open_propagation G hG O hrow hcolumn hrefl hprop
  have hxU : x ∈ U := by
    have hrpow : R S.center ^ (-1 / 2 : ℝ) = (Real.sqrt (R S.center))⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
        Real.rpow_neg (hR S.center).le, ← Real.sqrt_eq_rpow]
    have hd : (D₀ + 2) / Real.sqrt (R S.center) ≤
        ((K.flow.metric 0).edist S.center x).toReal := by
      apply le_of_not_gt
      intro hlt
      apply hx
      apply (ENNReal.lt_ofReal_iff_toReal_lt
        ((K.flow.metric 0).edist_ne_top S.center x)).mpr
      change ((K.flow.metric 0).edist S.center x).toReal <
        (D₀ + 2) * R S.center ^ (-1 / 2 : ℝ)
      rwa [hrpow, ← div_eq_mul_inv]
    exact (div_lt_div_of_pos_right (by linarith : D₀ < D₀ + 2)
      (hroot S.center)).trans_le hd
  have hxG : (⟨x, hxU⟩ : U) ∈ G := by rw [hfull]; trivial
  exact hxG

theorem noncompact_uniform_strongNeck_radius
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) (hεsmall : epsilon < 1 / 4)
    (hεsep : epsilon ≤ neckSeparationThreshold) :
    ∃ D : ℝ, 1 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (_hnoncompact : ¬ IsCompact (univ : Set M))
        (S : RiemannianMetric.PointSoulData (K.flow.metric 0)) (x : M),
        x ∉ (K.flow.metric 0).ball S.center
          (D * (K.flow.connection 0).scalarCurvature S.center ^ (-1 / 2 : ℝ)) →
        ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  exact noncompact_uniform_strongNeck_radius_of_services P.noncompactServices hε hεsmall hεsep

end PoincareConjecture
