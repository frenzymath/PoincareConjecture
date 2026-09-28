import PoincareConjecture.Statements.Ch06.LGeometry
import PoincareConjecture.Proofs.M09.WithinGeometricUniqueness
import PoincareConjecture.Proofs.M09.InitialVectorIdentification









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_regularized_path_lift
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (q : BackwardTimePath F T 0 b)
    (hq : q.curve 0 = p) (R : RegularizedLGeodesicData q) :
    ∃! Z : TangentSpace (𝓡 n) p, Set.EqOn q.curve (A.gamma Z) (Set.Icc 0 b) := by
  let K := sqrtParameterInterval 0 b
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp [K, sqrtParameterInterval]
  have hroot : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hzero : (0 : ℝ) ∈ K := by rw [hK]; exact ⟨le_rfl, hroot.le⟩
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc hroot
  have hconn : IsPreconnected K := hK ▸ isPreconnected_Icc
  have hx : R.path.curve 0 = p := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using (R.path.agrees 0 hzero).trans
      (show q.curve ((0 : ℝ) ^ 2) = p by simpa using hq)
  let Z : TangentSpace (𝓡 n) p := (1 / 2 : ℝ) • (curveVelocity (n := n) R.path.curve 0 : V)
  have hv : (curveVelocity (n := n) R.path.curve 0 : V) = (2 : ℝ) • Z := by
    simp only [Z, smul_smul]
    norm_num
  have hphase : curvePhase (n := n) R.path.curve 0 = Bundle.TotalSpace.mk' V p ((2 : ℝ) • Z) :=
    Bundle.TotalSpace.ext hx (heq_of_eq hv)
  let Ra := A.regularization Z b hb hmax
  let U := R.path.domain ∩ Ra.path.domain
  have hU : IsOpen U := R.path.open_domain.inter Ra.path.open_domain
  have hKU : K ⊆ U := fun s hs ↦ ⟨R.path.interval_subset hs, Ra.path.interval_subset hs⟩
  have htime : K ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    intro s hs
    rw [hK] at hs
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have heq := regularizedCurve_phase_eqOn_preconnected F hM04 T τmax hτmax hwindow
    R.path.curve Ra.path.curve U K hU hKU hKdiff hconn htime
    (R.path.smooth.mono Set.inter_subset_left) (Ra.path.smooth.mono Set.inter_subset_right)
    R.velocity_extension Ra.velocity_extension R.equation Ra.equation 0 hzero
    (hphase.trans (lExponentialFamily_regularization_initial_phase A Z b hb hmax).symm)
  have hZ : Set.EqOn q.curve (A.gamma Z) (Set.Icc 0 b) := by
    intro τ hτ
    have hs : Real.sqrt τ ∈ K := by
      rw [hK]
      exact ⟨Real.sqrt_nonneg τ, Real.sqrt_le_sqrt hτ.2⟩
    have hpos := congrArg Bundle.TotalSpace.proj (heq hs)
    have hR := R.path.agrees (Real.sqrt τ) hs
    have hRa := Ra.path.agrees (Real.sqrt τ) hs
    rw [Real.sq_sqrt hτ.1] at hR hRa
    exact hR.symm.trans (hpos.trans (hRa.trans (congrFun (A.path_eq Z b hb hmax) τ)))
  refine ⟨Z, hZ, ?_⟩
  intro W hW
  exact lExponentialFamily_initialVector_eq_of_eqOn A W Z b hb hmax
    (fun τ hτ ↦ (hW hτ).symm.trans (hZ hτ))

theorem lExponentialFamily_minimizers_lift [ConnectedSpace M]
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (q : BackwardTimePath F T 0 b)
    (hq : q.curve 0 = p) (hmin : IsMinimizingBackwardLPath F T 0 b q) :
    ∃! Z : TangentSpace (𝓡 n) p, Set.EqOn q.curve (A.gamma Z) (Set.Icc 0 b) := by
  have hEuler := hL.euler_lagrange 0 b le_rfl hb hmax.le q hmin
  obtain ⟨R⟩ := hL.regularized_geodesic 0 b le_rfl hb hmax.le q hEuler
  exact lExponentialFamily_regularized_path_lift hM04 hτmax hwindow A b hb hmax q hq R

end PoincareConjecture.Proofs.M09
