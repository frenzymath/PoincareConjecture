import PoincareConjecture.Proofs.M30.Thm11_1.TerminalBoundAssembly
import PoincareConjecture.Proofs.M30.Thm11_8.ClosedLeftDescent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.measurableSpace FlowCarrier.borelSpace FlowCarrier.secondCountable



theorem exists_left_endpoint_scalar_bound_threshold
    (hC : RicciFlowCurvatureTheory.{u}) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 200 ∧
      ∀ {S : GeneralizedBlowupSequence.{u}} {T : ℝ}, 0 < T →
      ∀ (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
        (Fbar : RicciFlow 3 G.limit.carrier.carrier (Icc (-T) 0)),
        G.limit.carrier.metricComplete (Fbar.metric (-T)) →
        (∀ x, (Fbar.connection (-T)).NonnegativeCurvatureOperator x) →
        (∀ A : ℝ, 0 < A →
          ∀ U : TopologicalSpace.Opens G.limit.carrier.carrier,
            (U : Set G.limit.carrier.carrier) =
              (G.limit.flow.metric 0).ball G.limit.base A →
            ∃ delta : ℝ, 0 < delta ∧
              ∃ F : RicciFlow 3 U (Icc (-(T + delta)) 0),
                (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
                  (F.metric (-T)).inner x v w =
                    (Fbar.metric (-T)).inner x.val
                      (mfderiv (𝓡 3) (𝓡 3)
                        (Subtype.val : U → G.limit.carrier.carrier) x v)
                      (mfderiv (𝓡 3) (𝓡 3)
                        (Subtype.val : U → G.limit.carrier.carrier) x w)) ∧
                ∀ t ∈ Icc (-(T + delta)) 0, ∀ x : U,
                  (F.connection t).NonnegativeCurvatureOperator x) →
      ∀ (eta C : ℝ), 0 < eta → eta ≤ eta0 →
        (∀ x, 4 < (Fbar.connection (-T)).scalarCurvature x →
          (∃ N : EpsilonNeck (Fbar.metric (-T)), N.epsilon = eta ∧
            (Fbar.connection (-T)).scalarCurvature x ≤
              max 1 C * (Fbar.connection (-T)).scalarCurvature N.center) ∨
            IsCompact (univ : Set G.limit.carrier.carrier)) →
        ∃ B : ℝ, 4 ≤ B ∧ ∀ x, (Fbar.connection (-T)).scalarCurvature x ≤ B := by
  classical
  obtain ⟨eta0, heta0, hsmall, hbound⟩ :=
    exists_terminal_curvature_bound_threshold.{u, u, 0}
  refine ⟨eta0, heta0, hsmall, ?_⟩
  intro S T hT G Fbar hcomplete hoperator hlocal eta C heta hetaLe hcanonical
  let M := G.limit.carrier.carrier
  let : ConnectedSpace M := G.limit.connectedSpace
  let g0 := G.limit.flow.metric 0
  let D := Fbar.connection (-T)
  by_cases hlow : ∀ x : M, D.scalarCurvature x ≤ 4
  · exact ⟨4, le_rfl, hlow⟩
  push Not at hlow
  obtain ⟨p, hp⟩ := hlow
  have hnonflat : D.curvatureTensorNorm p ≠ 0 := by
    intro hz
    have hs := D.abs_scalarCurvature_le_curvatureTensorNorm p
    rw [hz, mul_zero] at hs
    linarith [le_abs_self (D.scalarCurvature p)]
  have hballopen (r : ℝ) : IsOpen (g0.ball G.limit.base r) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g0.toRiemannianMetric⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    change IsOpen {x : M | edist G.limit.base x < ENNReal.ofReal r}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let U (j : ℕ) : TopologicalSpace.Opens M :=
    ⟨g0.ball G.limit.base (j + 1), hballopen (j + 1)⟩
  have hbase (j : ℕ) : G.limit.base ∈ (U j : Set M) := by
    change g0.edist G.limit.base G.limit.base < ENNReal.ofReal (j + 1)
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < j + 1)
  let : ∀ j, ConnectedSpace (U j) := fun j => Subtype.connectedSpace
    ⟨⟨G.limit.base, hbase j⟩, g0.isPreconnected_ball G.limit.base (j + 1)⟩
  let e (j : ℕ) : U j → M := Subtype.val
  have he (j : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e j) :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U j)
  choose delta hdelta F hmetric hsign using fun j : ℕ =>
    hlocal (j + 1) (by positivity : (0 : ℝ) < j + 1) (U j) rfl
  have hshift (j : ℕ) :
      (fun s : ℝ => s + -T) '' Icc (-(delta j)) 0 ⊆ Icc (-(T + delta j)) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  have hne (j : ℕ) : (Icc (-(delta j)) (0 : ℝ)).Nontrivial :=
    ⟨-(delta j), ⟨le_rfl, by linarith [hdelta j]⟩,
      0, ⟨by linarith [hdelta j], le_rfl⟩, by linarith [hdelta j]⟩
  let Fshift (j : ℕ) := (F j).translate (-T) (hshift j) ordConnected_Icc (hne j)
  have hshiftSign (j : ℕ) (t : ℝ) (ht : t ∈ Icc (-(delta j)) 0) (x : U j) :
      ((Fshift j).connection t).NonnegativeCurvatureOperator x :=
    hsign j (t + -T) (hshift j (mem_image_of_mem _ ht)) x
  have hshiftMetric (j : ℕ) (x : U j) (v w : TangentSpace (𝓡 3) x) :
      ((Fshift j).metric 0).inner x v w = (Fbar.metric (-T)).inner (e j x)
        (mfderiv (𝓡 3) (𝓡 3) (e j) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e j) x w) := by
    simpa only [Fshift, RicciFlow.translate, zero_add] using hmetric j x v w
  have hcover (x : M) : ∃ j, x ∈ (U j : Set M) := by
    obtain ⟨j, hj⟩ := exists_nat_gt ((g0.edist G.limit.base x).toReal)
    refine ⟨j, ?_⟩
    change g0.edist G.limit.base x < ENNReal.ofReal (j + 1)
    apply (ENNReal.lt_ofReal_iff_toReal_lt (g0.edist_ne_top G.limit.base x)).mpr
    linarith
  have hmono {i j : ℕ} (hij : i ≤ j) : (U i : Set M) ⊆ U j := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by exact_mod_cast Nat.add_le_add_right hij 1))
  have hcapture (x y : M) : ∃ j,
      x ∈ range (e j) ∧ p ∈ range (e j) ∧ y ∈ range (e j) := by
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨j, hj⟩ := hcover p
    obtain ⟨k, hk⟩ := hcover y
    let n := max i (max j k)
    refine ⟨n, ⟨⟨x, hmono (le_max_left _ _) hi⟩, rfl⟩,
      ⟨⟨p, hmono ((le_max_left _ _).trans (le_max_right _ _)) hj⟩, rfl⟩,
      ⟨⟨y, hmono ((le_max_right _ _).trans (le_max_right _ _)) hk⟩, rfl⟩⟩
  have hsec : D.NonnegativeSectionalCurvature := fun x v w =>
    D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x (hoperator x) v w
  obtain ⟨B, hB, hscalar, _hcurv⟩ := hbound
    (ι := ℕ) (N := fun j => U j) (M := M)
    hC
    (fun j => -(delta j)) (fun j => neg_neg_of_pos (hdelta j)) Fshift hshiftSign
    D D.curvatureTensorCalculus hcomplete hsec e he hshiftMetric p hnonflat hcapture
    eta C heta hetaLe hcanonical
  exact ⟨B, hB, hscalar⟩

end PoincareConjecture.M30
