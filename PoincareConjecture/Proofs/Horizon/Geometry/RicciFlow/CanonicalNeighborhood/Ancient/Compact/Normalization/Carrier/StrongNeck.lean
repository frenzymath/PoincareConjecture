import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticNeck
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Small









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N]

private theorem roundCylinderPullback_symm_eq
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (he : MetricHomothety g h e 1)
    (Φ : RoundCylinderSpace → N) (z : RoundCylinderSpace)
    (hΦ : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z)
    (a b : RoundCylinderTangent z) :
    roundCylinderPullback g (e.symm ∘ Φ) z a b = roundCylinderPullback h Φ z a b := by
  let f := e.symm ∘ Φ
  have hdiff : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z :=
    (e.symm.contMDiff.mdifferentiable (by simp) _).comp z hΦ
  have hcomp : e ∘ f = Φ := by
    funext y
    exact e.apply_symm_apply _
  have hd : (mfderiv (𝓡 3) (𝓡 3) e (f z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z := by
    rw [← mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _) hdiff, hcomp]
  have hv (a : RoundCylinderTangent z) :
      mfderiv (𝓡 3) (𝓡 3) e (f z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z a) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z a :=
    congrArg (fun A => A a) hd
  have hm := he (f z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z a)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z b)
  rw [hv a, hv b, one_mul] at hm
  dsimp only [f, Function.comp_apply] at hm
  rw [e.apply_symm_apply] at hm
  exact hm.symm

namespace StrongEvolvingNeck

variable [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  [MeasurableSpace N] [BorelSpace N]
  [T2Space N] [T3Space N] [SecondCountableTopology N] [ConnectedSpace N]
  {K : AncientKappaSolution 3 M} {L : AncientKappaSolution 3 N}
  {t epsilon : ℝ}



def pullbackCarrier (A : StrongEvolvingNeck L t epsilon)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (he : ∀ s : ℝ, s ≤ 0 → MetricHomothety (K.flow.metric s) (L.flow.metric s) e 1) :
    StrongEvolvingNeck K t epsilon := by
  let H := Homothety.metricHomothetyCalculus (K.flow.metric t) (L.flow.metric t)
    e 1 zero_lt_one (he t A.time_mem)
  let E := A.terminal_neck.m48_pullback (he t A.time_mem) H (K.flow.connection t)
  have hscalar : (K.flow.connection t).scalarCurvature (e.symm A.center) =
      (L.flow.connection t).scalarCurvature A.center := by
    simpa only [e.apply_symm_apply] using
      H.m48_scalar_eq (K.flow.connection t) (L.flow.connection t) (e.symm A.center)
  have hR : 0 < (L.flow.connection t).scalarCurvature A.center := by
    simpa only [A.terminal_connection, A.terminal_center] using
      A.terminal_neck.scalar_center_pos
  refine {
    time_mem := A.time_mem
    center := e.symm A.center
    duration := A.duration
    duration_pos := A.duration_pos
    normalized_duration := by rw [hscalar]; exact A.normalized_duration
    terminal_neck := E
    terminal_center := congrArg e.symm A.terminal_center
    terminal_epsilon := A.terminal_epsilon
    terminal_connection := rfl
    metric_comparison := ?_ }
  apply RoundCylinderFamilyClose.congr (B' := fun s z a b =>
    (L.flow.connection t).scalarCurvature A.center *
      roundCylinderPullback
        (L.flow.metric (t + s / (L.flow.connection t).scalarCurvature A.center))
        A.terminal_neck.coordinate_map z a b) ?_ A.metric_comparison
  intro s hs z hz a b
  rw [hscalar]
  have htime : t + s / (L.flow.connection t).scalarCurvature A.center ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 hR.le)).trans A.time_mem
  have hΦ : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      A.terminal_neck.coordinate_map z := by
    apply (A.terminal_neck.coordinate_map_smooth.contMDiffAt ?_).mdifferentiableAt (by simp)
    apply (isOpen_univ.prod isOpen_Ioo).mem_nhds
    exact ⟨mem_univ _, by simpa only [A.terminal_epsilon] using hz⟩
  exact congrArg (fun r : ℝ => (L.flow.connection t).scalarCurvature A.center * r)
    (roundCylinderPullback_symm_eq e (he _ htime) A.terminal_neck.coordinate_map z hΦ a b)

variable (A : StrongEvolvingNeck L t epsilon)
  (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
  (he : ∀ s : ℝ, s ≤ 0 → MetricHomothety (K.flow.metric s) (L.flow.metric s) e 1)

@[simp] theorem pullbackCarrier_center : (A.pullbackCarrier e he).center = e.symm A.center := rfl

@[simp] theorem pullbackCarrier_duration : (A.pullbackCarrier e he).duration = A.duration := rfl

@[simp] theorem pullbackCarrier_carrier :
    (A.pullbackCarrier e he).terminal_neck.carrier = e ⁻¹' A.terminal_neck.carrier := rfl

@[simp] theorem pullbackCarrier_coordinate_map :
    (A.pullbackCarrier e he).terminal_neck.coordinate_map =
      e.symm ∘ A.terminal_neck.coordinate_map := rfl

@[simp] theorem pullbackCarrier_coordinate_inverse :
    (A.pullbackCarrier e he).terminal_neck.coordinate_inverse =
      A.terminal_neck.coordinate_inverse ∘ e := rfl

@[simp] theorem pullbackCarrier_region (a b : ℝ) :
    (A.pullbackCarrier e he).terminal_neck.region a b =
      e ⁻¹' A.terminal_neck.region a b := rfl

@[simp] theorem pullbackCarrier_central_sphere :
    (A.pullbackCarrier e he).terminal_neck.central_sphere =
      e ⁻¹' A.terminal_neck.central_sphere := rfl

theorem pullbackCarrier_spacetime_coordinate
    (s : Ioc (t - A.duration) t) :
    (A.pullbackCarrier e he).spacetime_coordinate s =
      e.symm ∘ A.spacetime_coordinate s := rfl




def ofPullbackFlow (hflow : L.flow = K.flow.pullbackDiffeomorph e.symm) :
    StrongEvolvingNeck K t epsilon := by
  apply A.pullbackCarrier e
  intro s _ x a b
  have hid : e.symm ∘ e = id := by
    funext y
    exact e.symm_apply_apply y
  rw [hflow, RicciFlow.pullbackDiffeomorph_inner]
  have hi := mfderiv_comp x (e.symm.mdifferentiable (by simp) (e x))
    (e.mdifferentiable (by simp) x)
  rw [hid, mfderiv_id] at hi
  have ha := congrArg (fun T => T a) hi
  have hb := congrArg (fun T => T b) hi
  change a = mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x a) at ha
  change b = mfderiv (𝓡 3) (𝓡 3) e.symm (e x) (mfderiv (𝓡 3) (𝓡 3) e x b) at hb
  rw [← ha, ← hb, e.symm_apply_apply, one_mul]

variable (hflow : L.flow = K.flow.pullbackDiffeomorph e.symm)

@[simp] theorem ofPullbackFlow_center :
    (A.ofPullbackFlow e hflow).center = e.symm A.center := rfl

@[simp] theorem ofPullbackFlow_duration :
    (A.ofPullbackFlow e hflow).duration = A.duration := rfl

@[simp] theorem ofPullbackFlow_carrier :
    (A.ofPullbackFlow e hflow).terminal_neck.carrier = e ⁻¹' A.terminal_neck.carrier := rfl

@[simp] theorem ofPullbackFlow_coordinate_map :
    (A.ofPullbackFlow e hflow).terminal_neck.coordinate_map =
      e.symm ∘ A.terminal_neck.coordinate_map := rfl

@[simp] theorem ofPullbackFlow_coordinate_inverse :
    (A.ofPullbackFlow e hflow).terminal_neck.coordinate_inverse =
      A.terminal_neck.coordinate_inverse ∘ e := rfl

end StrongEvolvingNeck
end PoincareConjecture
