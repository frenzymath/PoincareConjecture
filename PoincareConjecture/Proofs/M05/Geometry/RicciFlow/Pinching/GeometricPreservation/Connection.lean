import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.Transport
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.SecondBianchi

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

private theorem mdifferentiableAt_transport_section
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (fun y => canonicalTransport F t y (Y y))) x := by
  exact ((canonicalTransport_contMDiff_space F ht x).mdifferentiableAt
    (by simp)).clm_bundle_apply hY

def transportedConnection (F : RicciFlow n M (Ico a b)) {t : ℝ}
    (ht : t ∈ Ico a b) :
    CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) where
  toFun Y x := (orthonormalTransport F t x).symm.toContinuousLinearMap.comp
    ((F.connection t).connection (fun y => canonicalTransport F t y (Y y)) x)
  isCovariantDerivativeOnUniv := {
    add := by
      intro Y Z x hY hZ hx
      have hadd : (fun y => canonicalTransport F t y ((Y + Z) y)) =
          (fun y => canonicalTransport F t y (Y y)) +
            (fun y => canonicalTransport F t y (Z y)) := by
        funext y
        simp only [Pi.add_apply, map_add]
      rw [hadd, (F.connection t).connection.isCovariantDerivativeOnUniv.add
        (mdifferentiableAt_transport_section F ht hY)
        (mdifferentiableAt_transport_section F ht hZ)]
      ext v
      simp
    leibniz := by
      intro Y f x hY hf hx
      have hsmul : (fun y => canonicalTransport F t y ((f • Y) y)) =
          f • (fun y => canonicalTransport F t y (Y y)) := by
        funext y
        change canonicalTransport F t y (f y • Y y) =
          f y • canonicalTransport F t y (Y y)
        exact map_smul (canonicalTransport F t y) (f y) (Y y)
      rw [hsmul, (F.connection t).connection.isCovariantDerivativeOnUniv.leibniz
        (mdifferentiableAt_transport_section F ht hY) hf]
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
        map_add, map_smul]
      change _ + _ • ((orthonormalTransport F t x).symm
        (orthonormalTransport F t x (Y x))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
  }

@[simp] theorem transportedConnection_apply
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    transportedConnection F ht Y x v = (orthonormalTransport F t x).symm
      ((F.connection t).connection (fun y => canonicalTransport F t y (Y y)) x v) :=
  rfl

theorem transportedConnection_metricCompatible
    (F : RicciFlow n M (Ico a b)) (hab : a < b)
    {t : ℝ} (ht : t ∈ Ico a b) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    (transportedConnection F ht).IsMetricCompatible := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  apply (transportedConnection F ht).isMetricCompatible_iff.mpr
  intro x X Y Z hX hY hZ
  have hpair : (fun y => (F.metric a).inner y (Y y) (Z y)) =
      (fun y => (F.metric t).inner y
        (canonicalTransport F t y (Y y)) (canonicalTransport F t y (Z y))) := by
    funext y
    exact (canonicalTransport_pairing F hab ht y (Y y) (Z y)).symm
  change mvfderiv (𝓡 n) (fun y => (F.metric a).inner y (Y y) (Z y)) x (X x) = _
  rw [hpair, (F.connection t).mvfderiv_inner_on_fields X
    (mdifferentiableAt_transport_section F ht hY)
    (mdifferentiableAt_transport_section F ht hZ)]
  change _ = (F.metric a).inner x (transportedConnection F ht Y x (X x)) (Z x) +
    (F.metric a).inner x (Y x) (transportedConnection F ht Z x (X x))
  rw [← canonicalTransport_pairing F hab ht x,
    ← canonicalTransport_pairing F hab ht x]
  simp only [transportedConnection_apply, LeviCivitaData.covariantDerivativeOnFields]
  change _ = (F.metric t).inner x
      (orthonormalTransport F t x ((orthonormalTransport F t x).symm _))
      (canonicalTransport F t x (Z x)) +
    (F.metric t).inner x (canonicalTransport F t x (Y x))
      (orthonormalTransport F t x ((orthonormalTransport F t x).symm _))
  simp only [ContinuousLinearEquiv.apply_symm_apply]

theorem contMDiffAt_inverseTransport_section
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (fun y => (orthonormalTransport F t y).symm (Y y))) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let A (y : M) := ContinuousLinearMap.inCoordinates E V E V x y x y
    (canonicalTransport F t y)
  have hA : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ A x :=
    (contMDiffAt_hom_bundle _).mp (canonicalTransport_contMDiff_space F ht x) |>.2
  have hAi (y : M) (hy : y ∈ e.baseSet) : (A y).IsInvertible := by
    dsimp only [A]
    rw [ContinuousLinearMap.inCoordinates_eq hy hy,
      ← orthonormalTransport_toContinuousLinearMap F t y]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (ContinuousLinearMap.isInvertible_equiv.comp ContinuousLinearMap.isInvertible_equiv)
  have hAx : (A x).IsInvertible := hAi x
    (FiberBundle.mem_baseSet_trivializationAt E V x)
  have hinv := (hAx.contDiffAt_map_inverse).contMDiffAt.comp x hA
  have hresult := hinv.clm_apply (contMDiffAt_totalSpace.mp hY).2
  rw [contMDiffAt_section]
  apply hresult.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x)]
    with y hy
  change (e ⟨y, (orthonormalTransport F t y).symm (Y y)⟩).2 =
    (A y).inverse ((e ⟨y, Y y⟩).2)
  symm
  apply (hAi y hy).inverse_apply_eq.mpr
  symm
  dsimp only [A]
  rw [ContinuousLinearMap.inCoordinates_eq hy hy]
  change (e.continuousLinearEquivAt ℝ y hy)
    (orthonormalTransport F t y ((e.continuousLinearEquivAt ℝ y hy).symm
      ((e.continuousLinearEquivAt ℝ y hy) ((orthonormalTransport F t y).symm (Y y))))) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem transportedConnection_smooth
    (F : RicciFlow n M (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b) :
    CovariantDerivative.ContMDiffCovariantDerivative (transportedConnection F ht) ∞ := by
  constructor
  constructor
  intro Y hY
  have hUY : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) (∞ + 1)
      (T% (fun y => canonicalTransport F t y (Y y))) univ := by
    simpa using (canonicalTransport_contMDiff_space F ht).contMDiffOn.clm_bundle_apply hY
  have hD := contMDiffOn_univ.mp ((F.connection t).smooth.contMDiff.contMDiff hUY)
  apply contMDiffOn_univ.mpr
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hX := (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
    (FiberBundle.mem_baseSet_trivializationAt E V x)).clm_bundle_apply hv
  have hfield := contMDiffAt_inverseTransport_section F ht ((hD x).clm_bundle_apply hX)
  have hc := (contMDiffAt_totalSpace.mp hfield).2
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x)]
    with y hy
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    transportedConnection_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]

end PoincareConjecture.RicciFlow.Frame
