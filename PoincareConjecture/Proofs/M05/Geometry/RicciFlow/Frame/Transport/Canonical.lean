import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.RicciEndomorphism
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.HalfOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Set

universe u

noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

def canonicalTransport (F : RicciFlow n M (Ico a b)) (t : ℝ) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  transportIco (ricciEndomorphism F x) a b
    (contDiffOn_ricciEndomorphism F x).continuousOn t

@[simp] theorem canonicalTransport_initial (F : RicciFlow n M (Ico a b))
    (hab : a < b) (x : M) :
    canonicalTransport F a x = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  unfold canonicalTransport
  exact transportIco_left _ hab _

theorem canonicalTransport_hasDerivWithinAt (F : RicciFlow n M (Ico a b))
    {t : ℝ} (ht : t ∈ Ico a b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
    HasDerivWithinAt (fun s => canonicalTransport F s x)
      ((ricciEndomorphism F x t).comp (canonicalTransport F t x)) (Ico a b) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  unfold canonicalTransport
  exact transportIco_hasDerivWithinAt _ _ ht

theorem canonicalTransport_contDiffOn_time (F : RicciFlow n M (Ico a b)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
    ContDiffOn ℝ ∞ (fun s => canonicalTransport F s x) (Ico a b) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  unfold canonicalTransport
  exact transportIco_contDiffOn _ (contDiffOn_ricciEndomorphism F x)

theorem canonicalTransport_bijective (F : RicciFlow n M (Ico a b))
    (t : ℝ) (x : M) : Function.Bijective (canonicalTransport F t x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  by_cases ht : t ∈ Ico a b
  · unfold canonicalTransport
    exact transportIco_bijective _ _ ht
  · simp only [canonicalTransport, transportIco, dif_neg ht]
    exact Function.bijective_id

theorem canonicalTransport_pairing (F : RicciFlow n M (Ico a b))
    (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x (canonicalTransport F t x v) (canonicalTransport F t x w) =
      (F.metric a).inner x v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  exact transportIco_pairing (ricciEndomorphism F x) hab
    (contDiffOn_ricciEndomorphism F x).continuousOn
    (fun s => (F.metric s).inner x) (ricciBilin F x)
    (fun _ hs => metricBilin_hasDerivWithinAt F x hs)
    (fun s _ => metric_ricciEndomorphism_left F x s)
    (fun _ hs => metric_ricciEndomorphism_right F x hs) ht v w

def orthonormalTransport (F : RicciFlow n M (Ico a b)) (t : ℝ) (x : M) :
    TangentSpace (𝓡 n) x ≃L[ℝ] TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  (LinearEquiv.ofBijective (canonicalTransport F t x).toLinearMap
    (canonicalTransport_bijective F t x)).toContinuousLinearEquiv

@[simp] theorem orthonormalTransport_toContinuousLinearMap
    (F : RicciFlow n M (Ico a b)) (t : ℝ) (x : M) :
    (orthonormalTransport F t x).toContinuousLinearMap = canonicalTransport F t x := by
  rfl

end PoincareConjecture.RicciFlow.Frame
