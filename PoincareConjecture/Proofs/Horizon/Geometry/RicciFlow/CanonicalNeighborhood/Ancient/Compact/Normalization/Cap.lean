import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.CapRescale
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.StructuralData

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaNormalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M} {b epsilon C : ℝ}

theorem inverseNormalizedMetric_eq (A : AncientKappaNormalization K p b) :
    rescaledMetric (A.target.flow.metric 0) A.scale⁻¹ (inv_pos.mpr A.scale_pos) =
      K.flow.metric b := by
  have hinner :
      (rescaledMetric (A.target.flow.metric 0) A.scale⁻¹ (inv_pos.mpr A.scale_pos)).inner =
        (K.flow.metric b).inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [rescaledMetric_inner, A.metric_eq, zero_div, add_zero,
      ← mul_assoc, inv_mul_cancel₀ A.scale_pos.ne', one_mul]
  have hext (g h : RiemannianMetric 3 M) (he : g.inner = h.inner) : g = h := by
    cases g
    cases h
    cases he
    rfl
  exact hext _ _ hinner

def capFromNormalization (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) : CapCertificate (K.flow.metric b) :=
  NoncompactKappa.capWithConnection
    ((cap.rescale A.scale⁻¹ (inv_pos.mpr A.scale_pos)).castMetric A.inverseNormalizedMetric_eq)
    (K.flow.connection b)

@[simp] theorem capFromNormalization_epsilon (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).epsilon = cap.epsilon := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_epsilon]
  rfl

@[simp] theorem capFromNormalization_cap_constant (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).cap_constant = cap.cap_constant := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_cap_constant]
  rfl

@[simp] theorem capFromNormalization_carrier (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).carrier = cap.carrier := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_carrier]
  rfl

@[simp] theorem capFromNormalization_core (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).core = cap.core := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_core]
  rfl

@[simp] theorem capFromNormalization_closed_core (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).closed_core = cap.closed_core := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_closed_core]
  rfl

@[simp] theorem capFromNormalization_model_kind (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).model_kind = cap.model_kind := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_model_kind]
  rfl

@[simp] theorem capFromNormalization_puncture (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).puncture = cap.puncture := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_puncture]
  rfl

@[simp] theorem capFromNormalization_boundary_sphere (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).boundary_sphere = cap.boundary_sphere := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_boundary_sphere]
  rfl

@[simp] theorem capFromNormalization_core_radius (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).core_radius =
      fun y => cap.core_radius y / Real.sqrt A.scale := by
  simp only [capFromNormalization, NoncompactKappa.capWithConnection,
    CapCertificate.castMetric_core_radius]
  funext y
  change Real.sqrt A.scale⁻¹ * cap.core_radius y = _
  rw [Real.sqrt_inv, div_eq_mul_inv, mul_comm]

@[simp] theorem capFromNormalization_connection (A : AncientKappaNormalization K p b)
    (cap : CapCertificate (A.target.flow.metric 0)) :
    (A.capFromNormalization cap).connection = K.flow.connection b := rfl

def strongCapFromNormalization (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (cap : StrongCapCertificate A.target 0 epsilon C) : StrongCapCertificate K b epsilon C :=
  { NoncompactKappa.strongCapOfCap K hb (A.capFromNormalization cap.cap)
      (by simpa using cap.cap_epsilon) (by simpa using cap.cap_constant) with
    center := cap.center
    center_in_core := by
      change cap.center ∈ (A.capFromNormalization cap.cap).core
      simpa only [capFromNormalization_core] using cap.center_in_core }

@[simp] theorem strongCapFromNormalization_center (A : AncientKappaNormalization K p b)
    (hb : b ≤ 0) (cap : StrongCapCertificate A.target 0 epsilon C) :
    (A.strongCapFromNormalization hb cap).center = cap.center := rfl

@[simp] theorem strongCapFromNormalization_carrier (A : AncientKappaNormalization K p b)
    (hb : b ≤ 0) (cap : StrongCapCertificate A.target 0 epsilon C) :
    (A.strongCapFromNormalization hb cap).cap.carrier = cap.cap.carrier := by
  change (A.capFromNormalization cap.cap).carrier = _
  exact A.capFromNormalization_carrier cap.cap

@[simp] theorem strongCapFromNormalization_core (A : AncientKappaNormalization K p b)
    (hb : b ≤ 0) (cap : StrongCapCertificate A.target 0 epsilon C) :
    (A.strongCapFromNormalization hb cap).cap.core = cap.cap.core := by
  change (A.capFromNormalization cap.cap).core = _
  exact A.capFromNormalization_core cap.cap

@[simp] theorem strongCapFromNormalization_cap_constant (A : AncientKappaNormalization K p b)
    (hb : b ≤ 0) (cap : StrongCapCertificate A.target 0 epsilon C) :
    (A.strongCapFromNormalization hb cap).cap.cap_constant = cap.cap.cap_constant := by
  change (A.capFromNormalization cap.cap).cap_constant = _
  exact A.capFromNormalization_cap_constant cap.cap

@[simp] theorem strongCapFromNormalization_connection (A : AncientKappaNormalization K p b)
    (hb : b ≤ 0) (cap : StrongCapCertificate A.target 0 epsilon C) :
    (A.strongCapFromNormalization hb cap).cap.connection = K.flow.connection b := rfl

end PoincareConjecture.AncientKappaNormalization
