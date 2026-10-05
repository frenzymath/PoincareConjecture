import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry

/-!
Adapted from Mapher `PoincareMT/Definitions/M34StandardCapExistence.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M34 repaired standard-cap existence data

The existence package retains the actual maximal cap flow and its geometric,
asymptotic, and noncollapsing certificates.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedStandardCapExistenceData (g₀ : StandardInitialMetric) where
  atlas : StandardCylinderAtlas
  flow : MaximalStandardCapFlow g₀
  lifetime_one : flow.base.lifetime = 1
  complete : ∀ t ∈ Set.Ico 0 flow.base.lifetime,
    MetricComplete (flow.metric t)
  positive_sectional : ∀ t ∈ Set.Ioo 0 flow.base.lifetime,
    StandardCapPositiveSectional (flow.connection t)
  nonnegative_sectional : ∀ t ∈ Set.Ico 0 flow.base.lifetime,
    (flow.connection t).NonnegativeSectionalCurvature
  rotation_invariant : ∀ t ∈ Set.Ico 0 flow.base.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x : StandardCapSpace, ∀ u v : TangentSpace (𝓡 3) x,
        (flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
            (flow.metric t).inner x u v
  initial_estimate : StandardCapEstimate g₀
  asymptotic : ∀ t₀ : ℝ, t₀ ∈ Set.Ico 0 flow.base.lifetime →
    ∀ epsilon : ℝ, 0 < epsilon →
      Nonempty (StandardFlowAsymptoticCertificate atlas flow epsilon t₀)
  noncollapsing : Nonempty (StandardFlowNoncollapsingCertificate flow)

end PoincareMT
