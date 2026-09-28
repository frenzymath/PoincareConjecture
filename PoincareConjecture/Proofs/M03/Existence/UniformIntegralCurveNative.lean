import PoincareConjecture.Proofs.M03.Existence.ConjugatingFlowFamilyNative
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.UniformIntegralCurveNative

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "I" => 𝓡 n

structure Data (V : (x : M) → TangentSpace I x) where
  ε : ℝ
  ε_pos : 0 < ε
  local_curve : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
    IsMIntegralCurveOn γ V (Ioo (-ε) ε)

variable {V : (x : M) → TangentSpace I x}

theorem exists_global_orbit
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M))
      ) (D : Data V) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V := by
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn
    hv D.ε_pos D.local_curve x

noncomputable def globalOrbit
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (D : Data V) (x : M) : ℝ → M :=
  Classical.choose (exists_global_orbit V hv D x)

theorem globalOrbit_spec
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (D : Data V) (x : M) :
    globalOrbit V hv D x 0 = x ∧ IsMIntegralCurve (globalOrbit V hv D x) V := by
  exact Classical.choose_spec (exists_global_orbit V hv D x)

@[simp] theorem globalOrbit_zero
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (D : Data V) (x : M) :
    globalOrbit V hv D x 0 = x :=
  (globalOrbit_spec V hv D x).1

theorem globalOrbit_isMIntegralCurve
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (D : Data V) (x : M) :
    IsMIntegralCurve (globalOrbit V hv D x) V :=
  (globalOrbit_spec V hv D x).2

noncomputable def globalMap
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (D : Data V) (t : ℝ) (x : M) : M :=
  globalOrbit V hv D x t

@[simp] theorem globalMap_zero
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (D : Data V) (x : M) :
    globalMap V hv D 0 x = x :=
  globalOrbit_zero V hv D x

theorem globalMap_orbit
    (V : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (D : Data V) (x : M) :
    IsMIntegralCurve (globalMap V hv D · x) V := by
  exact globalOrbit_isMIntegralCurve V hv D x

end PoincareConjecture.UniformIntegralCurveNative

end
