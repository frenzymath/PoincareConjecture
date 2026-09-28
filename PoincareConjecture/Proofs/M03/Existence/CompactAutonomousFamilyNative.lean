import PoincareConjecture.Proofs.M03.Existence.CompactIntegralCurveNative
import PoincareConjecture.Proofs.M03.Existence.AutonomousFlowInverseNative









set_option autoImplicit false

open scoped Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.CompactAutonomousFamilyNative

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

local notation "I" => 𝓡 n

noncomputable def orbitData
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (hSmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M =>
        UniformIntegralCurveNative.globalMap V hV
          (CompactIntegralCurveNative.uniformData hV) p.1 p.2)) :
    AutonomousFlowNative.Data V where
  map := fun t x => UniformIntegralCurveNative.globalMap V hV
    (CompactIntegralCurveNative.uniformData hV) t x
  smooth := hSmooth
  initial := fun x => UniformIntegralCurveNative.globalMap_zero V hV
    (CompactIntegralCurveNative.uniformData hV) x
  regularity := fun x => hV x
  orbit := fun x => UniformIntegralCurveNative.globalMap_orbit V hV
    (CompactIntegralCurveNative.uniformData hV) x

@[simp] theorem orbitData_apply
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (hSmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M =>
        UniformIntegralCurveNative.globalMap V hV
          (CompactIntegralCurveNative.uniformData hV) p.1 p.2))
    (t : ℝ) (x : M) :
    (orbitData V hV hSmooth).map t x =
      UniformIntegralCurveNative.globalMap V hV
        (CompactIntegralCurveNative.uniformData hV) t x := rfl

theorem exists_diffeomorph_family
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x : M => (⟨x, V x⟩ : TangentBundle I M)))
    (hSmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M =>
        UniformIntegralCurveNative.globalMap V hV
          (CompactIntegralCurveNative.uniformData hV) p.1 p.2)) :
    ∃ F : AutonomousFlowNative.Data V,
      ∀ t x, (AutonomousFlowNative.autonomousDiffeomorphFamily V F) t x =
        UniformIntegralCurveNative.globalMap V hV
          (CompactIntegralCurveNative.uniformData hV) t x := by
  let F := orbitData V hV hSmooth
  refine ⟨F, ?_⟩
  intro t x
  exact AutonomousFlowNative.autonomousDiffeomorphFamily_apply V F t x

end PoincareConjecture.CompactAutonomousFamilyNative

end
