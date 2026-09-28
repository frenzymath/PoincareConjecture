import PoincareConjecture.Proofs.M03.Existence.ConjugatingFlowFamilyNative
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique










set_option autoImplicit false

open Function Set
open scoped Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.AutonomousFlowNative

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "I" => 𝓡 n

structure Data (V : (x : M) → TangentSpace I x) where
  map : ℝ → M → M
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
    (fun p : ℝ × M => map p.1 p.2)
  initial : ∀ x, map 0 x = x
  regularity : ∀ y : M, ContMDiffAt I (ModelWithCorners.tangent I) 1
      (fun x : M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) x (V x)) y
  orbit : ∀ x, IsMIntegralCurve (map · x) V

variable {V : (x : M) → TangentSpace I x}

theorem autonomous_flow_group_law
    (V : (x : M) → TangentSpace I x) (F : Data V) (s t : ℝ) (x : M) :
    F.map (s + t) x = F.map s (F.map t x) := by
  have hv : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun y : M => (⟨y, V y⟩ : TangentBundle I M)) := by
    exact F.regularity
  have hshift : IsMIntegralCurve ((F.map · x) ∘ (· + t)) V :=
    (F.orbit x).comp_add t
  have hbase : IsMIntegralCurve (fun s : ℝ => F.map s (F.map t x)) V := F.orbit _
  have heq := isMIntegralCurve_eq_of_contMDiff
    (t₀ := 0) (v := V) (γ := (F.map · x) ∘ (· + t))
    (γ' := fun r : ℝ => F.map r (F.map t x))
    (fun _ => BoundarylessManifold.isInteriorPoint) hv hshift hbase
    (by simp [F.initial])
  have hs := congrFun heq s
  simpa [Function.comp_apply] using hs

theorem autonomous_flow_inverse_left
    (V : (x : M) → TangentSpace I x) (F : Data V) (t : ℝ) (x : M) :
    F.map (-t) (F.map t x) = x := by
  have h := autonomous_flow_group_law V F (-t) t x
  simpa [F.initial] using h.symm

theorem autonomous_flow_inverse_right
    (V : (x : M) → TangentSpace I x) (F : Data V) (t : ℝ) (x : M) :
    F.map t (F.map (-t) x) = x := by
  have h := autonomous_flow_group_law V F t (-t) x
  simpa [F.initial] using h.symm

private theorem autonomous_flow_reverse_smooth
    (V : (x : M) → TangentSpace I x) (F : Data V) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => F.map (-p.1) p.2) := by
  have hneg : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (-p.1, p.2)) := by
    have htime : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
        (fun t : ℝ => -t) := contDiff_neg.contMDiff
    exact (htime.comp contMDiff_fst).prodMk contMDiff_snd
  exact F.smooth.comp hneg


noncomputable def autonomousDiffeomorphFamily
    (V : (x : M) → TangentSpace I x) (F : Data V) :
    ℝ → Diffeomorph I I M M ∞ :=
  PoincareConjecture.ConjugatingFlowNative.diffeomorphFamily F.smooth
    (autonomous_flow_reverse_smooth V F)
    (fun t x => autonomous_flow_inverse_left V F t x)
    (fun t x => autonomous_flow_inverse_right V F t x)

@[simp] theorem autonomousDiffeomorphFamily_apply
    (V : (x : M) → TangentSpace I x) (F : Data V) (t : ℝ) (x : M) :
    (autonomousDiffeomorphFamily V F) t x = F.map t x := rfl

@[simp] theorem autonomousDiffeomorphFamily_symm_apply
    (V : (x : M) → TangentSpace I x) (F : Data V) (t : ℝ) (x : M) :
    (autonomousDiffeomorphFamily V F t).symm x = F.map (-t) x := rfl

theorem autonomousDiffeomorphFamily_zero
    (V : (x : M) → TangentSpace I x) (F : Data V) :
    autonomousDiffeomorphFamily V F 0 = Diffeomorph.refl I M ∞ := by
  apply Diffeomorph.ext
  intro x
  simp [autonomousDiffeomorphFamily, F.initial]

end PoincareConjecture.AutonomousFlowNative

end
