import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_marked_rim_of_trace
    {X : Type*} [TopologicalSpace X] {Z : Set X} {base v : Z}
    (g : V2 → X) (hg : ContinuousOn g D2) (hmark : ∀ x ∈ Q2, g x ∈ Z)
    (rho : Path v v) (p : Path base v)
    (htrace : ∀ t, (rho t : X) = g (squareRimLoop t)) :
    ∃ (rim : C(Q2, Z)) (basepath : Path base (rim squareRimBase)),
      (∀ x : Q2, g x = (rim x : X)) ∧
      basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) =
        p.whiskeredLoopClass rho := by
  let rim : C(Q2, Z) := ⟨fun x ↦ ⟨g x, hmark x x.property⟩,
    (hg.comp_continuous continuous_subtype_val
      (fun x ↦ sphere_subset_closedBall x.property)).subtype_mk _⟩
  have hv : rim squareRimBase = v := by
    apply Subtype.ext
    change g squareRimBase = (v : X)
    simpa using (htrace 0).symm
  have hrho : squareRimLoop.map rim.continuous = rho.cast hv hv := by
    apply Path.ext
    funext t
    apply Subtype.ext
    exact (htrace t).symm
  refine ⟨rim, p.cast rfl hv, fun _ ↦ rfl, ?_⟩
  rw [hrho]
  rfl

end PoincareConjecture.M76.Dehn
