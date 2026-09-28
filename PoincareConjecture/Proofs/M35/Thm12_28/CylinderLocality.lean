import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

private theorem cylinder_iterated_congr {epsilon : ℝ} {B B' : RoundCylinderTwoTensor}
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = B' z v w) (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) (p : RoundCylinderCoordinates) (hp : p.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (a : Fin (2 + k) → Fin 3) :
    roundCylinderIteratedDerivative u c B k p a =
      roundCylinderIteratedDerivative u c B' k p a := by
  induction k generalizing p with
  | zero =>
    exact congrArg (fun r : ℝ => r - roundCylinderGram u c p (a 0) (a 1))
      (h (c.symm p.1, p.2) hp _ _)
  | succ k ih =>
    have hf : (fun q => roundCylinderIteratedDerivative u c B k q (fun i => a i.succ)) =ᶠ[𝓝 p]
        (fun q => roundCylinderIteratedDerivative u c B' k q (fun i => a i.succ)) := by
      filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds hp] with q hq
      exact ih q hq _
    change fderiv ℝ _ p _ - _ = fderiv ℝ _ p _ - _
    apply congrArg₂ (fun r s : ℝ => r - s)
    · exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
        L (roundCylinderCoordinateBasis (a 0))) (hf.fderiv_eq (𝕜 := ℝ))
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun r : ℝ => roundCylinderChristoffel u c p j (a 0) (a i.succ) * r)
        (ih p hp _)

theorem cylinder_jet_congr {epsilon : ℝ} {B B' : RoundCylinderTwoTensor}
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = B' z v w) (u : ℝ) (k : ℕ)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    roundCylinderJetErrorSquared u B k z = roundCylinderJetErrorSquared u B' k z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_congr rfl
  intro j _
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  have heq := funext (cylinder_iterated_congr h u c j (c z.1, z.2) hz)
  rw [heq]

theorem cylinder_smooth_congr {epsilon : ℝ} {B B' : RoundCylinderTwoTensor}
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = B' z v w)
    (hsmooth : RoundCylinderTensorSmoothOn epsilon B) :
    RoundCylinderTensorSmoothOn epsilon B' := by
  intro q a b
  apply (hsmooth q a b).congr
  intro p hp
  exact (h _ hp.2 _ _).symm

theorem cylinder_family_congr {epsilon : ℝ} {I : Set ℝ}
    {B B' : ℝ → RoundCylinderTwoTensor}
    (h : ∀ u ∈ I, ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B u z v w = B' u z v w)
    (hclose : RoundCylinderFamilyClose epsilon I B) :
    RoundCylinderFamilyClose epsilon I B' := by
  obtain ⟨hsmooth, b, hb, hjet⟩ := hclose
  refine ⟨fun u hu => cylinder_smooth_congr (h u hu) (hsmooth u hu), b, hb, ?_⟩
  intro u hu z hz
  exact (cylinder_jet_congr (h u hu) u _ z hz) ▸ hjet u hu z hz

end PoincareConjecture.M35
