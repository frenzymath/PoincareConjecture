import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph.Product

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.CylinderCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in
private theorem exists_smooth_localChart
    {F : EuclideanSpace ℝ (Fin 3) → M} {p : EuclideanSpace ℝ (Fin 3)}
    (hF : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ F p) :
    ∃ B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      p ∈ B.source ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ B B.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ B.symm B.target ∧ (B : _ → _) = F := by
  obtain ⟨φ, hp, hφ⟩ := hF
  let ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞ := {
    φ with
    toFun := F
    map_source' := fun x hx => hφ hx ▸ φ.map_source hx
    left_inv' := fun x hx => by rw [hφ hx]; exact φ.left_inv hx
    right_inv' := fun y hy => (hφ (φ.map_target hy)).trans (φ.right_inv hy)
    contMDiffOn_toFun := φ.contMDiffOn_toFun.congr hφ }
  exact ⟨ψ.toOpenPartialHomeomorph, hp, ψ.contMDiffOn_toFun, ψ.contMDiffOn_invFun, rfl⟩

theorem centeredParametrization_isLocalDiffeomorphAt
    {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹) :
    IsLocalDiffeomorphAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞
      (centeredParametrization f q) (0, s) := by
  let c : PartialDiffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere (EuclideanSpace ℝ (Fin 2)) ∞ := {
    toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin 2)) q).toPartialEquiv
    open_source := (chartAt (EuclideanSpace ℝ (Fin 2)) q).open_source
    open_target := (chartAt (EuclideanSpace ℝ (Fin 2)) q).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 := by
    apply c.symm.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞
    change (0 : EuclideanSpace ℝ (Fin 2)) ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target
    rw [sphere_chart_target]
    trivial
  have hid : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (id : ℝ → ℝ) s :=
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph s
  have hp := hc.prodMap hid
  have hp' : IsLocalDiffeomorphAt 𝓘(ℝ, RoundCylinderCoordinates)
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (Prod.map (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm id) (0, s) := by
    simpa +instances only [modelWithCornersSelf_prod, chartedSpaceSelf_prod] using hp
  have hnext : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (Prod.map (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm id (0, s)) := by
    simp only [Prod.map_apply, id_eq, sphere_chart_symm_zero]
    exact hf ⟨(q, s), ⟨mem_univ _, hs⟩⟩
  exact hp'.comp (𝓡 3) M hnext

theorem exists_centered_localChart
    {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹)
    (e : RoundCylinderCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ∃ B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      e (0, s) ∈ B.source ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ B B.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ B.symm B.target ∧
      (B : _ → _) = centeredParametrization f q ∘ e.symm := by
  apply exists_smooth_localChart
  apply (e.symm.toDiffeomorph.isLocalDiffeomorph (e (0, s))).comp (𝓡 3) M
  change IsLocalDiffeomorphAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞
    (centeredParametrization f q) (e.symm (e (0, s)))
  rw [e.symm_apply_apply]
  exact centeredParametrization_isLocalDiffeomorphAt hf q hs

end PoincareConjecture.CylinderCover
