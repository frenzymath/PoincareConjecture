import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.ComponentDeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} (D : LeviCivitaData g)
  (hc : IsCoveringMap (unitRicciKernelProjection D))
  (p : UnitRicciKernel D)
  (hp : unitRicciKernelReverse D p ∈ connectedComponent p)

def unitRicciKernelComponentReverse :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    C ≃ₘ⟮𝓡 n, 𝓡 n⟯ C := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let r : C → C := fun q =>
    ⟨unitRicciKernelReverse D q.1, unitRicciKernelReverse_mem_component D q.2 hp⟩
  have hrr : Function.Involutive r := fun q =>
    Subtype.ext (unitRicciKernelReverse_involutive D q.1)
  have hr : ContMDiff (𝓡 n) (𝓡 n) ∞ r := by
    apply (ContMDiff.subtypeVal_comp_iff C r).mp
    exact (unitRicciKernelReverse_contMDiff D hc).comp contMDiff_subtype_val
  exact {
    toFun := r
    invFun := r
    left_inv := hrr
    right_inv := hrr
    contMDiff_toFun := hr
    contMDiff_invFun := hr }

@[simp] theorem unitRicciKernelComponentReverse_val :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    ∀ q : C, (unitRicciKernelComponentReverse D hc p hp q).1 =
      unitRicciKernelReverse D q.1 := by
  intros
  rfl

theorem unitRicciKernelComponentReverse_involutive :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    Function.Involutive (unitRicciKernelComponentReverse D hc p hp) := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  intro q
  exact Subtype.ext (unitRicciKernelReverse_involutive D q.1)

theorem unitRicciKernelComponentReverse_free :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    ∀ q, unitRicciKernelComponentReverse D hc p hp q ≠ q := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  intro q h
  exact unitRicciKernelReverse_fixedPointFree D q.1 (congrArg Subtype.val h)

theorem unitRicciKernelComponent_projection_fiber_eq_orbit
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    ∀ a b : C, unitRicciKernelProjection D a.1 = unitRicciKernelProjection D b.1 ↔
      b = a ∨ b = unitRicciKernelComponentReverse D hc p hp a := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  dsimp only
  intro a b
  rw [unitRicciKernelProjection_fiber_eq_reverse D hcard]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

omit D hc p hp in

theorem unitRicciKernelComponentReverse_preserves_metric
    {J : Set ℝ} (F : RicciFlow n M J)
    (hc : IsCoveringMap (unitRicciKernelProjection (F.connection 0)))
    (p : UnitRicciKernel (F.connection 0))
    (hp : unitRicciKernelReverse (F.connection 0) p ∈ connectedComponent p)
    (t : ℝ) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    let r := unitRicciKernelComponentReverse (F.connection 0) hc p hp
    let h := ((unitRicciKernelFlow F hc).restrictComponent p).metric t
    ∀ (q : C) (v w : TangentSpace (𝓡 n) q),
      h.inner (r q) (mfderiv (𝓡 n) (𝓡 n) r q v)
        (mfderiv (𝓡 n) (𝓡 n) r q w) = h.inner q v w := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let r := unitRicciKernelComponentReverse (F.connection 0) hc p hp
  let L := unitRicciKernelFlow F hc
  dsimp only
  intro q v w
  let incl : C → UnitRicciKernel (F.connection 0) := Subtype.val
  let rev := unitRicciKernelReverse (F.connection 0)
  have hi : ContMDiff (𝓡 n) (𝓡 n) ∞ incl := contMDiff_subtype_val
  have hr : ContMDiff (𝓡 n) (𝓡 n) ∞ rev :=
    unitRicciKernelReverse_contMDiff (F.connection 0) hc
  have hd : (mfderiv (𝓡 n) (𝓡 n) incl (r q)).comp
        (mfderiv (𝓡 n) (𝓡 n) r q) =
      (mfderiv (𝓡 n) (𝓡 n) rev (incl q)).comp
        (mfderiv (𝓡 n) (𝓡 n) incl q) := by
    rw [← mfderiv_comp q (hi.mdifferentiable (by simp) _)
      (r.contMDiff.mdifferentiable (by simp) q),
      ← mfderiv_comp q (hr.mdifferentiable (by simp) _)
        (hi.mdifferentiable (by simp) q)]
    rfl
  change (L.metric t).inner (rev (incl q))
    (mfderiv (𝓡 n) (𝓡 n) incl (r q) (mfderiv (𝓡 n) (𝓡 n) r q v))
    (mfderiv (𝓡 n) (𝓡 n) incl (r q) (mfderiv (𝓡 n) (𝓡 n) r q w)) = _
  rw [← ContinuousLinearMap.comp_apply, hd, ← ContinuousLinearMap.comp_apply, hd]
  exact unitRicciKernelFlow_reverse_preserves_metric F hc t (incl q)
    (mfderiv (𝓡 n) (𝓡 n) incl q v) (mfderiv (𝓡 n) (𝓡 n) incl q w)

end PoincareConjecture.RicciFlow.Splitting
