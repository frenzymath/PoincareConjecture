import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Isometry
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.LaplacianRegularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.SupportingLaplacian
import PoincareConjecture.Proofs.M05.Analysis.Parabolic.SupportTransport

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators InnerProductSpace

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
  unfold TangentSpace
  infer_instance

theorem exists_radialCarrierContact (D : LeviCivitaData g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ (r : ℝ) (Y : TangentSpace (𝓡 n) p → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < r ∧ Metric.ball 0 r ⊆ centeredChartDomain (n := n) p ∧
      (∀ v, ContDiff ℝ ∞ (Y v)) ∧
      (∀ v, fieldFromCenteredCoordinates p (Y v) p = v) ∧
      (∀ v z, z ∈ Metric.ball 0 r → ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Y v (s • z))
          (-(D.centeredConnectionCoefficient p (t • z) z (Y v (t • z)))) t) ∧
      ∃ P : (x : radialNeighborhood (n := n) p r) →
          TangentSpace (𝓡 n) p ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) x.1,
        (∀ x v, P x v = fieldFromCenteredCoordinates p (Y v) x.1) ∧
        ∀ (k : ℕ) (T : (x : M) → TensorFiber (TangentSpace (𝓡 n) x) k)
          (K : (x : M) → Set (TensorFiber (TangentSpace (𝓡 n) x) k))
          (hT : IsSmoothCovariantTensor (fun x v => T x v)),
          (K p).Nonempty → IsClosed (K p) → Convex ℝ (K p) →
          (∀ x : radialNeighborhood (n := n) p r,
            TensorFiber.transport (P x) k '' K p = K x.1) →
          ∀ q : TensorFiber (TangentSpace (𝓡 n) p) k × TensorFiber (TangentSpace (𝓡 n) p) k,
            q ∈ Poincare.Parabolic.unitSupportSet (K p) →
            ⟪q.2, T p - q.1⟫_ℝ = Metric.infDist (T p) (K p) →
            IsLocalMax (fun x => Metric.infDist (T x) (K x)) p →
            ⟪q.2, D.tensorLaplacianFiber hT p⟫_ℝ ≤ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨r, Y, hr, hrU, hY, hinit, hpar, hfirst, hsecond, P, hP⟩ :=
    D.exists_radialParallelIsometries_with_jets p
  refine ⟨r, Y, hr, hrU, hY, hinit, hpar, P, hP, ?_⟩
  intro k T K hT hne hclosed hconv hmap q hq hactive hmax
  let b := g.orthonormalBasis p
  let J := Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p))
  let c : J → ℝ := fun a => q.2 (fun i => b (a i))
  let W : J → Fin k → (x : M) → TangentSpace (𝓡 n) x :=
    fun a i => fieldFromCenteredCoordinates p (Y (b (a i)))
  let f : M → ℝ := fun x => ∑ a : J, c a * T x (fun i => W a i x)
  have hW (a : J) (i : Fin k) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W a i))
        (radialNeighborhood (n := n) p r) := by
    intro x hx
    exact (contMDiffAt_fieldFromCenteredCoordinates p (hY _).contDiffAt hx.1).contMDiffWithinAt
  have hfp : f p = ⟪q.2, T p⟫_ℝ := by
    rw [TensorFiber.inner_eq_sum b]
    simp only [f, c, W, hinit]
    rfl
  have hfy (x : radialNeighborhood (n := n) p r) :
      f x.1 = ⟪TensorFiber.transport (P x) k q.2, T x.1⟫_ℝ := by
    rw [TensorFiber.inner_transport_eq_sum b]
    simp only [hP]
    rfl
  have hmaxf : IsLocalMax f p := by
    filter_upwards [(isOpen_radialNeighborhood (n := n) p r).mem_nhds
      (mem_radialNeighborhood (n := n) p hr), hmax]
      with x hx hdist
    have hsupport := Poincare.Parabolic.transported_support_eval_le_infDist
      hne hclosed hconv (TensorFiber.transport (P ⟨x, hx⟩) k) (hmap ⟨x, hx⟩) hq (T x)
    rw [inner_sub_right, (TensorFiber.transport (P ⟨x, hx⟩) k).inner_map_map,
      ← hfy ⟨x, hx⟩] at hsupport
    rw [inner_sub_right, ← hfp] at hactive
    linarith
  have hsign := D.sum_tensorLaplacian_nonpos_of_isLocalMax hT c W
    (isOpen_radialNeighborhood (n := n) p r) hW (mem_radialNeighborhood (n := n) p hr)
    (fun a i v => hfirst (b (a i)) v)
    (fun a i v => hsecond (b (a i)) v) hmaxf
  rw [TensorFiber.inner_eq_sum b]
  simpa only [tensorLaplacianFiber_apply, c, W, hinit] using hsign

end PoincareConjecture.LeviCivitaData
