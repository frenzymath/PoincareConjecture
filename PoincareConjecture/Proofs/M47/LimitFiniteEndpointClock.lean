import PoincareConjecture.Proofs.M47.LimitFiniteSourceAlternative
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem limitFinite_endpoint_buffer_flow
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {T d K : ℝ} (hd : 0 < d) (hc : -T + d / 4 ≤ 0)
    (F : RicciFlow 3 M (Icc (-(T + d / 2)) 0))
    (hcurv : ∀ s ∈ Icc (-(T + d / 2)) 0, ∀ x : M,
      |(F.connection s).curvatureTensorNorm x| ≤ K) :
    ∃ A : RicciFlow 3 M (Icc (-(3 * d / 4)) 0),
      (∀ s, A.metric s = F.metric (s + (-T + d / 4))) ∧
      (∀ s (x : M), (A.connection s).curvatureTensorNorm x =
        (F.connection (s + (-T + d / 4))).curvatureTensorNorm x) ∧
      (∀ s ∈ Icc (-(3 * d / 4)) 0, ∀ x : M,
        |(A.connection s).curvatureTensorNorm x| ≤ K) ∧
      A.metric 0 = F.metric (-T + d / 4) ∧
      -d / 4 ∈ Ioo (-((3 * d / 4) / 2)) 0 ∧
      -d / 4 + (-T + d / 4) = -T := by
  have hmap : (fun s : ℝ => s + (-T + d / 4)) '' Icc (-(3 * d / 4)) 0 ⊆
      Icc (-(T + d / 2)) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  have hne : (Icc (-(3 * d / 4)) (0 : ℝ)).Nontrivial := by
    refine ⟨-(3 * d / 4), ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, ?_⟩
    linarith
  let A := F.translate (-T + d / 4) hmap ordConnected_Icc hne
  refine ⟨A, fun _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro s hs x
    exact hcurv _ (hmap ⟨s, hs, rfl⟩) x
  · change F.metric (0 + (-T + d / 4)) = F.metric (-T + d / 4)
    rw [zero_add]
  · constructor <;> linarith
  · ring

end PoincareConjecture.M47
