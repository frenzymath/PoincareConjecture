import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.CommonArc
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Compression.Isotopy



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1



theorem exists_supported_disk_isotopy_of_common_arc
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {r : Real} (hr : 1 < r)
    (f g : E1 → S1)
    (hfi : InjOn f (closedBall 0 r))
    (hfl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x)
    (hgi : InjOn g (closedBall 0 r))
    (hgl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x)
    (hmark : ∀ x ∈ closedBall (0 : E1) r, A (f x) = B (g x))
    (V : Set E2) (hV : IsOpen V)
    (hmarkV : (fun x => A (f x)) '' closedBall (0 : E1) r ⊆ V)
    (hside : V ∩ (A '' closedBall 0 1) = V ∩ (B '' closedBall 0 1))
    (O : Set E2) (hO : IsOpen O)
    (hAO : (A '' closedBall (0 : E2) 1) \
      ((fun x => A (f x)) '' closedBall (0 : E1) 1) ⊆ O)
    (hBO : (B '' closedBall (0 : E2) 1) \
      ((fun x => A (f x)) '' closedBall (0 : E1) 1) ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => A (f x)) '' closedBall (0 : E1) 1) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        Φ 1 '' (A '' closedBall 0 1) = B '' closedBall 0 1 := by
  obtain ⟨E, hE, W, hW, hmarkW, hEW⟩ :=
    exists_disk_matching_fixing_common_arc_neighborhood A B hr f g hfi hfl hgi hgl
      hmark V hV hmarkV hside
  obtain ⟨K, hK, hKO, hKarc, Φ, hΦ0, hΦs, hΦi, hΦfix, hΦ⟩ :=
    Compression.exists_supported_disk_isotopy_of_fixed_arc_neighborhood A E f
      (hfi.mono (closedBall_subset_closedBall hr.le))
      (fun x hx => hfl x (closedBall_subset_closedBall hr.le hx))
      hW hO hmarkW hEW hAO (by rwa [hE])
  exact ⟨K, hK, hKO, hKarc, Φ, hΦ0, hΦs, hΦi, hΦfix, (image_congr hΦ).trans hE⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
