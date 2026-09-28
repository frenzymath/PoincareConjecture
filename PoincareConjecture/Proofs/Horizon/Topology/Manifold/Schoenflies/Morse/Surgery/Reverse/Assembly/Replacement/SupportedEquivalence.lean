import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Germ.BallEquivalence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Localization



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1




theorem exists_supported_nested_ball_equivalence
    (B D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hnest : D '' (B '' closedBall (0 : E3) 1) ⊆ B '' closedBall (0 : E3) 1)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hsub : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hfix : ∀ x ∈ g '' closedBall (0 : E2) r, D x = x)
    {O : Set E3} (hO : IsOpen O)
    (hBO : (B '' closedBall (0 : E3) 1) \ (g '' closedBall (0 : E2) 1) ⊆ O)
    (p0 : S2) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ O ∧ Disjoint K (g '' closedBall (0 : E2) 1) ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧
        F '' (B '' closedBall (0 : E3) 1) = D '' (B '' closedBall (0 : E3) 1) := by
  obtain ⟨E, W, hW, hcapW, hEW, hEB⟩ :=
    exists_ball_equivalence_fixing_disk_neighborhood B D hnest g hg hgi hgd hr hsub hfix
  have hcap : g '' closedBall (0 : E2) 1 ⊆ B '' sphere (0 : E3) 1 :=
    (image_mono (closedBall_subset_closedBall hr.le)).trans hsub
  obtain ⟨m, hmi, hml, hm⟩ := exists_ambient_disk_marking B g hg hgi.injOn
    (fun x _ => hgd x) hcap p0
  have hmrange : (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 =
      g '' closedBall (0 : E2) 1 := image_congr hm
  obtain ⟨K, hK, hKO, hKD, F, hFfix, hFon⟩ :=
    exists_supported_ball_equivalence_of_fixed_disk_neighborhood B E m hmi hml hW hO
      (hmrange.symm ▸ hcapW) hEW (by rwa [hmrange]) (by
        rw [hmrange, hEB]
        exact fun y hy => hBO ⟨hnest hy.1, hy.2⟩)
  refine ⟨K, hK, hKO, hmrange ▸ hKD, F, hFfix, ?_⟩
  exact (image_congr hFon).trans hEB


theorem exists_nested_ball_equivalence_fixing_obstacle
    (B D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hnest : D '' (B '' closedBall (0 : E3) 1) ⊆ B '' closedBall (0 : E3) 1)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hsub : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hfix : ∀ x ∈ g '' closedBall (0 : E2) r, D x = x)
    {C : Set E3} (hC : IsClosed C)
    (hBC : (B '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1)
    (p0 : S2) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y ∈ C, F y = y) ∧
      (∀ y ∈ g '' closedBall (0 : E2) 1, F y = y) ∧
      F '' (B '' closedBall (0 : E3) 1) = D '' (B '' closedBall (0 : E3) 1) := by
  obtain ⟨K, _, hKO, hKD, F, hFfix, hFB⟩ :=
    exists_supported_nested_ball_equivalence B D hnest g hg hgi hgd hr hsub hfix
      hC.isOpen_compl (fun y hy hyC => hy.2 (hBC ⟨hy.1, hyC⟩)) p0
  refine ⟨F, ?_, ?_, hFB⟩
  · intro y hy
    exact hFfix y (fun hyK => hKO hyK hy)
  · intro y hy
    exact hFfix y (fun hyK => disjoint_left.mp hKD hyK hy)

end Poincare.Manifold.Schoenflies.Reverse
