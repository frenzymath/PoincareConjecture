import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.Support
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.Nested
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.Disjoint



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs

abbrev UnitCircle := sphere (0 : E2) 1



def NestedPair (inner outer : UnitCircle → E2) : Prop :=
  ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
    F '' sphere (0 : E2) 1 = range outer ∧ range inner ⊆ F '' ball 0 1

private theorem plane_rank : 1 < Module.rank Real E2 := by
  rw [← Module.finrank_eq_rank]
  norm_num

private theorem image_boundary_of_ball_matching
    (A B D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (h : D '' (A '' closedBall 0 1) = B '' closedBall 0 1) :
    D '' (A '' sphere (0 : E2) 1) = B '' sphere (0 : E2) 1 := by
  have hc := congrArg frontier h
  have hf (G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
      frontier (G '' closedBall (0 : E2) 1) = G '' sphere (0 : E2) 1 := by
    have hG := G.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
    change G '' frontier (closedBall (0 : E2) 1) = frontier (G '' closedBall 0 1) at hG
    rw [frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at hG
    exact hG.symm
  have hfront := D.toHomeomorph.image_frontier (A '' closedBall 0 1)
  change D '' frontier (A '' closedBall 0 1) = frontier (D '' (A '' closedBall 0 1)) at hfront
  rw [← hfront, hf A, hf B] at hc
  exact hc

theorem nestedPair_iff_of_normalizations
    (inner outer : UnitCircle → E2)
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A '' sphere (0 : E2) 1 = range inner)
    (hB : B '' sphere (0 : E2) 1 = range outer) :
    NestedPair inner outer ↔ A '' closedBall 0 1 ⊆ B '' ball 0 1 := by
  constructor
  · rintro ⟨F, hF, hin⟩
    have heq := F.toHomeomorph.image_ball_eq_of_image_sphere_eq
      B.toHomeomorph plane_rank (hF.trans hB.symm)
    apply B.toHomeomorph.image_closedBall_subset_image_ball_of_sphere_subset
      A.toHomeomorph plane_rank
    change A '' sphere (0 : E2) 1 ⊆ B '' ball 0 1
    rw [hA]
    change range inner ⊆ B.toHomeomorph '' ball 0 1
    exact heq ▸ hin
  · intro hin
    exact ⟨B, hB, hA ▸ (image_mono sphere_subset_closedBall).trans hin⟩


theorem exists_supported_circle_matching
    (c d : UnitCircle → E2)
    (hc : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ c)
    (hd : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ d) :
    ∃ K : Set E2, IsCompact K ∧
      ∃ D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, x ∉ K → D x = x) ∧ D '' range c = range d := by
  obtain ⟨A, hA⟩ := exists_ambient_diffeomorph_of_smooth_circle c hc
  obtain ⟨B, hB⟩ := exists_ambient_diffeomorph_of_smooth_circle d hd
  obtain ⟨_, K, hK, D, hfix, _, hD⟩ :=
    exists_supported_matching_of_ball_embeddings A B (by norm_num : (0 : Real) < 1)
  refine ⟨K, hK, D, hfix, ?_⟩
  rw [← hA, ← hB]
  exact image_boundary_of_ball_matching A B D hD

private theorem supported_matching_nested
    (A₀ A₁ B₀ B₁ : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A₁ '' closedBall 0 1 ⊆ A₀ '' ball 0 1)
    (hB : B₁ '' closedBall 0 1 ⊆ B₀ '' ball 0 1) :
    ∃ K : Set E2, IsCompact K ∧
      ∃ D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, x ∉ K → D x = x) ∧
        D '' (A₀ '' sphere (0 : E2) 1) = B₀ '' sphere (0 : E2) 1 ∧
        D '' (A₁ '' sphere (0 : E2) 1) = B₁ '' sphere (0 : E2) 1 := by
  obtain ⟨_, K₀, hK₀, P, hPfix, _, hP⟩ :=
    exists_supported_matching_of_ball_embeddings A₀ B₀ (by norm_num : (0 : Real) < 1)
  have hPsphere := image_boundary_of_ball_matching A₀ B₀ P hP
  have hPopen : P '' (A₀ '' ball 0 1) = B₀ '' ball 0 1 := by
    have hs : (A₀.trans P) '' sphere (0 : E2) 1 = B₀ '' sphere (0 : E2) 1 :=
      (image_comp P A₀ _).trans hPsphere
    have ho := (A₀.trans P).toHomeomorph.image_ball_eq_of_image_sphere_eq
      B₀.toHomeomorph plane_rank hs
    exact (image_comp P A₀ _).symm.trans ho
  have hPA : (A₁.trans P) '' closedBall 0 1 ⊆ B₀ '' ball 0 1 := by
    change (P ∘ A₁) '' closedBall 0 1 ⊆ B₀ '' ball 0 1
    rw [image_comp, ← hPopen]
    exact image_mono hA
  obtain ⟨K₁, hK₁, hK₁in, F, hFfix, hF⟩ :=
    exists_supported_matching_inside_ball (A₁.trans P) B₁ B₀ hPA hB
  have hFsphere : F '' (B₀ '' sphere (0 : E2) 1) = B₀ '' sphere (0 : E2) 1 := by
    apply (show EqOn F id (B₀ '' sphere (0 : E2) 1) from ?_).image_eq.trans
      (image_id _)
    rintro _ ⟨x, hx, rfl⟩
    apply hFfix
    intro hmem
    obtain ⟨y, hy, hyx⟩ := hK₁in hmem
    have heq : y = x := B₀.injective hyx
    subst y
    exact (ne_of_lt (mem_ball_zero_iff.mp hy)) (mem_sphere_zero_iff_norm.mp hx)
  refine ⟨K₀ ∪ K₁, hK₀.union hK₁, P.trans F, ?_, ?_, ?_⟩
  · intro x hx
    change F (P x) = x
    rw [hPfix x (fun h => hx (Or.inl h)), hFfix x (fun h => hx (Or.inr h))]
  · change (F ∘ P) '' _ = _
    rw [image_comp, hPsphere, hFsphere]
  · change (F ∘ P) '' _ = _
    rw [image_comp]
    have h := image_boundary_of_ball_matching (A₁.trans P) B₁ F hF
    change F '' ((P ∘ A₁) '' sphere (0 : E2) 1) = _ at h
    rwa [image_comp] at h

private theorem supported_matching_disjoint
    (A₀ A₁ B₀ B₁ : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : Disjoint (A₀ '' closedBall 0 1) (A₁ '' closedBall 0 1))
    (hB : Disjoint (B₀ '' closedBall 0 1) (B₁ '' closedBall 0 1)) :
    ∃ K : Set E2, IsCompact K ∧
      ∃ D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, x ∉ K → D x = x) ∧
        D '' (A₀ '' sphere (0 : E2) 1) = B₀ '' sphere (0 : E2) 1 ∧
        D '' (A₁ '' sphere (0 : E2) 1) = B₁ '' sphere (0 : E2) 1 := by
  obtain ⟨_, K₀, hK₀, P, hPfix, _, hP⟩ :=
    exists_supported_matching_of_ball_embeddings A₀ B₀ (by norm_num : (0 : Real) < 1)
  have hPsphere := image_boundary_of_ball_matching A₀ B₀ P hP
  have hPA : Disjoint ((A₁.trans P) '' closedBall 0 1) (B₀ '' closedBall 0 1) := by
    change Disjoint ((P ∘ A₁) '' closedBall 0 1) (B₀ '' closedBall 0 1)
    rw [image_comp, ← hP]
    exact (disjoint_image_iff P.injective).mpr hA.symm
  obtain ⟨K₁, hK₁, _, F, hFfix, hF, hFball⟩ :=
    exists_supported_matching_outside_ball plane_rank (A₁.trans P) B₁ B₀ hPA hB.symm
  have hFsphere : F '' (B₀ '' sphere (0 : E2) 1) = B₀ '' sphere (0 : E2) 1 := by
    exact (show EqOn F id (B₀ '' sphere (0 : E2) 1) from
      fun x hx => hFball x (image_mono sphere_subset_closedBall hx)).image_eq.trans (image_id _)
  refine ⟨K₀ ∪ K₁, hK₀.union hK₁, P.trans F, ?_, ?_, ?_⟩
  · intro x hx
    change F (P x) = x
    rw [hPfix x (fun h => hx (Or.inl h)), hFfix x (fun h => hx (Or.inr h))]
  · change (F ∘ P) '' _ = _
    rw [image_comp, hPsphere, hFsphere]
  · change (F ∘ P) '' _ = _
    rw [image_comp]
    have h := image_boundary_of_ball_matching (A₁.trans P) B₁ F hF
    change F '' ((P ∘ A₁) '' sphere (0 : E2) 1) = _ at h
    rwa [image_comp] at h



theorem exists_supported_circle_pair_matching
    (c d : Fin 2 → UnitCircle → E2)
    (hc : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i))
    (hd : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (d i))
    (hdisjc : Disjoint (range (c 0)) (range (c 1)))
    (hdisjd : Disjoint (range (d 0)) (range (d 1)))
    (hnest : ∀ i j, i ≠ j → (NestedPair (c i) (c j) ↔ NestedPair (d i) (d j))) :
    ∃ K : Set E2, IsCompact K ∧
      ∃ D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, x ∉ K → D x = x) ∧ ∀ i, D '' range (c i) = range (d i) := by
  choose A hA using fun i => exists_ambient_diffeomorph_of_smooth_circle (c i) (hc i)
  choose B hB using fun i => exists_ambient_diffeomorph_of_smooth_circle (d i) (hd i)
  have hnest' (i j : Fin 2) (hij : i ≠ j) :
      (A i '' closedBall 0 1 ⊆ A j '' ball 0 1) ↔
        B i '' closedBall 0 1 ⊆ B j '' ball 0 1 := by
    rw [← nestedPair_iff_of_normalizations (c i) (c j) (A i) (A j) (hA i) (hA j),
      ← nestedPair_iff_of_normalizations (d i) (d j) (B i) (B j) (hB i) (hB j)]
    exact hnest i j hij
  have hAc : Disjoint (A 0 '' sphere (0 : E2) 1) (A 1 '' sphere (0 : E2) 1) := by
    rwa [hA 0, hA 1]
  have hBc : Disjoint (B 0 '' sphere (0 : E2) 1) (B 1 '' sphere (0 : E2) 1) := by
    rwa [hB 0, hB 1]
  have finish (K : Set E2) (hK : IsCompact K)
      (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
      (hfix : ∀ x, x ∉ K → D x = x)
      (h₀ : D '' (A 0 '' sphere (0 : E2) 1) = B 0 '' sphere (0 : E2) 1)
      (h₁ : D '' (A 1 '' sphere (0 : E2) 1) = B 1 '' sphere (0 : E2) 1) :
      ∃ K : Set E2, IsCompact K ∧
        ∃ D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x, x ∉ K → D x = x) ∧ ∀ i, D '' range (c i) = range (d i) := by
    refine ⟨K, hK, D, hfix, ?_⟩
    intro i
    fin_cases i
    · change D '' range (c 0) = range (d 0)
      simpa only [hA 0, hB 0] using h₀
    · change D '' range (c 1) = range (d 1)
      simpa only [hA 1, hB 1] using h₁
  by_cases h₀₁ : A 0 '' closedBall 0 1 ⊆ A 1 '' ball 0 1
  · obtain ⟨K, hK, D, hfix, h₁, h₀⟩ :=
      supported_matching_nested (A 1) (A 0) (B 1) (B 0) h₀₁
        ((hnest' 0 1 (by decide)).mp h₀₁)
    exact finish K hK D hfix h₀ h₁
  by_cases h₁₀ : A 1 '' closedBall 0 1 ⊆ A 0 '' ball 0 1
  · obtain ⟨K, hK, D, hfix, h₀, h₁⟩ :=
      supported_matching_nested (A 0) (A 1) (B 0) (B 1) h₁₀
        ((hnest' 1 0 (by decide)).mp h₁₀)
    exact finish K hK D hfix h₀ h₁
  have hAdisj : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1) := by
    rcases (A 0).toHomeomorph.disjoint_or_nested_image_closedBall
      (A 1).toHomeomorph plane_rank hAc with h | h | h
    · exact h
    · exact (h₀₁ h).elim
    · exact (h₁₀ h).elim
  have hBdisj : Disjoint (B 0 '' closedBall 0 1) (B 1 '' closedBall 0 1) := by
    rcases (B 0).toHomeomorph.disjoint_or_nested_image_closedBall
      (B 1).toHomeomorph plane_rank hBc with h | h | h
    · exact h
    · exact (h₀₁ ((hnest' 0 1 (by decide)).mpr h)).elim
    · exact (h₁₀ ((hnest' 1 0 (by decide)).mpr h)).elim
  obtain ⟨K, hK, D, hfix, h₀, h₁⟩ :=
    supported_matching_disjoint (A 0) (A 1) (B 0) (B 1) hAdisj hBdisj
  exact finish K hK D hfix h₀ h₁

end Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs
