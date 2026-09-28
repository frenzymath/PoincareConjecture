import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.BallComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.AntipodalBallComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.CountableComplement










noncomputable section
set_option autoImplicit false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Topology

private theorem closed_side_of_region_choices
    {X : Type*} [TopologicalSpace X] {K A B : Set X}
    (hK : IsClosed K) (hregular : closure (interior K) = K)
    (hfront : (frontier K).Nonempty)
    (hcover : A ∪ B = (frontier K)ᶜ)
    (hFA : frontier K ⊆ closure A) (hFB : frontier K ⊆ closure B)
    (hA : A ⊆ interior K ∨ A ⊆ Kᶜ) (hB : B ⊆ interior K ∨ B ⊆ Kᶜ) :
    K = closure A ∨ K = closure B := by
  have hside {P Q : Set X} (hPQ : P ∪ Q = (frontier K)ᶜ)
      (hFP : frontier K ⊆ closure P) (hP : P ⊆ interior K) (hQ : Q ⊆ Kᶜ) :
      K = closure P := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxf : x ∈ frontier K
      · exact hFP hxf
      · rcases hPQ.superset hxf with hp | hq
        · exact subset_closure hp
        · exact (hQ hq hx).elim
    · exact closure_minimal (hP.trans interior_subset) hK
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · have hKuniv : K = univ := by
      apply eq_univ_of_forall
      intro x
      by_cases hxf : x ∈ frontier K
      · exact hK.frontier_subset hxf
      · exact (hcover.superset hxf).elim
          (fun hx => interior_subset (hA hx)) (fun hx => interior_subset (hB hx))
    have : frontier K = ∅ := by rw [hKuniv, frontier_univ]
    exact (not_nonempty_empty (this ▸ hfront)).elim
  · exact Or.inl (hside hcover hFA hA hB)
  · exact Or.inr (hside ((union_comm B A).trans hcover) hFB hB hA)
  · have hi : interior K = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxf : x ∉ frontier K := fun hf => disjoint_left.mp disjoint_interior_frontier hx hf
      exact (hcover.superset hxf).elim
        (fun ha => hA ha (interior_subset hx)) (fun hb => hB hb (interior_subset hx))
    have hKe : K = ∅ := by rw [← hregular, hi, closure_empty]
    have : frontier K = ∅ := by rw [hKe, frontier_empty]
    exact (not_nonempty_empty (this ▸ hfront)).elim

end Poincare.Topology

namespace PoincareConjecture.ProjectiveGluing

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => UnitThreeSphere



theorem isConnected_antipodal_ball_exterior
    (b : OpenPartialHomeomorph E3 S3) (hbs : closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hBB : Disjoint (b '' closedBall 0 1) (Neg.neg '' (b '' closedBall 0 1))) :
    IsConnected (b '' closedBall 0 1 ∪ Neg.neg '' (b '' closedBall 0 1))ᶜ := by
  obtain ⟨_, U, V, _, hU, hV, D, _⟩ :=
    Poincare.exists_diffeomorph_antipodal_ball_complement b hbs hb hbi hBB
  let : SimplyConnectedSpace S3 := Poincare.Topology.standardSphereSimplyConnected 1
  have hcU : IsConnected (U : Set S3) := by
    rw [hU]
    exact Poincare.Topology.Manifold.isConnected_compl_countable (n := 1)
      ((finite_singleton (-(b 0))).insert (b 0)).countable
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hcU
  have hrange : range (fun x : U => (D x : S3)) = (V : Set S3) := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact (D x).property
    · intro y hy
      obtain ⟨x, hx⟩ := D.surjective (⟨y, hy⟩ : V)
      exact ⟨x, congrArg Subtype.val hx⟩
  rw [← hV, ← hrange]
  exact isConnected_range (continuous_subtype_val.comp D.continuous)



theorem eq_antipodal_ball_side_of_frontier
    {L : Set S3} (hL : IsClosed L) (hregular : closure (interior L) = L)
    (hneg : ∀ x : S3, -x ∈ L ↔ x ∈ L)
    (b : OpenPartialHomeomorph E3 S3) (hbs : closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hBB : Disjoint (b '' closedBall 0 1) (Neg.neg '' (b '' closedBall 0 1)))
    (hfront : frontier L = b '' sphere 0 1 ∪ Neg.neg '' (b '' sphere 0 1)) :
    L = b '' closedBall 0 1 ∪ Neg.neg '' (b '' closedBall 0 1) ∨
      L = antipodalBallComplement b := by
  let A := b '' ball 0 1
  let P := A ∪ Neg.neg '' A
  let W := (b '' closedBall 0 1 ∪ Neg.neg '' (b '' closedBall 0 1))ᶜ
  obtain ⟨hD, hiD, hregD, hfD⟩ := antipodalBallComplement_topology b hbs hBB
  have hfrontD : frontier L = frontier (antipodalBallComplement b) := hfront.trans hfD.symm
  have hcover : P ∪ W = (frontier L)ᶜ := by
    rw [hfrontD, hD.isClosed.frontier_eq, hiD]
    ext x
    simp only [P, W, A, antipodalBallComplement, mem_union, mem_compl_iff, mem_sdiff]
    tauto
  have hAo : IsOpen A :=
    b.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hbs)
  have hPo : IsOpen P := hAo.union ((Homeomorph.neg S3).isOpenMap _ hAo)
  have hcA : IsPreconnected A := isPreconnected_ball.image b
    (b.continuousOn.mono (ball_subset_closedBall.trans hbs))
  have hcW : IsPreconnected W :=
    (isConnected_antipodal_ball_exterior b hbs hb hbi hBB).isPreconnected
  have hchoice {R : Set S3} (hcR : IsPreconnected R) (hR : R ⊆ (frontier L)ᶜ) :
      R ⊆ interior L ∨ R ⊆ Lᶜ := by
    apply hcR.subset_or_subset isOpen_interior hL.isOpen_compl
      (disjoint_left.mpr (fun x hx hn => hn (interior_subset hx)))
    intro x hx
    by_cases hxL : x ∈ L
    · left
      by_contra hxi
      exact hR hx (hL.frontier_eq.symm ▸ ⟨hxL, hxi⟩)
    · exact Or.inr hxL
  have hPchoice : P ⊆ interior L ∨ P ⊆ Lᶜ := by
    rcases hchoice hcA (fun _ hx => hcover.subset (Or.inl (Or.inl hx))) with hAi | hAc
    · left
      apply interior_maximal _ hPo
      rintro x (hx | ⟨y, hy, rfl⟩)
      · exact interior_subset (hAi hx)
      · exact (hneg y).mpr (interior_subset (hAi hy))
    · right
      rintro x (hx | ⟨y, hy, rfl⟩) hxL
      · exact hAc hx hxL
      · exact hAc hy ((hneg y).mp hxL)
  have hWchoice := hchoice hcW (fun _ hx => hcover.subset (Or.inr hx))
  have hclW : closure W = antipodalBallComplement b := by
    change closure (b '' closedBall 0 1 ∪ Neg.neg '' (b '' closedBall 0 1))ᶜ = _
    rw [← hiD]
    exact hregD
  have hclA : closure A = b '' closedBall 0 1 := by
    have h := (b.image_region_of_isCompact_closure (D := ball (0 : E3) 1) isOpen_ball
      (by simpa only [closure_ball (0 : E3) (by norm_num : (1 : ℝ) ≠ 0)] using
        isCompact_closedBall (0 : E3) 1)
      (by simpa only [closure_ball (0 : E3) (by norm_num : (1 : ℝ) ≠ 0)] using hbs)).2.2.1
    simpa only [closure_ball (0 : E3) (by norm_num : (1 : ℝ) ≠ 0)] using h
  have hclP : closure P = b '' closedBall 0 1 ∪ Neg.neg '' (b '' closedBall 0 1) := by
    have hncl : Neg.neg '' closure A = closure (Neg.neg '' A) :=
      (Homeomorph.neg S3).image_closure A
    rw [closure_union, ← hncl, hclA]
  have hFne : (frontier L).Nonempty := by
    rw [hfront]
    exact ⟨b (Poincare.Topology.standardSpherePole 0 : UnitTwoSphere),
      Or.inl (mem_image_of_mem b (Poincare.Topology.standardSpherePole 0).property)⟩
  have hFP : frontier L ⊆ closure P := by
    rw [hfrontD, antipodalBallComplement, frontier_compl]
    exact frontier_subset_closure
  have hFW : frontier L ⊆ closure W := by
    rw [hclW, hfrontD]
    exact hD.isClosed.frontier_subset
  rcases Poincare.Topology.closed_side_of_region_choices hL hregular hFne hcover
      hFP hFW hPchoice hWchoice with h | h
  · exact Or.inl (h.trans hclP)
  · exact Or.inr (h.trans hclW)

end PoincareConjecture.ProjectiveGluing
