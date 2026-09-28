import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLSphereDiskComplement
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_sphere_model_of_two_foot_ball
    {S₀ S₁ H T d₀ q₀ d₁ q₁ : Set E}
    (e₀ : S₀ ≃ₜ frontier (halfBall 1)) (he₀ : e₀.IsFinitePL)
    (e₁ : S₁ ≃ₜ frontier (halfBall 1)) (he₁ : e₁.IsFinitePL)
    (hH : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) H T)
    (hd₀ : IsFinitePLBallPair (ℝ × ℝ) d₀ q₀)
    (hd₁ : IsFinitePLBallPair (ℝ × ℝ) d₁ q₁)
    (hcontact₀ : H ∩ S₀ = d₀) (hcontact₁ : H ∩ S₁ = d₁)
    (hfoot₀ : d₀ ⊆ T) (hfoot₁ : d₁ ⊆ T)
    (hdisj : Disjoint S₀ S₁)
    (hout₀ : (S₀ \ d₀).Nonempty) (hout₁ : (S₁ \ d₁).Nonempty) :
    ∃ G : (((S₀ \ (d₀ \ q₀)) ∪ (S₁ \ (d₁ \ q₁))) ∪
      (T \ ((d₀ \ q₀) ∪ (d₁ \ q₁))) : Set E) ≃ₜ frontier (halfBall 1),
      G.IsFinitePL := by
  have hC : IsCompact (halfBall 1) := isCompact_halfBall (Or.inl rfl)
  have hcv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  have hne := interior_halfBall_nonempty (h := 1) (Or.inl rfl)
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  have hd₀S : d₀ ⊆ S₀ := fun _ hx => (hcontact₀.symm.subset hx).2
  have hd₁S : d₁ ⊆ S₁ := fun _ hx => (hcontact₁.symm.subset hx).2
  have hfeet : Disjoint d₀ d₁ := hdisj.mono hd₀S hd₁S
  have hT₀ : T ∩ S₀ = d₀ := by
    apply Subset.antisymm
    · exact fun _ hx => hcontact₀.subset ⟨hH.1 hx.1, hx.2⟩
    · exact fun _ hx => ⟨hfoot₀ hx, hd₀S hx⟩
  have hT₁ : T ∩ S₁ = d₁ := by
    apply Subset.antisymm
    · exact fun _ hx => hcontact₁.subset ⟨hH.1 hx.1, hx.2⟩
    · exact fun _ hx => ⟨hfoot₁ hx, hd₁S hx⟩
  let A₀ := S₀ \ (d₀ \ q₀)
  let A₁ := S₁ \ (d₁ \ q₁)
  let B₀ := T \ (d₀ \ q₀)
  have hA₀ : IsFinitePLBallPair (ℝ × ℝ) A₀ q₀ :=
    he₀.sphere_disk_complement hC hcv hne hdim hd₀ hd₀S hout₀
  have hA₁ : IsFinitePLBallPair (ℝ × ℝ) A₁ q₁ :=
    he₁.sphere_disk_complement hC hcv hne hdim hd₁ hd₁S hout₁
  have hTout : (T \ d₀).Nonempty := by
    obtain ⟨x, hx, _⟩ := hd₁.sdiff_nonempty
    exact ⟨x, hfoot₁ hx, fun h => disjoint_left.mp hfeet h hx⟩
  have hB₀ : IsFinitePLBallPair (ℝ × ℝ) B₀ q₀ :=
    hH.boundary_disk_complement hdim hd₀ hfoot₀ hTout
  have hinter₀ : A₀ ∩ B₀ = q₀ := by
    apply Subset.antisymm
    · intro x hx
      have hxd : x ∈ d₀ := hT₀.subset ⟨hx.2.1, hx.1.1⟩
      by_contra hxq
      exact hx.1.2 ⟨hxd, hxq⟩
    · exact fun _ hx => ⟨hA₀.1 hx, hB₀.1 hx⟩
  obtain ⟨eP, heP, _, _⟩ := hA₀.exists_sphere_model_of_disk_union hB₀ hinter₀
  let P := A₀ ∪ B₀
  have hd₁P : d₁ ⊆ P := by
    intro x hx
    exact Or.inr ⟨hfoot₁ hx, fun h => disjoint_left.mp hfeet h.1 hx⟩
  have hPout : (P \ d₁).Nonempty := by
    obtain ⟨x, hxS, hxd⟩ := hout₀
    refine ⟨x, Or.inl ⟨hxS, fun h => hxd h.1⟩, ?_⟩
    exact fun hx => disjoint_left.mp hdisj hxS (hd₁S hx)
  let D := P \ (d₁ \ q₁)
  have hD : IsFinitePLBallPair (ℝ × ℝ) D q₁ :=
    heP.sphere_disk_complement hC hcv hne hdim hd₁ hd₁P hPout
  have hP₁ : P ∩ S₁ = d₁ := by
    apply Subset.antisymm
    · rintro x ⟨hx | hx, hxS⟩
      · exact False.elim (disjoint_left.mp hdisj hx.1 hxS)
      · exact hT₁.subset ⟨hx.1, hxS⟩
    · exact fun _ hx => ⟨hd₁P hx, hd₁S hx⟩
  have hinter₁ : D ∩ A₁ = q₁ := by
    apply Subset.antisymm
    · intro x hx
      have hxd : x ∈ d₁ := hP₁.subset ⟨hx.1.1, hx.2.1⟩
      by_contra hxq
      exact hx.1.2 ⟨hxd, hxq⟩
    · exact fun _ hx => ⟨hD.1 hx, hA₁.1 hx⟩
  obtain ⟨G, hG, _, _⟩ := hD.exists_sphere_model_of_disk_union hA₁ hinter₁
  have hcarrier : D ∪ A₁ =
      (A₀ ∪ A₁) ∪ (T \ ((d₀ \ q₀) ∪ (d₁ \ q₁))) := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · rcases hx.1 with hA | hB
        · exact Or.inl (Or.inl hA)
        · exact Or.inr ⟨hB.1, fun h => h.elim hB.2 hx.2⟩
      · exact Or.inl (Or.inr hx)
    · rintro x ((hx | hx) | hx)
      · refine Or.inl ⟨Or.inl hx, ?_⟩
        exact fun h => disjoint_left.mp hdisj hx.1 (hd₁S h.1)
      · exact Or.inr hx
      · exact Or.inl ⟨Or.inr ⟨hx.1, fun h => hx.2 (Or.inl h)⟩,
          fun h => hx.2 (Or.inr h)⟩
  exact ⟨(Homeomorph.setCongr hcarrier.symm).trans G, hG.setCongr hcarrier rfl⟩

end Set
