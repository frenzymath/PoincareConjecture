import PoincareConjecture.Proofs.M76.Mathlib.SmallHeightPerturbation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem FinitePiecewiseAffineOn.heightChange {g : E × ℝ → ℝ} {S : Set (E × ℝ)}
    (hg : FinitePiecewiseAffineOn g S) (ε : ℝ) :
    FinitePiecewiseAffineOn (fun p : E × ℝ => (p.1, p.2 + ε * g p)) S := by
  obtain ⟨K, hK, hspace, hfaces⟩ := hg
  refine ⟨K, hK, hspace, fun s hs => ?_⟩
  obtain ⟨a, ha⟩ := hfaces s hs
  refine ⟨(ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
    ((ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap + ε • a), ?_⟩
  intro p hp
  change (p.1, p.2 + ε * g p) = (p.1, p.2 + ε * a p)
  rw [ha hp]

theorem FinitePiecewiseAffineOn.exists_heightBand_homeomorph
    {g : E × ℝ → ℝ} {B : Set E} {α β : ℝ} (hαβ : α ≤ β)
    (hg : FinitePiecewiseAffineOn g (B ×ˢ Icc α β)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ →
      ∃ H : (B ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ
        {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (α + ε * g (p.1, α)) (β + ε * g (p.1, β))},
        H.IsFinitePL ∧ ∀ p, (H p : E × ℝ) = ((p : E × ℝ).1, (p : E × ℝ).2 + ε * g p) := by
  obtain ⟨δ, hδ, hmono⟩ := hg.exists_strictMonoOn_vertical_perturbation
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  let f : E × ℝ → E × ℝ := fun p => (p.1, p.2 + ε * g p)
  have hinj : InjOn f (B ×ˢ Icc α β) := by
    rintro ⟨x, u⟩ hp ⟨y, v⟩ hq heq
    have hxy : x = y := congrArg Prod.fst heq
    subst y
    exact Prod.ext rfl ((hmono ε hε x hp.1).injOn hp.2 hq.2 (congrArg Prod.snd heq))
  have himage : f '' (B ×ˢ Icc α β) =
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (α + ε * g (p.1, α)) (β + ε * g (p.1, β))} := by
    ext p
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      refine ⟨hx, ?_, ?_⟩
      · exact (hmono ε hε x hx).monotoneOn ⟨le_rfl, hαβ⟩ ht ht.1
      · exact (hmono ε hε x hx).monotoneOn ht ⟨hαβ, le_rfl⟩ ht.2
    · rintro ⟨hx, ht⟩
      have hgc : ContinuousOn (fun t => g (p.1, t)) (Icc α β) :=
        hg.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => ⟨hx, ht⟩)
      have hc : ContinuousOn (fun t => t + ε * g (p.1, t)) (Icc α β) :=
        continuousOn_id.add (continuousOn_const.mul hgc)
      obtain ⟨t, htd, htv⟩ := intermediate_value_Icc hαβ hc ht
      exact ⟨(p.1, t), ⟨hx, htd⟩, Prod.ext rfl htv⟩
  obtain ⟨G, hG, hGval⟩ := (hg.heightChange ε).exists_homeomorph_image hinj
  let H := (Homeomorph.setCongr (rfl : B ×ˢ Icc α β = B ×ˢ Icc α β)).trans
    (G.trans (Homeomorph.setCongr himage))
  exact ⟨H, hG.setCongr rfl himage, fun p => hGval p⟩

end Geometry
