import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Parameters









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1



theorem exists_anchor_pasting_cover
    {g : S2 → E3} {v : E3} {c t a b a₀ b₀ δ : Real}
    (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real ≃ₘ[Real] Real)
    (hδ : 0 < δ)
    (hsource : ∀ s ∈ Icc (a - δ) (b + δ), (R s, t) ∈ F.source)
    (hheight : ∀ z ∈ F.source, inner Real v (g (F z)) = c + z.2)
    (hmargin : ∀ s ∈ Icc a₀ b₀, R.symm s ∈ Ioo (a - δ) (b + δ))
    (α : S1 → S2)
    (hlevel : ∀ q, inner Real v (g (α q)) = c + t)
    (hcover : range α ⊆ e.target ∪ F '' (Icc a₀ b₀ ×ˢ ({t} : Set Real))) :
    ∃ U V : Set S2, IsOpen U ∧ IsOpen V ∧ U ⊆ e.target ∧ V ⊆ F.target ∧
      range α ⊆ U ∪ V ∧
      (∀ q ∈ V, R.symm (F.symm q).1 ∈ Ioo (a - δ) (b + δ)) ∧
      (∀ q, α q ∈ V → F (R (R.symm (F.symm (α q)).1), t) = α q) ∧
      ∀ q, α q ∈ U ∩ V →
        R.symm (F.symm (α q)).1 ∈
          Ioo (a - δ) (a + δ) ∪ Ioo (b - δ) (b + δ) := by
  let P : Real → S2 := fun s => F (R s, t)
  let K : Set S2 := P '' Icc (a + δ) (b - δ)
  let σ : S2 → Real := fun q => R.symm (F.symm q).1
  let U : Set S2 := e.target \ K
  let V : Set S2 := F.target ∩ σ ⁻¹' Ioo (a - δ) (b + δ)
  have hsmall : Icc (a + δ) (b - δ) ⊆ Icc (a - δ) (b + δ) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hPK : ContinuousOn P (Icc (a + δ) (b - δ)) :=
    F.continuousOn.comp (R.continuous.prodMk continuous_const).continuousOn
      (fun s hs => hsource s (hsmall hs))
  have hK : IsClosed K := (isCompact_Icc.image_of_continuousOn hPK).isClosed
  have hU : IsOpen U := e.open_target.sdiff hK
  have hσ : ContinuousOn σ F.target :=
    R.symm.continuous.comp_continuousOn (continuous_fst.comp_continuousOn F.symm.continuousOn)
  have hV : IsOpen V := hσ.isOpen_inter_preimage F.open_target isOpen_Ioo
  have hPσ (s : Real) (hs : s ∈ Icc (a - δ) (b + δ)) : σ (P s) = s := by
    change R.symm (F.symm (F (R s, t))).1 = s
    rw [F.left_inv (hsource s hs), R.symm_apply_apply]
  have hKV : K ⊆ V := by
    rintro q ⟨s, hs, rfl⟩
    refine ⟨F.map_source (hsource s (hsmall hs)), ?_⟩
    change σ (P s) ∈ Ioo (a - δ) (b + δ)
    rw [hPσ s (hsmall hs)]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hcoordinates (q : S1) (hq : α q ∈ V) : F (R (σ (α q)), t) = α q := by
    have htarg : α q ∈ F.target := hq.1
    have hsrc := F.map_target htarg
    have hsecond : (F.symm (α q)).2 = t := by
      have hh := hheight (F.symm (α q)) hsrc
      rw [F.right_inv htarg, hlevel] at hh
      linarith
    have hpair : (R (σ (α q)), t) = F.symm (α q) := by
      apply Prod.ext
      · exact R.apply_symm_apply _
      · exact hsecond.symm
    rw [hpair, F.right_inv htarg]
  refine ⟨U, V, hU, hV, fun _ hq => hq.1, fun _ hq => hq.1, ?_,
    fun _ hq => hq.2, hcoordinates, ?_⟩
  · rintro q ⟨x, rfl⟩
    rcases hcover ⟨x, rfl⟩ with he | hF
    · by_cases hKq : α x ∈ K
      · exact Or.inr (hKV hKq)
      · exact Or.inl ⟨he, hKq⟩
    · rcases hF with ⟨⟨s, u⟩, ⟨hs, hu⟩, heq⟩
      have hut : u = t := hu
      subst u
      have hsR := hmargin s hs
      have hsrc : (s, t) ∈ F.source := by
        simpa only [R.apply_symm_apply] using hsource (R.symm s) ⟨hsR.1.le, hsR.2.le⟩
      refine Or.inr ⟨heq ▸ F.map_source hsrc, ?_⟩
      change σ (α x) ∈ Ioo (a - δ) (b + δ)
      rw [← heq]
      change R.symm (F.symm (F (s, t))).1 ∈ _
      rw [F.left_inv hsrc]
      exact hsR
  · intro q hq
    have hs : σ (α q) ∈ Ioo (a - δ) (b + δ) := hq.2.2
    have hn : σ (α q) ∉ Icc (a + δ) (b - δ) := by
      intro hmid
      exact hq.1.2 ⟨σ (α q), hmid, hcoordinates q hq.2⟩
    by_cases hlo : σ (α q) < a + δ
    · exact Or.inl ⟨hs.1, hlo⟩
    · exact Or.inr ⟨lt_of_not_ge (fun hhi => hn ⟨le_of_not_gt hlo, hhi⟩), hs.2⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
