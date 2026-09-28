import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding












open Set TopologicalSpace Filter Topology
open scoped ContDiff Manifold

namespace Poincare

variable {E F H K S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace K M]




theorem exists_pasted_cylinder
    (A B : Opens M)
    (f : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) J (S × ℝ) A ∞)
    (g : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) J (S × ℝ) B ∞)
    (r : ℝ) (hr : 0 < r)
    (hagree : ∀ p : S × ℝ, |p.2| < r → (f p : M) = g p)
    (hsep : ∀ p q : S × ℝ, p.2 ≤ 0 → 0 < q.2 → (f p : M) ≠ g q) :
    ∃ (W : Opens M)
      (D : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) J (S × ℝ) W ∞),
      (∀ p : S × ℝ,
        (D p : M) = if p.2 ≤ 0 then (f p : M) else (g p : M)) ∧
      (W : Set M) = (fun p => (f p : M)) '' {p | p.2 ≤ 0} ∪
        (fun p => (g p : M)) '' {p | 0 < p.2} := by
  classical
  let P : S × ℝ → M := fun p => if p.2 ≤ 0 then (f p : M) else (g p : M)
  have hloc (p : S × ℝ) :
      (P =ᶠ[𝓝 p] fun q => (f q : M)) ∨
      (P =ᶠ[𝓝 p] fun q => (g q : M)) := by
    by_cases hp : p.2 < r
    · left
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hp] with q hq
      dsimp [P]
      split_ifs with hn
      · rfl
      · exact (hagree q (by rw [abs_of_pos (lt_of_not_ge hn)]; exact hq)).symm
    · right
      have hp0 : 0 < p.2 := hr.trans_le (le_of_not_gt hp)
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp0] with q hq
      exact if_neg (not_le_of_gt hq)
  have hinj : Function.Injective P := by
    intro p q hpq
    by_cases hp : p.2 ≤ 0 <;> by_cases hq : q.2 ≤ 0
    · apply f.injective
      apply Subtype.ext
      change (f p : M) = f q
      simpa only [P, if_pos hp, if_pos hq] using hpq
    · exact False.elim (hsep p q hp (lt_of_not_ge hq)
        (by simpa only [P, if_pos hp, if_neg hq] using hpq))
    · exact False.elim (hsep q p hq (lt_of_not_ge hp)
        (by simpa only [P, if_neg hp, if_pos hq] using hpq.symm))
    · apply g.injective
      apply Subtype.ext
      change (g p : M) = g q
      simpa only [P, if_neg hp, if_neg hq] using hpq
  have hlocal : IsLocalDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J ∞ P := by
    intro p
    rcases hloc p with h | h
    · exact ((f.isLocalDiffeomorph p).comp J M
        (isLocalDiffeomorph_opensSubtypeVal J A (f p))).congr_of_eventuallyEq h
    · exact ((g.isLocalDiffeomorph p).comp J M
        (isLocalDiffeomorph_opensSubtypeVal J B (g p))).congr_of_eventuallyEq h
  let W : Opens M := ⟨range P, hlocal.isOpen_range⟩
  let G : S × ℝ → W := fun p => ⟨P p, ⟨p, rfl⟩⟩
  have hG : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ G := by
    rw [← ContMDiff.subtypeVal_comp_iff W]
    exact hlocal.contMDiff
  have hbij : Function.Bijective G :=
    ⟨fun p q hpq => hinj (congrArg Subtype.val hpq), by
      rintro ⟨x, p, rfl⟩
      exact ⟨p, rfl⟩⟩
  let e := Equiv.ofBijective G hbij
  have hinverse : ContMDiff J (I.prod 𝓘(ℝ, ℝ)) ∞ e.symm := by
    intro y
    let x := e.symm y
    have hx : P x = (y : M) := congrArg Subtype.val (e.apply_symm_apply y)
    let L := hlocal x
    have hL : ContMDiffAt J (I.prod 𝓘(ℝ, ℝ)) ∞ L.localInverse (y : M) := by
      rw [← hx]
      exact L.localInverse_contMDiffAt
    have heq : (fun z : W => e.symm z) =ᶠ[𝓝 y]
        (fun z => L.localInverse (z : M)) := by
      have hn := continuous_subtype_val.continuousAt.eventually
        (L.localInverse.open_source.mem_nhds
          (by rw [← hx]; exact L.localInverse_mem_source))
      filter_upwards [hn] with z hz
      apply hinj
      rw [L.localInverse_right_inv hz]
      exact congrArg Subtype.val (e.apply_symm_apply z)
    exact (hL.comp y contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq heq
  let D : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) J (S × ℝ) W ∞ :=
    { e with contMDiff_toFun := hG, contMDiff_invFun := hinverse }
  refine ⟨W, D, fun _ => rfl, ?_⟩
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : p.2 ≤ 0
    · exact Or.inl ⟨p, hp, (if_pos hp).symm⟩
    · exact Or.inr ⟨p, lt_of_not_ge hp, (if_neg hp).symm⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, if_pos hp⟩
    · exact ⟨p, if_neg (not_le_of_gt hp)⟩

end Poincare
