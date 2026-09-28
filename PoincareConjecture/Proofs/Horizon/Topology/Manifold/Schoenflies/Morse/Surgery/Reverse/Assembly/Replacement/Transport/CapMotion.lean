import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.AffineMotion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.AffineSetImage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NormedAddCommGroup V] [NormedSpace Real V]

theorem exists_cap_affine_stretch_in_coordinates
    (H : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, V) (E × Real) V ∞)
    (C : Set (E × Real)) (hC : IsCompact C) (Q : Set E)
    {b d k : Real} (hb : 0 < b) (hd : 0 ≤ d) (hk : 0 < k)
    (hbelow : ∀ p ∈ C, 0 ≤ p.2)
    (hbelt : ∀ x z, z ∈ Icc 0 b → ((x, z) ∈ C ↔ x ∈ Q))
    (P : Set V) (hP : IsClosed P)
    (havoid : ∀ p ∈ C, b ≤ p.2 → ∀ t ∈ Icc (0 : Real) 1,
      H (p.1, (1 - t) * p.2 + t * (d + k * p.2)) ∉ P) :
    ∃ J : Set V, IsCompact J ∧ Disjoint J P ∧
      ∃ F : Diffeomorph 𝓘(Real, V) 𝓘(Real, V) V V ∞,
        (∀ y ∉ J, F y = y) ∧ (∀ y ∈ P, F y = y) ∧
        F '' (H '' C) = H '' ((fun p : E × Real => (p.1, d + k * p.2)) '' C) ∪
          H '' (Q ×ˢ Icc 0 d) := by
  let K := C ∩ {p : E × Real | b ≤ p.2}
  let O := (H ⁻¹' P)ᶜ ∩ {p : E × Real | 0 < p.2}
  have hK : IsCompact K := hC.inter_right (isClosed_le continuous_const continuous_snd)
  have hO : IsOpen O := (hP.preimage H.continuous).isOpen_compl.inter
    (isOpen_lt continuous_const continuous_snd)
  have htrace : ∀ p ∈ K, ∀ t ∈ Icc (0 : Real) 1,
      (p.1, (1 - t) * p.2 + t * (d + k * p.2)) ∈ O := by
    intro p hp t ht
    refine ⟨havoid p hp.1 hp.2 t ht, ?_⟩
    have hp0 : 0 < p.2 := hb.trans_le hp.2
    have hp1 : 0 < d + k * p.2 := add_pos_of_nonneg_of_pos hd (mul_pos hk hp0)
    change 0 < (1 - t) * p.2 + t * (d + k * p.2)
    by_cases ht0 : t = 0
    · simpa only [ht0, sub_zero, one_mul, zero_mul, add_zero] using hp0
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) hp0.le) (mul_pos htp hp1)
  obtain ⟨J, hJ, hJO, G, hGfix, hGfirst, hGcore, hGmono⟩ :=
    exists_vertical_affine_motion_within hK hO d k hk htrace
  have hGcap := image_cap_eq_affine_union_cylinder C Q (a := 0) hb.le hd hk
    hbelow hbelt G G.continuous hGfirst (fun x => (hGmono x).monotone)
    (fun x _ => hGfix (x, 0) (fun hx => lt_irrefl (0 : Real) (hJO hx).2))
    (fun p hp hh => by simpa only [sub_zero] using hGcore p ⟨hp, hh⟩)
  let F := (H.symm.trans G).trans H
  have hFfix (y : V) (hy : y ∉ H '' J) : F y = y := by
    have hn : H.symm y ∉ J := fun hz => hy ⟨H.symm y, hz, H.apply_symm_apply y⟩
    change H (G (H.symm y)) = y
    rw [hGfix _ hn, H.apply_symm_apply]
  have hdisj : Disjoint (H '' J) P := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, rfl⟩ hy
    exact (hJO hp).1 hy
  refine ⟨H '' J, hJ.image H.continuous, hdisj, F, hFfix,
    fun y hy => hFfix y (fun hj => disjoint_left.mp hdisj hj hy), ?_⟩
  have hcomp : (F : V -> V) ∘ H = H ∘ G := by
    funext p
    change H (G (H.symm (H p))) = H (G p)
    rw [H.symm_apply_apply]
  rw [← image_comp, hcomp, image_comp, hGcap, image_union]
  simp only [sub_zero]

end Poincare.Manifold.Schoenflies.Reverse
