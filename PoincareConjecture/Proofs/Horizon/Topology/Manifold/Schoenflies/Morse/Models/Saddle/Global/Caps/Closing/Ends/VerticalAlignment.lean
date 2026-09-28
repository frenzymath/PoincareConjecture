import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.AffineMotion



noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]



theorem exists_supported_vertical_cap_alignment
    {C : Set (E × Real)} (hC : IsCompact C) {Q : Set E} (hQ : IsCompact Q)
    {a d b k : Real} (hab : a < b) (hdb : d < b) (hk : 0 < k)
    (hbelow : ∀ p ∈ C, p.2 ≤ a) :
    ∃ c : Real, max a d < c ∧ c < b ∧
      ∃ S : Set (E × Real), IsCompact S ∧ S ⊆ {p | p.2 < c} ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p ∉ S, F p = p) ∧
        (∀ p, c ≤ p.2 → F p = p) ∧
        (∀ p, (F p).1 = p.1) ∧
        F '' (C ∪ Q ×ˢ Icc a b) =
          (fun p : E × Real => (p.1, d + k * (p.2 - a))) '' C ∪ Q ×ˢ Icc d b := by
  let c := (max a d + b) / 2
  have hmax : max a d < b := max_lt hab hdb
  have hmc : max a d < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  let K := C ∪ Q ×ˢ ({a} : Set Real)
  have hK : IsCompact K := hC.union (hQ.prod isCompact_singleton)
  have hKa (p : E × Real) (hp : p ∈ K) : p.2 ≤ a := by
    rcases hp with hp | hp
    · exact hbelow p hp
    · exact (mem_singleton_iff.mp hp.2).le
  have htrace (p : E × Real) (hp : p ∈ K) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      (p.1, (1 - t) * p.2 + t * ((d - k * a) + k * p.2)) ∈
        {p : E × Real | p.2 < c} := by
    have hpa := hKa p hp
    have hpd : d - k * a + k * p.2 ≤ d := by nlinarith
    have hpm : p.2 ≤ max a d := hpa.trans (le_max_left _ _)
    have hdm : d - k * a + k * p.2 ≤ max a d := hpd.trans (le_max_right _ _)
    have hh := add_le_add (mul_le_mul_of_nonneg_left hpm (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hdm ht.1)
    change (1 - t) * p.2 + t * ((d - k * a) + k * p.2) < c
    nlinarith
  obtain ⟨S, hS, hSc, F, hfix, hfirst, haffine, hmono⟩ :=
    Reverse.exists_vertical_affine_motion_within hK
      (isOpen_lt continuous_snd continuous_const) (d - k * a) k hk htrace
  have hfixed (p : E × Real) (hp : c ≤ p.2) : F p = p :=
    hfix p (fun hpS => (not_lt_of_ge hp) (hSc hpS))
  have hbottom (x : E) (hx : x ∈ Q) : F (x, a) = (x, d) := by
    simpa only [mul_add, sub_add_cancel] using haffine (x, a) (Or.inr ⟨hx, rfl⟩)
  have htop (x : E) : F (x, b) = (x, b) := hfixed (x, b) hcb.le
  have hcylinder : F '' (Q ×ˢ Icc a b) = Q ×ˢ Icc d b := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      refine ⟨(hfirst (x, t)).symm ▸ hx, ?_, ?_⟩
      · simpa only [hbottom x hx] using (hmono x).monotone ht.1
      · simpa only [htop x] using (hmono x).monotone ht.2
    · rintro ⟨x, z⟩ ⟨hx, hz⟩
      have hc : Continuous (fun t : Real => (F (x, t)).2) := by fun_prop
      have hz' : z ∈ Icc (F (x, a)).2 (F (x, b)).2 := by
        simpa only [hbottom x hx, htop x] using hz
      obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hab.le hc.continuousOn hz'
      exact ⟨(x, t), ⟨hx, ht⟩, Prod.ext (hfirst (x, t)) heq⟩
  refine ⟨c, hmc, hcb, S, hS, hSc, F, hfix, hfixed, hfirst, ?_⟩
  rw [image_union, hcylinder]
  congr 1
  apply image_congr
  intro p hp
  rw [haffine p (Or.inl hp)]
  congr 1
  ring

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
