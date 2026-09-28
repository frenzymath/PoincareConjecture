import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_PointJetBounds










set_option autoImplicit false

open Set Filter Asymptotics
open scoped ContDiff Topology

namespace PoincareConjecture.M45

variable {ι E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



def PointJetsVanish (f : ι → E → F) (x : ι → E) (l : Filter ι) : Prop :=
  ∀ m : ℕ, Tendsto (fun i => iteratedFDeriv ℝ m (f i) (x i)) l (𝓝 0)



theorem zero_taylorComp (q : FormalMultilinearSeries ℝ E F) (m : ℕ) :
    (0 : FormalMultilinearSeries ℝ F G).taylorComp q m = 0 := by
  classical
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext v
  simp [FormalMultilinearSeries.compAlongOrderedFinpartition]

namespace PointJetsVanish

variable {l : Filter ι} {x : ι → E}




theorem comp {f : ι → E → F} {g : ι → F → G}
    (hg : PointJetsVanish g (fun i => f i (x i)) l)
    (hf : ∀ m, FinitePointJetBounded m f x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (f i (x i))) :
    PointJetsVanish (fun i => g i ∘ f i) x l := by
  intro m
  let p := fun i => ftaylorSeries ℝ (g i) (f i (x i))
  let q := fun i => ftaylorSeries ℝ (f i) (x i)
  have hp (k : ℕ) : (fun i => p i k) =o[l] (fun _ : ι => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (hg k)
  have h := FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO
    (p₁ := p) (p₂ := fun _ => (0 : FormalMultilinearSeries ℝ F G)) (q₁ := q) (q₂ := q)
    (f := fun _ : ι => (1 : ℝ))
    (fun k _ => (hg k).norm.isBoundedUnder_le)
    (fun k _ => by
      change (fun i => p i k - (0 : F [×k]→L[ℝ] G)) =o[l] (fun _ : ι => (1 : ℝ))
      simpa only [sub_zero] using hp k)
    (fun k hk => hf m k hk) (fun k hk => hf m k hk)
    (fun k _ => by simp only [sub_self]; exact isLittleO_zero _ _)
  have ht := (isLittleO_one_iff ℝ).mp h
  simpa only [zero_taylorComp, sub_zero, p, q,
    iteratedFDeriv_comp (hgs _) (hfs _) (by exact_mod_cast le_top)] using ht

end PointJetsVanish




theorem norm_iteratedFDeriv_bilinear_germ
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (m - j) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h

namespace PointJetsVanish



theorem bilinear {l : Filter ι} {x : ι → E} {f : ι → E → F} {g : ι → E → G}
    (hf : PointJetsVanish f x l) (hg : ∀ m, FinitePointJetBounded m g x l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (x i)) (B : F →L[ℝ] G →L[ℝ] H) :
    PointJetsVanish (fun i y => B (f i y) (g i y)) x l := by
  intro m
  have hterm (j : ℕ) : Tendsto (fun i => (m.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (f i) (x i)‖ * ‖iteratedFDeriv ℝ (m - j) (g i) (x i)‖) l (𝓝 0) := by
    have hf0 : Tendsto (fun i => ‖iteratedFDeriv ℝ j (f i) (x i)‖) l (𝓝 0) := by
      simpa only [norm_zero] using (hf j).norm
    have hb : l.IsBoundedUnder (· ≤ ·)
        (fun i => ‖‖iteratedFDeriv ℝ (m - j) (g i) (x i)‖‖) := by
      simpa only [norm_norm] using hg m (m - j) (Nat.sub_le _ _)
    have hm := hf0.zero_mul_isBoundedUnder_le hb
    simpa only [mul_zero, mul_assoc] using hm.const_mul (m.choose j : ℝ)
  have hsum := (tendsto_finsetSum (s := Finset.range (m + 1))
    (fun j _ => hterm j)).const_mul ‖B‖
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_iteratedFDeriv_bilinear_germ B (hfs i) (hgs i) m)
  simpa only [Finset.sum_const_zero, mul_zero] using hsum

end PointJetsVanish

end PoincareConjecture.M45
