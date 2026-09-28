import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.JetBounds










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35

variable {ι E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



def HasUniformJetBoundsAt (n : ℕ) (f : ι → E → F) (p : ι → E) : Prop :=
  ∀ m ≤ n, ∃ C : ℝ, ∀ i, ‖iteratedFDeriv ℝ m (f i) (p i)‖ ≤ C

theorem HasUniformJetBoundsAt.mono_order {m n : ℕ} {f : ι → E → F} {p : ι → E}
    (h : HasUniformJetBoundsAt n f p) (hmn : m ≤ n) : HasUniformJetBoundsAt m f p :=
  fun _ hj => h _ (hj.trans hmn)

theorem HasUniformJetBoundsAt.bound_all {n : ℕ} {f : ι → E → F} {p : ι → E}
    (h : HasUniformJetBoundsAt n f p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ≤ n, ∀ i, ‖iteratedFDeriv ℝ m (f i) (p i)‖ ≤ C := by
  classical
  choose c hc using fun j : Fin (n + 1) => h j.1 (by omega)
  let C := ∑ j, max (c j) 0
  refine ⟨C, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro m hm i
  let j : Fin (n + 1) := ⟨m, by omega⟩
  exact (hc j i).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ j)))

theorem HasUniformJetBoundsAt.congr {n : ℕ} {f g : ι → E → F} {p : ι → E}
    (h : HasUniformJetBoundsAt n f p) (heq : ∀ i, f i =ᶠ[𝓝 (p i)] g i) :
    HasUniformJetBoundsAt n g p := by
  intro m hm
  obtain ⟨C, hC⟩ := h m hm
  refine ⟨C, fun i => ?_⟩
  rw [← ((heq i).iteratedFDeriv ℝ m).eq_of_nhds]
  exact hC i

theorem HasUniformJetBoundsAt.prodMk {n : ℕ} {f : ι → E → F} {g : ι → E → G}
    {p : ι → E} (hf : HasUniformJetBoundsAt n f p) (hg : HasUniformJetBoundsAt n g p)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i)) (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (p i)) :
    HasUniformJetBoundsAt n (fun i x => (f i x, g i x)) p := by
  intro m hm
  obtain ⟨Cf, hCf⟩ := hf m hm
  obtain ⟨Cg, hCg⟩ := hg m hm
  refine ⟨max Cf Cg, fun i => ?_⟩
  rw [iteratedFDeriv_prodMk (hcf i) (hcg i)
    (by exact_mod_cast le_top (a := (m : ℕ∞))), ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max (hCf i) (hCg i)

theorem HasUniformJetBoundsAt.sub {n : ℕ} {f g : ι → E → F} {p : ι → E}
    (hf : HasUniformJetBoundsAt n f p) (hg : HasUniformJetBoundsAt n g p)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i)) (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (p i)) :
    HasUniformJetBoundsAt n (fun i x => f i x - g i x) p := by
  intro m hm
  obtain ⟨Cf, hCf⟩ := hf m hm
  obtain ⟨Cg, hCg⟩ := hg m hm
  refine ⟨Cf + Cg, fun i => ?_⟩
  have hr : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (m : ℕ∞))
  rw [fun_iteratedFDeriv_sub_apply ((hcf i).of_le hr) ((hcg i).of_le hr)]
  exact (norm_sub_le _ _).trans (add_le_add (hCf i) (hCg i))

theorem HasUniformJetBoundsAt.clm {n : ℕ} {f : ι → E → F} {p : ι → E}
    (hf : HasUniformJetBoundsAt n f p) (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i))
    (L : F →L[ℝ] G) : HasUniformJetBoundsAt n (fun i x => L (f i x)) p := by
  intro m hm
  obtain ⟨C, hC⟩ := hf m hm
  refine ⟨‖L‖ * C, fun i => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (hcf i)
    (by exact_mod_cast le_top (a := (m : ℕ∞)))).trans
      (mul_le_mul_of_nonneg_left (hC i) (norm_nonneg L))

private theorem local_bilinear_jet_bound (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} {p : E} (r : ℕ)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ‖iteratedFDeriv ℝ r (fun y => B (f y) (g y)) p‖ ≤
      ‖B‖ * ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f p‖ * ‖iteratedFDeriv ℝ (r - j) g p‖ := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  obtain ⟨Sf, hSf, hfs⟩ := hf.contDiffOn (m := r) hr (by simp)
  obtain ⟨Sg, hSg, hgs⟩ := hg.contDiffOn (m := r) hr (by simp)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp (inter_mem hSf hSg)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (hUsub.trans inter_subset_left))
    (hgs.mono (hUsub.trans inter_subset_right)) hU.uniqueDiffOn hpU (le_refl (r : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hpU] using h

theorem HasUniformJetBoundsAt.bilinear {n : ℕ} {f : ι → E → F} {g : ι → E → G}
    {p : ι → E} (hf : HasUniformJetBoundsAt n f p) (hg : HasUniformJetBoundsAt n g p)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i)) (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (p i))
    (B : F →L[ℝ] G →L[ℝ] H) :
    HasUniformJetBoundsAt n (fun i x => B (f i x) (g i x)) p := by
  obtain ⟨Cf, hCf, hfbound⟩ := hf.bound_all
  obtain ⟨Cg, hCg, hgbound⟩ := hg.bound_all
  intro m hm
  refine ⟨‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * Cf * Cg, fun i => ?_⟩
  apply (local_bilinear_jet_bound B m (hcf i) (hcg i)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hfbound j (hjm.trans hm) i)
    (Nat.cast_nonneg _)) (hgbound (m - j) ((Nat.sub_le _ _).trans hm) i)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hCf)

theorem HasUniformJetBoundsAt.clm_comp {n : ℕ}
    {f : ι → E → G →L[ℝ] H} {g : ι → E → F →L[ℝ] G} {p : ι → E}
    (hf : HasUniformJetBoundsAt n f p) (hg : HasUniformJetBoundsAt n g p)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i)) (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (p i)) :
    HasUniformJetBoundsAt n (fun i x => (f i x).comp (g i x)) p :=
  hf.bilinear hg hcf hcg (ContinuousLinearMap.compL ℝ F G H)

theorem HasUniformJetBoundsAt.comp {n : ℕ} {f : ι → E → F} {g : ι → F → G}
    {p : ι → E} (hf : HasUniformJetBoundsAt n f p)
    (hg : HasUniformJetBoundsAt n g (fun i => f i (p i)))
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i))
    (hcg : ∀ i, ContDiffAt ℝ ∞ (g i) (f i (p i))) :
    HasUniformJetBoundsAt n (fun i => g i ∘ f i) p := by
  obtain ⟨Cf, _, hfbound⟩ := hf.bound_all
  obtain ⟨Cg, _, hgbound⟩ := hg.bound_all
  intro m hm
  refine ⟨Nat.factorial m * Cg * (max Cf 1) ^ m, fun i => ?_⟩
  have hr : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (m : ℕ∞))
  apply CoordinateTransition.norm_iteratedFDeriv_comp_le_of_contDiffAt
    ((hcg i).of_le hr) ((hcf i).of_le hr)
    (fun j hj => hgbound j (hj.trans hm) i)
  intro j hj hjm
  exact (hfbound j (hjm.trans hm) i).trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right _ _) (Nat.ne_of_gt hj)))

theorem HasUniformJetBoundsAt.comp_fixed {n : ℕ} {f : ι → E → F} {p : ι → E}
    {g : F → G} {K : Set F} (hf : HasUniformJetBoundsAt n f p)
    (hcf : ∀ i, ContDiffAt ℝ ∞ (f i) (p i)) (hK : IsCompact K)
    (hcg : ∀ y ∈ K, ContDiffAt ℝ ∞ g y) (hmap : ∀ i, f i (p i) ∈ K) :
    HasUniformJetBoundsAt n (fun i => g ∘ f i) p := by
  have hg : HasUniformJetBoundsAt n (fun _ : ι => g) (fun i => f i (p i)) := by
    intro m _
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (fun y hy =>
      ((hcg y hy).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top (a := (m : ℕ∞)))).continuousWithinAt)
    exact ⟨C, fun i => hC (f i (p i)) (hmap i)⟩
  exact hf.comp hg hcf (fun i => hcg _ (hmap i))

theorem HasUniformJetBoundsAt.fderiv {n : ℕ} {f : ι → E → F} {p : ι → E}
    (h : HasUniformJetBoundsAt (n + 1) f p) :
    HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) p := by
  intro m hm
  obtain ⟨C, hC⟩ := h (m + 1) (by omega)
  exact ⟨C, fun i => by rw [norm_iteratedFDeriv_fderiv]; exact hC i⟩

theorem HasUniformJetBoundsAt.succ_of_fderiv {n : ℕ} {f : ι → E → F} {p : ι → E}
    (hzero : ∃ C : ℝ, ∀ i, ‖f i (p i)‖ ≤ C)
    (h : HasUniformJetBoundsAt n (fun i => _root_.fderiv ℝ (f i)) p) :
    HasUniformJetBoundsAt (n + 1) f p := by
  intro m hm
  cases m with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hzero
  | succ m =>
    obtain ⟨C, hC⟩ := h m (by omega)
    exact ⟨C, fun i => by rw [← norm_iteratedFDeriv_fderiv]; exact hC i⟩

end PoincareConjecture.M35
