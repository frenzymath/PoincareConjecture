import PoincareConjecture.Proofs.M35.Mathlib.FiniteJetComposition
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem tendsto_iteratedFDeriv_smooth_comp_of_jets
    {fseq : ℕ → E → F} {f : E → F} {phi : F → G}
    {pseq : ℕ → E} {p : E} (r : ℕ)
    (hf : ContDiffAt ℝ ∞ f p) (hs : ∀ k, ContDiffAt ℝ ∞ (fseq k) (pseq k))
    (hphi : ContDiffAt ℝ ∞ phi (f p))
    (hphis : ∀ k, ContDiffAt ℝ ∞ phi (fseq k (pseq k)))
    (hjet : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (fseq k) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m f p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (phi ∘ fseq k) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (phi ∘ f) p)) := by
  have hval : Tendsto (fun k => fseq k (pseq k)) atTop (𝓝 (f p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto _).comp
      (hjet 0 (Nat.zero_le _))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  apply tendsto_iteratedFDeriv_comp_of_jets r hf hphi
    (Eventually.of_forall hs) (Eventually.of_forall hphis) hjet
  intro m _
  exact (hphi.continuousAt_iteratedFDeriv (by
    exact_mod_cast le_top (a := (m : ℕ∞)))).tendsto.comp hval

theorem tendsto_iteratedFDeriv_clm_comp_of_jet
    {f : ℕ → E → F} {f₀ : E → F} {p : ℕ → E} {p₀ : E} (r : ℕ) (L : F →L[ℝ] G)
    (hf₀ : ContDiffAt ℝ ∞ f₀ p₀)
    (hf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hjet : Tendsto (fun k => iteratedFDeriv ℝ r (f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r f₀ p₀))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (L ∘ f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (L ∘ f₀) p₀)) := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  rw [L.iteratedFDeriv_comp_left hf₀ hr]
  have h := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin r => E) F G L).continuous.tendsto _).comp hjet
  exact h.congr' (hf.mono fun k hk => (L.iteratedFDeriv_comp_left hk hr).symm)

theorem tendsto_iteratedFDeriv_prodMk_of_jets
    {f : ℕ → E → F} {g : ℕ → E → G} {f₀ : E → F} {g₀ : E → G}
    {p : ℕ → E} {p₀ : E} (r : ℕ)
    (hf₀ : ContDiffAt ℝ ∞ f₀ p₀) (hg₀ : ContDiffAt ℝ ∞ g₀ p₀)
    (hf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hg : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (g k) (p k))
    (hfjet : Tendsto (fun k => iteratedFDeriv ℝ r (f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r f₀ p₀)))
    (hgjet : Tendsto (fun k => iteratedFDeriv ℝ r (g k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r g₀ p₀))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun x => (f k x, g k x)) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun x => (f₀ x, g₀ x)) p₀)) := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  rw [iteratedFDeriv_prodMk hf₀ hg₀ hr]
  have h := ((ContinuousMultilinearMap.prodL ℝ (fun _ : Fin r => E) F G).continuous.tendsto
    (iteratedFDeriv ℝ r f₀ p₀, iteratedFDeriv ℝ r g₀ p₀)).comp
      (hfjet.prodMk_nhds hgjet)
  apply h.congr'
  filter_upwards [hf, hg] with k hfk hgk
  exact (iteratedFDeriv_prodMk hfk hgk hr).symm

theorem tendsto_iteratedFDeriv_mul_of_jets
    {f g : ℕ → E → ℝ} {f₀ g₀ : E → ℝ} {p : ℕ → E} {p₀ : E} (r : ℕ)
    (hf₀ : ContDiffAt ℝ ∞ f₀ p₀) (hg₀ : ContDiffAt ℝ ∞ g₀ p₀)
    (hf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hg : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (g k) (p k))
    (hfjet : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ m f₀ p₀)))
    (hgjet : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (g k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g₀ p₀))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun x => f k x * g k x) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun x => f₀ x * g₀ x) p₀)) := by
  let mul : ℝ × ℝ → ℝ := fun z => z.1 * z.2
  have hmul : ContDiff ℝ ∞ mul := contDiff_fst.mul contDiff_snd
  have hpair (m : ℕ) (hm : m ≤ r) := tendsto_iteratedFDeriv_prodMk_of_jets
    m hf₀ hg₀ hf hg (hfjet m hm) (hgjet m hm)
  have hval : Tendsto (fun k => (f k (p k), g k (p k))) atTop (𝓝 (f₀ p₀, g₀ p₀)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ E (ℝ × ℝ)).continuous.tendsto _).comp
      (hpair 0 (Nat.zero_le _))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  apply tendsto_iteratedFDeriv_comp_of_jets r (hf₀.prodMk hg₀) hmul.contDiffAt
    (hf.and hg |>.mono fun _ h => h.1.prodMk h.2) (Eventually.of_forall fun _ => hmul.contDiffAt)
    hpair
  intro m _
  exact (hmul.contDiffAt.continuousAt_iteratedFDeriv (by
    exact_mod_cast le_top (a := (m : ℕ∞)))).tendsto.comp hval

theorem tendsto_iteratedFDeriv_fderiv_apply_of_jet
    {f : ℕ → E → F} {f₀ : E → F} {p : ℕ → E} {p₀ : E} (r : ℕ) (v : E)
    (hf₀ : ContDiffAt ℝ ∞ f₀ p₀)
    (hf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hjet : Tendsto (fun k => iteratedFDeriv ℝ (r + 1) (f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ (r + 1) f₀ p₀))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun x => fderiv ℝ (f k) x v) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun x => fderiv ℝ f₀ x v) p₀)) := by
  let C := continuousMultilinearCurryRightEquiv' ℝ r E F
  have hc (f : E → F) (x : E) :
      iteratedFDeriv ℝ r (fderiv ℝ f) x = C (iteratedFDeriv ℝ (r + 1) f x) := by
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact (C.apply_symm_apply _).symm
  have hderiv : Tendsto (fun k => iteratedFDeriv ℝ r (fderiv ℝ (f k)) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fderiv ℝ f₀) p₀)) := by
    simp_rw [hc]
    exact (C.continuous.tendsto _).comp hjet
  let ev := ContinuousLinearMap.apply ℝ F v
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  have hs (f : E → F) (x : E) (hf : ContDiffAt ℝ ∞ f x) :
      iteratedFDeriv ℝ r (fun y => fderiv ℝ f y v) x =
        ev.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fderiv ℝ f) x) :=
    ev.iteratedFDeriv_comp_left (hf.fderiv_right (by simp)) hr
  rw [hs f₀ p₀ hf₀]
  have h := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin r => E) (E →L[ℝ] F) F ev).continuous.tendsto _).comp hderiv
  exact h.congr' (hf.mono fun k hk => (hs (f k) (p k) hk).symm)

end PoincareConjecture.M35
