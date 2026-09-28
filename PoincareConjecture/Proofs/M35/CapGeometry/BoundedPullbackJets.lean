import PoincareConjecture.Proofs.M35.CapGeometry.VanishingMetricErrorJets
import PoincareConjecture.Proofs.M35.Thm12_28.NeckPullbackJets









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)



theorem cylinder_pullback_jet_difference_tendsto_zero_of_bounded
    (f : ℕ → RoundCylinderCoordinates → V) (p : ℕ → RoundCylinderCoordinates)
    (v w : RoundCylinderCoordinates) (A : ℕ → V → Fin 3 → Fin 3 → ℝ) (r : ℕ)
    (hf : ∀ k, ContDiffAt ℝ ∞ (f k) (p k))
    (hfjet : HasUniformJetBoundsAt (r + 1) f p)
    (hA : ∀ a b : Fin 3, ∀ᶠ k in atTop,
      ContDiffAt ℝ ∞ (fun y => A k y a b) (f k (p k)))
    (hAjet : ∀ m ≤ r, ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ m (fun y => A k y a b) (f k (p k))) atTop (𝓝 0)) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
      ∑ a : Fin 3, ∑ b : Fin 3,
        A k (f k y) a b * (fderiv ℝ (f k) y v) a * (fderiv ℝ (f k) y w) b) (p k))
      atTop (𝓝 0) := by
  let C (v : RoundCylinderCoordinates) (a : Fin 3) (k : ℕ)
      (y : RoundCylinderCoordinates) := (fderiv ℝ (f k) y v) a
  have hC (v : RoundCylinderCoordinates) (a : Fin 3) (k : ℕ) :
      ContDiffAt ℝ ∞ (C v a k) (p k) :=
    (EuclideanSpace.proj a).contDiff.contDiffAt.comp (p k)
      (((hf k).fderiv_right (by simp)).clm_apply contDiffAt_const)
  have hCjet (v : RoundCylinderCoordinates) (a : Fin 3) :
      HasUniformJetBoundsAt r (C v a) p :=
    hfjet.fderiv.clm (fun k => (hf k).fderiv_right (by simp))
      ((EuclideanSpace.proj a).comp (ContinuousLinearMap.apply ℝ V v))
  let H (k : ℕ) (a b : Fin 3) (y : RoundCylinderCoordinates) :=
    A k (f k y) a b * C v a k y * C w b k y
  have hH (a b : Fin 3) : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (H k a b) (p k) :=
    (hA a b).mono fun k hk =>
      ((hk.comp (p k) (hf k)).mul (hC v a k)).mul (hC w b k)
  have hlim (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ r (H k a b) (p k)) atTop (𝓝 0) := by
    have hcomp (m : ℕ) (hm : m ≤ r) :
        Tendsto (fun k => iteratedFDeriv ℝ m (fun y => A k (f k y) a b) (p k))
          atTop (𝓝 0) :=
      jet_comp_tendsto_zero_of_bounded (hfjet.mono_order (by omega))
        (Eventually.of_forall hf) (hA a b) (fun j hj => hAjet j (hj.trans hm) a b)
    have hfirst (m : ℕ) (hm : m ≤ r) :
        Tendsto (fun k => iteratedFDeriv ℝ m
          (fun y => A k (f k y) a b * C v a k y) (p k)) atTop (𝓝 0) :=
      jet_bilinear_tendsto_zero_of_bounded (ContinuousLinearMap.mul ℝ ℝ)
        (fun j hj => hcomp j (hj.trans hm)) ((hCjet v a).mono_order hm)
        ((hA a b).mono fun k hk => hk.comp (p k) (hf k))
        (Eventually.of_forall (hC v a))
    exact jet_bilinear_tendsto_zero_of_bounded (ContinuousLinearMap.mul ℝ ℝ)
      hfirst (hCjet w b)
      ((hA a b).mono fun k hk => (hk.comp (p k) (hf k)).mul (hC v a k))
      (Eventually.of_forall (hC w b))
  have hsum := tendsto_finsetSum Finset.univ (fun a _ =>
    tendsto_finsetSum Finset.univ (fun b _ => hlim a b))
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr'
  have hAll : ∀ᶠ k in atTop, ∀ a b : Fin 3, ContDiffAt ℝ ∞ (H k a b) (p k) :=
    eventually_all.mpr (fun a => eventually_all.mpr (fun b => hH a b))
  filter_upwards [hAll] with k hk
  symm
  change iteratedFDeriv ℝ r (fun y => ∑ a : Fin 3, ∑ b : Fin 3, H k a b y) (p k) = _
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  rw [iteratedFDeriv_fun_sum_apply (fun a _ =>
    (ContDiffAt.sum (fun b _ => hk a b)).of_le hr)]
  exact Finset.sum_congr rfl (fun a _ =>
    iteratedFDeriv_fun_sum_apply (fun b _ => (hk a b).of_le hr))

end PoincareConjecture.M35
