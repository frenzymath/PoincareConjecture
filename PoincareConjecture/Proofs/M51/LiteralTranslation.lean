import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Ordinary

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


noncomputable def literalTranslate {J : Set ℝ} (F : RicciFlow n M J)
    (a : ℝ) (K : Set ℝ) (hK : K.OrdConnected) (hne : K.Nontrivial)
    (hclock : MapsTo (fun v : ℝ => a + v) K J) : RicciFlow n M K where
  metric := fun v => F.metric (a + v)
  connection := fun v => F.connection (a + v)
  interval := hK
  nontrivial := hne
  smooth := by
    have hsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × M => (a + p.1, p.2)) (K ×ˢ univ) :=
      (contMDiffOn_const.add contMDiffOn_fst).prodMk contMDiffOn_snd
    exact F.smooth.comp hsm (fun p hp => ⟨hclock hp.1, hp.2⟩)
  equation := by
    intro t ht x v w
    have he := (F.equation (a + t) (hclock ht) x v w).comp t
      ((hasDerivAt_id t).const_add a).hasDerivWithinAt hclock
    simpa only [Function.comp_def, id_eq, mul_one] using he

@[simp] theorem literalTranslate_metric {J : Set ℝ} (F : RicciFlow n M J)
    (a : ℝ) (K : Set ℝ) (hK : K.OrdConnected) (hne : K.Nontrivial)
    (hclock : MapsTo (fun v : ℝ => a + v) K J) (t : ℝ) :
    (literalTranslate F a K hK hne hclock).metric t = F.metric (a + t) := rfl

@[simp] theorem literalTranslate_connection {J : Set ℝ} (F : RicciFlow n M J)
    (a : ℝ) (K : Set ℝ) (hK : K.OrdConnected) (hne : K.Nontrivial)
    (hclock : MapsTo (fun v : ℝ => a + v) K J) (t : ℝ) :
    (literalTranslate F a K hK hne hclock).connection t = F.connection (a + t) := rfl

@[simp] theorem literalTranslate_curvatureTensorNorm {J : Set ℝ}
    (F : RicciFlow n M J) (a : ℝ) (K : Set ℝ)
    (hK : K.OrdConnected) (hne : K.Nontrivial)
    (hclock : MapsTo (fun v : ℝ => a + v) K J) (t : ℝ) (x : M) :
    ((literalTranslate F a K hK hne hclock).connection t).curvatureTensorNorm x =
      (F.connection (a + t)).curvatureTensorNorm x := rfl


noncomputable def tail {T a : ℝ} (F : RicciFlow n M (Ico 0 T))
    (ha : 0 ≤ a) (haT : a < T) : RicciFlow n M (Ico 0 (T - a)) :=
  literalTranslate F a (Ico 0 (T - a)) ordConnected_Ico
    (by
      refine ⟨0, ⟨le_rfl, sub_pos.mpr haT⟩,
        (T - a) / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith)
    (by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)

@[simp] theorem tail_metric {T a : ℝ} (F : RicciFlow n M (Ico 0 T))
    (ha : 0 ≤ a) (haT : a < T) (t : ℝ) :
    (tail F ha haT).metric t = F.metric (a + t) := rfl

@[simp] theorem tail_connection {T a : ℝ} (F : RicciFlow n M (Ico 0 T))
    (ha : 0 ≤ a) (haT : a < T) (t : ℝ) :
    (tail F ha haT).connection t = F.connection (a + t) := rfl

@[simp] theorem tail_curvatureTensorNorm {T a : ℝ}
    (F : RicciFlow n M (Ico 0 T)) (ha : 0 ≤ a) (haT : a < T) (t : ℝ) (x : M) :
    ((tail F ha haT).connection t).curvatureTensorNorm x =
      (F.connection (a + t)).curvatureTensorNorm x := rfl

theorem tail_isLeast {T a : ℝ} (haT : a < T) : IsLeast (Ico 0 (T - a)) 0 :=
  ⟨⟨le_rfl, sub_pos.mpr haT⟩, fun _ ht => ht.1⟩


theorem tail_curvature_bound {T a L : ℝ} (F : RicciFlow n M (Ico 0 T))
    (ha : 0 ≤ a) (haT : a < T)
    (hbound : ∀ t ∈ Ico a T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ L) :
    ∀ t ∈ Ico 0 (T - a), ∀ x : M,
      ((tail F ha haT).connection t).curvatureTensorNorm x ≤ L := by
  intro t ht x
  exact hbound (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x


noncomputable def restart {δ : ℝ} (R : RicciFlow n M (Ico 0 δ))
    (hδ : 0 < δ) (a : ℝ) : RicciFlow n M (Ico a (a + δ)) :=
  literalTranslate R (-a) (Ico a (a + δ)) ordConnected_Ico
    (by
      refine ⟨a, ⟨le_rfl, by linarith⟩,
        a + δ / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith)
    (by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)

@[simp] theorem restart_metric {δ : ℝ} (R : RicciFlow n M (Ico 0 δ))
    (hδ : 0 < δ) (a t : ℝ) :
    (restart R hδ a).metric t = R.metric (t - a) := by
  change R.metric (-a + t) = R.metric (t - a)
  rw [show -a + t = t - a by linarith]

theorem restart_connection {δ : ℝ} (R : RicciFlow n M (Ico 0 δ))
    (hδ : 0 < δ) (a t : ℝ) :
    HEq ((restart R hδ a).connection t) (R.connection (t - a)) := by
  change HEq (R.connection (-a + t)) (R.connection (t - a))
  rw [show -a + t = t - a by linarith]

@[simp] theorem restart_curvatureTensorNorm {δ : ℝ}
    (R : RicciFlow n M (Ico 0 δ)) (hδ : 0 < δ) (a t : ℝ) (x : M) :
    ((restart R hδ a).connection t).curvatureTensorNorm x =
      (R.connection (t - a)).curvatureTensorNorm x := by
  change (R.connection (-a + t)).curvatureTensorNorm x =
    (R.connection (t - a)).curvatureTensorNorm x
  rw [show -a + t = t - a by linarith]

@[simp] theorem restart_metric_add {δ : ℝ} (R : RicciFlow n M (Ico 0 δ))
    (hδ : 0 < δ) (a t : ℝ) : (restart R hδ a).metric (a + t) = R.metric t := by
  rw [restart_metric, add_sub_cancel_left]

theorem restart_isLeast {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    IsLeast (Ico a (a + δ)) a :=
  ⟨⟨le_rfl, by linarith⟩, fun _ ht => ht.1⟩

end PoincareConjecture.M51Ordinary
