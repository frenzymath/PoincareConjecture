import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.Bounded
import Mathlib.Topology.Homotopy.Lifting














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_radial_deck_motion
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hlower : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (f (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => f (u • v)) t 1) ≤ ‖v‖)
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) (hx : f x = f 0) :
    let A := {v : EuclideanSpace ℝ (Fin n) // ‖(x : EuclideanSpace ℝ (Fin n))‖ + 2 * ‖v‖ < R}
    ∃ D : C(A, Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R),
      (∀ v, f (D v) = f v) ∧
      (∀ v, ‖(D v : EuclideanSpace ℝ (Fin n)) - x‖ ≤ 2 * ‖(v : EuclideanSpace ℝ (Fin n))‖) ∧
      (∀ v, ∃ l : C(unitInterval, Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R),
        l 0 = x ∧ l 1 = D v ∧ ∀ t, f (l t) = f ((t : ℝ) • (v : EuclideanSpace ℝ (Fin n)))) ∧
      (∀ v : A, (v : EuclideanSpace ℝ (Fin n)) = 0 → D v = x) ∧
      ((x : EuclideanSpace ℝ (Fin n)) ≠ 0 →
        ∀ v, (D v : EuclideanSpace ℝ (Fin n)) ≠ (v : EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  let E := EuclideanSpace ℝ (Fin n)
  let A := {v : E // ‖(x : E)‖ + 2 * ‖v‖ < R}
  let B := Metric.ball (0 : E) R
  let F := B.domRestrict f
  have hlocal : IsLocalHomeomorph F :=
    isLocalHomeomorph_domRestrict_of_nonsingular Metric.isOpen_ball hf hbij
  have hvR (v : A) : (v : E) ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    have := v.property
    have := norm_nonneg (x : E)
    have := norm_nonneg (v : E)
    linarith
  have htmem (v : A) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      t • (v : E) ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (v : E))).trans_lt
      (by simpa using hvR v)
  have hc (v : A) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun u : ℝ => f (u • (v : E))) t :=
    (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds (htmem v t ht))).comp t
      (contMDiffAt_iff_contDiffAt.mpr (by fun_prop))
  choose l hl h0 hproj hbound using fun v : A =>
    exists_bounded_lift_of_lower_differential g hf hbij hlower (hc v)
      (norm_nonneg (v : E)) (hspeed v (hvR v)) x (by simpa using hx) v.property
  let c (v : A) : C(unitInterval, B) :=
    ⟨fun t => l v t, (hl v).comp_continuous continuous_subtype_val (fun t => t.property)⟩
  let H : C(unitInterval × A, M) :=
    ⟨fun tv => f ((tv.1 : ℝ) • (tv.2 : E)),
      hf.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd))
        (fun tv => htmem tv.2 tv.1 tv.1.property)⟩
  have hcproj (v : A) (t : unitInterval) : F (c v t) = H (t, v) :=
    hproj v t.property
  have hc0 (v : A) : c v 0 = x := h0 v
  have hjoint : Continuous (fun tv : unitInterval × A => c tv.2 tv.1) := by
    apply hlocal.continuous_lift (T2Space.isSeparatedMap F) H
    · exact funext fun tv => hcproj tv.2 tv.1
    · simpa only [hc0] using (continuous_const : Continuous (fun _ : A => x))
    · exact fun v => (c v).continuous
  let D : C(A, B) := ⟨fun v => c v 1, hjoint.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    change f (c v 1) = f (v : E)
    simpa [F, H] using hcproj v 1
  · intro v
    change ‖(l v 1 : E) - x‖ ≤ 2 * ‖(v : E)‖
    simpa only [mul_one] using hbound v 1 (by simp)
  · intro v
    exact ⟨c v, hc0 v, rfl, hcproj v⟩
  · intro v hv
    have heq := (T2Space.isSeparatedMap F).eq_of_comp_eq hlocal.isLocallyInjective
      (c v).continuous (continuous_const : Continuous (fun _ : unitInterval => x))
      (funext fun t => by
        change F (c v t) = f x
        rw [hcproj]
        simpa [H, hv] using hx.symm) 0 (hc0 v)
    exact congrFun heq 1
  · intro hxne v heq
    change (c v 1 : E) = (v : E) at heq
    let r : C(unitInterval, B) :=
      ⟨fun t => ⟨(t : ℝ) • (v : E), htmem v t t.property⟩,
        (continuous_subtype_val.smul continuous_const).subtype_mk _⟩
    have hsame := (T2Space.isSeparatedMap F).eq_of_comp_eq hlocal.isLocallyInjective
      (c v).continuous r.continuous (funext fun t => hcproj v t) 1
      (Subtype.ext (by simpa [r] using heq))
    have hzero := congrArg Subtype.val (congrFun hsame 0)
    rw [hc0] at hzero
    exact hxne (by simpa [r] using hzero)

end PoincareConjecture
