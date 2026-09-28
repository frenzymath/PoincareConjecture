import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M40

variable {E H F K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}

theorem exists_smooth_of_finite_local_smoothing
    {ι : Type*} [Finite ι] (W : ι → Set M)
    (hcover : ∀ x, ∃ i, x ∈ W i)
    (dM : M → M → ℝ≥0∞) (dN : N → N → ℝ≥0∞)
    (hdN_self : ∀ y, dN y y = 0)
    (hdN_triangle : ∀ x y z, dN x z ≤ dN x y + dN y z)
    (f₀ : C(M, N)) {L ε σ : ℝ} (hL : 0 ≤ L)
    (hε : 0 < ε) (hσ : 0 < σ)
    (hf₀ : ∀ x y, dN (f₀ x) (f₀ y) ≤ ENNReal.ofReal L * dM x y)
    (hstep : ∀ (i : ι) (f : C(M, N)) (B : ℝ), 0 ≤ B →
      (∀ x, dN (f x) (f₀ x) < ENNReal.ofReal ε) →
      (∀ x y, dN (f x) (f y) ≤ ENNReal.ofReal B * dM x y) →
      ∀ (s e : ℝ), 0 < s → 0 < e →
        ∃ g : C(M, N),
          (∀ x ∈ W i, ContMDiffAt I J ∞ g x) ∧
          (∀ x, ContMDiffAt I J ∞ f x → ContMDiffAt I J ∞ g x) ∧
          ContinuousMap.Homotopic g f ∧
          (∀ x, dN (g x) (f x) < ENNReal.ofReal e) ∧
          (∀ x y, dN (g x) (g y) ≤ ENNReal.ofReal (B + s) * dM x y)) :
    ∃ g : C(M, N), ContMDiff I J ∞ g ∧ ContinuousMap.Homotopic g f₀ ∧
      (∀ x, dN (g x) (f₀ x) < ENNReal.ofReal ε) ∧
      (∀ x y, dN (g x) (g y) ≤ ENNReal.ofReal (L + σ) * dM x y) := by
  classical
  let := Fintype.ofFinite ι
  have hfinite : ∀ A : Finset ι, ∀ s e : ℝ, 0 < s → 0 < e → e ≤ ε →
      ∃ g : C(M, N),
        (∀ i ∈ A, ∀ x ∈ W i, ContMDiffAt I J ∞ g x) ∧
        ContinuousMap.Homotopic g f₀ ∧
        (∀ x, dN (g x) (f₀ x) < ENNReal.ofReal e) ∧
        (∀ x y, dN (g x) (g y) ≤ ENNReal.ofReal (L + s) * dM x y) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro s e hs he _
      refine ⟨f₀, by simp, ContinuousMap.Homotopic.refl f₀, ?_, ?_⟩
      · intro x
        rw [hdN_self]
        exact ENNReal.ofReal_pos.mpr he
      · intro x y
        exact (hf₀ x y).trans (mul_le_mul'
          (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)
    | @insert i A hi ih =>
      intro s e hs he heε
      have hs2 : 0 < s / 2 := by linarith
      have he2 : 0 < e / 2 := by linarith
      obtain ⟨f, hfsmooth, hfhom, hfclose, hfbound⟩ :=
        ih (s / 2) (e / 2) hs2 he2 (by linarith)
      have hfmargin : ∀ x, dN (f x) (f₀ x) < ENNReal.ofReal ε := fun x =>
        (hfclose x).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
      obtain ⟨g, hgsmooth, hgpreserve, hghom, hgclose, hgbound⟩ :=
        hstep i f (L + s / 2) (by linarith) hfmargin hfbound
          (s / 2) (e / 2) hs2 he2
      refine ⟨g, ?_, hghom.trans hfhom, ?_, ?_⟩
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hgsmooth x hx
        · exact hgpreserve x (hfsmooth j hj x hx)
      · intro x
        calc
          dN (g x) (f₀ x) ≤ dN (g x) (f x) + dN (f x) (f₀ x) :=
            hdN_triangle _ _ _
          _ < ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) :=
            ENNReal.add_lt_add (hgclose x) (hfclose x)
          _ = ENNReal.ofReal e := by
            rw [← ENNReal.ofReal_add he2.le he2.le]
            congr 1
            ring
      · have heq : L + s / 2 + s / 2 = L + s := by ring
        simpa only [heq] using hgbound
  obtain ⟨g, hgsmooth, hghom, hgclose, hgbound⟩ :=
    hfinite Finset.univ σ ε hσ hε le_rfl
  refine ⟨g, ?_, hghom, hgclose, hgbound⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact hgsmooth i (Finset.mem_univ i) x hi

end PoincareConjecture.M40
