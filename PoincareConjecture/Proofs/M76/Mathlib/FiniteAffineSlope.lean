import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic












set_option autoImplicit false

open Set

namespace ContinuousOn






theorem add_smul_eq_of_finite_affine_selection
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]
    {f : E → ℝ} {B : Set E} (hf : ContinuousOn f B) (hB : Convex ℝ B)
    (A : ι → E →ᴬ[ℝ] ℝ) (w : E)
    (hA : ∀ i, (A i).contLinear w = 1)
    (hselect : ∀ y ∈ B, ∃ i, f y = A i y)
    {x : E} {t : ℝ} (hx : x ∈ B) (hxt : t • w + x ∈ B) :
    f (t • w + x) = f x + t := by
  let q : ℝ → E := fun u => (u * t) • w + x
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hqB : MapsTo q (Icc 0 1) B := by
    intro u hu
    have h := hB.lineMap_mem hx hxt hu
    simpa only [AffineMap.lineMap_apply_module', add_sub_cancel_right, smul_smul]
      using h
  let g : ℝ → ℝ := fun u => f (q u) - u * t
  have hgc : ContinuousOn g (Icc 0 1) :=
    (hf.comp hq.continuousOn hqB).sub (continuous_id.mul continuous_const).continuousOn
  have hfinite : (g '' Icc 0 1).Finite := by
    apply (finite_range (fun i => A i x)).subset
    rintro z ⟨u, hu, rfl⟩
    obtain ⟨i, hi⟩ := hselect (q u) (hqB hu)
    refine ⟨i, ?_⟩
    dsimp [g]
    rw [hi]
    change A i x = A i ((u * t) • w +ᵥ x) - u * t
    rw [ContinuousAffineMap.map_vadd, map_smul, hA i]
    change A i x = (u * t) * 1 + A i x - u * t
    ring
  have hpre := isPreconnected_Icc.image g hgc
  have hzero : g 0 ∈ g '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hone : g 1 ∈ g '' Icc 0 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have heq : g 1 = g 0 := by
    by_contra hne
    exact hpre.infinite_of_nontrivial ⟨g 1, hone, g 0, hzero, hne⟩ hfinite
  have hdiff : f (t • w + x) - t = f x := by
    simpa only [g, q, one_mul, zero_mul, zero_smul, zero_add, sub_zero] using heq
  exact sub_eq_iff_eq_add.mp hdiff

end ContinuousOn
