import PoincareConjecture.Proofs.M02.Topology.GeometricAffineFlags
import PoincareConjecture.Proofs.M02.Topology.FiniteConvexLipschitz

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {I : Type u} [PartialOrder I] [Fintype I]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace Real E]

theorem exists_weights_of_mem_finite_hull_image
    {I : Type u} [Finite I]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace Real E]
    (c : I → E) (t : Finset I) (x : E)
    (hx : x ∈ convexHull Real (c '' (t : Set I))) :
    ∃ w : I → Real, (∀ i, 0 ≤ w i) ∧ (∀ i, i ∉ t → w i = 0) ∧
      (∑ i ∈ t, w i) = 1 ∧ (∑ i ∈ t, w i • c i) = x := by
  classical
  let := Fintype.ofFinite I
  let L : (I → Real) →ₗ[Real] E := Fintype.linearCombination Real c
  let b : I → I → Real := fun i => Pi.single i 1
  have himage : L '' convexHull Real (b '' (t : Set I)) =
      convexHull Real (c '' (t : Set I)) := by
    rw [L.image_convexHull, Set.image_image]
    congr 1
    have heval : (fun i => L (b i)) = c := by
      funext i
      simp only [L, b, Fintype.linearCombination_apply_single, one_smul]
    exact congrArg (fun f : I → E => f '' (t : Set I)) heval
  rw [← himage] at hx
  obtain ⟨w, hw, hval⟩ := hx
  have hstd : w ∈ stdSimplex Real I := by
    apply convexHull_min _ (convex_stdSimplex Real I) hw
    rintro _ ⟨i, _, rfl⟩
    exact single_mem_stdSimplex Real i
  have hzero (i : I) (hi : i ∉ t) : w i = 0 := by
    have hc : Convex Real {z : I → Real | z i = 0} := by
      intro a ha b hb r s hr hs hrs
      change r * a i + s * b i = 0
      rw [ha, hb]
      simp
    apply convexHull_min _ hc hw
    rintro _ ⟨j, hj, rfl⟩
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp only [b, Set.mem_ofPred_eq, Pi.single_apply, if_neg hij]
  refine ⟨w, hstd.1, hzero, ?_, ?_⟩
  · exact (Finset.sum_subset (Finset.subset_univ t)
      (fun i _ hi => hzero i hi)).trans hstd.2
  · have hsum : (∑ i ∈ t, w i • c i) = ∑ i, w i • c i :=
      Finset.sum_subset (Finset.subset_univ t)
        (fun i _ hi => by rw [hzero i hi, zero_smul])
    exact hsum.trans hval

def finiteFlagComparison (c d : I → E)
    (hinj : Function.Injective (finiteOrderComplexMap I c)) (x : E) : E := by
  classical
  exact if hx : x ∈ Set.range (finiteOrderComplexMap I c) then
    finiteOrderComplexMap I d
      ((Equiv.ofInjective (finiteOrderComplexMap I c) hinj).symm ⟨x, hx⟩)
  else 0

theorem finiteFlagComparison_map (c d : I → E)
    (hinj : Function.Injective (finiteOrderComplexMap I c))
    (z : (finiteOrderComplex I).space) :
    finiteFlagComparison c d hinj (finiteOrderComplexMap I c z) =
      finiteOrderComplexMap I d z := by
  unfold finiteFlagComparison
  rw [dif_pos (Set.mem_range_self z), Equiv.ofInjective_symm_apply]

theorem finiteFlagComparison_mem_range (c d : I → E)
    (hinj : Function.Injective (finiteOrderComplexMap I c))
    (x : E) (hx : x ∈ Set.range (finiteOrderComplexMap I c)) :
    finiteFlagComparison c d hinj x ∈ Set.range (finiteOrderComplexMap I d) := by
  obtain ⟨z, rfl⟩ := hx
  rw [finiteFlagComparison_map]
  exact Set.mem_range_self z

theorem finiteFlagComparison_eq_sum (c d : I → E)
    (hinj : Function.Injective (finiteOrderComplexMap I c))
    (t : Finset I) (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i)
    (w : I → Real) (hw : ∀ i, 0 ≤ w i)
    (hzero : ∀ i, i ∉ t → w i = 0) (hsum : ∑ i ∈ t, w i = 1) :
    finiteFlagComparison c d hinj (∑ i ∈ t, w i • c i) =
      ∑ i ∈ t, w i • d i := by
  have hsum' : ∑ i, w i = 1 :=
    (Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => hzero i hi)).symm.trans hsum
  have hspace : w ∈ (finiteOrderComplex I).space :=
    (finiteOrderComplex_space I w).mpr ⟨hw, hsum', fun i j hi hj =>
      hchain i (by_contra fun h => hi (hzero i h))
        j (by_contra fun h => hj (hzero j h))⟩
  have heval (f : I → E) : (∑ i ∈ t, w i • f i) =
      finiteOrderComplexMap I f ⟨w, hspace⟩ :=
    Finset.sum_subset (Finset.subset_univ t)
      (fun i _ hi => by rw [hzero i hi, zero_smul])
  rw [heval c, finiteFlagComparison_map, heval d]

theorem finiteFlagComparison_displacement_le (c d : I → E)
    (hinj : Function.Injective (finiteOrderComplexMap I c))
    (delta : Real) (hd : ∀ i, ‖d i - c i‖ ≤ delta)
    (x : E) (hx : x ∈ Set.range (finiteOrderComplexMap I c)) :
    ‖finiteFlagComparison c d hinj x - x‖ ≤ delta := by
  obtain ⟨z, rfl⟩ := hx
  rw [finiteFlagComparison_map]
  have hz := (finiteOrderComplex_space I z.val).mp z.property
  change ‖(∑ i, z.val i • d i) - ∑ i, z.val i • c i‖ ≤ delta
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    ‖∑ i, z.val i • (d i - c i)‖ ≤ ∑ i, ‖z.val i • (d i - c i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, z.val i * delta := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hz.1 i)]
      exact mul_le_mul_of_nonneg_left (hd i) (hz.1 i)
    _ = delta := by rw [← Finset.sum_mul, hz.2.1, one_mul]

theorem finiteFlagComparison_displacement_lipschitzOn
    (c d : I → E) (hinj : Function.Injective (finiteOrderComplexMap I c))
    (kappa : NNReal)
    (hbound : ∀ (t : Finset I),
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) →
      ∀ w : I → Real, (∑ i ∈ t, w i) = 0 →
        ‖∑ i ∈ t, w i • (d i - c i)‖ ≤
          (kappa : Real) * ‖∑ i ∈ t, w i • c i‖)
    (U : Set E) (hU : Convex Real U)
    (hUr : U ⊆ Set.range (finiteOrderComplexMap I c)) :
    LipschitzOnWith kappa (fun x => finiteFlagComparison c d hinj x - x) U := by
  classical
  let J := {t : Finset I //
    t.Nonempty ∧ ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i}
  let C (t : J) := convexHull Real (c '' (t.val : Set I))
  apply lipschitzOnWith_of_finite_convex_cover C
    (fun t => ((t.val.finite_toSet.image c).isCompact_convexHull Real).isClosed)
    (fun _ => convex_convexHull Real _) U hU ?_ kappa _ ?_
  · intro x hx
    obtain ⟨t, ht, hchain, hxt⟩ :=
      (mem_range_finiteOrderComplexMap_iff c x).mp (hUr hx)
    exact Set.mem_iUnion.mpr ⟨⟨t, ht, hchain⟩, hxt⟩
  · intro t
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    obtain ⟨w, hw, hwzero, hwsum, hwval⟩ :=
      exists_weights_of_mem_finite_hull_image c t.val x hx
    obtain ⟨w', hw', hw'zero, hw'sum, hw'val⟩ :=
      exists_weights_of_mem_finite_hull_image c t.val y hy
    have hfx : finiteFlagComparison c d hinj x - x =
        ∑ i ∈ t.val, w i • (d i - c i) := by
      rw [← hwval, finiteFlagComparison_eq_sum c d hinj t.val t.property.2 w hw hwzero hwsum]
      simp only [smul_sub, Finset.sum_sub_distrib]
    have hfy : finiteFlagComparison c d hinj y - y =
        ∑ i ∈ t.val, w' i • (d i - c i) := by
      rw [← hw'val, finiteFlagComparison_eq_sum c d hinj t.val t.property.2 w' hw' hw'zero hw'sum]
      simp only [smul_sub, Finset.sum_sub_distrib]
    have hsum : ∑ i ∈ t.val, (w i - w' i) = 0 := by
      rw [Finset.sum_sub_distrib, hwsum, hw'sum, sub_self]
    have h := hbound t.val t.property.2 (fun i => w i - w' i) hsum
    simp only [sub_smul, Finset.sum_sub_distrib] at h
    rw [hwval, hw'val] at h
    simpa only [dist_eq_norm, hfx, hfy] using h

end PoincareConjecture.Proofs.M02.Topology
