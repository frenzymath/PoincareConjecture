import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralOrderedSubdivision
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralChainCoordinates
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Poincare.Topology

def integralSimplexVertices (n : Nat) : Fin (n + 1) → integralSimplex n :=
  fun i => stdSimplex.vertex (S := Real) i

def integralSimplexBarycenter (d n : Nat)
    (v : Fin (n + 1) → integralSimplex d) : integralSimplex d := by
  refine ⟨((n + 1 : Real)⁻¹) • ∑ i, (v i).val, ?_⟩
  rw [Finset.smul_sum]
  apply (convex_stdSimplex Real (Fin (d + 1))).sum_mem
  · intro i _
    positivity
  · have hn : (n + 1 : Real) ≠ 0 := by positivity
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_inv_cancel₀ hn
  · intro i _
    exact (v i).property

def integralSimplexAffine {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) :
    C(integralSimplex n, integralSimplex d) where
  toFun x := ⟨∑ i, x.val i • (v i).val,
    (convex_stdSimplex Real (Fin (d + 1))).sum_mem
      (fun i _ => x.property.1 i) x.property.2 (fun i _ => (v i).property)⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_finsetSum Finset.univ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)) _

theorem integralSimplexBarycenter_val (d n : Nat)
    (v : Fin (n + 1) → integralSimplex d) :
    (integralSimplexBarycenter d n v).val =
      ((n + 1 : Real)⁻¹) • ∑ i, (v i).val := rfl

theorem integralSimplexBarycenter_one (d : Nat) (v : Fin 1 → integralSimplex d) :
    integralSimplexBarycenter d 0 v = v 0 := by
  apply Subtype.ext
  simp [integralSimplexBarycenter_val]

theorem integralSimplexAffine_apply {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (x : integralSimplex n) :
    (integralSimplexAffine v x).val = ∑ i, x.val i • (v i).val := rfl

theorem integralSimplexAffine_vertex {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (i : Fin (n + 1)) :
    integralSimplexAffine v (integralSimplexVertices n i) = v i := by
  apply Subtype.ext
  funext j
  simp [integralSimplexAffine, integralSimplexVertices, stdSimplex.vertex,
    Pi.single_apply]

theorem integralSimplexAffine_vertices (n : Nat) :
    integralSimplexAffine (integralSimplexVertices n) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  simp [integralSimplexAffine, integralSimplexVertices, stdSimplex.vertex,
    Pi.single_apply]

theorem integralSimplexAffine_comp {d n k : Nat}
    (v : Fin (n + 1) → integralSimplex d)
    (w : Fin (k + 1) → integralSimplex n) :
    (integralSimplexAffine v).comp (integralSimplexAffine w) =
      integralSimplexAffine (fun i => integralSimplexAffine v (w i)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, integralSimplexAffine_apply]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem integralSimplexAffine_barycenter {d n k : Nat}
    (v : Fin (n + 1) → integralSimplex d)
    (w : Fin (k + 1) → integralSimplex n) :
    integralSimplexAffine v (integralSimplexBarycenter n k w) =
      integralSimplexBarycenter d k (fun i => integralSimplexAffine v (w i)) := by
  apply Subtype.ext
  simp only [integralSimplexAffine_apply, integralSimplexBarycenter_val]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem integralSimplexAffine_face {d n : Nat}
    (v : Fin (n + 2) → integralSimplex d) (i : Fin (n + 2)) :
    (integralSimplexAffine v).comp (integralSimplexFace n i) =
      integralSimplexAffine (v ∘ i.succAbove) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, integralSimplexAffine_apply]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k : Fin (n + 2),
      FunOnFinite.linearMap Real Real i.succAbove x.val k * (v k).val j) =
    ∑ k : Fin (n + 1), x.val k * (v (i.succAbove k)).val j
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_mul,
    Finset.sum_filter, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem integralSimplexBarycenter_dist_le {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (D : Real) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (z : integralSimplex d)
    (hz : z.val ∈ convexHull Real (Set.range (fun i => (v i).val))) :
    dist (integralSimplexBarycenter d n v) z ≤ (n : Real) / (n + 1) * D := by
  have _ := hD
  have hn : (n + 1 : Real) ≠ 0 := by positivity
  have hmean (j : Fin (n + 1)) :
      (integralSimplexBarycenter d n v).val - (v j).val =
        (n + 1 : Real)⁻¹ • ∑ i, ((v i).val - (v j).val) := by
    rw [integralSimplexBarycenter_val]
    funext l
    simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_sub, Pi.mul_apply,
      Pi.add_apply, Pi.natCast_apply, Pi.one_apply, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul]
  have hvertex (j : Fin (n + 1)) :
      dist (integralSimplexBarycenter d n v).val (v j).val ≤
        (n : Real) / (n + 1) * D := by
    have hsum : ‖∑ i : Fin (n + 1), ((v i).val - (v j).val)‖ ≤ (n : Real) * D := by
      rw [Fin.sum_univ_succAbove (fun i => (v i).val - (v j).val) j]
      simp only [sub_self, zero_add]
      calc
        ‖∑ i : Fin n, ((v (j.succAbove i)).val - (v j).val)‖ ≤
            ∑ i : Fin n, ‖(v (j.succAbove i)).val - (v j).val‖ := norm_sum_le _ _
        _ ≤ ∑ _ : Fin n, D := Finset.sum_le_sum (fun i _ => by
          simpa only [Subtype.dist_eq, dist_eq_norm] using hv (j.succAbove i) j)
        _ = (n : Real) * D := by simp
    rw [dist_eq_norm, hmean, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      (n + 1 : Real)⁻¹ * ‖∑ i : Fin (n + 1), ((v i).val - (v j).val)‖ ≤
          (n + 1 : Real)⁻¹ * ((n : Real) * D) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (n : Real) / (n + 1) * D := by rw [div_eq_mul_inv]; ring
  have hball : convexHull Real (Set.range (fun i => (v i).val)) ⊆
      Metric.closedBall (integralSimplexBarycenter d n v).val
        ((n : Real) / (n + 1) * D) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨j, rfl⟩
    simpa only [Metric.mem_closedBall, dist_comm] using hvertex j
  change dist (integralSimplexBarycenter d n v).val z.val ≤ _
  rw [dist_comm]
  exact hball hz

theorem integralSimplexAffine_dist_le {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (D : Real) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : integralSimplex n) : dist (integralSimplexAffine v x)
      (integralSimplexAffine v y) ≤ D := by
  have _ := hD
  have hmem (z : integralSimplex n) :
      (integralSimplexAffine v z).val ∈
        convexHull Real (Set.range (fun i => (v i).val)) := by
    rw [integralSimplexAffine_apply]
    apply (convex_convexHull Real _).sum_mem
    · intro i _
      exact z.property.1 i
    · exact z.property.2
    · intro i _
      exact subset_convexHull Real _ ⟨i, rfl⟩
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h⟩ :=
    convexHull_exists_dist_ge2 (hmem x) (hmem y)
  exact h.trans (hv i j)

theorem integralSimplexSubdivision_mesh {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (D : Real) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (w : Fin (n + 1) → integralSimplex d)
    (hw : w ∈ (integralOrderedSubdivision (integralSimplexBarycenter d)
      (n + 1) (Finsupp.single v 1)).support) :
    ∀ i j, dist (w i) (w j) ≤ (n : Real) / (n + 1) * D := by
  classical
  induction n generalizing D with
  | zero =>
      intro i j
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      simp
  | succ n ih =>
      rw [integralOrderedSubdivision_single_succ] at hw
      change w ∈ (Finsupp.mapDomain
        (fun t : Fin (n + 1) → integralSimplex d =>
          Fin.cons (α := fun _ : Fin (n + 2) => integralSimplex d)
            (integralSimplexBarycenter d (n + 1) v) t)
        (integralOrderedSubdivision (integralSimplexBarycenter d) (n + 1)
          (integralOrderedBoundary (integralSimplex d) (n + 1)
            (Finsupp.single v 1)))).support at hw
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
      rw [integralOrderedBoundary_single, map_sum] at ht
      simp only [map_smul] at ht
      obtain ⟨a, _, hta⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum ht)
      have hta' := Finsupp.support_smul hta
      have hface (i j : Fin (n + 1)) :
          dist ((v ∘ a.succAbove) i) ((v ∘ a.succAbove) j) ≤ D :=
        hv (a.succAbove i) (a.succAbove j)
      have htail := ih (v ∘ a.succAbove) D hD hface t hta'
      let A : Set (integralSimplex d) :=
        {p | p.val ∈ convexHull Real (Set.range (fun i => (v i).val))}
      have hA (m : Nat) (u : Fin (m + 1) → integralSimplex d)
          (hu : Set.range u ⊆ A) : integralSimplexBarycenter d m u ∈ A := by
        change (integralSimplexBarycenter d m u).val ∈
          convexHull Real (Set.range (fun i => (v i).val))
        rw [integralSimplexBarycenter_val, Finset.smul_sum]
        apply (convex_convexHull Real _).sum_mem
        · intro i _
          positivity
        · have hm : (m + 1 : Real) ≠ 0 := by positivity
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          exact mul_inv_cancel₀ hm
        · intro i _
          exact hu ⟨i, rfl⟩
      have hunit : ∀ u ∈ (Finsupp.single (v ∘ a.succAbove) (1 : Int)).support,
          Set.range u ⊆ A := by
        intro u hu
        have he : u = v ∘ a.succAbove := ((Finsupp.mem_support_single _ _ _).mp hu).1
        subst u
        rintro _ ⟨j, rfl⟩
        exact subset_convexHull Real _ ⟨a.succAbove j, rfl⟩
      have htA : Set.range t ⊆ A :=
        integralOrderedSubdivision_support (integralSimplexBarycenter d)
          A hA (n + 1) _ hunit t hta'
      have hcenter (j : Fin (n + 1)) :
          dist (integralSimplexBarycenter d (n + 1) v) (t j) ≤
            ((n + 1 : Nat) : Real) / (((n + 1 : Nat) : Real) + 1) * D :=
        integralSimplexBarycenter_dist_le v D hD hv (t j) (htA ⟨j, rfl⟩)
      have hfactor : (n : Real) / (n + 1) ≤
          ((n + 1 : Nat) : Real) / (((n + 1 : Nat) : Real) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      have hR : 0 ≤ ((n + 1 : Nat) : Real) /
          (((n + 1 : Nat) : Real) + 1) * D := by positivity
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [dist_self] using hR
        · exact hcenter j
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [Fin.cons_succ, Fin.cons_zero, dist_comm] using hcenter i
        · exact (htail i j).trans (mul_le_mul_of_nonneg_right hfactor hD)

theorem integralSimplexSubdivision_iterate_mesh {d n : Nat}
    (r : Nat) (v : Fin (n + 1) → integralSimplex d)
    (D : Real) (hD : 0 ≤ D) (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (w : Fin (n + 1) → integralSimplex d)
    (hw : w ∈ (((integralOrderedSubdivision (integralSimplexBarycenter d)
      (n + 1)) ^ r) (Finsupp.single v 1)).support) :
    ∀ i j, dist (w i) (w j) ≤ ((n : Real) / (n + 1)) ^ r * D := by
  classical
  induction r generalizing w with
  | zero =>
      simp only [pow_zero, Module.End.one_apply, Finsupp.mem_support_single] at hw
      obtain ⟨rfl, _⟩ := hw
      simpa only [pow_zero, one_mul] using hv
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply] at hw
      let c := ((integralOrderedSubdivision (integralSimplexBarycenter d)
        (n + 1)) ^ r) (Finsupp.single v 1)
      change w ∈ (c.sum (fun u a => a • integralOrderedCone n
        (integralSimplexBarycenter d n u)
        (integralOrderedSubdivision (integralSimplexBarycenter d) n
          (integralOrderedBoundary (integralSimplex d) n
            (Finsupp.single u 1))))).support at hw
      obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
      have hwu' : w ∈ (integralOrderedSubdivision (integralSimplexBarycenter d)
          (n + 1) (Finsupp.single u 1)).support := by
        rw [integralOrderedSubdivision_single_succ]
        exact Finsupp.support_smul hwu
      have huD := ih u hu
      have hbound := integralSimplexSubdivision_mesh u
        (((n : Real) / (n + 1)) ^ r * D) (by positivity) huD w hwu'
      simpa only [pow_succ', mul_assoc] using hbound

end Poincare.Topology
