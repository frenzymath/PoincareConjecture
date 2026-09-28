import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

noncomputable def coordinateCircleArc (c : EuclideanSpace ℝ (Fin 2)) (r a : ℝ) :
    ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t => Complex.orthonormalBasisOneI.repr
    (circleMap (Complex.orthonormalBasisOneI.repr.symm c) r (a + t * Real.pi))

theorem coordinateCircleArc_mem_sphere (c : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 ≤ r) (a t : ℝ) :
    coordinateCircleArc c r a t ∈ sphere c r := by
  have himage := Complex.orthonormalBasisOneI.repr.image_sphere
    (Complex.orthonormalBasisOneI.repr.symm c) r
  rw [LinearIsometryEquiv.apply_symm_apply] at himage
  rw [← himage]
  exact ⟨_, circleMap_mem_sphere _ hr _, rfl⟩

theorem coordinateCircleArc_injOn (c : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) (a : ℝ) :
    InjOn (coordinateCircleArc c r a) (Icc (0 : ℝ) 1) := by
  intro s hs t ht heq
  have hangle := eq_of_circleMap_eq hr.ne'
    (show |(a + s * Real.pi) - (a + t * Real.pi)| < 2 * Real.pi from by
      rw [abs_lt]
      constructor <;> nlinarith [Real.pi_pos,
        mul_nonneg hs.1 Real.pi_pos.le, mul_nonneg ht.1 Real.pi_pos.le,
        mul_le_mul_of_nonneg_right hs.2 Real.pi_pos.le,
        mul_le_mul_of_nonneg_right ht.2 Real.pi_pos.le])
    (Complex.orthonormalBasisOneI.repr.injective heq)
  nlinarith [Real.pi_pos]

theorem coordinateCircleArc_inter_subset_endpoints
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    coordinateCircleArc c r a '' Icc (0 : ℝ) 1 ∩
        coordinateCircleArc c r (a + Real.pi) '' Icc (0 : ℝ) 1 ⊆
      {coordinateCircleArc c r a 0, coordinateCircleArc c r a 1} := by
  rintro x ⟨⟨t, ht, rfl⟩, ⟨u, hu, heq⟩⟩
  by_cases htzero : t = 0
  · exact Or.inl (congrArg (coordinateCircleArc c r a) htzero)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  have hangle := eq_of_circleMap_eq hr.ne'
    (show |(a + t * Real.pi) - (a + Real.pi + u * Real.pi)| < 2 * Real.pi from by
      rw [abs_lt]
      constructor <;> nlinarith [Real.pi_pos,
        mul_pos htpos Real.pi_pos, mul_nonneg hu.1 Real.pi_pos.le,
        mul_le_mul_of_nonneg_right ht.2 Real.pi_pos.le,
        mul_le_mul_of_nonneg_right hu.2 Real.pi_pos.le])
    (Complex.orthonormalBasisOneI.repr.injective heq.symm)
  have htone : t = 1 := by
    apply le_antisymm ht.2
    apply le_of_mul_le_mul_right (a := Real.pi) _ Real.pi_pos
    nlinarith [mul_nonneg hu.1 Real.pi_pos.le]
  exact Or.inr (congrArg (coordinateCircleArc c r a) htone)

theorem finite_inter_coordinateCircleArc_images
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    {i j : Fin 2} (hij : i ≠ j) :
    (coordinateCircleArc c r ((i : ℝ) * Real.pi) '' Icc (0 : ℝ) 1 ∩
      coordinateCircleArc c r ((j : ℝ) * Real.pi) '' Icc (0 : ℝ) 1).Finite := by
  have hfinite : (coordinateCircleArc c r 0 '' Icc (0 : ℝ) 1 ∩
      coordinateCircleArc c r Real.pi '' Icc (0 : ℝ) 1).Finite :=
    ((finite_singleton (coordinateCircleArc c r 0 1)).insert
      (coordinateCircleArc c r 0 0)).subset
      (by simpa using coordinateCircleArc_inter_subset_endpoints c hr 0)
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa using hfinite
  · simpa [inter_comm] using hfinite
  · exact (hij rfl).elim

theorem coordinateCircleArc_contDiff (c : EuclideanSpace ℝ (Fin 2)) (r a : ℝ) :
    ContDiff ℝ ∞ (coordinateCircleArc c r a) :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.comp
    ((contDiff_circleMap _ _).comp (contDiff_const.add (contDiff_id.mul contDiff_const)))

theorem coordinateCircleArc_fderiv_injective
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (a t : ℝ) :
    Function.Injective (fderiv ℝ (coordinateCircleArc c r a) t) := by
  let E := Complex.orthonormalBasisOneI.repr
  let v := Real.pi • (circleMap 0 r (a + t * Real.pi) * Complex.I)
  have hd : HasDerivAt (coordinateCircleArc c r a) (E v) t := by
    exact E.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_circleMap _ _ _).scomp t
        (by simpa using ((hasDerivAt_id t).mul_const Real.pi).const_add a))
  have hv : v ≠ 0 := by
    apply smul_ne_zero Real.pi_ne_zero
    exact mul_ne_zero (circleMap_ne_center hr.ne') Complex.I_ne_zero
  have hEv : E v ≠ 0 := fun h => hv (E.injective (by simpa using h))
  rw [hd.hasFDerivAt.fderiv]
  exact smul_left_injective ℝ hEv

theorem coordinateCircleArc_deriv_ne_zero
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (a t : ℝ) :
    deriv (coordinateCircleArc c r a) t ≠ 0 := by
  intro h
  apply one_ne_zero (α := ℝ)
  apply coordinateCircleArc_fderiv_injective c hr a t
  simpa only [fderiv_apply_one_eq_deriv, map_zero] using h

theorem coordinateCircleArc_affine_contDiff
    (c : EuclideanSpace ℝ (Fin 2)) (r θ a b : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => coordinateCircleArc c r θ (a + t * (b - a))) :=
  (coordinateCircleArc_contDiff c r θ).comp
    (contDiff_const.add (contDiff_id.mul contDiff_const))

theorem coordinateCircleArc_affine_deriv_ne_zero
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (θ : ℝ)
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    deriv (fun u : ℝ => coordinateCircleArc c r θ (a + u * (b - a))) t ≠ 0 := by
  have hinner : HasDerivAt (fun u : ℝ => a + u * (b - a)) (b - a) t := by
    simpa using ((hasDerivAt_id t).mul_const (b - a)).const_add a
  have houter := ((coordinateCircleArc_contDiff c r θ).differentiable
    (by simp)).differentiableAt (x := a + t * (b - a)) |>.hasDerivAt
  change deriv (coordinateCircleArc c r θ ∘ fun u : ℝ => a + u * (b - a)) t ≠ 0
  rw [(houter.scomp t hinner).deriv]
  exact smul_ne_zero (sub_ne_zero.mpr hab.ne')
    (coordinateCircleArc_deriv_ne_zero c hr θ _)

theorem coordinateCircleArc_affine_injOn
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (θ : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    InjOn (fun t : ℝ => coordinateCircleArc c r θ (a + t * (b - a)))
      (Icc (0 : ℝ) 1) := by
  have hparameter {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      a + t * (b - a) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab.le),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab.le)]
  intro s hs t ht h
  have heq := coordinateCircleArc_injOn c hr θ (hparameter hs) (hparameter ht) h
  exact mul_right_cancel₀ (sub_ne_zero.mpr hab.ne') (add_left_cancel heq)

theorem iUnion_coordinateCircleArc_image (c : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) :
    (⋃ i : Fin 2, coordinateCircleArc c r ((i : ℝ) * Real.pi) '' Icc (0 : ℝ) 1) =
      sphere c r := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hx
    exact coordinateCircleArc_mem_sphere c hr.le _ _
  · intro x hx
    let E := Complex.orthonormalBasisOneI.repr
    have hx' : E.symm x ∈ sphere (E.symm c) r := by
      change dist (E.symm x) (E.symm c) = r
      rw [E.symm.dist_map]
      exact hx
    rw [← abs_of_pos hr, ← image_circleMap_Ioc] at hx'
    obtain ⟨θ, hθ, hmap⟩ := hx'
    by_cases hθpi : θ ≤ Real.pi
    · refine mem_iUnion.mpr ⟨0, θ / Real.pi, ?_, ?_⟩
      · exact ⟨(div_pos hθ.1 Real.pi_pos).le, (div_le_one Real.pi_pos).mpr hθpi⟩
      · simp only [coordinateCircleArc, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add,
          div_mul_cancel₀ _ Real.pi_ne_zero]
        exact (congrArg E hmap).trans (E.apply_symm_apply x)
    · refine mem_iUnion.mpr ⟨1, (θ - Real.pi) / Real.pi, ?_, ?_⟩
      · constructor
        · exact div_nonneg (by linarith) Real.pi_pos.le
        · apply (div_le_one Real.pi_pos).mpr
          linarith [hθ.2]
      · simp only [coordinateCircleArc, Fin.val_one, Nat.cast_one, one_mul,
          div_mul_cancel₀ _ Real.pi_ne_zero, add_sub_cancel]
        exact (congrArg E hmap).trans (E.apply_symm_apply x)

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

theorem finite_inter_chartCircleArc_images (p : M)
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (hcircle : sphere c r ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target)
    {i j : Fin 2} (hij : i ≠ j) :
    (((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘
        coordinateCircleArc c r ((i : ℝ) * Real.pi)) '' Icc (0 : ℝ) 1 ∩
      ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘
        coordinateCircleArc c r ((j : ℝ) * Real.pi)) '' Icc (0 : ℝ) 1).Finite := by
  have hsub (k : Fin 2) : coordinateCircleArc c r ((k : ℝ) * Real.pi) '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).target := by
    rintro x ⟨t, ht, rfl⟩
    exact hcircle (coordinateCircleArc_mem_sphere c hr.le _ _)
  rw [image_comp, image_comp,
    ← (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm.injOn.image_inter (hsub i) (hsub j)]
  exact (finite_inter_coordinateCircleArc_images c hr hij).image _

variable [IsManifold (𝓡 2) ∞ M]

theorem exists_smoothEdge_of_coordinateCircleArc (p : M)
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (a : ℝ)
    (hcircle : sphere c r ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) :
    ∃ e : SmoothEdge M,
      e.map = (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘ coordinateCircleArc c r a ∧
      InjOn e.map (Icc (0 : ℝ) 1) := by
  have htarget (t : ℝ) := hcircle (coordinateCircleArc_mem_sphere c hr.le a t)
  let e : SmoothEdge M := {
    map := (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘ coordinateCircleArc c r a
    smooth := (contMDiffOn_chart_symm (I := 𝓡 2) (x := p)).comp
      (coordinateCircleArc_contDiff c r a).contMDiff.contMDiffOn (fun t _ => htarget t)
    regular := by
      intro t ht
      rw [mfderiv_comp t
        ((mdifferentiable_chart (I := 𝓡 2) p).mdifferentiableAt_symm (htarget t))
        (((coordinateCircleArc_contDiff c r a).differentiable (by simp)).differentiableAt.mdifferentiableAt),
        mfderiv_eq_fderiv]
      exact ((mdifferentiable_chart (I := 𝓡 2) p).symm.mfderiv_injective (htarget t)).comp
        (coordinateCircleArc_fderiv_injective c hr a t) }
  refine ⟨e, rfl, ?_⟩
  intro s hs t ht heq
  exact coordinateCircleArc_injOn c hr a hs ht
    ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm.injOn (htarget s) (htarget t) heq)

theorem exists_smoothEdges_of_chartCircle (p : M)
    (c : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (hcircle : sphere c r ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) :
    ∃ e : Fin 2 → SmoothEdge M,
      (∀ i, (e i).map = (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘
        coordinateCircleArc c r ((i : ℝ) * Real.pi)) ∧
      (∀ i, InjOn (e i).map (Icc (0 : ℝ) 1)) ∧
      (⋃ i, (e i).map '' Icc (0 : ℝ) 1) =
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' sphere c r := by
  choose e he hinj using fun i : Fin 2 =>
    exists_smoothEdge_of_coordinateCircleArc p c hr ((i : ℝ) * Real.pi) hcircle
  refine ⟨e, he, hinj, ?_⟩
  simp_rw [he, image_comp]
  rw [← image_iUnion, iUnion_coordinateCircleArc_image c hr]

end PoincareConjecture.Topology.Surface
