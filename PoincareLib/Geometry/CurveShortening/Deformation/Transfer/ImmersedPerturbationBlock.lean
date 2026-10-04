import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.Transfer.ImmersedPerturbationDerivative
import PoincareLib.Geometry.CurveShortening.Deformation.GoodTimes.CircleRelabeling

/-!
# Three genuine perturbation controls at a double point

The three velocities are chosen through the actual inverse chart
differential, then realized by actual ambient motions. A genuine source
bump separates the two circle points. Thus the desired coordinate block
is constructed, with one common positive flow interval.
MT Lemma 19.4, pp. 439-441; M65 derivation 49, section 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M65Perturbation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]

/-- At two distinct source points with a prescribed common image, actual
bounded source weights and three actual motions have the coordinate-basis
initial velocities. No transverse block is assumed. MT Lemma 19.4,
pp. 439-441; derivation 49, section 3. -/
theorem exists_double_point_controls (x y : LoopCircle) (hxy : x ≠ y) (z : M) :
    ∃ (d : ℝ) (beta : LoopPlane → ℝ) (Phi : Fin 3 → M × ℝ → M),
      0 < d ∧ ContDiff ℝ ∞ beta ∧ (∀ w, beta w ∈ Icc (0 : ℝ) 1) ∧
      beta x = 1 ∧ beta y = 0 ∧
      (∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
        (univ ×ˢ Ioo (-d) d)) ∧
      (∀ i w, Phi i (w, 0) = w) ∧
      ∀ i, mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient z) z
        (curveVelocity (n := 3) (fun r => Phi i (z, r)) 0) = EuclideanSpace.single i 1 := by
  have hs := (mdifferentiable_chart (I := 𝓡 3) z).mfderiv_surjective (mem_chart_source _ z)
  have hmotion (i : Fin 3) :
      ∃ (d : ℝ) (Phi : M × ℝ → M), 0 < d ∧
        ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ Phi (univ ×ˢ Ioo (-d) d) ∧
        (∀ w, Phi (w, 0) = w) ∧
        mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient z) z
          (curveVelocity (n := 3) (fun r => Phi (z, r)) 0) = EuclideanSpace.single i 1 := by
    obtain ⟨v, hv⟩ := hs (EuclideanSpace.single i 1)
    obtain ⟨d, Phi, hd, hPhi, hzero, hvel⟩ := exists_smooth_motion_with_velocity z v
    exact ⟨d, Phi, hd, hPhi, hzero, by rw [hvel]; exact hv⟩
  choose d Phi hd hPhi hzero hvel using hmotion
  obtain ⟨beta, hbeta, hbound, hx, hy⟩ := exists_source_bump x y hxy
  let delta := min (d 0) (min (d 1) (d 2))
  have hdelta : 0 < delta := lt_min (hd 0) (lt_min (hd 1) (hd 2))
  have hle (i : Fin 3) : delta ≤ d i := by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta, beta, Phi, hdelta, hbeta, hbound, hx, hy, ?_, hzero, hvel⟩
  intro i
  exact (hPhi i).mono (prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (hle i)) (hle i)))

omit [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [CompactSpace M] in
/-- The actual Euclidean source bump gives a genuinely smooth periodic
angular weight bounded by one. MT Lemma 19.4, pp. 439-441;
derivation 49, section 3. -/
theorem source_weight_regular (beta : LoopPlane → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (hbound : ∀ w, beta w ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x => beta (Proofs.M58.angularPoint x)) ∧
      Function.Periodic (fun x => beta (Proofs.M58.angularPoint x)) curvePeriod ∧
      ∀ x, |beta (Proofs.M58.angularPoint x)| ≤ 1 := by
  refine ⟨hbeta.comp Proofs.M58.contDiff_angularPoint, ?_, ?_⟩
  · intro x
    apply congrArg beta
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, curvePeriod, Real.cos_add_two_pi,
      Real.sin_add_two_pi]
  · intro x
    rw [abs_of_nonneg (hbound _).1]
    exact (hbound _).2

end PoincareMT.M65Perturbation
