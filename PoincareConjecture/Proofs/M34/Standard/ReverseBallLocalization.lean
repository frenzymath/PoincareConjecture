import PoincareConjecture.Proofs.M34.Standard.PathBallConfinement











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric





theorem ball_subset_image_ball_of_guarded_inverse_tangentNorm_le
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N] [T3Space M]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : OpenPartialHomeomorph M N)
    (hinv : ContMDiffOn (𝓡 m) (𝓡 n) 1 e.symm e.target)
    {o : M} (ho : o ∈ e.source) {r C : ℝ} (hC : 0 < C)
    (hcover : h.ball (e o) r ⊆ e.target)
    (hbound : ∀ y ∈ e.target, g.edist o (e.symm y) ≤ ENNReal.ofReal (C * r) →
      ∀ v : TangentSpace (𝓡 m) y,
        g.tangentNorm (e.symm y) (mfderiv (𝓡 m) (𝓡 n) e.symm y v) ≤
          C * h.tangentNorm y v) :
    h.ball (e o) r ⊆ e '' (g.ball o (C * r) ∩ e.source) := by
  intro y hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, hγball⟩ := h.exists_short_path_in_ball (e o) y hy
  let η : ℝ → M := e.symm ∘ γ
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 η (Icc (0 : ℝ) 1) :=
    hinv.comp hγ (fun t ht => hcover (hγball ht))
  have hη0 : η 0 = o := by
    change e.symm (γ 0) = o
    rw [hγ0, e.left_inv ho]
  have hscaled : ENNReal.ofReal C * h.pathELength γ 0 1 < ENNReal.ofReal (C * r) := by
    rw [ENNReal.ofReal_mul hC.le]
    exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
      ENNReal.ofReal_ne_top hlength
  have hconf := g.mapsTo_ball_of_local_speed_bound h hη hη0 hC.le (fun t ht hdist => by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htarget : γ t ∈ e.target := hcover (hγball ht')
    have hi := ((hinv (γ t) htarget).contMDiffAt
      (e.open_target.mem_nhds htarget)).mdifferentiableAt (by simp)
    have hg := ((hγ t ht').contMDiffAt
      (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp_apply t hi hg (1 : ℝ)
    change g.tangentNorm (η t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (e.symm ∘ γ) t 1) ≤ _
    rw [hchain]
    exact hbound (γ t) htarget hdist _) hscaled
  refine ⟨e.symm y, ⟨?_, e.map_target (hcover hy)⟩, e.right_inv (hcover hy)⟩
  simpa only [η, Function.comp_apply, hγ1] using hconf (show (1 : ℝ) ∈ Icc 0 1 by norm_num)

end PoincareConjecture.RiemannianMetric
