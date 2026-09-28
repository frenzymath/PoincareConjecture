import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Field











open Set
open scoped Topology ContDiff Manifold Bundle

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.M28.Comparison

open ConnectionAlongCurve ConnectionVariation ConjugateFrame ConjugateVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_affine_field_with_index_bound
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {γ : ℝ → M} {I : Set ℝ} {e : ℝ} (he : 0 < e) (hI : IsOpen I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (hsub : Icc (-e) (1 + e) ⊆ I)
    (w : EuclideanSpace ℝ (Fin n))
    (hsec : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v z : TangentSpace (𝓡 n) (γ t),
      0 ≤ D.curvatureTensor (γ t) v z v z) :
    ∃ V : ℝ → EuclideanSpace ℝ (Fin n),
      (∀ t ∈ Ioo (-e) (1 + e), ContDiffAt ℝ ∞ (chartField γ (γ t) V) t) ∧
      V 0 = 0 ∧ V 1 = w ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        intrinsicIndexIntegrand g D γ V t ≤ g.inner (γ 1) w w := by
  obtain ⟨P, hi, hP, hp⟩ := exists_orthonormal_parallel_transport g
    (show -e < 1 + e by linarith) hI hγ hsub
  let v := (P 1).inverse w
  let V : ℝ → EuclideanSpace ℝ (Fin n) := fun t => P t (t • v)
  have h1 : (1 : ℝ) ∈ Icc (-e) (1 + e) := ⟨by linarith, by linarith⟩
  have hv : P 1 v = w := (hi 1 h1).self_apply_inverse w
  have hpair : inner ℝ v v = g.inner (γ 1) w w := by
    rw [← hp 1 h1 v v, hv]
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact contDiffAt_frame_field
      (fun u => (hP t (Ioo_subset_Icc_self ht) u).1)
      (contDiffAt_id.smul contDiffAt_const)
  · simp [V]
  · simpa [V] using hv
  · intro t ht
    have ht' : t ∈ Ioo (-e) (1 + e) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htI := hsub (Ioo_subset_Icc_self ht')
    have hγt := hγ.contMDiffAt (hI.mem_nhds htI)
    have hder : deriv (fun s : ℝ => s • v) t = v := by
      simpa using ((hasDerivAt_id t).smul_const v).deriv
    have hDV : manifoldCovDerivAlong g γ V 1 t = P t v := by
      change manifoldCovDerivAlong g γ (fun s => P s (s • v)) 1 t = _
      rw [covDeriv_frame_field (W := fun s : ℝ => s • v)
        ht' hi hγt (hP t (Ioo_subset_Icc_self ht'))
        (contDiffAt_id.smul contDiffAt_const), hder]
    have hcurv := hsec t ht (V t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
    unfold intrinsicIndexIntegrand
    rw [hDV, hp t (Ioo_subset_Icc_self ht') v v, hpair]
    exact sub_le_self _ (by simpa only [LeviCivitaData.curvatureTensor] using hcurv)

end PoincareConjecture.M28.Comparison
end
