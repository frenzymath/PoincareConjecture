import PoincareConjecture.Proofs.M03.CurvatureExtension









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvature_pair_skew {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M)
    (u v z w : TangentSpace (𝓡 n) x) :
    g.inner x (D.curvature x u v z) w =
      -g.inner x z (D.curvature x u v w) := by
  obtain ⟨U, hU, hu⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  obtain ⟨V, hV, hv⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨Z, hZ, hz⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) z
  obtain ⟨W, hW, hw⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨S, hS, hSopen, hxS⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hU (Filter.inter_mem hV (Filter.inter_mem hZ hW)))
  have h := curvatureOnFields_pair_skew D hSopen
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w)
    (hu.mono fun _ hy => (hS hy).1)
    (hv.mono fun _ hy => (hS hy).2.1)
    (hz.mono fun _ hy => (hS hy).2.2.1)
    (hw.mono fun _ hy => (hS hy).2.2.2) hxS
  simp only [FiberBundle.extend_apply_self] at h
  exact h

theorem exists_curvature_trilinearMap {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) :
    ∃ R : TangentSpace (𝓡 n) x →ₗ[ℝ]
        TangentSpace (𝓡 n) x →ₗ[ℝ]
        TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x,
      ∀ u v w, R u v w = D.curvature x u v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB (z : TangentSpace (𝓡 n) x) :
      ∃ B : TangentSpace (𝓡 n) x →L[ℝ]
          TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
        ∀ u v, B u v = D.curvature x u v z := by
    obtain ⟨U, hU, hz⟩ :=
      FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) z
    obtain ⟨S, hS, hSopen, hxS⟩ := mem_nhds_iff.mp hU
    refine ⟨TensorialAt.mkHom₂
      (fun X Y => D.curvatureOnFields X Y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) x
      (fun Y _ => curvatureOnFields_tensorial_first D hSopen Y _ (hz.mono hS) hxS)
      (fun X _ => curvatureOnFields_tensorial_second D hSopen X _ (hz.mono hS) hxS), ?_⟩
    intro u v
    rfl
  let Q (u v : TangentSpace (𝓡 n) x) :
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x := {
    toFun := D.curvature x u v
    map_add' := by
      intro z z'
      apply ext_inner_right ℝ
      intro w
      change g.inner x (D.curvature x u v (z + z')) w =
        g.inner x (D.curvature x u v z + D.curvature x u v z') w
      simp only [map_add, add_apply, curvature_pair_skew, neg_add]
    map_smul' := by
      intro c z
      apply ext_inner_right ℝ
      intro w
      change g.inner x (D.curvature x u v (c • z)) w =
        g.inner x (c • D.curvature x u v z) w
      simp only [curvature_pair_skew, map_smul, smul_apply, smul_neg] }
  refine ⟨LinearMap.mk₂ ℝ Q ?_ ?_ ?_ ?_, ?_⟩
  · intro u u' v
    ext z
    obtain ⟨B, hB⟩ := hB z
    change D.curvature x (u + u') v z = D.curvature x u v z + D.curvature x u' v z
    rw [← hB, ← hB, ← hB, map_add, add_apply]
  · intro c u v
    ext z
    obtain ⟨B, hB⟩ := hB z
    change D.curvature x (c • u) v z = c • D.curvature x u v z
    rw [← hB, ← hB, map_smul, smul_apply]
  · intro u v v'
    ext z
    obtain ⟨B, hB⟩ := hB z
    change D.curvature x u (v + v') z = D.curvature x u v z + D.curvature x u v' z
    rw [← hB, ← hB, ← hB, map_add]
  · intro c u v
    ext z
    obtain ⟨B, hB⟩ := hB z
    change D.curvature x u (c • v) z = c • D.curvature x u v z
    rw [← hB, ← hB, map_smul]
  · intro u v z
    rfl

end PoincareConjecture.Proofs.M03
