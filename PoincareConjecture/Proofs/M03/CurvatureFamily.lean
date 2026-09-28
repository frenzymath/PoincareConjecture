import PoincareConjecture.Proofs.M03.ConnectionFamily











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_family_curvatureOnFields_pair
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    {U : Set M} (hU : IsOpen U)
    (X Y Z W : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2
        ((D p.1).curvatureOnFields X Y Z p.2) (W p.2)) (J ×ˢ U) := by
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  have hpair
      (A B : (p : ℝ × M) → TangentSpace (𝓡 n) p.2)
      (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (A p)) (J ×ˢ U))
      (hB : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (B p)) (J ×ˢ U)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p => (g p.1).inner p.2 (A p) (B p)) (J ×ˢ U) := by
    have hp := ContMDiffOn.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace (𝓡 n) x)
      (E₂ := fun x : M => TangentSpace (𝓡 n) x) (E₃ := fun _ : M => ℝ)
      (ψ := fun p : ℝ × M => (g p.1).inner p.2) (b := Prod.snd)
      (hg.mono (Set.prod_mono subset_rfl (subset_univ U))) hA hB
    intro p hpU
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (hp p hpU)).2
  have hW' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (W p.2))
      (J ×ˢ U) := hW.comp contMDiffOn_snd (fun _ hp => hp.2)
  have hYZ := contMDiffOn_connection_family_apply hg D hU Z Y hZ hY
  have hXZ := contMDiffOn_connection_family_apply hg D hU Z X hZ hX
  have hXW := contMDiffOn_connection_family_apply hg D hU W X hW hX
  have hYW := contMDiffOn_connection_family_apply hg D hU W Y hW hY
  have hbr : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mlieBracket (𝓡 n) X Y)) U := by
    intro x hx
    exact ((hX.contMDiffAt (hU.mem_nhds hx)).mlieBracket_vectorField
      (m := ⊤) (n := ⊤) (hY.contMDiffAt (hU.mem_nhds hx)) (by simp)).contMDiffWithinAt
  have hbrZ := contMDiffOn_connection_family_apply hg D hU Z
    (VectorField.mlieBracket (𝓡 n) X Y) hZ hbr
  have hdf := contMDiffOn_family_spatial_mvfderiv
    (f := fun t x => (g t).inner x ((D t).connection Z x (Y x)) (W x))
    hU (hpair _ _ hYZ hW') X hX
  have hdh := contMDiffOn_family_spatial_mvfderiv
    (f := fun t x => (g t).inner x ((D t).connection Z x (X x)) (W x))
    hU (hpair _ _ hXZ hW') Y hY
  have hsum := (((hdf.sub (hpair _ _ hYZ hXW)).sub hdh).add
    (hpair _ _ hXZ hYW)).sub (hpair _ _ hbrZ hW')
  apply hsum.congr
  intro p hp
  have hWpt := (hW.contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp)
  have hYZpt := ((D p.1).contMDiffOn_connection_apply hU Y Z hY hZ).contMDiffAt
    (hU.mem_nhds hp.2)
  have hXZpt := ((D p.1).contMDiffOn_connection_apply hU X Z hX hZ).contMDiffAt
    (hU.mem_nhds hp.2)
  simp only [Pi.add_apply]
  rw [(D p.1).mvfderiv_inner X (fun x => (D p.1).connection Z x (Y x)) W
      (hYZpt.mdifferentiableAt (by simp)) hWpt,
    (D p.1).mvfderiv_inner Y (fun x => (D p.1).connection Z x (X x)) W
      (hXZpt.mdifferentiableAt (by simp)) hWpt]
  delta LeviCivitaData.curvatureOnFields
  simp only [map_sub, sub_apply]
  ring

theorem contDiffOn_family_curvatureTensor_time
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    ContDiffOn ℝ ∞ (fun t => (D t).curvatureTensor x u v w z) J := by
  obtain ⟨Su, hSu, hu⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  obtain ⟨Sv, hSv, hv⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨Sw, hSw, hw⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨Sz, hSz, hz⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) z
  obtain ⟨U, hUsub, hU, hxU⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hSu hSv)
      (Filter.inter_mem hSw hSz))
  have hcurv := contMDiffOn_family_curvatureOnFields_pair hg D hU
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w)
    (hu.mono (fun _ hy => (hUsub hy).1.1))
    (hv.mono (fun _ hy => (hUsub hy).1.2))
    (hz.mono (fun _ hy => (hUsub hy).2.2))
    (hw.mono (fun _ hy => (hUsub hy).2.1))
  have hi : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ => (t, x)) J := contMDiffOn_id.prodMk contMDiffOn_const
  have ht := hcurv.comp hi (fun _ ht => ⟨ht, hxU⟩)
  apply ContMDiffOn.contDiffOn
  change ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
    (fun t => (g t).inner x ((D t).curvatureOnFields
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) w) J
  simpa only [Function.comp_def, FiberBundle.extend_apply_self] using ht

end PoincareConjecture.Proofs.M03
