import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzDiskArea
import PoincareConjecture.Proofs.M60.Filling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

private theorem metric_self_nonneg (g : RiemannianMetric 3 M) (x : M)
    (v : TangentSpace (𝓡 3) x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le


theorem m66_gram_det_le_of_metric_le (g h : RiemannianMetric 3 M)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ c * g.inner x v v)
    (x : M) (u v : TangentSpace (𝓡 3) x) :
    h.inner x u u * h.inner x v v - (h.inner x u v) ^ 2 ≤
      c ^ 2 * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
  by_cases hu : u = 0
  · simp [hu]
  have hgu : 0 < g.inner x u u := g.pos x u hu
  let a := g.inner x u v / g.inner x u u
  let w := v - a • u
  have hidentity (k : RiemannianMetric 3 M) :
      k.inner x u u * k.inner x v v - (k.inner x u v) ^ 2 =
        k.inner x u u * k.inner x w w - (k.inner x u w) ^ 2 := by
    dsimp [w]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [k.symm x v u]
    ring
  have horth : g.inner x u w = 0 := by
    dsimp [w, a]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  rw [hidentity h, hidentity g, horth, zero_pow (by decide : 2 ≠ 0), sub_zero]
  calc
    _ ≤ h.inner x u u * h.inner x w w := sub_le_self _ (sq_nonneg _)
    _ ≤ (c * g.inner x u u) * (c * g.inner x w w) :=
      mul_le_mul (hbound x u) (hbound x w) (metric_self_nonneg h x w)
        (mul_nonneg hc hgu.le)
    _ = _ := by ring


theorem m66_area_density_le_of_metric_le (g h : RiemannianMetric 3 M)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ c * g.inner x v v)
    (f : LoopPlane → M) (z : LoopPlane) :
    parametrizedAreaDensity h f z ≤ c * parametrizedAreaDensity g f z := by
  let e := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 3) f z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hdet := m66_gram_det_le_of_metric_le g h hc hbound (f z) (e 0) (e 1)
  have hdet' : Matrix.det (m60AreaGram h f z) ≤
      c ^ 2 * Matrix.det (m60AreaGram g f z) := by
    unfold m60AreaGram
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    change h.inner (f z) (e 0) (e 0) * h.inner (f z) (e 1) (e 1) -
      h.inner (f z) (e 0) (e 1) * h.inner (f z) (e 1) (e 0) ≤ _
    rw [h.symm (f z) (e 1) (e 0), g.symm (f z) (e 1) (e 0)]
    simpa only [pow_two] using hdet
  change Real.sqrt (max 0 (Matrix.det (m60AreaGram h f z))) ≤
    c * Real.sqrt (max 0 (Matrix.det (m60AreaGram g f z)))
  rw [max_eq_right (m60AreaGram_det_nonneg h f z),
    max_eq_right (m60AreaGram_det_nonneg g f z)]
  calc
    _ ≤ Real.sqrt (c ^ 2 * Matrix.det (m60AreaGram g f z)) := Real.sqrt_le_sqrt hdet'
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]


noncomputable def m66TransferDisk [T2Space M]
    (g h : RiemannianMetric 3 M) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ c * g.inner x v v)
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ) :
    LipschitzSpanningDisk h γ := by
  have hC : 0 ≤ Real.sqrt c * D.lipschitz_constant :=
    mul_nonneg (Real.sqrt_nonneg _) D.lipschitz_nonnegative
  have hLip : ∀ x y : LoopDisk,
      h.edist (D.map x) (D.map y) ≤
        ENNReal.ofReal (Real.sqrt c * D.lipschitz_constant) *
          ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    have he := g.edist_le_mul_of_inner_mfderiv_le h
      (F := id) contMDiff_id (Real.sqrt_pos.mpr hc)
      (fun z v => by
        simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply,
          Real.sq_sqrt hc.le] using hbound z v) (D.map x) (D.map y)
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt c) * g.edist (D.map x) (D.map y) := he
      _ ≤ ENNReal.ofReal (Real.sqrt c) *
          (ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :=
        mul_le_mul_right (D.lipschitz_on_disk x y) _
      _ = _ := by rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]
  exact {
    map := D.map
    continuous_on_disk := D.continuous_on_disk
    ae_manifold_differentiable := D.ae_manifold_differentiable
    reparameterization := D.reparameterization
    boundary_eq := D.boundary_eq
    lipschitz_constant := Real.sqrt c * D.lipschitz_constant
    lipschitz_nonnegative := hC
    lipschitz_on_disk := hLip
    area_integrable := m60AreaDensity_integrableOn_of_disk_lipschitz h hC hLip
    area_nonnegative := integral_nonneg (fun _ => Real.sqrt_nonneg _) }


theorem m66TransferDisk_area_le [T2Space M]
    (g h : RiemannianMetric 3 M) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ c * g.inner x v v)
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ) :
    (m66TransferDisk g h hc hbound D).area ≤ c * D.area := by
  change (∫ z in loopDiskSet, parametrizedAreaDensity h D.map z) ≤
    c * ∫ z in loopDiskSet, parametrizedAreaDensity g D.map z
  rw [← integral_const_mul]
  exact integral_mono (m66TransferDisk g h hc hbound D).area_integrable
    (D.area_integrable.const_mul c) (m66_area_density_le_of_metric_le g h hc.le hbound D.map)


theorem m66_fillingArea_le_of_metric_le [T2Space M]
    (g h : RiemannianMetric 3 M) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      h.inner x v v ≤ c * g.inner x v v)
    {d : ℝ} (hd : 0 < d)
    (hreverse : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ d * h.inner x v v)
    (γ : C1FreeLoopSpace (M := M)) :
    fillingArea h γ ≤ c * fillingArea g γ := by
  classical
  by_cases hnonempty : Nonempty (LipschitzSpanningDisk g γ)
  swap
  · have hg : Set.range (fun D : LipschitzSpanningDisk g γ => D.area) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨D, rfl⟩
      exact hnonempty ⟨D⟩
    have hh : Set.range (fun D : LipschitzSpanningDisk h γ => D.area) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨D, rfl⟩
      exact hnonempty ⟨m66TransferDisk h g hd hreverse D⟩
    simp only [fillingArea, hg, hh, Real.sInf_empty, mul_zero, le_refl]
  obtain ⟨D⟩ := hnonempty
  have hle : fillingArea h γ / c ≤ fillingArea g γ := by
    change fillingArea h γ / c ≤ sInf (Set.range (fun E : LipschitzSpanningDisk g γ => E.area))
    apply le_csInf (show (Set.range (fun E : LipschitzSpanningDisk g γ => E.area)).Nonempty
      from ⟨D.area, D, rfl⟩)
    rintro _ ⟨E, rfl⟩
    apply (div_le_iff₀ hc).mpr
    calc
      _ ≤ (m66TransferDisk g h hc hbound E).area :=
        m60FillingArea_le_disk h γ _
      _ ≤ c * E.area := m66TransferDisk_area_le g h hc hbound E
      _ = _ := mul_comm _ _
  exact (div_le_iff₀ hc).mp hle |>.trans_eq (mul_comm _ _)

end PoincareConjecture
