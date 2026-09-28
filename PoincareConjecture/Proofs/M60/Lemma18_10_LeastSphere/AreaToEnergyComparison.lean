import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaToEnergyLimit
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaToEnergyVolume









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60EnergyDensity_comp_le_of_differential_le (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (q : RiemannianMetric 2 UnitTwoSphere) (F : LoopPlane → UnitTwoSphere)
    (hF : ContMDiff (𝓡 2) (𝓡 2) 1 F)
    (hbound : ∀ (p : UnitTwoSphere) (v : TangentSpace (𝓡 2) p),
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v) ≤
        q.inner p v v) (z : LoopPlane) :
    m60EnergyDensity g (f ∘ F) z ≤ m60EnergyDensity q F z := by
  have h (i : Fin 2) := hbound (F z)
    (mfderiv (𝓡 2) (𝓡 2) F z (EuclideanSpace.basisFun (Fin 2) ℝ i))
  unfold m60EnergyDensity
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  unfold m60AreaGram
  rw [mfderiv_comp z (hf.mdifferentiable (by simp) _) (hF.mdifferentiable (by simp) _)]
  change (1 / 2 : ℝ) *
      (g.inner (f (F z)) _ _ + g.inner (f (F z)) _ _) ≤
    (1 / 2 : ℝ) * (q.inner (F z) _ _ + q.inner (F z) _ _)
  exact mul_le_mul_of_nonneg_left (add_le_add (h 0) (h 1)) (by norm_num)



theorem m60SphereEnergy_comp_le_of_differential_le (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (q : RiemannianMetric 2 UnitTwoSphere) (phi : UnitTwoSphere → UnitTwoSphere)
    (hphi : ContMDiff (𝓡 2) (𝓡 2) 1 phi)
    (hbound : ∀ (p : UnitTwoSphere) (v : TangentSpace (𝓡 2) p),
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v) ≤
        q.inner p v v) :
    m60SphereEnergy g (f ∘ phi) ≤ m60SphereEnergy q phi := by
  apply integral_mono (m60SphereEnergyDensity_integrable g (f ∘ phi) (hf.comp hphi))
    (m60SphereEnergyDensity_integrable q phi hphi)
  intro z
  exact m60EnergyDensity_comp_le_of_differential_le g f hf q
    (phi ∘ m60SphereParameter) (hphi.comp (m60SphereParameter_contMDiff.of_le (by simp)))
    hbound z




theorem m60SphereRegularizedMetric_energy_comp_le_area (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (delta : ℝ) (hdelta : 0 < delta)
    (phi : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (hphi : M60WeaklyConformal (m60SphereRegularizedMetric g f hf delta hdelta) phi) :
    m60SphereEnergy g (f ∘ phi) ≤
      m60SphereArea (m60SphereRegularizedMetric g f hf delta hdelta) id := by
  let q := m60SphereRegularizedMetric g f hf delta hdelta
  calc
    _ ≤ m60SphereEnergy q phi := m60SphereEnergy_comp_le_of_differential_le g f
      (hf.of_le (by simp)) q phi (phi.contMDiff.of_le (by simp))
      (m60SphereRegularizedMetric_dominates g f hf delta hdelta)
    _ = m60SphereArea q phi :=
      (m60SphereArea_eq_energy_of_weaklyConformal q phi
        (phi.contMDiff.of_le (by simp)) hphi).symm
    _ = _ := m60SphereMetric_area_diffeomorph_eq q phi



theorem m60IsNullHomotopicSphere_comp_homeomorph (f : UnitTwoSphere → M)
    (phi : UnitTwoSphere ≃ₜ UnitTwoSphere) :
    IsNullHomotopicSphere (f ∘ phi) ↔ IsNullHomotopicSphere f := by
  constructor
  · rintro ⟨hc, p, hp⟩
    have hf : Continuous f := by
      simpa only [Function.comp_def, phi.apply_symm_apply] using hc.comp phi.symm.continuous
    refine ⟨hf, p, ?_⟩
    have h := hp.comp (ContinuousMap.Homotopic.refl
      (⟨phi.symm, phi.symm.continuous⟩ : ContinuousMap UnitTwoSphere UnitTwoSphere))
    convert h using 1 <;> ext x <;> simp
  · rintro ⟨hf, p, hp⟩
    refine ⟨hf.comp phi.continuous, p, ?_⟩
    exact hp.comp (ContinuousMap.Homotopic.refl
      (⟨phi, phi.continuous⟩ : ContinuousMap UnitTwoSphere UnitTwoSphere))




theorem m60SmoothSphereAreaToEnergy_of_uniformization
    (huniform : ∀ q : RiemannianMetric 2 UnitTwoSphere,
      ∃ phi : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere, M60WeaklyConformal q phi)
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (eta : ℝ) (heta : 0 < eta) :
    ∃ h : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) ∞ h ∧
      m60SphereEnergy g h < m60SphereArea g f + eta ∧
      (IsNullHomotopicSphere h → IsNullHomotopicSphere f) := by
  obtain ⟨delta, hdelta, harea⟩ :=
    m60SphereRegularizedMetric_exists_area_lt g f hf eta heta
  obtain ⟨phi, hphi⟩ := huniform (m60SphereRegularizedMetric g f hf delta hdelta)
  refine ⟨f ∘ phi, hf.comp phi.contMDiff, ?_, ?_⟩
  · exact (m60SphereRegularizedMetric_energy_comp_le_area
      g f hf delta hdelta phi hphi).trans_lt harea
  · exact (m60IsNullHomotopicSphere_comp_homeomorph f phi.toHomeomorph).mp

end PoincareConjecture
