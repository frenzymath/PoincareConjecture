import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusLipschitzSeed












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64ObservedMetric_diagonal_of_mDifferentiableAt
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    {f : LoopPlane → M} {p : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p)
    (i : Fin 2) :
    B (f p) (fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1))
      (fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1)) = m60AreaGram g f p i i := by
  have hh := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 n) (I'' := 𝓡 m)
    (f := f) (g := e) p (he.mdifferentiable (by simp) _) hf
  have hc := congrArg (fun L => L (EuclideanSpace.single i 1)) hh
  rw [mfderiv_eq_fderiv] at hc
  change fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1) =
    mfderiv (𝓡 n) (𝓡 m) e (f p)
      (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.single i 1)) at hc
  erw [hc, hdiag]
  simp only [m60AreaGram, EuclideanSpace.basisFun_apply]



theorem m64ObservedWeakAnnulus_seed_energyDensity_eq_ae
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1) (hmap : W.map = A.map)
    (hcol : ∀ i, ∀ᵐ p ∂mu, W.column i p =
      fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1)) :
    ∀ᵐ p ∂mu, (B (W.map p) (W.column 0 p) (W.column 0 p) +
      B (W.map p) (W.column 1 p) (W.column 1 p)) / 2 = m60EnergyDensity g A.map p := by
  filter_upwards [hcol 0, hcol 1, ae_restrict_of_ae A.ae_manifold_differentiable,
    ae_restrict_mem isOpen_interior.measurableSet] with p h0 h1 hp hm
  rw [hmap, h0, h1]
  rw [m64ObservedMetric_diagonal_of_mDifferentiableAt g e he B hdiag (hp (interior_subset hm)) 0,
    m64ObservedMetric_diagonal_of_mDifferentiableAt g e he B hdiag (hp (interior_subset hm)) 1]
  simp only [m60EnergyDensity, Matrix.trace_fin_two]
  ring



theorem m64ObservedWeakAnnulus_seed_energy_eq
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1) (hmap : W.map = A.map)
    (hcol : ∀ i, ∀ᵐ p ∂mu, W.column i p =
      fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1)) :
    W.energy B = ∫ p in S, m60EnergyDensity g A.map p :=
  integral_congr_ae (m64ObservedWeakAnnulus_seed_energyDensity_eq_ae A e he B hdiag W hmap hcol)



theorem m64ObservedWeakAnnulus_exists_seed_with_energy [CompactSpace M]
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1, W.map = A.map ∧
      W.energy B = ∫ p in S, m60EnergyDensity g A.map p := by
  obtain ⟨W, hmap, hcols⟩ := m64ObservedWeakAnnulus_of_annulus A e he
  exact ⟨W, hmap, m64ObservedWeakAnnulus_seed_energy_eq A e he B hdiag W hmap hcols⟩

end PoincareConjecture
