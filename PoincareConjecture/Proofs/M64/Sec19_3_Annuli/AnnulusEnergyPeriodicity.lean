import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSmoothGram












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

private theorem annulus_map_periodic_add (A : M64Annulus g c0 c1) (p : LoopPlane) :
    A.map (annulusPoint curvePeriod 0 + p) = A.map p := by
  have hp : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  have hshift : annulusPoint curvePeriod 0 + p =
      annulusPoint (p 0 + curvePeriod) (p 1) := by
    ext i
    fin_cases i <;> simp [annulusPoint, add_comm]
  rw [hshift, A.periodic, hp]





theorem m64Annulus_energyDensity_periodic_of_mdifferentiable
    (A : M64Annulus g c0 c1) (p : LoopPlane)
    (hp : MDifferentiableAt (𝓡 2) (𝓡 n) A.map (annulusPoint curvePeriod 0 + p)) :
    m60EnergyDensity g A.map (annulusPoint curvePeriod 0 + p) =
      m60EnergyDensity g A.map p := by
  let T : LoopPlane := annulusPoint curvePeriod 0
  have hshift : HasFDerivAt (fun q : LoopPlane => T + q)
      (ContinuousLinearMap.id ℝ LoopPlane) p := (hasFDerivAt_id p).const_add T
  have hfun : (A.map ∘ fun q : LoopPlane => T + q) = A.map :=
    funext (annulus_map_periodic_add A)
  have hmd : MDifferentiableAt (𝓡 2) (𝓡 2) (fun q : LoopPlane => T + q) p :=
    hshift.differentiableAt.mdifferentiableAt
  have hd := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 n) p hp hmd
  have hT : mfderiv (𝓡 2) (𝓡 2) (fun q : LoopPlane => T + q) p =
      ContinuousLinearMap.id ℝ LoopPlane := by
    rw [mfderiv_eq_fderiv]
    exact hshift.fderiv
  rw [hfun, hT] at hd
  have hd' : mfderiv (𝓡 2) (𝓡 n) A.map p =
      mfderiv (𝓡 2) (𝓡 n) A.map (T + p) := by
    simpa only [ContinuousLinearMap.comp_id] using! hd
  have heq : m60AreaGram g A.map (T + p) = m60AreaGram g A.map p := by
    ext i j
    simp only [m60AreaGram, ← hd']
    exact congrArg (fun x : M => g.inner x
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ j)))
      (annulus_map_periodic_add A p)
  exact congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => (1 / 2 : ℝ) * B.trace) heq





theorem m64Annulus_energy_transform_fderiv_periodic
    (A : M64Annulus g c0 c1) (Phi : ℝ → ℝ) (p : LoopPlane)
    (hp : ContMDiffAt (𝓡 2) (𝓡 n) ∞ A.map (annulusPoint curvePeriod 0 + p)) :
    fderiv ℝ (fun q => Phi (m60EnergyDensity g A.map q)) (annulusPoint curvePeriod 0 + p) =
      fderiv ℝ (fun q => Phi (m60EnergyDensity g A.map q)) p := by
  let T : LoopPlane := annulusPoint curvePeriod 0
  have hnear : ∀ᶠ q in 𝓝 (T + p), ContMDiffAt (𝓡 2) (𝓡 n) 1 A.map q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hp.of_le (by simp))
  have htrans : Tendsto (fun q : LoopPlane => T + q) (𝓝 p) (𝓝 (T + p)) :=
    (continuous_const.add continuous_id).continuousAt.tendsto
  have heq : (fun q => Phi (m60EnergyDensity g A.map (T + q))) =ᶠ[𝓝 p]
      fun q => Phi (m60EnergyDensity g A.map q) := by
    filter_upwards [htrans.eventually hnear] with q hq
    exact congrArg Phi
      (m64Annulus_energyDensity_periodic_of_mdifferentiable A q (hq.mdifferentiableAt one_ne_zero))
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp_add_left (f := fun q => Phi (m60EnergyDensity g A.map q)) T] at hd
  exact hd

end PoincareConjecture
