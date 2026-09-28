import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialChartMetric
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceTensorReadout
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace E M] [ChartedSpace E X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]

omit [IsManifold (𝓡 3) ∞ M] in


theorem terminalCurvature_partial_chart_composed_metric
    (h : RiemannianMetric 3 X)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    {phi : E → M} {psi : M → X} {x : E}
    (hphi : MDifferentiableAt (𝓡 3) (𝓡 3) phi x)
    (hpsi : MDifferentiableAt (𝓡 3) (𝓡 3) psi (phi x))
    (hx : phi x ∈ c.source) :
    (h.pullbackCoefficients (psi ∘ c.symm) (c (phi x))).bilinearComp
        (fderiv ℝ ((c : M → E) ∘ phi) x)
        (fderiv ℝ ((c : M → E) ∘ phi) x) =
      h.pullbackCoefficients (psi ∘ phi) x := by
  have hd := terminalCurvature_partial_chart_inverse_derivative c hphi hx
  have hci := (c.contMDiffOn_invFun.contMDiffAt
    (c.open_target.mem_nhds (c.map_source hx))).mdifferentiableAt (by simp)
  have hinv : c.symm (c (phi x)) = phi x := c.left_inv hx
  have hpsi' : MDifferentiableAt (𝓡 3) (𝓡 3) psi (c.symm (c (phi x))) := by
    rw [hinv]
    exact hpsi
  ext a b
  change h.inner _
      (mfderiv (𝓡 3) (𝓡 3) (psi ∘ c.symm) (c (phi x))
        (fderiv ℝ ((c : M → E) ∘ phi) x a))
      (mfderiv (𝓡 3) (𝓡 3) (psi ∘ c.symm) (c (phi x))
        (fderiv ℝ ((c : M → E) ∘ phi) x b)) =
    h.inner _ (mfderiv (𝓡 3) (𝓡 3) (psi ∘ phi) x a)
      (mfderiv (𝓡 3) (𝓡 3) (psi ∘ phi) x b)
  rw [mfderiv_comp _ hpsi' hci, mfderiv_comp x hpsi hphi]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have ha := congrArg (fun A => A a) hd
  have hb := congrArg (fun A => A b) hd
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  exact (congrArg₂ (fun V W : E => h.inner (psi (c.symm (c (phi x))))
    (mfderiv (𝓡 3) (𝓡 3) psi (c.symm (c (phi x))) V)
    (mfderiv (𝓡 3) (𝓡 3) psi (c.symm (c (phi x))) W)) ha hb).trans
      (congrArg (fun y : M => h.inner (psi y)
        (mfderiv (𝓡 3) (𝓡 3) psi y (mfderiv (𝓡 3) (𝓡 3) phi x a))
        (mfderiv (𝓡 3) (𝓡 3) psi y (mfderiv (𝓡 3) (𝓡 3) phi x b))) hinv)



theorem terminalCurvature_neck_composed_coefficient
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (h : RiemannianMetric 3 X)
    (psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hsource : N.carrier ⊆ psi.source)
    (q : UnitTwoSphere) (s : ℝ) {x : E}
    (hx : x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : Fin 3) :
    roundCylinderTensorCoefficient (roundCylinderPullback h (psi ∘ N.coordinate_map))
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, s)) a b =
      h.pullbackCoefficients (psi ∘ N.capPersistenceEuclideanMap q s) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  let T := fun y : M => fun v w : TangentSpace (𝓡 3) y =>
    h.inner (psi y) (mfderiv (𝓡 3) (𝓡 3) psi y v) (mfderiv (𝓡 3) (𝓡 3) psi y w)
  have hround (y : RoundCylinderCoordinates)
      (hy : y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
      roundCylinderTensorCoefficient (roundCylinderPullback h (psi ∘ N.coordinate_map))
          (chartAt E₂ q) y a b =
        roundCylinderTensorCoefficient (fun z v w => T (N.coordinate_map z)
          (mfderiv Ic (𝓡 3) N.coordinate_map z v)
          (mfderiv Ic (𝓡 3) N.coordinate_map z w)) (chartAt E₂ q) y a b := by
    let z : RoundCylinderSpace := ((chartAt E₂ q).symm y.1, y.2)
    have hN : MDifferentiableAt Ic (𝓡 3) N.coordinate_map z :=
      (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hy⟩)).mdifferentiableAt (by simp)
    have hpsi := (psi.contMDiffOn_toFun.contMDiffAt (psi.open_source.mem_nhds
      (hsource (N.coordinate_map_mem_of_axial_mem (z := z) hy)))).mdifferentiableAt (by simp)
    dsimp only [roundCylinderTensorCoefficient, roundCylinderPullback, T]
    rw [mfderiv_comp z hpsi hN]
    rfl
  rw [hround _ (by exact hx),
    N.capPersistence_tensor_coefficient T q s hx a b]
  have hN := (N.capPersistenceEuclideanMap_contMDiffAt q s hx).mdifferentiableAt (by simp)
  have hmem : N.capPersistenceEuclideanMap q s x ∈ N.carrier :=
    N.coordinate_map_mem_of_axial_mem hx
  have hpsi := (psi.contMDiffOn_toFun.contMDiffAt
    (psi.open_source.mem_nhds (hsource hmem))).mdifferentiableAt (by simp)
  change _ = h.inner _ (mfderiv (𝓡 3) (𝓡 3)
    (psi ∘ N.capPersistenceEuclideanMap q s) x _)
      (mfderiv (𝓡 3) (𝓡 3) (psi ∘ N.capPersistenceEuclideanMap q s) x _)
  rw [mfderiv_comp x hpsi hN]
  rfl



theorem terminalCurvature_neck_chart_error_germ
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (h : RiemannianMetric 3 X)
    (psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hsource : N.carrier ⊆ psi.source)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (q : UnitTwoSphere) (s : ℝ)
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hc : N.coordinate_map (q, s) ∈ c.source) (a b : Fin 3) :
    let f := (c : M → E) ∘ N.capPersistenceEuclideanMap q s
    let B := fun y => N.scale⁻¹ ^ 2 •
      (h.pullbackCoefficients (psi ∘ c.symm) y - g.pullbackCoefficients c.symm y)
    (fun x : E =>
      roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
          roundCylinderPullback h (psi ∘ N.coordinate_map) z v w)
          (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, s)) a b -
        roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
          roundCylinderPullback g N.coordinate_map z v w)
          (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, s)) a b)
      =ᶠ[𝓝 (0 : E)] fun x =>
        ((B (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x))
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  dsimp only
  let phi := N.capPersistenceEuclideanMap q s
  have hphi0 : phi 0 = N.coordinate_map (q, s) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q s)
  have hphi : ContinuousAt phi 0 :=
    (N.capPersistenceEuclideanMap_contMDiffAt q s (by simpa using hs)).continuousAt
  have haxis : ContinuousAt (fun x : E => x 2 + s) 0 :=
    ((EuclideanSpace.proj 2 : E →L[ℝ] ℝ).continuous.add continuous_const).continuousAt
  filter_upwards [hphi.tendsto.eventually (c.open_source.mem_nhds (hphi0 ▸ hc)),
    haxis.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa using hs))] with x hxc hx
  have hN := (N.capPersistenceEuclideanMap_contMDiffAt q s hx).mdifferentiableAt (by simp)
  have hmem : phi x ∈ N.carrier := N.coordinate_map_mem_of_axial_mem hx
  have hpsi := (psi.contMDiffOn_toFun.contMDiffAt
    (psi.open_source.mem_nhds (hsource hmem))).mdifferentiableAt (by simp)
  have ht := terminalCurvature_partial_chart_composed_metric h c hN hpsi hxc
  have ho := terminalCurvature_partial_chart_metric g c hN hxc
  have hn := N.capPersistence_tensor_coefficient (fun y v w => g.inner y v w) q s hx a b
  have hnew := terminalCurvature_neck_composed_coefficient N h psi hsource q s hx a b
  have ht' := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) ht
  have ho' := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) ho
  simp only [ContinuousLinearMap.bilinearComp_apply] at ht' ho'
  calc
    _ = N.scale⁻¹ ^ 2 * h.pullbackCoefficients
          (psi ∘ N.capPersistenceEuclideanMap q s) x
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) -
        N.scale⁻¹ ^ 2 * g.pullbackCoefficients (N.capPersistenceEuclideanMap q s) x
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) :=
      congrArg₂ (fun v w : ℝ => N.scale⁻¹ ^ 2 * v - N.scale⁻¹ ^ 2 * w) hnew hn
    _ = _ := by
      simp only [ContinuousLinearMap.bilinearComp_apply, smul_apply,
        sub_apply, smul_eq_mul, Function.comp_apply]
      rw [ht', ho']
      ring

end PoincareConjecture.M47
