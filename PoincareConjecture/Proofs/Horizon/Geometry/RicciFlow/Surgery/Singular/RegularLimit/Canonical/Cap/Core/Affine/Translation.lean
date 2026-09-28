import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.AxialContraction
import Mathlib.Analysis.Calculus.FDeriv.Add



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderTranslation

def coordinates (s : ℝ) (p : RoundCylinderCoordinates) : RoundCylinderCoordinates :=
  (p.1, p.2 + s)

def space (s : ℝ) (z : RoundCylinderSpace) : RoundCylinderSpace := (z.1, z.2 + s)

def pullback (s : ℝ) (B : RoundCylinderTwoTensor) : RoundCylinderTwoTensor :=
  fun z v w => B (space s z) v w

theorem coordinates_eq_add (s : ℝ) (p : RoundCylinderCoordinates) :
    coordinates s p = p + (0, s) := by
  apply Prod.ext <;> simp [coordinates]

theorem coefficient_pullback (s : ℝ) (B : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderTensorCoefficient (pullback s B) c p a b =
      roundCylinderTensorCoefficient B c (coordinates s p) a b := rfl


theorem fderiv_translate (s : ℝ) (f : RoundCylinderCoordinates → ℝ)
    (p : RoundCylinderCoordinates) :
    fderiv ℝ (fun q => f (coordinates s q)) p = fderiv ℝ f (coordinates s p) := by
  simp only [coordinates_eq_add]
  exact fderiv_comp_add_right _

theorem gram_translate (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) :
    roundCylinderGram u c (coordinates s p) = roundCylinderGram u c p := rfl

theorem gram_fderiv_translate (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (a b : Fin 3) :
    fderiv ℝ (fun q => roundCylinderGram u c q a b) (coordinates s p) =
      fderiv ℝ (fun q => roundCylinderGram u c q a b) p := by
  rw [← fderiv_translate]
  rfl

theorem christoffel_translate (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    roundCylinderChristoffel u c (coordinates s p) a b d =
      roundCylinderChristoffel u c p a b d := by
  simp only [roundCylinderChristoffel, gram_translate, gram_fderiv_translate]

theorem derivative_translate (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {r : ℕ} (A : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates) (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u c (fun q => A (coordinates s q)) p a =
      roundCylinderTensorDerivative u c A (coordinates s p) a := by
  simp only [roundCylinderTensorDerivative, christoffel_translate]
  rw [fderiv_translate s (fun q => A q (fun i => a i.succ)) p]

theorem iteratedDerivative_pullback (s u : ℝ) (B : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2))) :
    ∀ k : ℕ, roundCylinderIteratedDerivative u c (pullback s B) k =
      fun p => roundCylinderIteratedDerivative u c B k (coordinates s p)
  | 0 => by
    funext p a
    simp only [roundCylinderIteratedDerivative, coefficient_pullback, gram_translate]
  | k + 1 => by
    change roundCylinderTensorDerivative u c
      (roundCylinderIteratedDerivative u c (pullback s B) k) = _
    rw [iteratedDerivative_pullback s u B c k]
    funext p a
    exact derivative_translate s u c (roundCylinderIteratedDerivative u c B k) p a



theorem jetErrorSquared_pullback (s u : ℝ) (B : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u (pullback s B) order z =
      roundCylinderJetErrorSquared u B order (space s z) := by
  unfold roundCylinderJetErrorSquared
  dsimp only [space]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivative_pullback]
  rfl

theorem smoothOn_pullback {ε δ : ℝ} (s : ℝ) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn ε B)
    (hsub : MapsTo (fun t : ℝ => t + s) (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderTensorSmoothOn δ (pullback s B) := by
  intro q a b
  change ContDiffOn ℝ ∞ (fun p => roundCylinderTensorCoefficient B
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) (coordinates s p) a b) _
  apply (hB q a b).comp ?_ (fun p hp => ⟨hp.1, hsub hp.2⟩)
  exact (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contDiffOn


theorem close_pullback {ε δ u : ℝ} (s : ℝ) {B : RoundCylinderTwoTensor}
    (hε : 0 < ε) (hεδ : ε ≤ δ) (hu : u < 1) (hB : RoundCylinderClose ε u B)
    (hsub : MapsTo (fun t : ℝ => t + s) (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderClose δ u (pullback s B) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hB
  refine ⟨smoothOn_pullback s hsmooth hsub, bound,
    hbound.trans_le ((sq_le_sq₀ hε.le (hε.le.trans hεδ)).2 hεδ), ?_⟩
  intro z hz
  rw [jetErrorSquared_pullback]
  have horder : ⌊δ⁻¹⌋₊ ≤ ⌊ε⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (hε.trans_le hεδ) hε).2 hεδ)
  exact (DeepHorn.evolvingCylinderJetErrorSquared_mono hu B (space s z) horder).trans
    (hjet (space s z) (hsub hz))


theorem metric_pullback_translate
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    (s : ℝ) (z : RoundCylinderSpace)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (space s z))
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback g (f ∘ space s) z v w =
      pullback s (roundCylinderPullback g f) z v w := by
  have hss : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (space s) :=
    contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)
  have hs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (space s) z :=
    (hss z).mdifferentiableAt (by simp)
  have hder (v : RoundCylinderTangent z) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (space s) z v = v := by
    have hh := CylinderGluing.mfderiv_axial_map_apply z ((hasDerivAt_id z.2).add_const s) v
    dsimp only [TangentSpace] at hh ⊢
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : RoundCylinderSpace => (p.1, p.2 + s)) z v = v
    simpa only [TangentSpace, id_eq, one_mul, Prod.eta] using hh
  unfold roundCylinderPullback pullback
  rw [mfderiv_comp z hf hs]
  dsimp only [TangentSpace]
  change g.inner (f (space s z))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (space s z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (space s) z v))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (space s z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (space s) z w)) = _
  rw [hder, hder]
  rfl

end PoincareConjecture.RoundCylinderTranslation

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem translated_metric_comparison (N : EpsilonNeck g) {δ : ℝ}
    (hεδ : N.epsilon ≤ δ) (s : ℝ)
    (hsub : MapsTo (fun t : ℝ => t + s) (Ioo (-δ⁻¹) δ⁻¹)
      (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)) :
    RoundCylinderClose δ 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback g (N.coordinate_map ∘ RoundCylinderTranslation.space s) z v w) := by
  have hh := RoundCylinderTranslation.close_pullback s N.epsilon_pos hεδ
    (by norm_num : (0 : ℝ) < 1) N.metric_comparison.close hsub
  apply DeepHorn.roundCylinderClose_congr_axial (B := RoundCylinderTranslation.pullback s
    (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)) _ hh
  intro z hz v w
  have hdom : RoundCylinderTranslation.space s z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨mem_univ _, hsub hz⟩
  have hf := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hdom)).mdifferentiableAt (by simp)
  rw [RoundCylinderTranslation.metric_pullback_translate g N.coordinate_map s z hf]
  rfl



theorem negative_half_metric_comparison (N : EpsilonNeck g) :
    RoundCylinderClose (2 * N.epsilon) 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback g (N.coordinate_map ∘
        RoundCylinderTranslation.space (-N.epsilon⁻¹ / 2)) z v w) := by
  apply N.translated_metric_comparison (by linarith [N.epsilon_pos])
  intro t ht
  have hi : (2 * N.epsilon)⁻¹ = N.epsilon⁻¹ / 2 := by
    rw [mul_inv_rev]
    ring
  rw [hi] at ht
  have he := inv_pos.mpr N.epsilon_pos
  constructor <;> dsimp only <;> linarith [ht.1, ht.2]

end PoincareConjecture.EpsilonNeck
