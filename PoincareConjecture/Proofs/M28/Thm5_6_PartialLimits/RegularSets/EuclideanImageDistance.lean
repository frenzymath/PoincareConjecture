import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EuclideanImageBuffer
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.LocalIntrinsicDistance
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.OpenImageDiffeomorph
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ChartSegment

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

namespace PoincareConjecture.M28

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {N : Type*} [TopologicalSpace N]
  [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]

private theorem intrinsicImage_edist_le_of_convex_upper
    (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    (V : TopologicalSpace.Opens E) (W : TopologicalSpace.Opens N)
    (hsource : (V : Set E) ⊆ e.source) (hconv : Convex ℝ (V : Set E))
    (hmap : MapsTo e (V : Set E) (W : Set N))
    {b : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ z ∈ (V : Set E), ∀ v : E,
      h.inner (e z) (mfderiv (𝓡 3) (𝓡 3) e z v)
        (mfderiv (𝓡 3) (𝓡 3) e z v) ≤ b * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ (V : Set E)) (hy : y ∈ (V : Set E))
    (p q : W) (hp : (p : N) = e x) (hq : (q : N) = e y) :
    (intrinsicOpenMetric h W).edist p q ≤
      ENNReal.ofReal (Real.sqrt b) * edist x y := by
  let j := W.openPartialHomeomorphSubtypeCoe ⟨p⟩
  let F : E → W := j.symm ∘ e
  let g := intrinsicOpenMetric h W
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : W → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F (V : Set E) :=
    (openSubtypeInverse_contMDiffOn W ⟨p⟩).comp
      (e.contMDiffOn.mono hsource) hmap
  have hread (z : E) (hz : z ∈ (V : Set E)) : (F z : N) = e z := by
    change j (j.symm (e z)) = e z
    exact j.right_inv (by
      simpa only [j, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
        using hmap hz)
  have hsquare (z : E) (hz : z ∈ (V : Set E)) (v : E) :
      g.inner (F z) (mfderiv (𝓡 3) (𝓡 3) F z v)
        (mfderiv (𝓡 3) (𝓡 3) F z v) ≤ b * ‖v‖ ^ 2 := by
    have hnear : ((Subtype.val : W → N) ∘ F) =ᶠ[𝓝 z] e := by
      filter_upwards [V.isOpen.mem_nhds hz] with w hw
      exact hread w hw
    have hde : mfderiv (𝓡 3) (𝓡 3) ((Subtype.val : W → N) ∘ F) z =
        mfderiv (𝓡 3) (𝓡 3) e z := hnear.mfderiv_eq
    have hi : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : W → N) (F z) :=
      (contMDiff_subtype_val (I := 𝓡 3) (U := W) (n := 1)).mdifferentiable
        one_ne_zero (F z)
    have hdF : MDifferentiableAt (𝓡 3) (𝓡 3) F z :=
      (hF.contMDiffAt (V.isOpen.mem_nhds hz)).mdifferentiableAt (by simp)
    have hpush : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → N) (F z)
        (mfderiv (𝓡 3) (𝓡 3) F z v) = mfderiv (𝓡 3) (𝓡 3) e z v :=
      congrArg (fun L => L v) ((mfderiv_comp z hi hdF).symm.trans hde)
    change h.inner (F z : N)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → N) (F z)
        (mfderiv (𝓡 3) (𝓡 3) F z v))
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → N) (F z)
        (mfderiv (𝓡 3) (𝓡 3) F z v)) ≤ b * ‖v‖ ^ 2
    rw [hpush, hread z hz]
    exact hupper z hz v
  let K : ℝ≥0 := ⟨Real.sqrt b, Real.sqrt_nonneg b⟩
  have hnorm (z : E) (hz : z ∈ (V : Set E)) :
      ‖mfderiv (𝓡 3) (𝓡 3) F z‖ₑ ≤ (K : ℝ≥0∞) := by
    rw [← ofReal_norm, ENNReal.ofReal_le_coe]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg b)
    intro v
    change g.tangentNorm (F z) (mfderiv (𝓡 3) (𝓡 3) F z v) ≤
      Real.sqrt b * ‖v‖
    have hh := Real.sqrt_le_sqrt (hsquare z hz v)
    simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul hb,
      Real.sqrt_sq (norm_nonneg v)] using hh
  have hd := Poincare.riemannianEDist_le_mul_edist_of_convex hconv
    (fun z hz => (hF.contMDiffAt (V.isOpen.mem_nhds hz)).of_le (by simp))
    hnorm hx hy
  have hFx : F x = p := Subtype.ext ((hread x hx).trans hp.symm)
  have hFy : F y = q := Subtype.ext ((hread y hy).trans hq.symm)
  change g.edist (F x) (F y) ≤ (K : ℝ≥0∞) * edist x y at hd
  rw [hFx, hFy, ← ENNReal.ofReal_coe_nnreal] at hd
  exact hd

variable [T2Space N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]

theorem originalOpen_edist_eq_openImagePullback_of_euclidean_bounds
    (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    (U W : TopologicalSpace.Opens N) {a : ℝ} (ha : 0 < a)
    (hsource : ball (0 : E) a ⊆ e.source)
    (hW : (W : Set N) = e '' ball (0 : E) a)
    (hWU : (W : Set N) ⊆ (U : Set N))
    (hlower : ∀ z ∈ ball (0 : E) a, ∀ v : E,
      (1 / 8 : ℝ) * ‖v‖ ^ 2 ≤ h.inner (e z)
        (mfderiv (𝓡 3) (𝓡 3) e z v) (mfderiv (𝓡 3) (𝓡 3) e z v))
    (hupper : ∀ z ∈ ball (0 : E) a, ∀ v : E,
      h.inner (e z) (mfderiv (𝓡 3) (𝓡 3) e z v)
        (mfderiv (𝓡 3) (𝓡 3) e z v) ≤ (9 / 2 : ℝ) * ‖v‖ ^ 2)
    (D : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ W) (p q : X)
    {x y : E} (hx : x ∈ closedBall (0 : E) (a / 64))
    (hy : y ∈ closedBall (0 : E) (a / 64))
    (hp : (D p : N) = e x) (hq : (D q : N) = e y) :
    let g := h.pullbackOfLocalDiffeomorph ((Subtype.val : W → N) ∘ D)
      (diffeomorph_openImageMap_isLocalDiffeomorph W D)
    (intrinsicOpenMetric h U).edist ⟨D p, hWU (D p).property⟩
        ⟨D q, hWU (D q).property⟩ = g.edist p q ∧
      g.edist p q ≤ ENNReal.ofReal (Real.sqrt (9 / 2 : ℝ)) * edist x y ∧
      g.edist p q < ENNReal.ofReal (a / 8) := by
  let V : TopologicalSpace.Opens E := ⟨ball 0 a, isOpen_ball⟩
  let W0 : TopologicalSpace.Opens N :=
    ⟨e '' (V : Set E), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      V.isOpen hsource⟩
  have hWdef : W = W0 := by
    ext z
    change z ∈ (W : Set N) ↔ z ∈ e '' ball (0 : E) a
    rw [hW]
  subst W
  have hxV : x ∈ (V : Set E) := closedBall_subset_ball (by linarith) hx
  have hyV : y ∈ (V : Set E) := closedBall_subset_ball (by linarith) hy
  have hmap : MapsTo e (V : Set E) (W0 : Set N) := fun z hz => ⟨z, hz, rfl⟩
  have hbound := intrinsicImage_edist_le_of_convex_upper h e V W0 hsource
    (convex_ball (0 : E) a) hmap (by norm_num : (0 : ℝ) ≤ 9 / 2)
    hupper hxV hyV (D p) (D q) hp hq
  have hxy : dist x y ≤ a / 32 := by
    have hx0 : dist x 0 ≤ a / 64 := hx
    have hy0 : dist y 0 ≤ a / 64 := hy
    have ht := dist_triangle x (0 : E) y
    rw [dist_comm (0 : E) y] at ht
    linarith
  have hsqrt : Real.sqrt (9 / 2 : ℝ) < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 2),
      Real.sqrt_nonneg (9 / 2 : ℝ)]
  have hsmall : ENNReal.ofReal (Real.sqrt (9 / 2 : ℝ)) * edist x y <
      ENNReal.ofReal (a / 8) := by
    rw [edist_dist, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    calc
      Real.sqrt (9 / 2 : ℝ) * dist x y ≤ Real.sqrt (9 / 2 : ℝ) * (a / 32) :=
        mul_le_mul_of_nonneg_left hxy (Real.sqrt_nonneg _)
      _ < 3 * (a / 32) := mul_lt_mul_of_pos_right hsqrt (by positivity)
      _ < a / 8 := by linarith
  have hshort := hbound.trans_lt hsmall
  have hregular : D p ∈ regularPoints (intrinsicOpenMetric h W0) (a / 8) :=
    mem_intrinsicImage_regularPoints_of_euclidean_buffer h e ha hsource hlower
      hx (D p) hp
  have hlocal := intrinsicOpenMetric_edist_eq_on_nested_regular_image h U W0 hWU
    (D p) (D q) hregular hshort
  have hmetric := pullbackOfLocalDiffeomorph_edist_openImage h W0 D p q
  exact ⟨hlocal.trans hmetric.symm, hmetric.le.trans hbound,
    hmetric.le.trans_lt hshort⟩

end PoincareConjecture.M28
