import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.RicciTrace
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.Exponential
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import PoincareConjecture.Proofs.M60.Mathlib.DominatedDerivative
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem m60FixedMapAreaProperties_of_ricci_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Icc a b))
    (htensor : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    (D : ℝ) (hD : 0 ≤ D)
    (hnorm : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).ricciNormSq x ≤ D ^ 2)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    M60FixedMapAreaProperties F D f := by
  let A := fun s z => m60SphereAreaDensity (F.metric s) f z
  let V := fun s z => -m60SphereRicciTraceDensity (F.connection s) f z
  have hd (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => A s z) (V t z) (Icc a b) t :=
    m60SphereDensity_variation F f z ht
  have hv (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) :
      |V t z| ≤ 4 * D * A t z := by
    simpa only [V, abs_neg] using
      m60SphereRicciTraceDensity_bound (F.connection t) (htensor t ht) hD (hnorm t ht) f z
  have hAi (s : ℝ) : Integrable (A s) volume :=
    m60SphereAreaDensity_integrable (F.metric s) f hf
  have hA0 (z : LoopPlane) : 0 ≤ A a z :=
    m60AreaDensity_nonneg (F.metric a) (f ∘ m60SphereParameter) z
  let K := Real.exp (4 * D * (b - a))
  have hA (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) : A t z ≤ K * A a z := by
    have h := M60.le_exp_abs_mul_of_abs_deriv_le (hd z) (hv z)
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
        (by positivity))) (hA0 z))
  let bound := fun z => 4 * D * K * A a z
  have hbound : Integrable bound volume := (hAi a).const_mul (4 * D * K)
  have hV (z : LoopPlane) (t : ℝ) (ht : t ∈ Icc a b) : ‖V t z‖ ≤ bound z := by
    rw [Real.norm_eq_abs]
    exact (hv z t ht).trans (by
      simpa only [bound, mul_assoc] using
        mul_le_mul_of_nonneg_left (hA z t ht) (by positivity : 0 ≤ 4 * D))
  have hlip (z : LoopPlane) {t s : ℝ} (ht : t ∈ Icc a b) (hs : s ∈ Icc a b) :
      ‖A s z - A t z‖ ≤ bound z * ‖s - t‖ :=
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => A s z) (f' := fun s => V s z) (hd z) (hV z) ht hs
  have hintegral (t : ℝ) (ht : t ∈ Icc a b) :
      Integrable (V t) volume ∧
        HasDerivWithinAt (fun s => ∫ z, A s z ∂volume) (∫ z, V t z ∂volume) (Icc a b) t := by
    let : NeBot (𝓝[Icc a b \ {t}] t) :=
      accPt_principal_iff_nhdsWithin.mp ((uniqueDiffOn_Icc hab) t ht).accPt
    exact M60.hasDerivWithinAt_integral_of_dominated_lipschitz hAi hbound
      (Eventually.of_forall fun z s hs => hlip z ht hs)
      (Eventually.of_forall fun z => hd z t ht)
  have htrace (t : ℝ) (ht : t ∈ Icc a b) :
      Integrable (m60SphereRicciTraceDensity (F.connection t) f) volume := by
    exact integrable_neg_iff.mp (hintegral t ht).1
  apply m60FixedMapAreaProperties_of_variation F D f htrace
  · intro t ht
    simpa only [A, V, m60SphereArea, integral_neg] using (hintegral t ht).2
  · intro t ht
    rw [← integral_neg]
    change |∫ z, V t z ∂volume| ≤ 4 * D * m60SphereArea (F.metric t) f
    calc
      |∫ z, V t z ∂volume| ≤ ∫ z, ‖V t z‖ ∂volume := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (V t)
      _ ≤ ∫ z, 4 * D * A t z ∂volume :=
        integral_mono (hintegral t ht).1.norm ((hAi t).const_mul (4 * D))
          (fun z => by simpa only [Real.norm_eq_abs] using hv z t ht)
      _ = 4 * D * m60SphereArea (F.metric t) f := integral_const_mul _ _

end PoincareConjecture
